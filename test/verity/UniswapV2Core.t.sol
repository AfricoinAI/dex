// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {UniswapV2FactoryDeployer} from "../../src/generated/verity/UniswapV2FactoryDeployer.sol";
import {UniswapV2FactoryIface} from "../../src/generated/verity/UniswapV2FactoryIface.sol";
import {UniswapV2PairIface} from "../../src/generated/verity/UniswapV2PairIface.sol";

contract MockERC20 {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    uint256 public totalSupply;

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "BALANCE");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        uint256 allowed = allowance[from][msg.sender];
        require(allowed >= amount, "ALLOWANCE");
        if (allowed != type(uint256).max) {
            allowance[from][msg.sender] = allowed - amount;
        }
        require(balanceOf[from] >= amount, "BALANCE");
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        return true;
    }
}

contract FlashCallee {
    MockERC20 public token0;
    MockERC20 public token1;

    function uniswapV2Call(address, uint256 amount0Out, uint256 amount1Out, bytes calldata data) external {
        uint256 amount0In;
        uint256 amount1In;
        (token0, token1, amount0In, amount1In) = abi.decode(data, (MockERC20, MockERC20, uint256, uint256));
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "FLASH_TRANSFER0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "FLASH_TRANSFER1");
        amount0Out;
        amount1Out;
    }
}

contract UniswapV2CoreTest is Test {
    MockERC20 tokenA;
    MockERC20 tokenB;
    UniswapV2FactoryIface factory;
    UniswapV2PairIface pair;

    function setUp() public {
        tokenA = new MockERC20();
        tokenB = new MockERC20();
        factory = UniswapV2FactoryDeployer.deploy();
        pair = UniswapV2PairIface(factory.createPair(address(tokenA), address(tokenB)));
    }

    function seed(uint256 amountA, uint256 amountB) internal {
        tokenA.mint(address(pair), amountA);
        tokenB.mint(address(pair), amountB);
        pair.mint(address(this));
    }

    function getAmountIn(uint256 amountOut, uint256 reserveIn, uint256 reserveOut) internal pure returns (uint256) {
        return (reserveIn * amountOut * 1000) / ((reserveOut - amountOut) * 997) + 1;
    }

    function testFactorySortsStoresReversePairAndRejectsDuplicates() public {
        (address token0, address token1) =
            address(tokenA) < address(tokenB) ? (address(tokenA), address(tokenB)) : (address(tokenB), address(tokenA));

        assertEq(factory.allPairsLength(), 1);
        assertEq(factory.allPairs(0), address(pair));
        assertEq(factory.getPair(address(tokenA), address(tokenB)), address(pair));
        assertEq(factory.getPair(address(tokenB), address(tokenA)), address(pair));
        assertEq(pair.factory(), address(factory));
        assertEq(pair.token0(), token0);
        assertEq(pair.token1(), token1);

        vm.expectRevert();
        factory.createPair(address(tokenA), address(tokenB));
        vm.expectRevert();
        factory.createPair(address(tokenA), address(tokenA));
        vm.expectRevert();
        factory.createPair(address(0), address(tokenB));
    }

    function testMintLocksMinimumLiquidityAndBurnsProRata() public {
        seed(1_000_000, 4_000_000);

        assertEq(pair.MINIMUM_LIQUIDITY(), 1000);
        assertEq(pair.totalSupply(), 2_000_000);
        assertEq(pair.balanceOf(address(0)), 1000);
        assertEq(pair.balanceOf(address(this)), 1_999_000);
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        assertEq(reserve0, pair.token0() == address(tokenA) ? 1_000_000 : 4_000_000);
        assertEq(reserve1, pair.token0() == address(tokenA) ? 4_000_000 : 1_000_000);

        assertTrue(pair.transfer(address(pair), 200_000));
        (uint256 amount0, uint256 amount1) = pair.burn(address(this));
        assertEq(amount0, reserve0 / 10);
        assertEq(amount1, reserve1 / 10);
        assertEq(pair.totalSupply(), 1_800_000);
    }

    function testSwapEnforcesFeeAdjustedKAndUpdatesReserves() public {
        seed(10_000, 10_000);
        address token0 = pair.token0();
        MockERC20 inToken = token0 == address(tokenA) ? tokenA : tokenB;
        MockERC20 outToken = token0 == address(tokenA) ? tokenB : tokenA;

        inToken.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
        assertEq(outToken.balanceOf(address(this)), 906);
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        assertEq(reserve0, 11_000);
        assertEq(reserve1, 9_094);

        inToken.mint(address(pair), 1_000);
        vm.expectRevert();
        pair.swap(0, 907, address(this), "");
    }

    function testFlashSwapCallbackAndKLastFeeOff() public {
        seed(10_000, 10_000);
        FlashCallee callee = new FlashCallee();
        uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
        MockERC20 sorted0 = pair.token0() == address(tokenA) ? tokenA : tokenB;
        MockERC20 sorted1 = pair.token0() == address(tokenA) ? tokenB : tokenA;
        sorted1.mint(address(callee), requiredIn);

        bytes memory data = abi.encode(sorted0, sorted1, 0, requiredIn);
        pair.swap(1_000, 0, address(callee), data);
        assertEq(pair.kLast(), 0);
    }

    function testSkimAndSync() public {
        seed(10_000, 10_000);
        tokenA.mint(address(pair), 123);
        tokenB.mint(address(pair), 456);
        pair.skim(address(this));

        assertEq(tokenA.balanceOf(address(this)), 123);
        assertEq(tokenB.balanceOf(address(this)), 456);

        tokenA.mint(address(pair), 7);
        tokenB.mint(address(pair), 9);
        pair.sync();
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        assertEq(reserve0, 10_000 + (pair.token0() == address(tokenA) ? 7 : 9));
        assertEq(reserve1, 10_000 + (pair.token0() == address(tokenA) ? 9 : 7));
    }

    function testLpErc20ApproveTransferFromAndMaxAllowance() public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.decimals(), 18);
        assertTrue(pair.approve(address(0xBEEF), type(uint256).max));

        vm.prank(address(0xBEEF));
        assertTrue(pair.transferFrom(address(this), address(0xCAFE), 100));
        assertEq(pair.allowance(address(this), address(0xBEEF)), type(uint256).max);
        assertEq(pair.balanceOf(address(0xCAFE)), 100);
    }
}
