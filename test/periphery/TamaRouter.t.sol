// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {TamaRouter} from "../../src/TamaRouter.sol";
import {UniswapV2FactoryDeployer} from "../../src/generated/verity/UniswapV2FactoryDeployer.sol";
import {UniswapV2FactoryIface} from "../../src/generated/verity/UniswapV2FactoryIface.sol";
import {UniswapV2PairIface} from "../../src/generated/verity/UniswapV2PairIface.sol";
import {MockERC20} from "../verity/UniswapV2Helpers.sol";

contract MockWETH is MockERC20 {
    string public constant name = "Wrapped Ether";
    string public constant symbol = "WETH";
    uint8 public constant decimals = 18;

    event Deposit(address indexed dst, uint256 wad);
    event Withdrawal(address indexed src, uint256 wad);

    function deposit() external payable {
        balanceOf[msg.sender] += msg.value;
        totalSupply += msg.value;
        emit Deposit(msg.sender, msg.value);
        emit Transfer(address(0), msg.sender, msg.value);
    }

    function withdraw(uint256 amount) external {
        require(balanceOf[msg.sender] >= amount, "BALANCE");
        balanceOf[msg.sender] -= amount;
        totalSupply -= amount;
        emit Transfer(msg.sender, address(0), amount);
        emit Withdrawal(msg.sender, amount);
        payable(msg.sender).transfer(amount);
    }

    receive() external payable {
        this.deposit{value: msg.value}();
    }
}

contract TamaRouterTest is Test {
    UniswapV2FactoryIface internal factory;
    TamaRouter internal router;
    MockWETH internal weth;
    MockERC20 internal tokenA;
    MockERC20 internal tokenB;

    function setUp() public {
        factory = UniswapV2FactoryDeployer.deploy();
        weth = new MockWETH();
        router = new TamaRouter(address(factory), address(weth));
        tokenA = new MockERC20();
        tokenB = new MockERC20();
        tokenA.mint(address(this), 1_000_000 ether);
        tokenB.mint(address(this), 1_000_000 ether);
        tokenA.approve(address(router), type(uint256).max);
        tokenB.approve(address(router), type(uint256).max);
    }

    receive() external payable {}

    function testAddLiquidityCreatesPairAndMintsLp() public {
        (uint256 amountA, uint256 amountB, uint256 liquidity) = router.addLiquidity(
            address(tokenA),
            address(tokenB),
            100_000 ether,
            200_000 ether,
            100_000 ether,
            200_000 ether,
            address(this),
            block.timestamp
        );

        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        UniswapV2PairIface pair = UniswapV2PairIface(pairAddr);

        assertTrue(pairAddr != address(0));
        assertEq(amountA, 100_000 ether);
        assertEq(amountB, 200_000 ether);
        assertGt(liquidity, 0);
        assertEq(pair.balanceOf(address(this)), liquidity);
        assertEq(tokenA.balanceOf(pairAddr), 100_000 ether);
        assertEq(tokenB.balanceOf(pairAddr), 200_000 ether);
    }

    function testAddLiquidityUsesOptimalAmountForExistingPool() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 200_000 ether, 0, 0, address(this), block.timestamp
        );

        (uint256 amountA, uint256 amountB,) = router.addLiquidity(
            address(tokenA), address(tokenB), 10_000 ether, 30_000 ether, 0, 0, address(this), block.timestamp
        );

        assertEq(amountA, 10_000 ether);
        assertEq(amountB, 20_000 ether);
    }

    function testSwapExactTokensForTokensTransfersOutput() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(tokenA);
        path[1] = address(tokenB);
        uint256[] memory expected = router.getAmountsOut(1_000 ether, path);
        address recipient = address(0xBEEF);

        uint256[] memory amounts =
            router.swapExactTokensForTokens(1_000 ether, expected[1], path, recipient, block.timestamp);

        assertEq(amounts[0], 1_000 ether);
        assertEq(amounts[1], expected[1]);
        assertEq(tokenB.balanceOf(recipient), expected[1]);
    }

    function testSwapTokensForExactTokensTransfersRequestedOutput() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(tokenA);
        path[1] = address(tokenB);
        uint256 amountOut = 500 ether;
        uint256[] memory expected = router.getAmountsIn(amountOut, path);
        uint256 tokenABefore = tokenA.balanceOf(address(this));
        address recipient = address(0xBEEF);

        uint256[] memory amounts =
            router.swapTokensForExactTokens(amountOut, expected[0], path, recipient, block.timestamp);

        assertEq(amounts[0], expected[0]);
        assertEq(amounts[1], amountOut);
        assertEq(tokenABefore - tokenA.balanceOf(address(this)), expected[0]);
        assertEq(tokenB.balanceOf(recipient), amountOut);
    }

    function testSwapTokensForExactTokensEnforcesMaxInput() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(tokenA);
        path[1] = address(tokenB);
        uint256[] memory expected = router.getAmountsIn(500 ether, path);

        vm.expectRevert(bytes("TamaRouter: EXCESSIVE_INPUT_AMOUNT"));
        router.swapTokensForExactTokens(500 ether, expected[0] - 1, path, address(0xBEEF), block.timestamp);
    }

    function testAddLiquidityETHWrapsNativeValueAndMintsLp() public {
        (uint256 amountToken, uint256 amountETH, uint256 liquidity) = router.addLiquidityETH{value: 100 ether}(
            address(tokenA), 200 ether, 200 ether, 100 ether, address(this), block.timestamp
        );

        address pairAddr = factory.getPair(address(tokenA), address(weth));
        UniswapV2PairIface pair = UniswapV2PairIface(pairAddr);

        assertTrue(pairAddr != address(0));
        assertEq(amountToken, 200 ether);
        assertEq(amountETH, 100 ether);
        assertGt(liquidity, 0);
        assertEq(pair.balanceOf(address(this)), liquidity);
        assertEq(tokenA.balanceOf(pairAddr), 200 ether);
        assertEq(weth.balanceOf(pairAddr), 100 ether);
    }

    function testSwapExactETHForTokensWrapsAndTransfersOutput() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA), 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(weth);
        path[1] = address(tokenA);
        uint256[] memory expected = router.getAmountsOut(1 ether, path);
        address recipient = address(0xBEEF);

        uint256[] memory amounts = router.swapExactETHForTokens{value: 1 ether}(expected[1], path, recipient, block.timestamp);

        assertEq(amounts[0], 1 ether);
        assertEq(amounts[1], expected[1]);
        assertEq(tokenA.balanceOf(recipient), expected[1]);
    }

    function testSwapTokensForExactETHUnwrapsAndTransfersNativeOutput() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA), 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(tokenA);
        path[1] = address(weth);
        uint256 amountOut = 1 ether;
        uint256[] memory expected = router.getAmountsIn(amountOut, path);
        address recipient = address(0xBEEF);
        uint256 ethBefore = recipient.balance;

        uint256[] memory amounts =
            router.swapTokensForExactETH(amountOut, expected[0], path, recipient, block.timestamp);

        assertEq(amounts[0], expected[0]);
        assertEq(amounts[1], amountOut);
        assertEq(recipient.balance - ethBefore, amountOut);
    }

    function testRemoveLiquidityETHUnwrapsWethToNativeETH() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA), 200_000 ether, 0, 0, address(this), block.timestamp
        );
        address pairAddr = factory.getPair(address(tokenA), address(weth));
        UniswapV2PairIface pair = UniswapV2PairIface(pairAddr);
        uint256 liquidity = pair.balanceOf(address(this)) / 2;
        pair.approve(address(router), liquidity);
        address recipient = address(0xBEEF);
        uint256 ethBefore = recipient.balance;

        (uint256 amountToken, uint256 amountETH) =
            router.removeLiquidityETH(address(tokenA), liquidity, 0, 0, recipient, block.timestamp);

        assertGt(amountToken, 0);
        assertGt(amountETH, 0);
        assertEq(tokenA.balanceOf(recipient), amountToken);
        assertEq(recipient.balance - ethBefore, amountETH);
    }

    function testWrapAndUnwrapETH() public {
        router.wrapETH{value: 2 ether}(address(this));
        assertEq(weth.balanceOf(address(this)), 2 ether);

        weth.approve(address(router), 1 ether);
        uint256 ethBefore = address(this).balance;
        router.unwrapETH(1 ether, address(this));

        assertEq(weth.balanceOf(address(this)), 1 ether);
        assertEq(address(this).balance - ethBefore, 1 ether);
    }

    function testRemoveLiquidityBurnsLpAndReturnsTokens() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 200_000 ether, 0, 0, address(this), block.timestamp
        );
        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        UniswapV2PairIface pair = UniswapV2PairIface(pairAddr);
        uint256 liquidity = pair.balanceOf(address(this)) / 2;
        pair.approve(address(router), liquidity);
        address recipient = address(0xCAFE);

        (uint256 amountA, uint256 amountB) =
            router.removeLiquidity(address(tokenA), address(tokenB), liquidity, 0, 0, recipient, block.timestamp);

        assertGt(amountA, 0);
        assertGt(amountB, 0);
        assertEq(tokenA.balanceOf(recipient), amountA);
        assertEq(tokenB.balanceOf(recipient), amountB);
    }

    function testDeadlineIsEnforced() public {
        vm.expectRevert(bytes("TamaRouter: EXPIRED"));
        router.addLiquidity(address(tokenA), address(tokenB), 1, 1, 0, 0, address(this), block.timestamp - 1);
    }
}
