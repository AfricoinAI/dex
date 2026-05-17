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

contract ReentrantCallee {
    UniswapV2PairIface public pair;
    MockERC20 public token0;
    MockERC20 public token1;
    uint256 public amount0In;
    uint256 public amount1In;
    bool public reentryRejected;

    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_, uint256 amount0In_, uint256 amount1In_) {
        pair = pair_;
        token0 = token0_;
        token1 = token1_;
        amount0In = amount0In_;
        amount1In = amount1In_;
    }

    function uniswapV2Call(address, uint256, uint256, bytes calldata) external {
        try pair.sync() {
            revert("REENTRY_ALLOWED");
        } catch {
            reentryRejected = true;
        }
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "REENTER_TRANSFER0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "REENTER_TRANSFER1");
    }
}

contract UniswapV2CoreTest is Test {
    MockERC20 tokenA;
    MockERC20 tokenB;
    UniswapV2FactoryIface factory;
    UniswapV2PairIface pair;

    uint256 constant MAX_UINT112 = 5192296858534827628530496329220095;

    event Approval(address indexed owner, address indexed spender, uint256 value);
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(address indexed sender, uint256 amount0, uint256 amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint256 reserve0, uint256 reserve1);
    event PairCreated(address indexed token0, address indexed token1, address pair, uint256 allPairsLength);

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

    function sorted(address x, address y) internal pure returns (address token0, address token1) {
        return x < y ? (x, y) : (y, x);
    }

    function sortedAmounts(uint256 amountA, uint256 amountB) internal view returns (uint256 amount0, uint256 amount1) {
        return pair.token0() == address(tokenA) ? (amountA, amountB) : (amountB, amountA);
    }

    function pairCreationCodeHex() internal view returns (string memory) {
        bytes memory raw = bytes(vm.readFile("artifacts/bytecode/UniswapV2Pair.bin"));
        uint256 length = raw.length;
        if (length > 0 && raw[length - 1] == 0x0a) {
            length -= 1;
        }
        bytes memory trimmed = new bytes(length);
        for (uint256 i = 0; i < length; i++) {
            trimmed[i] = raw[i];
        }
        return string.concat("0x", string(trimmed));
    }

    function expectedCreate2Pair(address token0, address token1) internal view returns (address) {
        bytes memory creationCode = vm.parseBytes(pairCreationCodeHex());
        bytes32 salt = keccak256(abi.encodePacked(token0, token1));
        return address(uint160(uint256(keccak256(abi.encodePacked(hex"ff", address(factory), salt, keccak256(creationCode))))));
    }

    // tama: mirrors=factory_createPair_rejects_duplicates
    // tama: mirrors=factory_createPair_rejects_identical_addresses
    // tama: mirrors=factory_createPair_rejects_zero_address
    function testFuzzFactorySortsStoresReversePairAndRejectsDuplicates() public {
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

    // tama: mirrors=factory_allPairs_reverts_out_of_bounds
    function testFuzzFactoryAllPairsOutOfBoundsReverts() public {
        uint256 length = factory.allPairsLength();
        vm.expectRevert();
        factory.allPairs(length);
    }

    function testFuzzFactoryCreatePairUsesPackedSaltAndEmits() public {
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        (address token0, address token1) = sorted(address(tokenC), address(tokenD));
        address expectedPair = expectedCreate2Pair(token0, token1);
        uint256 expectedLength = factory.allPairsLength() + 1;

        vm.expectEmit(true, true, false, true, address(factory));
        emit PairCreated(token0, token1, expectedPair, expectedLength);
        address created = factory.createPair(address(tokenC), address(tokenD));

        assertEq(created, expectedPair);
        assertEq(factory.getPair(address(tokenC), address(tokenD)), expectedPair);
        assertEq(factory.allPairs(expectedLength - 1), expectedPair);
    }

    // tama: mirrors=pair_initialize_reverts_for_non_factory
    // tama: mirrors=pair_initialize_reverts_when_already_initialized
    function testFuzzPairInitializeRequiresFactoryAndRejectsSecondCall() public {
        vm.expectRevert();
        pair.initialize(address(tokenA), address(tokenB));

        vm.prank(address(factory));
        vm.expectRevert();
        pair.initialize(address(tokenA), address(tokenB));
    }

    function testFuzzPairOmitsMetadataAndPermitSurface() public {
        (bool nameOk,) = address(pair).staticcall(abi.encodeWithSignature("name()"));
        (bool symbolOk,) = address(pair).staticcall(abi.encodeWithSignature("symbol()"));
        (bool permitOk,) = address(pair).call(
            abi.encodeWithSignature(
                "permit(address,address,uint256,uint256,uint8,bytes32,bytes32)",
                address(this),
                address(0xBEEF),
                uint256(1),
                block.timestamp,
                uint8(27),
                bytes32(0),
                bytes32(0)
            )
        );

        assertFalse(nameOk);
        assertFalse(symbolOk);
        assertFalse(permitOk);
    }

    function testFuzzLargeInitialMintUsesFloorSqrt() public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);

        uint256 liquidity = pair.mint(address(this));

        assertEq(liquidity, 1 ether - 1000);
        assertEq(pair.totalSupply(), 1 ether);
        assertEq(pair.balanceOf(address(0)), 1000);
        assertEq(pair.balanceOf(address(this)), 1 ether - 1000);
    }

    function testFuzzSubsequentMintUsesMinProRataLiquidity() public {
        seed(1_000_000, 1_000_000);
        tokenA.mint(address(pair), 100_000);
        tokenB.mint(address(pair), 50_000);

        uint256 liquidity = pair.mint(address(this));

        assertEq(liquidity, 50_000);
        assertEq(pair.totalSupply(), 1_050_000);
    }

    function testFuzzMintRevertsWhenOneTokenAmountMissing() public {
        tokenA.mint(address(pair), 1_000_000);

        vm.expectRevert();
        pair.mint(address(this));
    }

    function testFuzzMintRevertsOnReserveOverflow() public {
        tokenA.mint(address(pair), MAX_UINT112 + 1);
        tokenB.mint(address(pair), 1);

        vm.expectRevert();
        pair.mint(address(this));
    }

    function testFuzzMintLocksMinimumLiquidityAndBurnsProRata() public {
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

    function testFuzzBurnRevertsWithoutLiquidity() public {
        vm.expectRevert();
        pair.burn(address(this));
    }

    // tama: mirrors=pair_approve_succeeds
    // tama: mirrors=pair_approve_sets_allowance
    // tama: mirrors=pair_approve_keeps_balances
    // tama: mirrors=pair_approve_keeps_total_supply
    // tama: mirrors=pair_transfer_moves_tokens_between_distinct_accounts
    function testFuzzLpApproveTransferAndEvents() public {
        seed(1_000_000, 1_000_000);
        uint256 senderBefore = pair.balanceOf(address(this));
        uint256 supplyBefore = pair.totalSupply();

        vm.expectEmit(true, true, false, true, address(pair));
        emit Approval(address(this), address(0xBEEF), 123);
        assertTrue(pair.approve(address(0xBEEF), 123));
        assertEq(pair.balanceOf(address(this)), senderBefore);
        assertEq(pair.totalSupply(), supplyBefore);

        vm.expectEmit(true, true, false, true, address(pair));
        emit Transfer(address(this), address(0xCAFE), 100);
        assertTrue(pair.transfer(address(0xCAFE), 100));

        assertEq(pair.allowance(address(this), address(0xBEEF)), 123);
        assertEq(pair.balanceOf(address(0xCAFE)), 100);
        assertEq(pair.balanceOf(address(this)), senderBefore - 100);
    }

    // tama: mirrors=pair_transfer_reverts_when_balance_low
    // tama: mirrors=pair_transferFrom_reverts_when_allowance_low
    // tama: mirrors=pair_transferFrom_reverts_when_balance_low
    function testFuzzLpTransferAndTransferFromRevertGuards() public {
        seed(1_000_000, 1_000_000);

        vm.prank(address(0xBEEF));
        (bool lowBalanceOk,) = address(pair).call(abi.encodeCall(UniswapV2PairIface.transfer, (address(this), 1)));
        assertFalse(lowBalanceOk);

        (bool allowanceOk,) =
            address(pair).call(abi.encodeCall(UniswapV2PairIface.transferFrom, (address(this), address(0xCAFE), 1)));
        assertFalse(allowanceOk);

        vm.prank(address(0xD00D));
        assertTrue(pair.approve(address(0xBEEF), 1));
        vm.prank(address(0xBEEF));
        (bool balanceOk,) =
            address(pair).call(abi.encodeCall(UniswapV2PairIface.transferFrom, (address(0xD00D), address(0xCAFE), 1)));
        assertFalse(balanceOk);
    }

    function testMintEmitsTransferSyncAndMint() public {
        uint256 amountA = 1_000_000;
        uint256 amountB = 4_000_000;
        (uint256 amount0, uint256 amount1) = sortedAmounts(amountA, amountB);
        tokenA.mint(address(pair), amountA);
        tokenB.mint(address(pair), amountB);

        vm.expectEmit(true, true, false, true, address(pair));
        emit Transfer(address(0), address(0), 1000);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Transfer(address(0), address(this), 1_999_000);
        vm.expectEmit(false, false, false, true, address(pair));
        emit Sync(amount0, amount1);
        vm.expectEmit(true, false, false, true, address(pair));
        emit Mint(address(this), amount0, amount1);
        pair.mint(address(this));
    }

    function testBurnEmitsTransferSyncAndBurn() public {
        seed(1_000_000, 4_000_000);
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        uint256 liquidity = 200_000;
        assertTrue(pair.transfer(address(pair), liquidity));
        uint256 amount0 = (liquidity * reserve0) / pair.totalSupply();
        uint256 amount1 = (liquidity * reserve1) / pair.totalSupply();

        vm.expectEmit(true, true, false, true, address(pair));
        emit Transfer(address(pair), address(0), liquidity);
        vm.expectEmit(false, false, false, true, address(pair));
        emit Sync(reserve0 - amount0, reserve1 - amount1);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Burn(address(this), amount0, amount1, address(this));
        pair.burn(address(this));
    }

    function testFuzzSwapEnforcesFeeAdjustedKAndUpdatesReserves() public {
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

    function testSwapEmitsSyncAndSwap() public {
        seed(10_000, 10_000);
        address token0 = pair.token0();
        MockERC20 inToken = token0 == address(tokenA) ? tokenA : tokenB;
        inToken.mint(address(pair), 1_000);

        vm.expectEmit(false, false, false, true, address(pair));
        emit Sync(11_000, 9_094);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Swap(address(this), 1_000, 0, 0, 906, address(this));
        pair.swap(0, 906, address(this), "");
    }

    // tama: mirrors=pair_swap_run_revert_zero_output
    function testFuzzSwapRevertGuards() public {
        seed(10_000, 10_000);

        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"));
        pair.swap(0, 0, address(this), "");

        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_LIQUIDITY"));
        pair.swap(10_000, 0, address(this), "");

        address token0Addr = pair.token0();
        vm.expectRevert(bytes("UniswapV2: INVALID_TO"));
        pair.swap(1, 0, token0Addr, "");

        vm.expectRevert();
        pair.swap(1, 0, address(this), "");
    }

    function testFuzzFlashSwapCallbackAndKLastFeeOff() public {
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

    function testFuzzFlashSwapCallbackCannotReenterPair() public {
        seed(10_000, 10_000);
        uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
        MockERC20 sorted0 = pair.token0() == address(tokenA) ? tokenA : tokenB;
        MockERC20 sorted1 = pair.token0() == address(tokenA) ? tokenB : tokenA;
        ReentrantCallee callee = new ReentrantCallee(pair, sorted0, sorted1, 0, requiredIn);
        sorted1.mint(address(callee), requiredIn);

        pair.swap(1_000, 0, address(callee), abi.encode(uint256(1)));

        assertTrue(callee.reentryRejected());
    }

    function testFuzzSkimAndSync() public {
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

    function testSyncEmitsUpdatedReserves() public {
        seed(10_000, 10_000);
        tokenA.mint(address(pair), 7);
        tokenB.mint(address(pair), 9);
        uint256 reserve0 = 10_000 + (pair.token0() == address(tokenA) ? 7 : 9);
        uint256 reserve1 = 10_000 + (pair.token0() == address(tokenA) ? 9 : 7);

        vm.expectEmit(false, false, false, true, address(pair));
        emit Sync(reserve0, reserve1);
        pair.sync();
    }

    function testFuzzSyncRevertsOnReserveOverflow() public {
        seed(10_000, 10_000);
        tokenA.mint(address(pair), MAX_UINT112);

        vm.expectRevert();
        pair.sync();
    }

    function testFuzzPriceCumulativeUpdatesAfterElapsedTime() public {
        seed(10_000, 10_000);
        vm.warp(block.timestamp + 10);
        tokenA.mint(address(pair), 7);
        tokenB.mint(address(pair), 9);

        pair.sync();

        assertEq(pair.price0CumulativeLast(), 10 * 2 ** 112);
        assertEq(pair.price1CumulativeLast(), 10 * 2 ** 112);
    }

    // tama: mirrors=pair_transferFrom_keeps_infinite_allowance
    function testFuzzLpErc20ApproveTransferFromAndMaxAllowance() public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.decimals(), 18);
        assertTrue(pair.approve(address(0xBEEF), type(uint256).max));

        vm.prank(address(0xBEEF));
        assertTrue(pair.transferFrom(address(this), address(0xCAFE), 100));
        assertEq(pair.allowance(address(this), address(0xBEEF)), type(uint256).max);
        assertEq(pair.balanceOf(address(0xCAFE)), 100);
    }

    // tama: mirrors=pair_transfer_keeps_total_supply
    // tama: mirrors=pair_transferFrom_spends_finite_allowance
    function testFuzzLpTransfersCanGoToZeroAddressLikeUniswapV2() public {
        seed(1_000_000, 1_000_000);

        assertTrue(pair.transfer(address(0), 123));
        assertEq(pair.balanceOf(address(0)), 1123);
        assertEq(pair.totalSupply(), 1_000_000);

        assertTrue(pair.approve(address(0xBEEF), 50));
        vm.prank(address(0xBEEF));
        assertTrue(pair.transferFrom(address(this), address(0), 50));
        assertEq(pair.balanceOf(address(0)), 1173);
        assertEq(pair.allowance(address(this), address(0xBEEF)), 0);
        assertEq(pair.totalSupply(), 1_000_000);
    }
}
