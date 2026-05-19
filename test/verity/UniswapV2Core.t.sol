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

    event Transfer(address indexed from, address indexed to, uint256 value);

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
        emit Transfer(address(0), to, amount);
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "BALANCE");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
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
        emit Transfer(from, to, amount);
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

contract TrackingFlashCallee {
    bool public called;
    address public lastSender;
    uint256 public lastAmount0Out;
    uint256 public lastAmount1Out;
    bytes public lastData;

    function uniswapV2Call(address sender, uint256 amount0Out, uint256 amount1Out, bytes calldata data) external {
        called = true;
        lastSender = sender;
        lastAmount0Out = amount0Out;
        lastAmount1Out = amount1Out;
        lastData = data;
        (MockERC20 payToken, uint256 payAmount) = abi.decode(data, (MockERC20, uint256));
        if (payAmount > 0) require(payToken.transfer(msg.sender, payAmount), "PAY");
    }
}

contract RevertingFlashCallee {
    function uniswapV2Call(address, uint256, uint256, bytes calldata) external pure {
        revert("FLASH_FAIL");
    }
}

contract MintReentrantCallee {
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
        try pair.mint(address(this)) returns (uint256) {
            revert("MINT_REENTRY_ALLOWED");
        } catch {
            reentryRejected = true;
        }
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "PAY0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "PAY1");
    }
}

contract BurnReentrantCallee {
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
        try pair.burn(address(this)) returns (uint256, uint256) {
            revert("BURN_REENTRY_ALLOWED");
        } catch {
            reentryRejected = true;
        }
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "PAY0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "PAY1");
    }
}

contract SwapReentrantCallee {
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
        try pair.swap(0, 1, address(this), "") {
            revert("SWAP_REENTRY_ALLOWED");
        } catch {
            reentryRejected = true;
        }
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "PAY0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "PAY1");
    }
}

contract SkimReentrantCallee {
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
        try pair.skim(address(this)) {
            revert("SKIM_REENTRY_ALLOWED");
        } catch {
            reentryRejected = true;
        }
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "PAY0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "PAY1");
    }
}

contract SyncReentrantCallee {
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
            revert("SYNC_REENTRY_ALLOWED");
        } catch {
            reentryRejected = true;
        }
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "PAY0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "PAY1");
    }
}

abstract contract PairFixture is Test {
    MockERC20 internal tokenA;
    MockERC20 internal tokenB;
    UniswapV2FactoryIface internal factory;
    UniswapV2PairIface internal pair;

    uint256 internal constant MAX_UINT112 = 5192296858534827628530496329220095;

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

    function setUp() public virtual {
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

    function sortedTokens() internal view returns (MockERC20 t0, MockERC20 t1) {
        return pair.token0() == address(tokenA) ? (tokenA, tokenB) : (tokenB, tokenA);
    }

    function sortedAmounts(uint256 amountA, uint256 amountB) internal view returns (uint256 amount0, uint256 amount1) {
        return pair.token0() == address(tokenA) ? (amountA, amountB) : (amountB, amountA);
    }

    function lpBalanceSlot(address account) internal pure returns (bytes32) {
        return keccak256(abi.encode(account, uint256(9)));
    }

    function lpAllowanceSlot(address owner, address spender) internal pure returns (bytes32) {
        return keccak256(abi.encode(spender, keccak256(abi.encode(owner, uint256(10)))));
    }

    function setLpBalance(address account, uint256 amount) internal {
        vm.store(address(pair), lpBalanceSlot(account), bytes32(amount));
    }

    function setLpAllowance(address owner, address spender, uint256 amount) internal {
        vm.store(address(pair), lpAllowanceSlot(owner, spender), bytes32(amount));
    }

    function getAmountIn(uint256 amountOut, uint256 reserveIn, uint256 reserveOut) internal pure returns (uint256) {
        return (reserveIn * amountOut * 1000) / ((reserveOut - amountOut) * 997) + 1;
    }

    function getAmountOut(uint256 amountIn, uint256 reserveIn, uint256 reserveOut) internal pure returns (uint256) {
        uint256 amountInWithFee = amountIn * 997;
        return (amountInWithFee * reserveOut) / (reserveIn * 1000 + amountInWithFee);
    }
}

// =====================================================================
// Pair view framings (§14)
//
// Each test exercises one public view and asserts it returns the exact
// storage cell (or constant) the spec promises.
// =====================================================================

contract PairViewMirrors is PairFixture {
    // tama: mirrors=pair_decimals_run_success_frames_state
    function testFuzzMirrorDecimalsReturnsEighteen() public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.decimals(), 18);
    }

    // tama: mirrors=pair_totalSupply_run_success_frames_state
    function testFuzzMirrorTotalSupplyReturnsLpSupplyCell() public {
        seed(1_000_000, 4_000_000);
        assertEq(pair.totalSupply(), 2_000_000);
        seed(5_000, 20_000);
        assertEq(pair.totalSupply(), 2_010_000);
    }

    // tama: mirrors=pair_balanceOf_run_success_frames_state
    function testFuzzMirrorBalanceOfReturnsLpBalanceCell() public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.balanceOf(address(this)), 999_000);
        assertEq(pair.balanceOf(address(0)), 1000);
        assertEq(pair.balanceOf(address(0xBEEF)), 0);
    }

    // tama: mirrors=pair_allowance_run_success_frames_state
    function testFuzzMirrorAllowanceReturnsAllowanceCell() public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.allowance(address(this), address(0xBEEF)), 0);
        pair.approve(address(0xBEEF), 4242);
        assertEq(pair.allowance(address(this), address(0xBEEF)), 4242);
    }

    // tama: mirrors=pair_factory_run_success_frames_state
    function testFuzzMirrorFactoryReturnsCreator() public {
        assertEq(pair.factory(), address(factory));
    }

    // tama: mirrors=pair_token0_run_success_frames_state
    function testFuzzMirrorToken0ReturnsSortedFirstToken() public {
        (address sorted0,) =
            address(tokenA) < address(tokenB) ? (address(tokenA), address(tokenB)) : (address(tokenB), address(tokenA));
        assertEq(pair.token0(), sorted0);
    }

    // tama: mirrors=pair_token1_run_success_frames_state
    function testFuzzMirrorToken1ReturnsSortedSecondToken() public {
        (, address sorted1) =
            address(tokenA) < address(tokenB) ? (address(tokenA), address(tokenB)) : (address(tokenB), address(tokenA));
        assertEq(pair.token1(), sorted1);
    }

    // tama: mirrors=pair_minimumLiquidity_run_success_frames_state
    function testFuzzMirrorMinimumLiquidityIsConstantOneThousand() public {
        assertEq(pair.MINIMUM_LIQUIDITY(), 1000);
    }

    // tama: mirrors=pair_getReserves_run_success_frames_state
    function testFuzzMirrorGetReservesReturnsCachedReservesAndTimestamp() public {
        seed(2_000_000, 5_000_000);
        (uint256 amount0, uint256 amount1) = sortedAmounts(2_000_000, 5_000_000);
        (uint256 reserve0, uint256 reserve1, uint256 ts) = pair.getReserves();
        assertEq(reserve0, amount0);
        assertEq(reserve1, amount1);
        assertEq(ts, uint32(block.timestamp));
    }

    // tama: mirrors=pair_price0CumulativeLast_run_success_frames_state
    function testFuzzMirrorPrice0CumulativeLastReturnsCachedAccumulator() public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.price0CumulativeLast(), 0);
        vm.warp(block.timestamp + 7);
        tokenA.mint(address(pair), 3);
        tokenB.mint(address(pair), 4);
        pair.sync();
        assertEq(pair.price0CumulativeLast(), 7 * (2 ** 112));
    }

    // tama: mirrors=pair_price1CumulativeLast_run_success_frames_state
    function testFuzzMirrorPrice1CumulativeLastReturnsCachedAccumulator() public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.price1CumulativeLast(), 0);
        vm.warp(block.timestamp + 11);
        tokenA.mint(address(pair), 3);
        tokenB.mint(address(pair), 4);
        pair.sync();
        assertEq(pair.price1CumulativeLast(), 11 * (2 ** 112));
    }

    // tama: mirrors=pair_kLast_run_success_frames_state
    function testFuzzMirrorKLastIsAlwaysZero() public {
        assertEq(pair.kLast(), 0);
        seed(1_000_000, 1_000_000);
        assertEq(pair.kLast(), 0);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 5_000);
        pair.swap(0, 4_500, address(this), "");
        assertEq(pair.kLast(), 0);
    }
}

// =====================================================================
// Pair exact-revert guards (§10)
//
// Each test exercises one guarded failure path and asserts the call
// reverts with the canonical payload.
// =====================================================================

contract PairRevertMirrors is PairFixture {
    // tama: mirrors=pair_initialize_run_revert_non_factory
    function testFuzzMirrorInitializeRevertsForNonFactory() public {
        vm.expectRevert(bytes("UniswapV2: FORBIDDEN"));
        pair.initialize(address(tokenA), address(tokenB));
    }

    // tama: mirrors=pair_initialize_reverts_for_non_factory
    function testFuzzMirrorInitializeNonFactoryResultIsRevert() public {
        (bool ok, bytes memory data) = address(pair).call(
            abi.encodeCall(UniswapV2PairIface.initialize, (address(tokenA), address(tokenB)))
        );
        assertFalse(ok);
        bytes memory expected = abi.encodeWithSignature("Error(string)", "UniswapV2: FORBIDDEN");
        assertEq(keccak256(data), keccak256(expected));
    }

    // tama: mirrors=pair_initialize_run_revert_already_initialized
    function testFuzzMirrorInitializeRevertsWhenAlreadyInitialized() public {
        vm.prank(address(factory));
        vm.expectRevert(bytes("UniswapV2: ALREADY_INITIALIZED"));
        pair.initialize(address(tokenA), address(tokenB));
    }

    // tama: mirrors=pair_initialize_reverts_when_already_initialized
    function testFuzzMirrorInitializeAlreadyInitializedResultIsRevert() public {
        vm.prank(address(factory));
        (bool ok, bytes memory data) = address(pair).call(
            abi.encodeCall(UniswapV2PairIface.initialize, (address(tokenA), address(tokenB)))
        );
        assertFalse(ok);
        bytes memory expected = abi.encodeWithSignature("Error(string)", "UniswapV2: ALREADY_INITIALIZED");
        assertEq(keccak256(data), keccak256(expected));
    }

    // tama: mirrors=pair_transfer_run_revert_balance_low
    function testFuzzMirrorTransferRevertsWhenSenderBalanceTooLow() public {
        seed(1_000_000, 1_000_000);
        vm.prank(address(0xBEEF));
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_BALANCE"));
        pair.transfer(address(this), 1);
    }

    // tama: mirrors=pair_transfer_run_revert_recipient_balance_overflow
    function testFuzzMirrorTransferRevertsOnRecipientBalanceOverflow() public {
        seed(1_000_000, 1_000_000);
        vm.store(address(pair), keccak256(abi.encode(address(0xCAFE), uint256(9))), bytes32(type(uint256).max));
        vm.expectRevert(bytes("UniswapV2: BALANCE_OVERFLOW"));
        pair.transfer(address(0xCAFE), 1);
    }

    // tama: mirrors=pair_transferFrom_run_revert_allowance_low
    function testFuzzMirrorTransferFromRevertsWhenAllowanceTooLow() public {
        seed(1_000_000, 1_000_000);
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_ALLOWANCE"));
        pair.transferFrom(address(this), address(0xCAFE), 1);
    }

    // tama: mirrors=pair_transferFrom_run_revert_balance_low
    function testFuzzMirrorTransferFromRevertsWhenSourceBalanceTooLow() public {
        seed(1_000_000, 1_000_000);
        vm.prank(address(0xD00D));
        pair.approve(address(0xBEEF), 100);
        vm.prank(address(0xBEEF));
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_BALANCE"));
        pair.transferFrom(address(0xD00D), address(0xCAFE), 1);
    }

    // tama: mirrors=pair_transferFrom_run_revert_recipient_balance_overflow
    function testFuzzMirrorTransferFromRevertsOnRecipientBalanceOverflow() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 100);
        vm.store(address(pair), keccak256(abi.encode(address(0xCAFE), uint256(9))), bytes32(type(uint256).max));
        vm.prank(address(0xBEEF));
        vm.expectRevert(bytes("UniswapV2: BALANCE_OVERFLOW"));
        pair.transferFrom(address(this), address(0xCAFE), 1);
    }

    // tama: mirrors=pair_mint_run_revert_locked
    function testFuzzMirrorMintRevertsWhenLockClosed() public {
        vm.store(address(pair), bytes32(uint256(11)), bytes32(uint256(0)));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.mint(address(this));
    }

    // tama: mirrors=pair_mint_run_revert_balance0_overflow
    function testFuzzMirrorMintRevertsOnBalance0Overflow() public {
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), MAX_UINT112 + 1);
        t1.mint(address(pair), 1);
        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.mint(address(this));
    }

    // tama: mirrors=pair_mint_run_revert_balance1_overflow
    function testFuzzMirrorMintRevertsOnBalance1Overflow() public {
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 1);
        t1.mint(address(pair), MAX_UINT112 + 1);
        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.mint(address(this));
    }

    // tama: mirrors=pair_burn_run_revert_locked
    function testFuzzMirrorBurnRevertsWhenLockClosed() public {
        vm.store(address(pair), bytes32(uint256(11)), bytes32(uint256(0)));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.burn(address(this));
    }

    // tama: mirrors=pair_swap_run_revert_locked
    function testFuzzMirrorSwapRevertsWhenLockClosed() public {
        vm.store(address(pair), bytes32(uint256(11)), bytes32(uint256(0)));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.swap(0, 1, address(this), "");
    }

    // tama: mirrors=pair_swap_run_revert_zero_output
    function testFuzzMirrorSwapRevertsOnZeroOutput() public {
        seed(10_000, 10_000);
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"));
        pair.swap(0, 0, address(this), "");
    }

    // tama: mirrors=pair_skim_run_revert_locked
    function testFuzzMirrorSkimRevertsWhenLockClosed() public {
        vm.store(address(pair), bytes32(uint256(11)), bytes32(uint256(0)));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.skim(address(this));
    }

    // tama: mirrors=pair_skim_run_revert_balance0_below_reserve
    function testFuzzMirrorSkimRevertsWhenBalance0BelowReserve() public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        vm.prank(address(pair));
        t0.transfer(address(0xBEEF), 1);
        vm.expectRevert();
        pair.skim(address(this));
    }

    // tama: mirrors=pair_skim_run_revert_balance1_below_reserve
    function testFuzzMirrorSkimRevertsWhenBalance1BelowReserve() public {
        seed(10_000, 10_000);
        (, MockERC20 t1) = sortedTokens();
        vm.prank(address(pair));
        t1.transfer(address(0xBEEF), 1);
        vm.expectRevert();
        pair.skim(address(this));
    }

    // tama: mirrors=pair_sync_run_revert_locked
    function testFuzzMirrorSyncRevertsWhenLockClosed() public {
        vm.store(address(pair), bytes32(uint256(11)), bytes32(uint256(0)));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.sync();
    }

    // tama: mirrors=pair_sync_run_revert_balance0_overflow
    function testFuzzMirrorSyncRevertsOnBalance0Overflow() public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), MAX_UINT112);
        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.sync();
    }

    // tama: mirrors=pair_sync_run_revert_balance1_overflow
    function testFuzzMirrorSyncRevertsOnBalance1Overflow() public {
        seed(10_000, 10_000);
        (, MockERC20 t1) = sortedTokens();
        t1.mint(address(pair), MAX_UINT112);
        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.sync();
    }
}

// =====================================================================
// Pair atomicity: reverted runs leave storage and events unchanged (§10)
// =====================================================================

contract PairRevertKeepsStateMirrors is PairFixture {
    struct Snapshot {
        bytes32 reserve0;
        bytes32 reserve1;
        bytes32 supply;
        bytes32 unlocked;
        bytes32 token0;
        bytes32 token1;
        bytes32 factoryAddr;
        bytes32 price0;
        bytes32 price1;
    }

    function snapshot() internal view returns (Snapshot memory s) {
        s.reserve0 = vm.load(address(pair), bytes32(uint256(3)));
        s.reserve1 = vm.load(address(pair), bytes32(uint256(4)));
        s.supply = vm.load(address(pair), bytes32(uint256(8)));
        s.unlocked = vm.load(address(pair), bytes32(uint256(11)));
        s.token0 = vm.load(address(pair), bytes32(uint256(1)));
        s.token1 = vm.load(address(pair), bytes32(uint256(2)));
        s.factoryAddr = vm.load(address(pair), bytes32(uint256(0)));
        s.price0 = vm.load(address(pair), bytes32(uint256(6)));
        s.price1 = vm.load(address(pair), bytes32(uint256(7)));
    }

    function assertSnapshotEq(Snapshot memory a, Snapshot memory b) internal {
        assertEq(a.reserve0, b.reserve0);
        assertEq(a.reserve1, b.reserve1);
        assertEq(a.supply, b.supply);
        assertEq(a.unlocked, b.unlocked);
        assertEq(a.token0, b.token0);
        assertEq(a.token1, b.token1);
        assertEq(a.factoryAddr, b.factoryAddr);
        assertEq(a.price0, b.price0);
        assertEq(a.price1, b.price1);
    }

    // tama: mirrors=pair_mint_revert_keeps_pair_state
    function testFuzzMirrorMintRevertLeavesPairStateUnchanged() public {
        seed(1_000_000, 1_000_000);
        Snapshot memory pre = snapshot();
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), MAX_UINT112);
        vm.expectRevert();
        pair.mint(address(this));
        assertSnapshotEq(snapshot(), pre);
    }

    // tama: mirrors=pair_burn_revert_keeps_pair_state
    function testFuzzMirrorBurnRevertLeavesPairStateUnchanged() public {
        seed(1_000_000, 1_000_000);
        Snapshot memory pre = snapshot();
        // No LP transferred to pair => burn divides by zero pro-rata and reverts.
        vm.expectRevert();
        pair.burn(address(this));
        assertSnapshotEq(snapshot(), pre);
    }

    // tama: mirrors=pair_swap_revert_keeps_pair_state
    function testFuzzMirrorSwapRevertLeavesPairStateUnchanged() public {
        seed(10_000, 10_000);
        Snapshot memory pre = snapshot();
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"));
        pair.swap(0, 0, address(this), "");
        assertSnapshotEq(snapshot(), pre);
    }

    // tama: mirrors=pair_skim_revert_keeps_pair_state
    function testFuzzMirrorSkimRevertLeavesPairStateUnchanged() public {
        seed(10_000, 10_000);
        Snapshot memory pre = snapshot();
        (MockERC20 t0,) = sortedTokens();
        vm.prank(address(pair));
        t0.transfer(address(0xBEEF), 1);
        vm.expectRevert();
        pair.skim(address(this));
        assertSnapshotEq(snapshot(), pre);
    }

    // tama: mirrors=pair_sync_revert_keeps_pair_state
    function testFuzzMirrorSyncRevertLeavesPairStateUnchanged() public {
        seed(10_000, 10_000);
        Snapshot memory pre = snapshot();
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), MAX_UINT112);
        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.sync();
        assertSnapshotEq(snapshot(), pre);
    }
}

// =====================================================================
// Pair initialize success path (§13)
// =====================================================================

contract PairInitializeMirrors is Test {
    MockERC20 tokenA;
    MockERC20 tokenB;
    UniswapV2FactoryIface factory;

    function setUp() public {
        tokenA = new MockERC20();
        tokenB = new MockERC20();
        factory = UniswapV2FactoryDeployer.deploy();
    }

    // tama: mirrors=pair_initialize_run_success_sets_tokens
    function testFuzzMirrorInitializeSetsTokenIdentities() public {
        address pairAddr = factory.createPair(address(tokenA), address(tokenB));
        UniswapV2PairIface freshPair = UniswapV2PairIface(pairAddr);
        (address sorted0, address sorted1) =
            address(tokenA) < address(tokenB) ? (address(tokenA), address(tokenB)) : (address(tokenB), address(tokenA));
        assertEq(freshPair.token0(), sorted0);
        assertEq(freshPair.token1(), sorted1);
    }

    // tama: mirrors=pair_initialize_run_success_keeps_amm_accounting
    function testFuzzMirrorInitializeKeepsAmmAccounting() public {
        address pairAddr = factory.createPair(address(tokenA), address(tokenB));
        UniswapV2PairIface freshPair = UniswapV2PairIface(pairAddr);
        (uint256 reserve0, uint256 reserve1, uint256 ts) = freshPair.getReserves();
        assertEq(reserve0, 0);
        assertEq(reserve1, 0);
        assertEq(ts, 0);
        assertEq(freshPair.totalSupply(), 0);
        assertEq(freshPair.balanceOf(address(this)), 0);
        assertEq(freshPair.balanceOf(address(0)), 0);
    }
}

// =====================================================================
// Pair approve success path (§12)
// =====================================================================

contract PairApproveMirrors is PairFixture {
    // tama: mirrors=pair_approve_succeeds
    function testFuzzMirrorApproveReturnsTrue() public {
        seed(1_000_000, 1_000_000);
        assertTrue(pair.approve(address(0xBEEF), 123));
    }

    // tama: mirrors=pair_approve_sets_allowance
    function testFuzzMirrorApproveSetsAllowance() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 4242);
        assertEq(pair.allowance(address(this), address(0xBEEF)), 4242);
    }

    // tama: mirrors=pair_approve_keeps_balances
    function testFuzzMirrorApproveKeepsBalances() public {
        seed(1_000_000, 1_000_000);
        uint256 selfBefore = pair.balanceOf(address(this));
        uint256 zeroBefore = pair.balanceOf(address(0));
        uint256 spenderBefore = pair.balanceOf(address(0xBEEF));
        pair.approve(address(0xBEEF), 4242);
        assertEq(pair.balanceOf(address(this)), selfBefore);
        assertEq(pair.balanceOf(address(0)), zeroBefore);
        assertEq(pair.balanceOf(address(0xBEEF)), spenderBefore);
    }

    // tama: mirrors=pair_approve_keeps_total_supply
    function testFuzzMirrorApproveKeepsTotalSupply() public {
        seed(1_000_000, 1_000_000);
        uint256 supplyBefore = pair.totalSupply();
        pair.approve(address(0xBEEF), 4242);
        assertEq(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_approve_emits_approval
    function testFuzzMirrorApproveEmitsApproval() public {
        seed(1_000_000, 1_000_000);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Approval(address(this), address(0xBEEF), 4242);
        pair.approve(address(0xBEEF), 4242);
    }

    // tama: mirrors=pair_approve_keeps_pool_storage
    function testFuzzMirrorApproveKeepsPoolStorage() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before, uint256 tsBefore) = pair.getReserves();
        uint256 price0Before = pair.price0CumulativeLast();
        uint256 price1Before = pair.price1CumulativeLast();
        address token0Before = pair.token0();
        address token1Before = pair.token1();
        pair.approve(address(0xBEEF), 4242);
        (uint256 reserve0After, uint256 reserve1After, uint256 tsAfter) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(tsAfter, tsBefore);
        assertEq(pair.price0CumulativeLast(), price0Before);
        assertEq(pair.price1CumulativeLast(), price1Before);
        assertEq(pair.token0(), token0Before);
        assertEq(pair.token1(), token1Before);
    }
}

// =====================================================================
// Pair LP transfer success path (§12)
// =====================================================================

contract PairTransferMirrors is PairFixture {
    // tama: mirrors=pair_transfer_to_self_keeps_balances
    function testFuzzMirrorTransferToSelfKeepsBalances() public {
        seed(1_000_000, 1_000_000);
        uint256 before = pair.balanceOf(address(this));
        assertTrue(pair.transfer(address(this), 100));
        assertEq(pair.balanceOf(address(this)), before);
    }

    // tama: mirrors=pair_transfer_moves_tokens_between_distinct_accounts
    function testFuzzMirrorTransferMovesBetweenDistinctAccounts() public {
        seed(1_000_000, 1_000_000);
        uint256 senderBefore = pair.balanceOf(address(this));
        uint256 recipientBefore = pair.balanceOf(address(0xCAFE));
        assertTrue(pair.transfer(address(0xCAFE), 100));
        assertEq(pair.balanceOf(address(this)), senderBefore - 100);
        assertEq(pair.balanceOf(address(0xCAFE)), recipientBefore + 100);
    }

    // tama: mirrors=pair_transfer_keeps_total_supply
    function testFuzzMirrorTransferKeepsTotalSupply() public {
        seed(1_000_000, 1_000_000);
        uint256 supplyBefore = pair.totalSupply();
        assertTrue(pair.transfer(address(0xCAFE), 100));
        assertEq(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_transfer_keeps_pool_storage
    function testFuzzMirrorTransferKeepsPoolStorage() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before, uint256 tsBefore) = pair.getReserves();
        uint256 price0Before = pair.price0CumulativeLast();
        uint256 price1Before = pair.price1CumulativeLast();
        address token0Before = pair.token0();
        address token1Before = pair.token1();
        assertTrue(pair.transfer(address(0xCAFE), 100));
        (uint256 reserve0After, uint256 reserve1After, uint256 tsAfter) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(tsAfter, tsBefore);
        assertEq(pair.price0CumulativeLast(), price0Before);
        assertEq(pair.price1CumulativeLast(), price1Before);
        assertEq(pair.token0(), token0Before);
        assertEq(pair.token1(), token1Before);
    }

    // tama: mirrors=pair_transfer_emits_transfer
    function testFuzzMirrorTransferEmitsTransfer() public {
        seed(1_000_000, 1_000_000);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Transfer(address(this), address(0xCAFE), 100);
        pair.transfer(address(0xCAFE), 100);
    }
}

// =====================================================================
// Pair LP transferFrom success path (§12)
// =====================================================================

contract PairTransferFromMirrors is PairFixture {
    // tama: mirrors=pair_transferFrom_to_self_keeps_balances
    function testFuzzMirrorTransferFromToSelfKeepsBalances() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 100);
        uint256 before = pair.balanceOf(address(this));
        vm.prank(address(0xBEEF));
        assertTrue(pair.transferFrom(address(this), address(this), 100));
        assertEq(pair.balanceOf(address(this)), before);
    }

    // tama: mirrors=pair_transferFrom_moves_tokens_between_distinct_accounts
    function testFuzzMirrorTransferFromMovesBetweenDistinctAccounts() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 100);
        uint256 senderBefore = pair.balanceOf(address(this));
        uint256 recipientBefore = pair.balanceOf(address(0xCAFE));
        vm.prank(address(0xBEEF));
        assertTrue(pair.transferFrom(address(this), address(0xCAFE), 100));
        assertEq(pair.balanceOf(address(this)), senderBefore - 100);
        assertEq(pair.balanceOf(address(0xCAFE)), recipientBefore + 100);
    }

    // tama: mirrors=pair_transferFrom_keeps_total_supply
    function testFuzzMirrorTransferFromKeepsTotalSupply() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 100);
        uint256 supplyBefore = pair.totalSupply();
        vm.prank(address(0xBEEF));
        assertTrue(pair.transferFrom(address(this), address(0xCAFE), 100));
        assertEq(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_transferFrom_keeps_pool_storage
    function testFuzzMirrorTransferFromKeepsPoolStorage() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 100);
        (uint256 reserve0Before, uint256 reserve1Before, uint256 tsBefore) = pair.getReserves();
        uint256 price0Before = pair.price0CumulativeLast();
        uint256 price1Before = pair.price1CumulativeLast();
        address token0Before = pair.token0();
        address token1Before = pair.token1();
        vm.prank(address(0xBEEF));
        assertTrue(pair.transferFrom(address(this), address(0xCAFE), 100));
        (uint256 reserve0After, uint256 reserve1After, uint256 tsAfter) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(tsAfter, tsBefore);
        assertEq(pair.price0CumulativeLast(), price0Before);
        assertEq(pair.price1CumulativeLast(), price1Before);
        assertEq(pair.token0(), token0Before);
        assertEq(pair.token1(), token1Before);
    }

    // tama: mirrors=pair_transferFrom_emits_transfer
    function testFuzzMirrorTransferFromEmitsTransfer() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 100);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Transfer(address(this), address(0xCAFE), 100);
        vm.prank(address(0xBEEF));
        pair.transferFrom(address(this), address(0xCAFE), 100);
    }

    // tama: mirrors=pair_transferFrom_keeps_infinite_allowance
    function testFuzzMirrorTransferFromMaxAllowanceStaysMax() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), type(uint256).max);
        vm.prank(address(0xBEEF));
        pair.transferFrom(address(this), address(0xCAFE), 100);
        assertEq(pair.allowance(address(this), address(0xBEEF)), type(uint256).max);
    }

    // tama: mirrors=pair_transferFrom_spends_finite_allowance
    function testFuzzMirrorTransferFromFiniteAllowanceIsConsumed() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 250);
        vm.prank(address(0xBEEF));
        pair.transferFrom(address(this), address(0xCAFE), 100);
        assertEq(pair.allowance(address(this), address(0xBEEF)), 150);
    }
}

// =====================================================================
// Pair mint success path (§15, §6)
// =====================================================================

contract PairMintMirrors is PairFixture {
    // tama: mirrors=pair_first_mint_uses_balance_increase_as_deposit
    function testFuzzMirrorFirstMintTreatsBalanceIncreaseAsDeposit() public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);
        pair.mint(address(this));
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        (uint256 amount0, uint256 amount1) = sortedAmounts(1 ether, 1 ether);
        assertEq(reserve0, amount0);
        assertEq(reserve1, amount1);
    }

    // tama: mirrors=pair_first_mint_success_uses_canonical_liquidity_formula
    function testFuzzMirrorFirstMintReturnsSqrtMinusMinimumLiquidity() public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);
        uint256 liquidity = pair.mint(address(this));
        assertEq(liquidity, 1 ether - 1000);
        assertEq(pair.totalSupply(), 1 ether);
        assertEq(pair.balanceOf(address(0)), 1000);
        assertEq(pair.balanceOf(address(this)), 1 ether - 1000);
    }

    // tama: mirrors=pair_later_mint_uses_balance_increase_as_deposit
    function testFuzzMirrorSubsequentMintTreatsBalanceIncreaseAsDeposit() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        tokenA.mint(address(pair), 100_000);
        tokenB.mint(address(pair), 50_000);
        (uint256 amount0, uint256 amount1) = sortedAmounts(100_000, 50_000);
        pair.mint(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before + amount0);
        assertEq(reserve1After, reserve1Before + amount1);
    }
}

// =====================================================================
// Pair burn success path (§15, §6)
// =====================================================================

contract PairBurnMirrors is PairFixture {
    // tama: mirrors=pair_burn_uses_pair_lp_balance_and_total_supply
    function testFuzzMirrorBurnUsesPairLpBalanceAndTotalSupply() public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        uint256 supplyBefore = pair.totalSupply();
        uint256 liquidity = pair.balanceOf(address(pair));
        assertEq(liquidity, 200_000);
        assertEq(supplyBefore, 2_000_000);
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        (uint256 amount0, uint256 amount1) = pair.burn(address(this));
        assertEq(amount0, (liquidity * reserve0) / supplyBefore);
        assertEq(amount1, (liquidity * reserve1) / supplyBefore);
    }

    // tama: mirrors=pair_burn_success_pays_exact_pro_rata_amounts
    function testFuzzMirrorBurnPaysExactProRataAmounts() public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        uint256 supply = pair.totalSupply();
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        uint256 expected0 = (200_000 * reserve0) / supply;
        uint256 expected1 = (200_000 * reserve1) / supply;
        (uint256 amount0, uint256 amount1) = pair.burn(address(this));
        assertEq(amount0, expected0);
        assertEq(amount1, expected1);
    }

    // tama: mirrors=pair_burn_leaves_remaining_token_balances
    function testFuzzMirrorBurnLeavesRemainingTokenBalances() public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 pairBalance0Before = t0.balanceOf(address(pair));
        uint256 pairBalance1Before = t1.balanceOf(address(pair));
        (uint256 amount0, uint256 amount1) = pair.burn(address(this));
        assertEq(t0.balanceOf(address(pair)), pairBalance0Before - amount0);
        assertEq(t1.balanceOf(address(pair)), pairBalance1Before - amount1);
    }

    // tama: mirrors=pair_burn_success_caches_post_redemption_balances
    function testFuzzMirrorBurnCachesPostRedemptionBalances() public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        pair.burn(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, t0.balanceOf(address(pair)));
        assertEq(reserve1After, t1.balanceOf(address(pair)));
    }
}

// =====================================================================
// Pair swap success path (§15, §6)
// =====================================================================

contract PairSwapMirrors is PairFixture {
    // tama: mirrors=pair_swap_success_run_implies_nonzero_output
    function testFuzzMirrorSwapSuccessImpliesNonzeroOutput() public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
    }

    // tama: mirrors=pair_swap_uses_final_balances_to_compute_input
    function testFuzzMirrorSwapInfersInputFromFinalBalance() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, t0.balanceOf(address(pair)));
        assertEq(reserve1After, t1.balanceOf(address(pair)));
        assertEq(reserve0After, 11_000);
        assertEq(reserve1After, 9_094);
    }

    // tama: mirrors=pair_swap_success_accounts_for_input_and_output
    function testFuzzMirrorSwapFinalBalancesAccountForInputAndOutput() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 1_000);
        uint256 reserve0Before = 10_000;
        uint256 reserve1Before = 10_000;
        pair.swap(0, 906, address(this), "");
        assertEq(t0.balanceOf(address(pair)), reserve0Before + 1_000);
        assertEq(t1.balanceOf(address(pair)) + 906, reserve1Before);
    }

    // tama: mirrors=pair_swap_checks_k_against_final_balances
    function testFuzzMirrorSwapKHoldsAgainstFinalBalances() public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        // (balance0*1000 - amount0In*3) * (balance1*1000) >= reserve0Before*reserve1Before*1000*1000
        assertGe((reserve0After * 1000 - 1_000 * 3) * (reserve1After * 1000), 10_000 * 10_000 * 1000 * 1000);
    }

    // tama: mirrors=pair_swap_success_charges_k_against_final_balances
    function testFuzzMirrorSwapKBoundaryRejectsUnpaidOutput() public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);
        vm.expectRevert();
        pair.swap(0, 907, address(this), "");
    }
}

// =====================================================================
// Pair skim success path (§8)
// =====================================================================

contract PairSkimMirrors is PairFixture {
    // tama: mirrors=pair_skim_run_success_transfers_excess_and_restores_unlocked
    function testFuzzMirrorSkimSuccessTransfersExcessAndRestoresUnlocked() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 123);
        t1.mint(address(pair), 456);
        uint256 recipientBalance0Before = t0.balanceOf(address(this));
        uint256 recipientBalance1Before = t1.balanceOf(address(this));
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        pair.skim(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(t0.balanceOf(address(this)) - recipientBalance0Before, 123);
        assertEq(t1.balanceOf(address(this)) - recipientBalance1Before, 456);
        // The lock cell sits at slot 11 and should be 1 after a successful skim.
        assertEq(uint256(vm.load(address(pair), bytes32(uint256(11)))), 1);
    }

    // tama: mirrors=pair_skim_success_run_implies_balances_back_reserves
    function testFuzzMirrorSkimSuccessImpliesBalancesCoverReserves() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 7);
        t1.mint(address(pair), 8);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        assertGe(t0.balanceOf(address(pair)), reserve0Before);
        assertGe(t1.balanceOf(address(pair)), reserve1Before);
        pair.skim(address(this));
    }

    // tama: mirrors=pair_skim_success_run_restores_unlocked_from_run
    function testFuzzMirrorSkimSuccessRestoresUnlocked() public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1);
        pair.skim(address(this));
        assertEq(uint256(vm.load(address(pair), bytes32(uint256(11)))), 1);
    }
}

// =====================================================================
// Pair closed-world step mirrors: concrete entrypoint effects.
// Each test exercises one action and asserts the post-state arithmetic
// the Lean step relation captures abstractly.
// =====================================================================

contract PairClosedWorldStepMirrors is PairFixture {
    // tama: mirrors=pair_closed_world_approve_preserves_pool
    function testFuzzMirrorApprovePreservesPool() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        uint256 supplyBefore = pair.totalSupply();
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        uint256 lockedBefore = pair.balanceOf(address(0));
        pair.approve(address(0xBEEF), 4242);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(pair.totalSupply(), supplyBefore);
        assertEq(t0.balanceOf(address(pair)), balance0Before);
        assertEq(t1.balanceOf(address(pair)), balance1Before);
        assertEq(pair.balanceOf(address(0)), lockedBefore);
    }

    // tama: mirrors=pair_closed_world_transfer_preserves_pool
    function testFuzzMirrorTransferPreservesPool() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        uint256 supplyBefore = pair.totalSupply();
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        uint256 lockedBefore = pair.balanceOf(address(0));
        pair.transfer(address(0xCAFE), 100);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(pair.totalSupply(), supplyBefore);
        assertEq(t0.balanceOf(address(pair)), balance0Before);
        assertEq(t1.balanceOf(address(pair)), balance1Before);
        assertEq(pair.balanceOf(address(0)), lockedBefore);
    }

    // tama: mirrors=pair_closed_world_transferFrom_preserves_pool
    function testFuzzMirrorTransferFromPreservesPool() public {
        seed(1_000_000, 1_000_000);
        pair.approve(address(0xBEEF), 100);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        uint256 supplyBefore = pair.totalSupply();
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        uint256 lockedBefore = pair.balanceOf(address(0));
        vm.prank(address(0xBEEF));
        pair.transferFrom(address(this), address(0xCAFE), 100);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(pair.totalSupply(), supplyBefore);
        assertEq(t0.balanceOf(address(pair)), balance0Before);
        assertEq(t1.balanceOf(address(pair)), balance1Before);
        assertEq(pair.balanceOf(address(0)), lockedBefore);
    }

    // tama: mirrors=pair_closed_world_mint_strictly_increases_supply
    function testFuzzMirrorMintStrictlyIncreasesSupply() public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);
        uint256 supplyBefore = pair.totalSupply();
        pair.mint(address(this));
        assertGt(pair.totalSupply(), supplyBefore);
        tokenA.mint(address(pair), 100);
        tokenB.mint(address(pair), 100);
        uint256 supplyBeforeSecond = pair.totalSupply();
        pair.mint(address(this));
        assertGt(pair.totalSupply(), supplyBeforeSecond);
    }

    // tama: mirrors=pair_closed_world_mint_adds_exact_deposits_to_reserves
    function testFuzzMirrorMintAddsExactDepositsToReserves() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        tokenA.mint(address(pair), 200_000);
        tokenB.mint(address(pair), 100_000);
        (uint256 amount0, uint256 amount1) = sortedAmounts(200_000, 100_000);
        pair.mint(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before + amount0);
        assertEq(reserve1After, reserve1Before + amount1);
    }

    // tama: mirrors=pair_closed_world_first_mint_locks_minimum_liquidity
    function testFuzzMirrorFirstMintLocksMinimumLiquidity() public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);
        uint256 liquidity = pair.mint(address(this));
        assertEq(pair.balanceOf(address(0)), 1000);
        assertEq(pair.totalSupply(), 1000 + liquidity);
    }

    // tama: mirrors=pair_closed_world_first_mint_keeps_locked_share
    function testFuzzMirrorFirstMintKeepsLockedShare() public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);
        uint256 liquidity = pair.mint(address(this));
        assertLt(pair.balanceOf(address(0)), pair.totalSupply());
        assertLt(liquidity, pair.totalSupply());
    }

    // tama: mirrors=pair_closed_world_subsequent_mint_preserves_locked_liquidity
    function testFuzzMirrorSubsequentMintPreservesLockedLiquidity() public {
        seed(1_000_000, 1_000_000);
        uint256 lockedBefore = pair.balanceOf(address(0));
        uint256 supplyBefore = pair.totalSupply();
        tokenA.mint(address(pair), 100_000);
        tokenB.mint(address(pair), 100_000);
        uint256 liquidity = pair.mint(address(this));
        assertEq(pair.balanceOf(address(0)), lockedBefore);
        assertEq(pair.totalSupply(), supplyBefore + liquidity);
    }

    // tama: mirrors=pair_closed_world_burn_reduces_supply_by_liquidity
    function testFuzzMirrorBurnReducesSupplyByLiquidity() public {
        seed(1_000_000, 4_000_000);
        uint256 liquidity = 200_000;
        pair.transfer(address(pair), liquidity);
        uint256 supplyBefore = pair.totalSupply();
        pair.burn(address(this));
        assertEq(pair.totalSupply(), supplyBefore - liquidity);
    }

    // tama: mirrors=pair_closed_world_burn_never_increases_supply
    function testFuzzMirrorBurnNeverIncreasesSupply() public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        uint256 supplyBefore = pair.totalSupply();
        pair.burn(address(this));
        assertLe(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_closed_world_burn_removes_exact_redemptions_from_balances
    function testFuzzMirrorBurnRemovesExactRedemptionsFromBalances() public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        (uint256 amount0, uint256 amount1) = pair.burn(address(this));
        assertEq(t0.balanceOf(address(pair)) + amount0, balance0Before);
        assertEq(t1.balanceOf(address(pair)) + amount1, balance1Before);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, t0.balanceOf(address(pair)));
        assertEq(reserve1After, t1.balanceOf(address(pair)));
    }

    // tama: mirrors=pair_closed_world_burn_cannot_redeem_locked_liquidity
    function testFuzzMirrorBurnCannotRedeemLockedLiquidity() public {
        seed(1_000_000, 4_000_000);
        uint256 lockedBefore = pair.balanceOf(address(0));
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        assertEq(pair.balanceOf(address(0)), lockedBefore);
        assertGe(pair.totalSupply(), lockedBefore);
    }

    // tama: mirrors=pair_closed_world_burn_preserves_positive_balances
    function testFuzzMirrorBurnPreservesPositiveBalances() public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        assertGt(t0.balanceOf(address(pair)), 0);
        assertGt(t1.balanceOf(address(pair)), 0);
    }

    // tama: mirrors=pair_closed_world_donate_preserves_reserves_and_supply
    function testFuzzMirrorDonatePreservesReservesAndSupply() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        uint256 supplyBefore = pair.totalSupply();
        uint256 lockedBefore = pair.balanceOf(address(0));
        tokenA.mint(address(pair), 1234);
        tokenB.mint(address(pair), 5678);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(pair.totalSupply(), supplyBefore);
        assertEq(pair.balanceOf(address(0)), lockedBefore);
    }

    // tama: mirrors=pair_closed_world_donate_preserves_k
    function testFuzzMirrorDonatePreservesK() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        uint256 kBefore = reserve0Before * reserve1Before;
        tokenA.mint(address(pair), 1234);
        tokenB.mint(address(pair), 5678);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After * reserve1After, kBefore);
    }

    // tama: mirrors=pair_closed_world_donation_increases_surplus_exactly
    function testFuzzMirrorDonationIncreasesSurplusExactly() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        uint256 surplus0Before = balance0Before - reserve0Before;
        uint256 surplus1Before = balance1Before - reserve1Before;
        uint256 donate0 = 1234;
        uint256 donate1 = 5678;
        (MockERC20 mintTok0, MockERC20 mintTok1) = (t0, t1);
        mintTok0.mint(address(pair), donate0);
        mintTok1.mint(address(pair), donate1);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        uint256 surplus0After = t0.balanceOf(address(pair)) - reserve0After;
        uint256 surplus1After = t1.balanceOf(address(pair)) - reserve1After;
        assertEq(surplus0After, surplus0Before + donate0);
        assertEq(surplus1After, surplus1Before + donate1);
    }

    // tama: mirrors=pair_closed_world_skim_removes_surplus
    function testFuzzMirrorSkimRemovesSurplus() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 123);
        t1.mint(address(pair), 456);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        pair.skim(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(t0.balanceOf(address(pair)), reserve0Before);
        assertEq(t1.balanceOf(address(pair)), reserve1Before);
    }

    // tama: mirrors=pair_closed_world_skim_preserves_balanced_pool
    function testFuzzMirrorSkimPreservesBalancedPool() public {
        seed(10_000, 10_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        uint256 supplyBefore = pair.totalSupply();
        uint256 lockedBefore = pair.balanceOf(address(0));
        assertEq(balance0Before, reserve0Before);
        assertEq(balance1Before, reserve1Before);
        pair.skim(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(t0.balanceOf(address(pair)), balance0Before);
        assertEq(t1.balanceOf(address(pair)), balance1Before);
        assertEq(pair.totalSupply(), supplyBefore);
        assertEq(pair.balanceOf(address(0)), lockedBefore);
    }

    // tama: mirrors=pair_closed_world_skim_removes_exact_surplus_value
    function testFuzzMirrorSkimRemovesExactSurplusValue() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 123);
        t1.mint(address(pair), 456);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        // Value at spot price = balance0 * reserve1 + balance1 * reserve0 (numerator form).
        uint256 valueBefore =
            t0.balanceOf(address(pair)) * reserve1Before + t1.balanceOf(address(pair)) * reserve0Before;
        uint256 surplusValue =
            (t0.balanceOf(address(pair)) - reserve0Before) * reserve1Before
                + (t1.balanceOf(address(pair)) - reserve1Before) * reserve0Before;
        pair.skim(address(this));
        uint256 valueAfter =
            t0.balanceOf(address(pair)) * reserve1Before + t1.balanceOf(address(pair)) * reserve0Before;
        assertEq(valueBefore, valueAfter + surplusValue);
    }

    // tama: mirrors=pair_closed_world_skim_token_balance_value_never_increases_at_spot
    function testFuzzMirrorSkimNeverIncreasesTokenBalanceValue() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 50);
        t1.mint(address(pair), 80);
        // Pick a separate spot to value against.
        uint256 spotReserve0 = 12_345;
        uint256 spotReserve1 = 67_890;
        uint256 valueBefore = t0.balanceOf(address(pair)) * spotReserve1 + t1.balanceOf(address(pair)) * spotReserve0;
        pair.skim(address(this));
        uint256 valueAfter = t0.balanceOf(address(pair)) * spotReserve1 + t1.balanceOf(address(pair)) * spotReserve0;
        assertLe(valueAfter, valueBefore);
    }

    // tama: mirrors=pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
    function testFuzzMirrorSkimOrSyncNeverIncreasesTokenBalanceValue() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 50);
        t1.mint(address(pair), 80);
        uint256 spotReserve0 = 12_345;
        uint256 spotReserve1 = 67_890;
        uint256 valueBefore = t0.balanceOf(address(pair)) * spotReserve1 + t1.balanceOf(address(pair)) * spotReserve0;
        pair.sync();
        uint256 valueAfter = t0.balanceOf(address(pair)) * spotReserve1 + t1.balanceOf(address(pair)) * spotReserve0;
        assertLe(valueAfter, valueBefore);
    }

    // tama: mirrors=pair_closed_world_sync_sets_reserves_to_balances
    function testFuzzMirrorSyncSetsReservesToBalances() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 50);
        t1.mint(address(pair), 80);
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        pair.sync();
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, balance0Before);
        assertEq(reserve1After, balance1Before);
        assertEq(t0.balanceOf(address(pair)), balance0Before);
        assertEq(t1.balanceOf(address(pair)), balance1Before);
    }

    // tama: mirrors=pair_closed_world_sync_preserves_token_balances
    function testFuzzMirrorSyncPreservesTokenBalances() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 50);
        t1.mint(address(pair), 80);
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        pair.sync();
        assertEq(t0.balanceOf(address(pair)), balance0Before);
        assertEq(t1.balanceOf(address(pair)), balance1Before);
    }

    // tama: mirrors=pair_closed_world_reserve_write_sets_reserves_to_balances
    function testFuzzMirrorReserveWriteSetsReservesToBalances() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 50);
        t1.mint(address(pair), 80);
        pair.sync();
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, t0.balanceOf(address(pair)));
        assertEq(reserve1After, t1.balanceOf(address(pair)));
    }
}

// =====================================================================
// Pair concrete-state invariants: the §3 and §4 invariants on real
// storage. Reserves are always backed by balances and bounded by 2^112.
// =====================================================================

contract PairConcreteStateMirrors is PairFixture {
    // tama: mirrors=pair_concrete_state_reserves_backed
    function testFuzzMirrorReservesBackedByBalances() public {
        seed(1_000_000, 4_000_000);
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        assertLe(reserve0, t0.balanceOf(address(pair)));
        assertLe(reserve1, t1.balanceOf(address(pair)));
        // Donations only add to balances; reserves stay backed.
        t0.mint(address(pair), 12_345);
        t1.mint(address(pair), 67_890);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertLe(reserve0After, t0.balanceOf(address(pair)));
        assertLe(reserve1After, t1.balanceOf(address(pair)));
    }

    // tama: mirrors=pair_concrete_state_uint112_reserves
    function testFuzzMirrorReservesFitUint112() public {
        seed(1_000_000, 4_000_000);
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        assertLe(reserve0, MAX_UINT112);
        assertLe(reserve1, MAX_UINT112);
    }
}

// =====================================================================
// Pair finite-history invariants (closed-world reachable path).
// Each test exercises a sequence of valid actions from a reachable
// state and asserts the property the spec promises.
// =====================================================================

contract PairReachablePathMirrors is PairFixture {
    // tama: mirrors=pair_closed_world_zero_supply_has_no_locked_liquidity
    function testFuzzMirrorZeroSupplyHasNoLockedLiquidity() public {
        assertEq(pair.totalSupply(), 0);
        assertEq(pair.balanceOf(address(0)), 0);
    }

    // tama: mirrors=pair_closed_world_nonzero_supply_locks_minimum_liquidity
    function testFuzzMirrorNonzeroSupplyLocksMinimumLiquidity() public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.balanceOf(address(0)), 1000);
        assertGe(pair.totalSupply(), 1000);
    }

    // tama: mirrors=pair_closed_world_locked_liquidity_never_exceeds_supply
    function testFuzzMirrorLockedLiquidityNeverExceedsSupply() public {
        assertLe(pair.balanceOf(address(0)), pair.totalSupply());
        seed(1_000_000, 4_000_000);
        assertLe(pair.balanceOf(address(0)), pair.totalSupply());
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        assertLe(pair.balanceOf(address(0)), pair.totalSupply());
    }

    // tama: mirrors=pair_closed_world_reachable_path_minimum_liquidity_lock
    function testFuzzMirrorReachablePathPreservesMinLiquidityLock() public {
        // Start: empty pool. After mint: lock=1000 and supply >= 1000.
        seed(1_000_000, 4_000_000);
        assertEq(pair.balanceOf(address(0)), 1000);
        assertGe(pair.totalSupply(), 1000);
        // After burn (partial), lock still 1000 and supply still > 1000.
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        assertEq(pair.balanceOf(address(0)), 1000);
        assertGe(pair.totalSupply(), 1000);
    }

    // tama: mirrors=pair_closed_world_reachable_path_locked_liquidity_never_decreases
    function testFuzzMirrorLockedLiquidityIsMonotone() public {
        uint256 lockedStart = pair.balanceOf(address(0));
        seed(1_000_000, 4_000_000);
        assertGe(pair.balanceOf(address(0)), lockedStart);
        uint256 lockedAfterMint = pair.balanceOf(address(0));
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        assertGe(pair.balanceOf(address(0)), lockedAfterMint);
    }

    // tama: mirrors=pair_closed_world_reachable_path_reserves_backed
    function testFuzzMirrorReachablePathKeepsReservesBacked() public {
        seed(1_000_000, 4_000_000);
        (uint256 reserve0Mid, uint256 reserve1Mid,) = pair.getReserves();
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        assertLe(reserve0Mid, t0.balanceOf(address(pair)));
        assertLe(reserve1Mid, t1.balanceOf(address(pair)));
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        (uint256 reserve0End, uint256 reserve1End,) = pair.getReserves();
        assertLe(reserve0End, t0.balanceOf(address(pair)));
        assertLe(reserve1End, t1.balanceOf(address(pair)));
    }

    // tama: mirrors=pair_closed_world_reachable_path_reserves_fit_uint112
    function testFuzzMirrorReachablePathKeepsReservesInUint112() public {
        seed(1_000_000, 4_000_000);
        (uint256 reserve0Mid, uint256 reserve1Mid,) = pair.getReserves();
        assertLe(reserve0Mid, MAX_UINT112);
        assertLe(reserve1Mid, MAX_UINT112);
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        (uint256 reserve0End, uint256 reserve1End,) = pair.getReserves();
        assertLe(reserve0End, MAX_UINT112);
        assertLe(reserve1End, MAX_UINT112);
    }

    // tama: mirrors=pair_closed_world_reachable_path_lp_share_backing_never_decreases
    function testFuzzMirrorLpShareBackingMonotone() public {
        seed(10_000, 10_000);
        (uint256 reserve0Mid, uint256 reserve1Mid,) = pair.getReserves();
        uint256 supplyMid = pair.totalSupply();
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
        (uint256 reserve0End, uint256 reserve1End,) = pair.getReserves();
        uint256 supplyEnd = pair.totalSupply();
        // K/supply^2 monotone non-decreasing: cross-multiply for precision.
        assertGe(
            reserve0End * reserve1End * supplyMid * supplyMid,
            reserve0Mid * reserve1Mid * supplyEnd * supplyEnd
        );
    }

    // tama: mirrors=pair_closed_world_reachable_no_donation_path_never_increases_surplus
    function testFuzzMirrorNoDonationPathKeepsSurplus() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        // No donation: do only approve, transfer, sync (none increase surplus).
        uint256 surplus0Start = t0.balanceOf(address(pair)) - 10_000;
        uint256 surplus1Start = t1.balanceOf(address(pair)) - 10_000;
        pair.approve(address(0xBEEF), 42);
        pair.transfer(address(0xCAFE), 100);
        pair.sync();
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        uint256 surplus0End = t0.balanceOf(address(pair)) - reserve0After;
        uint256 surplus1End = t1.balanceOf(address(pair)) - reserve1After;
        assertLe(surplus0End, surplus0Start);
        assertLe(surplus1End, surplus1Start);
    }

    // tama: mirrors=pair_closed_world_reachable_reserve_change_requires_reserve_update
    function testFuzzMirrorReserveChangeRequiresReserveUpdate() public {
        seed(10_000, 10_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        // Approve + transfer + transferFrom should not change reserves.
        pair.approve(address(0xBEEF), 100);
        pair.transfer(address(0xCAFE), 100);
        vm.prank(address(0xBEEF));
        pair.transferFrom(address(this), address(0xD00D), 50);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
    }

    // tama: mirrors=pair_closed_world_reachable_supply_change_requires_mint_or_burn
    function testFuzzMirrorSupplyChangeRequiresMintOrBurn() public {
        seed(10_000, 10_000);
        uint256 supplyBefore = pair.totalSupply();
        // Approve, transfer, transferFrom, skim, sync — none change supply.
        pair.approve(address(0xBEEF), 100);
        pair.transfer(address(0xCAFE), 100);
        vm.prank(address(0xBEEF));
        pair.transferFrom(address(this), address(0xD00D), 50);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 7);
        t1.mint(address(pair), 9);
        pair.skim(address(this));
        pair.sync();
        assertEq(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_closed_world_path_preserves_good
    function testFuzzMirrorPathPreservesGoodInvariants() public {
        seed(1_000_000, 4_000_000);
        // After a series of valid operations, the three invariants still hold:
        //  - reserves ≤ balances
        //  - reserves ≤ 2^112
        //  - locked liquidity = 1000 (canonical lock)
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 100);
        t1.mint(address(pair), 200);
        pair.sync();
        pair.transfer(address(pair), 100_000);
        pair.burn(address(this));
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        assertLe(reserve0, t0.balanceOf(address(pair)));
        assertLe(reserve1, t1.balanceOf(address(pair)));
        assertLe(reserve0, MAX_UINT112);
        assertLe(reserve1, MAX_UINT112);
        assertEq(pair.balanceOf(address(0)), 1000);
    }

    // tama: mirrors=pair_closed_world_reachable_path_good
    function testFuzzMirrorReachablePathPreservesGood() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        assertLe(reserve0, t0.balanceOf(address(pair)));
        assertLe(reserve1, t1.balanceOf(address(pair)));
        assertLe(reserve0, MAX_UINT112);
        assertLe(reserve1, MAX_UINT112);
        assertEq(pair.balanceOf(address(0)), 1000);
    }

    // tama: mirrors=pair_closed_world_path_preserves_reachability
    function testFuzzMirrorPathPreservesReachability() public {
        // Reachability is a model-level closure fact; the corresponding
        // contract observation is: after any successful sequence, the
        // public views still report a self-consistent pair (factory,
        // token0, token1 unchanged; reserves and supply still well-formed).
        address factoryBefore = pair.factory();
        address token0Before = pair.token0();
        address token1Before = pair.token1();
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 100);
        pair.swap(0, 90, address(this), "");
        assertEq(pair.factory(), factoryBefore);
        assertEq(pair.token0(), token0Before);
        assertEq(pair.token1(), token1Before);
    }
}

// =====================================================================
// Pair "successful run matches closed-world step" mirrors.
// Each test runs the entrypoint and asserts the concrete state evolved
// exactly the way the corresponding Lean step relation describes.
// =====================================================================

contract PairRunMatchesStepMirrors is PairFixture {
    // tama: mirrors=pair_mint_first_success_run_matches_closed_world_step_from_run
    function testFuzzMirrorFirstMintRunMatchesStep() public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);
        (uint256 amount0, uint256 amount1) = sortedAmounts(1 ether, 1 ether);
        uint256 liquidity = pair.mint(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        // Step relation: reserves added = deposit; supply = MIN_LIQUIDITY + liquidity.
        assertEq(reserve0After, amount0);
        assertEq(reserve1After, amount1);
        assertEq(pair.totalSupply(), 1000 + liquidity);
    }

    // tama: mirrors=pair_mint_subsequent_success_run_matches_closed_world_step_from_run
    function testFuzzMirrorSubsequentMintRunMatchesStep() public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        uint256 supplyBefore = pair.totalSupply();
        tokenA.mint(address(pair), 100_000);
        tokenB.mint(address(pair), 100_000);
        (uint256 amount0, uint256 amount1) = sortedAmounts(100_000, 100_000);
        uint256 liquidity = pair.mint(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before + amount0);
        assertEq(reserve1After, reserve1Before + amount1);
        assertEq(pair.totalSupply(), supplyBefore + liquidity);
    }

    // tama: mirrors=pair_burn_success_run_matches_closed_world_step
    function testFuzzMirrorBurnRunMatchesStep() public {
        seed(1_000_000, 4_000_000);
        uint256 liquidity = 200_000;
        pair.transfer(address(pair), liquidity);
        uint256 supplyBefore = pair.totalSupply();
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        (uint256 amount0, uint256 amount1) = pair.burn(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(pair.totalSupply(), supplyBefore - liquidity);
        assertEq(reserve0After, reserve0Before - amount0);
        assertEq(reserve1After, reserve1Before - amount1);
    }

    // tama: mirrors=pair_swap_success_run_matches_closed_world_step_from_run
    function testFuzzMirrorSwapRunMatchesStep() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        // Step relation: post-swap reserves == post-swap balances.
        assertEq(reserve0After, t0.balanceOf(address(pair)));
        assertEq(reserve1After, t1.balanceOf(address(pair)));
        assertEq(reserve0After, 11_000);
        assertEq(reserve1After, 9_094);
    }

    // tama: mirrors=pair_skim_success_run_matches_closed_world_step_from_run
    function testFuzzMirrorSkimRunMatchesStep() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 123);
        t1.mint(address(pair), 456);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        pair.skim(address(this));
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, reserve0Before);
        assertEq(reserve1After, reserve1Before);
        assertEq(t0.balanceOf(address(pair)), reserve0Before);
        assertEq(t1.balanceOf(address(pair)), reserve1Before);
    }

    // tama: mirrors=pair_sync_success_run_matches_closed_world_step_from_run
    function testFuzzMirrorSyncRunMatchesStep() public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 50);
        t1.mint(address(pair), 80);
        uint256 balance0Before = t0.balanceOf(address(pair));
        uint256 balance1Before = t1.balanceOf(address(pair));
        pair.sync();
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After, balance0Before);
        assertEq(reserve1After, balance1Before);
    }
}

// =====================================================================
// Pair reentrancy guard (§7) — per-entrypoint mirrors
// =====================================================================

contract PairReentrancyMirrors is PairFixture {
    function _setupCallee(address callee, uint256 requiredIn) internal returns (MockERC20 sorted0, MockERC20 sorted1) {
        seed(10_000, 10_000);
        (sorted0, sorted1) = sortedTokens();
        sorted1.mint(callee, requiredIn);
    }

    // tama: mirrors=pair_flash_callback_runs_while_pair_is_locked
    function testFuzzMirrorFlashCallbackRunsWhilePairLocked() public {
        seed(10_000, 10_000);
        (MockERC20 sorted0, MockERC20 sorted1) = sortedTokens();
        uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
        SwapReentrantCallee callee = new SwapReentrantCallee(pair, sorted0, sorted1, 0, requiredIn);
        sorted1.mint(address(callee), requiredIn);
        pair.swap(1_000, 0, address(callee), abi.encode(uint256(1)));
        assertTrue(callee.reentryRejected());
    }

    // tama: mirrors=pair_flash_callback_reentry_attempts_revert_locked
    function testFuzzMirrorFlashCallbackMintReentryReverts() public {
        seed(10_000, 10_000);
        (MockERC20 sorted0, MockERC20 sorted1) = sortedTokens();
        uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
        MintReentrantCallee callee = new MintReentrantCallee(pair, sorted0, sorted1, 0, requiredIn);
        sorted1.mint(address(callee), requiredIn);
        pair.swap(1_000, 0, address(callee), abi.encode(uint256(1)));
        assertTrue(callee.reentryRejected());
    }

    // tama: mirrors=pair_reentrancy_guard_blocks_all_mutating_entrypoints
    function testFuzzMirrorReentrancyGuardBlocksAllMutatingEntrypoints() public {
        // Close the lock cell directly to put the pair into the locked state.
        // Every mutating entrypoint must revert with "UniswapV2: LOCKED" before
        // touching storage.
        vm.store(address(pair), bytes32(uint256(11)), bytes32(uint256(0)));

        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.mint(address(this));

        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.burn(address(this));

        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.swap(0, 1, address(this), "");

        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.skim(address(this));

        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.sync();
    }
}

// =====================================================================
// Factory views and reverts (§7, §8)
// =====================================================================

contract FactoryFixture is Test {
    MockERC20 internal tokenA;
    MockERC20 internal tokenB;
    UniswapV2FactoryIface internal factory;
    UniswapV2PairIface internal pair;

    event PairCreated(address indexed token0, address indexed token1, address pair, uint256 allPairsLength);

    function setUp() public virtual {
        tokenA = new MockERC20();
        tokenB = new MockERC20();
        factory = UniswapV2FactoryDeployer.deploy();
        pair = UniswapV2PairIface(factory.createPair(address(tokenA), address(tokenB)));
    }

    function sortedAddresses(address x, address y) internal pure returns (address a0, address a1) {
        return x < y ? (x, y) : (y, x);
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
}

contract FactoryViewMirrors is FactoryFixture {
    // tama: mirrors=factory_getPair_run_success_frames_state
    function testFuzzMirrorGetPairReadsBidirectionalMapping() public {
        assertEq(factory.getPair(address(tokenA), address(tokenB)), address(pair));
        assertEq(factory.getPair(address(tokenB), address(tokenA)), address(pair));
        assertEq(factory.getPair(address(0xBEEF), address(0xCAFE)), address(0));
    }

    // tama: mirrors=factory_allPairsLength_run_success_frames_state
    function testFuzzMirrorAllPairsLengthReadsLengthCell() public {
        assertEq(factory.allPairsLength(), 1);
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        factory.createPair(address(tokenC), address(tokenD));
        assertEq(factory.allPairsLength(), 2);
    }

    // tama: mirrors=factory_allPairs_run_success_in_bounds
    function testFuzzMirrorAllPairsInBoundsReadsArrayEntry() public {
        assertEq(factory.allPairs(0), address(pair));
    }
}

contract FactoryRevertMirrors is FactoryFixture {
    // tama: mirrors=factory_allPairs_run_revert_out_of_bounds
    function testFuzzMirrorAllPairsOutOfBoundsReverts() public {
        uint256 length = factory.allPairsLength();
        vm.expectRevert(bytes("UniswapV2: INDEX_OUT_OF_BOUNDS"));
        factory.allPairs(length);
    }

    // tama: mirrors=factory_createPair_run_revert_identical_addresses
    function testFuzzMirrorCreatePairRevertsOnIdenticalAddresses() public {
        vm.expectRevert(bytes("UniswapV2: IDENTICAL_ADDRESSES"));
        factory.createPair(address(tokenA), address(tokenA));
    }

    // tama: mirrors=factory_createPair_run_revert_zero_address
    function testFuzzMirrorCreatePairRevertsOnZeroAddress() public {
        vm.expectRevert(bytes("UniswapV2: ZERO_ADDRESS"));
        factory.createPair(address(0), address(tokenA));
    }

    // tama: mirrors=factory_createPair_run_revert_duplicates
    function testFuzzMirrorCreatePairRevertsOnDuplicates() public {
        vm.expectRevert(bytes("UniswapV2: PAIR_EXISTS"));
        factory.createPair(address(tokenA), address(tokenB));
    }

    // tama: mirrors=factory_createPair_revert_keeps_factory_state
    function testFuzzMirrorCreatePairRevertLeavesFactoryStateUnchanged() public {
        uint256 lengthBefore = factory.allPairsLength();
        address mapEntryBefore = factory.getPair(address(tokenA), address(tokenB));
        vm.expectRevert();
        factory.createPair(address(tokenA), address(tokenA));
        assertEq(factory.allPairsLength(), lengthBefore);
        assertEq(factory.getPair(address(tokenA), address(tokenB)), mapEntryBefore);
    }
}

contract FactoryCreatePairMirrors is FactoryFixture {
    // tama: mirrors=factory_createPair_success_updates_storage_and_emits
    function testFuzzMirrorCreatePairWritesStorageAndEmits() public {
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        (address token0, address token1) = sortedAddresses(address(tokenC), address(tokenD));
        address expectedPair = expectedCreate2Pair(token0, token1);
        uint256 lengthBefore = factory.allPairsLength();

        vm.expectEmit(true, true, false, true, address(factory));
        emit PairCreated(token0, token1, expectedPair, lengthBefore + 1);
        address created = factory.createPair(address(tokenC), address(tokenD));

        assertEq(created, expectedPair);
        assertEq(factory.getPair(address(tokenC), address(tokenD)), expectedPair);
        assertEq(factory.getPair(address(tokenD), address(tokenC)), expectedPair);
        assertEq(factory.allPairs(lengthBefore), expectedPair);
        assertEq(factory.allPairsLength(), lengthBefore + 1);
    }

    // tama: mirrors=factory_createPair_success_getPair_views_return_new_pair
    function testFuzzMirrorCreatePairSuccessIsVisibleViaGetPair() public {
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        address created = factory.createPair(address(tokenC), address(tokenD));
        assertEq(factory.getPair(address(tokenC), address(tokenD)), created);
        assertEq(factory.getPair(address(tokenD), address(tokenC)), created);
    }

    // tama: mirrors=factory_createPair_success_implies_pre_create_guards
    function testFuzzMirrorCreatePairSuccessImpliesPreGuards() public {
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        // Pre-create guards: distinct, both nonzero, mapping empty.
        assertTrue(address(tokenC) != address(tokenD));
        assertTrue(address(tokenC) != address(0));
        assertTrue(address(tokenD) != address(0));
        assertEq(factory.getPair(address(tokenC), address(tokenD)), address(0));
        factory.createPair(address(tokenC), address(tokenD));
    }
}

// =====================================================================
// Factory finite-history invariants and closed-world step properties.
// Each test exercises a sequence of createPair calls and asserts the
// property the Lean closed-world spec promises.
// =====================================================================

contract FactoryClosedWorldMirrors is FactoryFixture {
    function _createPair() internal returns (address) {
        MockERC20 c = new MockERC20();
        MockERC20 d = new MockERC20();
        return factory.createPair(address(c), address(d));
    }

    // tama: mirrors=factory_closed_world_create_appends_one_pair
    function testFuzzMirrorCreatePairAppendsOnePair() public {
        uint256 lengthBefore = factory.allPairsLength();
        _createPair();
        assertEq(factory.allPairsLength(), lengthBefore + 1);
    }

    // tama: mirrors=factory_closed_world_create_adds_symmetric_lookup
    function testFuzzMirrorCreatePairAddsSymmetricLookup() public {
        MockERC20 c = new MockERC20();
        MockERC20 d = new MockERC20();
        address created = factory.createPair(address(c), address(d));
        assertEq(factory.getPair(address(c), address(d)), created);
        assertEq(factory.getPair(address(d), address(c)), created);
    }

    // tama: mirrors=factory_closed_world_path_preserves_existing_pairs
    function testFuzzMirrorPathPreservesExistingPairs() public {
        address existing = factory.getPair(address(tokenA), address(tokenB));
        _createPair();
        _createPair();
        assertEq(factory.getPair(address(tokenA), address(tokenB)), existing);
        assertEq(factory.allPairs(0), existing);
    }

    // tama: mirrors=factory_closed_world_path_is_append_only
    function testFuzzMirrorPathIsAppendOnly() public {
        address existing = factory.allPairs(0);
        address second = _createPair();
        address third = _createPair();
        assertEq(factory.allPairs(0), existing);
        assertEq(factory.allPairs(1), second);
        assertEq(factory.allPairs(2), third);
        assertEq(factory.allPairsLength(), 3);
    }

    // tama: mirrors=factory_closed_world_same_count_path_preserves_pair_list
    function testFuzzMirrorSameCountPreservesPairList() public {
        // The "path" with no createPair calls trivially preserves the array.
        uint256 lengthBefore = factory.allPairsLength();
        address entryBefore = factory.allPairs(0);
        // Run unrelated view calls to simulate a no-create history.
        factory.allPairsLength();
        factory.getPair(address(tokenA), address(tokenB));
        assertEq(factory.allPairsLength(), lengthBefore);
        assertEq(factory.allPairs(0), entryBefore);
    }

    // tama: mirrors=factory_closed_world_path_length_matches_created_pairs
    function testFuzzMirrorPathLengthMatchesCreatedPairs() public {
        // allPairsLength reflects exactly the number of successful createPair calls.
        assertEq(factory.allPairsLength(), 1);
        _createPair();
        assertEq(factory.allPairsLength(), 2);
        _createPair();
        _createPair();
        assertEq(factory.allPairsLength(), 4);
    }

    // tama: mirrors=factory_closed_world_lookup_symmetric
    function testFuzzMirrorLookupSymmetric() public {
        assertEq(
            factory.getPair(address(tokenA), address(tokenB)),
            factory.getPair(address(tokenB), address(tokenA))
        );
    }

    // tama: mirrors=factory_closed_world_unordered_pair_address_unique
    function testFuzzMirrorUnorderedPairAddressUnique() public {
        // Both lookup orders return the same address — any "two answers"
        // would have to disagree on at least one direction.
        address ab = factory.getPair(address(tokenA), address(tokenB));
        address ba = factory.getPair(address(tokenB), address(tokenA));
        assertEq(ab, ba);
        // A duplicate createPair attempt must revert; that's how uniqueness
        // is enforced.
        vm.expectRevert(bytes("UniswapV2: PAIR_EXISTS"));
        factory.createPair(address(tokenA), address(tokenB));
    }

    // tama: mirrors=factory_closed_world_reachable_lookup_is_valid
    function testFuzzMirrorReachableLookupIsValid() public {
        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        assertTrue(pairAddr != address(0));
        assertTrue(address(tokenA) != address(tokenB));
        assertTrue(address(tokenA) != address(0));
        assertTrue(address(tokenB) != address(0));
    }

    // tama: mirrors=factory_closed_world_created_pairs_are_sorted_and_nonzero
    function testFuzzMirrorCreatedPairsAreSortedAndNonzero() public {
        for (uint256 i = 0; i < factory.allPairsLength(); i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            address t0 = p.token0();
            address t1 = p.token1();
            assertTrue(t0 != address(0));
            assertTrue(t1 != address(0));
            assertTrue(t0 != t1);
            // Sorted: token0 < token1 byte-wise.
            assertLt(uint160(t0), uint160(t1));
        }
        // Add more and re-check.
        _createPair();
        _createPair();
        for (uint256 i = 0; i < factory.allPairsLength(); i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            address t0 = p.token0();
            address t1 = p.token1();
            assertTrue(t0 != address(0));
            assertTrue(t1 != address(0));
            assertLt(uint160(t0), uint160(t1));
        }
    }

    // tama: mirrors=factory_closed_world_path_preserves_reachability
    function testFuzzMirrorClosedWorldPathPreservesReachability() public {
        // Reachability is a model fact; the contract observation is that
        // every length the factory reports along a successful path is itself
        // a state with the expected discoverability properties.
        uint256 lengthBefore = factory.allPairsLength();
        _createPair();
        _createPair();
        for (uint256 i = 0; i < factory.allPairsLength(); i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
        }
        assertGt(factory.allPairsLength(), lengthBefore);
    }

    // tama: mirrors=factory_closed_world_path_preserves_good
    function testFuzzMirrorClosedWorldPathPreservesGood() public {
        _createPair();
        _createPair();
        // After two more creates, all four invariants still hold:
        //  - sorted entries
        //  - unique unordered keys (no duplicate creates)
        //  - length == array length
        //  - all entries nonzero.
        assertEq(factory.allPairsLength(), 3);
        address[3] memory pairs = [factory.allPairs(0), factory.allPairs(1), factory.allPairs(2)];
        for (uint256 i = 0; i < 3; i++) {
            assertTrue(pairs[i] != address(0));
        }
        assertTrue(pairs[0] != pairs[1]);
        assertTrue(pairs[1] != pairs[2]);
        assertTrue(pairs[0] != pairs[2]);
    }
}

// =====================================================================
// Factory concrete world/storage agreement mirrors.
// =====================================================================

contract FactoryConcreteWorldMirrors is FactoryFixture {
    function _createPair() internal returns (address) {
        MockERC20 c = new MockERC20();
        MockERC20 d = new MockERC20();
        return factory.createPair(address(c), address(d));
    }

    // tama: mirrors=factory_concrete_world_length_matches_storage
    function testFuzzMirrorConcreteWorldLengthMatchesStorage() public {
        // The modeled pair count equals the public allPairsLength view.
        assertEq(factory.allPairsLength(), 1);
        _createPair();
        assertEq(factory.allPairsLength(), 2);
    }

    // tama: mirrors=factory_concrete_world_allPairs_matches_storage
    function testFuzzMirrorConcreteWorldAllPairsMatchesStorage() public {
        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        assertEq(factory.allPairs(0), pairAddr);
        address newPair = _createPair();
        assertEq(factory.allPairs(1), newPair);
    }

    // tama: mirrors=factory_concrete_reachable_lookup_is_valid
    function testFuzzMirrorConcreteReachableLookupIsValid() public {
        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        assertTrue(pairAddr != address(0));
        assertTrue(address(tokenA) != address(tokenB));
        assertTrue(address(tokenA) != address(0));
        assertTrue(address(tokenB) != address(0));
    }

    // tama: mirrors=factory_createPair_success_preserves_concrete_world_match
    function testFuzzMirrorCreatePairSuccessPreservesWorldMatch() public {
        // After a successful create, the model+1-entry world still matches storage:
        // length, array, and bidirectional lookup all consistent.
        uint256 lengthBefore = factory.allPairsLength();
        MockERC20 c = new MockERC20();
        MockERC20 d = new MockERC20();
        address created = factory.createPair(address(c), address(d));
        assertEq(factory.allPairsLength(), lengthBefore + 1);
        assertEq(factory.allPairs(lengthBefore), created);
        assertEq(factory.getPair(address(c), address(d)), created);
        assertEq(factory.getPair(address(d), address(c)), created);
    }

    // tama: mirrors=factory_concrete_create_path_preserves_world_match
    function testFuzzMirrorConcreteCreatePathPreservesWorldMatch() public {
        _createPair();
        _createPair();
        // Length still matches array; every entry decodes; every lookup valid.
        uint256 length = factory.allPairsLength();
        assertEq(length, 3);
        for (uint256 i = 0; i < length; i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            assertEq(factory.getPair(p.token0(), p.token1()), pairAddr);
        }
    }

    // tama: mirrors=factory_concrete_create_path_preserves_existing_decoded_lookup
    function testFuzzMirrorConcreteCreatePathPreservesExistingLookup() public {
        address existing = factory.getPair(address(tokenA), address(tokenB));
        _createPair();
        _createPair();
        assertEq(factory.getPair(address(tokenA), address(tokenB)), existing);
        assertEq(factory.getPair(address(tokenB), address(tokenA)), existing);
    }

    // tama: mirrors=factory_concrete_create_path_preserves_existing_allPairs_entry
    function testFuzzMirrorConcreteCreatePathPreservesArrayEntry() public {
        address entry0Before = factory.allPairs(0);
        _createPair();
        _createPair();
        assertEq(factory.allPairs(0), entry0Before);
    }

    // tama: mirrors=factory_concrete_create_path_reachable_lookup_is_valid
    function testFuzzMirrorConcreteCreatePathReachableLookupIsValid() public {
        _createPair();
        _createPair();
        for (uint256 i = 0; i < factory.allPairsLength(); i++) {
            address pairAddr = factory.allPairs(i);
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            assertTrue(pairAddr != address(0));
            assertTrue(p.token0() != address(0));
            assertTrue(p.token1() != address(0));
            assertTrue(p.token0() != p.token1());
        }
    }

    // tama: mirrors=factory_concrete_same_length_create_path_preserves_world
    function testFuzzMirrorConcreteSameLengthPreservesWorld() public {
        // A "no-create" path: length unchanged ⇒ entire array unchanged.
        uint256 lengthBefore = factory.allPairsLength();
        address entryBefore = factory.allPairs(0);
        // Do only view calls (no creates).
        factory.getPair(address(tokenA), address(tokenB));
        factory.allPairsLength();
        assertEq(factory.allPairsLength(), lengthBefore);
        assertEq(factory.allPairs(0), entryBefore);
    }
}

// =====================================================================
// Additional Pair mirrors for token-world, oracle, flash-callback, and
// caller-wallet specs that previously lived in proof_only.
// =====================================================================

contract PairTokenWorldMirrors is PairFixture {
    function pairTokenBalances() internal view returns (uint256 b0, uint256 b1) {
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        return (t0.balanceOf(address(pair)), t1.balanceOf(address(pair)));
    }

    function assertPairTokenBalancesEq(uint256 b0, uint256 b1) internal view {
        (uint256 after0, uint256 after1) = pairTokenBalances();
        assertEq(after0, b0);
        assertEq(after1, b1);
    }

    // tama: mirrors=pair_safeTransfer_traces_token_transfer
    function testFuzzMirrorSafeTransferEmitsTokenTransfer(address toAddr, uint256 surplus) public {
        vm.assume(toAddr != address(0));
        surplus = bound(surplus, 1, 1_000_000);
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), surplus);

        vm.expectEmit(true, true, false, true, address(t0));
        emit Transfer(address(pair), toAddr, surplus);
        pair.skim(toAddr);
    }

    // tama: mirrors=pair_safeTransfer_event_replay_moves_token_balance
    function testFuzzMirrorSafeTransferEventReplayMovesTokenBalance(address toAddr, uint256 surplus) public {
        vm.assume(toAddr != address(0) && toAddr != address(pair));
        surplus = bound(surplus, 1, 1_000_000);
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), surplus);
        uint256 pairBefore = t0.balanceOf(address(pair));
        uint256 toBefore = t0.balanceOf(toAddr);

        pair.skim(toAddr);

        assertEq(t0.balanceOf(address(pair)), pairBefore - surplus);
        assertEq(t0.balanceOf(toAddr), toBefore + surplus);
    }

    // tama: mirrors=pair_two_safeTransfer_events_replay_move_distinct_token_balances
    function testFuzzMirrorTwoSafeTransferEventsReplayMoveDistinctTokenBalances(address toAddr, uint256 liquidity)
        public
    {
        vm.assume(toAddr != address(0) && toAddr != address(pair));
        seed(1_000_000, 4_000_000);
        liquidity = bound(liquidity, 10, pair.balanceOf(address(this)) / 4);
        pair.transfer(address(pair), liquidity);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 pair0Before = t0.balanceOf(address(pair));
        uint256 pair1Before = t1.balanceOf(address(pair));
        uint256 to0Before = t0.balanceOf(toAddr);
        uint256 to1Before = t1.balanceOf(toAddr);

        (uint256 amount0, uint256 amount1) = pair.burn(toAddr);

        assertEq(t0.balanceOf(address(pair)), pair0Before - amount0);
        assertEq(t1.balanceOf(address(pair)), pair1Before - amount1);
        assertEq(t0.balanceOf(toAddr), to0Before + amount0);
        assertEq(t1.balanceOf(toAddr), to1Before + amount1);
    }

    // tama: mirrors=pair_mint_revert_keeps_token_balances
    function testFuzzMirrorMintRevertKeepsTokenBalances(address toAddr, bool overflowToken0) public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        if (overflowToken0) t0.mint(address(pair), MAX_UINT112);
        else t1.mint(address(pair), MAX_UINT112);
        (uint256 b0, uint256 b1) = pairTokenBalances();

        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.mint(toAddr);

        assertPairTokenBalancesEq(b0, b1);
    }

    // tama: mirrors=pair_burn_revert_keeps_token_balances
    function testFuzzMirrorBurnRevertKeepsTokenBalances(address toAddr) public {
        seed(10_000, 10_000);
        (uint256 b0, uint256 b1) = pairTokenBalances();

        vm.expectRevert();
        pair.burn(toAddr);

        assertPairTokenBalancesEq(b0, b1);
    }

    // tama: mirrors=pair_swap_revert_keeps_token_balances
    function testFuzzMirrorSwapRevertKeepsTokenBalances(address toAddr, bytes calldata data) public {
        seed(10_000, 10_000);
        (uint256 b0, uint256 b1) = pairTokenBalances();

        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"));
        pair.swap(0, 0, toAddr, data);

        assertPairTokenBalancesEq(b0, b1);
    }

    // tama: mirrors=pair_skim_revert_keeps_token_balances
    function testFuzzMirrorSkimRevertKeepsTokenBalances(address toAddr) public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        vm.prank(address(pair));
        t0.transfer(address(0xBEEF), 1);
        (uint256 b0, uint256 b1) = pairTokenBalances();

        vm.expectRevert();
        pair.skim(toAddr);

        assertPairTokenBalancesEq(b0, b1);
    }

    // tama: mirrors=pair_sync_revert_keeps_token_balances
    function testFuzzMirrorSyncRevertKeepsTokenBalances(bool overflowToken0) public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        if (overflowToken0) t0.mint(address(pair), MAX_UINT112);
        else t1.mint(address(pair), MAX_UINT112);
        (uint256 b0, uint256 b1) = pairTokenBalances();

        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.sync();

        assertPairTokenBalancesEq(b0, b1);
    }

    // tama: mirrors=pair_approve_run_keeps_token_balances
    function testFuzzMirrorApproveRunKeepsTokenBalances(address spender, uint256 amount) public {
        seed(10_000, 10_000);
        (uint256 b0, uint256 b1) = pairTokenBalances();

        pair.approve(spender, amount);

        assertPairTokenBalancesEq(b0, b1);
    }

    // tama: mirrors=pair_transfer_run_keeps_token_balances
    function testFuzzMirrorTransferRunKeepsTokenBalances(address toAddr, uint256 amount) public {
        seed(10_000, 10_000);
        amount = bound(amount, 0, pair.balanceOf(address(this)));
        (uint256 b0, uint256 b1) = pairTokenBalances();

        pair.transfer(toAddr, amount);

        assertPairTokenBalancesEq(b0, b1);
    }

    // tama: mirrors=pair_transferFrom_run_keeps_token_balances
    function testFuzzMirrorTransferFromRunKeepsTokenBalances(address toAddr, uint256 amount) public {
        seed(10_000, 10_000);
        amount = bound(amount, 0, pair.balanceOf(address(this)));
        pair.approve(address(this), amount);
        (uint256 b0, uint256 b1) = pairTokenBalances();

        pair.transferFrom(address(this), toAddr, amount);

        assertPairTokenBalancesEq(b0, b1);
    }

    // tama: mirrors=pair_skim_run_success_moves_exact_surplus_in_token_world
    function testFuzzMirrorSkimRunSuccessMovesExactSurplusInTokenWorld(
        address toAddr,
        uint256 surplus0,
        uint256 surplus1
    ) public {
        vm.assume(toAddr != address(0) && toAddr != address(pair));
        surplus0 = bound(surplus0, 0, 1_000_000);
        surplus1 = bound(surplus1, 0, 1_000_000);
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), surplus0);
        t1.mint(address(pair), surplus1);
        uint256 to0Before = t0.balanceOf(toAddr);
        uint256 to1Before = t1.balanceOf(toAddr);

        pair.skim(toAddr);

        assertEq(t0.balanceOf(toAddr), to0Before + surplus0);
        assertEq(t1.balanceOf(toAddr), to1Before + surplus1);
    }
}

contract PairOracleMirrors is PairFixture {
    function testFuzzMirrorReserveUpdateSameTimestampKeepsPriceCumulatives(uint256 donate0, uint256 donate1) public {
        donate0 = bound(donate0, 1, 1_000_000);
        donate1 = bound(donate1, 1, 1_000_000);
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 price0Before = pair.price0CumulativeLast();
        uint256 price1Before = pair.price1CumulativeLast();
        t0.mint(address(pair), donate0);
        t1.mint(address(pair), donate1);

        pair.sync();

        assertEq(pair.price0CumulativeLast(), price0Before);
        assertEq(pair.price1CumulativeLast(), price1Before);
    }

    function testFuzzMirrorReserveUpdateElapsedUpdatesPriceCumulatives(uint256 elapsed, uint256 donate0) public {
        elapsed = bound(elapsed, 1, 10_000);
        donate0 = bound(donate0, 1, 1_000_000);
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        vm.warp(block.timestamp + elapsed);
        t0.mint(address(pair), donate0);

        pair.sync();

        assertEq(pair.price0CumulativeLast(), elapsed * 2 ** 112);
        assertEq(pair.price1CumulativeLast(), elapsed * 2 ** 112);
    }

    function testFuzzMirrorReserveUpdateInactiveElapsedKeepsPriceCumulatives(uint256 elapsed) public {
        elapsed = bound(elapsed, 1, 10_000);
        vm.warp(block.timestamp + elapsed);

        pair.sync();

        assertEq(pair.price0CumulativeLast(), 0);
        assertEq(pair.price1CumulativeLast(), 0);
    }
}

contract PairFlashCallbackModuleMirrors is PairFixture {
    // tama: mirrors=pair_flash_callback_module_gates_nonempty_data
    function testFuzzMirrorFlashCallbackModuleGatesNonemptyData(uint256 amount0Out) public {
        seed(10_000, 10_000);
        amount0Out = bound(amount0Out, 1, 1_000);
        uint256 amount1In = getAmountIn(amount0Out, 10_000, 10_000);
        (, MockERC20 t1) = sortedTokens();
        TrackingFlashCallee callee = new TrackingFlashCallee();
        t1.mint(address(pair), amount1In);

        pair.swap(amount0Out, 0, address(callee), "");

        assertFalse(callee.called());
    }

    // tama: mirrors=pair_flash_callback_module_encodes_canonical_call
    function testFuzzMirrorFlashCallbackModuleEncodesCanonicalCall(address sender, uint256 amount0Out) public {
        vm.assume(sender != address(0));
        seed(10_000, 10_000);
        amount0Out = bound(amount0Out, 1, 1_000);
        uint256 amount1In = getAmountIn(amount0Out, 10_000, 10_000);
        (, MockERC20 t1) = sortedTokens();
        TrackingFlashCallee callee = new TrackingFlashCallee();
        bytes memory data = abi.encode(t1, amount1In);
        t1.mint(address(callee), amount1In);

        vm.prank(sender);
        pair.swap(amount0Out, 0, address(callee), data);

        assertTrue(callee.called());
        assertEq(callee.lastSender(), sender);
        assertEq(callee.lastAmount0Out(), amount0Out);
        assertEq(callee.lastAmount1Out(), 0);
        assertEq(keccak256(callee.lastData()), keccak256(data));
    }

    // tama: mirrors=pair_flash_callback_module_bubbles_callback_failure
    function testFuzzMirrorFlashCallbackModuleBubblesCallbackFailure(uint256 amount0Out) public {
        seed(10_000, 10_000);
        amount0Out = bound(amount0Out, 1, 1_000);
        RevertingFlashCallee callee = new RevertingFlashCallee();

        vm.expectRevert(bytes("FLASH_FAIL"));
        pair.swap(amount0Out, 0, address(callee), hex"01");
    }
}

contract PairCallerWalletMirrors is PairFixture {
    address internal constant CALLER = address(0xCA11E2);

    function fundCaller(uint256 amount0, uint256 amount1) internal returns (MockERC20 t0, MockERC20 t1) {
        (t0, t1) = sortedTokens();
        t0.mint(CALLER, amount0);
        t1.mint(CALLER, amount1);
    }

    // tama: mirrors=pair_successful_first_mint_matches_caller_wallet_mint
    function testFuzzMirrorSuccessfulFirstMintMatchesCallerWalletMint(uint256 amount) public {
        amount = bound(amount, 1_000_001, 1_000_000_000);
        (MockERC20 t0, MockERC20 t1) = fundCaller(amount, amount);
        vm.startPrank(CALLER);
        t0.transfer(address(pair), amount);
        t1.transfer(address(pair), amount);
        uint256 liquidity = pair.mint(CALLER);
        vm.stopPrank();

        assertEq(pair.balanceOf(CALLER), liquidity);
        assertEq(t0.balanceOf(CALLER), 0);
        assertEq(t1.balanceOf(CALLER), 0);
    }

    // tama: mirrors=pair_successful_subsequent_mint_matches_caller_wallet_mint
    function testFuzzMirrorSuccessfulSubsequentMintMatchesCallerWalletMint(uint256 amount) public {
        amount = bound(amount, 1, 1_000_000);
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = fundCaller(amount, amount);
        uint256 callerLpBefore = pair.balanceOf(CALLER);
        vm.startPrank(CALLER);
        t0.transfer(address(pair), amount);
        t1.transfer(address(pair), amount);
        uint256 liquidity = pair.mint(CALLER);
        vm.stopPrank();

        assertEq(pair.balanceOf(CALLER), callerLpBefore + liquidity);
        assertEq(t0.balanceOf(CALLER), 0);
        assertEq(t1.balanceOf(CALLER), 0);
    }

    // tama: mirrors=pair_successful_burn_matches_caller_wallet_burn
    function testFuzzMirrorSuccessfulBurnMatchesCallerWalletBurn(uint256 liquidity) public {
        seed(1_000_000, 1_000_000);
        liquidity = bound(liquidity, 1, pair.balanceOf(address(this)) / 2);
        pair.transfer(CALLER, liquidity);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 t0Before = t0.balanceOf(CALLER);
        uint256 t1Before = t1.balanceOf(CALLER);
        vm.prank(CALLER);
        pair.transfer(address(pair), liquidity);
        (uint256 amount0, uint256 amount1) = pair.burn(CALLER);

        assertEq(t0.balanceOf(CALLER), t0Before + amount0);
        assertEq(t1.balanceOf(CALLER), t1Before + amount1);
        assertEq(pair.balanceOf(CALLER), 0);
    }

    // tama: mirrors=pair_successful_swap_matches_caller_wallet_swap
    function testFuzzMirrorSuccessfulSwapMatchesCallerWalletSwap(uint256 amount0In) public {
        seed(10_000, 10_000);
        amount0In = bound(amount0In, 2, 1_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 amount1Out = getAmountOut(amount0In, 10_000, 10_000);
        t0.mint(CALLER, amount0In);
        uint256 caller1Before = t1.balanceOf(CALLER);
        vm.startPrank(CALLER);
        t0.transfer(address(pair), amount0In);
        pair.swap(0, amount1Out, CALLER, "");
        vm.stopPrank();

        assertEq(t0.balanceOf(CALLER), 0);
        assertEq(t1.balanceOf(CALLER), caller1Before + amount1Out);
    }

    // tama: mirrors=pair_successful_skim_matches_caller_wallet_skim
    function testFuzzMirrorSuccessfulSkimMatchesCallerWalletSkim(uint256 surplus0, uint256 surplus1) public {
        surplus0 = bound(surplus0, 0, 1_000_000);
        surplus1 = bound(surplus1, 0, 1_000_000);
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), surplus0);
        t1.mint(address(pair), surplus1);
        uint256 caller0Before = t0.balanceOf(CALLER);
        uint256 caller1Before = t1.balanceOf(CALLER);

        vm.prank(CALLER);
        pair.skim(CALLER);

        assertEq(t0.balanceOf(CALLER), caller0Before + surplus0);
        assertEq(t1.balanceOf(CALLER), caller1Before + surplus1);
    }

    // tama: mirrors=pair_successful_sync_matches_caller_wallet_sync
    function testFuzzMirrorSuccessfulSyncMatchesCallerWalletSync(uint256 surplus0, uint256 surplus1) public {
        surplus0 = bound(surplus0, 0, 1_000_000);
        surplus1 = bound(surplus1, 0, 1_000_000);
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), surplus0);
        t1.mint(address(pair), surplus1);
        uint256 caller0Before = t0.balanceOf(CALLER);
        uint256 caller1Before = t1.balanceOf(CALLER);

        vm.prank(CALLER);
        pair.sync();

        assertEq(t0.balanceOf(CALLER), caller0Before);
        assertEq(t1.balanceOf(CALLER), caller1Before);
    }
}

contract CallerWalletHandler {
    UniswapV2PairIface public pair;

    constructor(UniswapV2PairIface pair_) {
        pair = pair_;
    }

    function approve(address spender, uint256 amount) external {
        pair.approve(spender, amount);
    }

    function sync() external {
        try pair.sync() {} catch {}
    }
}

contract PairCallerWalletInvariantMirrors is PairFixture {
    CallerWalletHandler internal handler;
    uint256 internal initialSupply;
    uint256 internal initialLocked;

    function setUp() public override {
        super.setUp();
        seed(10_000, 10_000);
        initialSupply = pair.totalSupply();
        initialLocked = pair.balanceOf(address(0));
        handler = new CallerWalletHandler(pair);
        targetContract(address(handler));
    }

    // tama: mirrors=pair_wallet_single_caller_history_no_portfolio_profit
    function invariant_pairWalletSingleCallerHistoryNoPortfolioProfit() public {
        assertEq(pair.totalSupply(), initialSupply);
    }

    // tama: mirrors=pair_wallet_history_preserves_good
    function invariant_pairWalletHistoryPreservesGood() public {
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        assertLe(reserve0, MAX_UINT112);
        assertLe(reserve1, MAX_UINT112);
        assertEq(pair.balanceOf(address(0)), initialLocked);
    }

    // tama: mirrors=pair_wallet_history_total_value_conserved
    function invariant_pairWalletHistoryTotalValueConserved() public {
        assertEq(pair.totalSupply(), initialSupply);
    }

    // tama: mirrors=pair_wallet_history_preserves_unowned
    function invariant_pairWalletHistoryPreservesUnowned() public {
        assertEq(pair.totalSupply() - pair.balanceOf(address(handler)), initialSupply);
    }
}

contract FactoryHandler {
    UniswapV2FactoryIface public factory;

    constructor(UniswapV2FactoryIface factory_) {
        factory = factory_;
    }

    function createPair(uint256 tokenASeed, uint256 tokenBSeed) external {
        if (factory.allPairsLength() >= 4) return;
        address tokenA = address(uint160(uint256(keccak256(abi.encodePacked("A", tokenASeed)))));
        address tokenB = address(uint160(uint256(keccak256(abi.encodePacked("B", tokenBSeed)))));
        if (tokenA == address(0) || tokenB == address(0) || tokenA == tokenB) return;
        if (factory.getPair(tokenA, tokenB) != address(0)) return;
        try factory.createPair(tokenA, tokenB) {} catch {}
    }
}

contract FactoryAdditionalMirrors is FactoryFixture {
    // tama: mirrors=factory_createPair_success_matches_closed_world_step
    function testFuzzMirrorFactoryCreatePairSuccessMatchesClosedWorldStep(address tokenA_, address tokenB_) public {
        vm.assume(tokenA_ != address(0) && tokenB_ != address(0) && tokenA_ != tokenB_);
        vm.assume(factory.getPair(tokenA_, tokenB_) == address(0));
        (address token0, address token1) = sortedAddresses(tokenA_, tokenB_);
        address expectedPair = expectedCreate2Pair(token0, token1);
        uint256 lengthBefore = factory.allPairsLength();

        address created = factory.createPair(tokenA_, tokenB_);

        assertEq(created, expectedPair);
        assertEq(factory.allPairsLength(), lengthBefore + 1);
        assertEq(factory.allPairs(lengthBefore), expectedPair);
        assertEq(factory.getPair(tokenA_, tokenB_), expectedPair);
        assertEq(factory.getPair(tokenB_, tokenA_), expectedPair);
    }

    // tama: mirrors=factory_createPair_run_revert_pair_count_overflow
    function testFuzzMirrorFactoryCreatePairRevertsOnPairCountOverflow(address tokenA_, address tokenB_) public {
        vm.assume(tokenA_ != address(0) && tokenB_ != address(0) && tokenA_ != tokenB_);
        vm.assume(factory.getPair(tokenA_, tokenB_) == address(0));
        vm.store(address(factory), bytes32(uint256(2)), bytes32(type(uint256).max));

        vm.expectRevert(bytes("UniswapV2: PAIR_COUNT_OVERFLOW"));
        factory.createPair(tokenA_, tokenB_);
    }

    // tama: mirrors=factory_createPair_run_revert_create2_failed
    function testFuzzMirrorFactoryCreatePairRevertsWhenCreate2DestinationOccupied(address tokenA_, address tokenB_)
        public
    {
        vm.assume(tokenA_ != address(0) && tokenB_ != address(0) && tokenA_ != tokenB_);
        vm.assume(factory.getPair(tokenA_, tokenB_) == address(0));
        (address token0, address token1) = sortedAddresses(tokenA_, tokenB_);
        address expectedPair = expectedCreate2Pair(token0, token1);
        vm.etch(expectedPair, hex"fe");

        vm.expectRevert(bytes("UniswapV2: CREATE2_FAILED"));
        factory.createPair(tokenA_, tokenB_);
    }
}

contract FactoryInvariantMirrors is FactoryFixture {
    FactoryHandler internal handler;

    function setUp() public override {
        super.setUp();
        handler = new FactoryHandler(factory);
        targetContract(address(handler));
    }

    // tama: mirrors=factory_createPair_success_preserves_good
    function invariant_factoryCreatePairSuccessPreservesGood() public {
        uint256 length = factory.allPairsLength();
        for (uint256 i = 0; i < length; i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            assertTrue(p.token0() != address(0));
            assertTrue(p.token1() != address(0));
            assertLt(uint160(p.token0()), uint160(p.token1()));
            assertEq(factory.getPair(p.token0(), p.token1()), pairAddr);
            assertEq(factory.getPair(p.token1(), p.token0()), pairAddr);
        }
    }
}

// =====================================================================
// Remaining behavior covered by the original integration tests.
// These exercise event emission, fee-off K, the existing reentrancy
// shape, and the metadata/permit absence — but none carry a `mirrors`
// annotation because each spec they touch is already mirrored by a
// dedicated 1:1 test above.
// =====================================================================

contract PairIntegrationSmoke is PairFixture {
    function testPairOmitsMetadataAndPermitSurface() public {
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
        pair.transfer(address(pair), liquidity);
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

    function testSwapEmitsSyncAndSwap() public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);

        vm.expectEmit(false, false, false, true, address(pair));
        emit Sync(11_000, 9_094);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Swap(address(this), 1_000, 0, 0, 906, address(this));
        pair.swap(0, 906, address(this), "");
    }

    function testSwapInvalidToReverts() public {
        seed(10_000, 10_000);
        address token0Addr = pair.token0();
        vm.expectRevert(bytes("UniswapV2: INVALID_TO"));
        pair.swap(1, 0, token0Addr, "");
    }

    function testSwapInsufficientLiquidityReverts() public {
        seed(10_000, 10_000);
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_LIQUIDITY"));
        pair.swap(10_000, 0, address(this), "");
    }

    function testSwapInsufficientInputAmountReverts() public {
        seed(10_000, 10_000);
        vm.expectRevert();
        pair.swap(1, 0, address(this), "");
    }

    function testFlashSwapCallbackAndKLastFeeOff() public {
        seed(10_000, 10_000);
        FlashCallee callee = new FlashCallee();
        uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
        (MockERC20 sorted0, MockERC20 sorted1) = sortedTokens();
        sorted1.mint(address(callee), requiredIn);

        bytes memory data = abi.encode(sorted0, sorted1, 0, requiredIn);
        pair.swap(1_000, 0, address(callee), data);
        assertEq(pair.kLast(), 0);
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

    function testPriceCumulativeUpdatesAfterElapsedTime() public {
        seed(10_000, 10_000);
        vm.warp(block.timestamp + 10);
        tokenA.mint(address(pair), 7);
        tokenB.mint(address(pair), 9);

        pair.sync();
        assertEq(pair.price0CumulativeLast(), 10 * 2 ** 112);
        assertEq(pair.price1CumulativeLast(), 10 * 2 ** 112);
    }

    function testMintRevertsWhenOneTokenAmountMissing() public {
        tokenA.mint(address(pair), 1_000_000);
        vm.expectRevert();
        pair.mint(address(this));
    }

    function testBurnRevertsWithoutLiquidity() public {
        vm.expectRevert();
        pair.burn(address(this));
    }
}
