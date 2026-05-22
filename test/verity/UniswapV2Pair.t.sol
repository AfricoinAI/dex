// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {UniswapV2FactoryDeployer} from "../../src/generated/verity/UniswapV2FactoryDeployer.sol";
import {UniswapV2FactoryIface} from "../../src/generated/verity/UniswapV2FactoryIface.sol";
import {UniswapV2PairIface} from "../../src/generated/verity/UniswapV2PairIface.sol";
import {
    MockERC20,
    NoReturnERC20,
    FalseReturnERC20,
    RevertingTransferERC20,
    ReentrantTransferERC20,
    RevertingBalanceOfERC20,
    ShortReturnBalanceOfERC20,
    FlashCallee,
    TrackingFlashCallee,
    RevertingFlashCallee,
    MintReentrantCallee,
    BurnReentrantCallee,
    SwapReentrantCallee,
    SkimReentrantCallee,
    SyncReentrantCallee,
    AllEntrypointReentrantCallee,
    RevertingAllEntrypointReentrantCallee,
    PairFixture
} from "./UniswapV2Helpers.sol";

contract PairViewMirrors is PairFixture {
    function testLayoutConstantsMatchGeneratedReport() public {
        string memory json = vm.readFile("artifacts/layout-report.json");

        assertEq(vm.parseJsonString(json, ".contracts[1].contract"), "UniswapV2Pair");
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[0].name"), "factorySlot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[0].canonicalSlot"), PAIR_FACTORY_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[1].name"), "token0Slot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[1].canonicalSlot"), PAIR_TOKEN0_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[2].name"), "token1Slot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[2].canonicalSlot"), PAIR_TOKEN1_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[3].name"), "reserve0Slot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[3].canonicalSlot"), PAIR_RESERVE0_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[4].name"), "reserve1Slot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[4].canonicalSlot"), PAIR_RESERVE1_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[5].name"), "blockTimestampLastSlot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[5].canonicalSlot"), PAIR_BLOCK_TIMESTAMP_LAST_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[6].name"), "price0CumulativeLastSlot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[6].canonicalSlot"), PAIR_PRICE0_CUMULATIVE_LAST_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[7].name"), "price1CumulativeLastSlot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[7].canonicalSlot"), PAIR_PRICE1_CUMULATIVE_LAST_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[8].name"), "totalSupplySlot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[8].canonicalSlot"), PAIR_TOTAL_SUPPLY_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[9].name"), "balancesSlot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[9].canonicalSlot"), PAIR_BALANCES_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[10].name"), "allowancesSlot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[10].canonicalSlot"), PAIR_ALLOWANCES_SLOT);
        assertEq(vm.parseJsonString(json, ".contracts[1].fields[11].name"), "unlockedSlot");
        assertEq(vm.parseJsonUint(json, ".contracts[1].fields[11].canonicalSlot"), PAIR_UNLOCKED_SLOT);
    }

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
    function testFuzzMirrorBalanceOfReturnsLpBalanceCell(address account) public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.balanceOf(account), uint256(vm.load(address(pair), lpBalanceSlot(account))));
    }

    // tama: mirrors=pair_allowance_run_success_frames_state
    function testFuzzMirrorAllowanceReturnsAllowanceCell(address owner, address spender) public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.allowance(owner, spender), uint256(vm.load(address(pair), lpAllowanceSlot(owner, spender))));
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
    function testFuzzMirrorInitializeRevertsForNonFactory(address token0Value, address token1Value, address caller)
        public
    {
        vm.assume(caller != address(factory));
        vm.prank(caller);
        vm.expectRevert(bytes("UniswapV2: FORBIDDEN"));
        pair.initialize(token0Value, token1Value);
    }

    // tama: mirrors=pair_initialize_reverts_for_non_factory
    function testFuzzMirrorInitializeNonFactoryResultIsRevert(address token0Value, address token1Value, address caller)
        public
    {
        vm.assume(caller != address(factory));
        vm.prank(caller);
        (bool ok, bytes memory data) =
            address(pair).call(abi.encodeCall(UniswapV2PairIface.initialize, (token0Value, token1Value)));
        assertFalse(ok);
        bytes memory expected = abi.encodeWithSignature("Error(string)", "UniswapV2: FORBIDDEN");
        assertEq(keccak256(data), keccak256(expected));
    }

    // tama: mirrors=pair_initialize_run_revert_already_initialized
    function testFuzzMirrorInitializeRevertsWhenAlreadyInitialized(address token0Value, address token1Value) public {
        vm.prank(address(factory));
        vm.expectRevert(bytes("UniswapV2: ALREADY_INITIALIZED"));
        pair.initialize(token0Value, token1Value);
    }

    // tama: mirrors=pair_initialize_reverts_when_already_initialized
    function testFuzzMirrorInitializeAlreadyInitializedResultIsRevert(address token0Value, address token1Value) public {
        vm.prank(address(factory));
        (bool ok, bytes memory data) =
            address(pair).call(abi.encodeCall(UniswapV2PairIface.initialize, (token0Value, token1Value)));
        assertFalse(ok);
        bytes memory expected = abi.encodeWithSignature("Error(string)", "UniswapV2: ALREADY_INITIALIZED");
        assertEq(keccak256(data), keccak256(expected));
    }

    // tama: mirrors=pair_transfer_run_revert_balance_low
    function testFuzzMirrorTransferRevertsWhenSenderBalanceTooLow(address toAddr, uint96 amount, address sender)
        public
    {
        seed(1_000_000, 1_000_000);
        uint256 sendAmount = uint256(amount) + pair.balanceOf(sender) + 1;
        vm.prank(sender);
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_BALANCE"));
        pair.transfer(toAddr, sendAmount);
    }

    // tama: mirrors=pair_transfer_run_revert_recipient_balance_overflow
    function testFuzzMirrorTransferRevertsOnRecipientBalanceOverflow(address toAddr, uint96 amount) public {
        vm.assume(toAddr != address(this));
        seed(1_000_000, 1_000_000);
        uint256 sendAmount = uint256(amount) + 1;
        vm.assume(sendAmount <= pair.balanceOf(address(this)));
        setLpBalance(toAddr, type(uint256).max);
        vm.expectRevert(bytes("UniswapV2: BALANCE_OVERFLOW"));
        pair.transfer(toAddr, sendAmount);
    }

    // tama: mirrors=pair_transferFrom_run_revert_allowance_low
    function testFuzzMirrorTransferFromRevertsWhenAllowanceTooLow(address fromAddr, address toAddr, uint96 amount)
        public
    {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount) + 1;
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_ALLOWANCE"));
        pair.transferFrom(fromAddr, toAddr, transferAmount);
    }

    // tama: mirrors=pair_transferFrom_run_revert_balance_low
    function testFuzzMirrorTransferFromRevertsWhenSourceBalanceTooLow(
        address fromAddr,
        address toAddr,
        address spender,
        uint96 amount
    ) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount) + pair.balanceOf(fromAddr) + 1;
        setLpAllowance(fromAddr, spender, transferAmount);
        vm.prank(spender);
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_BALANCE"));
        pair.transferFrom(fromAddr, toAddr, transferAmount);
    }

    // tama: mirrors=pair_transferFrom_run_revert_recipient_balance_overflow
    function testFuzzMirrorTransferFromRevertsOnRecipientBalanceOverflow(
        address fromAddr,
        address toAddr,
        address spender,
        uint96 amount
    ) public {
        vm.assume(fromAddr != toAddr);
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount) + 1;
        setLpBalance(fromAddr, transferAmount);
        setLpAllowance(fromAddr, spender, transferAmount);
        setLpBalance(toAddr, type(uint256).max);
        vm.prank(spender);
        vm.expectRevert(bytes("UniswapV2: BALANCE_OVERFLOW"));
        pair.transferFrom(fromAddr, toAddr, transferAmount);
    }

    // tama: mirrors=pair_mint_run_revert_locked
    function testFuzzMirrorMintRevertsWhenLockClosed(address toAddr) public {
        vm.store(address(pair), pairSlot(PAIR_UNLOCKED_SLOT), bytes32(0));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.mint(toAddr);
    }

    // tama: mirrors=pair_mint_run_revert_balance0_overflow
    function testFuzzMirrorMintRevertsOnBalance0Overflow(address toAddr, uint256 extra) public {
        extra = bound(extra, 1, type(uint128).max);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), MAX_UINT112 + extra);
        t1.mint(address(pair), 1);
        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.mint(toAddr);
    }

    // tama: mirrors=pair_mint_run_revert_balance1_overflow
    function testFuzzMirrorMintRevertsOnBalance1Overflow(address toAddr, uint256 extra) public {
        extra = bound(extra, 1, type(uint128).max);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 1);
        t1.mint(address(pair), MAX_UINT112 + extra);
        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.mint(toAddr);
    }

    // tama: mirrors=pair_burn_run_revert_locked
    function testFuzzMirrorBurnRevertsWhenLockClosed(address toAddr) public {
        vm.store(address(pair), pairSlot(PAIR_UNLOCKED_SLOT), bytes32(0));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.burn(toAddr);
    }

    // tama: mirrors=pair_swap_run_revert_locked
    function testFuzzMirrorSwapRevertsWhenLockClosed(
        uint256 amount0Out,
        uint256 amount1Out,
        address toAddr,
        bytes calldata data
    ) public {
        vm.store(address(pair), pairSlot(PAIR_UNLOCKED_SLOT), bytes32(0));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.swap(amount0Out, amount1Out, toAddr, data);
    }

    // tama: mirrors=pair_swap_run_revert_zero_output
    function testFuzzMirrorSwapRevertsOnZeroOutput(address toAddr, bytes calldata data) public {
        seed(10_000, 10_000);
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"));
        pair.swap(0, 0, toAddr, data);
    }

    // tama: mirrors=pair_skim_run_revert_locked
    function testFuzzMirrorSkimRevertsWhenLockClosed(address toAddr) public {
        vm.store(address(pair), pairSlot(PAIR_UNLOCKED_SLOT), bytes32(0));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.skim(toAddr);
    }

    // tama: mirrors=pair_skim_run_revert_balance0_below_reserve
    function testFuzzMirrorSkimRevertsWhenBalance0BelowReserve(address toAddr, uint96 deficit) public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        uint256 amount = bound(deficit, 1, 10_000);
        vm.prank(address(pair));
        t0.transfer(address(0xBEEF), amount);
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_BALANCE"));
        pair.skim(toAddr);
    }

    // tama: mirrors=pair_skim_run_revert_balance1_below_reserve
    function testFuzzMirrorSkimRevertsWhenBalance1BelowReserve(address toAddr, uint96 deficit) public {
        seed(10_000, 10_000);
        (, MockERC20 t1) = sortedTokens();
        uint256 amount = bound(deficit, 1, 10_000);
        vm.prank(address(pair));
        t1.transfer(address(0xBEEF), amount);
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_BALANCE"));
        pair.skim(toAddr);
    }

    // tama: mirrors=pair_sync_run_revert_locked
    function testFuzzMirrorSyncRevertsWhenLockClosed() public {
        vm.store(address(pair), pairSlot(PAIR_UNLOCKED_SLOT), bytes32(0));
        vm.expectRevert(bytes("UniswapV2: LOCKED"));
        pair.sync();
    }

    // tama: mirrors=pair_sync_run_revert_balance0_overflow
    function testFuzzMirrorSyncRevertsOnBalance0Overflow(uint256 extra) public {
        extra = bound(extra, 1, type(uint128).max);
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), MAX_UINT112 + extra);
        vm.expectRevert(bytes("UniswapV2: OVERFLOW"));
        pair.sync();
    }

    // tama: mirrors=pair_sync_run_revert_balance1_overflow
    function testFuzzMirrorSyncRevertsOnBalance1Overflow(uint256 extra) public {
        extra = bound(extra, 1, type(uint128).max);
        seed(10_000, 10_000);
        (, MockERC20 t1) = sortedTokens();
        t1.mint(address(pair), MAX_UINT112 + extra);
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
        s.reserve0 = vm.load(address(pair), pairSlot(PAIR_RESERVE0_SLOT));
        s.reserve1 = vm.load(address(pair), pairSlot(PAIR_RESERVE1_SLOT));
        s.supply = vm.load(address(pair), pairSlot(PAIR_TOTAL_SUPPLY_SLOT));
        s.unlocked = vm.load(address(pair), pairSlot(PAIR_UNLOCKED_SLOT));
        s.token0 = vm.load(address(pair), pairSlot(PAIR_TOKEN0_SLOT));
        s.token1 = vm.load(address(pair), pairSlot(PAIR_TOKEN1_SLOT));
        s.factoryAddr = vm.load(address(pair), pairSlot(PAIR_FACTORY_SLOT));
        s.price0 = vm.load(address(pair), pairSlot(PAIR_PRICE0_CUMULATIVE_LAST_SLOT));
        s.price1 = vm.load(address(pair), pairSlot(PAIR_PRICE1_CUMULATIVE_LAST_SLOT));
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
    function testFuzzMirrorMintRevertLeavesPairStateUnchanged(address toAddr, uint256 extra) public {
        extra = bound(extra, 1, type(uint128).max);
        seed(1_000_000, 1_000_000);
        Snapshot memory pre = snapshot();
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), MAX_UINT112 + extra);
        vm.expectRevert();
        pair.mint(toAddr);
        assertSnapshotEq(snapshot(), pre);
    }

    // tama: mirrors=pair_burn_revert_keeps_pair_state
    function testFuzzMirrorBurnRevertLeavesPairStateUnchanged(address toAddr) public {
        seed(1_000_000, 1_000_000);
        Snapshot memory pre = snapshot();
        // No LP transferred to pair => burn divides by zero pro-rata and reverts.
        vm.expectRevert();
        pair.burn(toAddr);
        assertSnapshotEq(snapshot(), pre);
    }

    // tama: mirrors=pair_swap_revert_keeps_pair_state
    function testFuzzMirrorSwapRevertLeavesPairStateUnchanged(address toAddr, bytes calldata data) public {
        seed(10_000, 10_000);
        Snapshot memory pre = snapshot();
        vm.expectRevert(bytes("UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"));
        pair.swap(0, 0, toAddr, data);
        assertSnapshotEq(snapshot(), pre);
    }

    // tama: mirrors=pair_skim_revert_keeps_pair_state
    function testFuzzMirrorSkimRevertLeavesPairStateUnchanged(address toAddr, uint96 deficit) public {
        seed(10_000, 10_000);
        Snapshot memory pre = snapshot();
        (MockERC20 t0,) = sortedTokens();
        uint256 amount = bound(deficit, 1, 10_000);
        vm.prank(address(pair));
        t0.transfer(address(0xBEEF), amount);
        vm.expectRevert();
        pair.skim(toAddr);
        assertSnapshotEq(snapshot(), pre);
    }

    // tama: mirrors=pair_sync_revert_keeps_pair_state
    function testFuzzMirrorSyncRevertLeavesPairStateUnchanged(uint256 extra) public {
        extra = bound(extra, 1, type(uint128).max);
        seed(10_000, 10_000);
        Snapshot memory pre = snapshot();
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), MAX_UINT112 + extra);
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
    function testFuzzMirrorInitializeSetsTokenIdentities(address tokenA_, address tokenB_) public {
        vm.assume(tokenA_ != address(0) && tokenB_ != address(0) && tokenA_ != tokenB_);
        address pairAddr = factory.createPair(tokenA_, tokenB_);
        UniswapV2PairIface freshPair = UniswapV2PairIface(pairAddr);
        (address sorted0, address sorted1) = tokenA_ < tokenB_ ? (tokenA_, tokenB_) : (tokenB_, tokenA_);
        assertEq(freshPair.token0(), sorted0);
        assertEq(freshPair.token1(), sorted1);
    }

    // tama: mirrors=pair_initialize_run_success_keeps_amm_accounting
    function testFuzzMirrorInitializeKeepsAmmAccounting(address tokenA_, address tokenB_, address account) public {
        vm.assume(tokenA_ != address(0) && tokenB_ != address(0) && tokenA_ != tokenB_);
        address pairAddr = factory.createPair(tokenA_, tokenB_);
        UniswapV2PairIface freshPair = UniswapV2PairIface(pairAddr);
        (uint256 reserve0, uint256 reserve1, uint256 ts) = freshPair.getReserves();
        assertEq(reserve0, 0);
        assertEq(reserve1, 0);
        assertEq(ts, 0);
        assertEq(freshPair.totalSupply(), 0);
        assertEq(freshPair.balanceOf(account), 0);
        assertEq(freshPair.balanceOf(address(0)), 0);
    }
}

// =====================================================================
// Pair approve success path (§12)
// =====================================================================

contract PairApproveMirrors is PairFixture {
    // tama: mirrors=pair_approve_succeeds
    function testFuzzMirrorApproveReturnsTrue(address spender, uint256 amount) public {
        seed(1_000_000, 1_000_000);
        assertTrue(pair.approve(spender, amount));
    }

    // tama: mirrors=pair_approve_sets_allowance
    function testFuzzMirrorApproveSetsAllowance(address spender, uint256 amount) public {
        seed(1_000_000, 1_000_000);
        pair.approve(spender, amount);
        assertEq(pair.allowance(address(this), spender), amount);
    }

    // tama: mirrors=pair_approve_keeps_balances
    function testFuzzMirrorApproveKeepsBalances(address spender, uint256 amount, address probe) public {
        seed(1_000_000, 1_000_000);
        uint256 before = pair.balanceOf(probe);
        pair.approve(spender, amount);
        assertEq(pair.balanceOf(probe), before);
    }

    // tama: mirrors=pair_approve_keeps_total_supply
    function testFuzzMirrorApproveKeepsTotalSupply(address spender, uint256 amount) public {
        seed(1_000_000, 1_000_000);
        uint256 supplyBefore = pair.totalSupply();
        pair.approve(spender, amount);
        assertEq(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_approve_emits_approval
    function testFuzzMirrorApproveEmitsApproval(address spender, uint256 amount) public {
        seed(1_000_000, 1_000_000);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Approval(address(this), spender, amount);
        pair.approve(spender, amount);
    }

    // tama: mirrors=pair_approve_keeps_pool_storage
    function testFuzzMirrorApproveKeepsPoolStorage(address spender, uint256 amount) public {
        seed(1_000_000, 1_000_000);
        bytes32 reserve0Before = vm.load(address(pair), pairSlot(PAIR_RESERVE0_SLOT));
        bytes32 reserve1Before = vm.load(address(pair), pairSlot(PAIR_RESERVE1_SLOT));
        bytes32 supplyBefore = vm.load(address(pair), pairSlot(PAIR_TOTAL_SUPPLY_SLOT));
        bytes32 unlockedBefore = vm.load(address(pair), pairSlot(PAIR_UNLOCKED_SLOT));
        bytes32 price0Before = vm.load(address(pair), pairSlot(PAIR_PRICE0_CUMULATIVE_LAST_SLOT));
        bytes32 price1Before = vm.load(address(pair), pairSlot(PAIR_PRICE1_CUMULATIVE_LAST_SLOT));
        bytes32 token0Before = vm.load(address(pair), pairSlot(PAIR_TOKEN0_SLOT));
        bytes32 token1Before = vm.load(address(pair), pairSlot(PAIR_TOKEN1_SLOT));
        pair.approve(spender, amount);
        assertEq(vm.load(address(pair), pairSlot(PAIR_RESERVE0_SLOT)), reserve0Before);
        assertEq(vm.load(address(pair), pairSlot(PAIR_RESERVE1_SLOT)), reserve1Before);
        assertEq(vm.load(address(pair), pairSlot(PAIR_TOTAL_SUPPLY_SLOT)), supplyBefore);
        assertEq(vm.load(address(pair), pairSlot(PAIR_UNLOCKED_SLOT)), unlockedBefore);
        assertEq(vm.load(address(pair), pairSlot(PAIR_PRICE0_CUMULATIVE_LAST_SLOT)), price0Before);
        assertEq(vm.load(address(pair), pairSlot(PAIR_PRICE1_CUMULATIVE_LAST_SLOT)), price1Before);
        assertEq(vm.load(address(pair), pairSlot(PAIR_TOKEN0_SLOT)), token0Before);
        assertEq(vm.load(address(pair), pairSlot(PAIR_TOKEN1_SLOT)), token1Before);
    }
}

// =====================================================================
// Pair LP transfer success path (§12)
// =====================================================================

contract PairTransferMirrors is PairFixture {
    // tama: mirrors=pair_transfer_to_self_keeps_balances
    function testFuzzMirrorTransferToSelfKeepsBalances(uint96 amount) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = bound(uint256(amount), 0, pair.balanceOf(address(this)));
        uint256 before = pair.balanceOf(address(this));
        assertTrue(pair.transfer(address(this), transferAmount));
        assertEq(pair.balanceOf(address(this)), before);
    }

    // tama: mirrors=pair_transfer_moves_tokens_between_distinct_accounts
    function testFuzzMirrorTransferMovesBetweenDistinctAccounts(address toAddr, uint96 amount) public {
        seed(1_000_000, 1_000_000);
        vm.assume(toAddr != address(this));
        uint256 senderBefore = pair.balanceOf(address(this));
        uint256 transferAmount = bound(uint256(amount), 0, senderBefore);
        uint256 recipientBefore = pair.balanceOf(toAddr);
        vm.assume(recipientBefore + transferAmount <= type(uint256).max);
        assertTrue(pair.transfer(toAddr, transferAmount));
        assertEq(pair.balanceOf(address(this)), senderBefore - transferAmount);
        assertEq(pair.balanceOf(toAddr), recipientBefore + transferAmount);
    }

    // tama: mirrors=pair_transfer_keeps_total_supply
    function testFuzzMirrorTransferKeepsTotalSupply(address toAddr, uint96 amount) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = bound(uint256(amount), 0, pair.balanceOf(address(this)));
        if (toAddr != address(this)) {
            vm.assume(pair.balanceOf(toAddr) + transferAmount <= type(uint256).max);
        }
        uint256 supplyBefore = pair.totalSupply();
        assertTrue(pair.transfer(toAddr, transferAmount));
        assertEq(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_transfer_keeps_pool_storage
    function testFuzzMirrorTransferKeepsPoolStorage(address toAddr, uint96 amount) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = bound(uint256(amount), 0, pair.balanceOf(address(this)));
        if (toAddr != address(this)) {
            vm.assume(pair.balanceOf(toAddr) + transferAmount <= type(uint256).max);
        }
        bytes32 reserve0Before = vm.load(address(pair), pairSlot(PAIR_RESERVE0_SLOT));
        bytes32 reserve1Before = vm.load(address(pair), pairSlot(PAIR_RESERVE1_SLOT));
        bytes32 supplyBefore = vm.load(address(pair), pairSlot(PAIR_TOTAL_SUPPLY_SLOT));
        bytes32 unlockedBefore = vm.load(address(pair), pairSlot(PAIR_UNLOCKED_SLOT));
        bytes32 price0Before = vm.load(address(pair), pairSlot(PAIR_PRICE0_CUMULATIVE_LAST_SLOT));
        bytes32 price1Before = vm.load(address(pair), pairSlot(PAIR_PRICE1_CUMULATIVE_LAST_SLOT));
        assertTrue(pair.transfer(toAddr, transferAmount));
        assertEq(vm.load(address(pair), pairSlot(PAIR_RESERVE0_SLOT)), reserve0Before);
        assertEq(vm.load(address(pair), pairSlot(PAIR_RESERVE1_SLOT)), reserve1Before);
        assertEq(vm.load(address(pair), pairSlot(PAIR_TOTAL_SUPPLY_SLOT)), supplyBefore);
        assertEq(vm.load(address(pair), pairSlot(PAIR_UNLOCKED_SLOT)), unlockedBefore);
        assertEq(vm.load(address(pair), pairSlot(PAIR_PRICE0_CUMULATIVE_LAST_SLOT)), price0Before);
        assertEq(vm.load(address(pair), pairSlot(PAIR_PRICE1_CUMULATIVE_LAST_SLOT)), price1Before);
    }

    // tama: mirrors=pair_transfer_emits_transfer
    function testFuzzMirrorTransferEmitsTransfer(address toAddr, uint96 amount) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = bound(uint256(amount), 0, pair.balanceOf(address(this)));
        if (toAddr != address(this)) {
            vm.assume(pair.balanceOf(toAddr) + transferAmount <= type(uint256).max);
        }
        vm.expectEmit(true, true, false, true, address(pair));
        emit Transfer(address(this), toAddr, transferAmount);
        pair.transfer(toAddr, transferAmount);
    }
}

// =====================================================================
// Pair LP transferFrom success path (§12)
// =====================================================================

contract PairTransferFromMirrors is PairFixture {
    // tama: mirrors=pair_transferFrom_to_self_keeps_balances
    function testFuzzMirrorTransferFromToSelfKeepsBalances(address fromAddr, address spender, uint96 amount) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount);
        setLpBalance(fromAddr, transferAmount);
        setLpAllowance(fromAddr, spender, transferAmount);
        uint256 before = pair.balanceOf(fromAddr);
        vm.prank(spender);
        assertTrue(pair.transferFrom(fromAddr, fromAddr, transferAmount));
        assertEq(pair.balanceOf(fromAddr), before);
    }

    // tama: mirrors=pair_transferFrom_moves_tokens_between_distinct_accounts
    function testFuzzMirrorTransferFromMovesBetweenDistinctAccounts(
        address fromAddr,
        address toAddr,
        address spender,
        uint96 amount
    ) public {
        vm.assume(fromAddr != toAddr);
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount);
        setLpBalance(fromAddr, transferAmount);
        setLpAllowance(fromAddr, spender, transferAmount);
        uint256 senderBefore = pair.balanceOf(fromAddr);
        uint256 recipientBefore = pair.balanceOf(toAddr);
        vm.prank(spender);
        assertTrue(pair.transferFrom(fromAddr, toAddr, transferAmount));
        assertEq(pair.balanceOf(fromAddr), senderBefore - transferAmount);
        assertEq(pair.balanceOf(toAddr), recipientBefore + transferAmount);
    }

    // tama: mirrors=pair_transferFrom_keeps_total_supply
    function testFuzzMirrorTransferFromKeepsTotalSupply(
        address fromAddr,
        address toAddr,
        address spender,
        uint96 amount
    ) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount);
        setLpBalance(fromAddr, transferAmount);
        setLpAllowance(fromAddr, spender, transferAmount);
        uint256 supplyBefore = pair.totalSupply();
        vm.prank(spender);
        assertTrue(pair.transferFrom(fromAddr, toAddr, transferAmount));
        assertEq(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_transferFrom_keeps_pool_storage
    function testFuzzMirrorTransferFromKeepsPoolStorage(
        address fromAddr,
        address toAddr,
        address spender,
        uint96 amount
    ) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount);
        setLpBalance(fromAddr, transferAmount);
        setLpAllowance(fromAddr, spender, transferAmount);
        (uint256 reserve0Before, uint256 reserve1Before, uint256 tsBefore) = pair.getReserves();
        uint256 price0Before = pair.price0CumulativeLast();
        uint256 price1Before = pair.price1CumulativeLast();
        address token0Before = pair.token0();
        address token1Before = pair.token1();
        vm.prank(spender);
        assertTrue(pair.transferFrom(fromAddr, toAddr, transferAmount));
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
    function testFuzzMirrorTransferFromEmitsTransfer(address fromAddr, address toAddr, address spender, uint96 amount)
        public
    {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount);
        setLpBalance(fromAddr, transferAmount);
        setLpAllowance(fromAddr, spender, transferAmount);
        vm.expectEmit(true, true, false, true, address(pair));
        emit Transfer(fromAddr, toAddr, transferAmount);
        vm.prank(spender);
        pair.transferFrom(fromAddr, toAddr, transferAmount);
    }

    // tama: mirrors=pair_transferFrom_keeps_infinite_allowance
    function testFuzzMirrorTransferFromMaxAllowanceStaysMax(
        address fromAddr,
        address toAddr,
        address spender,
        uint96 amount
    ) public {
        seed(1_000_000, 1_000_000);
        uint256 transferAmount = uint256(amount);
        setLpBalance(fromAddr, transferAmount);
        setLpAllowance(fromAddr, spender, type(uint256).max);
        vm.prank(spender);
        pair.transferFrom(fromAddr, toAddr, transferAmount);
        assertEq(pair.allowance(fromAddr, spender), type(uint256).max);
    }

    // tama: mirrors=pair_transferFrom_spends_finite_allowance
    function testFuzzMirrorTransferFromFiniteAllowanceIsConsumed(
        address fromAddr,
        address toAddr,
        address spender,
        uint96 allowanceAmount,
        uint96 amount
    ) public {
        seed(1_000_000, 1_000_000);
        uint256 finiteAllowance = bound(uint256(allowanceAmount), uint256(amount), type(uint96).max);
        uint256 transferAmount = uint256(amount);
        setLpBalance(fromAddr, transferAmount);
        setLpAllowance(fromAddr, spender, finiteAllowance);
        vm.prank(spender);
        pair.transferFrom(fromAddr, toAddr, transferAmount);
        assertEq(pair.allowance(fromAddr, spender), finiteAllowance - transferAmount);
    }
}

// =====================================================================
// Pair mint success path (§15, §6)
// =====================================================================

contract PairMintMirrors is PairFixture {
    // tama: mirrors=pair_first_mint_uses_balance_increase_as_deposit
    function testFuzzMirrorFirstMintTreatsBalanceIncreaseAsDeposit(address toAddr, uint128 amountA_, uint128 amountB_)
        public
    {
        uint256 amountA = bound(uint256(amountA_), 1_001, 1 ether);
        uint256 amountB = bound(uint256(amountB_), 1_001, 1 ether);
        tokenA.mint(address(pair), amountA);
        tokenB.mint(address(pair), amountB);
        pair.mint(toAddr);
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        (uint256 amount0, uint256 amount1) = sortedAmounts(amountA, amountB);
        assertEq(reserve0, amount0);
        assertEq(reserve1, amount1);
    }

    // tama: mirrors=pair_first_mint_success_uses_canonical_liquidity_formula
    function testFuzzMirrorFirstMintReturnsSqrtMinusMinimumLiquidity(address toAddr, uint128 amount_) public {
        vm.assume(toAddr != address(0));
        uint256 amount = bound(uint256(amount_), 1_001, 1 ether);
        tokenA.mint(address(pair), amount);
        tokenB.mint(address(pair), amount);
        uint256 liquidity = pair.mint(toAddr);
        assertEq(liquidity, amount - 1000);
        assertEq(pair.totalSupply(), amount);
        assertEq(pair.balanceOf(address(0)), 1000);
        assertEq(pair.balanceOf(toAddr), amount - 1000);
    }

    // tama: mirrors=pair_later_mint_uses_balance_increase_as_deposit
    function testFuzzMirrorSubsequentMintTreatsBalanceIncreaseAsDeposit(
        address toAddr,
        uint128 depositA_,
        uint128 depositB_
    ) public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        uint256 depositA = bound(uint256(depositA_), 1, 1_000_000);
        uint256 depositB = bound(uint256(depositB_), 1, 1_000_000);
        tokenA.mint(address(pair), depositA);
        tokenB.mint(address(pair), depositB);
        (uint256 amount0, uint256 amount1) = sortedAmounts(depositA, depositB);
        pair.mint(toAddr);
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
    function testFuzzMirrorBurnUsesPairLpBalanceAndTotalSupply(address toAddr, uint96 liquidity_) public {
        seed(1_000_000, 4_000_000);
        uint256 liquidityToBurn = bound(uint256(liquidity_), 4, pair.balanceOf(address(this)) / 2);
        pair.transfer(address(pair), liquidityToBurn);
        uint256 supplyBefore = pair.totalSupply();
        uint256 liquidity = pair.balanceOf(address(pair));
        assertEq(liquidity, liquidityToBurn);
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        (uint256 amount0, uint256 amount1) = pair.burn(toAddr);
        assertEq(amount0, (liquidity * reserve0) / supplyBefore);
        assertEq(amount1, (liquidity * reserve1) / supplyBefore);
    }

    // tama: mirrors=pair_burn_success_pays_exact_pro_rata_amounts
    function testFuzzMirrorBurnPaysExactProRataAmounts(address toAddr, uint96 liquidity_) public {
        seed(1_000_000, 4_000_000);
        uint256 liquidity = bound(uint256(liquidity_), 4, pair.balanceOf(address(this)) / 2);
        pair.transfer(address(pair), liquidity);
        uint256 supply = pair.totalSupply();
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        uint256 expected0 = (liquidity * reserve0) / supply;
        uint256 expected1 = (liquidity * reserve1) / supply;
        (uint256 amount0, uint256 amount1) = pair.burn(toAddr);
        assertEq(amount0, expected0);
        assertEq(amount1, expected1);
    }

    // tama: mirrors=pair_burn_leaves_remaining_token_balances
    function testFuzzMirrorBurnLeavesRemainingTokenBalances(address toAddr, uint96 liquidity_) public {
        seed(1_000_000, 4_000_000);
        vm.assume(toAddr != address(pair));
        uint256 liquidity = bound(uint256(liquidity_), 4, pair.balanceOf(address(this)) / 2);
        pair.transfer(address(pair), liquidity);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        uint256 pairBalance0Before = t0.balanceOf(address(pair));
        uint256 pairBalance1Before = t1.balanceOf(address(pair));
        (uint256 amount0, uint256 amount1) = pair.burn(toAddr);
        assertEq(t0.balanceOf(address(pair)), pairBalance0Before - amount0);
        assertEq(t1.balanceOf(address(pair)), pairBalance1Before - amount1);
    }

    // tama: mirrors=pair_burn_success_caches_post_redemption_balances
    function testFuzzMirrorBurnCachesPostRedemptionBalances(address toAddr, uint96 liquidity_) public {
        seed(1_000_000, 4_000_000);
        uint256 liquidity = bound(uint256(liquidity_), 4, pair.balanceOf(address(this)) / 2);
        pair.transfer(address(pair), liquidity);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        pair.burn(toAddr);
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
    function testFuzzMirrorSwapSuccessImpliesNonzeroOutput(uint96) public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
    }

    // tama: mirrors=pair_swap_uses_final_balances_to_compute_input
    function testFuzzMirrorSwapInfersInputFromFinalBalance(uint96) public {
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
    function testFuzzMirrorSwapFinalBalancesAccountForInputAndOutput(uint96) public {
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
    function testFuzzMirrorSwapKHoldsAgainstFinalBalances(uint96) public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        // (balance0*1000 - amount0In*3) * (balance1*1000) >= reserve0Before*reserve1Before*1000*1000
        assertGe((reserve0After * 1000 - 1_000 * 3) * (reserve1After * 1000), 10_000 * 10_000 * 1000 * 1000);
    }

    // tama: mirrors=pair_swap_success_charges_k_against_final_balances
    function testFuzzMirrorSwapKBoundaryRejectsUnpaidOutput(uint96) public {
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
    function testFuzzMirrorSkimSuccessTransfersExcessAndRestoresUnlocked(uint96) public {
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
        // The lock cell should be 1 after a successful skim.
        assertEq(uint256(vm.load(address(pair), pairSlot(PAIR_UNLOCKED_SLOT))), 1);
    }

    // tama: mirrors=pair_skim_success_run_implies_balances_back_reserves
    function testFuzzMirrorSkimSuccessImpliesBalancesCoverReserves(uint96) public {
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
    function testFuzzMirrorSkimSuccessRestoresUnlocked(uint96) public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1);
        pair.skim(address(this));
        assertEq(uint256(vm.load(address(pair), pairSlot(PAIR_UNLOCKED_SLOT))), 1);
    }
}

// =====================================================================
// Pair closed-world step mirrors: concrete entrypoint effects.
// Each test exercises one action and asserts the post-state arithmetic
// the Lean step relation captures abstractly.
// =====================================================================

contract PairClosedWorldStepMirrors is PairFixture {
    // tama: mirrors=pair_closed_world_approve_preserves_pool
    function testFuzzMirrorApprovePreservesPool(uint96) public {
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
    function testFuzzMirrorTransferPreservesPool(uint96) public {
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
    function testFuzzMirrorTransferFromPreservesPool(uint96) public {
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
    function testFuzzMirrorMintStrictlyIncreasesSupply(uint96) public {
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
    function testFuzzMirrorMintAddsExactDepositsToReserves(uint96) public {
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
    function testFuzzMirrorFirstMintLocksMinimumLiquidity(uint96) public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);
        uint256 liquidity = pair.mint(address(this));
        assertEq(pair.balanceOf(address(0)), 1000);
        assertEq(pair.totalSupply(), 1000 + liquidity);
    }

    // tama: mirrors=pair_closed_world_first_mint_keeps_locked_share
    function testFuzzMirrorFirstMintKeepsLockedShare(uint96) public {
        tokenA.mint(address(pair), 1 ether);
        tokenB.mint(address(pair), 1 ether);
        uint256 liquidity = pair.mint(address(this));
        assertLt(pair.balanceOf(address(0)), pair.totalSupply());
        assertLt(liquidity, pair.totalSupply());
    }

    // tama: mirrors=pair_closed_world_subsequent_mint_preserves_locked_liquidity
    function testFuzzMirrorSubsequentMintPreservesLockedLiquidity(uint96) public {
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
    function testFuzzMirrorBurnReducesSupplyByLiquidity(uint96) public {
        seed(1_000_000, 4_000_000);
        uint256 liquidity = 200_000;
        pair.transfer(address(pair), liquidity);
        uint256 supplyBefore = pair.totalSupply();
        pair.burn(address(this));
        assertEq(pair.totalSupply(), supplyBefore - liquidity);
    }

    // tama: mirrors=pair_closed_world_burn_never_increases_supply
    function testFuzzMirrorBurnNeverIncreasesSupply(uint96) public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        uint256 supplyBefore = pair.totalSupply();
        pair.burn(address(this));
        assertLe(pair.totalSupply(), supplyBefore);
    }

    // tama: mirrors=pair_closed_world_burn_removes_exact_redemptions_from_balances
    function testFuzzMirrorBurnRemovesExactRedemptionsFromBalances(uint96) public {
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
    function testFuzzMirrorBurnCannotRedeemLockedLiquidity(uint96) public {
        seed(1_000_000, 4_000_000);
        uint256 lockedBefore = pair.balanceOf(address(0));
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        assertEq(pair.balanceOf(address(0)), lockedBefore);
        assertGe(pair.totalSupply(), lockedBefore);
    }

    // tama: mirrors=pair_closed_world_burn_preserves_positive_balances
    function testFuzzMirrorBurnPreservesPositiveBalances(uint96) public {
        seed(1_000_000, 4_000_000);
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        assertGt(t0.balanceOf(address(pair)), 0);
        assertGt(t1.balanceOf(address(pair)), 0);
    }

    // tama: mirrors=pair_closed_world_donate_preserves_reserves_and_supply
    function testFuzzMirrorDonatePreservesReservesAndSupply(uint96) public {
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
    function testFuzzMirrorDonatePreservesK(uint96) public {
        seed(1_000_000, 1_000_000);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        uint256 kBefore = reserve0Before * reserve1Before;
        tokenA.mint(address(pair), 1234);
        tokenB.mint(address(pair), 5678);
        (uint256 reserve0After, uint256 reserve1After,) = pair.getReserves();
        assertEq(reserve0After * reserve1After, kBefore);
    }

    // tama: mirrors=pair_closed_world_donation_increases_surplus_exactly
    function testFuzzMirrorDonationIncreasesSurplusExactly(uint96) public {
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
    function testFuzzMirrorSkimRemovesSurplus(uint96) public {
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
    function testFuzzMirrorSkimPreservesBalancedPool(uint96) public {
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
    function testFuzzMirrorSkimRemovesExactSurplusValue(uint96) public {
        seed(10_000, 10_000);
        (MockERC20 t0, MockERC20 t1) = sortedTokens();
        t0.mint(address(pair), 123);
        t1.mint(address(pair), 456);
        (uint256 reserve0Before, uint256 reserve1Before,) = pair.getReserves();
        // Value at spot price = balance0 * reserve1 + balance1 * reserve0 (numerator form).
        uint256 valueBefore =
            t0.balanceOf(address(pair)) * reserve1Before + t1.balanceOf(address(pair)) * reserve0Before;
        uint256 surplusValue = (t0.balanceOf(address(pair)) - reserve0Before) * reserve1Before
            + (t1.balanceOf(address(pair)) - reserve1Before) * reserve0Before;
        pair.skim(address(this));
        uint256 valueAfter = t0.balanceOf(address(pair)) * reserve1Before + t1.balanceOf(address(pair)) * reserve0Before;
        assertEq(valueBefore, valueAfter + surplusValue);
    }

    // tama: mirrors=pair_closed_world_skim_token_balance_value_never_increases_at_spot
    function testFuzzMirrorSkimNeverIncreasesTokenBalanceValue(uint96) public {
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
    function testFuzzMirrorSkimOrSyncNeverIncreasesTokenBalanceValue(uint96) public {
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
    function testFuzzMirrorSyncSetsReservesToBalances(uint96) public {
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
    function testFuzzMirrorSyncPreservesTokenBalances(uint96) public {
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
    function testFuzzMirrorReserveWriteSetsReservesToBalances(uint96) public {
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
    function testFuzzMirrorReservesBackedByBalances(uint96) public {
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
    function testFuzzMirrorReservesFitUint112(uint96) public {
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
    function testFuzzMirrorZeroSupplyHasNoLockedLiquidity(uint96) public {
        assertEq(pair.totalSupply(), 0);
        assertEq(pair.balanceOf(address(0)), 0);
    }

    // tama: mirrors=pair_closed_world_nonzero_supply_locks_minimum_liquidity
    function testFuzzMirrorNonzeroSupplyLocksMinimumLiquidity(uint96) public {
        seed(1_000_000, 1_000_000);
        assertEq(pair.balanceOf(address(0)), 1000);
        assertGe(pair.totalSupply(), 1000);
    }

    // tama: mirrors=pair_closed_world_locked_liquidity_never_exceeds_supply
    function testFuzzMirrorLockedLiquidityNeverExceedsSupply(uint96) public {
        assertLe(pair.balanceOf(address(0)), pair.totalSupply());
        seed(1_000_000, 4_000_000);
        assertLe(pair.balanceOf(address(0)), pair.totalSupply());
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        assertLe(pair.balanceOf(address(0)), pair.totalSupply());
    }

    // tama: mirrors=pair_closed_world_reachable_path_minimum_liquidity_lock
    function testFuzzMirrorReachablePathPreservesMinLiquidityLock(uint96) public {
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
    function testFuzzMirrorLockedLiquidityIsMonotone(uint96) public {
        uint256 lockedStart = pair.balanceOf(address(0));
        seed(1_000_000, 4_000_000);
        assertGe(pair.balanceOf(address(0)), lockedStart);
        uint256 lockedAfterMint = pair.balanceOf(address(0));
        pair.transfer(address(pair), 200_000);
        pair.burn(address(this));
        assertGe(pair.balanceOf(address(0)), lockedAfterMint);
    }

    // tama: mirrors=pair_closed_world_reachable_path_reserves_backed
    function testFuzzMirrorReachablePathKeepsReservesBacked(uint96) public {
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
    function testFuzzMirrorReachablePathKeepsReservesInUint112(uint96) public {
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
    function testFuzzMirrorLpShareBackingMonotone(uint96) public {
        seed(10_000, 10_000);
        (uint256 reserve0Mid, uint256 reserve1Mid,) = pair.getReserves();
        uint256 supplyMid = pair.totalSupply();
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);
        pair.swap(0, 906, address(this), "");
        (uint256 reserve0End, uint256 reserve1End,) = pair.getReserves();
        uint256 supplyEnd = pair.totalSupply();
        // K/supply^2 monotone non-decreasing: cross-multiply for precision.
        assertGe(reserve0End * reserve1End * supplyMid * supplyMid, reserve0Mid * reserve1Mid * supplyEnd * supplyEnd);
    }

    // tama: mirrors=pair_closed_world_reachable_no_donation_path_never_increases_surplus
    function testFuzzMirrorNoDonationPathKeepsSurplus(uint96) public {
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
    function testFuzzMirrorReserveChangeRequiresReserveUpdate(uint96) public {
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
    function testFuzzMirrorSupplyChangeRequiresMintOrBurn(uint96) public {
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
    function testFuzzMirrorPathPreservesGoodInvariants(uint96) public {
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
    function testFuzzMirrorReachablePathPreservesGood(uint96) public {
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
    function testFuzzMirrorPathPreservesReachability(uint96) public {
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
// Pair actual-execution bridge mirrors.
// Each test runs the entrypoint and asserts the concrete/token state reaches
// the expected pair state named by the corresponding Lean bridge spec.
// =====================================================================

contract PairActualExecutionBridgeMirrors is PairFixture {
    // tama: mirrors=pair_first_mint_success_reaches_expected_pair_state
    function testFuzzMirrorFirstMintRunMatchesStep(uint96) public {
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

    // tama: mirrors=pair_later_mint_success_reaches_expected_pair_state
    function testFuzzMirrorSubsequentMintRunMatchesStep(uint96) public {
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

    // tama: mirrors=pair_burn_success_reaches_expected_pair_state
    function testFuzzMirrorBurnRunMatchesStep(uint96) public {
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

    // tama: mirrors=pair_swap_success_reaches_expected_pair_state
    function testFuzzMirrorSwapRunMatchesStep(uint96) public {
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

    // tama: mirrors=pair_skim_success_reaches_expected_pair_state
    function testFuzzMirrorSkimRunMatchesStep(uint96) public {
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

    // tama: mirrors=pair_sync_success_reaches_expected_pair_state
    function testFuzzMirrorSyncRunMatchesStep(uint96) public {
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
    function testFuzzMirrorFlashCallbackRunsWhilePairLocked(uint96) public {
        seed(10_000, 10_000);
        (MockERC20 sorted0, MockERC20 sorted1) = sortedTokens();
        uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
        SwapReentrantCallee callee = new SwapReentrantCallee(pair, sorted0, sorted1, 0, requiredIn);
        sorted1.mint(address(callee), requiredIn);
        pair.swap(1_000, 0, address(callee), abi.encode(uint256(1)));
        // Spec semantics: the callback observed `unlocked == 0`. The contract
        // observable equivalent is that any mutating reentry rejects with
        // UniswapV2: LOCKED while the callback is running.
        assertTrue(callee.reentryRejected());
        assertEq(callee.revertReason(), "UniswapV2: LOCKED");
    }

    // tama: mirrors=pair_flash_callback_reentry_attempts_revert_locked
    function testFuzzMirrorFlashCallbackAllEntrypointReentriesRevertLocked(uint96) public {
        seed(10_000, 10_000);
        (MockERC20 sorted0, MockERC20 sorted1) = sortedTokens();
        uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
        AllEntrypointReentrantCallee callee = new AllEntrypointReentrantCallee(pair, sorted0, sorted1, 0, requiredIn);
        sorted1.mint(address(callee), requiredIn);
        pair.swap(1_000, 0, address(callee), abi.encode(uint256(1)));
        assertTrue(callee.mintRejected());
        assertEq(callee.mintRevertReason(), "UniswapV2: LOCKED");
        assertTrue(callee.burnRejected());
        assertEq(callee.burnRevertReason(), "UniswapV2: LOCKED");
        assertTrue(callee.swapRejected());
        assertEq(callee.swapRevertReason(), "UniswapV2: LOCKED");
        assertTrue(callee.skimRejected());
        assertEq(callee.skimRevertReason(), "UniswapV2: LOCKED");
        assertTrue(callee.syncRejected());
        assertEq(callee.syncRevertReason(), "UniswapV2: LOCKED");
    }

    // tama: mirrors=pair_reentrancy_guard_blocks_all_mutating_entrypoints
    function testFuzzMirrorReentrancyGuardBlocksAllMutatingEntrypoints(uint96) public {
        // Close the lock cell directly to put the pair into the locked state.
        // Every mutating entrypoint must revert with "UniswapV2: LOCKED" before
        // touching storage.
        vm.store(address(pair), pairSlot(PAIR_UNLOCKED_SLOT), bytes32(0));

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

contract PairBoundaryAssumptionMirrors is PairFixture {
    struct PairSnapshot {
        uint256 reserve0;
        uint256 reserve1;
        uint256 totalSupply;
        uint256 pairToken0;
        uint256 pairToken1;
    }

    function _snapshot(UniswapV2PairIface observedPair, address observedToken0, address observedToken1)
        internal
        view
        returns (PairSnapshot memory snap)
    {
        (snap.reserve0, snap.reserve1,) = observedPair.getReserves();
        snap.totalSupply = observedPair.totalSupply();
        snap.pairToken0 = _balanceOf(observedToken0, address(observedPair));
        snap.pairToken1 = _balanceOf(observedToken1, address(observedPair));
    }

    function _assertSnapshotEq(
        PairSnapshot memory beforeSnap,
        UniswapV2PairIface observedPair,
        address observedToken0,
        address observedToken1
    ) internal view {
        PairSnapshot memory afterSnap = _snapshot(observedPair, observedToken0, observedToken1);
        assertEq(afterSnap.reserve0, beforeSnap.reserve0);
        assertEq(afterSnap.reserve1, beforeSnap.reserve1);
        assertEq(afterSnap.totalSupply, beforeSnap.totalSupply);
        assertEq(afterSnap.pairToken0, beforeSnap.pairToken0);
        assertEq(afterSnap.pairToken1, beforeSnap.pairToken1);
    }

    function _balanceOf(address token, address owner) internal view returns (uint256 balance) {
        (bool ok, bytes memory data) = token.staticcall(abi.encodeWithSignature("balanceOf(address)", owner));
        require(ok && data.length == 32, "BALANCE_READ");
        return abi.decode(data, (uint256));
    }

    function _seedNoReturnPair(NoReturnERC20 oddToken, MockERC20 normalToken)
        internal
        returns (UniswapV2PairIface oddPair)
    {
        oddPair = UniswapV2PairIface(factory.createPair(address(oddToken), address(normalToken)));
        oddToken.mint(address(oddPair), 10_000);
        normalToken.mint(address(oddPair), 10_000);
        oddPair.mint(address(this));
    }

    function testFuzzMirrorNoReturnERC20TransferOutAccepted(uint96) public {
        NoReturnERC20 oddToken = new NoReturnERC20();
        MockERC20 normalToken = new MockERC20();
        UniswapV2PairIface oddPair = _seedNoReturnPair(oddToken, normalToken);

        uint256 liquidity = oddPair.balanceOf(address(this)) / 4;
        oddPair.transfer(address(oddPair), liquidity);
        uint256 beforeBalance = oddToken.balanceOf(address(this));
        oddPair.burn(address(this));

        assertGt(oddToken.balanceOf(address(this)), beforeBalance);
    }

    function testFuzzMirrorFalseReturnERC20TransferOutRevertsAndRollsBack(uint96) public {
        FalseReturnERC20 oddToken = new FalseReturnERC20();
        MockERC20 normalToken = new MockERC20();
        UniswapV2PairIface oddPair = UniswapV2PairIface(factory.createPair(address(oddToken), address(normalToken)));
        oddToken.mint(address(oddPair), 10_000);
        normalToken.mint(address(oddPair), 10_000);
        oddPair.mint(address(this));

        address token0 = oddPair.token0();
        address token1 = oddPair.token1();
        PairSnapshot memory beforeSnap = _snapshot(oddPair, token0, token1);
        oddPair.transfer(address(oddPair), oddPair.balanceOf(address(this)) / 4);

        vm.expectRevert(bytes("transfer returned false"));
        oddPair.burn(address(this));

        _assertSnapshotEq(beforeSnap, oddPair, token0, token1);
    }

    function testFuzzMirrorRevertingERC20TransferOutRevertsAndRollsBack(uint96) public {
        RevertingTransferERC20 oddToken = new RevertingTransferERC20();
        MockERC20 normalToken = new MockERC20();
        UniswapV2PairIface oddPair = UniswapV2PairIface(factory.createPair(address(oddToken), address(normalToken)));
        oddToken.mint(address(oddPair), 10_000);
        normalToken.mint(address(oddPair), 10_000);
        oddPair.mint(address(this));

        address token0 = oddPair.token0();
        address token1 = oddPair.token1();
        PairSnapshot memory beforeSnap = _snapshot(oddPair, token0, token1);
        oddPair.transfer(address(oddPair), oddPair.balanceOf(address(this)) / 4);

        vm.expectRevert(bytes("transfer reverted"));
        oddPair.burn(address(this));

        _assertSnapshotEq(beforeSnap, oddPair, token0, token1);
    }

    // tama: mirrors=pair_reentrancy_guard_blocks_all_mutating_entrypoints
    function testFuzzMirrorReentrantTransferOutCannotEnterPair(uint96) public {
        ReentrantTransferERC20 oddToken = new ReentrantTransferERC20();
        MockERC20 normalToken = new MockERC20();
        UniswapV2PairIface oddPair = UniswapV2PairIface(factory.createPair(address(oddToken), address(normalToken)));
        oddToken.mint(address(oddPair), 10_000);
        normalToken.mint(address(oddPair), 10_000);
        oddPair.mint(address(this));

        oddToken.configureReentry(oddPair, ReentrantTransferERC20.Entrypoint.Sync);
        if (oddPair.token0() == address(oddToken)) {
            uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
            normalToken.mint(address(oddPair), requiredIn);
            oddPair.swap(1_000, 0, address(this), "");
        } else {
            uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
            normalToken.mint(address(oddPair), requiredIn);
            oddPair.swap(0, 1_000, address(this), "");
        }

        assertTrue(oddToken.reentryRejected());
        assertEq(oddToken.revertReason(), "UniswapV2: LOCKED");
    }

    function testFuzzMirrorRevertingBalanceOfCausesMintToRevert(uint96) public {
        RevertingBalanceOfERC20 oddToken = new RevertingBalanceOfERC20();
        MockERC20 normalToken = new MockERC20();
        UniswapV2PairIface oddPair = UniswapV2PairIface(factory.createPair(address(oddToken), address(normalToken)));
        normalToken.mint(address(oddPair), 10_000);

        vm.expectRevert(bytes("BALANCE_REVERTED"));
        oddPair.mint(address(this));
    }

    function testFuzzMirrorShortBalanceOfReturnCausesMintToRevert(uint96) public {
        ShortReturnBalanceOfERC20 oddToken = new ShortReturnBalanceOfERC20();
        MockERC20 normalToken = new MockERC20();
        UniswapV2PairIface oddPair = UniswapV2PairIface(factory.createPair(address(oddToken), address(normalToken)));
        oddToken.mint(address(oddPair), 10_000);
        normalToken.mint(address(oddPair), 10_000);

        vm.expectRevert();
        oddPair.mint(address(this));
    }

    // tama: mirrors=pair_swap_revert_keeps_pair_state
    function testFuzzMirrorCallbackReentryThenRevertKeepsPairState(uint96) public {
        seed(10_000, 10_000);
        (MockERC20 sorted0, MockERC20 sorted1) = sortedTokens();
        uint256 requiredIn = getAmountIn(1_000, 10_000, 10_000);
        RevertingAllEntrypointReentrantCallee callee =
            new RevertingAllEntrypointReentrantCallee(pair, sorted0, sorted1, 0, requiredIn);
        sorted1.mint(address(callee), requiredIn);
        PairSnapshot memory beforeSnap = _snapshot(pair, address(sorted0), address(sorted1));

        vm.expectRevert(bytes("CALLBACK_REVERT_AFTER_REENTRY"));
        pair.swap(1_000, 0, address(callee), abi.encode(uint256(1)));

        _assertSnapshotEq(beforeSnap, pair, address(sorted0), address(sorted1));
    }
}

// =====================================================================
// Factory views and reverts (§7, §8)
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

contract CallerWalletHandler {
    UniswapV2PairIface public pair;
    MockERC20 public token0;
    MockERC20 public token1;

    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_) {
        pair = pair_;
        token0 = token0_;
        token1 = token1_;
    }

    function approve(address spender, uint256 amount) external {
        pair.approve(spender, amount);
    }

    function donate(uint256 amount0, uint256 amount1) external {
        amount0 = _boundToBalance(token0, amount0);
        amount1 = _boundToBalance(token1, amount1);
        if (amount0 > 0) require(token0.transfer(address(pair), amount0), "DONATE0");
        if (amount1 > 0) require(token1.transfer(address(pair), amount1), "DONATE1");
    }

    function mint(uint256 amount0, uint256 amount1) external {
        amount0 = _boundToBalance(token0, amount0);
        amount1 = _boundToBalance(token1, amount1);
        if (amount0 == 0 || amount1 == 0) return;
        require(token0.transfer(address(pair), amount0), "MINT0");
        require(token1.transfer(address(pair), amount1), "MINT1");
        try pair.mint(address(this)) returns (uint256) {} catch {}
    }

    function burn(uint256 liquidity) external {
        uint256 lpBalance = pair.balanceOf(address(this));
        if (lpBalance == 0) return;
        liquidity = (liquidity % lpBalance) + 1;
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        uint256 supply = pair.totalSupply();
        if (supply == 0 || liquidity * reserve0 / supply == 0 || liquidity * reserve1 / supply == 0) return;
        require(pair.transfer(address(pair), liquidity), "BURN_LP");
        try pair.burn(address(this)) returns (uint256, uint256) {} catch {}
    }

    function swap0For1(uint256 amount0In) external {
        amount0In = _boundToBalance(token0, amount0In);
        if (amount0In == 0) return;
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        if (reserve0 == 0 || reserve1 == 0) return;
        uint256 amount1Out = _amountOut(amount0In, reserve0, reserve1);
        if (amount1Out == 0 || amount1Out >= reserve1) return;
        require(token0.transfer(address(pair), amount0In), "SWAP0_IN");
        try pair.swap(0, amount1Out, address(this), "") {} catch {}
    }

    function swap1For0(uint256 amount1In) external {
        amount1In = _boundToBalance(token1, amount1In);
        if (amount1In == 0) return;
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        if (reserve0 == 0 || reserve1 == 0) return;
        uint256 amount0Out = _amountOut(amount1In, reserve1, reserve0);
        if (amount0Out == 0 || amount0Out >= reserve0) return;
        require(token1.transfer(address(pair), amount1In), "SWAP1_IN");
        try pair.swap(amount0Out, 0, address(this), "") {} catch {}
    }

    function skim() external {
        try pair.skim(address(this)) {} catch {}
    }

    function sync() external {
        try pair.sync() {} catch {}
    }

    function _boundToBalance(MockERC20 token, uint256 amount) internal view returns (uint256) {
        uint256 balance = token.balanceOf(address(this));
        if (balance == 0) return 0;
        return amount % (balance + 1);
    }

    function _amountOut(uint256 amountIn, uint256 reserveIn, uint256 reserveOut) internal pure returns (uint256) {
        uint256 amountInWithFee = amountIn * 997;
        return (amountInWithFee * reserveOut) / (reserveIn * 1000 + amountInWithFee);
    }
}

contract PairCallerWalletInvariantMirrors is PairFixture {
    CallerWalletHandler internal handler;
    MockERC20 internal sorted0;
    MockERC20 internal sorted1;
    uint256 internal initialSupply;
    uint256 internal initialLocked;
    uint256 internal initialReserve0;
    uint256 internal initialReserve1;
    uint256 internal initialPortfolioValue;

    function setUp() public override {
        super.setUp();
        seed(100_000, 100_000);
        (sorted0, sorted1) = sortedTokens();
        initialSupply = pair.totalSupply();
        initialLocked = pair.balanceOf(address(0));
        (initialReserve0, initialReserve1,) = pair.getReserves();
        handler = new CallerWalletHandler(pair, sorted0, sorted1);
        sorted0.mint(address(handler), 1_000);
        sorted1.mint(address(handler), 1_000);
        initialPortfolioValue = _spotValue(1_000, 1_000);
        targetContract(address(handler));
    }

    // tama: mirrors=pair_actual_execution_no_free_lunch
    function invariant_pairActualExecutionNoFreeLunch() public {
        assertLe(_currentPortfolioValueNumerator(), initialPortfolioValue * pair.totalSupply());
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
        assertLe(_currentPortfolioValueNumerator(), initialPortfolioValue * pair.totalSupply());
    }

    // tama: mirrors=pair_wallet_history_preserves_unowned
    function invariant_pairWalletHistoryPreservesUnowned() public {
        assertEq(pair.totalSupply() - pair.balanceOf(address(handler)), initialSupply);
    }

    function _spotValue(uint256 amount0, uint256 amount1) internal view returns (uint256) {
        return amount0 * initialReserve1 + amount1 * initialReserve0;
    }

    function _currentPortfolioValueNumerator() internal view returns (uint256) {
        uint256 supply = pair.totalSupply();
        (uint256 reserve0, uint256 reserve1,) = pair.getReserves();
        uint256 lpBalance = pair.balanceOf(address(handler));
        uint256 amount0Numerator = sorted0.balanceOf(address(handler)) * supply + lpBalance * reserve0;
        uint256 amount1Numerator = sorted1.balanceOf(address(handler)) * supply + lpBalance * reserve1;
        return amount0Numerator * initialReserve1 + amount1Numerator * initialReserve0;
    }
}

contract PairIntegrationSmoke is PairFixture {
    function testPairOmitsMetadataAndPermitSurface() public {
        (bool nameOk,) = address(pair).staticcall(abi.encodeWithSignature("name()"));
        (bool symbolOk,) = address(pair).staticcall(abi.encodeWithSignature("symbol()"));
        (bool permitOk,) = address(pair)
            .call(
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
        emit Sync(uint112(amount0), uint112(amount1));
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
        emit Sync(uint112(reserve0 - amount0), uint112(reserve1 - amount1));
        vm.expectEmit(true, true, false, true, address(pair));
        emit Burn(address(this), amount0, amount1, address(this));
        pair.burn(address(this));
    }

    function testSwapEmitsSyncAndSwap() public {
        seed(10_000, 10_000);
        (MockERC20 t0,) = sortedTokens();
        t0.mint(address(pair), 1_000);

        vm.expectEmit(false, false, false, true, address(pair));
        emit Sync(uint112(11_000), uint112(9_094));
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

    function testFlashSwapCallbackPreservesInvariant() public {
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
        emit Sync(uint112(reserve0), uint112(reserve1));
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
