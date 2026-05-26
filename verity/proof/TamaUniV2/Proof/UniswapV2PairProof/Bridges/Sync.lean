import TamaUniV2.Proof.UniswapV2PairProof.Bridges.Common
namespace TamaUniV2.Proof.UniswapV2PairProof

set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

open Verity
open Verity.EVM.Uint256
open TamaUniV2.Spec.UniswapV2PairSpec
open TamaUniV2.UniswapV2Pair
open TamaUniV2.Common.UniswapV2PairConcrete
open TamaUniV2.Common.UniswapV2PairGhost

attribute [local simp] decimals totalSupply balanceOf allowance factory token0 token1
  MINIMUM_LIQUIDITY getReserves price0CumulativeLast price1CumulativeLast kLast
  «initialize» approve transfer transferFrom mint burn swap skim sync
  factorySlot token0Slot token1Slot reserve0Slot reserve1Slot blockTimestampLastSlot
  totalSupplySlot balancesSlot allowancesSlot price0CumulativeLastSlot price1CumulativeLastSlot
  unlockedSlot feeDenominator feeAdjustment maxUint112 maxUint256 q112 uint32Modulus
  UniswapV2PairBase.decimals UniswapV2PairBase.totalSupply
  UniswapV2PairBase.balanceOf UniswapV2PairBase.allowance
  UniswapV2PairBase.factory UniswapV2PairBase.token0 UniswapV2PairBase.token1
  UniswapV2PairBase.MINIMUM_LIQUIDITY UniswapV2PairBase.getReserves
  UniswapV2PairBase.price0CumulativeLast
  UniswapV2PairBase.price1CumulativeLast UniswapV2PairBase.kLast
  UniswapV2PairBase.«initialize» UniswapV2PairBase.approve
  UniswapV2PairBase.transfer UniswapV2PairBase.transferFrom
  UniswapV2PairBase.mint UniswapV2PairBase.burn UniswapV2PairBase.swap
  UniswapV2PairBase.skim UniswapV2PairBase.sync
  UniswapV2PairBase.factorySlot UniswapV2PairBase.token0Slot
  UniswapV2PairBase.token1Slot UniswapV2PairBase.reserve0Slot
  UniswapV2PairBase.reserve1Slot UniswapV2PairBase.blockTimestampLastSlot
  UniswapV2PairBase.totalSupplySlot UniswapV2PairBase.balancesSlot
  UniswapV2PairBase.allowancesSlot UniswapV2PairBase.price0CumulativeLastSlot
  UniswapV2PairBase.price1CumulativeLastSlot UniswapV2PairBase.unlockedSlot
  UniswapV2PairBase.feeDenominator UniswapV2PairBase.feeAdjustment
  UniswapV2PairBase.maxUint112 UniswapV2PairBase.maxUint256
  UniswapV2PairBase.q112 UniswapV2PairBase.uint32Modulus
  TamaUniV2.erc20BalanceOf pairSelf pairToken0 pairToken1 observedBalance0 observedBalance1
  TamaUniV2.pairSafeTransfer TamaUniV2.tracePairTokenSafeTransfer
  TamaUniV2.pairTokenSafeTransferEvent pairTraceContains hasPairSafeTransferTrace
  pairLpApprovalEvent pairLpTransferEvent pairMintEvent pairBurnEvent pairSwapEvent pairSyncEvent
  mintAmount0 mintAmount1 timestamp32 oracleElapsed oraclePrice0 oraclePrice1
  oraclePrice0Increment oraclePrice1Increment
  oraclePrice0CumulativeAfterElapsed oraclePrice1CumulativeAfterElapsed
  oraclePrice0CumulativeAfterSync oraclePrice1CumulativeAfterSync
  skimExcess0 skimExcess1
  swapExpected0 swapExpected1 swapAmountIn swapAmount0In swapAmount1In
  swapBalance0Scaled swapBalance1Scaled swapAmount0Fee swapAmount1Fee
  swapBalance0Adjusted swapBalance1Adjusted swapAdjustedProduct swapReserveProductOf
  swapReserveProduct swapScaleProduct swapRequiredProductOf swapRequiredProduct
  Contracts.emit emitEvent

attribute [local simp] sqrt_run_success_frames_state
theorem sync_run_revert_balance0_overflow (s : ContractState) :
  pair_sync_run_revert_balance0_overflow s := by
  intro h_unlocked h_overflow
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_require_false :
      ¬ ((observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val) := by
    intro h
    exact (Nat.not_le_of_gt (by simpa [Verity.Core.Uint256.lt_def] using h_overflow)) h.1
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_sync_run_revert_balance0_overflow, sync, UniswapV2PairBase.sync,
    unlockedSlot, token0Slot, token1Slot, maxUint112, UniswapV2PairBase.maxUint112,
    getStorage, getStorageAddr, setStorage, Verity.blockTimestamp,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, observedBalance0,
    observedBalance1, pairToken0, pairToken1, pairSelf, TamaUniV2.erc20BalanceOf,
    h_unlocked_raw, h_require_false_raw]

-- tama: discharges=pair_sync_run_revert_balance1_overflow
theorem sync_run_revert_balance1_overflow (s : ContractState) :
  pair_sync_run_revert_balance1_overflow s := by
  intro h_unlocked h_overflow
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_require_false :
      ¬ ((observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val) := by
    intro h
    exact (Nat.not_le_of_gt (by simpa [Verity.Core.Uint256.lt_def] using h_overflow)) h.2
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_sync_run_revert_balance1_overflow, sync, UniswapV2PairBase.sync,
    unlockedSlot, token0Slot, token1Slot, maxUint112, UniswapV2PairBase.maxUint112,
    getStorage, getStorageAddr, setStorage, Verity.blockTimestamp,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, observedBalance0,
    observedBalance1, pairToken0, pairToken1, pairSelf, TamaUniV2.erc20BalanceOf,
    h_unlocked_raw, h_require_false_raw]

theorem sync_success_run_implies_balances_fit_uint112
    (s : ContractState) (result : ContractResult Unit) :
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      observedBalance0 s ≤ maxUint112 ∧ observedBalance1 s ≤ maxUint112 := by
  intro h_run h_success
  have h_unlocked : s.storage unlockedSlot.slot = 1 := by
    by_contra h_not_open
    have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
      simpa using h_not_open
    have h_revert := sync_run_revert_locked s h_locked
    rw [← h_run, h_success] at h_revert
    cases h_revert
  constructor
  · by_contra h_not_le
    have h_gt : observedBalance0 s > maxUint112 := by
      have h_nat : ¬ (observedBalance0 s).val ≤ maxUint112.val := by
        simpa [Verity.Core.Uint256.le_def] using h_not_le
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_nat
    have h_revert := sync_run_revert_balance0_overflow s h_unlocked h_gt
    rw [← h_run, h_success] at h_revert
    cases h_revert
  · by_contra h_not_le
    have h_gt : observedBalance1 s > maxUint112 := by
      have h_nat : ¬ (observedBalance1 s).val ≤ maxUint112.val := by
        simpa [Verity.Core.Uint256.le_def] using h_not_le
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_nat
    have h_revert := sync_run_revert_balance1_overflow s h_unlocked h_gt
    rw [← h_run, h_success] at h_revert
    cases h_revert

def pair_sync_expected_matches_closed_world_step
    (s : ContractState) : Prop :=
  observedBalance0 s ≤ maxUint112 →
    observedBalance1 s ≤ maxUint112 →
      PairWorldStep PairWorldAction.sync
        (pairWorldFromConcreteState s)
        (pairWorldAfterSyncRun s)

theorem sync_expected_matches_closed_world_step (s : ContractState) :
  pair_sync_expected_matches_closed_world_step s := by
  intro h_bound0 h_bound1
  simp [pair_sync_expected_matches_closed_world_step, PairWorldStep,
    PairWorldSyncStep, pairWorldFromConcreteState, pairWorldAfterSyncRun,
    pairWorldLockedLiquidity, maxUint112Nat, maxUint112,
    UniswapV2PairBase.maxUint112]
  exact ⟨by simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using h_bound0,
    by simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using h_bound1⟩

def pair_sync_success_run_matches_closed_world_step
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      observedBalance0 s ≤ maxUint112 →
        observedBalance1 s ≤ maxUint112 →
          PairWorldStep PairWorldAction.sync
            (pairWorldFromConcreteState s)
            (pairWorldAfterSyncRun s)

theorem sync_success_run_matches_closed_world_step
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_matches_closed_world_step s result := by
  intro _h_run _h_success h_bound0 h_bound1
  exact sync_expected_matches_closed_world_step s h_bound0 h_bound1



def pair_sync_success_run_matches_closed_world_step_from_run
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      PairWorldStep PairWorldAction.sync
        (pairWorldFromConcreteState s)
        (pairWorldAfterSyncRun s)

theorem sync_success_run_matches_closed_world_step_from_run
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_matches_closed_world_step_from_run s result := by
  intro h_run h_success
  rcases sync_success_run_implies_balances_fit_uint112
      s result h_run h_success with
    ⟨h_bound0, h_bound1⟩
  exact sync_expected_matches_closed_world_step s h_bound0 h_bound1

theorem sync_unlocked_raw
    (s : ContractState) (h_unlocked : s.storage unlockedSlot.slot = 1) :
    s.storage 11 = (1 : Uint256) := by simpa [unlockedSlot] using h_unlocked

theorem sync_bound_val
    (s : ContractState)
    (h0 : observedBalance0 s ≤ maxUint112) (h1 : observedBalance1 s ≤ maxUint112) :
    (observedBalance0 s).val ≤ maxUint112.val ∧ (observedBalance1 s).val ≤ maxUint112.val := by
  rw [Verity.Core.Uint256.le_def] at h0 h1
  exact ⟨h0, h1⟩

theorem sync_post_reserve0_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    (sync.run s).snd.storage reserve0Slot.slot = observedBalance0 s := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit :
      (observedBalance0 s).val ≤ UniswapV2PairBase.maxUint112.val ∧
        (observedBalance1 s).val ≤ UniswapV2PairBase.maxUint112.val := by
    simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bfold
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    UniswapV2PairBase.updateReservesAndEmitSync,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

theorem sync_post_reserve1_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    (sync.run s).snd.storage reserve1Slot.slot = observedBalance1 s := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit :
      (observedBalance0 s).val ≤ UniswapV2PairBase.maxUint112.val ∧
        (observedBalance1 s).val ≤ UniswapV2PairBase.maxUint112.val := by
    simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bfold
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    UniswapV2PairBase.updateReservesAndEmitSync,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

theorem sync_post_supply_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    (sync.run s).snd.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit :
      (observedBalance0 s).val ≤ UniswapV2PairBase.maxUint112.val ∧
        (observedBalance1 s).val ≤ UniswapV2PairBase.maxUint112.val := by
    simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bfold
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    UniswapV2PairBase.updateReservesAndEmitSync,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

theorem sync_post_obs0_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    observedBalance0 (sync.run s).snd = observedBalance0 s := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit :
      (observedBalance0 s).val ≤ UniswapV2PairBase.maxUint112.val ∧
        (observedBalance1 s).val ≤ UniswapV2PairBase.maxUint112.val := by
    simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bfold
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    UniswapV2PairBase.updateReservesAndEmitSync,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore, ContractResult.fst, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore, ContractResult.fst, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

theorem sync_post_obs1_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    observedBalance1 (sync.run s).snd = observedBalance1 s := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit :
      (observedBalance0 s).val ≤ UniswapV2PairBase.maxUint112.val ∧
        (observedBalance1 s).val ≤ UniswapV2PairBase.maxUint112.val := by
    simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bfold
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    UniswapV2PairBase.updateReservesAndEmitSync,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore, ContractResult.fst, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore, ContractResult.fst, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

def pair_sync_success_run_reaches_world
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      pairWorldFromConcreteState result.snd = pairWorldAfterSyncRun s

theorem sync_success_run_reaches_world
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_reaches_world s result := by
  intro h_run h_success
  have h_unlocked : s.storage unlockedSlot.slot = 1 := by
    by_contra h_not_open
    have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
      simpa using h_not_open
    have h_revert := sync_run_revert_locked s h_locked
    rw [← h_run, h_success] at h_revert
    cases h_revert
  rcases sync_success_run_implies_balances_fit_uint112 s result h_run h_success with
    ⟨h_bound0, h_bound1⟩
  subst h_run
  simp only [pairWorldFromConcreteState, pairWorldAfterSyncRun, pairWorldLockedLiquidity,
    sync_post_obs0_run s h_unlocked h_bound0 h_bound1,
    sync_post_obs1_run s h_unlocked h_bound0 h_bound1,
    sync_post_reserve0_run s h_unlocked h_bound0 h_bound1,
    sync_post_reserve1_run s h_unlocked h_bound0 h_bound1,
    sync_post_supply_run s h_unlocked h_bound0 h_bound1]

theorem sync_success_run_storage_matches_world
    (s : ContractState) (result : ContractResult Unit) :
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      pairConcreteStorageMatchesWorld result.snd (pairWorldAfterSyncRun s) := by
  intro h_run h_success
  have h_world := sync_success_run_reaches_world s result h_run h_success
  unfold pairConcreteStorageMatchesWorld
  constructor
  · exact congrArg PairWorldState.reserve0 h_world
  constructor
  · exact congrArg PairWorldState.reserve1 h_world
  constructor
  · exact congrArg PairWorldState.totalSupply h_world
  · exact congrArg PairWorldState.lockedLiquidity h_world

theorem sync_run_token_world_unchanged
    (preTokens : PairTokenBalances) (s : ContractState) :
  pairTokenWorldAfterCall preTokens s ((sync).run s) = preTokens := by
  unfold sync UniswapV2PairBase.sync
  simp [pairTokenWorldAfterCall, emittedPairEventsAfterCall,
    getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure,
    TamaUniV2.erc20BalanceOf, UniswapV2PairBase.updateReservesAndEmitSync,
    pairTokenWorldAfterEvents, pairTokenWorldAfterEvent, Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [pairTokenWorldAfterEvents, pairTokenWorldAfterEvent, getStorage, setStorage,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure,
        Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem sync_run_storageAddr_frame
    (s : ContractState) (i : Nat) :
  ((sync).run s).snd.storageAddr i = s.storageAddr i := by
  unfold sync UniswapV2PairBase.sync
  simp [getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure,
    TamaUniV2.erc20BalanceOf, UniswapV2PairBase.updateReservesAndEmitSync,
    Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [getStorage, setStorage, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Pure.pure, Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem sync_run_balances_frame
    (s : ContractState) (a : Address) :
  ((sync).run s).snd.storageMap balancesSlot.slot a =
    s.storageMap balancesSlot.slot a := by
  unfold sync UniswapV2PairBase.sync
  simp [getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Pure.pure,
    TamaUniV2.erc20BalanceOf, UniswapV2PairBase.updateReservesAndEmitSync,
    Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [getStorage, setStorage, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Pure.pure, Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

-- tama: discharges=pair_sync_success_reaches_expected_pair_state
theorem sync_success_reaches_expected_pair_state
    (preTokens : PairTokenBalances)
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_reaches_expected_pair_state preTokens s result := by
  intro h_run h_success h_tokens
  rcases h_tokens with ⟨h_before_tokens, h_after_tokens⟩
  have h_before :
      pairWorldFromConcreteAndTokens preTokens s =
        pairWorldFromConcreteState s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
      (pairWorldFromConcreteState s) h_before_tokens
      (by simp [pairConcreteStorageMatchesWorld, pairWorldFromConcreteState])
  have h_after :
      pairWorldFromConcreteAndTokens
        (pairTokenWorldAfterCall preTokens s result) result.snd =
          pairWorldAfterSyncRun s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts
      (pairTokenWorldAfterCall preTokens s result) result.snd
      (pairWorldAfterSyncRun s) h_after_tokens
      (sync_success_run_storage_matches_world s result h_run h_success)
  have h_step :=
    sync_success_run_matches_closed_world_step_from_run s result h_run h_success
  rw [h_before, h_after]
  exact h_step

-- tama: discharges=pair_flash_callback_module_gates_nonempty_data

end TamaUniV2.Proof.UniswapV2PairProof
