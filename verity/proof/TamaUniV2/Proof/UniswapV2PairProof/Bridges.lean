import TamaUniV2.Proof.UniswapV2PairProof.ViewsAndGuards

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

theorem swap_success_run_implies_lock_open
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) :
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      s.storage unlockedSlot.slot = 1 := by
  intro h_run h_success
  by_contra h_not_open
  have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
    simpa using h_not_open
  have h_revert :=
    swap_run_revert_locked amount0Out amount1Out toAddr data s h_locked
  rw [← h_run, h_success] at h_revert
  cases h_revert

theorem skim_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      s.storage unlockedSlot.slot = 1 := by
  intro h_run h_success
  by_contra h_not_open
  have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
    simpa using h_not_open
  have h_revert := skim_run_revert_locked toAddr s h_locked
  rw [← h_run, h_success] at h_revert
  cases h_revert




-- tama: discharges=pair_swap_success_run_implies_nonzero_output
theorem swap_success_run_implies_nonzero_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) :
  pair_swap_success_run_implies_nonzero_output
    amount0Out amount1Out toAddr data s result := by
  intro h_run h_success
  by_cases h_amount0 : amount0Out = 0
  · by_cases h_amount1 : amount1Out = 0
    · have h_unlocked :=
        swap_success_run_implies_lock_open
          amount0Out amount1Out toAddr data s result h_run h_success
      have h_revert :=
        swap_run_revert_zero_output
          amount0Out amount1Out toAddr data s h_unlocked h_amount0 h_amount1
      rw [h_run] at h_success
      rw [h_revert] at h_success
      cases h_success
    · exact Or.inr h_amount1
  · exact Or.inl h_amount0


-- tama: discharges=pair_skim_success_run_implies_balances_back_reserves
theorem skim_success_run_implies_balances_back_reserves
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_implies_balances_back_reserves toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  constructor
  · by_contra h_not_bound
    have h_not_bound_val :
        ¬ (s.storage reserve0Slot.slot).val ≤ (observedBalance0 s).val := by
      simpa [Verity.Core.Uint256.le_def] using h_not_bound
    have h_under : observedBalance0 s < s.storage reserve0Slot.slot := by
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_not_bound_val
    have h_revert := skim_run_revert_balance0_below_reserve toAddr s h_unlocked h_under
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success
  · by_contra h_not_bound
    have h_not_bound_val :
        ¬ (s.storage reserve1Slot.slot).val ≤ (observedBalance1 s).val := by
      simpa [Verity.Core.Uint256.le_def] using h_not_bound
    have h_under : observedBalance1 s < s.storage reserve1Slot.slot := by
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_not_bound_val
    have h_revert := skim_run_revert_balance1_below_reserve toAddr s h_unlocked h_under
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success

-- tama: discharges=pair_skim_success_run_restores_unlocked_from_run
theorem skim_success_run_restores_unlocked_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_restores_unlocked_from_run toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  rcases skim_success_run_implies_balances_back_reserves
      toAddr s result h_run h_success with
    ⟨h_balance0, h_balance1⟩
  have h_skim :=
    skim_run_success_transfers_excess_and_restores_unlocked
      toAddr s h_unlocked h_balance0 h_balance1
  rcases h_skim with ⟨_h_actual, _h_reserve0, _h_reserve1, h_restored,
    _h_transfer0, _h_transfer1⟩
  rw [h_run]
  exact h_restored

def pair_skim_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      PairWorldStep PairWorldAction.skim
        (pairWorldFromConcreteState s)
        (pairWorldAfterSkimRun s)

theorem skim_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_matches_closed_world_step_from_run toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  rcases skim_success_run_implies_balances_back_reserves
      toAddr s result h_run h_success with
    ⟨h_balance0, h_balance1⟩
  have h_step := skim_run_success_matches_closed_world_step toAddr s
    h_unlocked h_balance0 h_balance1
  rw [← h_run, h_success] at h_step
  exact h_step

def pair_skim_success_run_preserves_world
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      pairWorldFromConcreteState result.snd = pairWorldFromConcreteState s

theorem skim_success_run_preserves_world
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_preserves_world toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  rcases skim_success_run_implies_balances_back_reserves toAddr s result h_run h_success with
    ⟨h_b0, h_b1⟩
  subst h_run
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by simpa [unlockedSlot] using h_unlocked
  have h_require_raw :
      (s.storage 3).val ≤ (observedBalance0 s).val ∧
      (s.storage 4).val ≤ (observedBalance1 s).val := by
    refine ⟨?_, ?_⟩
    · simpa [reserve0Slot] using h_b0
    · simpa [reserve1Slot] using h_b1
  have h_require_raw_unfold := h_require_raw
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_require_raw_unfold
  simp [skim, UniswapV2PairBase.skim, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.pairSafeTransfer, TamaUniV2.tracePairTokenSafeTransfer,
    TamaUniV2.pairTokenSafeTransferEvent, Contracts.safeTransfer,
      pairWorldFromConcreteState, pairWorldLockedLiquidity,
      h_unlocked_raw, h_require_raw_unfold]

theorem skim_success_run_storage_matches_world
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      pairConcreteStorageMatchesWorld result.snd (pairWorldAfterSkimRun s) := by
  intro h_run h_success
  have h_world := skim_success_run_preserves_world toAddr s result h_run h_success
  unfold pairConcreteStorageMatchesWorld
  constructor
  · change (result.snd.storage reserve0Slot.slot).val =
      (s.storage reserve0Slot.slot).val
    exact congrArg PairWorldState.reserve0 h_world
  constructor
  · change (result.snd.storage reserve1Slot.slot).val =
      (s.storage reserve1Slot.slot).val
    exact congrArg PairWorldState.reserve1 h_world
  constructor
  · change (result.snd.storage totalSupplySlot.slot).val =
      (s.storage totalSupplySlot.slot).val
    exact congrArg PairWorldState.totalSupply h_world
  · change pairWorldLockedLiquidity (result.snd.storage totalSupplySlot.slot) =
      pairWorldLockedLiquidity (s.storage totalSupplySlot.slot)
    exact congrArg PairWorldState.lockedLiquidity h_world

-- tama: discharges=pair_skim_success_reaches_expected_pair_state
theorem skim_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances)
    (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_reaches_expected_pair_state toAddr preTokens s result := by
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
          pairWorldAfterSkimRun s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts
      (pairTokenWorldAfterCall preTokens s result) result.snd
      (pairWorldAfterSkimRun s) h_after_tokens
      (skim_success_run_storage_matches_world toAddr s result h_run h_success)
  have h_step :=
    skim_success_run_matches_closed_world_step_from_run
      toAddr s result h_run h_success
  rw [h_before, h_after]
  exact h_step

-- tama: discharges=pair_sync_run_revert_balance0_overflow
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

theorem mint_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) :
  result = (mint toAddr).run s →
    (∃ liquidity, result = ContractResult.success liquidity result.snd) →
      s.storage unlockedSlot.slot = 1 := by
  intro h_run h_success_exists
  rcases h_success_exists with ⟨liquidity, h_success⟩
  by_contra h_not_open
  have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
    simpa using h_not_open
  have h_revert := mint_run_revert_locked toAddr s h_locked
  rw [← h_run, h_success] at h_revert
  cases h_revert

theorem mint_success_run_implies_balances_fit_uint112
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) :
  result = (mint toAddr).run s →
    (∃ liquidity, result = ContractResult.success liquidity result.snd) →
      observedBalance0 s ≤ maxUint112 ∧ observedBalance1 s ≤ maxUint112 := by
  intro h_run h_success_exists
  have h_unlocked :=
    mint_success_run_implies_lock_open toAddr s result h_run h_success_exists
  rcases h_success_exists with ⟨liquidity, h_success⟩
  constructor
  · by_contra h_not_le
    have h_gt : observedBalance0 s > maxUint112 := by
      have h_nat : ¬ (observedBalance0 s).val ≤ maxUint112.val := by
        simpa [Verity.Core.Uint256.le_def] using h_not_le
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_nat
    have h_revert := mint_run_revert_balance0_overflow toAddr s h_unlocked h_gt
    rw [← h_run, h_success] at h_revert
    cases h_revert
  · by_contra h_not_le
    have h_gt : observedBalance1 s > maxUint112 := by
      have h_nat : ¬ (observedBalance1 s).val ≤ maxUint112.val := by
        simpa [Verity.Core.Uint256.le_def] using h_not_le
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_nat
    have h_revert := mint_run_revert_balance1_overflow toAddr s h_unlocked h_gt
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
theorem flash_callback_module_gates_nonempty_data :
  pair_flash_callback_module_gates_nonempty_data := by
  intro ctx target sender amount0Out amount1Out stmts h_compile
  dsimp [TamaUniV2.uniswapV2CallbackModule] at h_compile
  injection h_compile with h_stmts
  exact ⟨_, h_stmts.symm⟩

-- tama: discharges=pair_flash_callback_module_encodes_canonical_call
theorem flash_callback_module_encodes_canonical_call :
  pair_flash_callback_module_encodes_canonical_call := by
  intro ctx target sender amount0Out amount1Out stmts h_compile
  dsimp [TamaUniV2.uniswapV2CallbackModule] at h_compile
  injection h_compile with h_stmts
  let bytesLenExpr := Compiler.Yul.YulExpr.ident "data_length"
  let bytesDataOffset := Compiler.Yul.YulExpr.ident "data_data_offset"
  let bytesDataSlot : Nat := 4 + (3 + 2) * 32
  let paddedBytesLen := Compiler.Yul.YulExpr.call "and" [
    Compiler.Yul.YulExpr.call "add" [bytesLenExpr, Compiler.Yul.YulExpr.lit 31],
    Compiler.Yul.YulExpr.call "not" [Compiler.Yul.YulExpr.lit 31]
  ]
  let totalSize := Compiler.Yul.YulExpr.call "add"
    [Compiler.Yul.YulExpr.lit bytesDataSlot, paddedBytesLen]
  let body :=
    [ Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "mstore" [
        Compiler.Yul.YulExpr.lit 0,
        Compiler.Yul.YulExpr.call "shl"
          [Compiler.Yul.YulExpr.lit 224, Compiler.Yul.YulExpr.hex 0x10d1e85c]])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 4, sender])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 36, amount0Out])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 68, amount1Out])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore"
          [Compiler.Yul.YulExpr.lit 100, Compiler.Yul.YulExpr.lit 128])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore"
          [Compiler.Yul.YulExpr.lit 132, bytesLenExpr])
    ] ++
    Compiler.ECM.dynamicCopyData ctx
      (Compiler.Yul.YulExpr.lit bytesDataSlot) bytesDataOffset bytesLenExpr ++
    [ Compiler.Yul.YulStmt.let_ "__uv2_cb_success"
        (Compiler.Yul.YulExpr.call "call" [
          Compiler.Yul.YulExpr.call "gas" [],
          target,
          Compiler.Yul.YulExpr.lit 0,
          Compiler.Yul.YulExpr.lit 0,
          totalSize,
          Compiler.Yul.YulExpr.lit 0,
          Compiler.Yul.YulExpr.lit 0
        ])
    , Compiler.Yul.YulStmt.if_
        (Compiler.Yul.YulExpr.call "iszero"
          [Compiler.Yul.YulExpr.ident "__uv2_cb_success"])
        [ Compiler.Yul.YulStmt.let_ "__uv2_cb_rds"
            (Compiler.Yul.YulExpr.call "returndatasize" [])
        , Compiler.Yul.YulStmt.expr
            (Compiler.Yul.YulExpr.call "returndatacopy"
              [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.lit 0,
                Compiler.Yul.YulExpr.ident "__uv2_cb_rds"])
        , Compiler.Yul.YulStmt.expr
            (Compiler.Yul.YulExpr.call "revert"
              [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.ident "__uv2_cb_rds"])
        ]
    ]
  refine ⟨body, totalSize, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [body, totalSize, paddedBytesLen, bytesDataSlot, bytesDataOffset,
      bytesLenExpr] using h_stmts.symm
  · simp [body]
  · simp [body]
  · simp [body]
  · simp [body]
  · simp [body, totalSize]

-- tama: discharges=pair_flash_callback_module_bubbles_callback_failure
theorem flash_callback_module_bubbles_callback_failure :
  pair_flash_callback_module_bubbles_callback_failure := by
  intro ctx target sender amount0Out amount1Out stmts h_compile
  dsimp [TamaUniV2.uniswapV2CallbackModule] at h_compile
  injection h_compile with h_stmts
  refine ⟨_, h_stmts.symm, ?_⟩
  simp

def pair_mint_first_expected_matches_closed_world_step
    (_toAddr : Address) (s : ContractState) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  s.storage unlockedSlot.slot = 1 →
    s.storage totalSupplySlot.slot = 0 →
      observedBalance0 s ≤ maxUint112 →
        observedBalance1 s ≤ maxUint112 →
          s.storage reserve0Slot.slot ≤ observedBalance0 s →
            s.storage reserve1Slot.slot ≤ observedBalance1 s →
              amount0 > 0 →
                amount1 > 0 →
                  (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                    mintFirstRoot s > minimumLiquidity →
                      PairWorldStep
                        (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                        (pairWorldBeforeMintRun s)
                        (pairWorldAfterFirstMintRun s)

theorem mint_first_expected_matches_closed_world_step (toAddr : Address) (s : ContractState) :
  pair_mint_first_expected_matches_closed_world_step toAddr s := by
  dsimp [pair_mint_first_expected_matches_closed_world_step]
  intro h_unlocked h_supply_zero h_bound0 h_bound1 h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_supply_zero_raw : s.storage 8 = (0 : Uint256) := by
    simpa [totalSupplySlot] using h_supply_zero
  have h_supply_zero_val : (s.storage 8).val = 0 := by
    rw [h_supply_zero_raw]
    rfl
  unfold PairWorldStep PairWorldMintStep pairWorldBeforeMintRun
    pairWorldAfterFirstMintRun pairWorldLockedLiquidity
  simp only [totalSupplySlot, h_supply_zero_raw, h_supply_zero_val, if_true]
  constructor
  · simpa [mintAmount0] using h_amount0
  constructor
  · simpa [mintAmount1] using h_amount1
  constructor
  · have h_root_le : minimumLiquidity.val ≤ (mintFirstRoot s).val :=
      Nat.le_of_lt h_root
    have h_liquidity_eq :
        (mintFirstLiquidity s).val =
          (mintFirstRoot s).val - minimumLiquidity.val := by
      simpa [mintFirstLiquidity] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := mintFirstRoot s) (b := minimumLiquidity) h_root_le)
    have h_liquidity_pos : 0 < (mintFirstLiquidity s).val := by
      rw [h_liquidity_eq]
      omega
    simpa [mintFirstLiquidity] using h_liquidity_pos
  constructor
  · have h_sub :
        (mintAmount0 s).val =
          (observedBalance0 s).val - (s.storage reserve0Slot.slot).val := by
      simpa [mintAmount0] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance0 s) (b := s.storage reserve0Slot.slot) h_reserve0)
    have h_sub_raw :
        (Verity.EVM.Uint256.sub
            ((Contracts.balanceOf (s.storageAddr 1) s.thisAddress).run s).fst
            (s.storage 3)).val =
          (observedBalance0 s).val - (s.storage reserve0Slot.slot).val := by
      simpa [mintAmount0, observedBalance0, pairToken0, pairSelf,
        TamaUniV2.erc20BalanceOf, Contracts.balanceOf, reserve0Slot, Contract.run,
        ContractResult.fst, Verity.pure, Pure.pure] using h_sub
    change (observedBalance0 s).val =
      (s.storage reserve0Slot.slot).val +
        (Verity.EVM.Uint256.sub
          ((Contracts.balanceOf (s.storageAddr 1) s.thisAddress).run s).fst
          (s.storage 3)).val
    rw [h_sub_raw]
    omega
  constructor
  · have h_sub :
        (mintAmount1 s).val =
          (observedBalance1 s).val - (s.storage reserve1Slot.slot).val := by
      simpa [mintAmount1] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance1 s) (b := s.storage reserve1Slot.slot) h_reserve1)
    have h_sub_raw :
        (Verity.EVM.Uint256.sub
            ((Contracts.balanceOf (s.storageAddr 2) s.thisAddress).run s).fst
            (s.storage 4)).val =
          (observedBalance1 s).val - (s.storage reserve1Slot.slot).val := by
      simpa [mintAmount1, observedBalance1, pairToken1, pairSelf,
        TamaUniV2.erc20BalanceOf, Contracts.balanceOf, reserve1Slot, Contract.run,
        ContractResult.fst, Verity.pure, Pure.pure] using h_sub
    change (observedBalance1 s).val =
      (s.storage reserve1Slot.slot).val +
        (Verity.EVM.Uint256.sub
          ((Contracts.balanceOf (s.storageAddr 2) s.thisAddress).run s).fst
          (s.storage 4)).val
    rw [h_sub_raw]
    omega
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound0
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound1
  constructor
  · have h_root_le : minimumLiquidity.val ≤ (mintFirstRoot s).val :=
      Nat.le_of_lt h_root
    have h_min_val : minimumLiquidity.val = minimumLiquidityNat := by
      change (Verity.Core.Uint256.ofNat 1000).val = (1000 : Nat)
      norm_num [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
        Verity.Core.UINT256_MODULUS]
    have h_liquidity_eq :
        (mintFirstLiquidity s).val =
          (mintFirstRoot s).val - minimumLiquidity.val := by
      simpa [mintFirstLiquidity] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := mintFirstRoot s) (b := minimumLiquidity) h_root_le)
    have h_root_le_nat : minimumLiquidityNat ≤ (mintFirstRoot s).val := by
      rw [← h_min_val]
      exact h_root_le
    have h_root_eq :
        (mintFirstRoot s).val =
          minimumLiquidityNat + ((mintFirstRoot s).val - minimumLiquidityNat) := by
      exact (Nat.add_sub_of_le h_root_le_nat).symm
    simpa [h_supply_zero_val, h_liquidity_eq, h_min_val] using h_root_eq
  · simp [h_supply_zero_val]

def pair_mint_first_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage unlockedSlot.slot = 1 →
        s.storage totalSupplySlot.slot = 0 →
          observedBalance0 s ≤ maxUint112 →
            observedBalance1 s ≤ maxUint112 →
              s.storage reserve0Slot.slot ≤ observedBalance0 s →
                s.storage reserve1Slot.slot ≤ observedBalance1 s →
                  amount0 > 0 →
                    amount1 > 0 →
                      (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                        mintFirstRoot s > minimumLiquidity →
                          PairWorldStep
                            (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                            (pairWorldBeforeMintRun s)
                            (pairWorldAfterFirstMintRun s)

theorem mint_first_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_matches_closed_world_step toAddr s
    ((mint toAddr).run s) := by
  dsimp [pair_mint_first_success_run_matches_closed_world_step]
  intro _h_actual _h_success h_unlocked h_supply_zero h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_product h_root
  exact mint_first_expected_matches_closed_world_step toAddr s
    h_unlocked h_supply_zero h_bound0 h_bound1 h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root

def pair_mint_first_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    PairWorldStep
                      (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                      (pairWorldBeforeMintRun s)
                      (pairWorldAfterFirstMintRun s)

theorem mint_first_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_matches_closed_world_step_from_run toAddr s
    ((mint toAddr).run s) := by
  dsimp [pair_mint_first_success_run_matches_closed_world_step_from_run]
  intro _h_actual h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_success_exists :
      ∃ liquidity,
        (mint toAddr).run s =
          ContractResult.success liquidity ((mint toAddr).run s).snd := by
    exact ⟨mintFirstLiquidity s, h_success⟩
  have h_unlocked :=
    mint_success_run_implies_lock_open toAddr s
      ((mint toAddr).run s) rfl h_success_exists
  rcases mint_success_run_implies_balances_fit_uint112 toAddr s
      ((mint toAddr).run s) rfl h_success_exists with
    ⟨h_bound0, h_bound1⟩
  exact mint_first_expected_matches_closed_world_step toAddr s
    h_unlocked h_supply_zero h_bound0 h_bound1 h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root

theorem updateReservesAndEmitSync_run_storage_matches_world
    (balance0Now balance1Now reserve0Value reserve1Value timestamp32 previousTimestamp : Uint256)
    (s : ContractState) (expected : PairWorldState)
    (h_reserve0 : expected.reserve0 = balance0Now.val)
    (h_reserve1 : expected.reserve1 = balance1Now.val)
    (h_supply : expected.totalSupply = (s.storage totalSupplySlot.slot).val)
    (h_locked : expected.lockedLiquidity = pairWorldLockedLiquidity (s.storage totalSupplySlot.slot)) :
  pairConcreteStorageMatchesWorld
    ((UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
      reserve0Value reserve1Value timestamp32 previousTimestamp).run s).snd
    expected := by
  unfold pairConcreteStorageMatchesWorld
  constructor
  · simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_reserve0,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
    all_goals (split_ifs <;>
      simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore])
  constructor
  · simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_reserve1,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
    all_goals (split_ifs <;>
      simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore])
  constructor
  · simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_supply,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
    all_goals (split_ifs <;>
      simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore])
  · simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_locked,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
    all_goals (split_ifs <;>
      simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore])

theorem finishFirstMint_suffix_run_storage_matches_world
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 root
      liquidity newToBalance timestamp32 previousTimestamp : Uint256)
    (original s : ContractState) :
  root = mintFirstRoot s →
    balance0Now = observedBalance0 s →
      balance1Now = observedBalance1 s →
        root > minimumLiquidity →
        pairConcreteStorageMatchesWorld
          ((UniswapV2PairBase.finishFirstMint toAddr sender
            balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
            root liquidity newToBalance timestamp32 previousTimestamp).run original).snd
          (pairWorldAfterFirstMintRun s) := by
  intro h_root_eq h_balance0 h_balance1 h_root_gt
  subst h_root_eq
  subst h_balance0
  subst h_balance1
  have h_root_ne_zero : (mintFirstRoot s).val ≠ 0 := by
    have h_min_pos : 0 < minimumLiquidity.val := by decide
    change minimumLiquidity.val < (mintFirstRoot s).val at h_root_gt
    omega
  simp [UniswapV2PairBase.finishFirstMint,
    UniswapV2PairBase.updateReservesAndEmitSync, pairConcreteStorageMatchesWorld,
    pairWorldAfterFirstMintRun, pairWorldLockedLiquidity, getStorage, getMapping,
    setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
    Contracts.rawLog, Contracts.mstore, h_root_ne_zero]
  all_goals (split_ifs <;> simp [getStorage, setStorage, setMapping, getMapping,
    Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, emitEvent, Contracts.emit, Contracts.rawLog, Contracts.mstore,
    pairWorldLockedLiquidity, h_root_ne_zero])

theorem finishFirstMintChecked_success_run_storage_matches_world
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 root
      timestamp32 previousTimestamp : Uint256)
    (original s : ContractState) (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.finishFirstMintChecked toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
        root timestamp32 previousTimestamp).run s →
    result = ContractResult.success (sub root minimumLiquidity) result.snd →
      root = mintFirstRoot original →
        balance0Now = observedBalance0 original →
          balance1Now = observedBalance1 original →
            root > minimumLiquidity →
              pairConcreteStorageMatchesWorld result.snd
                (pairWorldAfterFirstMintRun original) := by
  intro h_run h_success h_root h_b0 h_b1 h_root_gt
  subst h_run
  by_cases h_over : Verity.Stdlib.Math.MAX_UINT256 <
      (s.storageMap 9 toAddr).val + (sub root minimumLiquidity).val
  · simp [UniswapV2PairBase.finishFirstMintChecked, getStorage, getMapping,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Verity.Stdlib.Math.safeAdd,
      Verity.Stdlib.Math.requireSomeUint, h_over] at h_success
    cases h_success
  · simp [UniswapV2PairBase.finishFirstMintChecked, getStorage, getMapping,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Verity.Stdlib.Math.safeAdd,
      Verity.Stdlib.Math.requireSomeUint, h_over]
    change pairConcreteStorageMatchesWorld
      ((UniswapV2PairBase.finishFirstMint toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 root
        (sub root minimumLiquidity) ((sub root minimumLiquidity) + (s.storageMap 9 toAddr))
        timestamp32 previousTimestamp).run s).snd
      (pairWorldAfterFirstMintRun original)
    exact finishFirstMint_suffix_run_storage_matches_world toAddr sender
      balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 root
      (sub root minimumLiquidity) ((sub root minimumLiquidity) + (s.storageMap 9 toAddr))
      timestamp32 previousTimestamp s original h_root h_b0 h_b1 h_root_gt

theorem firstMintPath_run_storage_matches_world
    (toAddr sender : Address) (original : ContractState)
    (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.firstMintPath toAddr sender
        (observedBalance0 original) (observedBalance1 original)
        (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
        (mintAmount0 original) (mintAmount1 original)).run
        (mintLockedState original) →
    result = ContractResult.success (mintFirstLiquidity original) result.snd →
      (mintAmount0 original == 0 ||
          div (mintFirstProduct original) (mintAmount0 original) == mintAmount1 original) = true →
        mintFirstRoot original > minimumLiquidity →
          pairConcreteStorageMatchesWorld result.snd
            (pairWorldAfterFirstMintRun original) := by
  intro h_run h_success h_product h_root
  subst h_run
  let checked :=
    (UniswapV2PairBase.finishFirstMintChecked toAddr sender
      (observedBalance0 original) (observedBalance1 original)
      (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
      (mintAmount0 original) (mintAmount1 original) (mintFirstRoot original)
      (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
      (if (5 == 11) = true then 0 else original.storage 5)).run
      (mintLockedState original)
  have h_product_raw :
      (mintAmount0 original == 0 ||
        div (mul (mintAmount0 original) (mintAmount1 original))
          (mintAmount0 original) == mintAmount1 original) = true := by
    simpa [mintFirstProduct] using h_product
  have h_root_val :
      Core.Uint256.val 1000 <
        (sqrtValue (mul (mintAmount0 original) (mintAmount1 original))
          (mintLockedState original)).val := by
    simpa [mintFirstRoot, mintFirstProduct, minimumLiquidity,
      UniswapV2PairBase.minimumLiquidity] using h_root
  have h_root_val2 := h_root_val
  simp [mintLockedState, unlockedSlot, UniswapV2PairBase.unlockedSlot] at h_root_val2
  have h_root_guard :
      Core.Uint256.val 1000 <
        (sqrtValue (mul (mintAmount0 original) (mintAmount1 original))
          { original with «storage» := fun slotIdx =>
              if (slotIdx == 11) = true then 0 else original.storage slotIdx }).val := by
    simpa [mintLockedState, unlockedSlot, UniswapV2PairBase.unlockedSlot] using h_root_val
  have h_product_fold := h_product_raw
  simp [mintAmount0, mintAmount1, mintFirstProduct, observedBalance0,
    observedBalance1, pairToken0, pairToken1, pairSelf, TamaUniV2.erc20BalanceOf,
    Contracts.balanceOf, Contract.run, ContractResult.fst, Verity.pure, Pure.pure]
    at h_product_fold
  let pathResult :=
    (UniswapV2PairBase.firstMintPath toAddr sender
      (observedBalance0 original) (observedBalance1 original)
      (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
      (mintAmount0 original) (mintAmount1 original)).run
      (mintLockedState original)
  have h_path_reduced : pathResult = checked := by
    dsimp only [pathResult]
    simp only [UniswapV2PairBase.firstMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right]
    simp only [Contract.run, Verity.bind, Bind.bind]
    simp only [Verity.require, h_product_raw, if_true]
    simp only [sqrt_run_success_frames_state]
    simp only [Verity.Core.Uint256.lt_def, minimumLiquidity,
      UniswapV2PairBase.minimumLiquidity]
    rw [if_pos (by simpa only [decide_eq_true_eq] using h_root_guard)]
    simp only [Verity.blockTimestamp, getStorage]
    simp only [Verity.pure, Pure.pure, ContractResult.fst, ContractResult.snd]
    simp only [checked, Contract.run, mintFirstRoot, mintFirstProduct,
      mintLockedState, timestamp32, reserve0Slot, reserve1Slot,
      blockTimestampLastSlot, unlockedSlot, UniswapV2PairBase.reserve0Slot,
      UniswapV2PairBase.reserve1Slot,
      UniswapV2PairBase.blockTimestampLastSlot,
      UniswapV2PairBase.unlockedSlot,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus,
      -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment,
      -oraclePrice1Increment, -oraclePrice0CumulativeAfterElapsed,
      -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync,
      -oraclePrice1CumulativeAfterSync, -timestamp32, -oracleElapsed]
  cases h_checked_case : checked with
  | success liquidity post =>
      have h_liquidity : liquidity = mintFirstLiquidity original := by
        change pathResult = ContractResult.success (mintFirstLiquidity original)
          pathResult.snd at h_success
        rw [h_path_reduced, h_checked_case] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
        rfl
      subst liquidity
      have h_checked_success :
          checked = ContractResult.success (mintFirstLiquidity original) checked.snd := by
        simp [h_checked_case]
      have h_checked_storage :
          pairConcreteStorageMatchesWorld checked.snd
            (pairWorldAfterFirstMintRun original) := by
        exact finishFirstMintChecked_success_run_storage_matches_world toAddr sender
          (observedBalance0 original) (observedBalance1 original)
          (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
          (mintAmount0 original) (mintAmount1 original) (mintFirstRoot original)
          (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else original.storage 5)
          original (mintLockedState original) checked
          rfl h_checked_success rfl rfl rfl h_root
      change pairConcreteStorageMatchesWorld pathResult.snd
        (pairWorldAfterFirstMintRun original)
      rw [h_path_reduced, h_checked_case]
      have h_checked_storage_post :
          pairConcreteStorageMatchesWorld post
            (pairWorldAfterFirstMintRun original) := by
        simpa only [h_checked_case, ContractResult.snd] using h_checked_storage
      simpa only [ContractResult.snd] using h_checked_storage_post
  | «revert» reason post =>
      have h_impossible : False := by
        change pathResult = ContractResult.success (mintFirstLiquidity original)
          pathResult.snd at h_success
        rw [h_path_reduced, h_checked_case] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
      cases h_impossible

theorem mint_first_success_run_storage_matches_world
    (toAddr : Address) (s : ContractState) :
  (mint toAddr).run s =
      ContractResult.success (mintFirstLiquidity s) ((mint toAddr).run s).snd →
    s.storage totalSupplySlot.slot = 0 →
      s.storage reserve0Slot.slot ≤ observedBalance0 s →
        s.storage reserve1Slot.slot ≤ observedBalance1 s →
          mintAmount0 s > 0 →
            mintAmount1 s > 0 →
              (mintAmount0 s == 0 || div (mintFirstProduct s) (mintAmount0 s) == mintAmount1 s) = true →
                mintFirstRoot s > minimumLiquidity →
                  pairConcreteStorageMatchesWorld
                    ((mint toAddr).run s).snd (pairWorldAfterFirstMintRun s) := by
  intro h_success h_supply_zero h_reserve0 h_reserve1 h_amount0 h_amount1
    h_product h_root
  have h_success_exists :
      ∃ liquidity,
        (mint toAddr).run s =
          ContractResult.success liquidity ((mint toAddr).run s).snd := by
    exact ⟨mintFirstLiquidity s, h_success⟩
  have h_unlocked :=
    mint_success_run_implies_lock_open toAddr s
      ((mint toAddr).run s) rfl h_success_exists
  rcases mint_success_run_implies_balances_fit_uint112 toAddr s
      ((mint toAddr).run s) rfl h_success_exists with
    ⟨h_bound0, h_bound1⟩
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_supply_zero_raw : s.storage 8 = (0 : Uint256) := by
    simpa [totalSupplySlot] using h_supply_zero
  have h_bfold :
      (observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val := by
    rw [Verity.Core.Uint256.le_def] at h_bound0 h_bound1
    exact ⟨h_bound0, h_bound1⟩
  have h_bfold_base :
      (observedBalance0 s).val ≤ UniswapV2PairBase.maxUint112.val ∧
        (observedBalance1 s).val ≤ UniswapV2PairBase.maxUint112.val := by
    simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bfold
  have h_reserve_fold :
      (s.storage 3).val ≤ (observedBalance0 s).val ∧
        (s.storage 4).val ≤ (observedBalance1 s).val := by
    refine ⟨?_, ?_⟩
    · simpa [reserve0Slot, Verity.Core.Uint256.le_def] using h_reserve0
    · simpa [reserve1Slot, Verity.Core.Uint256.le_def] using h_reserve1
  have h_amount_fold :
      0 < (mintAmount0 s).val ∧ 0 < (mintAmount1 s).val := by
    exact ⟨by simpa [Verity.Core.Uint256.lt_def] using h_amount0,
      by simpa [Verity.Core.Uint256.lt_def] using h_amount1⟩
  have h_root_fold : minimumLiquidity.val < (mintFirstRoot s).val := by
    simpa [Verity.Core.Uint256.lt_def] using h_root
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold h_bfold_base h_reserve_fold
  have h_path_success :
      (UniswapV2PairBase.firstMintPath toAddr s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s) =
        ContractResult.success (mintFirstLiquidity s)
          ((UniswapV2PairBase.firstMintPath toAddr s.sender
            (observedBalance0 s) (observedBalance1 s)
            (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
            (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s)).snd := by
    simpa [mint, UniswapV2PairBase.mint,
      getStorage, getStorageAddr, setStorage, Verity.contractAddress,
      msgSender, Contracts.balanceOf, Verity.require, Contract.run,
      ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, TamaUniV2.erc20BalanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      mintAmount0, mintAmount1, mintLockedState, h_unlocked_raw,
      unlockedSlot, reserve0Slot, reserve1Slot, totalSupplySlot,
      UniswapV2PairBase.unlockedSlot, UniswapV2PairBase.reserve0Slot,
      UniswapV2PairBase.reserve1Slot, UniswapV2PairBase.totalSupplySlot,
      h_supply_zero_raw, h_bfold, h_bfold_base, h_reserve_fold, h_amount_fold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed] using h_success
  simpa [mint, UniswapV2PairBase.mint,
    getStorage, getStorageAddr, setStorage, Verity.contractAddress,
    msgSender, Contracts.balanceOf, Verity.require, Contract.run,
    ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, TamaUniV2.erc20BalanceOf,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    mintAmount0, mintAmount1, mintLockedState, h_unlocked_raw,
    unlockedSlot, reserve0Slot, reserve1Slot, totalSupplySlot,
    UniswapV2PairBase.unlockedSlot, UniswapV2PairBase.reserve0Slot,
    UniswapV2PairBase.reserve1Slot, UniswapV2PairBase.totalSupplySlot,
    h_supply_zero_raw, h_bfold, h_bfold_base, h_reserve_fold, h_amount_fold,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed] using
    (firstMintPath_run_storage_matches_world toAddr s.sender s
      ((UniswapV2PairBase.firstMintPath toAddr s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s))
      rfl h_path_success h_product h_root)

-- tama: discharges=pair_first_mint_success_reaches_expected_pair_state
theorem first_mint_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances) (s : ContractState) :
  pair_first_mint_success_reaches_expected_pair_state
    toAddr preTokens s ((mint toAddr).run s) := by
  intro h_run h_success h_boundary h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  rcases h_boundary with ⟨h_before_tokens, h_after_tokens⟩
  have h_before :
      pairWorldFromConcreteAndTokens preTokens s =
        pairWorldBeforeMintRun s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
      (pairWorldBeforeMintRun s) h_before_tokens
      (by simp [pairConcreteStorageMatchesWorld, pairWorldBeforeMintRun])
  have h_after :
      pairWorldFromConcreteAndTokens
        (pairTokenWorldAfterCall preTokens s ((mint toAddr).run s))
          ((mint toAddr).run s).snd =
        pairWorldAfterFirstMintRun s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts
      (pairTokenWorldAfterCall preTokens s ((mint toAddr).run s))
      ((mint toAddr).run s).snd
      (pairWorldAfterFirstMintRun s) h_after_tokens
      (mint_first_success_run_storage_matches_world toAddr s
        h_success h_supply_zero h_reserve0 h_reserve1 h_amount0 h_amount1
        h_product h_root)
  have h_step :=
    mint_first_success_run_matches_closed_world_step_from_run
      toAddr s h_run h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  rw [h_before, h_after]
  exact h_step

-- tama: discharges=pair_first_mint_uses_balance_increase_as_deposit
theorem first_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState) :
  pair_first_mint_uses_balance_increase_as_deposit
    toAddr s ((mint toAddr).run s) := by
  intro _h_run _h_success _h_supply_zero _h_reserve0 _h_reserve1
  constructor <;> rfl

def pair_mint_subsequent_expected_matches_closed_world_step
    (s : ContractState) (liquidity : Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  0 < (s.storage totalSupplySlot.slot).val →
    s.storage reserve0Slot.slot > 0 →
      s.storage reserve1Slot.slot > 0 →
        observedBalance0 s ≤ maxUint112 →
          observedBalance1 s ≤ maxUint112 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          PairWorldStep
                            (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                            (pairWorldBeforeMintRun s)
                            (pairWorldAfterSubsequentMintRun liquidity s)

theorem mint_subsequent_expected_matches_closed_world_step
    (s : ContractState) (liquidity : Uint256) :
  pair_mint_subsequent_expected_matches_closed_world_step s liquidity := by
  dsimp [pair_mint_subsequent_expected_matches_closed_world_step]
  intro h_supply_pos h_reserve0_pos h_reserve1_pos h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_supply_ne :
      ¬ (s.storage totalSupplySlot.slot).val = 0 :=
    Nat.ne_of_gt h_supply_pos
  have h_supply_ne_raw : ¬ (s.storage 8).val = 0 := by
    simpa [totalSupplySlot] using h_supply_ne
  unfold PairWorldStep PairWorldMintStep pairWorldBeforeMintRun
    pairWorldAfterSubsequentMintRun
  constructor
  · simpa [mintAmount0] using h_amount0
  constructor
  · simpa [mintAmount1] using h_amount1
  constructor
  · simpa using h_liquidity
  constructor
  · have h_sub :
        (mintAmount0 s).val =
          (observedBalance0 s).val - (s.storage reserve0Slot.slot).val := by
      simpa [mintAmount0] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance0 s) (b := s.storage reserve0Slot.slot) h_reserve0)
    have h_sub_raw :
        (Verity.EVM.Uint256.sub
            ((Contracts.balanceOf (s.storageAddr 1) s.thisAddress).run s).fst
            (s.storage 3)).val =
          (observedBalance0 s).val - (s.storage reserve0Slot.slot).val := by
      simpa [mintAmount0, observedBalance0, pairToken0, pairSelf,
        TamaUniV2.erc20BalanceOf, Contracts.balanceOf, reserve0Slot, Contract.run,
        ContractResult.fst, Verity.pure, Pure.pure] using h_sub
    change (observedBalance0 s).val =
      (s.storage reserve0Slot.slot).val +
        (Verity.EVM.Uint256.sub
          ((Contracts.balanceOf (s.storageAddr 1) s.thisAddress).run s).fst
          (s.storage 3)).val
    rw [h_sub_raw]
    omega
  constructor
  · have h_sub :
        (mintAmount1 s).val =
          (observedBalance1 s).val - (s.storage reserve1Slot.slot).val := by
      simpa [mintAmount1] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance1 s) (b := s.storage reserve1Slot.slot) h_reserve1)
    have h_sub_raw :
        (Verity.EVM.Uint256.sub
            ((Contracts.balanceOf (s.storageAddr 2) s.thisAddress).run s).fst
            (s.storage 4)).val =
          (observedBalance1 s).val - (s.storage reserve1Slot.slot).val := by
      simpa [mintAmount1, observedBalance1, pairToken1, pairSelf,
        TamaUniV2.erc20BalanceOf, Contracts.balanceOf, reserve1Slot, Contract.run,
        ContractResult.fst, Verity.pure, Pure.pure] using h_sub
    change (observedBalance1 s).val =
      (s.storage reserve1Slot.slot).val +
        (Verity.EVM.Uint256.sub
          ((Contracts.balanceOf (s.storageAddr 2) s.thisAddress).run s).fst
          (s.storage 4)).val
    rw [h_sub_raw]
    omega
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound0
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound1
  constructor
  · simp [pairWorldLockedLiquidity, totalSupplySlot, h_supply_ne_raw]
  constructor
  · simp [pairWorldLockedLiquidity, totalSupplySlot, h_supply_ne_raw]
  · exact Or.inr ⟨h_ratio0, h_ratio1⟩

def pair_mint_subsequent_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      pair_mint_subsequent_expected_matches_closed_world_step s liquidity

theorem mint_subsequent_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_matches_closed_world_step
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run _h_success
  exact mint_subsequent_expected_matches_closed_world_step s liquidity

def pair_mint_subsequent_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot > 0 →
          s.storage reserve1Slot.slot > 0 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          PairWorldStep
                            (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                            (pairWorldBeforeMintRun s)
                            (pairWorldAfterSubsequentMintRun liquidity s)

theorem mint_subsequent_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_matches_closed_world_step_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  dsimp [pair_mint_subsequent_success_run_matches_closed_world_step_from_run]
  intro _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_success_exists :
      ∃ liquidity',
        (mint toAddr).run s =
          ContractResult.success liquidity' ((mint toAddr).run s).snd := by
    exact ⟨liquidity, h_success⟩
  rcases mint_success_run_implies_balances_fit_uint112 toAddr s
      ((mint toAddr).run s) rfl h_success_exists with
    ⟨h_bound0, h_bound1⟩
  exact mint_subsequent_expected_matches_closed_world_step s liquidity
    h_supply_pos h_reserve0_pos h_reserve1_pos h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1

-- tama: discharges=pair_later_mint_success_reaches_expected_pair_state
theorem later_mint_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances) (s : ContractState)
    (liquidity : Uint256) :
  pair_later_mint_success_reaches_expected_pair_state
    toAddr preTokens s ((mint toAddr).run s) liquidity := by
  intro h_run h_success h_boundary h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  rcases h_boundary with ⟨h_before, h_post⟩
  have h_step :=
    mint_subsequent_success_run_matches_closed_world_step_from_run
      toAddr s liquidity h_run h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1
      h_liquidity h_ratio0 h_ratio1
  rw [h_before, h_post]
  exact h_step

-- tama: discharges=pair_later_mint_uses_balance_increase_as_deposit
theorem later_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  pair_later_mint_uses_balance_increase_as_deposit
    toAddr s liquidity ((mint toAddr).run s) := by
  intro _h_run _h_success _h_supply_pos _h_reserve0 _h_reserve1
  constructor <;> rfl

def pair_burn_expected_matches_closed_world_step
    (s : ContractState) : Prop :=
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  0 < liquidity.val →
    0 < (burnSupply s).val →
      liquidity.val ≤ (burnSupply s).val →
        minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
          amount0 > 0 →
            amount1 > 0 →
              amount0 ≤ observedBalance0 s →
                amount1 ≤ observedBalance1 s →
                  burnBalance0After s ≤ maxUint112 →
                    burnBalance1After s ≤ maxUint112 →
                      amount0.val * (burnSupply s).val ≤
                          liquidity.val * (observedBalance0 s).val →
                        amount1.val * (burnSupply s).val ≤
                            liquidity.val * (observedBalance1 s).val →
                          PairWorldStep
                            (PairWorldAction.burn amount0.val amount1.val liquidity.val)
                            (pairWorldFromConcreteState s)
                            (pairWorldAfterBurnRun s)

theorem burn_expected_matches_closed_world_step
    (s : ContractState) :
  pair_burn_expected_matches_closed_world_step s := by
  dsimp [pair_burn_expected_matches_closed_world_step]
  intro h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
    h_amount0 h_amount1 h_amount0_le h_amount1_le h_bound0 h_bound1
    h_ratio0 h_ratio1
  have h_supply_ne : ¬ (burnSupply s).val = 0 :=
    Nat.ne_of_gt h_supply_pos
  have h_supply_ne_raw : ¬ (s.storage 8).val = 0 := by
    simpa [burnSupply, totalSupplySlot] using h_supply_ne
  have h_balance0_after :
      (burnBalance0After s).val =
        (observedBalance0 s).val - (burnAmount0 s).val := by
    simpa [burnBalance0After] using
      (Verity.Core.Uint256.sub_eq_of_le
        (a := observedBalance0 s) (b := burnAmount0 s) h_amount0_le)
  have h_balance1_after :
      (burnBalance1After s).val =
        (observedBalance1 s).val - (burnAmount1 s).val := by
    simpa [burnBalance1After] using
      (Verity.Core.Uint256.sub_eq_of_le
        (a := observedBalance1 s) (b := burnAmount1 s) h_amount1_le)
  have h_supply_after :
      (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s)).val =
        (burnSupply s).val - (burnLiquidity s).val := by
    simpa using
      (Verity.Core.Uint256.sub_eq_of_le
        (a := burnSupply s) (b := burnLiquidity s) h_liquidity_le)
  unfold PairWorldStep PairWorldBurnStep pairWorldFromConcreteState
    pairWorldAfterBurnRun pairWorldLockedLiquidity
  constructor
  · simpa using h_amount0
  constructor
  · simpa using h_amount1
  constructor
  · exact h_liquidity_pos
  constructor
  · exact h_supply_pos
  constructor
  · simpa using h_amount0_le
  constructor
  · simpa using h_amount1_le
  constructor
  · exact h_liquidity_le
  constructor
  · simp [h_supply_ne]
    simpa [burnSupply, pairWorldLockedLiquidity, totalSupplySlot, h_supply_ne_raw]
      using h_locked_remaining
  constructor
  · exact h_balance0_after
  constructor
  · exact h_balance1_after
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound0
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound1
  constructor
  · exact h_supply_after
  constructor
  · rfl
  constructor
  · exact h_ratio0
  · exact h_ratio1

def pair_burn_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          liquidity.val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
              amount0 > 0 →
                amount1 > 0 →
                  amount0 ≤ observedBalance0 s →
                    amount1 ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          amount0.val * (burnSupply s).val ≤
                              liquidity.val * (observedBalance0 s).val →
                            amount1.val * (burnSupply s).val ≤
                                liquidity.val * (observedBalance1 s).val →
                              PairWorldStep
                                (PairWorldAction.burn amount0.val amount1.val liquidity.val)
                                (pairWorldFromConcreteState s)
                                (pairWorldAfterBurnRun s)

theorem burn_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_matches_closed_world_step toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success
  exact burn_expected_matches_closed_world_step s

-- tama: discharges=pair_burn_success_reaches_expected_pair_state
theorem burn_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances) (s : ContractState) :
  pair_burn_success_reaches_expected_pair_state
    toAddr preTokens s ((burn toAddr).run s) := by
  intro h_run h_success h_boundary h_liquidity_pos h_supply_pos h_liquidity_le
    h_locked_remaining h_amount0_pos h_amount1_pos h_amount0_le h_amount1_le
    h_bound0 h_bound1 h_ratio0 h_ratio1
  rcases h_boundary with ⟨h_before, h_post⟩
  have h_step :=
    burn_success_run_matches_closed_world_step toAddr s h_run h_success
      h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
      h_amount0_pos h_amount1_pos h_amount0_le h_amount1_le h_bound0
      h_bound1 h_ratio0 h_ratio1
  rw [h_before, h_post]
  exact h_step

-- tama: discharges=pair_burn_uses_pair_lp_balance_and_total_supply
theorem burn_uses_pair_lp_balance_and_total_supply
    (toAddr : Address) (s : ContractState) :
  pair_burn_uses_pair_lp_balance_and_total_supply
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success
  constructor <;> rfl

-- tama: discharges=pair_burn_leaves_remaining_token_balances
theorem burn_leaves_remaining_token_balances
    (toAddr : Address) (s : ContractState) :
  pair_burn_leaves_remaining_token_balances
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success h_amount0 h_amount1
  constructor
  · have h_sub :
        (burnBalance0After s).val =
          (observedBalance0 s).val - (burnAmount0 s).val := by
      simpa [burnBalance0After] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance0 s) (b := burnAmount0 s) h_amount0)
    have h_le : (burnAmount0 s).val ≤ (observedBalance0 s).val := by
      simpa using h_amount0
    change (burnBalance0After s).val + (burnAmount0 s).val =
      (observedBalance0 s).val
    rw [h_sub]
    omega
  · have h_sub :
        (burnBalance1After s).val =
          (observedBalance1 s).val - (burnAmount1 s).val := by
      simpa [burnBalance1After] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance1 s) (b := burnAmount1 s) h_amount1)
    have h_le : (burnAmount1 s).val ≤ (observedBalance1 s).val := by
      simpa using h_amount1
    change (burnBalance1After s).val + (burnAmount1 s).val =
      (observedBalance1 s).val
    rw [h_sub]
    omega

theorem feeAdjustedSwap_implies_raw_k
    (amount0In amount1In : Nat)
    (before after : PairWorldState) :
  after.reserve0 = after.balance0 →
    after.reserve1 = after.balance1 →
      feeAdjustedBalance after.balance0 amount0In *
          feeAdjustedBalance after.balance1 amount1In ≥
        requiredK before.reserve0 before.reserve1 →
        PairWorldK before ≤ PairWorldK after := by
  intro h_reserve0 h_reserve1 h_adjusted_k
  have h_adjusted0_le :
      feeAdjustedBalance after.balance0 amount0In ≤
        after.balance0 * feeDenominatorNat := by
    unfold feeAdjustedBalance
    exact Nat.sub_le _ _
  have h_adjusted1_le :
      feeAdjustedBalance after.balance1 amount1In ≤
        after.balance1 * feeDenominatorNat := by
    unfold feeAdjustedBalance
    exact Nat.sub_le _ _
  have h_adjusted_product_le :
      feeAdjustedBalance after.balance0 amount0In *
          feeAdjustedBalance after.balance1 amount1In ≤
        (after.balance0 * feeDenominatorNat) *
          (after.balance1 * feeDenominatorNat) :=
    Nat.mul_le_mul h_adjusted0_le h_adjusted1_le
  have h_required_le_scaled :=
    Nat.le_trans h_adjusted_k h_adjusted_product_le
  have h_scale_pos : 0 < feeDenominatorNat * feeDenominatorNat := by
    norm_num [feeDenominatorNat]
  have h_scaled :
      PairWorldK before * (feeDenominatorNat * feeDenominatorNat) ≤
        PairWorldK after * (feeDenominatorNat * feeDenominatorNat) := by
    unfold requiredK at h_required_le_scaled
    unfold PairWorldK
    rw [h_reserve0, h_reserve1]
    nlinarith [h_required_le_scaled]
  exact Nat.le_of_mul_le_mul_right h_scaled h_scale_pos

def pair_swap_expected_matches_closed_world_step
    (amount0Out amount1Out balance0Now balance1Now : Uint256)
    (s : ContractState) : Prop :=
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  (amount0Out > 0 ∨ amount1Out > 0) →
    amount0Out < s.storage reserve0Slot.slot →
      amount1Out < s.storage reserve1Slot.slot →
        (amount0In > 0 ∨ amount1In > 0) →
          balance0Now.val =
              (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
            balance1Now.val =
                (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
              balance0Now ≤ maxUint112 →
                balance1Now ≤ maxUint112 →
                  amount0In.val * feeAdjustmentNat ≤
                      balance0Now.val * feeDenominatorNat →
                    amount1In.val * feeAdjustmentNat ≤
                        balance1Now.val * feeDenominatorNat →
                      feeAdjustedBalance balance0Now.val amount0In.val *
                          feeAdjustedBalance balance1Now.val amount1In.val ≥
                        requiredK
                          (s.storage reserve0Slot.slot).val
                          (s.storage reserve1Slot.slot).val →
                          PairWorldStep
                            (PairWorldAction.swap
                              amount0In.val amount1In.val
                              amount0Out.val amount1Out.val)
                            (pairWorldFromConcreteState s)
                            (pairWorldAfterSwapRun balance0Now balance1Now s)

theorem swap_expected_matches_closed_world_step
    (amount0Out amount1Out balance0Now balance1Now : Uint256)
    (s : ContractState) :
  pair_swap_expected_matches_closed_world_step
    amount0Out amount1Out balance0Now balance1Now s := by
  dsimp [pair_swap_expected_matches_closed_world_step]
  intro h_output h_liq0 h_liq1 h_input h_balance0 h_balance1 h_bound0 h_bound1
    h_fee0 h_fee1 h_adjusted_k
  unfold PairWorldStep PairWorldSwapStep pairWorldFromConcreteState
    pairWorldAfterSwapRun
  constructor
  · exact h_output
  constructor
  · simpa using h_liq0
  constructor
  · simpa using h_liq1
  constructor
  · have h_liq0_nat : amount0Out.val < (s.storage reserve0Slot.slot).val := by
      simpa using h_liq0
    exact Nat.le_trans (Nat.le_of_lt h_liq0_nat)
      (Nat.le_add_right
        (s.storage reserve0Slot.slot).val
        (swapAmount0In amount0Out balance0Now s).val)
  constructor
  · have h_liq1_nat : amount1Out.val < (s.storage reserve1Slot.slot).val := by
      simpa using h_liq1
    exact Nat.le_trans (Nat.le_of_lt h_liq1_nat)
      (Nat.le_add_right
        (s.storage reserve1Slot.slot).val
        (swapAmount1In amount1Out balance1Now s).val)
  constructor
  · exact h_input
  constructor
  · exact h_balance0
  constructor
  · exact h_balance1
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound0
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound1
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact h_fee0
  constructor
  · exact h_fee1
  · exact h_adjusted_k

def pair_swap_success_run_matches_closed_world_step
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      pair_swap_expected_matches_closed_world_step
        amount0Out amount1Out balance0Now balance1Now s

theorem swap_success_run_matches_closed_world_step
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_matches_closed_world_step
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run _h_success
  exact swap_expected_matches_closed_world_step
    amount0Out amount1Out balance0Now balance1Now s

-- tama: discharges=pair_swap_uses_final_balances_to_compute_input
theorem swap_uses_final_balances_to_compute_input
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_uses_final_balances_to_compute_input
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run _h_success
  simp [pair_swap_uses_final_balances_to_compute_input, swapAmount0In,
    swapAmount1In, swapAmountIn]

-- tama: discharges=pair_swap_checks_k_against_final_balances
theorem swap_checks_k_against_final_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_checks_k_against_final_balances
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run _h_success h_k
  simpa [pair_swap_checks_k_against_final_balances,
    pairWorldAfterSwapRun, pairWorldFromConcreteState] using h_k

def pair_swap_success_run_matches_closed_world_step_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                            PairWorldStep
                            (PairWorldAction.swap
                              amount0In.val amount1In.val
                              amount0Out.val amount1Out.val)
                            (pairWorldFromConcreteState s)
                            (pairWorldAfterSwapRun balance0Now balance1Now s)

theorem swap_success_run_matches_closed_world_step_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_matches_closed_world_step_from_run
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  have h_nonzero :=
    swap_success_run_implies_nonzero_output
      amount0Out amount1Out toAddr data s
      ((swap amount0Out amount1Out toAddr data).run s) rfl h_success
  have h_output : amount0Out > 0 ∨ amount1Out > 0 := by
    rcases h_nonzero with h_amount0 | h_amount1
    · exact Or.inl (uint256_pos_of_ne_zero h_amount0)
    · exact Or.inr (uint256_pos_of_ne_zero h_amount1)
  exact swap_expected_matches_closed_world_step
    amount0Out amount1Out balance0Now balance1Now s h_output
    h_liq0 h_liq1 h_input h_balance0 h_balance1 h_bound0 h_bound1
    h_fee0 h_fee1 h_adjusted_k

-- tama: discharges=pair_swap_success_reaches_expected_pair_state
theorem swap_success_reaches_expected_pair_state
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (preTokens : PairTokenBalances)
    (s : ContractState) :
  pair_swap_success_reaches_expected_pair_state
    amount0Out amount1Out toAddr data balance0Now balance1Now preTokens s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_run h_success h_boundary h_liq0 h_liq1 h_input h_balance0
    h_balance1 h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  rcases h_boundary with ⟨h_before, h_post⟩
  have h_step :=
    swap_success_run_matches_closed_world_step_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  rw [h_before, h_post]
  exact h_step


end TamaUniV2.Proof.UniswapV2PairProof
