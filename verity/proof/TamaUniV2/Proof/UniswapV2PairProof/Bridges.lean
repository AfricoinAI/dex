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

theorem burn_run_revert_amount0_product_overflow
    (toAddr : Address) (s : ContractState) :
  s.storage unlockedSlot.slot = 1 →
    burnLiquidity s > 0 →
      burnSupply s > 0 →
        (burnLiquidity s == 0 ||
            div (burnAmount0Product s) (burnLiquidity s) == observedBalance0 s) = false →
          (burn toAddr).run s =
            ContractResult.revert "UniswapV2: BURN_OVERFLOW" s := by
  intro h_unlocked h_liquidity_pos h_supply_pos h_guard_false
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_liquidity_guard :
      (decide (burnLiquidity s > 0) && decide (burnSupply s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_liquidity_pos h_supply_pos
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_timestamp :
      Verity.blockTimestamp s = ContractResult.success s.blockTimestamp s := rfl
  have h_previous :
      getStorage UniswapV2PairBase.blockTimestampLastSlot s =
        ContractResult.success (s.storage blockTimestampLastSlot.slot) s := by
    simp only [getStorage, blockTimestampLastSlot, UniswapV2PairBase.blockTimestampLastSlot]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_sender :
      msgSender (mintLockedState s) =
        ContractResult.success s.sender (mintLockedState s) := rfl
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_self :
      contractAddress (mintLockedState s) =
        ContractResult.success (mintLockedState s).thisAddress (mintLockedState s) := rfl
  have h_balance0 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance0 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance0_balanceOf_mintLockedState_app_nf s
  have h_balance1 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance1 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance1_balanceOf_mintLockedState_app_nf s
  have h_liquidity :
      getMapping UniswapV2PairBase.balancesSlot (mintLockedState s).thisAddress
          (mintLockedState s) =
        ContractResult.success (burnLiquidity s) (mintLockedState s) := by
    simp [getMapping, burnLiquidity, pairSelf, balancesSlot,
      UniswapV2PairBase.balancesSlot, mintLockedState, mintLockedState_thisAddress]
  have h_supply :
      getStorage UniswapV2PairBase.totalSupplySlot (mintLockedState s) =
        ContractResult.success (burnSupply s) (mintLockedState s) := by
    simp [getStorage, burnSupply, totalSupplySlot, UniswapV2PairBase.totalSupplySlot,
      mintLockedState, mintLockedState_storage_totalSupply]
  have h_req_liquidity :
      Verity.require (decide (burnLiquidity s > 0) && decide (burnSupply s > 0))
        "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED" (mintLockedState s) =
          ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_liquidity_guard, if_true]
  have h_req_overflow :
      Verity.require
          (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance0 s)) (burnLiquidity s) ==
              observedBalance0 s)
          "UniswapV2: BURN_OVERFLOW" (mintLockedState s) =
        ContractResult.revert "UniswapV2: BURN_OVERFLOW" (mintLockedState s) := by
    have h_guard_false_mul :
        (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance0 s)) (burnLiquidity s) ==
              observedBalance0 s) = false := by
      simpa [burnAmount0Product] using h_guard_false
    simp only [Verity.require, h_guard_false_mul, Bool.false_eq_true, if_false]
  unfold burn UniswapV2PairBase.burn Contract.run
  rw [contract_bind_success _ _ _ _ _ h_get_lock]
  rw [contract_bind_success _ _ _ _ _ h_req_lock]
  rw [contract_bind_success _ _ _ _ _ h_timestamp]
  rw [contract_bind_success _ _ _ _ _ h_previous]
  rw [contract_bind_success _ _ _ _ _ h_set_lock]
  rw [contract_bind_success _ _ _ _ _ h_sender]
  rw [contract_bind_success _ _ _ _ _ h_token0]
  rw [contract_bind_success _ _ _ _ _ h_token1]
  rw [contract_bind_success _ _ _ _ _ h_self]
  rw [contract_bind_success _ _ _ _ _ h_balance0]
  rw [contract_bind_success _ _ _ _ _ h_balance1]
  rw [contract_bind_success _ _ _ _ _ h_liquidity]
  rw [contract_bind_success _ _ _ _ _ h_supply]
  rw [contract_bind_success _ _ _ _ _ h_req_liquidity]
  simp only [Bind.bind, Verity.bind, h_req_overflow]

theorem burn_run_revert_amount1_product_overflow
    (toAddr : Address) (s : ContractState) :
  s.storage unlockedSlot.slot = 1 →
    burnLiquidity s > 0 →
      burnSupply s > 0 →
        (burnLiquidity s == 0 ||
            div (burnAmount0Product s) (burnLiquidity s) == observedBalance0 s) = true →
          (burnLiquidity s == 0 ||
              div (burnAmount1Product s) (burnLiquidity s) == observedBalance1 s) = false →
            (burn toAddr).run s =
              ContractResult.revert "UniswapV2: BURN_OVERFLOW" s := by
  intro h_unlocked h_liquidity_pos h_supply_pos h_guard0_true h_guard_false
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_liquidity_guard :
      (decide (burnLiquidity s > 0) && decide (burnSupply s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_liquidity_pos h_supply_pos
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_timestamp :
      Verity.blockTimestamp s = ContractResult.success s.blockTimestamp s := rfl
  have h_previous :
      getStorage UniswapV2PairBase.blockTimestampLastSlot s =
        ContractResult.success (s.storage blockTimestampLastSlot.slot) s := by
    simp only [getStorage, blockTimestampLastSlot, UniswapV2PairBase.blockTimestampLastSlot]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_sender :
      msgSender (mintLockedState s) =
        ContractResult.success s.sender (mintLockedState s) := rfl
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_self :
      contractAddress (mintLockedState s) =
        ContractResult.success (mintLockedState s).thisAddress (mintLockedState s) := rfl
  have h_balance0 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance0 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance0_balanceOf_mintLockedState_app_nf s
  have h_balance1 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance1 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance1_balanceOf_mintLockedState_app_nf s
  have h_liquidity :
      getMapping UniswapV2PairBase.balancesSlot (mintLockedState s).thisAddress
          (mintLockedState s) =
        ContractResult.success (burnLiquidity s) (mintLockedState s) := by
    simp [getMapping, burnLiquidity, pairSelf, balancesSlot,
      UniswapV2PairBase.balancesSlot, mintLockedState, mintLockedState_thisAddress]
  have h_supply :
      getStorage UniswapV2PairBase.totalSupplySlot (mintLockedState s) =
        ContractResult.success (burnSupply s) (mintLockedState s) := by
    simp [getStorage, burnSupply, totalSupplySlot, UniswapV2PairBase.totalSupplySlot,
      mintLockedState, mintLockedState_storage_totalSupply]
  have h_req_liquidity :
      Verity.require (decide (burnLiquidity s > 0) && decide (burnSupply s > 0))
        "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED" (mintLockedState s) =
          ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_liquidity_guard, if_true]
  have h_req_overflow0 :
      Verity.require
          (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance0 s)) (burnLiquidity s) ==
              observedBalance0 s)
          "UniswapV2: BURN_OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    have h_guard0_true_mul :
        (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance0 s)) (burnLiquidity s) ==
              observedBalance0 s) = true := by
      simpa [burnAmount0Product] using h_guard0_true
    simp only [Verity.require, h_guard0_true_mul, if_true]
  have h_req_overflow1 :
      Verity.require
          (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance1 s)) (burnLiquidity s) ==
              observedBalance1 s)
          "UniswapV2: BURN_OVERFLOW" (mintLockedState s) =
        ContractResult.revert "UniswapV2: BURN_OVERFLOW" (mintLockedState s) := by
    have h_guard_false_mul :
        (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance1 s)) (burnLiquidity s) ==
              observedBalance1 s) = false := by
      simpa [burnAmount1Product] using h_guard_false
    simp only [Verity.require, h_guard_false_mul, Bool.false_eq_true, if_false]
  unfold burn UniswapV2PairBase.burn Contract.run
  rw [contract_bind_success _ _ _ _ _ h_get_lock]
  rw [contract_bind_success _ _ _ _ _ h_req_lock]
  rw [contract_bind_success _ _ _ _ _ h_timestamp]
  rw [contract_bind_success _ _ _ _ _ h_previous]
  rw [contract_bind_success _ _ _ _ _ h_set_lock]
  rw [contract_bind_success _ _ _ _ _ h_sender]
  rw [contract_bind_success _ _ _ _ _ h_token0]
  rw [contract_bind_success _ _ _ _ _ h_token1]
  rw [contract_bind_success _ _ _ _ _ h_self]
  rw [contract_bind_success _ _ _ _ _ h_balance0]
  rw [contract_bind_success _ _ _ _ _ h_balance1]
  rw [contract_bind_success _ _ _ _ _ h_liquidity]
  rw [contract_bind_success _ _ _ _ _ h_supply]
  rw [contract_bind_success _ _ _ _ _ h_req_liquidity]
  rw [contract_bind_success _ _ _ _ _ h_req_overflow0]
  simp only [Bind.bind, Verity.bind, h_req_overflow1]

theorem burn_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) :
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      s.storage unlockedSlot.slot = 1 := by
  intro h_run h_success
  by_contra h_not_open
  have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
    simpa using h_not_open
  have h_revert := burn_run_revert_locked toAddr s h_locked
  rw [← h_run, h_success] at h_revert
  cases h_revert

theorem burn_success_run_implies_amount0_product_guard
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) :
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      burnLiquidity s > 0 →
        burnSupply s > 0 →
          (burnLiquidity s == 0 ||
              div (burnAmount0Product s) (burnLiquidity s) == observedBalance0 s) = true := by
  intro h_run h_success h_liquidity_pos h_supply_pos
  have h_unlocked :=
    burn_success_run_implies_lock_open toAddr s result h_run h_success
  by_contra h_not_true
  have h_guard_false :
      (burnLiquidity s == 0 ||
          div (burnAmount0Product s) (burnLiquidity s) == observedBalance0 s) = false := by
    cases h_guard :
      (burnLiquidity s == 0 ||
        div (burnAmount0Product s) (burnLiquidity s) == observedBalance0 s)
    · rfl
    · exact False.elim (h_not_true h_guard)
  have h_revert :=
    burn_run_revert_amount0_product_overflow toAddr s h_unlocked
      h_liquidity_pos h_supply_pos h_guard_false
  rw [← h_run, h_success] at h_revert
  cases h_revert

theorem burn_success_run_implies_amount1_product_guard
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) :
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      burnLiquidity s > 0 →
        burnSupply s > 0 →
          (burnLiquidity s == 0 ||
              div (burnAmount1Product s) (burnLiquidity s) == observedBalance1 s) = true := by
  intro h_run h_success h_liquidity_pos h_supply_pos
  have h_unlocked :=
    burn_success_run_implies_lock_open toAddr s result h_run h_success
  have h_guard0 :=
    burn_success_run_implies_amount0_product_guard toAddr s result
      h_run h_success h_liquidity_pos h_supply_pos
  by_contra h_not_true
  have h_guard_false :
      (burnLiquidity s == 0 ||
          div (burnAmount1Product s) (burnLiquidity s) == observedBalance1 s) = false := by
    cases h_guard :
      (burnLiquidity s == 0 ||
        div (burnAmount1Product s) (burnLiquidity s) == observedBalance1 s)
    · rfl
    · exact False.elim (h_not_true h_guard)
  have h_revert :=
    burn_run_revert_amount1_product_overflow toAddr s h_unlocked
      h_liquidity_pos h_supply_pos h_guard0 h_guard_false
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

theorem pairTokenWorldAfterEvent_eq_pairTransferOfEvent
    (pre : PairTokenBalances) (event : Event) :
  pairTokenWorldAfterEvent pre event =
    match pairTransferOfEvent event with
    | some tr => pairTokenWorldAfterPairTransfer pre tr
    | none => pre := by
  rcases event with ⟨name, args, indexedArgs⟩
  by_cases h_name : name = "UniswapV2PairTokenSafeTransfer"
  · subst name
    cases args with
    | nil =>
        simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
    | cons tokenWord args =>
        cases args with
        | nil =>
            simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
        | cons fromWord args =>
            cases args with
            | nil =>
                simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
            | cons toWord args =>
                cases args with
                | nil =>
                    simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
                | cons amount args =>
                    cases args with
                    | nil =>
                        cases indexedArgs with
                        | nil =>
                            simp [pairTokenWorldAfterEvent, pairTransferOfEvent,
                              pairTokenWorldAfterPairTransfer]
                        | cons indexed indexedArgs =>
                            simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
                    | cons extra args =>
                        simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
  · simp [pairTokenWorldAfterEvent, pairTransferOfEvent, h_name]

theorem pairTokenWorldAfterEvents_eq_pairTransfers
    (pre : PairTokenBalances) (events : List Event) :
  pairTokenWorldAfterEvents pre events =
    pairTokenWorldAfterPairTransfers pre (pairTransfersAfterEvents events) := by
  induction events generalizing pre with
  | nil =>
      rfl
  | cons event events ih =>
      rw [pairTokenWorldAfterEvents]
      rw [ih]
      rw [pairTokenWorldAfterEvent_eq_pairTransferOfEvent]
      cases h_transfer : pairTransferOfEvent event <;>
        simp [pairTransfersAfterEvents, pairTokenWorldAfterPairTransfers, h_transfer]

theorem pairTokenWorldAfterCall_eq_pairTransfers {α : Type}
    (pre : PairTokenBalances) (s : ContractState) (result : ContractResult α) :
  pairTokenWorldAfterCall pre s result =
    pairTokenWorldAfterPairTransfers pre (pairTransfersAfterCall s result) := by
  simp [pairTokenWorldAfterCall, pairTransfersAfterCall,
    pairTokenWorldAfterEvents_eq_pairTransfers]

theorem pairTransfersAfterEvents_append (l1 l2 : List Event) :
  pairTransfersAfterEvents (l1 ++ l2) =
    pairTransfersAfterEvents l1 ++ pairTransfersAfterEvents l2 := by
  simp [pairTransfersAfterEvents]

theorem pairTransfersAfterCall_bind_success {α β : Type}
    (c : Contract α) (k : α → Contract β)
    (s mid : ContractState) (a : α)
    (h : c.run s = ContractResult.success a mid)
    (h_k_success : ∃ b post, (k a).run mid = ContractResult.success b post)
    (h_mid_events :
      mid.events = s.events ++ emittedPairEventsAfterCall s (c.run s))
    (h_post_events :
      ((k a).run mid).snd.events =
        mid.events ++ emittedPairEventsAfterCall mid ((k a).run mid)) :
  pairTransfersAfterCall s ((do let x ← c; k x).run s) =
    pairTransfersAfterCall s (c.run s) ++
    pairTransfersAfterCall mid ((k a).run mid) := by
  rcases h_k_success with ⟨b, post, h_k_success⟩
  have h_bind_raw : (Bind.bind c k) s = k a mid :=
    contract_bind_success c k s mid a (Contract.eq_of_run_success h)
  have h_bind : (Bind.bind c k).run s = (k a).run mid := by
    unfold Contract.run
    rw [h_bind_raw]
    rw [Contract.eq_of_run_success h_k_success]
  have h_post_events' :
      post.events =
        mid.events ++ emittedPairEventsAfterCall mid ((k a).run mid) := by
    simpa [h_k_success] using h_post_events
  have h_bind_events :
      emittedPairEventsAfterCall s ((Bind.bind c k).run s) =
        emittedPairEventsAfterCall s (c.run s) ++
          emittedPairEventsAfterCall mid ((k a).run mid) := by
    unfold emittedPairEventsAfterCall
    rw [h_bind, h, h_k_success]
    simp only [ContractResult.snd_success]
    rw [h_post_events', h_mid_events]
    simp [List.append_assoc, List.drop_left]
  unfold pairTransfersAfterCall
  rw [h_bind_events, pairTransfersAfterEvents_append]

theorem pairSafeTransfer_pairTransfers
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
  pairTransfersAfterCall s
    ((TamaUniV2.pairSafeTransfer token toAddr amount).run s) =
    [{ token := token, fromAddr := pairSelf s, toAddr := toAddr, amount := amount }] := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, TamaUniV2.pairSafeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, TamaUniV2.pairTokenSafeTransferEvent,
    Contracts.safeTransfer, Contract.run, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, pairSelf, addressOfNat_toNat_mod_uint256]

theorem run_success_events_extend_of_append {α : Type}
    (c : Contract α) (s s' : ContractState) (a : α)
    (h_run : c.run s = ContractResult.success a s')
    (emitted : List Event) (h_events : s'.events = s.events ++ emitted) :
  s'.events = s.events ++ emittedPairEventsAfterCall s (c.run s) := by
  unfold emittedPairEventsAfterCall
  rw [h_run]
  simp only [ContractResult.snd_success]
  rw [h_events]
  congr 1
  rw [List.drop_left]

theorem pairTransfersAfterCall_of_events_eq {α : Type}
    (s t : ContractState) (result : ContractResult α)
    (h_events : t.events = s.events) :
  pairTransfersAfterCall s result = pairTransfersAfterCall t result := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, h_events]

theorem updateReservesAndEmitSync_pairTransfers
    (balance0Now balance1Now reserve0Value reserve1Value
      timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
      reserve0Value reserve1Value timestamp32 previousTimestamp).run s) = [] := by
  unfold UniswapV2PairBase.updateReservesAndEmitSync
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, getStorage, setStorage, Contract.run, ContractResult.snd,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [pairTransfersAfterEvents, pairTransferOfEvent, getStorage, setStorage,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem finishFirstMint_pairTransfers
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      root liquidity newToBalance timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.finishFirstMint toAddr sender balance0Now balance1Now
      reserve0Value reserve1Value amount0 amount1 root liquidity newToBalance
      timestamp32 previousTimestamp).run s) = [] := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, UniswapV2PairBase.finishFirstMint,
    UniswapV2PairBase.updateReservesAndEmitSync, getStorage, setStorage, setMapping,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, Contracts.emit, emitEvent, Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [pairTransfersAfterEvents, pairTransferOfEvent, getStorage, setStorage,
        setMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Contracts.emit, emitEvent, Contracts.rawLog,
        Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem firstMintPath_pairTransfers
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.firstMintPath toAddr sender balance0Now balance1Now
      reserve0Value reserve1Value amount0 amount1).run s) = [] := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, UniswapV2PairBase.firstMintPath,
    UniswapV2PairBase.finishFirstMintChecked, UniswapV2PairBase.finishFirstMint,
    UniswapV2PairBase.updateReservesAndEmitSync, getStorage, setStorage, setMapping,
    getMapping, Verity.blockTimestamp, Verity.require,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
    Contract.run, ContractResult.snd, ContractResult.fst,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.emit,
    emitEvent, Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [pairTransfersAfterEvents, pairTransferOfEvent, getStorage, setStorage,
        setMapping, getMapping, Verity.blockTimestamp, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.emit, emitEvent,
        Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem finishLaterMint_pairTransfers
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      supply liquidity timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.finishLaterMint toAddr sender balance0Now balance1Now
      reserve0Value reserve1Value amount0 amount1 supply liquidity timestamp32
      previousTimestamp).run s) = [] := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, UniswapV2PairBase.finishLaterMint,
    UniswapV2PairBase.updateReservesAndEmitSync, getStorage, setStorage, setMapping,
    getMapping, Verity.require, Verity.Stdlib.Math.requireSomeUint,
    Verity.Stdlib.Math.safeAdd, Contract.run, ContractResult.snd,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.emit, emitEvent,
    Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [pairTransfersAfterEvents, pairTransferOfEvent, getStorage, setStorage,
        setMapping, getMapping, Verity.require, Verity.Stdlib.Math.requireSomeUint,
        Verity.Stdlib.Math.safeAdd, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.emit, emitEvent,
        Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem laterMintPath_pairTransfers
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      supply : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.laterMintPath toAddr sender balance0Now balance1Now
      reserve0Value reserve1Value amount0 amount1 supply).run s) = [] := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, UniswapV2PairBase.laterMintPath,
    UniswapV2PairBase.finishLaterMint, UniswapV2PairBase.updateReservesAndEmitSync,
    getStorage, setStorage, setMapping, getMapping, Verity.blockTimestamp,
    Verity.require, Verity.Stdlib.Math.requireSomeUint,
    Verity.Stdlib.Math.safeAdd, Contract.run, ContractResult.snd,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.emit, emitEvent,
    Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [pairTransfersAfterEvents, pairTransferOfEvent, getStorage, setStorage,
        setMapping, getMapping, Verity.blockTimestamp, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, Contracts.emit, emitEvent, Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem skim_success_pairTransfers
    (toAddr : Address) (s : ContractState)
    (h_success :
      (skim toAddr).run s =
        ContractResult.success () ((skim toAddr).run s).snd) :
  pairTransfersAfterCall s ((skim toAddr).run s) =
    [{ token := pairToken0 s, fromAddr := pairSelf s,
       toAddr := toAddr, amount := skimExcess0 s },
     { token := pairToken1 s, fromAddr := pairSelf s,
       toAddr := toAddr, amount := skimExcess1 s }] := by
  have h_unlocked := skim_success_run_implies_lock_open toAddr s
    ((skim toAddr).run s) rfl h_success
  rcases skim_success_run_implies_balances_back_reserves toAddr s
      ((skim toAddr).run s) rfl h_success with ⟨h_balance0, h_balance1⟩
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_require_raw :
      (s.storage 3).val ≤ (observedBalance0 s).val ∧
      (s.storage 4).val ≤ (observedBalance1 s).val := by
    constructor
    · simpa [reserve0Slot] using h_balance0
    · simpa [reserve1Slot] using h_balance1
  have h_require_raw_unfold := h_require_raw
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_raw_unfold
  have h_require_guard_unfold := h_require_raw_unfold
  simp only [token0Slot, token1Slot, UniswapV2PairBase.token0Slot,
    UniswapV2PairBase.token1Slot] at h_require_guard_unfold
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, skim, UniswapV2PairBase.skim, unlockedSlot, token0Slot,
    token1Slot, reserve0Slot, reserve1Slot, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.pairSafeTransfer, TamaUniV2.tracePairTokenSafeTransfer,
    TamaUniV2.pairTokenSafeTransferEvent, Contracts.safeTransfer,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    skimExcess0, skimExcess1, h_unlocked_raw, h_lock_guard,
    h_require_guard_unfold, h_require_raw_unfold,
    addressOfNat_toNat_mod_uint256,
    UniswapV2PairBase.unlockedSlot, UniswapV2PairBase.token0Slot,
    UniswapV2PairBase.token1Slot, UniswapV2PairBase.reserve0Slot,
    UniswapV2PairBase.reserve1Slot]

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
    cases h_finish :
        UniswapV2PairBase.finishFirstMintChecked toAddr sender
          (observedBalance0 original) (observedBalance1 original)
          (original.storage 3) (original.storage 4)
          (mintAmount0 original) (mintAmount1 original)
          (sqrtValue (mul (mintAmount0 original) (mintAmount1 original))
            { original with «storage» := fun slotIdx =>
                if (slotIdx == 11) = true then 0 else original.storage slotIdx })
          (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else original.storage 5)
          { original with «storage» := fun slotIdx =>
              if (slotIdx == 11) = true then 0 else original.storage slotIdx } <;>
      simp only [h_finish]
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
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_bound0_uint : observedBalance0 s ≤ maxUint112 := by
    simpa [Verity.Core.Uint256.le_def] using h_bfold.1
  have h_bound1_uint : observedBalance1 s ≤ maxUint112 := by
    simpa [Verity.Core.Uint256.le_def] using h_bfold.2
  have h_bound_guard :
      (decide (observedBalance0 s ≤ maxUint112) &&
        decide (observedBalance1 s ≤ maxUint112)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_bound0_uint h_bound1_uint
  have h_bound_guard_base :
      (decide (observedBalance0 s ≤ UniswapV2PairBase.maxUint112) &&
        decide (observedBalance1 s ≤ UniswapV2PairBase.maxUint112)) = true := by
    have h0 : observedBalance0 s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound0_uint
    have h1 : observedBalance1 s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound1_uint
    simpa [Bool.and_eq_true] using And.intro h0 h1
  have h_bound_guard_raw :
      (decide
          (((Contracts.balanceOf (s.storageAddr UniswapV2PairBase.token0Slot.slot)
              s.thisAddress).run s).fst ≤ UniswapV2PairBase.maxUint112) &&
        decide
          (((Contracts.balanceOf (s.storageAddr UniswapV2PairBase.token1Slot.slot)
              s.thisAddress).run s).fst ≤ UniswapV2PairBase.maxUint112)) = true := by
    simpa only [observedBalance0, observedBalance1, pairToken0, pairToken1,
      pairSelf, TamaUniV2.erc20BalanceOf] using h_bound_guard_base
  have h_reserve_fold :
      (s.storage 3).val ≤ (observedBalance0 s).val ∧
        (s.storage 4).val ≤ (observedBalance1 s).val := by
    refine ⟨?_, ?_⟩
    · simpa [reserve0Slot, Verity.Core.Uint256.le_def] using h_reserve0
    · simpa [reserve1Slot, Verity.Core.Uint256.le_def] using h_reserve1
  have h_reserve_guard :
      (decide (s.storage reserve0Slot.slot ≤ observedBalance0 s) &&
        decide (s.storage reserve1Slot.slot ≤ observedBalance1 s)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_reserve0 h_reserve1
  have h_amount_fold :
      0 < (mintAmount0 s).val ∧ 0 < (mintAmount1 s).val := by
    exact ⟨by simpa [Verity.Core.Uint256.lt_def] using h_amount0,
      by simpa [Verity.Core.Uint256.lt_def] using h_amount1⟩
  have h_amount_guard :
      (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_amount0 h_amount1
  have h_supply_guard :
      (s.storage UniswapV2PairBase.totalSupplySlot.slot == (0 : Uint256)) = true := by
    simp [UniswapV2PairBase.totalSupplySlot, h_supply_zero_raw]
  have h_root_fold : minimumLiquidity.val < (mintFirstRoot s).val := by
    simpa [Verity.Core.Uint256.lt_def] using h_root
  have h_bfold_raw := h_bfold
  have h_reserve_fold_raw := h_reserve_fold
  have h_amount_fold_raw := h_amount_fold
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    mintAmount0, mintAmount1, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
    Contract.run, ContractResult.fst, Verity.pure, Pure.pure] at h_bfold_raw
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    mintAmount0, mintAmount1, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
    Contract.run, ContractResult.fst, Verity.pure, Pure.pure] at h_reserve_fold_raw
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    mintAmount0, mintAmount1, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
    Contract.run, ContractResult.fst, Verity.pure, Pure.pure] at h_amount_fold_raw
  let pathResult :=
    UniswapV2PairBase.firstMintPath toAddr s.sender
      (observedBalance0 s) (observedBalance1 s)
      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
      (mintAmount0 s) (mintAmount1 s) (mintLockedState s)
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_sender :
      msgSender (mintLockedState s) =
        ContractResult.success s.sender (mintLockedState s) := rfl
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_self :
      contractAddress (mintLockedState s) =
        ContractResult.success (mintLockedState s).thisAddress (mintLockedState s) := rfl
  have h_balance0 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance0 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance0_balanceOf_mintLockedState_app_nf s
  have h_balance1 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance1 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance1_balanceOf_mintLockedState_app_nf s
  have h_req_bound :
      Verity.require
          (decide (observedBalance0 s ≤ UniswapV2PairBase.maxUint112) &&
            decide (observedBalance1 s ≤ UniswapV2PairBase.maxUint112))
          "UniswapV2: OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_bound_guard_base, if_true]
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  have h_req_reserve :
      Verity.require
          (decide (observedBalance0 s ≥ s.storage reserve0Slot.slot) &&
            decide (observedBalance1 s ≥ s.storage reserve1Slot.slot))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simpa only [ge_iff_le] using (by
      simp only [Verity.require, h_reserve_guard, if_true])
  have h_req_amount :
      Verity.require
          (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_amount_guard, if_true]
  have h_get_supply :
      getStorage UniswapV2PairBase.totalSupplySlot (mintLockedState s) =
        ContractResult.success (s.storage totalSupplySlot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_totalSupply]
  have h_mint_prefix :
      (mint toAddr).run s = Contract.run (fun _ => pathResult) s := by
    unfold mint UniswapV2PairBase.mint Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_sender]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_self]
    rw [contract_bind_success _ _ _ _ _ h_balance0]
    rw [contract_bind_success _ _ _ _ _ h_balance1]
    rw [contract_bind_success _ _ _ _ _ h_req_bound]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_req_reserve]
    rw [mintAmount0_observed_nf, mintAmount1_observed_nf]
    rw [contract_bind_success _ _ _ _ _ h_req_amount]
    rw [contract_bind_success _ _ _ _ _ h_get_supply]
    simp only [h_supply_guard, if_true]
    dsimp only [pathResult, Bind.bind, Verity.bind, Pure.pure, Verity.pure]
    generalize
      (UniswapV2PairBase.firstMintPath toAddr s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s) (mintLockedState s)) = d
    cases d <;> rfl
  cases h_path : pathResult with
  | success liquidity post =>
      have h_path_success :
          pathResult = ContractResult.success (mintFirstLiquidity s) pathResult.snd := by
        have h_success_path := h_success
        rw [h_mint_prefix, h_path] at h_success_path
        simp only [ContractResult.snd] at h_success_path
        cases h_success_path
        rw [h_path]
        simp only [ContractResult.snd]
      have h_path_run :
          pathResult =
            (UniswapV2PairBase.firstMintPath toAddr s.sender
              (observedBalance0 s) (observedBalance1 s)
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s) := by
        have h_path_raw := h_path
        dsimp only [pathResult] at h_path_raw
        dsimp only [Contract.run]
        rw [h_path_raw]
        rw [h_path]
      have h_path_storage :
          pairConcreteStorageMatchesWorld pathResult.snd
            (pairWorldAfterFirstMintRun s) :=
        firstMintPath_run_storage_matches_world toAddr s.sender s
          pathResult h_path_run h_path_success h_product h_root
      have h_public_post :
          ((mint toAddr).run s).snd = pathResult.snd := by
        rw [h_mint_prefix, h_path]
        simp only [Contract.run, ContractResult.snd]
      rw [h_public_post]
      exact h_path_storage
  | «revert» msg post =>
      have h_impossible : False := by
        rw [h_mint_prefix, h_path] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
      cases h_impossible

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

theorem finishLaterMint_success_run_storage_matches_world
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      supply liquidity timestamp32 previousTimestamp : Uint256)
    (original s : ContractState) (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.finishLaterMint toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
        supply liquidity timestamp32 previousTimestamp).run s →
    result = ContractResult.success liquidity result.snd →
      balance0Now = observedBalance0 original →
        balance1Now = observedBalance1 original →
          supply = original.storage totalSupplySlot.slot →
            0 < supply.val →
              pairConcreteStorageMatchesWorld result.snd
                (pairWorldAfterSubsequentMintRun liquidity original) := by
  intro h_run h_success h_b0 h_b1 h_supply h_supply_pos
  subst h_run
  subst h_b0
  subst h_b1
  subst h_supply
  by_cases h_supply_over :
      (original.storage totalSupplySlot.slot).val + liquidity.val >
        Verity.Stdlib.Math.MAX_UINT256
  · have h_supply_over_raw :
        Verity.Stdlib.Math.MAX_UINT256 < (original.storage 8).val + liquidity.val := by
      simpa [gt_iff_lt, totalSupplySlot] using h_supply_over
    simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Verity.require, gt_iff_lt, Verity.Stdlib.Math.safeAdd,
      Verity.Stdlib.Math.requireSomeUint, h_supply_over_raw] at h_success
  · have h_supply_ok :
        (original.storage totalSupplySlot.slot).val + liquidity.val ≤
          Verity.Stdlib.Math.MAX_UINT256 := by omega
    have h_supply_not_raw :
        ¬ Verity.Stdlib.Math.MAX_UINT256 < (original.storage 8).val + liquidity.val := by
      simpa [gt_iff_lt, totalSupplySlot] using h_supply_over
    have h_safe_supply :
        Verity.Stdlib.Math.safeAdd (original.storage totalSupplySlot.slot) liquidity =
          some (original.storage totalSupplySlot.slot + liquidity) :=
      Verity.Proofs.Stdlib.Automation.safeAdd_some_val
        (original.storage totalSupplySlot.slot) liquidity h_supply_ok
    by_cases h_balance_over :
        (s.storageMap balancesSlot.slot toAddr).val + liquidity.val >
          Verity.Stdlib.Math.MAX_UINT256
    · have h_balance_over_raw :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + liquidity.val := by
        simpa [gt_iff_lt, balancesSlot] using h_balance_over
      simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
        Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Verity.require, gt_iff_lt, Verity.Stdlib.Math.safeAdd,
        Verity.Stdlib.Math.requireSomeUint, h_supply_not_raw, h_balance_over_raw] at h_success
    · have h_balance_ok :
          (s.storageMap balancesSlot.slot toAddr).val + liquidity.val ≤
            Verity.Stdlib.Math.MAX_UINT256 := by omega
      have h_balance_not_raw :
          ¬ Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + liquidity.val := by
        simpa [gt_iff_lt, balancesSlot] using h_balance_over
      have h_safe_balance :
          Verity.Stdlib.Math.safeAdd (s.storageMap balancesSlot.slot toAddr) liquidity =
            some (s.storageMap balancesSlot.slot toAddr + liquidity) :=
        Verity.Proofs.Stdlib.Automation.safeAdd_some_val
          (s.storageMap balancesSlot.slot toAddr) liquidity h_balance_ok
      have h_add_val :
          (original.storage totalSupplySlot.slot + liquidity).val =
            (original.storage totalSupplySlot.slot).val + liquidity.val := by
        have h_lt :
            (original.storage totalSupplySlot.slot).val + liquidity.val <
              Core.Uint256.modulus := by
          rw [← Core.Uint256.max_uint256_succ_eq_modulus]
          exact Nat.lt_succ_of_le h_supply_ok
        simpa using
          (Core.Uint256.add_eq_of_lt
            (a := original.storage totalSupplySlot.slot) (b := liquidity) h_lt)
      have h_add_val_comm :
          (liquidity + original.storage totalSupplySlot.slot).val =
            (original.storage totalSupplySlot.slot).val + liquidity.val := by
        have h_lt :
            liquidity.val + (original.storage totalSupplySlot.slot).val <
              Core.Uint256.modulus := by
          rw [Nat.add_comm]
          rw [← Core.Uint256.max_uint256_succ_eq_modulus]
          exact Nat.lt_succ_of_le h_supply_ok
        have h_val :=
          (Core.Uint256.add_eq_of_lt
            (a := liquidity) (b := original.storage totalSupplySlot.slot) h_lt)
        simpa [Nat.add_comm] using h_val
      have h_nonzero :
          ¬ (original.storage totalSupplySlot.slot).val = 0 := Nat.ne_of_gt h_supply_pos
      have h_nonzero_raw :
          ¬ (original.storage 8).val = 0 := by
        simpa [totalSupplySlot] using h_nonzero
      have h_add_nonzero :
          ¬ (original.storage totalSupplySlot.slot).val + liquidity.val = 0 := by
        omega
      have h_add_val_comm_raw :
          (liquidity + original.storage 8).val =
            (original.storage 8).val + liquidity.val := by
        simpa [totalSupplySlot] using h_add_val_comm
      simp [UniswapV2PairBase.finishLaterMint,
        UniswapV2PairBase.updateReservesAndEmitSync, pairConcreteStorageMatchesWorld,
        pairWorldAfterSubsequentMintRun, pairWorldLockedLiquidity, getStorage, getMapping,
        setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
        Contracts.rawLog, Contracts.mstore, Verity.Stdlib.Math.safeAdd,
        Verity.Stdlib.Math.requireSomeUint, gt_iff_lt, h_supply_not_raw, h_balance_not_raw,
        h_add_val, h_add_val_comm, h_add_val_comm_raw, h_nonzero,
        h_nonzero_raw, h_add_nonzero]
      all_goals (split_ifs <;> simp [getStorage, setStorage, setMapping, getMapping,
        Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, emitEvent, Contracts.emit, Contracts.rawLog,
        Contracts.mstore, pairWorldLockedLiquidity, gt_iff_lt, h_supply_not_raw,
        h_balance_not_raw, h_add_val, h_add_val_comm, h_add_val_comm_raw,
        h_nonzero, h_nonzero_raw, h_add_nonzero] <;> contradiction)

theorem finishLaterMint_success_value_eq
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      supply liquidity timestamp32 previousTimestamp minted : Uint256)
    (s : ContractState) (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.finishLaterMint toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
        supply liquidity timestamp32 previousTimestamp).run s →
    result = ContractResult.success minted result.snd →
      minted = liquidity := by
  intro h_run h_success
  subst h_run
  by_cases h_supply_over : Verity.Stdlib.Math.MAX_UINT256 < supply.val + liquidity.val
  · simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
      setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
      Contracts.rawLog, Contracts.mstore, Verity.Stdlib.Math.safeAdd,
      Verity.Stdlib.Math.requireSomeUint, h_supply_over] at h_success
    have h_tag := congrArg
      (fun r : ContractResult Uint256 =>
        match r with
        | ContractResult.success _ _ => true
        | ContractResult.revert _ _ => false) h_success
    simp at h_tag
    cases h_tag
  · by_cases h_balance_over :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + liquidity.val
    · simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
        setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
        Contracts.rawLog, Contracts.mstore, Verity.Stdlib.Math.safeAdd,
        Verity.Stdlib.Math.requireSomeUint, h_supply_over, h_balance_over] at h_success
      have h_tag := congrArg
        (fun r : ContractResult Uint256 =>
          match r with
          | ContractResult.success _ _ => true
          | ContractResult.revert _ _ => false) h_success
      simp at h_tag
      cases h_tag
    · simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
        setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
        Contracts.rawLog, Contracts.mstore, Verity.Stdlib.Math.safeAdd,
        Verity.Stdlib.Math.requireSomeUint, h_supply_over, h_balance_over] at h_success
      cases h_update :
          UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
            reserve0Value reserve1Value timestamp32 previousTimestamp
            { «storage» := fun slotIdx =>
                if slotIdx = 8 then supply + liquidity else s.storage slotIdx
              transientStorage := s.transientStorage
              storageAddr := s.storageAddr
              storageMap := fun slotIdx addr =>
                if slotIdx = 9 ∧ addr = toAddr
                  then liquidity + s.storageMap 9 toAddr
                  else s.storageMap slotIdx addr
              storageMapUint := s.storageMapUint
              storageMap2 := s.storageMap2
              storageArray := s.storageArray
              sender := s.sender
              thisAddress := s.thisAddress
              msgValue := s.msgValue
              selfBalance := s.selfBalance
              blockTimestamp := s.blockTimestamp
              blockNumber := s.blockNumber
              chainId := s.chainId
              blobBaseFee := s.blobBaseFee
              calldataSize := s.calldataSize
              calldata := s.calldata
              memory := s.memory
              knownAddresses := fun slotIdx =>
                if slotIdx = 9
                  then Core.FiniteAddressSet.insert toAddr (s.knownAddresses slotIdx)
                  else s.knownAddresses slotIdx
              events :=
                s.events ++
                  [{ name := "Transfer"
                     args :=
                       [Core.Uint256.ofNat (Core.Address.toNat 0),
                        Core.Uint256.ofNat (Core.Address.toNat toAddr), liquidity]
                     indexedArgs := [] }] } with
      | success a post =>
          simp [h_update, ContractResult.snd] at h_success
          exact h_success.symm
      | «revert» msg post =>
          simp [h_update, ContractResult.snd] at h_success

theorem laterMintPath_run_storage_matches_world
    (toAddr sender : Address) (original : ContractState)
    (liquidity : Uint256) (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.laterMintPath toAddr sender
        (observedBalance0 original) (observedBalance1 original)
        (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
        (mintAmount0 original) (mintAmount1 original)
        (original.storage totalSupplySlot.slot)).run
        (mintLockedState original) →
    result = ContractResult.success liquidity result.snd →
      0 < (original.storage totalSupplySlot.slot).val →
        original.storage reserve0Slot.slot > 0 →
          original.storage reserve1Slot.slot > 0 →
            mintAmount0 original > 0 →
              mintAmount1 original > 0 →
                liquidity > 0 →
                  pairConcreteStorageMatchesWorld result.snd
                    (pairWorldAfterSubsequentMintRun liquidity original) := by
  intro h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_amount0 h_amount1 h_liquidity
  subst h_run
  let computedLiquidity :=
    Contracts.min
      (div (mul (mintAmount0 original) (original.storage totalSupplySlot.slot))
        (original.storage reserve0Slot.slot))
      (div (mul (mintAmount1 original) (original.storage totalSupplySlot.slot))
        (original.storage reserve1Slot.slot))
  have h_reserve_guard :
      (original.storage reserve0Slot.slot > 0 &&
        original.storage reserve1Slot.slot > 0) = true := by
    simp only [Bool.and_eq_true]
    exact ⟨by simpa only [decide_eq_true_eq] using h_reserve0_pos,
      by simpa only [decide_eq_true_eq] using h_reserve1_pos⟩
  have h_reserve_guard_raw :
      (original.storage 3 > 0 && original.storage 4 > 0) = true := by
    simpa [reserve0Slot, reserve1Slot] using h_reserve_guard
  have h_amount0_over :
      (mintAmount0 original == 0 ||
        div (mul (mintAmount0 original) (original.storage totalSupplySlot.slot))
          (mintAmount0 original) == original.storage totalSupplySlot.slot) = true := by
    by_contra h_not
    have h_false :
        (mintAmount0 original == 0 ||
          div (mul (mintAmount0 original) (original.storage totalSupplySlot.slot))
            (mintAmount0 original) == original.storage totalSupplySlot.slot) = false :=
      Bool.eq_false_of_not_eq_true h_not
    simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_reserve_guard, h_false, if_true, if_false,
      ContractResult.snd] at h_success
    cases h_success
  have h_amount1_over :
      (mintAmount1 original == 0 ||
        div (mul (mintAmount1 original) (original.storage totalSupplySlot.slot))
          (mintAmount1 original) == original.storage totalSupplySlot.slot) = true := by
    by_contra h_not
    have h_false :
        (mintAmount1 original == 0 ||
          div (mul (mintAmount1 original) (original.storage totalSupplySlot.slot))
            (mintAmount1 original) == original.storage totalSupplySlot.slot) = false :=
      Bool.eq_false_of_not_eq_true h_not
    simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_reserve_guard, h_amount0_over, h_false, if_true, if_false,
      ContractResult.snd] at h_success
    cases h_success
  have h_amount0_over_raw :
      (mintAmount0 original == 0 ||
        div (mul (mintAmount0 original) (original.storage 8))
          (mintAmount0 original) == original.storage 8) = true := by
    simpa [totalSupplySlot] using h_amount0_over
  have h_amount1_over_raw :
      (mintAmount1 original == 0 ||
        div (mul (mintAmount1 original) (original.storage 8))
          (mintAmount1 original) == original.storage 8) = true := by
    simpa [totalSupplySlot] using h_amount1_over
  have h_computed_guard : decide (computedLiquidity > 0) = true := by
    by_contra h_not
    have h_false : decide (computedLiquidity > 0) = false :=
      Bool.eq_false_of_not_eq_true h_not
    simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_reserve_guard, h_amount0_over, h_amount1_over,
      if_true, computedLiquidity, h_false, if_false, ContractResult.snd] at h_success
    cases h_success
  have h_computed_guard_raw :
      decide
          (Contracts.min
            (div (mul (mintAmount0 original) (original.storage totalSupplySlot.slot))
              (original.storage reserve0Slot.slot))
            (div (mul (mintAmount1 original) (original.storage totalSupplySlot.slot))
              (original.storage reserve1Slot.slot)) > 0) = true := by
    simpa [computedLiquidity] using h_computed_guard
  have h_computed_eq_raw :
      computedLiquidity =
        Contracts.min
          (div (mul (mintAmount0 original) (original.storage 8))
            (original.storage 3))
          (div (mul (mintAmount1 original) (original.storage 8))
            (original.storage 4)) := by
    simpa [computedLiquidity, totalSupplySlot, reserve0Slot, reserve1Slot]
  let checked :=
    (UniswapV2PairBase.finishLaterMint toAddr sender
      (observedBalance0 original) (observedBalance1 original)
      (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
      (mintAmount0 original) (mintAmount1 original)
      (original.storage totalSupplySlot.slot) computedLiquidity
      (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
      (if (5 == 11) = true then 0 else original.storage 5)).run
      (mintLockedState original)
  let pathResult :=
    (UniswapV2PairBase.laterMintPath toAddr sender
      (observedBalance0 original) (observedBalance1 original)
      (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
      (mintAmount0 original) (mintAmount1 original)
      (original.storage totalSupplySlot.slot)).run
      (mintLockedState original)
  have h_path_reduced : pathResult = checked := by
    dsimp only [pathResult]
    simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right]
    simp only [Contract.run, Verity.bind, Bind.bind]
    simp only [Verity.require, h_reserve_guard, h_amount0_over, h_amount1_over,
      if_true]
    simp only [Verity.require, h_computed_guard_raw, if_true]
    simp only [Verity.blockTimestamp, getStorage]
    simp only [Verity.pure, Pure.pure, ContractResult.fst, ContractResult.snd]
    simp only [checked, Contract.run, mintLockedState, timestamp32,
      reserve0Slot, reserve1Slot, totalSupplySlot, blockTimestampLastSlot,
      unlockedSlot, UniswapV2PairBase.reserve0Slot,
      UniswapV2PairBase.reserve1Slot, UniswapV2PairBase.totalSupplySlot,
      UniswapV2PairBase.blockTimestampLastSlot,
      UniswapV2PairBase.unlockedSlot]
    rw [h_computed_eq_raw]
    cases h_finish :
        UniswapV2PairBase.finishLaterMint toAddr sender
          (observedBalance0 original) (observedBalance1 original)
          (original.storage 3) (original.storage 4)
          (mintAmount0 original) (mintAmount1 original)
          (original.storage 8)
          (Contracts.min
            (div (mul (mintAmount0 original) (original.storage 8))
              (original.storage 3))
            (div (mul (mintAmount1 original) (original.storage 8))
              (original.storage 4)))
          (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else original.storage 5)
          { original with «storage» := fun slotIdx =>
              if (slotIdx == 11) = true then 0 else original.storage slotIdx } <;>
      simp only [h_finish]
  cases h_checked_case : checked with
  | success minted post =>
      have h_minted : minted = liquidity := by
        change pathResult = ContractResult.success liquidity pathResult.snd at h_success
        rw [h_path_reduced, h_checked_case] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
        rfl
      have h_minted_computed : minted = computedLiquidity := by
        exact finishLaterMint_success_value_eq toAddr sender
          (observedBalance0 original) (observedBalance1 original)
          (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
          (mintAmount0 original) (mintAmount1 original)
          (original.storage totalSupplySlot.slot) computedLiquidity
          (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else original.storage 5)
          minted (mintLockedState original) checked rfl
          (by simp [h_checked_case])
      have h_liquidity_eq : liquidity = computedLiquidity := by
        rw [← h_minted, h_minted_computed]
      subst minted
      subst liquidity
      have h_checked_success :
          checked = ContractResult.success computedLiquidity checked.snd := by
        simp [h_checked_case]
      have h_checked_storage :
          pairConcreteStorageMatchesWorld checked.snd
            (pairWorldAfterSubsequentMintRun computedLiquidity original) := by
        exact finishLaterMint_success_run_storage_matches_world toAddr sender
          (observedBalance0 original) (observedBalance1 original)
          (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
          (mintAmount0 original) (mintAmount1 original)
          (original.storage totalSupplySlot.slot) computedLiquidity
          (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else original.storage 5)
          original (mintLockedState original) checked
          rfl h_checked_success rfl rfl rfl h_supply_pos
      change pairConcreteStorageMatchesWorld pathResult.snd
        (pairWorldAfterSubsequentMintRun computedLiquidity original)
      rw [h_path_reduced, h_checked_case]
      have h_checked_storage_post :
          pairConcreteStorageMatchesWorld post
            (pairWorldAfterSubsequentMintRun computedLiquidity original) := by
        simpa only [h_checked_case, ContractResult.snd] using h_checked_storage
      simpa only [ContractResult.snd] using h_checked_storage_post
  | «revert» reason post =>
      have h_impossible : False := by
        change pathResult = ContractResult.success liquidity pathResult.snd at h_success
        rw [h_path_reduced, h_checked_case] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
      cases h_impossible

theorem mint_subsequent_success_run_storage_matches_world
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  (mint toAddr).run s =
      ContractResult.success liquidity ((mint toAddr).run s).snd →
    0 < (s.storage totalSupplySlot.slot).val →
      s.storage reserve0Slot.slot > 0 →
        s.storage reserve1Slot.slot > 0 →
          s.storage reserve0Slot.slot ≤ observedBalance0 s →
            s.storage reserve1Slot.slot ≤ observedBalance1 s →
              mintAmount0 s > 0 →
                mintAmount1 s > 0 →
                  liquidity > 0 →
                    pairConcreteStorageMatchesWorld
                      ((mint toAddr).run s).snd
                      (pairWorldAfterSubsequentMintRun liquidity s) := by
  intro h_success h_supply_pos h_reserve0_pos h_reserve1_pos h_reserve0 h_reserve1
    h_amount0 h_amount1 h_liquidity
  have h_success_exists :
      ∃ liquidity',
        (mint toAddr).run s =
          ContractResult.success liquidity' ((mint toAddr).run s).snd := by
    exact ⟨liquidity, h_success⟩
  have h_unlocked :=
    mint_success_run_implies_lock_open toAddr s
      ((mint toAddr).run s) rfl h_success_exists
  rcases mint_success_run_implies_balances_fit_uint112 toAddr s
      ((mint toAddr).run s) rfl h_success_exists with
    ⟨h_bound0, h_bound1⟩
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_supply_ne :
      s.storage totalSupplySlot.slot ≠ (0 : Uint256) := by
    intro h_zero
    have h_zero_val : (s.storage totalSupplySlot.slot).val = 0 := by
      rw [h_zero]
      rfl
    omega
  have h_bfold :
      (observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val := by
    rw [Verity.Core.Uint256.le_def] at h_bound0 h_bound1
    exact ⟨h_bound0, h_bound1⟩
  have h_bound0_uint : observedBalance0 s ≤ maxUint112 := by
    simpa [Verity.Core.Uint256.le_def] using h_bfold.1
  have h_bound1_uint : observedBalance1 s ≤ maxUint112 := by
    simpa [Verity.Core.Uint256.le_def] using h_bfold.2
  have h_bound_guard_base :
      (decide (observedBalance0 s ≤ UniswapV2PairBase.maxUint112) &&
        decide (observedBalance1 s ≤ UniswapV2PairBase.maxUint112)) = true := by
    have h0 : observedBalance0 s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound0_uint
    have h1 : observedBalance1 s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound1_uint
    simpa [Bool.and_eq_true] using And.intro h0 h1
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_reserve_guard :
      (decide (s.storage reserve0Slot.slot ≤ observedBalance0 s) &&
        decide (s.storage reserve1Slot.slot ≤ observedBalance1 s)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_reserve0 h_reserve1
  have h_amount_guard :
      (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_amount0 h_amount1
  have h_supply_guard :
      (s.storage UniswapV2PairBase.totalSupplySlot.slot == (0 : Uint256)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_eq_true
    apply h_supply_ne
    simpa [UniswapV2PairBase.totalSupplySlot] using h_eq_true
  let pathResult :=
    UniswapV2PairBase.laterMintPath toAddr s.sender
      (observedBalance0 s) (observedBalance1 s)
      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
      (mintAmount0 s) (mintAmount1 s) (s.storage totalSupplySlot.slot) (mintLockedState s)
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_sender :
      msgSender (mintLockedState s) =
        ContractResult.success s.sender (mintLockedState s) := rfl
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_self :
      contractAddress (mintLockedState s) =
        ContractResult.success (mintLockedState s).thisAddress (mintLockedState s) := rfl
  have h_balance0 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance0 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance0_balanceOf_mintLockedState_app_nf s
  have h_balance1 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance1 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance1_balanceOf_mintLockedState_app_nf s
  have h_req_bound :
      Verity.require
          (decide (observedBalance0 s ≤ UniswapV2PairBase.maxUint112) &&
            decide (observedBalance1 s ≤ UniswapV2PairBase.maxUint112))
          "UniswapV2: OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_bound_guard_base, if_true]
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  have h_req_reserve :
      Verity.require
          (decide (observedBalance0 s ≥ s.storage reserve0Slot.slot) &&
            decide (observedBalance1 s ≥ s.storage reserve1Slot.slot))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simpa only [ge_iff_le] using (by
      simp only [Verity.require, h_reserve_guard, if_true])
  have h_req_amount :
      Verity.require
          (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_amount_guard, if_true]
  have h_get_supply :
      getStorage UniswapV2PairBase.totalSupplySlot (mintLockedState s) =
        ContractResult.success (s.storage totalSupplySlot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_totalSupply]
  have h_mint_prefix :
      (mint toAddr).run s = Contract.run (fun _ => pathResult) s := by
    unfold mint UniswapV2PairBase.mint Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_sender]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_self]
    rw [contract_bind_success _ _ _ _ _ h_balance0]
    rw [contract_bind_success _ _ _ _ _ h_balance1]
    rw [contract_bind_success _ _ _ _ _ h_req_bound]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_req_reserve]
    rw [mintAmount0_observed_nf, mintAmount1_observed_nf]
    rw [contract_bind_success _ _ _ _ _ h_req_amount]
    rw [contract_bind_success _ _ _ _ _ h_get_supply]
    simp only [h_supply_guard, Bool.false_eq_true, if_false]
    dsimp only [pathResult, Bind.bind, Verity.bind, Pure.pure, Verity.pure]
    generalize
      (UniswapV2PairBase.laterMintPath toAddr s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s) (s.storage totalSupplySlot.slot)
        (mintLockedState s)) = d
    cases d <;> rfl
  cases h_path : pathResult with
  | success minted post =>
      have h_path_success :
          pathResult = ContractResult.success liquidity pathResult.snd := by
        have h_success_path := h_success
        rw [h_mint_prefix, h_path] at h_success_path
        simp only [ContractResult.snd] at h_success_path
        cases h_success_path
        rw [h_path]
        simp only [ContractResult.snd]
      have h_path_run :
          pathResult =
            (UniswapV2PairBase.laterMintPath toAddr s.sender
              (observedBalance0 s) (observedBalance1 s)
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              (mintAmount0 s) (mintAmount1 s)
              (s.storage totalSupplySlot.slot)).run (mintLockedState s) := by
        have h_path_raw := h_path
        dsimp only [pathResult] at h_path_raw
        dsimp only [Contract.run]
        rw [h_path_raw]
        rw [h_path]
      have h_path_storage :
          pairConcreteStorageMatchesWorld pathResult.snd
            (pairWorldAfterSubsequentMintRun liquidity s) :=
        laterMintPath_run_storage_matches_world toAddr s.sender s
          liquidity pathResult h_path_run h_path_success h_supply_pos
          h_reserve0_pos h_reserve1_pos h_amount0 h_amount1 h_liquidity
      have h_public_post :
          ((mint toAddr).run s).snd = pathResult.snd := by
        rw [h_mint_prefix, h_path]
        simp only [Contract.run, ContractResult.snd]
      rw [h_public_post]
      exact h_path_storage
  | «revert» msg post =>
      have h_impossible : False := by
        rw [h_mint_prefix, h_path] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
      cases h_impossible

theorem mint_first_run_eq_path
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
                  (mint toAddr).run s =
                    (UniswapV2PairBase.firstMintPath toAddr s.sender
                      (observedBalance0 s) (observedBalance1 s)
                      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
                      (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s) := by
  intro h_success h_supply_zero h_reserve0 h_reserve1 h_amount0 h_amount1
    _h_product _h_root
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
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_bound0_uint : observedBalance0 s ≤ maxUint112 := by
    simpa [Verity.Core.Uint256.le_def] using h_bfold.1
  have h_bound1_uint : observedBalance1 s ≤ maxUint112 := by
    simpa [Verity.Core.Uint256.le_def] using h_bfold.2
  have h_bound_guard_base :
      (decide (observedBalance0 s ≤ UniswapV2PairBase.maxUint112) &&
        decide (observedBalance1 s ≤ UniswapV2PairBase.maxUint112)) = true := by
    have h0 : observedBalance0 s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound0_uint
    have h1 : observedBalance1 s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound1_uint
    simpa [Bool.and_eq_true] using And.intro h0 h1
  have h_reserve_guard :
      (decide (s.storage reserve0Slot.slot ≤ observedBalance0 s) &&
        decide (s.storage reserve1Slot.slot ≤ observedBalance1 s)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_reserve0 h_reserve1
  have h_amount_guard :
      (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_amount0 h_amount1
  have h_supply_guard :
      (s.storage UniswapV2PairBase.totalSupplySlot.slot == (0 : Uint256)) = true := by
    simp [UniswapV2PairBase.totalSupplySlot, h_supply_zero_raw]
  let pathResult :=
    UniswapV2PairBase.firstMintPath toAddr s.sender
      (observedBalance0 s) (observedBalance1 s)
      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
      (mintAmount0 s) (mintAmount1 s) (mintLockedState s)
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_sender :
      msgSender (mintLockedState s) =
        ContractResult.success s.sender (mintLockedState s) := rfl
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_self :
      contractAddress (mintLockedState s) =
        ContractResult.success (mintLockedState s).thisAddress (mintLockedState s) := rfl
  have h_balance0 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance0 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance0_balanceOf_mintLockedState_app_nf s
  have h_balance1 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance1 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance1_balanceOf_mintLockedState_app_nf s
  have h_req_bound :
      Verity.require
          (decide (observedBalance0 s ≤ UniswapV2PairBase.maxUint112) &&
            decide (observedBalance1 s ≤ UniswapV2PairBase.maxUint112))
          "UniswapV2: OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_bound_guard_base, if_true]
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  have h_req_reserve :
      Verity.require
          (decide (observedBalance0 s ≥ s.storage reserve0Slot.slot) &&
            decide (observedBalance1 s ≥ s.storage reserve1Slot.slot))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simpa only [ge_iff_le] using (by
      simp only [Verity.require, h_reserve_guard, if_true])
  have h_req_amount :
      Verity.require
          (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_amount_guard, if_true]
  have h_get_supply :
      getStorage UniswapV2PairBase.totalSupplySlot (mintLockedState s) =
        ContractResult.success (s.storage totalSupplySlot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_totalSupply]
  have h_mint_prefix :
      (mint toAddr).run s = Contract.run (fun _ => pathResult) s := by
    unfold mint UniswapV2PairBase.mint Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_sender]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_self]
    rw [contract_bind_success _ _ _ _ _ h_balance0]
    rw [contract_bind_success _ _ _ _ _ h_balance1]
    rw [contract_bind_success _ _ _ _ _ h_req_bound]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_req_reserve]
    rw [mintAmount0_observed_nf, mintAmount1_observed_nf]
    rw [contract_bind_success _ _ _ _ _ h_req_amount]
    rw [contract_bind_success _ _ _ _ _ h_get_supply]
    simp only [h_supply_guard, if_true]
    dsimp only [pathResult, Bind.bind, Verity.bind, Pure.pure, Verity.pure]
    generalize
      (UniswapV2PairBase.firstMintPath toAddr s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s) (mintLockedState s)) = d
    cases d <;> rfl
  cases h_path : pathResult with
  | success liquidity post =>
      rw [h_mint_prefix]
      simp only [Contract.run, h_path]
      have h_path_raw :
          UniswapV2PairBase.firstMintPath toAddr s.sender
            (observedBalance0 s) (observedBalance1 s)
            (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
            (mintAmount0 s) (mintAmount1 s) (mintLockedState s) =
            ContractResult.success liquidity post := by
        simpa only [pathResult] using h_path
      rw [h_path_raw]
  | «revert» msg post =>
      have h_impossible : False := by
        rw [h_mint_prefix, h_path] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
      cases h_impossible

theorem mint_later_run_eq_path
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  (mint toAddr).run s =
      ContractResult.success liquidity ((mint toAddr).run s).snd →
    0 < (s.storage totalSupplySlot.slot).val →
      s.storage reserve0Slot.slot > 0 →
        s.storage reserve1Slot.slot > 0 →
          s.storage reserve0Slot.slot ≤ observedBalance0 s →
            s.storage reserve1Slot.slot ≤ observedBalance1 s →
              mintAmount0 s > 0 →
                mintAmount1 s > 0 →
                  liquidity > 0 →
                    (mint toAddr).run s =
                      (UniswapV2PairBase.laterMintPath toAddr s.sender
                        (observedBalance0 s) (observedBalance1 s)
                        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
                        (mintAmount0 s) (mintAmount1 s)
                        (s.storage totalSupplySlot.slot)).run (mintLockedState s) := by
  intro h_success h_supply_pos _h_reserve0_pos _h_reserve1_pos h_reserve0 h_reserve1
    h_amount0 h_amount1 _h_liquidity
  have h_success_exists :
      ∃ liquidity',
        (mint toAddr).run s =
          ContractResult.success liquidity' ((mint toAddr).run s).snd := by
    exact ⟨liquidity, h_success⟩
  have h_unlocked :=
    mint_success_run_implies_lock_open toAddr s
      ((mint toAddr).run s) rfl h_success_exists
  rcases mint_success_run_implies_balances_fit_uint112 toAddr s
      ((mint toAddr).run s) rfl h_success_exists with
    ⟨h_bound0, h_bound1⟩
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_supply_ne :
      s.storage totalSupplySlot.slot ≠ (0 : Uint256) := by
    intro h_zero
    have h_zero_val : (s.storage totalSupplySlot.slot).val = 0 := by
      rw [h_zero]
      rfl
    omega
  have h_bfold :
      (observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val := by
    rw [Verity.Core.Uint256.le_def] at h_bound0 h_bound1
    exact ⟨h_bound0, h_bound1⟩
  have h_bound0_uint : observedBalance0 s ≤ maxUint112 := by
    simpa [Verity.Core.Uint256.le_def] using h_bfold.1
  have h_bound1_uint : observedBalance1 s ≤ maxUint112 := by
    simpa [Verity.Core.Uint256.le_def] using h_bfold.2
  have h_bound_guard_base :
      (decide (observedBalance0 s ≤ UniswapV2PairBase.maxUint112) &&
        decide (observedBalance1 s ≤ UniswapV2PairBase.maxUint112)) = true := by
    have h0 : observedBalance0 s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound0_uint
    have h1 : observedBalance1 s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound1_uint
    simpa [Bool.and_eq_true] using And.intro h0 h1
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_reserve_guard :
      (decide (s.storage reserve0Slot.slot ≤ observedBalance0 s) &&
        decide (s.storage reserve1Slot.slot ≤ observedBalance1 s)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_reserve0 h_reserve1
  have h_amount_guard :
      (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_amount0 h_amount1
  have h_supply_guard :
      (s.storage UniswapV2PairBase.totalSupplySlot.slot == (0 : Uint256)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_eq_true
    apply h_supply_ne
    simpa [UniswapV2PairBase.totalSupplySlot] using h_eq_true
  let pathResult :=
    UniswapV2PairBase.laterMintPath toAddr s.sender
      (observedBalance0 s) (observedBalance1 s)
      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
      (mintAmount0 s) (mintAmount1 s) (s.storage totalSupplySlot.slot) (mintLockedState s)
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_sender :
      msgSender (mintLockedState s) =
        ContractResult.success s.sender (mintLockedState s) := rfl
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_self :
      contractAddress (mintLockedState s) =
        ContractResult.success (mintLockedState s).thisAddress (mintLockedState s) := rfl
  have h_balance0 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance0 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance0_balanceOf_mintLockedState_app_nf s
  have h_balance1 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance1 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance1_balanceOf_mintLockedState_app_nf s
  have h_req_bound :
      Verity.require
          (decide (observedBalance0 s ≤ UniswapV2PairBase.maxUint112) &&
            decide (observedBalance1 s ≤ UniswapV2PairBase.maxUint112))
          "UniswapV2: OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_bound_guard_base, if_true]
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  have h_req_reserve :
      Verity.require
          (decide (observedBalance0 s ≥ s.storage reserve0Slot.slot) &&
            decide (observedBalance1 s ≥ s.storage reserve1Slot.slot))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simpa only [ge_iff_le] using (by
      simp only [Verity.require, h_reserve_guard, if_true])
  have h_req_amount :
      Verity.require
          (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_amount_guard, if_true]
  have h_get_supply :
      getStorage UniswapV2PairBase.totalSupplySlot (mintLockedState s) =
        ContractResult.success (s.storage totalSupplySlot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_totalSupply]
  have h_mint_prefix :
      (mint toAddr).run s = Contract.run (fun _ => pathResult) s := by
    unfold mint UniswapV2PairBase.mint Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_sender]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_self]
    rw [contract_bind_success _ _ _ _ _ h_balance0]
    rw [contract_bind_success _ _ _ _ _ h_balance1]
    rw [contract_bind_success _ _ _ _ _ h_req_bound]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_req_reserve]
    rw [mintAmount0_observed_nf, mintAmount1_observed_nf]
    rw [contract_bind_success _ _ _ _ _ h_req_amount]
    rw [contract_bind_success _ _ _ _ _ h_get_supply]
    simp only [h_supply_guard, Bool.false_eq_true, if_false]
    dsimp only [pathResult, Bind.bind, Verity.bind, Pure.pure, Verity.pure]
    generalize
      (UniswapV2PairBase.laterMintPath toAddr s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s) (s.storage totalSupplySlot.slot)
        (mintLockedState s)) = d
    cases d <;> rfl
  cases h_path : pathResult with
  | success minted post =>
      rw [h_mint_prefix]
      simp only [Contract.run, h_path]
      have h_path_raw :
          UniswapV2PairBase.laterMintPath toAddr s.sender
            (observedBalance0 s) (observedBalance1 s)
            (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
            (mintAmount0 s) (mintAmount1 s)
            (s.storage totalSupplySlot.slot) (mintLockedState s) =
            ContractResult.success minted post := by
        simpa only [pathResult] using h_path
      rw [h_path_raw]
  | «revert» msg post =>
      have h_impossible : False := by
        rw [h_mint_prefix, h_path] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
      cases h_impossible

theorem mintLockedState_events_eq (s : ContractState) :
    (mintLockedState s).events = s.events := by
  rfl

theorem mint_first_pairTransfers
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
                  pairTransfersAfterCall s ((mint toAddr).run s) = [] := by
  intro h_success h_supply_zero h_reserve0 h_reserve1 h_amount0 h_amount1
    h_product h_root
  rw [mint_first_run_eq_path toAddr s h_success h_supply_zero h_reserve0
    h_reserve1 h_amount0 h_amount1 h_product h_root]
  rw [pairTransfersAfterCall_of_events_eq s (mintLockedState s) _
    (mintLockedState_events_eq s)]
  exact firstMintPath_pairTransfers toAddr s.sender
    (observedBalance0 s) (observedBalance1 s)
    (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
    (mintAmount0 s) (mintAmount1 s) (mintLockedState s)

theorem mint_later_pairTransfers
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  (mint toAddr).run s =
      ContractResult.success liquidity ((mint toAddr).run s).snd →
    0 < (s.storage totalSupplySlot.slot).val →
      s.storage reserve0Slot.slot > 0 →
        s.storage reserve1Slot.slot > 0 →
          s.storage reserve0Slot.slot ≤ observedBalance0 s →
            s.storage reserve1Slot.slot ≤ observedBalance1 s →
              mintAmount0 s > 0 →
                mintAmount1 s > 0 →
                  liquidity > 0 →
                    pairTransfersAfterCall s ((mint toAddr).run s) = [] := by
  intro h_success h_supply_pos h_reserve0_pos h_reserve1_pos h_reserve0 h_reserve1
    h_amount0 h_amount1 h_liquidity
  rw [mint_later_run_eq_path toAddr s liquidity h_success h_supply_pos
    h_reserve0_pos h_reserve1_pos h_reserve0 h_reserve1 h_amount0
    h_amount1 h_liquidity]
  rw [pairTransfersAfterCall_of_events_eq s (mintLockedState s) _
    (mintLockedState_events_eq s)]
  exact laterMintPath_pairTransfers toAddr s.sender
    (observedBalance0 s) (observedBalance1 s)
    (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
    (mintAmount0 s) (mintAmount1 s) (s.storage totalSupplySlot.slot)
    (mintLockedState s)

theorem mint_success_pairTransfers
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  (mint toAddr).run s =
      ContractResult.success liquidity ((mint toAddr).run s).snd →
    s.storage reserve0Slot.slot ≤ observedBalance0 s →
      s.storage reserve1Slot.slot ≤ observedBalance1 s →
        mintAmount0 s > 0 →
          mintAmount1 s > 0 →
            (s.storage totalSupplySlot.slot = 0 →
              liquidity = mintFirstLiquidity s ∧
              (mintAmount0 s == 0 ||
                div (mintFirstProduct s) (mintAmount0 s) == mintAmount1 s) = true ∧
              mintFirstRoot s > minimumLiquidity) →
              (s.storage totalSupplySlot.slot ≠ 0 →
                s.storage reserve0Slot.slot > 0 ∧
                s.storage reserve1Slot.slot > 0 ∧
                liquidity > 0) →
                pairTransfersAfterCall s ((mint toAddr).run s) = [] := by
  intro h_success h_reserve0 h_reserve1 h_amount0 h_amount1 h_first h_later
  by_cases h_supply_zero : s.storage totalSupplySlot.slot = 0
  · rcases h_first h_supply_zero with ⟨h_liquidity_first, h_product, h_root⟩
    have h_success_first :
        (mint toAddr).run s =
          ContractResult.success (mintFirstLiquidity s) ((mint toAddr).run s).snd := by
      simpa [h_liquidity_first] using h_success
    exact mint_first_pairTransfers toAddr s h_success_first h_supply_zero
      h_reserve0 h_reserve1 h_amount0 h_amount1 h_product h_root
  · rcases h_later h_supply_zero with
      ⟨h_reserve0_pos, h_reserve1_pos, h_liquidity⟩
    have h_supply_pos : 0 < (s.storage totalSupplySlot.slot).val := by
      simpa [Verity.Core.Uint256.lt_def] using
        uint256_pos_of_ne_zero h_supply_zero
    exact mint_later_pairTransfers toAddr s liquidity h_success h_supply_pos
      h_reserve0_pos h_reserve1_pos h_reserve0 h_reserve1 h_amount0
      h_amount1 h_liquidity

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
        pairWorldAfterSubsequentMintRun liquidity s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts
      (pairTokenWorldAfterCall preTokens s ((mint toAddr).run s))
      ((mint toAddr).run s).snd
      (pairWorldAfterSubsequentMintRun liquidity s) h_after_tokens
      (mint_subsequent_success_run_storage_matches_world toAddr s liquidity
        h_success h_supply_pos h_reserve0_pos h_reserve1_pos h_reserve0
        h_reserve1 h_amount0 h_amount1 h_liquidity)
  have h_step :=
    mint_subsequent_success_run_matches_closed_world_step_from_run
      toAddr s liquidity h_run h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1
      h_liquidity h_ratio0 h_ratio1
  rw [h_before, h_after]
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

theorem burn_success_run_storage_matches_world
    (toAddr : Address) (s : ContractState) :
  (burn toAddr).run s =
      ContractResult.success (burnAmount0 s, burnAmount1 s) ((burn toAddr).run s).snd →
    pairPostCallSelfBalancesMatch s ((burn toAddr).run s).snd
      (burnBalance0After s) (burnBalance1After s) →
      0 < (burnLiquidity s).val →
        0 < (burnSupply s).val →
          (burnLiquidity s).val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - (burnLiquidity s).val →
              burnAmount0 s > 0 →
                burnAmount1 s > 0 →
                  burnAmount0 s ≤ observedBalance0 s →
                    burnAmount1 s ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          pairConcreteStorageMatchesWorld
                            ((burn toAddr).run s).snd (pairWorldAfterBurnRun s) := by
  intro h_success h_post h_liquidity_pos h_supply_pos h_liquidity_le
    h_locked_remaining h_amount0_pos h_amount1_pos h_amount0_le h_amount1_le
    h_bound0 h_bound1
  have h_success_exists :
      (burn toAddr).run s =
        ContractResult.success (burnAmount0 s, burnAmount1 s) ((burn toAddr).run s).snd := h_success
  have h_unlocked :=
    burn_success_run_implies_lock_open toAddr s ((burn toAddr).run s) rfl h_success_exists
  have h_guard0 :=
    burn_success_run_implies_amount0_product_guard toAddr s ((burn toAddr).run s)
      rfl h_success_exists (by simpa [Verity.Core.Uint256.lt_def] using h_liquidity_pos)
      (by simpa [Verity.Core.Uint256.lt_def] using h_supply_pos)
  have h_guard1 :=
    burn_success_run_implies_amount1_product_guard toAddr s ((burn toAddr).run s)
      rfl h_success_exists (by simpa [Verity.Core.Uint256.lt_def] using h_liquidity_pos)
      (by simpa [Verity.Core.Uint256.lt_def] using h_supply_pos)
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_liquidity_guard :
      (decide (burnLiquidity s > 0) && decide (burnSupply s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro
      (by simpa [Verity.Core.Uint256.lt_def] using h_liquidity_pos)
      (by simpa [Verity.Core.Uint256.lt_def] using h_supply_pos)
  have h_amount_guard :
      (decide (burnAmount0 s > 0) && decide (burnAmount1 s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_amount0_pos h_amount1_pos
  have h_bound_guard :
      (decide (burnBalance0After s ≤ UniswapV2PairBase.maxUint112) &&
        decide (burnBalance1After s ≤ UniswapV2PairBase.maxUint112)) = true := by
    have h0 : burnBalance0After s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound0
    have h1 : burnBalance1After s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound1
    simpa [Bool.and_eq_true] using And.intro h0 h1
  have h_after0 :
      ∀ readState : ContractState,
        TamaUniV2.erc20BalanceOf
            ((mintLockedState s).storageAddr token0Slot.slot)
            (mintLockedState s).thisAddress readState =
          ContractResult.success (burnBalance0After s) readState := by
    intro readState
    simpa [pairToken0, pairSelf, mintLockedState_storageAddr,
      mintLockedState_thisAddress] using
      (pairPostCallSelfBalancesMatch_balance0_app_nf
        (s := s) (post := ((burn toAddr).run s).snd)
        (readState := readState) (b0 := burnBalance0After s)
        (b1 := burnBalance1After s) h_post)
  have h_after1 :
      ∀ readState : ContractState,
        TamaUniV2.erc20BalanceOf
            ((mintLockedState s).storageAddr token1Slot.slot)
            (mintLockedState s).thisAddress readState =
          ContractResult.success (burnBalance1After s) readState := by
    intro readState
    simpa [pairToken1, pairSelf, mintLockedState_storageAddr,
      mintLockedState_thisAddress] using
      (pairPostCallSelfBalancesMatch_balance1_app_nf
        (s := s) (post := ((burn toAddr).run s).snd)
        (readState := readState) (b0 := burnBalance0After s)
        (b1 := burnBalance1After s) h_post)
  have h_supply_sub :
      (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s)).val =
        (burnSupply s).val - (burnLiquidity s).val := by
    simpa using
      (Verity.Core.Uint256.sub_eq_of_le
        (a := burnSupply s) (b := burnLiquidity s) h_liquidity_le)
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_timestamp :
      Verity.blockTimestamp s = ContractResult.success s.blockTimestamp s := rfl
  have h_previous :
      getStorage UniswapV2PairBase.blockTimestampLastSlot s =
        ContractResult.success (s.storage blockTimestampLastSlot.slot) s := by
    simp only [getStorage, blockTimestampLastSlot, UniswapV2PairBase.blockTimestampLastSlot]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_sender :
      msgSender (mintLockedState s) =
        ContractResult.success s.sender (mintLockedState s) := rfl
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_self :
      contractAddress (mintLockedState s) =
        ContractResult.success (mintLockedState s).thisAddress (mintLockedState s) := rfl
  have h_balance0 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance0 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance0_balanceOf_mintLockedState_app_nf s
  have h_balance1 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance1 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance1_balanceOf_mintLockedState_app_nf s
  have h_liquidity :
      getMapping UniswapV2PairBase.balancesSlot (mintLockedState s).thisAddress
          (mintLockedState s) =
        ContractResult.success (burnLiquidity s) (mintLockedState s) := by
    simp [getMapping, burnLiquidity, pairSelf, balancesSlot,
      UniswapV2PairBase.balancesSlot, mintLockedState, mintLockedState_thisAddress]
  have h_supply :
      getStorage UniswapV2PairBase.totalSupplySlot (mintLockedState s) =
        ContractResult.success (burnSupply s) (mintLockedState s) := by
    simp [getStorage, burnSupply, totalSupplySlot, UniswapV2PairBase.totalSupplySlot,
      mintLockedState, mintLockedState_storage_totalSupply]
  have h_req_liquidity :
      Verity.require (decide (burnLiquidity s > 0) && decide (burnSupply s > 0))
        "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED" (mintLockedState s) =
          ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_liquidity_guard, if_true]
  have h_req_overflow0 :
      Verity.require
          (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance0 s)) (burnLiquidity s) ==
              observedBalance0 s)
          "UniswapV2: BURN_OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    have h_guard0_mul :
        (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance0 s)) (burnLiquidity s) ==
              observedBalance0 s) = true := by
      simpa [burnAmount0Product] using h_guard0
    simp only [Verity.require, h_guard0_mul, if_true]
  have h_req_overflow1 :
      Verity.require
          (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance1 s)) (burnLiquidity s) ==
              observedBalance1 s)
          "UniswapV2: BURN_OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    have h_guard1_mul :
        (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance1 s)) (burnLiquidity s) ==
              observedBalance1 s) = true := by
      simpa [burnAmount1Product] using h_guard1
    simp only [Verity.require, h_guard1_mul, if_true]
  have h_req_amount :
      Verity.require
          (decide (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s) > 0) &&
            decide (div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s) > 0))
        "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED" (mintLockedState s) =
          ContractResult.success () (mintLockedState s) := by
    have h_amount_guard_mul :
        (decide (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s) > 0) &&
          decide (div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s) > 0)) =
            true := by
      simpa [burnAmount0, burnAmount1, burnAmount0Product, burnAmount1Product]
        using h_amount_guard
    simp only [Verity.require, h_amount_guard_mul, if_true]
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  let burnZeroBalanceState :=
    (setMapping UniswapV2PairBase.balancesSlot (mintLockedState s).thisAddress
      (0 : Uint256) (mintLockedState s)).snd
  let burnSupplyState :=
    (setStorage UniswapV2PairBase.totalSupplySlot
      (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s))
      burnZeroBalanceState).snd
  let burnTransferEventState :=
    (Contracts.emit "Transfer"
      [addressToWord (mintLockedState s).thisAddress, addressToWord zeroAddress,
        burnLiquidity s] burnSupplyState).snd
  let burnTransfer0State :=
    (TamaUniV2.pairSafeTransfer
      ((mintLockedState s).storageAddr token0Slot.slot) toAddr
        (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s))
      burnTransferEventState).snd
  let burnTransfer1State :=
    (TamaUniV2.pairSafeTransfer
      ((mintLockedState s).storageAddr token1Slot.slot) toAddr
        (div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s))
      burnTransfer0State).snd
  let burnPreUpdateState :=
    (Contracts.mstore (64 : Uint256) (128 : Uint256) burnTransfer1State).snd
  have h_zero_balance :
      setMapping UniswapV2PairBase.balancesSlot (mintLockedState s).thisAddress
          (0 : Uint256) (mintLockedState s) =
        ContractResult.success () burnZeroBalanceState := by
    rfl
  have h_set_supply :
      setStorage UniswapV2PairBase.totalSupplySlot
          (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s))
          burnZeroBalanceState =
        ContractResult.success () burnSupplyState := by
    rfl
  have h_emit_transfer :
      Contracts.emit "Transfer"
          [addressToWord (mintLockedState s).thisAddress, addressToWord zeroAddress,
            burnLiquidity s] burnSupplyState =
        ContractResult.success () burnTransferEventState := by
    rfl
  have h_transfer0 :
      TamaUniV2.pairSafeTransfer
          ((mintLockedState s).storageAddr token0Slot.slot) toAddr
          (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s))
          burnTransferEventState =
        ContractResult.success 1 burnTransfer0State := by
    rfl
  have h_transfer1 :
      TamaUniV2.pairSafeTransfer
          ((mintLockedState s).storageAddr token1Slot.slot) toAddr
          (div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s))
          burnTransfer0State =
        ContractResult.success 1 burnTransfer1State := by
    rfl
  have h_balance0_after :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress burnTransfer1State =
        ContractResult.success (burnBalance0After s) burnTransfer1State :=
    h_after0 burnTransfer1State
  have h_balance1_after :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress burnTransfer1State =
        ContractResult.success (burnBalance1After s) burnTransfer1State :=
    h_after1 burnTransfer1State
  have h_req_bound :
      Verity.require
          (decide (burnBalance0After s ≤ UniswapV2PairBase.maxUint112) &&
            decide (burnBalance1After s ≤ UniswapV2PairBase.maxUint112))
          "UniswapV2: OVERFLOW" burnTransfer1State =
        ContractResult.success () burnTransfer1State := by
    simp only [Verity.require, h_bound_guard, if_true]
  have h_mstore :
      Contracts.mstore (64 : Uint256) (128 : Uint256) burnTransfer1State =
        ContractResult.success () burnPreUpdateState := by
    rfl
  have h_burn_prefix :
      (burn toAddr).run s =
        Contract.run
          (fun _ =>
            ((do
              UniswapV2PairBase.updateReservesAndEmitSync
                (burnBalance0After s) (burnBalance1After s)
                (s.storage UniswapV2PairBase.reserve0Slot.slot)
                (s.storage UniswapV2PairBase.reserve1Slot.slot)
                (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
                (s.storage UniswapV2PairBase.blockTimestampLastSlot.slot)
              Contracts.emit "Burn"
                [addressToWord s.sender,
                  div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s),
                  div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s),
                  addressToWord toAddr]
              setStorage UniswapV2PairBase.unlockedSlot (1 : Uint256)
              Pure.pure
                (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s),
                  div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s))) :
                Contract (Uint256 × Uint256))
                burnPreUpdateState) s := by
    unfold burn UniswapV2PairBase.burn Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_timestamp]
    rw [contract_bind_success _ _ _ _ _ h_previous]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_sender]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_self]
    rw [contract_bind_success _ _ _ _ _ h_balance0]
    rw [contract_bind_success _ _ _ _ _ h_balance1]
    rw [contract_bind_success _ _ _ _ _ h_liquidity]
    rw [contract_bind_success _ _ _ _ _ h_supply]
    rw [contract_bind_success _ _ _ _ _ h_req_liquidity]
    rw [contract_bind_success _ _ _ _ _ h_req_overflow0]
    rw [contract_bind_success _ _ _ _ _ h_req_overflow1]
    rw [contract_bind_success _ _ _ _ _ h_req_amount]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_zero_balance]
    rw [contract_bind_success _ _ _ _ _ h_set_supply]
    rw [contract_bind_success _ _ _ _ _ h_emit_transfer]
    rw [contract_bind_success _ _ _ _ _ h_transfer0]
    rw [contract_bind_success _ _ _ _ _ h_transfer1]
    rw [contract_bind_success _ _ _ _ _ h_balance0_after]
    rw [contract_bind_success _ _ _ _ _ h_balance1_after]
    rw [contract_bind_success _ _ _ _ _ h_req_bound]
    rw [contract_bind_success _ _ _ _ _ h_mstore]
  have h_pre_update_totalSupply :
      burnPreUpdateState.storage totalSupplySlot.slot =
        Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s) := by
    rfl
  have h_supply_ne : ¬ (burnSupply s).val = 0 :=
    Nat.ne_of_gt h_supply_pos
  have h_supply_after_ne :
      ¬ (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s)).val = 0 := by
    rw [h_supply_sub]
    have h_min_pos : 0 < minimumLiquidityNat := by decide
    omega
  have h_update_storage :
      pairConcreteStorageMatchesWorld
        ((UniswapV2PairBase.updateReservesAndEmitSync
          (burnBalance0After s) (burnBalance1After s)
          (s.storage UniswapV2PairBase.reserve0Slot.slot)
          (s.storage UniswapV2PairBase.reserve1Slot.slot)
          (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (s.storage UniswapV2PairBase.blockTimestampLastSlot.slot)).run burnPreUpdateState).snd
        (pairWorldAfterBurnRun s) := by
    apply updateReservesAndEmitSync_run_storage_matches_world
    · simp only [pairWorldAfterBurnRun]
    · simp only [pairWorldAfterBurnRun]
    · change (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s)).val =
        (burnPreUpdateState.storage totalSupplySlot.slot).val
      rw [h_pre_update_totalSupply]
    · change pairWorldLockedLiquidity (burnSupply s) =
        pairWorldLockedLiquidity (burnPreUpdateState.storage totalSupplySlot.slot)
      rw [h_pre_update_totalSupply]
      simp [pairWorldLockedLiquidity, h_supply_ne, h_supply_after_ne]
  rw [h_burn_prefix]
  cases h_update_case :
      (UniswapV2PairBase.updateReservesAndEmitSync
        (burnBalance0After s) (burnBalance1After s)
        (s.storage UniswapV2PairBase.reserve0Slot.slot)
        (s.storage UniswapV2PairBase.reserve1Slot.slot)
        (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
        (s.storage UniswapV2PairBase.blockTimestampLastSlot.slot)) burnPreUpdateState with
  | success _ postUpdate =>
      unfold Contract.run at h_update_storage
      rw [h_update_case] at h_update_storage
      simp only [ContractResult.snd] at h_update_storage
      unfold Contract.run
      dsimp only [Bind.bind, Verity.bind]
      rw [h_update_case]
      simpa only [pairConcreteStorageMatchesWorld, ContractResult.snd,
        Pure.pure, Verity.pure, Contracts.emit, emitEvent, setStorage,
        reserve0Slot, reserve1Slot,
        totalSupplySlot, unlockedSlot, UniswapV2PairBase.unlockedSlot,
        pairWorldAfterBurnRun] using h_update_storage
  | «revert» reason postUpdate =>
      have h_impossible : False := by
        rw [h_burn_prefix] at h_success
        unfold Contract.run at h_success
        dsimp only [Bind.bind, Verity.bind] at h_success
        rw [h_update_case] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
      cases h_impossible

theorem burn_success_pairTransfers
    (toAddr : Address) (s : ContractState) :
  (burn toAddr).run s =
      ContractResult.success (burnAmount0 s, burnAmount1 s) ((burn toAddr).run s).snd →
    pairPostCallSelfBalancesMatch s ((burn toAddr).run s).snd
      (burnBalance0After s) (burnBalance1After s) →
      0 < (burnLiquidity s).val →
        0 < (burnSupply s).val →
          (burnLiquidity s).val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - (burnLiquidity s).val →
              burnAmount0 s > 0 →
                burnAmount1 s > 0 →
                  burnAmount0 s ≤ observedBalance0 s →
                    burnAmount1 s ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          pairTransfersAfterCall s ((burn toAddr).run s) =
                            [{ token := pairToken0 s, fromAddr := pairSelf s,
                               toAddr := toAddr, amount := burnAmount0 s },
                             { token := pairToken1 s, fromAddr := pairSelf s,
                               toAddr := toAddr, amount := burnAmount1 s }] := by
  intro h_success h_post h_liquidity_pos h_supply_pos h_liquidity_le
    _h_locked_remaining h_amount0_pos h_amount1_pos _h_amount0_le _h_amount1_le
    h_bound0 h_bound1
  have h_success_exists :
      (burn toAddr).run s =
        ContractResult.success (burnAmount0 s, burnAmount1 s) ((burn toAddr).run s).snd := h_success
  have h_unlocked :=
    burn_success_run_implies_lock_open toAddr s ((burn toAddr).run s) rfl h_success_exists
  have h_guard0 :=
    burn_success_run_implies_amount0_product_guard toAddr s ((burn toAddr).run s)
      rfl h_success_exists (by simpa [Verity.Core.Uint256.lt_def] using h_liquidity_pos)
      (by simpa [Verity.Core.Uint256.lt_def] using h_supply_pos)
  have h_guard1 :=
    burn_success_run_implies_amount1_product_guard toAddr s ((burn toAddr).run s)
      rfl h_success_exists (by simpa [Verity.Core.Uint256.lt_def] using h_liquidity_pos)
      (by simpa [Verity.Core.Uint256.lt_def] using h_supply_pos)
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_liquidity_guard :
      (decide (burnLiquidity s > 0) && decide (burnSupply s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro
      (by simpa [Verity.Core.Uint256.lt_def] using h_liquidity_pos)
      (by simpa [Verity.Core.Uint256.lt_def] using h_supply_pos)
  have h_amount_guard :
      (decide (burnAmount0 s > 0) && decide (burnAmount1 s > 0)) = true := by
    simpa [Bool.and_eq_true] using And.intro h_amount0_pos h_amount1_pos
  have h_bound_guard :
      (decide (burnBalance0After s ≤ UniswapV2PairBase.maxUint112) &&
        decide (burnBalance1After s ≤ UniswapV2PairBase.maxUint112)) = true := by
    have h0 : burnBalance0After s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound0
    have h1 : burnBalance1After s ≤ UniswapV2PairBase.maxUint112 := by
      simpa [maxUint112, UniswapV2PairBase.maxUint112] using h_bound1
    simpa [Bool.and_eq_true] using And.intro h0 h1
  have h_after0 :
      ∀ readState : ContractState,
        TamaUniV2.erc20BalanceOf
            ((mintLockedState s).storageAddr token0Slot.slot)
            (mintLockedState s).thisAddress readState =
          ContractResult.success (burnBalance0After s) readState := by
    intro readState
    simpa [pairToken0, pairSelf, mintLockedState_storageAddr,
      mintLockedState_thisAddress] using
      (pairPostCallSelfBalancesMatch_balance0_app_nf
        (s := s) (post := ((burn toAddr).run s).snd)
        (readState := readState) (b0 := burnBalance0After s)
        (b1 := burnBalance1After s) h_post)
  have h_after1 :
      ∀ readState : ContractState,
        TamaUniV2.erc20BalanceOf
            ((mintLockedState s).storageAddr token1Slot.slot)
            (mintLockedState s).thisAddress readState =
          ContractResult.success (burnBalance1After s) readState := by
    intro readState
    simpa [pairToken1, pairSelf, mintLockedState_storageAddr,
      mintLockedState_thisAddress] using
      (pairPostCallSelfBalancesMatch_balance1_app_nf
        (s := s) (post := ((burn toAddr).run s).snd)
        (readState := readState) (b0 := burnBalance0After s)
        (b1 := burnBalance1After s) h_post)
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_timestamp :
      Verity.blockTimestamp s = ContractResult.success s.blockTimestamp s := rfl
  have h_previous :
      getStorage UniswapV2PairBase.blockTimestampLastSlot s =
        ContractResult.success (s.storage blockTimestampLastSlot.slot) s := by
    simp only [getStorage, blockTimestampLastSlot, UniswapV2PairBase.blockTimestampLastSlot]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_sender :
      msgSender (mintLockedState s) =
        ContractResult.success s.sender (mintLockedState s) := rfl
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_self :
      contractAddress (mintLockedState s) =
        ContractResult.success (mintLockedState s).thisAddress (mintLockedState s) := rfl
  have h_balance0 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance0 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance0_balanceOf_mintLockedState_app_nf s
  have h_balance1 :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress (mintLockedState s) =
        ContractResult.success (observedBalance1 s) (mintLockedState s) := by
    simpa only [TamaUniV2.erc20BalanceOf] using
      observedBalance1_balanceOf_mintLockedState_app_nf s
  have h_liquidity :
      getMapping UniswapV2PairBase.balancesSlot (mintLockedState s).thisAddress
          (mintLockedState s) =
        ContractResult.success (burnLiquidity s) (mintLockedState s) := by
    simp [getMapping, burnLiquidity, pairSelf, balancesSlot,
      UniswapV2PairBase.balancesSlot, mintLockedState, mintLockedState_thisAddress]
  have h_supply :
      getStorage UniswapV2PairBase.totalSupplySlot (mintLockedState s) =
        ContractResult.success (burnSupply s) (mintLockedState s) := by
    simp [getStorage, burnSupply, totalSupplySlot, UniswapV2PairBase.totalSupplySlot,
      mintLockedState, mintLockedState_storage_totalSupply]
  have h_req_liquidity :
      Verity.require (decide (burnLiquidity s > 0) && decide (burnSupply s > 0))
        "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED" (mintLockedState s) =
          ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_liquidity_guard, if_true]
  have h_req_overflow0 :
      Verity.require
          (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance0 s)) (burnLiquidity s) ==
              observedBalance0 s)
          "UniswapV2: BURN_OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    have h_guard0_mul :
        (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance0 s)) (burnLiquidity s) ==
              observedBalance0 s) = true := by
      simpa [burnAmount0Product] using h_guard0
    simp only [Verity.require, h_guard0_mul, if_true]
  have h_req_overflow1 :
      Verity.require
          (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance1 s)) (burnLiquidity s) ==
              observedBalance1 s)
          "UniswapV2: BURN_OVERFLOW" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    have h_guard1_mul :
        (burnLiquidity s == 0 ||
            div (mul (burnLiquidity s) (observedBalance1 s)) (burnLiquidity s) ==
              observedBalance1 s) = true := by
      simpa [burnAmount1Product] using h_guard1
    simp only [Verity.require, h_guard1_mul, if_true]
  have h_req_amount :
      Verity.require
          (decide (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s) > 0) &&
            decide (div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s) > 0))
        "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED" (mintLockedState s) =
          ContractResult.success () (mintLockedState s) := by
    have h_amount_guard_mul :
        (decide (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s) > 0) &&
          decide (div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s) > 0)) =
            true := by
      simpa [burnAmount0, burnAmount1, burnAmount0Product, burnAmount1Product]
        using h_amount_guard
    simp only [Verity.require, h_amount_guard_mul, if_true]
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  let burnZeroBalanceState :=
    (setMapping UniswapV2PairBase.balancesSlot (mintLockedState s).thisAddress
      (0 : Uint256) (mintLockedState s)).snd
  let burnSupplyState :=
    (setStorage UniswapV2PairBase.totalSupplySlot
      (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s))
      burnZeroBalanceState).snd
  let burnTransferEventState :=
    (Contracts.emit "Transfer"
      [addressToWord (mintLockedState s).thisAddress, addressToWord zeroAddress,
        burnLiquidity s] burnSupplyState).snd
  let burnTransfer0State :=
    (TamaUniV2.pairSafeTransfer
      ((mintLockedState s).storageAddr token0Slot.slot) toAddr
        (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s))
      burnTransferEventState).snd
  let burnTransfer1State :=
    (TamaUniV2.pairSafeTransfer
      ((mintLockedState s).storageAddr token1Slot.slot) toAddr
        (div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s))
      burnTransfer0State).snd
  let burnPreUpdateState :=
    (Contracts.mstore (64 : Uint256) (128 : Uint256) burnTransfer1State).snd
  have h_zero_balance :
      setMapping UniswapV2PairBase.balancesSlot (mintLockedState s).thisAddress
          (0 : Uint256) (mintLockedState s) =
        ContractResult.success () burnZeroBalanceState := by
    rfl
  have h_set_supply :
      setStorage UniswapV2PairBase.totalSupplySlot
          (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s))
          burnZeroBalanceState =
        ContractResult.success () burnSupplyState := by
    rfl
  have h_emit_transfer :
      Contracts.emit "Transfer"
          [addressToWord (mintLockedState s).thisAddress, addressToWord zeroAddress,
            burnLiquidity s] burnSupplyState =
        ContractResult.success () burnTransferEventState := by
    rfl
  have h_transfer0 :
      TamaUniV2.pairSafeTransfer
          ((mintLockedState s).storageAddr token0Slot.slot) toAddr
          (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s))
          burnTransferEventState =
        ContractResult.success 1 burnTransfer0State := by
    rfl
  have h_transfer1 :
      TamaUniV2.pairSafeTransfer
          ((mintLockedState s).storageAddr token1Slot.slot) toAddr
          (div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s))
          burnTransfer0State =
        ContractResult.success 1 burnTransfer1State := by
    rfl
  have h_balance0_after :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token0Slot.slot)
          (mintLockedState s).thisAddress burnTransfer1State =
        ContractResult.success (burnBalance0After s) burnTransfer1State :=
    h_after0 burnTransfer1State
  have h_balance1_after :
      TamaUniV2.erc20BalanceOf ((mintLockedState s).storageAddr token1Slot.slot)
          (mintLockedState s).thisAddress burnTransfer1State =
        ContractResult.success (burnBalance1After s) burnTransfer1State :=
    h_after1 burnTransfer1State
  have h_req_bound :
      Verity.require
          (decide (burnBalance0After s ≤ UniswapV2PairBase.maxUint112) &&
            decide (burnBalance1After s ≤ UniswapV2PairBase.maxUint112))
          "UniswapV2: OVERFLOW" burnTransfer1State =
        ContractResult.success () burnTransfer1State := by
    simp only [Verity.require, h_bound_guard, if_true]
  have h_mstore :
      Contracts.mstore (64 : Uint256) (128 : Uint256) burnTransfer1State =
        ContractResult.success () burnPreUpdateState := by
    rfl
  have h_burn_prefix :
      (burn toAddr).run s =
        Contract.run
          (fun _ =>
            ((do
              UniswapV2PairBase.updateReservesAndEmitSync
                (burnBalance0After s) (burnBalance1After s)
                (s.storage UniswapV2PairBase.reserve0Slot.slot)
                (s.storage UniswapV2PairBase.reserve1Slot.slot)
                (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
                (s.storage UniswapV2PairBase.blockTimestampLastSlot.slot)
              Contracts.emit "Burn"
                [addressToWord s.sender,
                  div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s),
                  div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s),
                  addressToWord toAddr]
              setStorage UniswapV2PairBase.unlockedSlot (1 : Uint256)
              Pure.pure
                (div (mul (burnLiquidity s) (observedBalance0 s)) (burnSupply s),
                  div (mul (burnLiquidity s) (observedBalance1 s)) (burnSupply s))) :
                Contract (Uint256 × Uint256))
                burnPreUpdateState) s := by
    unfold burn UniswapV2PairBase.burn Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_timestamp]
    rw [contract_bind_success _ _ _ _ _ h_previous]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_sender]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_self]
    rw [contract_bind_success _ _ _ _ _ h_balance0]
    rw [contract_bind_success _ _ _ _ _ h_balance1]
    rw [contract_bind_success _ _ _ _ _ h_liquidity]
    rw [contract_bind_success _ _ _ _ _ h_supply]
    rw [contract_bind_success _ _ _ _ _ h_req_liquidity]
    rw [contract_bind_success _ _ _ _ _ h_req_overflow0]
    rw [contract_bind_success _ _ _ _ _ h_req_overflow1]
    rw [contract_bind_success _ _ _ _ _ h_req_amount]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_zero_balance]
    rw [contract_bind_success _ _ _ _ _ h_set_supply]
    rw [contract_bind_success _ _ _ _ _ h_emit_transfer]
    rw [contract_bind_success _ _ _ _ _ h_transfer0]
    rw [contract_bind_success _ _ _ _ _ h_transfer1]
    rw [contract_bind_success _ _ _ _ _ h_balance0_after]
    rw [contract_bind_success _ _ _ _ _ h_balance1_after]
    rw [contract_bind_success _ _ _ _ _ h_req_bound]
    rw [contract_bind_success _ _ _ _ _ h_mstore]
  rw [h_burn_prefix]
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, UniswapV2PairBase.updateReservesAndEmitSync,
    burnPreUpdateState, burnTransfer1State, burnTransfer0State,
    burnTransferEventState, burnSupplyState, burnZeroBalanceState,
    TamaUniV2.pairSafeTransfer, TamaUniV2.tracePairTokenSafeTransfer,
    TamaUniV2.pairTokenSafeTransferEvent, Contracts.safeTransfer,
    getStorage, setStorage, setMapping, Verity.blockTimestamp, Contract.run,
    ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contracts.emit, emitEvent, Contracts.rawLog, Contracts.mstore,
    pairToken0, pairToken1, pairSelf, observedBalance0, observedBalance1,
    mintLockedState, burnAmount0, burnAmount1,
    burnAmount0Product, burnAmount1Product, mintLockedState_storageAddr,
    mintLockedState_thisAddress, addressOfNat_toNat_mod_uint256,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [pairTransfersAfterEvents, pairTransferOfEvent, getStorage, setStorage,
        setMapping, Verity.blockTimestamp, Contract.run, ContractResult.snd,
        ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Contracts.emit, emitEvent, Contracts.rawLog, Contracts.mstore,
        pairToken0, pairToken1, pairSelf, observedBalance0, observedBalance1,
        mintLockedState, burnAmount0, burnAmount1, burnAmount0Product,
        burnAmount1Product, addressOfNat_toNat_mod_uint256,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

-- tama: discharges=pair_burn_success_reaches_expected_pair_state
theorem burn_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances) (s : ContractState) :
  pair_burn_success_reaches_expected_pair_state
    toAddr preTokens s ((burn toAddr).run s) := by
  intro h_run h_success h_boundary h_post_balances h_liquidity_pos h_supply_pos
    h_liquidity_le h_locked_remaining h_amount0_pos h_amount1_pos h_amount0_le
    h_amount1_le h_bound0 h_bound1 h_ratio0 h_ratio1
  rcases h_boundary with ⟨h_before_tokens, h_after_tokens⟩
  have h_before :
      pairWorldFromConcreteAndTokens preTokens s =
        pairWorldFromConcreteState s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
      (pairWorldFromConcreteState s) h_before_tokens
      (by simp [pairConcreteStorageMatchesWorld, pairWorldFromConcreteState])
  have h_after :
      pairWorldFromConcreteAndTokens
        (pairTokenWorldAfterCall preTokens s ((burn toAddr).run s))
          ((burn toAddr).run s).snd =
        pairWorldAfterBurnRun s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts
      (pairTokenWorldAfterCall preTokens s ((burn toAddr).run s))
      ((burn toAddr).run s).snd
      (pairWorldAfterBurnRun s) h_after_tokens
      (burn_success_run_storage_matches_world toAddr s h_success h_post_balances
        h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
        h_amount0_pos h_amount1_pos h_amount0_le h_amount1_le h_bound0 h_bound1)
  have h_step :=
    burn_success_run_matches_closed_world_step toAddr s h_run h_success
      h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
      h_amount0_pos h_amount1_pos h_amount0_le h_amount1_le h_bound0
      h_bound1 h_ratio0 h_ratio1
  rw [h_before, h_after]
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

private def contractPreservesState {α : Type} (c : Contract α) : Prop :=
  ∀ s, (c s).snd = s

private theorem contractPreservesState_pure {α : Type} (a : α) :
    contractPreservesState (Verity.pure a) := by
  intro s
  rfl

private theorem contractPreservesState_require (condition : Bool) (message : String) :
    contractPreservesState (Verity.require condition message) := by
  intro s
  unfold Verity.require
  cases condition <;> rfl

private theorem contractPreservesState_bind {α β : Type}
    (ma : Contract α) (f : α → Contract β)
    (h_ma : contractPreservesState ma)
    (h_f : ∀ a, contractPreservesState (f a)) :
    contractPreservesState (ma >>= f) := by
  intro s
  change ((Verity.bind ma f) s).snd = s
  unfold Verity.bind
  cases h_run : ma s with
  | success a s' =>
      have h_state : s' = s := by
        have h_preserved := h_ma s
        rw [h_run] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst s'
      exact h_f a s
  | «revert» reason s' =>
      have h_state : s' = s := by
        have h_preserved := h_ma s
        rw [h_run] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst s'
      rfl

private theorem contractPreservesState_run_snd {α : Type}
    (c : Contract α) (h_c : contractPreservesState c) (s : ContractState) :
    (c.run s).snd = s := by
  unfold Contract.run
  cases h_run : c s with
  | success a s' =>
      have h_state : s' = s := by
        have h_preserved := h_c s
        rw [h_run] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst s'
      rfl
  | «revert» reason s' =>
      rfl

private theorem finishSwapChecked_preserves_state_raw
    (sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out : Uint256) :
    contractPreservesState
      (UniswapV2PairBase.finishSwapChecked sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out) := by
  unfold UniswapV2PairBase.finishSwapChecked
  by_cases h_balance0 :
      balance0Now > sub reserve0Value amount0Out
  · rw [if_pos h_balance0]
    apply contractPreservesState_bind
    · exact contractPreservesState_pure PUnit.unit
    · intro _
      dsimp only
      by_cases h_balance1 :
          balance1Now > sub reserve1Value amount1Out
      · rw [if_pos h_balance1]
        apply contractPreservesState_bind
        · exact contractPreservesState_pure PUnit.unit
        · intro _
          repeat
            first
            | apply contractPreservesState_bind
            | intro _
            | exact contractPreservesState_require _ _ _
            | exact contractPreservesState_pure _ _
            | exact contractPreservesState_require _ _
            | exact contractPreservesState_pure _
      · rw [if_neg h_balance1]
        apply contractPreservesState_bind
        · exact contractPreservesState_pure ()
        · intro _
          repeat
            first
            | apply contractPreservesState_bind
            | intro _
            | exact contractPreservesState_require _ _ _
            | exact contractPreservesState_pure _ _
            | exact contractPreservesState_require _ _
            | exact contractPreservesState_pure _
  · rw [if_neg h_balance0]
    apply contractPreservesState_bind
    · exact contractPreservesState_pure ()
    · intro _
      dsimp only
      by_cases h_balance1 :
          balance1Now > sub reserve1Value amount1Out
      · rw [if_pos h_balance1]
        apply contractPreservesState_bind
        · exact contractPreservesState_pure PUnit.unit
        · intro _
          repeat
            first
            | apply contractPreservesState_bind
            | intro _
            | exact contractPreservesState_require _ _ _
            | exact contractPreservesState_pure _ _
            | exact contractPreservesState_require _ _
            | exact contractPreservesState_pure _
      · rw [if_neg h_balance1]
        apply contractPreservesState_bind
        · exact contractPreservesState_pure ()
        · intro _
          repeat
            first
            | apply contractPreservesState_bind
            | intro _
            | exact contractPreservesState_require _ _ _
            | exact contractPreservesState_pure _ _
            | exact contractPreservesState_require _ _
            | exact contractPreservesState_pure _

theorem finishSwapChecked_preserves_storage
    (sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out : Uint256)
    (s : ContractState) (slotIdx : Nat) :
    ((UniswapV2PairBase.finishSwapChecked sender
      balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out).run s).snd.storage slotIdx = s.storage slotIdx := by
  rw [contractPreservesState_run_snd]
  exact finishSwapChecked_preserves_state_raw sender
    balance0Now balance1Now reserve0Value reserve1Value amount0Out amount1Out

theorem finishSwapUpdate_run_storage_matches_world
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (original s : ContractState) (result : ContractResult Unit) :
  result =
      (UniswapV2PairBase.finishSwapUpdate sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out toAddr
        timestamp32 previousTimestamp).run s →
    result = ContractResult.success () result.snd →
      s.storage totalSupplySlot.slot = original.storage totalSupplySlot.slot →
    pairConcreteStorageMatchesWorld
      result.snd
      (pairWorldAfterSwapRun balance0Now balance1Now original) := by
  intro h_run h_success h_supply
  have h_success_run :
      (UniswapV2PairBase.finishSwapUpdate sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out toAddr
        timestamp32 previousTimestamp).run s =
        ContractResult.success () result.snd := by
    rw [← h_run]
    exact h_success
  let preUpdateState := (Contracts.mstore (64 : Uint256) (128 : Uint256) s).snd
  have h_mstore :
      Contracts.mstore (64 : Uint256) (128 : Uint256) s =
        ContractResult.success () preUpdateState := by
    rfl
  have h_pre_supply :
      preUpdateState.storage totalSupplySlot.slot = original.storage totalSupplySlot.slot := by
    dsimp only [preUpdateState]
    rw [← h_supply]
    rfl
  have h_update_storage :
      pairConcreteStorageMatchesWorld
        ((UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
          reserve0Value reserve1Value timestamp32 previousTimestamp).run preUpdateState).snd
        (pairWorldAfterSwapRun balance0Now balance1Now original) := by
    apply updateReservesAndEmitSync_run_storage_matches_world
    · simp only [pairWorldAfterSwapRun]
    · simp only [pairWorldAfterSwapRun]
    · change (original.storage totalSupplySlot.slot).val =
        (preUpdateState.storage totalSupplySlot.slot).val
      rw [h_pre_supply]
    · change pairWorldLockedLiquidity (original.storage totalSupplySlot.slot) =
        pairWorldLockedLiquidity (preUpdateState.storage totalSupplySlot.slot)
      rw [h_pre_supply]
  cases h_update_case :
      (UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
        reserve0Value reserve1Value timestamp32 previousTimestamp) preUpdateState with
  | success _ postUpdate =>
      unfold Contract.run at h_update_storage
      rw [h_update_case] at h_update_storage
      simp only [ContractResult.snd] at h_update_storage
      rw [h_run]
      unfold UniswapV2PairBase.finishSwapUpdate Contract.run at h_success_run ⊢
      dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure] at h_success_run ⊢
      simpa only [h_mstore, h_update_case, pairConcreteStorageMatchesWorld,
        ContractResult.snd, Contracts.emit, emitEvent, setStorage,
        reserve0Slot, reserve1Slot, totalSupplySlot, unlockedSlot,
        UniswapV2PairBase.unlockedSlot, pairWorldAfterSwapRun] using
        h_update_storage
  | «revert» reason postUpdate =>
      have h_impossible : False := by
        unfold UniswapV2PairBase.finishSwapUpdate Contract.run at h_success_run
        dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure] at h_success_run
        simp only [h_mstore, h_update_case, ContractResult.snd] at h_success_run
        cases h_success_run
      cases h_impossible

theorem finishSwap_run_storage_matches_world
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (original s : ContractState) (result : ContractResult Unit) :
  result =
      (UniswapV2PairBase.finishSwap sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out toAddr timestamp32 previousTimestamp).run s →
    result = ContractResult.success () result.snd →
      s.storage totalSupplySlot.slot = original.storage totalSupplySlot.slot →
  pairConcreteStorageMatchesWorld
      result.snd
      (pairWorldAfterSwapRun balance0Now balance1Now original) := by
  intro h_run h_success h_supply
  have h_success_run :
      (UniswapV2PairBase.finishSwap sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out toAddr timestamp32 previousTimestamp).run s =
        ContractResult.success () result.snd := by
    rw [← h_run]
    exact h_success
  cases h_checked_case :
      (UniswapV2PairBase.finishSwapChecked sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out) s with
  | success amounts checkedState =>
      have h_checked_state : checkedState = s := by
        have h_preserved :=
          finishSwapChecked_preserves_state_raw sender
            balance0Now balance1Now reserve0Value reserve1Value
            amount0Out amount1Out s
        rw [h_checked_case] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst checkedState
      rcases amounts with ⟨amount0In, amount1In⟩
      have h_update_run :
          result =
            (UniswapV2PairBase.finishSwapUpdate sender
              balance0Now balance1Now reserve0Value reserve1Value
              amount0In amount1In amount0Out amount1Out toAddr
              timestamp32 previousTimestamp).run s := by
        rw [h_run]
        unfold UniswapV2PairBase.finishSwap Contract.run
        dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure]
        rw [h_checked_case]
      exact finishSwapUpdate_run_storage_matches_world sender toAddr
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp
        original s result h_update_run h_success h_supply
  | «revert» reason checkedState =>
      have h_impossible : False := by
        unfold UniswapV2PairBase.finishSwap Contract.run at h_success_run
        dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure] at h_success_run
        rw [h_checked_case] at h_success_run
        cases h_success_run
      cases h_impossible

private theorem pairSafeTransfer_snd_storage
    (token toAddr : Address) (amount : Uint256) (s : ContractState) (idx : Nat) :
  (((TamaUniV2.pairSafeTransfer token toAddr amount) s).snd).storage idx =
    s.storage idx := by
  simp [TamaUniV2.pairSafeTransfer, Contracts.safeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, Bind.bind, Verity.bind,
    Pure.pure, Verity.pure]

private theorem pairSafeTransfer_snd_storageAddr
    (token toAddr : Address) (amount : Uint256) (s : ContractState) (idx : Nat) :
  (((TamaUniV2.pairSafeTransfer token toAddr amount) s).snd).storageAddr idx =
    s.storageAddr idx := by
  simp [TamaUniV2.pairSafeTransfer, Contracts.safeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, Bind.bind, Verity.bind,
    Pure.pure, Verity.pure]

private theorem pairSafeTransfer_snd_thisAddress
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
  (((TamaUniV2.pairSafeTransfer token toAddr amount) s).snd).thisAddress =
    s.thisAddress := by
  simp [TamaUniV2.pairSafeTransfer, Contracts.safeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, Bind.bind, Verity.bind,
    Pure.pure, Verity.pure]

private theorem uniswapV2Callback_snd_storage
    (toAddr sender : Address) (amount0Out amount1Out : Uint256)
    (s : ContractState) (idx : Nat) :
  (((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out] :
        Contract Unit) s).snd).storage idx =
    s.storage idx := by
  rfl

private theorem uniswapV2Callback_snd_storageAddr
    (toAddr sender : Address) (amount0Out amount1Out : Uint256)
    (s : ContractState) (idx : Nat) :
  (((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out] :
        Contract Unit) s).snd).storageAddr idx =
    s.storageAddr idx := by
  rfl

private theorem uniswapV2Callback_snd_thisAddress
    (toAddr sender : Address) (amount0Out amount1Out : Uint256)
    (s : ContractState) :
  (((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out] :
        Contract Unit) s).snd).thisAddress =
    s.thisAddress := by
  rfl

private theorem require_if_success_state
    {cond : Bool} {msg : String} {s s' : ContractState} {a : Unit} :
  (if cond = true then ContractResult.success () s
    else ContractResult.revert msg s) = ContractResult.success a s' →
    s' = s := by
  intro h
  cases cond <;> simp at h
  cases h
  rfl

theorem swap_success_run_storage_matches_world
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  (swap amount0Out amount1Out toAddr data).run s =
      ContractResult.success () ((swap amount0Out amount1Out toAddr data).run s).snd →
    pairPostCallSelfBalancesMatch s
      ((swap amount0Out amount1Out toAddr data).run s).snd balance0Now balance1Now →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          pairConcreteStorageMatchesWorld
            ((swap amount0Out amount1Out toAddr data).run s).snd
            (pairWorldAfterSwapRun balance0Now balance1Now s) := by
  intro h_success h_post h_liq0 h_liq1
  have h_success_exists :
      (swap amount0Out amount1Out toAddr data).run s =
        ContractResult.success () ((swap amount0Out amount1Out toAddr data).run s).snd :=
    h_success
  have h_unlocked :=
    swap_success_run_implies_lock_open amount0Out amount1Out toAddr data s
      ((swap amount0Out amount1Out toAddr data).run s) rfl h_success_exists
  have h_nonzero :=
    swap_success_run_implies_nonzero_output amount0Out amount1Out toAddr data s
      ((swap amount0Out amount1Out toAddr data).run s) rfl h_success_exists
  have h_output : amount0Out > 0 ∨ amount1Out > 0 := by
    rcases h_nonzero with h_amount0 | h_amount1
    · exact Or.inl (uint256_pos_of_ne_zero h_amount0)
    · exact Or.inr (uint256_pos_of_ne_zero h_amount1)
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_output_guard : (amount0Out > 0 || amount1Out > 0) = true := by
    simpa [Bool.or_eq_true] using h_output
  have h_liq_guard :
      (amount0Out < s.storage reserve0Slot.slot &&
        amount1Out < s.storage reserve1Slot.slot) = true := by
    simpa [Bool.and_eq_true] using And.intro h_liq0 h_liq1
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_timestamp :
      Verity.blockTimestamp s = ContractResult.success s.blockTimestamp s := rfl
  have h_previous :
      getStorage UniswapV2PairBase.blockTimestampLastSlot s =
        ContractResult.success (s.storage blockTimestampLastSlot.slot) s := by
    simp only [getStorage, blockTimestampLastSlot, UniswapV2PairBase.blockTimestampLastSlot]
  have h_req_output :
      Verity.require (amount0Out > 0 || amount1Out > 0)
        "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT" s =
          ContractResult.success () s := by
    simp only [Verity.require, h_output_guard, if_true]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  have h_req_liq :
      Verity.require
          (amount0Out < s.storage reserve0Slot.slot &&
            amount1Out < s.storage reserve1Slot.slot)
          "UniswapV2: INSUFFICIENT_LIQUIDITY" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_liq_guard, if_true]
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_to_guard :
      (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
        toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot) = true := by
    by_cases h_guard :
        (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
          toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot) = true
    · exact h_guard
    · exfalso
      have h_req_to_false :
          Verity.require
              (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
                toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
              "UniswapV2: INVALID_TO" (mintLockedState s) =
            ContractResult.revert "UniswapV2: INVALID_TO" (mintLockedState s) := by
        simp only [Verity.require]
        rw [if_neg h_guard]
      have h_swap_invalid :
          (swap amount0Out amount1Out toAddr data).run s =
            ContractResult.revert "UniswapV2: INVALID_TO" s := by
        unfold swap UniswapV2PairBase.swap Contract.run
        rw [contract_bind_success _ _ _ _ _ h_get_lock]
        rw [contract_bind_success _ _ _ _ _ h_req_lock]
        rw [contract_bind_success _ _ _ _ _ h_timestamp]
        rw [contract_bind_success _ _ _ _ _ h_previous]
        rw [contract_bind_success _ _ _ _ _ h_req_output]
        rw [contract_bind_success _ _ _ _ _ h_set_lock]
        rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
        rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
        rw [contract_bind_success _ _ _ _ _ h_req_liq]
        rw [contract_bind_success _ _ _ _ _ h_token0]
        rw [contract_bind_success _ _ _ _ _ h_token1]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_req_to_false]
      rw [h_swap_invalid] at h_success
      cases h_success
  have h_req_to :
      Verity.require
          (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
            toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          "UniswapV2: INVALID_TO" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_to_guard, if_true]
  let token0Value := (mintLockedState s).storageAddr token0Slot.slot
  let token1Value := (mintLockedState s).storageAddr token1Slot.slot
  let swapTransfer0State :=
    if amount0Out > 0 then
      (TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out (mintLockedState s)).snd
    else
      mintLockedState s
  let swapTransfer1State :=
    if amount1Out > 0 then
      (TamaUniV2.pairSafeTransfer token1Value toAddr amount1Out swapTransfer0State).snd
    else
      swapTransfer0State
  let swapSender := swapTransfer1State.sender
  let swapCallbackState :=
    ((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord swapSender, amount0Out, amount1Out] :
        Contract Unit) swapTransfer1State).snd
  have h_sender :
      msgSender swapTransfer1State =
        ContractResult.success swapSender swapTransfer1State := by
    rfl
  have h_callback :
      ((ecmDo uniswapV2CallbackModule
          [addressToWord toAddr, addressToWord swapSender, amount0Out, amount1Out] :
            Contract Unit) swapTransfer1State) =
        ContractResult.success () swapCallbackState := by
    dsimp [swapCallbackState, swapSender]
    rfl
  have h_self :
      contractAddress swapCallbackState =
        ContractResult.success swapCallbackState.thisAddress swapCallbackState := by
    rfl
  have h_transfer0_thisAddress :
      swapTransfer0State.thisAddress = s.thisAddress := by
    dsimp only [swapTransfer0State]
    by_cases h_amount0 : amount0Out > 0
    · rw [if_pos h_amount0]
      rw [pairSafeTransfer_snd_thisAddress]
      exact mintLockedState_thisAddress s
    · rw [if_neg h_amount0]
      exact mintLockedState_thisAddress s
  have h_transfer1_thisAddress :
      swapTransfer1State.thisAddress = s.thisAddress := by
    dsimp only [swapTransfer1State]
    by_cases h_amount1 : amount1Out > 0
    · rw [if_pos h_amount1]
      rw [pairSafeTransfer_snd_thisAddress]
      exact h_transfer0_thisAddress
    · rw [if_neg h_amount1]
      exact h_transfer0_thisAddress
  have h_callback_thisAddress :
      swapCallbackState.thisAddress = s.thisAddress := by
    calc
      swapCallbackState.thisAddress = swapTransfer1State.thisAddress := by
        simpa [swapCallbackState] using
          (uniswapV2Callback_snd_thisAddress
            toAddr swapSender amount0Out amount1Out swapTransfer1State)
      _ = s.thisAddress := h_transfer1_thisAddress
  have h_balance0_after :
      TamaUniV2.erc20BalanceOf token0Value swapCallbackState.thisAddress
          swapCallbackState =
        ContractResult.success balance0Now swapCallbackState := by
    dsimp only [token0Value]
    simpa [pairToken0, pairSelf, mintLockedState_storageAddr,
      mintLockedState_thisAddress, h_callback_thisAddress] using
      (pairPostCallSelfBalancesMatch_balance0_app_nf
        (s := s) (post := ((swap amount0Out amount1Out toAddr data).run s).snd)
        (readState := swapCallbackState) (b0 := balance0Now)
        (b1 := balance1Now) h_post)
  have h_balance1_after :
      TamaUniV2.erc20BalanceOf token1Value swapCallbackState.thisAddress
          swapCallbackState =
        ContractResult.success balance1Now swapCallbackState := by
    dsimp only [token1Value]
    simpa [pairToken1, pairSelf, mintLockedState_storageAddr,
      mintLockedState_thisAddress, h_callback_thisAddress] using
      (pairPostCallSelfBalancesMatch_balance1_app_nf
        (s := s) (post := ((swap amount0Out amount1Out toAddr data).run s).snd)
        (readState := swapCallbackState) (b0 := balance0Now)
        (b1 := balance1Now) h_post)
  have h_callback_supply :
      swapCallbackState.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot := by
    have h_transfer0_supply :
        swapTransfer0State.storage totalSupplySlot.slot =
          s.storage totalSupplySlot.slot := by
      dsimp only [swapTransfer0State]
      by_cases h_amount0 : amount0Out > 0
      · rw [if_pos h_amount0]
        rw [pairSafeTransfer_snd_storage]
        exact mintLockedState_storage_totalSupply s
      · rw [if_neg h_amount0]
        exact mintLockedState_storage_totalSupply s
    have h_transfer1_supply :
        swapTransfer1State.storage totalSupplySlot.slot =
          s.storage totalSupplySlot.slot := by
      dsimp only [swapTransfer1State]
      by_cases h_amount1 : amount1Out > 0
      · rw [if_pos h_amount1]
        rw [pairSafeTransfer_snd_storage]
        exact h_transfer0_supply
      · rw [if_neg h_amount1]
        exact h_transfer0_supply
    calc
      swapCallbackState.storage totalSupplySlot.slot =
          swapTransfer1State.storage totalSupplySlot.slot := by
        simpa [swapCallbackState] using
          (uniswapV2Callback_snd_storage
            toAddr swapSender amount0Out amount1Out swapTransfer1State
            totalSupplySlot.slot)
      _ = s.storage totalSupplySlot.slot := h_transfer1_supply
  have h_swap_prefix :
      (swap amount0Out amount1Out toAddr data).run s =
        Contract.run
          (fun _ =>
            ((UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
              (s.storage blockTimestampLastSlot.slot)) : Contract Unit)
              swapCallbackState) s := by
    unfold swap UniswapV2PairBase.swap Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_timestamp]
    rw [contract_bind_success _ _ _ _ _ h_previous]
    rw [contract_bind_success _ _ _ _ _ h_req_output]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_req_liq]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_req_to]
    by_cases h_amount0 : amount0Out > 0
    · rw [if_pos h_amount0]
      have h_transfer0_success :
          TamaUniV2.pairSafeTransfer
              ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
              toAddr amount0Out (mintLockedState s) =
            ContractResult.success 1 swapTransfer0State := by
        dsimp only [swapTransfer0State, token0Value]
        rw [if_pos h_amount0]
        rfl
      dsimp only [Bind.bind, Verity.bind]
      rw [h_transfer0_success]
      dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure]
      by_cases h_amount1 : amount1Out > 0
      · rw [if_pos h_amount1]
        have h_transfer1_success :
            TamaUniV2.pairSafeTransfer
                ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
                toAddr amount1Out swapTransfer0State =
              ContractResult.success 1 swapTransfer1State := by
          dsimp only [swapTransfer1State, token1Value]
          rw [if_pos h_amount1]
          rfl
        dsimp only [Bind.bind, Verity.bind]
        rw [h_transfer1_success]
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer1State =
          ContractResult.success () swapTransfer1State by rfl]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_sender]
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer1State =
          ContractResult.success () swapCallbackState by simpa using h_callback]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_self]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance0_after]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance1_after]
      · rw [if_neg h_amount1]
        have h_transfer1_state : swapTransfer1State = swapTransfer0State := by
          dsimp only [swapTransfer1State]
          rw [if_neg h_amount1]
        have h_sender' :
            msgSender swapTransfer0State =
              ContractResult.success swapSender swapTransfer0State := by
          simpa [h_transfer1_state] using h_sender
        have h_callback' :
            ((ecmDo uniswapV2CallbackModule
                [addressToWord toAddr, addressToWord swapSender, amount0Out, amount1Out] :
                  Contract Unit) swapTransfer0State) =
              ContractResult.success () swapCallbackState := by
          simpa [h_transfer1_state] using h_callback
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer0State =
          ContractResult.success () swapTransfer0State by rfl]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_sender']
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer0State =
          ContractResult.success () swapCallbackState by simpa using h_callback']
        dsimp only [Bind.bind, Verity.bind]
        rw [h_self]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance0_after]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance1_after]
    · rw [if_neg h_amount0]
      have h_transfer0_state : swapTransfer0State = mintLockedState s := by
        dsimp only [swapTransfer0State]
        rw [if_neg h_amount0]
      dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure]
      by_cases h_amount1 : amount1Out > 0
      · rw [if_pos h_amount1]
        have h_transfer1_success :
            TamaUniV2.pairSafeTransfer
                ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
                toAddr amount1Out (mintLockedState s) =
              ContractResult.success 1 swapTransfer1State := by
          dsimp only [swapTransfer1State, token1Value]
          rw [h_transfer0_state]
          rw [if_pos h_amount1]
          rfl
        dsimp only [Bind.bind, Verity.bind]
        rw [h_transfer1_success]
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer1State =
          ContractResult.success () swapTransfer1State by rfl]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_sender]
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer1State =
          ContractResult.success () swapCallbackState by simpa using h_callback]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_self]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance0_after]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance1_after]
      · rw [if_neg h_amount1]
        have h_transfer1_state : swapTransfer1State = mintLockedState s := by
          dsimp only [swapTransfer1State]
          rw [h_transfer0_state]
          rw [if_neg h_amount1]
        have h_sender' :
            msgSender (mintLockedState s) =
              ContractResult.success swapSender (mintLockedState s) := by
          simpa [h_transfer1_state] using h_sender
        have h_callback' :
            ((ecmDo uniswapV2CallbackModule
                [addressToWord toAddr, addressToWord swapSender, amount0Out, amount1Out] :
                  Contract Unit) (mintLockedState s)) =
              ContractResult.success () swapCallbackState := by
          simpa [h_transfer1_state] using h_callback
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) (mintLockedState s) =
          ContractResult.success () (mintLockedState s) by rfl]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_sender']
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) (mintLockedState s) =
          ContractResult.success () swapCallbackState by simpa using h_callback']
        dsimp only [Bind.bind, Verity.bind]
        rw [h_self]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance0_after]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance1_after]
  have h_finish_success_raw :
      UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
        (s.storage blockTimestampLastSlot.slot) swapCallbackState =
          ContractResult.success ()
            (UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
              (s.storage blockTimestampLastSlot.slot) swapCallbackState).snd := by
    cases h_finish :
        UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
          (s.storage blockTimestampLastSlot.slot) swapCallbackState with
    | success value postFinish =>
        cases value
        rfl
    | «revert» reason postFinish =>
        rw [h_swap_prefix] at h_success
        unfold Contract.run at h_success
        dsimp only at h_success
        rw [h_finish] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
  have h_finish_success :
      (UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
        (s.storage blockTimestampLastSlot.slot)).run swapCallbackState =
          ContractResult.success ()
            ((UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
              (s.storage blockTimestampLastSlot.slot)).run swapCallbackState).snd := by
    unfold Contract.run
    rw [h_finish_success_raw]
    rfl
  have h_finish_storage :
      pairConcreteStorageMatchesWorld
        ((UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
          (s.storage blockTimestampLastSlot.slot)).run swapCallbackState).snd
        (pairWorldAfterSwapRun balance0Now balance1Now s) := by
    apply finishSwap_run_storage_matches_world
    · rfl
    · exact h_finish_success
    · exact h_callback_supply
  rw [h_swap_prefix]
  unfold Contract.run
  dsimp only
  rw [h_finish_success_raw]
  have h_finish_storage' := h_finish_storage
  unfold Contract.run at h_finish_storage'
  rw [h_finish_success_raw] at h_finish_storage'
  simpa only [ContractResult.snd] using h_finish_storage'

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
  intro h_run h_success h_boundary h_post_balances h_liq0 h_liq1 h_input
    h_balance0 h_balance1 h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  rcases h_boundary with ⟨h_before_tokens, h_after_tokens⟩
  have h_before :
      pairWorldFromConcreteAndTokens preTokens s =
        pairWorldFromConcreteState s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
      (pairWorldFromConcreteState s) h_before_tokens
      (by simp [pairConcreteStorageMatchesWorld, pairWorldFromConcreteState])
  have h_after :
      pairWorldFromConcreteAndTokens
        (pairTokenWorldAfterCall preTokens s
          ((swap amount0Out amount1Out toAddr data).run s))
        ((swap amount0Out amount1Out toAddr data).run s).snd =
        pairWorldAfterSwapRun balance0Now balance1Now s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts
      (pairTokenWorldAfterCall preTokens s
        ((swap amount0Out amount1Out toAddr data).run s))
      ((swap amount0Out amount1Out toAddr data).run s).snd
      (pairWorldAfterSwapRun balance0Now balance1Now s) h_after_tokens
      (swap_success_run_storage_matches_world
        amount0Out amount1Out toAddr data balance0Now balance1Now s
        h_success h_post_balances h_liq0 h_liq1)
  have h_step :=
    swap_success_run_matches_closed_world_step_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  rw [h_before, h_after]
  exact h_step


end TamaUniV2.Proof.UniswapV2PairProof
