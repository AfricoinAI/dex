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

private theorem contractPreservesStorageAddr_skim (toAddr : Address) :
    contractPreservesStorageAddr (skim toAddr) := by
  unfold skim UniswapV2PairBase.skim
  repeat
    first
    | exact contractPreservesStorageAddr_getStorage _
    | exact contractPreservesStorageAddr_getStorageAddr _
    | exact contractPreservesStorageAddr_require _ _
    | exact contractPreservesStorageAddr_setStorage _ _
    | exact contractPreservesStorageAddr_contractAddress
    | exact contractPreservesStorageAddr_erc20BalanceOf _ _
    | exact contractPreservesStorageAddr_pairSafeTransfer _ _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _

private theorem contractPreservesStorageMap_skim (key toAddr : Address) :
    contractPreservesStorageMap key (skim toAddr) := by
  unfold skim UniswapV2PairBase.skim
  repeat
    first
    | exact contractPreservesStorageMap_getStorage key _
    | exact contractPreservesStorageMap_getStorageAddr key _
    | exact contractPreservesStorageMap_require key _ _
    | exact contractPreservesStorageMap_setStorage key _ _
    | exact contractPreservesStorageMap_contractAddress key
    | exact contractPreservesStorageMap_erc20BalanceOf key _ _
    | exact contractPreservesStorageMap_pairSafeTransfer key _ _ _
    | exact contractPreservesStorageMap_pure key _
    | apply contractPreservesStorageMap_bind
    | intro _

theorem skim_run_storageAddr_frame
    (toAddr : Address) (s : ContractState) (i : Nat) :
  ((skim toAddr).run s).snd.storageAddr i = s.storageAddr i :=
  contractPreservesStorageAddr_run_snd (skim toAddr)
    (contractPreservesStorageAddr_skim toAddr) s i

theorem skim_caller_lp_frame
    (toAddr caller : Address) (s : ContractState) :
  ((skim toAddr).run s).snd.storageMap balancesSlot.slot caller =
    s.storageMap balancesSlot.slot caller := by
  exact contractPreservesStorageMap_run_snd caller (skim toAddr)
    (contractPreservesStorageMap_skim caller toAddr) s




end TamaUniV2.Proof.UniswapV2PairProof
