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

private theorem contractPreservesStorageAddr_burn (toAddr : Address) :
    contractPreservesStorageAddr (burn toAddr) := by
  unfold burn UniswapV2PairBase.burn
  repeat
    first
    | exact contractPreservesStorageAddr_getStorage _
    | exact contractPreservesStorageAddr_getStorageAddr _
    | exact contractPreservesStorageAddr_getMapping _ _
    | exact contractPreservesStorageAddr_require _ _
    | exact contractPreservesStorageAddr_setStorage _ _
    | exact contractPreservesStorageAddr_setMapping _ _ _
    | exact contractPreservesStorageAddr_blockTimestamp
    | exact contractPreservesStorageAddr_msgSender
    | exact contractPreservesStorageAddr_contractAddress
    | exact contractPreservesStorageAddr_erc20BalanceOf _ _
    | exact contractPreservesStorageAddr_emit _ _
    | exact contractPreservesStorageAddr_pairSafeTransfer _ _ _
    | exact contractPreservesStorageAddr_mstore _ _
    | exact contractPreservesStorageAddr_updateReservesAndEmitSync _ _ _ _ _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _

theorem burn_run_storageAddr_frame
    (toAddr : Address) (s : ContractState) (i : Nat) :
  ((burn toAddr).run s).snd.storageAddr i = s.storageAddr i :=
  contractPreservesStorageAddr_run_snd (burn toAddr)
    (contractPreservesStorageAddr_burn toAddr) s i


end TamaUniV2.Proof.UniswapV2PairProof
