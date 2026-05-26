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

theorem mint_success_run_implies_prefix_guards
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256)
    (liquidity : Uint256) :
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      mintAmount0 s > 0 ∧
      mintAmount1 s > 0 ∧
      (s.storage totalSupplySlot.slot = 0 →
        (UniswapV2PairBase.firstMintPath toAddr s.sender
          (observedBalance0 s) (observedBalance1 s)
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s) =
            ContractResult.success liquidity result.snd) ∧
      (s.storage totalSupplySlot.slot ≠ 0 →
        (UniswapV2PairBase.laterMintPath toAddr s.sender
          (observedBalance0 s) (observedBalance1 s)
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          (mintAmount0 s) (mintAmount1 s)
          (s.storage totalSupplySlot.slot)).run (mintLockedState s) =
            ContractResult.success liquidity result.snd) := by
  intro h_run h_success
  subst result
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
  have h_reserve_guard :
      (decide (observedBalance0 s ≥ s.storage reserve0Slot.slot) &&
        decide (observedBalance1 s ≥ s.storage reserve1Slot.slot)) = true := by
    by_cases h_guard :
        (decide (observedBalance0 s ≥ s.storage reserve0Slot.slot) &&
          decide (observedBalance1 s ≥ s.storage reserve1Slot.slot)) = true
    · exact h_guard
    · have h_false :
          (decide (observedBalance0 s ≥ s.storage reserve0Slot.slot) &&
            decide (observedBalance1 s ≥ s.storage reserve1Slot.slot)) = false :=
        Bool.eq_false_of_not_eq_true h_guard
      have h_revert :
          (mint toAddr).run s =
            ContractResult.revert "UniswapV2: INSUFFICIENT_AMOUNT" s := by
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
        simp only [Verity.require, h_false, Bool.false_eq_true, if_false,
          Bind.bind, Verity.bind]
      rw [h_revert] at h_success
      cases h_success
  have h_req_reserve :
      Verity.require
          (decide (observedBalance0 s ≥ s.storage reserve0Slot.slot) &&
            decide (observedBalance1 s ≥ s.storage reserve1Slot.slot))
          "UniswapV2: INSUFFICIENT_AMOUNT" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_reserve_guard, if_true]
  have h_amount_guard :
      (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0)) = true := by
    by_cases h_guard :
        (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0)) = true
    · exact h_guard
    · have h_false :
          (decide (mintAmount0 s > 0) && decide (mintAmount1 s > 0)) = false :=
        Bool.eq_false_of_not_eq_true h_guard
      have h_revert :
          (mint toAddr).run s =
            ContractResult.revert "UniswapV2: INSUFFICIENT_AMOUNT" s := by
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
        simp only [Verity.require, h_false, Bool.false_eq_true, if_false,
          Bind.bind, Verity.bind]
      rw [h_revert] at h_success
      cases h_success
  have h_amount0 : mintAmount0 s > 0 := by
    have h_parts : mintAmount0 s > 0 ∧ mintAmount1 s > 0 := by
      simpa [Bool.and_eq_true] using h_amount_guard
    exact h_parts.1
  have h_amount1 : mintAmount1 s > 0 := by
    have h_parts : mintAmount0 s > 0 ∧ mintAmount1 s > 0 := by
      simpa [Bool.and_eq_true] using h_amount_guard
    exact h_parts.2
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
  constructor
  · exact h_amount0
  constructor
  · exact h_amount1
  constructor
  · intro h_supply_zero
    have h_supply_zero_raw : s.storage 8 = (0 : Uint256) := by
      simpa [totalSupplySlot] using h_supply_zero
    have h_supply_guard :
        (s.storage UniswapV2PairBase.totalSupplySlot.slot == (0 : Uint256)) = true := by
      simp [UniswapV2PairBase.totalSupplySlot, h_supply_zero_raw]
    let pathResult :=
      UniswapV2PairBase.firstMintPath toAddr s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s) (mintLockedState s)
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
    | success minted post =>
        have h_success_path :
            ContractResult.success minted post =
              ContractResult.success liquidity post := by
          rw [h_mint_prefix, h_path] at h_success
          simpa only [Contract.run, ContractResult.snd] using h_success
        cases h_success_path
        have h_path_raw :
            UniswapV2PairBase.firstMintPath toAddr s.sender
              (observedBalance0 s) (observedBalance1 s)
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              (mintAmount0 s) (mintAmount1 s) (mintLockedState s) =
                ContractResult.success liquidity post := by
          simpa only [pathResult] using h_path
        have h_public_snd : ((mint toAddr).run s).snd = post := by
          rw [h_mint_prefix, h_path]
          simp only [Contract.run, ContractResult.snd]
        rw [h_public_snd]
        simp only [Contract.run, h_path_raw]
    | «revert» msg post =>
        have h_impossible : False := by
          rw [h_mint_prefix, h_path] at h_success
          simp only [Contract.run, ContractResult.snd] at h_success
          cases h_success
        cases h_impossible
  · intro h_supply_nonzero
    have h_supply_guard :
        (s.storage UniswapV2PairBase.totalSupplySlot.slot == (0 : Uint256)) = false := by
      apply Bool.eq_false_iff.mpr
      intro h_eq_true
      apply h_supply_nonzero
      simpa [UniswapV2PairBase.totalSupplySlot] using h_eq_true
    let pathResult :=
      UniswapV2PairBase.laterMintPath toAddr s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s) (s.storage totalSupplySlot.slot)
        (mintLockedState s)
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
        have h_success_path :
            ContractResult.success minted post =
              ContractResult.success liquidity post := by
          rw [h_mint_prefix, h_path] at h_success
          simpa only [Contract.run, ContractResult.snd] using h_success
        cases h_success_path
        have h_path_raw :
            UniswapV2PairBase.laterMintPath toAddr s.sender
              (observedBalance0 s) (observedBalance1 s)
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              (mintAmount0 s) (mintAmount1 s)
              (s.storage totalSupplySlot.slot) (mintLockedState s) =
                ContractResult.success liquidity post := by
          simpa only [pathResult] using h_path
        have h_public_snd : ((mint toAddr).run s).snd = post := by
          rw [h_mint_prefix, h_path]
          simp only [Contract.run, ContractResult.snd]
        rw [h_public_snd]
        simp only [Contract.run, h_path_raw]
    | «revert» msg post =>
        have h_impossible : False := by
          rw [h_mint_prefix, h_path] at h_success
          simp only [Contract.run, ContractResult.snd] at h_success
          cases h_success
        cases h_impossible

private theorem uint256_mul_val_le_nat_mul (a b : Uint256) :
    (mul a b).val ≤ a.val * b.val := by
  simp [Verity.EVM.Uint256.mul, Verity.Core.Uint256.mul,
    Verity.Core.Uint256.ofNat]
  exact Nat.mod_le _ _

private theorem uint256_div_mul_le_num (a b : Uint256) (hb : 0 < b.val) :
    (div a b).val * b.val ≤ a.val := by
  have hb_ne : b.val ≠ 0 := Nat.ne_of_gt hb
  have hq_lt : a.val / b.val < Verity.Core.Uint256.modulus := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self a.val b.val) a.isLt
  simp [Verity.EVM.Uint256.div, Verity.Core.Uint256.div, hb_ne,
    Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hq_lt]
  exact Nat.div_mul_le_self a.val b.val

private theorem uint256_min_le_left (a b : Uint256) :
    (Contracts.min a b).val ≤ a.val := by
  by_cases h : a ≤ b
  · simp [Contracts.min, h]
  · have hba : b.val ≤ a.val := by
      have h' : ¬ a.val ≤ b.val := by
        simpa [Verity.Core.Uint256.le_def] using h
      omega
    simpa [Contracts.min, h] using hba

private theorem uint256_min_le_right (a b : Uint256) :
    (Contracts.min a b).val ≤ b.val := by
  by_cases h : a ≤ b
  · have hab : a.val ≤ b.val := by
      simpa [Verity.Core.Uint256.le_def] using h
    simpa [Contracts.min, h] using hab
  · simp [Contracts.min, h]

private theorem finishFirstMint_success_value_eq
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 root
      liquidity newToBalance timestamp32 previousTimestamp minted : Uint256)
    (s : ContractState) (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.finishFirstMint toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
        root liquidity newToBalance timestamp32 previousTimestamp).run s →
    result = ContractResult.success minted result.snd →
      minted = liquidity := by
  intro h_run h_success
  subst h_run
  simp [UniswapV2PairBase.finishFirstMint,
    UniswapV2PairBase.updateReservesAndEmitSync, getStorage, getMapping,
    setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
    Contracts.rawLog, Contracts.mstore, Verity.Stdlib.Math.safeAdd,
    Verity.Stdlib.Math.requireSomeUint] at h_success
  repeat' (first
    | split at h_success
    | simp at h_success)
  all_goals
    rename_i _ value _ hmatch
    split at hmatch <;> simp at hmatch
    · exact h_success.symm.trans hmatch.1.symm

private theorem finishFirstMintChecked_success_value_eq
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 root
      timestamp32 previousTimestamp liquidity : Uint256)
    (s : ContractState) (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.finishFirstMintChecked toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
        root timestamp32 previousTimestamp).run s →
    result = ContractResult.success liquidity result.snd →
      liquidity = sub root minimumLiquidity := by
  intro h_run h_success
  subst h_run
  by_cases h_over : Verity.Stdlib.Math.MAX_UINT256 <
      (s.storageMap 9 toAddr).val + (sub root minimumLiquidity).val
  · simp [UniswapV2PairBase.finishFirstMintChecked, getStorage, getMapping,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind,
      Bind.bind, Verity.pure, Pure.pure, Verity.Stdlib.Math.safeAdd,
      Verity.Stdlib.Math.requireSomeUint, h_over] at h_success
    have h_tag := congrArg
      (fun r : ContractResult Uint256 =>
        match r with
        | ContractResult.success _ _ => true
        | ContractResult.revert _ _ => false) h_success
    simp at h_tag
    cases h_tag
  · cases h_finish :
        UniswapV2PairBase.finishFirstMint toAddr sender
          balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
          root (sub root minimumLiquidity)
          ((sub root minimumLiquidity) + s.storageMap 9 toAddr)
          timestamp32 previousTimestamp s <;>
      simp [UniswapV2PairBase.finishFirstMintChecked, getStorage, getMapping,
        Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Verity.Stdlib.Math.safeAdd,
        Verity.Stdlib.Math.requireSomeUint, h_over, h_finish] at h_success
    · have h_value := finishFirstMint_success_value_eq toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
        root (sub root minimumLiquidity)
        ((sub root minimumLiquidity) + s.storageMap 9 toAddr)
        timestamp32 previousTimestamp liquidity s
        ((UniswapV2PairBase.finishFirstMint toAddr sender
          balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
          root (sub root minimumLiquidity)
          ((sub root minimumLiquidity) + s.storageMap 9 toAddr)
          timestamp32 previousTimestamp).run s)
        rfl (by
          dsimp only [Contract.run]
          simpa [h_finish])
      exact h_value

private theorem finishLaterMint_success_value_eq_prefix
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      supply liquidity minted timestamp32 previousTimestamp : Uint256)
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
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind,
      Bind.bind, Verity.pure, Pure.pure, Verity.require,
      Verity.Stdlib.Math.safeAdd, Verity.Stdlib.Math.requireSomeUint,
      h_supply_over] at h_success
  · by_cases h_balance_over :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + liquidity.val
    · simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
        Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Verity.require,
        Verity.Stdlib.Math.safeAdd, Verity.Stdlib.Math.requireSomeUint,
        h_supply_over, h_balance_over] at h_success
    · simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
        setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
        Contracts.rawLog, Contracts.mstore, Verity.require,
        Verity.Stdlib.Math.safeAdd, Verity.Stdlib.Math.requireSomeUint,
        h_supply_over, h_balance_over] at h_success
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

theorem firstMintPath_success_implies_guards
    (toAddr sender : Address) (s : ContractState) (liquidity : Uint256)
    (final : ContractState) :
  (UniswapV2PairBase.firstMintPath toAddr sender
      (observedBalance0 s) (observedBalance1 s)
      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
      (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s) =
      ContractResult.success liquidity final →
    liquidity = mintFirstLiquidity s ∧
      (mintAmount0 s == 0 ||
        div (mintFirstProduct s) (mintAmount0 s) == mintAmount1 s) = true ∧
      mintFirstRoot s > minimumLiquidity := by
  intro h_success
  have h_product :
      (mintAmount0 s == 0 ||
        div (mintFirstProduct s) (mintAmount0 s) == mintAmount1 s) = true := by
    by_contra h_not
    have h_false :
        (mintAmount0 s == 0 ||
          div (mintFirstProduct s) (mintAmount0 s) == mintAmount1 s) = false :=
      Bool.eq_false_of_not_eq_true h_not
    have h_false_raw :
        (mintAmount0 s == 0 ||
          div (mul (mintAmount0 s) (mintAmount1 s))
            (mintAmount0 s) == mintAmount1 s) = false := by
      simpa [mintFirstProduct] using h_false
    simp only [UniswapV2PairBase.firstMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_false_raw, if_false, ContractResult.snd] at h_success
    cases h_success
  have h_root : mintFirstRoot s > minimumLiquidity := by
    by_contra h_not
    have h_root_false :
        decide (mintFirstRoot s > minimumLiquidity) = false := by
      simp [h_not]
    have h_product_raw :
        (mintAmount0 s == 0 ||
          div (mul (mintAmount0 s) (mintAmount1 s))
            (mintAmount0 s) == mintAmount1 s) = true := by
      simpa [mintFirstProduct] using h_product
    have h_root_false_raw :
        decide
            (sqrtValue (mul (mintAmount0 s) (mintAmount1 s)) (mintLockedState s) >
              UniswapV2PairBase.minimumLiquidity) = false := by
      simpa [mintFirstRoot, mintFirstProduct, minimumLiquidity,
        UniswapV2PairBase.minimumLiquidity] using h_root_false
    simp only [UniswapV2PairBase.firstMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_product_raw, if_true, sqrt_run_success_frames_state,
      h_root_false_raw, if_false, ContractResult.snd] at h_success
    cases h_success
  have h_liquidity : liquidity = mintFirstLiquidity s := by
    let checked :=
      (UniswapV2PairBase.finishFirstMintChecked toAddr sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s) (mintFirstRoot s)
        (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
        (if (5 == 11) = true then 0 else s.storage 5)).run
        (mintLockedState s)
    have h_product_raw :
        (mintAmount0 s == 0 ||
          div (mul (mintAmount0 s) (mintAmount1 s))
            (mintAmount0 s) == mintAmount1 s) = true := by
      simpa [mintFirstProduct] using h_product
    have h_root_guard :
        decide
            (sqrtValue (mul (mintAmount0 s) (mintAmount1 s)) (mintLockedState s) >
              UniswapV2PairBase.minimumLiquidity) = true := by
      simpa [mintFirstRoot, mintFirstProduct, minimumLiquidity,
        UniswapV2PairBase.minimumLiquidity] using h_root
    have h_path_reduced :
        (UniswapV2PairBase.firstMintPath toAddr sender
          (observedBalance0 s) (observedBalance1 s)
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s) = checked := by
      simp only [UniswapV2PairBase.firstMintPath, Contract.bind_pure_left,
        Contract.bind_pure_right]
      simp only [Contract.run, Verity.bind, Bind.bind]
      simp only [Verity.require, h_product_raw, if_true]
      simp only [sqrt_run_success_frames_state]
      simp only [h_root_guard, if_true]
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
            (observedBalance0 s) (observedBalance1 s)
            (s.storage 3) (s.storage 4)
            (mintAmount0 s) (mintAmount1 s)
            (sqrtValue (mul (mintAmount0 s) (mintAmount1 s))
              { s with «storage» := fun slotIdx =>
                  if (slotIdx == 11) = true then 0 else s.storage slotIdx })
            (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
            (if (5 == 11) = true then 0 else s.storage 5)
            { s with «storage» := fun slotIdx =>
                if (slotIdx == 11) = true then 0 else s.storage slotIdx } <;>
        simp only [h_finish]
    rw [h_path_reduced] at h_success
    have h_checked_success :
        checked = ContractResult.success liquidity checked.snd := by
      simpa [h_success] using h_success
    have h_value := finishFirstMintChecked_success_value_eq toAddr sender
      (observedBalance0 s) (observedBalance1 s)
      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
      (mintAmount0 s) (mintAmount1 s) (mintFirstRoot s)
      (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
      (if (5 == 11) = true then 0 else s.storage 5)
      liquidity (mintLockedState s) checked rfl h_checked_success
    simpa [mintFirstLiquidity] using h_value
  exact ⟨h_liquidity, h_product, h_root⟩

theorem laterMintPath_success_implies_guards
    (toAddr sender : Address) (s : ContractState) (liquidity totalSupply : Uint256)
    (final : ContractState) :
  totalSupply = s.storage totalSupplySlot.slot →
    0 < totalSupply.val →
      (UniswapV2PairBase.laterMintPath toAddr sender
          (observedBalance0 s) (observedBalance1 s)
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          (mintAmount0 s) (mintAmount1 s) totalSupply).run (mintLockedState s) =
          ContractResult.success liquidity final →
        0 < totalSupply.val ∧
          s.storage reserve0Slot.slot > 0 ∧
          s.storage reserve1Slot.slot > 0 ∧
          liquidity > 0 ∧
          liquidity.val * (s.storage reserve0Slot.slot).val ≤
            (mintAmount0 s).val * totalSupply.val ∧
          liquidity.val * (s.storage reserve1Slot.slot).val ≤
            (mintAmount1 s).val * totalSupply.val := by
  intro h_total h_supply_pos h_success
  subst totalSupply
  let liq0 :=
    div (mul (mintAmount0 s) (s.storage totalSupplySlot.slot))
      (s.storage reserve0Slot.slot)
  let liq1 :=
    div (mul (mintAmount1 s) (s.storage totalSupplySlot.slot))
      (s.storage reserve1Slot.slot)
  let computedLiquidity := Contracts.min liq0 liq1
  have h_reserve_guard :
      (s.storage reserve0Slot.slot > 0 &&
        s.storage reserve1Slot.slot > 0) = true := by
    by_contra h_not
    have h_false :
        (s.storage reserve0Slot.slot > 0 &&
          s.storage reserve1Slot.slot > 0) = false :=
      Bool.eq_false_of_not_eq_true h_not
    simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_false, if_false, ContractResult.snd] at h_success
    cases h_success
  have h_reserve_pos :
      s.storage reserve0Slot.slot > 0 ∧ s.storage reserve1Slot.slot > 0 := by
    simpa [Bool.and_eq_true] using h_reserve_guard
  have h_amount0_over :
      (mintAmount0 s == 0 ||
        div (mul (mintAmount0 s) (s.storage totalSupplySlot.slot))
          (mintAmount0 s) == s.storage totalSupplySlot.slot) = true := by
    by_contra h_not
    have h_false :
        (mintAmount0 s == 0 ||
          div (mul (mintAmount0 s) (s.storage totalSupplySlot.slot))
            (mintAmount0 s) == s.storage totalSupplySlot.slot) = false :=
      Bool.eq_false_of_not_eq_true h_not
    simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_reserve_guard, h_false, if_true, if_false,
      ContractResult.snd] at h_success
    cases h_success
  have h_amount1_over :
      (mintAmount1 s == 0 ||
        div (mul (mintAmount1 s) (s.storage totalSupplySlot.slot))
          (mintAmount1 s) == s.storage totalSupplySlot.slot) = true := by
    by_contra h_not
    have h_false :
        (mintAmount1 s == 0 ||
          div (mul (mintAmount1 s) (s.storage totalSupplySlot.slot))
            (mintAmount1 s) == s.storage totalSupplySlot.slot) = false :=
      Bool.eq_false_of_not_eq_true h_not
    simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_reserve_guard, h_amount0_over, h_false, if_true, if_false,
      ContractResult.snd] at h_success
    cases h_success
  have h_computed_guard : decide (computedLiquidity > 0) = true := by
    by_contra h_not
    have h_false : decide (computedLiquidity > 0) = false :=
      Bool.eq_false_of_not_eq_true h_not
    simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
      Contract.bind_pure_right, Contract.run, Verity.bind, Bind.bind,
      Verity.require, h_reserve_guard, h_amount0_over, h_amount1_over,
      if_true, computedLiquidity, liq0, liq1, h_false, if_false,
      ContractResult.snd] at h_success
    cases h_success
  have h_liquidity_eq : liquidity = computedLiquidity := by
    have h_path_reduced :
        (UniswapV2PairBase.laterMintPath toAddr sender
          (observedBalance0 s) (observedBalance1 s)
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          (mintAmount0 s) (mintAmount1 s)
          (s.storage totalSupplySlot.slot)).run (mintLockedState s) =
        (UniswapV2PairBase.finishLaterMint toAddr sender
          (observedBalance0 s) (observedBalance1 s)
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          (mintAmount0 s) (mintAmount1 s)
          (s.storage totalSupplySlot.slot) computedLiquidity
          (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else s.storage 5)).run
          (mintLockedState s) := by
      simp only [UniswapV2PairBase.laterMintPath, Contract.bind_pure_left,
        Contract.bind_pure_right]
      simp only [Contract.run, Verity.bind, Bind.bind]
      simp only [Verity.require, h_reserve_guard, h_amount0_over,
        h_amount1_over, if_true]
      simp only [Verity.require, computedLiquidity, liq0, liq1,
        h_computed_guard, if_true]
      simp only [Verity.blockTimestamp, getStorage]
      simp only [Verity.pure, Pure.pure, ContractResult.fst, ContractResult.snd]
      simp only [computedLiquidity, liq0, liq1, mintLockedState, timestamp32,
        reserve0Slot, reserve1Slot, totalSupplySlot, blockTimestampLastSlot,
        unlockedSlot, UniswapV2PairBase.reserve0Slot,
        UniswapV2PairBase.reserve1Slot, UniswapV2PairBase.totalSupplySlot,
        UniswapV2PairBase.blockTimestampLastSlot,
        UniswapV2PairBase.unlockedSlot]
      cases h_finish :
          UniswapV2PairBase.finishLaterMint toAddr sender
            (observedBalance0 s) (observedBalance1 s)
            (s.storage 3) (s.storage 4)
            (mintAmount0 s) (mintAmount1 s)
            (s.storage 8)
            (Contracts.min
              (div (mul (mintAmount0 s) (s.storage 8))
                (s.storage 3))
              (div (mul (mintAmount1 s) (s.storage 8))
                (s.storage 4)))
            (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
            (if (5 == 11) = true then 0 else s.storage 5)
            { s with «storage» := fun slotIdx =>
                if (slotIdx == 11) = true then 0 else s.storage slotIdx } <;>
        simp only [h_finish]
    have h_finish_success :
        (UniswapV2PairBase.finishLaterMint toAddr sender
          (observedBalance0 s) (observedBalance1 s)
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          (mintAmount0 s) (mintAmount1 s)
          (s.storage totalSupplySlot.slot) computedLiquidity
          (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else s.storage 5)).run
          (mintLockedState s) =
          ContractResult.success liquidity final := by
      rw [← h_path_reduced]
      exact h_success
    have h_finish_success_snd :
        (UniswapV2PairBase.finishLaterMint toAddr sender
          (observedBalance0 s) (observedBalance1 s)
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          (mintAmount0 s) (mintAmount1 s)
          (s.storage totalSupplySlot.slot) computedLiquidity
          (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else s.storage 5)).run
          (mintLockedState s) =
          ContractResult.success liquidity
            (((UniswapV2PairBase.finishLaterMint toAddr sender
              (observedBalance0 s) (observedBalance1 s)
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              (mintAmount0 s) (mintAmount1 s)
              (s.storage totalSupplySlot.slot) computedLiquidity
              (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
              (if (5 == 11) = true then 0 else s.storage 5)).run
              (mintLockedState s)).snd) := by
      rw [h_finish_success]
      rfl
    exact finishLaterMint_success_value_eq_prefix toAddr sender
      (observedBalance0 s) (observedBalance1 s)
      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
      (mintAmount0 s) (mintAmount1 s)
      (s.storage totalSupplySlot.slot) computedLiquidity
      liquidity (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
      (if (5 == 11) = true then 0 else s.storage 5)
      (mintLockedState s)
      ((UniswapV2PairBase.finishLaterMint toAddr sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s)
        (s.storage totalSupplySlot.slot) computedLiquidity
        (mod s.blockTimestamp UniswapV2PairBase.uint32Modulus)
        (if (5 == 11) = true then 0 else s.storage 5)).run
        (mintLockedState s))
      rfl h_finish_success_snd
  have h_liquidity_pos : liquidity > 0 := by
    subst liquidity
    simpa using h_computed_guard
  have h_ratio0 :
      liquidity.val * (s.storage reserve0Slot.slot).val ≤
        (mintAmount0 s).val * (s.storage totalSupplySlot.slot).val := by
    subst liquidity
    calc
      computedLiquidity.val * (s.storage reserve0Slot.slot).val ≤
          liq0.val * (s.storage reserve0Slot.slot).val := by
        exact Nat.mul_le_mul_right _ (uint256_min_le_left liq0 liq1)
      _ ≤ (mul (mintAmount0 s) (s.storage totalSupplySlot.slot)).val := by
        exact uint256_div_mul_le_num
          (mul (mintAmount0 s) (s.storage totalSupplySlot.slot))
          (s.storage reserve0Slot.slot) h_reserve_pos.1
      _ ≤ (mintAmount0 s).val * (s.storage totalSupplySlot.slot).val := by
        exact uint256_mul_val_le_nat_mul (mintAmount0 s)
          (s.storage totalSupplySlot.slot)
  have h_ratio1 :
      liquidity.val * (s.storage reserve1Slot.slot).val ≤
        (mintAmount1 s).val * (s.storage totalSupplySlot.slot).val := by
    subst liquidity
    calc
      computedLiquidity.val * (s.storage reserve1Slot.slot).val ≤
          liq1.val * (s.storage reserve1Slot.slot).val := by
        exact Nat.mul_le_mul_right _ (uint256_min_le_right liq0 liq1)
      _ ≤ (mul (mintAmount1 s) (s.storage totalSupplySlot.slot)).val := by
        exact uint256_div_mul_le_num
          (mul (mintAmount1 s) (s.storage totalSupplySlot.slot))
          (s.storage reserve1Slot.slot) h_reserve_pos.2
      _ ≤ (mintAmount1 s).val * (s.storage totalSupplySlot.slot).val := by
        exact uint256_mul_val_le_nat_mul (mintAmount1 s)
          (s.storage totalSupplySlot.slot)
  exact ⟨h_supply_pos, h_reserve_pos.1, h_reserve_pos.2, h_liquidity_pos,
    h_ratio0, h_ratio1⟩

theorem mint_success_implies_guards
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256)
    (liquidity : Uint256) :
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      mintAmount0 s > 0 ∧
      mintAmount1 s > 0 ∧
      (s.storage totalSupplySlot.slot = 0 →
        liquidity = mintFirstLiquidity s ∧
          (mintAmount0 s == 0 ||
            div (mintFirstProduct s) (mintAmount0 s) == mintAmount1 s) = true ∧
          mintFirstRoot s > minimumLiquidity) ∧
      (s.storage totalSupplySlot.slot ≠ 0 →
        0 < (s.storage totalSupplySlot.slot).val ∧
          s.storage reserve0Slot.slot > 0 ∧
          s.storage reserve1Slot.slot > 0 ∧
          liquidity > 0 ∧
          liquidity.val * (s.storage reserve0Slot.slot).val ≤
            (mintAmount0 s).val * (s.storage totalSupplySlot.slot).val ∧
          liquidity.val * (s.storage reserve1Slot.slot).val ≤
            (mintAmount1 s).val * (s.storage totalSupplySlot.slot).val) := by
  intro h_run h_success
  rcases mint_success_run_implies_prefix_guards
      toAddr s result liquidity h_run h_success with
    ⟨h_amount0, h_amount1, h_first_path, h_later_path⟩
  constructor
  · exact h_amount0
  constructor
  · exact h_amount1
  constructor
  · intro h_supply_zero
    exact firstMintPath_success_implies_guards toAddr s.sender s liquidity
      result.snd (h_first_path h_supply_zero)
  · intro h_supply_nonzero
    have h_supply_pos : 0 < (s.storage totalSupplySlot.slot).val := by
      simpa [Verity.Core.Uint256.lt_def] using
        uint256_pos_of_ne_zero h_supply_nonzero
    exact laterMintPath_success_implies_guards toAddr s.sender s liquidity
      (s.storage totalSupplySlot.slot) result.snd rfl h_supply_pos
      (h_later_path h_supply_nonzero)

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

theorem finishFirstMintChecked_success_run_lp_write
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 root
      timestamp32 previousTimestamp : Uint256)
    (s : ContractState) (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.finishFirstMintChecked toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
        root timestamp32 previousTimestamp).run s →
    result = ContractResult.success (sub root minimumLiquidity) result.snd →
      (result.snd.storageMap balancesSlot.slot toAddr).val =
        (s.storageMap balancesSlot.slot toAddr).val + (sub root minimumLiquidity).val := by
  intro h_run h_success
  subst h_run
  by_cases h_over : Verity.Stdlib.Math.MAX_UINT256 <
      (s.storageMap 9 toAddr).val + (sub root minimumLiquidity).val
  · simp [UniswapV2PairBase.finishFirstMintChecked, getStorage, getMapping,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Verity.Stdlib.Math.safeAdd,
      Verity.Stdlib.Math.requireSomeUint, h_over] at h_success
    cases h_success
  · have h_balance_ok :
        (s.storageMap balancesSlot.slot toAddr).val + (sub root minimumLiquidity).val ≤
          Verity.Stdlib.Math.MAX_UINT256 := by
      simpa [balancesSlot, gt_iff_lt] using h_over
    have h_add_val :
        (s.storageMap balancesSlot.slot toAddr + (sub root minimumLiquidity)).val =
          (s.storageMap balancesSlot.slot toAddr).val + (sub root minimumLiquidity).val := by
      have h_lt :
          (s.storageMap balancesSlot.slot toAddr).val + (sub root minimumLiquidity).val <
            Core.Uint256.modulus := by
        rw [← Core.Uint256.max_uint256_succ_eq_modulus]
        exact Nat.lt_succ_of_le h_balance_ok
      simpa using
        (Core.Uint256.add_eq_of_lt
          (a := s.storageMap balancesSlot.slot toAddr)
          (b := sub root minimumLiquidity) h_lt)
    have h_add_val_comm :
        ((sub root minimumLiquidity) + s.storageMap balancesSlot.slot toAddr).val =
          (s.storageMap balancesSlot.slot toAddr).val + (sub root minimumLiquidity).val := by
      have h_lt :
          (sub root minimumLiquidity).val + (s.storageMap balancesSlot.slot toAddr).val <
            Core.Uint256.modulus := by
        rw [Nat.add_comm]
        rw [← Core.Uint256.max_uint256_succ_eq_modulus]
        exact Nat.lt_succ_of_le h_balance_ok
      have h_val :=
        (Core.Uint256.add_eq_of_lt
          (a := sub root minimumLiquidity)
          (b := s.storageMap balancesSlot.slot toAddr) h_lt)
      simpa [Nat.add_comm] using h_val
    have h_add_val_comm_raw :
        ((sub root UniswapV2PairBase.minimumLiquidity) + s.storageMap 9 toAddr).val =
          (s.storageMap 9 toAddr).val + (sub root minimumLiquidity).val := by
      simpa [balancesSlot, minimumLiquidity, UniswapV2PairBase.minimumLiquidity]
        using h_add_val_comm
    have h_not_raw :
        ¬ Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 9 toAddr).val + (sub root minimumLiquidity).val := h_over
    simp [UniswapV2PairBase.finishFirstMintChecked,
      UniswapV2PairBase.finishFirstMint,
      UniswapV2PairBase.updateReservesAndEmitSync, getStorage, getMapping,
      setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
      ContractResult.fst, Contracts.rawLog, Contracts.mstore,
      Verity.Stdlib.Math.safeAdd, Verity.Stdlib.Math.requireSomeUint,
      h_not_raw, h_add_val, h_add_val_comm, h_add_val_comm_raw]
    all_goals (split_ifs <;> simp [getStorage, setStorage, setMapping, getMapping,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, emitEvent, Contracts.emit, Contracts.rawLog,
      Contracts.mstore, h_not_raw, h_add_val, h_add_val_comm, h_add_val_comm_raw])

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

theorem firstMintPath_run_lp_write
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
          (result.snd.storageMap balancesSlot.slot toAddr).val =
            ((mintLockedState original).storageMap balancesSlot.slot toAddr).val +
              (mintFirstLiquidity original).val := by
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
      have h_checked_lp :
          (checked.snd.storageMap balancesSlot.slot toAddr).val =
            ((mintLockedState original).storageMap balancesSlot.slot toAddr).val +
              (mintFirstLiquidity original).val := by
        simpa [mintFirstLiquidity] using
          finishFirstMintChecked_success_run_lp_write toAddr sender
            (observedBalance0 original) (observedBalance1 original)
            (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
            (mintAmount0 original) (mintAmount1 original) (mintFirstRoot original)
            (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
            (if (5 == 11) = true then 0 else original.storage 5)
            (mintLockedState original) checked rfl h_checked_success
      change (pathResult.snd.storageMap balancesSlot.slot toAddr).val =
        ((mintLockedState original).storageMap balancesSlot.slot toAddr).val +
          (mintFirstLiquidity original).val
      rw [h_path_reduced, h_checked_case]
      have h_checked_lp_post :
          (post.storageMap balancesSlot.slot toAddr).val =
            ((mintLockedState original).storageMap balancesSlot.slot toAddr).val +
              (mintFirstLiquidity original).val := by
        simpa only [h_checked_case, ContractResult.snd] using h_checked_lp
      simpa only [ContractResult.snd] using h_checked_lp_post
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

theorem finishLaterMint_success_run_lp_write
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      supply liquidity timestamp32 previousTimestamp : Uint256)
    (s : ContractState) (result : ContractResult Uint256) :
  result =
      (UniswapV2PairBase.finishLaterMint toAddr sender
        balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
        supply liquidity timestamp32 previousTimestamp).run s →
    result = ContractResult.success liquidity result.snd →
      (result.snd.storageMap balancesSlot.slot toAddr).val =
        (s.storageMap balancesSlot.slot toAddr).val + liquidity.val := by
  intro h_run h_success
  subst h_run
  by_cases h_supply_over : Verity.Stdlib.Math.MAX_UINT256 < supply.val + liquidity.val
  · simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Verity.require, Verity.Stdlib.Math.safeAdd,
      Verity.Stdlib.Math.requireSomeUint, h_supply_over] at h_success
  · by_cases h_balance_over :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + liquidity.val
    · simp [UniswapV2PairBase.finishLaterMint, getStorage, getMapping,
        Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Verity.require, Verity.Stdlib.Math.safeAdd,
        Verity.Stdlib.Math.requireSomeUint, h_supply_over, h_balance_over] at h_success
    · have h_balance_ok :
          (s.storageMap balancesSlot.slot toAddr).val + liquidity.val ≤
            Verity.Stdlib.Math.MAX_UINT256 := by
        simpa [balancesSlot, gt_iff_lt] using h_balance_over
      have h_add_val :
          (s.storageMap balancesSlot.slot toAddr + liquidity).val =
            (s.storageMap balancesSlot.slot toAddr).val + liquidity.val := by
        have h_lt :
            (s.storageMap balancesSlot.slot toAddr).val + liquidity.val <
              Core.Uint256.modulus := by
          rw [← Core.Uint256.max_uint256_succ_eq_modulus]
          exact Nat.lt_succ_of_le h_balance_ok
        simpa using
          (Core.Uint256.add_eq_of_lt
            (a := s.storageMap balancesSlot.slot toAddr) (b := liquidity) h_lt)
      have h_add_val_comm :
          (liquidity + s.storageMap balancesSlot.slot toAddr).val =
            (s.storageMap balancesSlot.slot toAddr).val + liquidity.val := by
        have h_lt :
            liquidity.val + (s.storageMap balancesSlot.slot toAddr).val <
              Core.Uint256.modulus := by
          rw [Nat.add_comm]
          rw [← Core.Uint256.max_uint256_succ_eq_modulus]
          exact Nat.lt_succ_of_le h_balance_ok
        have h_val :=
          (Core.Uint256.add_eq_of_lt
            (a := liquidity) (b := s.storageMap balancesSlot.slot toAddr) h_lt)
        simpa [Nat.add_comm] using h_val
      have h_add_val_comm_raw :
          (liquidity + s.storageMap 9 toAddr).val =
            (s.storageMap 9 toAddr).val + liquidity.val := by
        simpa [balancesSlot] using h_add_val_comm
      simp [UniswapV2PairBase.finishLaterMint,
        UniswapV2PairBase.updateReservesAndEmitSync, getStorage, getMapping,
        setStorage, setMapping, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        emitEvent, Contracts.emit, Contract.run, ContractResult.snd,
        ContractResult.fst, Contracts.rawLog, Contracts.mstore, Verity.Stdlib.Math.safeAdd,
        Verity.Stdlib.Math.requireSomeUint, h_supply_over, h_balance_over,
        h_add_val, h_add_val_comm, h_add_val_comm_raw]
      all_goals (split_ifs <;> simp [getStorage, setStorage, setMapping, getMapping,
        Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, emitEvent, Contracts.emit, Contracts.rawLog,
        Contracts.mstore, h_supply_over, h_balance_over, h_add_val,
        h_add_val_comm, h_add_val_comm_raw])

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

theorem laterMintPath_run_lp_write
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
                  (result.snd.storageMap balancesSlot.slot toAddr).val =
                    ((mintLockedState original).storageMap balancesSlot.slot toAddr).val +
                      liquidity.val := by
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
      have h_checked_lp :
          (checked.snd.storageMap balancesSlot.slot toAddr).val =
            ((mintLockedState original).storageMap balancesSlot.slot toAddr).val +
              computedLiquidity.val :=
        finishLaterMint_success_run_lp_write toAddr sender
          (observedBalance0 original) (observedBalance1 original)
          (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot)
          (mintAmount0 original) (mintAmount1 original)
          (original.storage totalSupplySlot.slot) computedLiquidity
          (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else original.storage 5)
          (mintLockedState original) checked rfl h_checked_success
      change (pathResult.snd.storageMap balancesSlot.slot toAddr).val =
        ((mintLockedState original).storageMap balancesSlot.slot toAddr).val +
          computedLiquidity.val
      rw [h_path_reduced, h_checked_case]
      have h_checked_lp_post :
          (post.storageMap balancesSlot.slot toAddr).val =
            ((mintLockedState original).storageMap balancesSlot.slot toAddr).val +
              computedLiquidity.val := by
        simpa only [h_checked_case, ContractResult.snd] using h_checked_lp
      simpa only [ContractResult.snd] using h_checked_lp_post
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

theorem mint_first_caller_lp_add
    (toAddr caller : Address) (s : ContractState) :
  toAddr = caller →
    (mint toAddr).run s =
      ContractResult.success (mintFirstLiquidity s) ((mint toAddr).run s).snd →
    s.storage totalSupplySlot.slot = 0 →
      s.storage reserve0Slot.slot ≤ observedBalance0 s →
        s.storage reserve1Slot.slot ≤ observedBalance1 s →
          mintAmount0 s > 0 →
            mintAmount1 s > 0 →
              (mintAmount0 s == 0 || div (mintFirstProduct s) (mintAmount0 s) == mintAmount1 s) = true →
                mintFirstRoot s > minimumLiquidity →
                  (((mint toAddr).run s).snd.storageMap balancesSlot.slot caller).val =
                    (s.storageMap balancesSlot.slot caller).val +
                      (mintFirstLiquidity s).val := by
  intro h_to h_success h_supply_zero h_reserve0 h_reserve1 h_amount0 h_amount1
    h_product h_root
  subst toAddr
  have h_path_eq :=
    mint_first_run_eq_path caller s h_success h_supply_zero h_reserve0
      h_reserve1 h_amount0 h_amount1 h_product h_root
  have h_path_success :
      (UniswapV2PairBase.firstMintPath caller s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s) =
        ContractResult.success (mintFirstLiquidity s)
          ((UniswapV2PairBase.firstMintPath caller s.sender
            (observedBalance0 s) (observedBalance1 s)
            (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
            (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s)).snd := by
    rw [← h_path_eq]
    exact h_success
  have h_lp :=
    firstMintPath_run_lp_write caller s.sender s
      ((UniswapV2PairBase.firstMintPath caller s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s)).run (mintLockedState s))
      rfl h_path_success h_product h_root
  rw [h_path_eq]
  simpa [mintLockedState_storageMap] using h_lp

theorem mint_later_caller_lp_add
    (toAddr caller : Address) (s : ContractState) (liquidity : Uint256) :
  toAddr = caller →
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
                    (((mint toAddr).run s).snd.storageMap balancesSlot.slot caller).val =
                      (s.storageMap balancesSlot.slot caller).val + liquidity.val := by
  intro h_to h_success h_supply_pos h_reserve0_pos h_reserve1_pos h_reserve0 h_reserve1
    h_amount0 h_amount1 h_liquidity
  subst toAddr
  have h_path_eq :=
    mint_later_run_eq_path caller s liquidity h_success h_supply_pos
      h_reserve0_pos h_reserve1_pos h_reserve0 h_reserve1 h_amount0
      h_amount1 h_liquidity
  have h_path_success :
      (UniswapV2PairBase.laterMintPath caller s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s)
        (s.storage totalSupplySlot.slot)).run (mintLockedState s) =
        ContractResult.success liquidity
          ((UniswapV2PairBase.laterMintPath caller s.sender
            (observedBalance0 s) (observedBalance1 s)
            (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
            (mintAmount0 s) (mintAmount1 s)
            (s.storage totalSupplySlot.slot)).run (mintLockedState s)).snd := by
    rw [← h_path_eq]
    exact h_success
  have h_lp :=
    laterMintPath_run_lp_write caller s.sender s liquidity
      ((UniswapV2PairBase.laterMintPath caller s.sender
        (observedBalance0 s) (observedBalance1 s)
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        (mintAmount0 s) (mintAmount1 s)
        (s.storage totalSupplySlot.slot)).run (mintLockedState s))
      rfl h_path_success h_supply_pos h_reserve0_pos h_reserve1_pos
      h_amount0 h_amount1 h_liquidity
  rw [h_path_eq]
  simpa [mintLockedState_storageMap] using h_lp

theorem mint_success_caller_lp_add
    (toAddr caller : Address) (s : ContractState) (liquidity : Uint256) :
  toAddr = caller →
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
                (((mint toAddr).run s).snd.storageMap balancesSlot.slot caller).val =
                  (s.storageMap balancesSlot.slot caller).val + liquidity.val := by
  intro h_to h_success h_reserve0 h_reserve1 h_amount0 h_amount1 h_first h_later
  by_cases h_supply_zero : s.storage totalSupplySlot.slot = 0
  · rcases h_first h_supply_zero with ⟨h_liquidity_first, h_product, h_root⟩
    have h_success_first :
        (mint toAddr).run s =
          ContractResult.success (mintFirstLiquidity s) ((mint toAddr).run s).snd := by
      simpa [h_liquidity_first] using h_success
    have h_lp :=
      mint_first_caller_lp_add toAddr caller s h_to h_success_first
        h_supply_zero h_reserve0 h_reserve1 h_amount0 h_amount1 h_product h_root
    simpa [h_liquidity_first] using h_lp
  · rcases h_later h_supply_zero with
      ⟨h_reserve0_pos, h_reserve1_pos, h_liquidity⟩
    have h_supply_pos : 0 < (s.storage totalSupplySlot.slot).val := by
      simpa [Verity.Core.Uint256.lt_def] using
        uint256_pos_of_ne_zero h_supply_zero
    exact mint_later_caller_lp_add toAddr caller s liquidity h_to h_success
      h_supply_pos h_reserve0_pos h_reserve1_pos h_reserve0 h_reserve1
      h_amount0 h_amount1 h_liquidity

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

private theorem contractPreservesStorageAddr_finishFirstMint
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      root liquidity newToBalance timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.finishFirstMint toAddr sender balance0Now balance1Now
        reserve0Value reserve1Value amount0 amount1 root liquidity newToBalance
        timestamp32 previousTimestamp) := by
  unfold UniswapV2PairBase.finishFirstMint
  repeat
    first
    | exact contractPreservesStorageAddr_updateReservesAndEmitSync _ _ _ _ _ _
    | exact contractPreservesStorageAddr_setStorage _ _
    | exact contractPreservesStorageAddr_setMapping _ _ _
    | exact contractPreservesStorageAddr_emit _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _

private theorem contractPreservesStorageAddr_finishFirstMintChecked
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      root timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.finishFirstMintChecked toAddr sender balance0Now balance1Now
        reserve0Value reserve1Value amount0 amount1 root timestamp32 previousTimestamp) := by
  unfold UniswapV2PairBase.finishFirstMintChecked
  repeat
    first
    | exact contractPreservesStorageAddr_getMapping _ _
    | exact contractPreservesStorageAddr_requireSomeUint _ _
    | exact contractPreservesStorageAddr_finishFirstMint _ _ _ _ _ _ _ _ _ _ _ _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _

private theorem contractPreservesStorageAddr_finishLaterMint
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      supply liquidity timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.finishLaterMint toAddr sender balance0Now balance1Now
        reserve0Value reserve1Value amount0 amount1 supply liquidity
        timestamp32 previousTimestamp) := by
  unfold UniswapV2PairBase.finishLaterMint
  repeat
    first
    | exact contractPreservesStorageAddr_updateReservesAndEmitSync _ _ _ _ _ _
    | exact contractPreservesStorageAddr_getMapping _ _
    | exact contractPreservesStorageAddr_requireSomeUint _ _
    | exact contractPreservesStorageAddr_setStorage _ _
    | exact contractPreservesStorageAddr_setMapping _ _ _
    | exact contractPreservesStorageAddr_emit _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _

private theorem contractPreservesStorageAddr_firstMintPath
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1 : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.firstMintPath toAddr sender balance0Now balance1Now
        reserve0Value reserve1Value amount0 amount1) := by
  unfold UniswapV2PairBase.firstMintPath
  repeat
    first
    | exact contractPreservesStorageAddr_require _ _
    | exact contractPreservesStorageAddr_sqrt _
    | exact contractPreservesStorageAddr_blockTimestamp
    | exact contractPreservesStorageAddr_getStorage _
    | exact contractPreservesStorageAddr_finishFirstMintChecked _ _ _ _ _ _ _ _ _ _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _

private theorem contractPreservesStorageAddr_laterMintPath
    (toAddr sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value amount0 amount1
      supply : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.laterMintPath toAddr sender balance0Now balance1Now
        reserve0Value reserve1Value amount0 amount1 supply) := by
  unfold UniswapV2PairBase.laterMintPath
  repeat
    first
    | exact contractPreservesStorageAddr_require _ _
    | exact contractPreservesStorageAddr_blockTimestamp
    | exact contractPreservesStorageAddr_getStorage _
    | exact contractPreservesStorageAddr_finishLaterMint _ _ _ _ _ _ _ _ _ _ _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _

private theorem contractPreservesStorageAddr_mint (toAddr : Address) :
    contractPreservesStorageAddr (mint toAddr) := by
  unfold mint UniswapV2PairBase.mint
  repeat
    first
    | exact contractPreservesStorageAddr_getStorage _
    | exact contractPreservesStorageAddr_getStorageAddr _
    | exact contractPreservesStorageAddr_require _ _
    | exact contractPreservesStorageAddr_setStorage _ _
    | exact contractPreservesStorageAddr_msgSender
    | exact contractPreservesStorageAddr_contractAddress
    | exact contractPreservesStorageAddr_erc20BalanceOf _ _
    | exact contractPreservesStorageAddr_firstMintPath _ _ _ _ _ _ _ _
    | exact contractPreservesStorageAddr_laterMintPath _ _ _ _ _ _ _ _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _
    | split_ifs

theorem mint_run_storageAddr_frame
    (toAddr : Address) (s : ContractState) (i : Nat) :
  ((mint toAddr).run s).snd.storageAddr i = s.storageAddr i :=
  contractPreservesStorageAddr_run_snd (mint toAddr)
    (contractPreservesStorageAddr_mint toAddr) s i


end TamaUniV2.Proof.UniswapV2PairProof
