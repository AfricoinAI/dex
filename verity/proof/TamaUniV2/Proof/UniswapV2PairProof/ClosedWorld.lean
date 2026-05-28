-- SPDX-License-Identifier: AGPL-3.0-only
import TamaUniV2.Proof.UniswapV2PairProof.Bridges

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

theorem pairWorldStep_preserves_good
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldStep action before after →
      PairWorldGood after := by
  intro h_good h_step
  cases action <;>
    simp [PairWorldStep, PairWorldMintStep, PairWorldBurnStep, PairWorldSwapStep,
      PairWorldSkimStep, PairWorldSyncStep] at h_step
  · subst after
    exact h_good
  · subst after
    exact h_good
  · subst after
    exact h_good
  · rcases h_good with ⟨h_back0, h_back1, h_bound0, h_bound1, h_supply⟩
    rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
      h_supply_eq, h_locked_eq⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h_reserve0, h_balance0]
      omega
    · rw [h_reserve1, h_balance1]
      omega
    · rw [h_reserve0]
      exact h_bound0
    · rw [h_reserve1]
      exact h_bound1
    · simpa [PairWorldSupplyGood, h_supply_eq, h_locked_eq] using h_supply
  · rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
    rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity,
      _h_before_balance0, _h_before_balance1, h_after_balance0, h_after_balance1,
      h_after_reserve0, h_after_reserve1, h_bound0, h_bound1, h_supply_eq,
      h_locked_eq, _h_ratio⟩
    refine ⟨?_, ?_, h_bound0, h_bound1, ?_⟩
    · rw [h_after_reserve0, h_after_balance0]
    · rw [h_after_reserve1, h_after_balance1]
    · by_cases h_zero : before.totalSupply = 0
      · right
        rw [h_supply_eq, h_locked_eq]
        simp [h_zero, minimumLiquidityNat]
      · rcases h_supply with h_empty | h_nonzero
        · exact False.elim (h_zero h_empty.1)
        · rcases h_nonzero with ⟨h_positive, h_locked, h_min⟩
          have h_min_raw : 1000 ≤ before.totalSupply := by
            simpa [minimumLiquidityNat] using h_min
          right
          rw [h_supply_eq, h_locked_eq]
          simp [h_zero, h_locked, minimumLiquidityNat]
          omega
  · rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
    rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      h_supply_pos, _h_amount0_le, _h_amount1_le, h_liquidity_le,
      h_locked_remaining, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
      h_bound0, h_bound1, h_supply_eq, h_locked_eq, _h_ratio0, _h_ratio1⟩
    refine ⟨?_, ?_, h_bound0, h_bound1, ?_⟩
    · rw [h_reserve0]
    · rw [h_reserve1]
    · rcases h_supply with h_empty | h_nonzero
      · exact False.elim (Nat.ne_of_gt h_supply_pos h_empty.1)
      · rcases h_nonzero with ⟨_h_positive, h_locked, _h_min⟩
        right
        rw [h_supply_eq, h_locked_eq]
        constructor
        · rw [h_locked] at h_locked_remaining
          simp [minimumLiquidityNat] at h_locked_remaining
          omega
        · constructor
          · exact h_locked
          · rw [h_locked] at h_locked_remaining
            exact h_locked_remaining
  · rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
    rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
      _h_input, _h_balance0, _h_balance1, h_reserve0, h_reserve1, h_bound0,
      h_bound1, h_supply_eq, h_locked_eq, _h_fee0, _h_fee1, _h_k⟩
    refine ⟨?_, ?_, h_bound0, h_bound1, ?_⟩
    · rw [h_reserve0]
    · rw [h_reserve1]
    · simpa [PairWorldSupplyGood, h_supply_eq, h_locked_eq] using h_supply
  · rcases h_good with ⟨_h_back0, _h_back1, h_bound0, h_bound1, h_supply⟩
    rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
      h_supply_eq, h_locked_eq⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h_reserve0, h_balance0]
    · rw [h_reserve1, h_balance1]
    · rw [h_reserve0]
      exact h_bound0
    · rw [h_reserve1]
      exact h_bound1
    · simpa [PairWorldSupplyGood, h_supply_eq, h_locked_eq] using h_supply
  · rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
    rcases h_step with ⟨h_bound0, h_bound1, h_balance0, h_balance1,
      h_reserve0, h_reserve1, h_supply_eq, h_locked_eq⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h_reserve0, h_balance0]
    · rw [h_reserve1, h_balance1]
    · rw [h_reserve0]
      exact h_bound0
    · rw [h_reserve1]
      exact h_bound1
    · simpa [PairWorldSupplyGood, h_supply_eq, h_locked_eq] using h_supply

theorem pairWorldReachable_good
    (w : PairWorldState) :
  PairWorldReachable w → PairWorldGood w := by
  intro h_reachable
  induction h_reachable with
  | init =>
      simp [PairWorldInitial, PairWorldGood, PairWorldSupplyGood,
        minimumLiquidityNat, maxUint112Nat]
  | step action h_before h_step ih =>
      exact pairWorldStep_preserves_good ih h_step

theorem pairWorldPath_preserves_good
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPath before after →
      PairWorldGood after := by
  intro h_good h_path
  revert h_good
  induction h_path with
  | refl =>
      intro h_good
      exact h_good
  | step action h_prefix h_step ih =>
      intro h_good
      exact pairWorldStep_preserves_good (ih h_good) h_step

theorem pairWorldPath_preserves_reachability
    {before after : PairWorldState} :
  PairWorldReachable before →
    PairWorldPath before after →
      PairWorldReachable after := by
  intro h_reachable h_path
  induction h_path with
  | refl =>
      exact h_reachable
  | step action h_prefix h_step ih =>
      exact PairWorldReachable.step action ih h_step

theorem pairWorldPath_of_noBurn
    {before after : PairWorldState} :
  PairWorldPathNoBurn before after →
    PairWorldPath before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWorldPath.refl before
  | step action h_prefix h_step _h_not_burn ih =>
      exact PairWorldPath.step action ih h_step

theorem pairWorldPath_of_noMintBurn
    {before after : PairWorldState} :
  PairWorldPathNoMintBurn before after →
    PairWorldPath before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWorldPath.refl before
  | step action h_prefix h_step _h_not_mint _h_not_burn ih =>
      exact PairWorldPath.step action ih h_step

theorem pairWorldPath_of_noDonation
    {before after : PairWorldState} :
  PairWorldPathNoDonation before after →
    PairWorldPath before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWorldPath.refl before
  | step action h_prefix h_step _h_not_donation ih =>
      exact PairWorldPath.step action ih h_step

theorem pairWorldNoBurnPath_of_noMintBurn
    {before after : PairWorldState} :
  PairWorldPathNoMintBurn before after →
    PairWorldPathNoBurn before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWorldPathNoBurn.refl before
  | step action h_prefix h_step _h_not_mint h_not_burn ih =>
      exact PairWorldPathNoBurn.step action ih h_step h_not_burn

theorem pairWorldNoMintBurnPath_preserves_supply
    {before after : PairWorldState} :
  PairWorldPathNoMintBurn before after →
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity := by
  intro h_path
  induction h_path with
  | refl =>
      exact ⟨rfl, rfl⟩
  | step action h_prefix h_step h_not_mint h_not_burn ih =>
      cases action with
      | approve ownerAddr spender amount =>
          simp [PairWorldStep] at h_step
          rw [h_step]
          exact ih
      | transfer fromAddr toAddr amount =>
          simp [PairWorldStep] at h_step
          rw [h_step]
          exact ih
      | transferFrom spender fromAddr toAddr amount =>
          simp [PairWorldStep] at h_step
          rw [h_step]
          exact ih
      | donate amount0 amount1 =>
          simp [PairWorldStep] at h_step
          rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, h_supply, h_locked⟩
          exact ⟨h_supply.trans ih.1, h_locked.trans ih.2⟩
      | mint amount0 amount1 liquidity =>
          exact False.elim (h_not_mint amount0 amount1 liquidity rfl)
      | burn amount0 amount1 liquidity =>
          exact False.elim (h_not_burn amount0 amount1 liquidity rfl)
      | swap amount0In amount1In amount0Out amount1Out =>
          simp [PairWorldStep, PairWorldSwapStep] at h_step
          rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
            _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, _h_bound0, _h_bound1, h_supply, h_locked, _h_fee0,
            _h_fee1, _h_adjusted_k⟩
          exact ⟨h_supply.trans ih.1, h_locked.trans ih.2⟩
      | skim =>
          simp [PairWorldStep, PairWorldSkimStep] at h_step
          rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, h_supply, h_locked⟩
          exact ⟨h_supply.trans ih.1, h_locked.trans ih.2⟩
      | sync =>
          simp [PairWorldStep, PairWorldSyncStep] at h_step
          rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
            _h_reserve0, _h_reserve1, h_supply, h_locked⟩
          exact ⟨h_supply.trans ih.1, h_locked.trans ih.2⟩

theorem pairWorldNonBurnStep_never_decreases_supply
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      before.totalSupply ≤ after.totalSupply := by
  intro h_step h_not_burn
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_before_balance0, _h_before_balance1, _h_after_balance0,
        _h_after_balance1, _h_after_reserve0, _h_after_reserve1, _h_bound0,
        _h_bound1, h_supply, _h_locked, _h_ratio⟩
      by_cases h_zero : before.totalSupply = 0
      · rw [h_supply, if_pos h_zero, h_zero]
        exact Nat.zero_le _
      · rw [h_supply, if_neg h_zero]
        exact Nat.le_add_right before.totalSupply liquidity
  | burn amount0 amount1 liquidity =>
      exact False.elim (h_not_burn amount0 amount1 liquidity rfl)
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
        _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0,
        _h_fee1, _h_adjusted_k⟩
      rw [h_supply]
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
      rw [h_supply]

theorem pairWorldNoBurnPath_never_decreases_supply
    {before after : PairWorldState} :
  PairWorldPathNoBurn before after →
    before.totalSupply ≤ after.totalSupply := by
  intro h_path
  induction h_path with
  | refl =>
      rfl
  | step action h_prefix h_step h_not_burn ih =>
      exact Nat.le_trans ih
        (pairWorldNonBurnStep_never_decreases_supply h_step h_not_burn)

theorem pairWorldNonMintStep_never_increases_supply
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
      after.totalSupply ≤ before.totalSupply := by
  intro h_step h_not_mint
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
  | mint amount0 amount1 liquidity =>
      exact False.elim (h_not_mint amount0 amount1 liquidity rfl)
  | burn amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liquidity_le,
        _h_locked_remaining, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_ratio0,
        _h_ratio1⟩
      rw [h_supply]
      exact Nat.sub_le before.totalSupply liquidity
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
        _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0,
        _h_fee1, _h_adjusted_k⟩
      rw [h_supply]
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
      rw [h_supply]

theorem pairWorldNoMintPath_never_increases_supply
    {before after : PairWorldState} :
  PairWorldPathNoMint before after →
    after.totalSupply ≤ before.totalSupply := by
  intro h_path
  induction h_path with
  | refl =>
      rfl
  | step action h_prefix h_step h_not_mint ih =>
      exact Nat.le_trans
        (pairWorldNonMintStep_never_increases_supply h_step h_not_mint)
        ih

theorem pairWorldStep_locked_liquidity_never_decreases
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldStep action before after →
      before.lockedLiquidity ≤ after.lockedLiquidity := by
  intro h_good h_step
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        _h_supply, h_locked⟩
      rw [h_locked]
  | mint amount0 amount1 liquidity =>
      rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1,
        h_supply_good⟩
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_before_balance0, _h_before_balance1, _h_after_balance0,
        _h_after_balance1, _h_after_reserve0, _h_after_reserve1, _h_bound0,
        _h_bound1, _h_supply, h_locked, _h_ratio⟩
      by_cases h_zero : before.totalSupply = 0
      · have h_locked_before : before.lockedLiquidity = 0 := by
          rcases h_supply_good with h_empty | h_nonempty
          · exact h_empty.2
          · exact False.elim ((Nat.ne_of_gt h_nonempty.1) h_zero)
        rw [h_locked_before, h_locked, if_pos h_zero]
        exact Nat.zero_le _
      · rw [h_locked, if_neg h_zero]
  | burn amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liquidity_le,
        _h_locked_remaining, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, _h_supply, h_locked, _h_ratio0,
        _h_ratio1⟩
      rw [h_locked]
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
        _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, _h_supply, h_locked, _h_fee0,
        _h_fee1, _h_adjusted_k⟩
      rw [h_locked]
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        _h_supply, h_locked⟩
      rw [h_locked]
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, _h_supply, h_locked⟩
      rw [h_locked]

theorem pairWorldPath_locked_liquidity_never_decreases
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPath before after →
      before.lockedLiquidity ≤ after.lockedLiquidity := by
  intro h_good h_path
  revert h_good
  induction h_path with
  | refl =>
      intro _h_good
      rfl
  | step action h_prefix h_step ih =>
      intro h_good
      have h_good_before := pairWorldPath_preserves_good h_good h_prefix
      exact Nat.le_trans
        (ih h_good)
        (pairWorldStep_locked_liquidity_never_decreases h_good_before h_step)

theorem pairWorldNonBurnStep_never_decreases_k
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
        PairWorldK before ≤ PairWorldK after := by
  intro h_good h_step h_not_burn
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      unfold PairWorldK
      rw [h_reserve0, h_reserve1]
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        h_before_balance0, h_before_balance1, h_after_balance0, h_after_balance1,
        h_after_reserve0, h_after_reserve1, _h_bound0, _h_bound1, _h_supply,
        _h_locked, _h_ratio⟩
      unfold PairWorldK
      rw [h_after_reserve0, h_after_reserve1]
      have h0 : before.reserve0 ≤ before.balance0 := by
        rw [h_before_balance0]
        omega
      have h1 : before.reserve1 ≤ before.balance1 := by
        rw [h_before_balance1]
        omega
      exact Nat.mul_le_mul h0 h1
  | burn amount0 amount1 liquidity =>
      exact False.elim (h_not_burn amount0 amount1 liquidity rfl)
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
        _h_input, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1,
        h_adjusted_k⟩
      exact feeAdjustedSwap_implies_raw_k
        amount0In amount1In before after h_reserve0 h_reserve1 h_adjusted_k
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      unfold PairWorldK
      rw [h_reserve0, h_reserve1]
  | sync =>
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1,
        _h_supply_good⟩
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        h_reserve0, h_reserve1, _h_supply, _h_locked⟩
      unfold PairWorldK
      rw [h_reserve0, h_reserve1]
      exact Nat.mul_le_mul h_back0 h_back1

theorem pairWorldNoBurnPath_never_decreases_k
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPathNoBurn before after →
      PairWorldK before ≤ PairWorldK after := by
  intro h_good h_path
  revert h_good
  induction h_path with
  | refl =>
      intro _h_good
      rfl
  | step action h_prefix h_step h_not_burn ih =>
      intro h_good
      have h_good_before :=
        pairWorldPath_preserves_good h_good
          (pairWorldPath_of_noBurn h_prefix)
      exact Nat.le_trans
        (ih h_good)
        (pairWorldNonBurnStep_never_decreases_k
          h_good_before h_step h_not_burn)

theorem pairWorldStep_positive_supply_preserved
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep action before after →
        0 < after.totalSupply := by
  intro h_good h_positive h_step
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact h_positive
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact h_positive
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact h_positive
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
      exact h_positive
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity, _h_before_balance0,
        _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
        _h_after_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_ratio⟩
      by_cases h_zero : before.totalSupply = 0
      · exact False.elim (Nat.ne_of_gt h_positive h_zero)
      · rw [h_supply]
        simp [h_zero]
        omega
  | burn amount0 amount1 liquidity =>
      rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply_good⟩
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
        _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, h_locked_remaining,
        _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
        h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
      rcases h_supply_good with h_empty | h_nonempty
      · exact False.elim (Nat.ne_of_gt h_positive h_empty.1)
      · rcases h_nonempty with ⟨_h_supply_pos, h_locked, _h_min⟩
        rw [h_supply]
        rw [h_locked] at h_locked_remaining
        simp [minimumLiquidityNat] at h_locked_remaining
        omega
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
        _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0, _h_fee1,
        _h_adjusted_k⟩
      rw [h_supply]
      exact h_positive
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
      exact h_positive
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
      rw [h_supply]
      exact h_positive

theorem pairWorldPath_positive_supply_preserved
    {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        0 < after.totalSupply := by
  intro h_good h_positive h_path
  induction h_path with
  | refl =>
      exact h_positive
  | step action h_prefix h_step ih =>
      have h_good_before := pairWorldPath_preserves_good h_good h_prefix
      exact pairWorldStep_positive_supply_preserved h_good_before ih h_step

theorem pairWorldStep_k_per_supply_never_decreases
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep action before after →
        PairWorldKPerSupplyNondecreasing before after := by
  intro h_good h_positive h_step
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      unfold PairWorldKPerSupplyNondecreasing
      rfl
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      unfold PairWorldKPerSupplyNondecreasing
      rfl
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      unfold PairWorldKPerSupplyNondecreasing
      rfl
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        h_supply, _h_locked⟩
      unfold PairWorldKPerSupplyNondecreasing PairWorldK
      rw [h_reserve0, h_reserve1, h_supply]
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, h_before_balance0,
        h_before_balance1, h_after_balance0, h_after_balance1, h_after_reserve0,
        h_after_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, h_ratio⟩
      by_cases h_zero : before.totalSupply = 0
      · exact False.elim (Nat.ne_of_gt h_positive h_zero)
      · rcases h_ratio with h_first | h_ratio
        · exact False.elim (h_zero h_first)
        · have h_supply' :
              after.totalSupply = before.totalSupply + liquidity := by
            simpa [h_zero] using h_supply
          have h_reserve0' :
              after.reserve0 = before.reserve0 + amount0 := by
            rw [h_after_reserve0, h_before_balance0]
          have h_reserve1' :
              after.reserve1 = before.reserve1 + amount1 := by
            rw [h_after_reserve1, h_before_balance1]
          have h0 :
              before.reserve0 * after.totalSupply ≤
                after.reserve0 * before.totalSupply := by
            rw [h_supply', h_reserve0']
            nlinarith [h_ratio.1]
          have h1 :
              before.reserve1 * after.totalSupply ≤
                after.reserve1 * before.totalSupply := by
            rw [h_supply', h_reserve1']
            nlinarith [h_ratio.2]
          have h_mul := Nat.mul_le_mul h0 h1
          unfold PairWorldKPerSupplyNondecreasing PairWorldK
          nlinarith [h_mul]
  | burn amount0 amount1 liquidity =>
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
        _h_supply_pos, h_amount0, h_amount1, h_liquidity, _h_locked_remaining,
        h_balance0, h_balance1, h_reserve0, h_reserve1, _h_bound0, _h_bound1,
        h_supply, _h_locked, h_ratio0, h_ratio1⟩
      have h_after0 :
          after.reserve0 = before.balance0 - amount0 := by
        rw [h_reserve0, h_balance0]
      have h_after1 :
          after.reserve1 = before.balance1 - amount1 := by
        rw [h_reserve1, h_balance1]
      have h0_balance :
          before.balance0 * (before.totalSupply - liquidity) ≤
            (before.balance0 - amount0) * before.totalSupply := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.sub_le_sub_left h_ratio0 (before.balance0 * before.totalSupply)
      have h1_balance :
          before.balance1 * (before.totalSupply - liquidity) ≤
            (before.balance1 - amount1) * before.totalSupply := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.sub_le_sub_left h_ratio1 (before.balance1 * before.totalSupply)
      have h0 :
          before.reserve0 * after.totalSupply ≤
            after.reserve0 * before.totalSupply := by
        rw [h_supply, h_after0]
        exact Nat.le_trans (Nat.mul_le_mul_right _ h_back0) h0_balance
      have h1 :
          before.reserve1 * after.totalSupply ≤
            after.reserve1 * before.totalSupply := by
        rw [h_supply, h_after1]
        exact Nat.le_trans (Nat.mul_le_mul_right _ h_back1) h1_balance
      have h_mul := Nat.mul_le_mul h0 h1
      unfold PairWorldKPerSupplyNondecreasing PairWorldK
      nlinarith [h_mul]
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
        _h_input, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0, _h_fee1,
        h_adjusted_k⟩
      have h_raw_k :
          PairWorldK before ≤ PairWorldK after :=
        feeAdjustedSwap_implies_raw_k
          amount0In amount1In before after h_reserve0 h_reserve1 h_adjusted_k
      unfold PairWorldKPerSupplyNondecreasing
      rw [h_supply]
      exact Nat.mul_le_mul_right before.totalSupply
        (Nat.mul_le_mul_right before.totalSupply h_raw_k)
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        h_supply, _h_locked⟩
      unfold PairWorldKPerSupplyNondecreasing PairWorldK
      rw [h_reserve0, h_reserve1, h_supply]
  | sync =>
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1,
        _h_supply_good⟩
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        h_reserve0, h_reserve1, h_supply, _h_locked⟩
      have h_k : PairWorldK before ≤ PairWorldK after := by
        unfold PairWorldK
        rw [h_reserve0, h_reserve1]
        exact Nat.mul_le_mul h_back0 h_back1
      unfold PairWorldKPerSupplyNondecreasing
      rw [h_supply]
      exact Nat.mul_le_mul_right before.totalSupply
        (Nat.mul_le_mul_right before.totalSupply h_k)

theorem pairWorldPath_k_per_supply_never_decreases
    {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        PairWorldKPerSupplyNondecreasing before after := by
  intro h_good h_positive h_path
  revert h_good h_positive
  induction h_path with
  | refl =>
      intro h_good h_positive
      unfold PairWorldKPerSupplyNondecreasing
      rfl
  | step action h_prefix h_step ih =>
      rename_i mid last
      intro h_good h_positive
      have h_good_mid := pairWorldPath_preserves_good h_good h_prefix
      have h_positive_mid :=
        pairWorldPath_positive_supply_preserved h_good h_positive h_prefix
      have h_prefix_scaled := ih h_good h_positive
      have h_step_scaled :=
        pairWorldStep_k_per_supply_never_decreases
          h_good_mid h_positive_mid h_step
      have h_mid_sq_pos := Nat.mul_pos h_positive_mid h_positive_mid
      have h_prefix_mul :=
        Nat.mul_le_mul_right (last.totalSupply * last.totalSupply) h_prefix_scaled
      have h_step_mul :=
        Nat.mul_le_mul_right (before.totalSupply * before.totalSupply) h_step_scaled
      unfold PairWorldKPerSupplyNondecreasing at *
      nlinarith [h_prefix_mul, h_step_mul, h_mid_sq_pos]

theorem pairWorldSameSupplyPath_never_decreases_k
    {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldK before ≤ PairWorldK after := by
  intro h_good h_positive h_path h_supply
  have h_scaled :=
    pairWorldPath_k_per_supply_never_decreases h_good h_positive h_path
  unfold PairWorldKPerSupplyNondecreasing at h_scaled
  rw [← h_supply] at h_scaled
  have h_scaled' :
      PairWorldK before * (before.totalSupply * before.totalSupply) ≤
        PairWorldK after * (before.totalSupply * before.totalSupply) := by
    simpa [Nat.mul_assoc] using h_scaled
  exact Nat.le_of_mul_le_mul_right h_scaled'
    (Nat.mul_pos h_positive h_positive)

def pair_closed_world_step_preserves_good
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      PairWorldGood after

theorem closed_world_step_preserves_good
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_step_preserves_good action before after := by
  exact pairWorldStep_preserves_good

-- tama: discharges=pair_closed_world_path_preserves_good
theorem closed_world_path_preserves_good
    (before after : PairWorldState) :
  pair_closed_world_path_preserves_good before after := by
  exact pairWorldPath_preserves_good


-- tama: discharges=pair_closed_world_reachable_path_good
theorem closed_world_reachable_path_good
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_good before after := by
  intro h_reachable h_path
  exact pairWorldPath_preserves_good
    (pairWorldReachable_good before h_reachable)
    h_path

-- tama: discharges=pair_closed_world_path_preserves_reachability
theorem closed_world_path_preserves_reachability
    (before after : PairWorldState) :
  pair_closed_world_path_preserves_reachability before after := by
  exact pairWorldPath_preserves_reachability







-- tama: discharges=pair_concrete_state_reserves_backed
theorem concrete_state_reserves_backed (s : ContractState) :
  pair_concrete_state_reserves_backed s := by
  intro h_good
  rcases h_good with ⟨h0, h1, _h1120, _h1121, _hsupply⟩
  exact ⟨h0, h1⟩

-- tama: discharges=pair_concrete_state_uint112_reserves
theorem concrete_state_uint112_reserves (s : ContractState) :
  pair_concrete_state_uint112_reserves s := by
  intro h_good
  rcases h_good with ⟨_h0, _h1, h1120, h1121, _hsupply⟩
  exact ⟨h1120, h1121⟩



-- tama: discharges=pair_closed_world_reachable_path_reserves_backed
theorem closed_world_reachable_path_reserves_backed
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_reserves_backed before after := by
  intro h_reachable h_path
  rcases pairWorldPath_preserves_good
      (pairWorldReachable_good before h_reachable) h_path with
    ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  exact ⟨h_back0, h_back1⟩

-- tama: discharges=pair_closed_world_reachable_path_reserves_fit_uint112
theorem closed_world_reachable_path_reserves_fit_uint112
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_reserves_fit_uint112 before after := by
  intro h_reachable h_path
  rcases pairWorldPath_preserves_good
      (pairWorldReachable_good before h_reachable) h_path with
    ⟨_h_back0, _h_back1, h_bound0, h_bound1, _h_supply⟩
  exact ⟨h_bound0, h_bound1⟩


-- tama: discharges=pair_closed_world_nonzero_supply_locks_minimum_liquidity
theorem closed_world_nonzero_supply_locks_minimum_liquidity
    (w : PairWorldState) :
  pair_closed_world_nonzero_supply_locks_minimum_liquidity w := by
  intro h_reachable h_nonzero
  rcases pairWorldReachable_good w h_reachable with
    ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
  rcases h_supply with h_empty | h_nonempty
  · exact False.elim (h_nonzero h_empty.1)
  · rcases h_nonempty with ⟨_h_positive, h_locked, h_min⟩
    exact ⟨h_locked, h_min⟩

-- tama: discharges=pair_closed_world_zero_supply_has_no_locked_liquidity
theorem closed_world_zero_supply_has_no_locked_liquidity
    (w : PairWorldState) :
  pair_closed_world_zero_supply_has_no_locked_liquidity w := by
  intro h_reachable h_zero_supply
  rcases pairWorldReachable_good w h_reachable with
    ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
  rcases h_supply with h_empty | h_nonempty
  · exact h_empty.2
  · rcases h_nonempty with ⟨h_positive, _h_locked, _h_min⟩
    have h_positive_zero : 0 < 0 := by
      simp [h_zero_supply] at h_positive
    exact False.elim ((Nat.lt_irrefl 0) h_positive_zero)

-- tama: discharges=pair_closed_world_locked_liquidity_never_exceeds_supply
theorem closed_world_locked_liquidity_never_exceeds_supply
    (w : PairWorldState) :
  pair_closed_world_locked_liquidity_never_exceeds_supply w := by
  intro h_reachable
  rcases pairWorldReachable_good w h_reachable with
    ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
  rcases h_supply with h_empty | h_nonempty
  · rcases h_empty with ⟨h_supply_zero, h_locked_zero⟩
    rw [h_supply_zero, h_locked_zero]
  · rcases h_nonempty with ⟨_h_positive, h_locked, h_min⟩
    rw [h_locked]
    exact h_min

-- tama: discharges=pair_closed_world_reachable_path_minimum_liquidity_lock
theorem closed_world_reachable_path_minimum_liquidity_lock
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_minimum_liquidity_lock before after := by
  intro h_reachable h_path
  exact (pairWorldPath_preserves_good
    (pairWorldReachable_good before h_reachable) h_path).2.2.2.2


/-- The finite-history version of permanent locked liquidity. Starting from a
good pool model, no successful sequence can unwind the locked floor. -/
def pair_closed_world_path_locked_liquidity_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      before.lockedLiquidity ≤ after.lockedLiquidity

theorem closed_world_path_locked_liquidity_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_path_locked_liquidity_never_decreases before after := by
  exact pairWorldPath_locked_liquidity_never_decreases

-- tama: discharges=pair_closed_world_reachable_path_locked_liquidity_never_decreases
theorem closed_world_reachable_path_locked_liquidity_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_locked_liquidity_never_decreases before after := by
  intro h_reachable h_path
  exact pairWorldPath_locked_liquidity_never_decreases
    (pairWorldReachable_good before h_reachable) h_path



/-- Finite-history reserve isolation. A history made only of LP bookkeeping,
direct donations, and skim may change LP ownership or token balances, but it
never changes the cached reserves. This is the path-level form of the
reserve-change classifier above, and it is the invariant a router-facing reader
can cite when reasoning that cached price state is stable unless a reserve
update action actually occurs. -/
def pair_closed_world_no_reserve_update_path_preserves_reserves
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoReserveUpdate before after →
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1

theorem closed_world_no_reserve_update_path_preserves_reserves
    (start finish : PairWorldState) :
  pair_closed_world_no_reserve_update_path_preserves_reserves start finish := by
  intro h_path
  induction h_path with
  | refl =>
      exact ⟨rfl, rfl⟩
  | @step mid next action h_prefix h_step
      h_not_mint h_not_burn h_not_swap h_not_sync ih =>
      have h_step_reserves :
          next.reserve0 = mid.reserve0 ∧
          next.reserve1 = mid.reserve1 := by
        cases action with
        | approve ownerAddr spender amount =>
            simp [PairWorldStep] at h_step
            subst next
            exact ⟨rfl, rfl⟩
        | transfer fromAddr toAddr amount =>
            simp [PairWorldStep] at h_step
            subst next
            exact ⟨rfl, rfl⟩
        | transferFrom spender fromAddr toAddr amount =>
            simp [PairWorldStep] at h_step
            subst next
            exact ⟨rfl, rfl⟩
        | donate amount0 amount1 =>
            simp [PairWorldStep] at h_step
            rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0,
              h_reserve1, _h_supply, _h_locked⟩
            exact ⟨h_reserve0, h_reserve1⟩
        | mint amount0 amount1 liquidity =>
            exact False.elim (h_not_mint amount0 amount1 liquidity rfl)
        | burn amount0 amount1 liquidity =>
            exact False.elim (h_not_burn amount0 amount1 liquidity rfl)
        | swap amount0In amount1In amount0Out amount1Out =>
            exact False.elim
              (h_not_swap amount0In amount1In amount0Out amount1Out rfl)
        | skim =>
            simp [PairWorldStep, PairWorldSkimStep] at h_step
            rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0,
              h_reserve1, _h_supply, _h_locked⟩
            exact ⟨h_reserve0, h_reserve1⟩
        | sync =>
            exact False.elim (h_not_sync rfl)
      exact ⟨by rw [h_step_reserves.1, ih.1],
        by rw [h_step_reserves.2, ih.2]⟩

/-- Economic corollary of finite-history reserve isolation. If no mint, burn,
swap, or sync occurs, the cached reserve product and reserve-denominated spot
value are unchanged. This deliberately talks about cached reserves rather than
actual token balances: direct donations and `skim` may change surplus, but they
do not change the reserve price state. -/
def pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoReserveUpdate before after →
    PairWorldK after = PairWorldK before ∧
    PairWorldSpotValueNum before after =
      PairWorldSpotValueNum before before

theorem closed_world_no_reserve_update_path_preserves_k_and_spot_value
    (before after : PairWorldState) :
  pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value
    before after := by
  intro h_path
  have h_reserves :=
    closed_world_no_reserve_update_path_preserves_reserves before after h_path
  constructor
  · unfold PairWorldK
    rw [h_reserves.1, h_reserves.2]
  · unfold PairWorldSpotValueNum
    rw [h_reserves.1, h_reserves.2]

-- tama: discharges=pair_closed_world_reachable_reserve_change_requires_reserve_update
theorem closed_world_reachable_reserve_change_requires_reserve_update
    (before after : PairWorldState) :
  pair_closed_world_reachable_reserve_change_requires_reserve_update
    before after := by
  intro _h_reachable h_changed h_no_reserve_update
  have h_preserve :=
    closed_world_no_reserve_update_path_preserves_reserves
      before after h_no_reserve_update
  rcases h_changed with h_reserve0_changed | h_reserve1_changed
  · exact h_reserve0_changed h_preserve.1
  · exact h_reserve1_changed h_preserve.2

/-- The one-step LP-supply firewall. A successful modeled action that is not
mint and not burn cannot change total LP supply or the permanently locked
liquidity amount. This is the local fact that the finite-history theorem below
iterates. -/
def pair_closed_world_non_liquidity_step_preserves_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      after.totalSupply = before.totalSupply ∧
      after.lockedLiquidity = before.lockedLiquidity

theorem closed_world_non_liquidity_step_preserves_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_liquidity_step_preserves_supply action before after := by
  intro h_step h_not_mint h_not_burn
  exact pairWorldNoMintBurnPath_preserves_supply
    (PairWorldPathNoMintBurn.step action
      (PairWorldPathNoMintBurn.refl before)
      h_step h_not_mint h_not_burn)

/-- The finite-history version of the LP supply firewall. If a successful
modeled path contains no mint and no burn, then it cannot change total LP supply
or the permanently locked liquidity amount. -/
def pair_closed_world_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoMintBurn before after →
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

theorem closed_world_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) :
  pair_closed_world_no_mint_burn_path_preserves_supply before after := by
  exact pairWorldNoMintBurnPath_preserves_supply


/-- The directional LP-supply firewall. A single successful modeled action that
is not burn cannot destroy LP supply. Mint may create new shares and ordinary
pool operations may leave supply unchanged, but redemption is the only direction
that can move supply downward. -/
def pair_closed_world_non_burn_step_never_decreases_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      before.totalSupply ≤ after.totalSupply

theorem closed_world_non_burn_step_never_decreases_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_burn_step_never_decreases_supply action before after := by
  exact pairWorldNonBurnStep_never_decreases_supply

/-- The finite-history version of the same supply direction fact. Along any
successful modeled history with no burn step, total LP supply cannot decrease.
This is the trace-level statement that "LP redemption requires burn." -/
def pair_closed_world_no_burn_path_never_decreases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoBurn before after →
    before.totalSupply ≤ after.totalSupply

theorem closed_world_no_burn_path_never_decreases_supply
    (before after : PairWorldState) :
  pair_closed_world_no_burn_path_never_decreases_supply before after := by
  exact pairWorldNoBurnPath_never_decreases_supply


/-- The other direction of LP-supply isolation. A single successful modeled
action that is not mint cannot create LP supply. Burn may redeem shares and
ordinary pool operations may leave supply unchanged, but issuance is isolated to
mint. -/
def pair_closed_world_non_mint_step_never_increases_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
      after.totalSupply ≤ before.totalSupply

theorem closed_world_non_mint_step_never_increases_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_mint_step_never_increases_supply action before after := by
  exact pairWorldNonMintStep_never_increases_supply

/-- The finite-history version of LP issuance isolation. Along any successful
modeled history with no mint step, total LP supply cannot increase. This is the
trace-level statement that new LP claims require mint. -/
def pair_closed_world_no_mint_path_never_increases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoMint before after →
    after.totalSupply ≤ before.totalSupply

theorem closed_world_no_mint_path_never_increases_supply
    (before after : PairWorldState) :
  pair_closed_world_no_mint_path_never_increases_supply before after := by
  exact pairWorldNoMintPath_never_increases_supply




-- tama: discharges=pair_closed_world_reachable_supply_change_requires_mint_or_burn
theorem closed_world_reachable_supply_change_requires_mint_or_burn
    (before after : PairWorldState) :
  pair_closed_world_reachable_supply_change_requires_mint_or_burn before after := by
  intro h_reachable h_changed h_no_mint_burn
  have h_preserve :=
    closed_world_no_mint_burn_path_preserves_supply
      before after h_no_mint_burn
  exact h_changed h_preserve.1

-- tama: discharges=pair_closed_world_approve_preserves_pool
theorem closed_world_approve_preserves_pool
    (ownerAddr spender : Address) (amount : Nat)
    (before after : PairWorldState) :
  pair_closed_world_approve_preserves_pool ownerAddr spender amount before after := by
  intro h_step
  simpa [PairWorldStep] using h_step

-- tama: discharges=pair_closed_world_transfer_preserves_pool
theorem closed_world_transfer_preserves_pool
    (fromAddr toAddr : Address) (amount : Nat)
    (before after : PairWorldState) :
  pair_closed_world_transfer_preserves_pool fromAddr toAddr amount before after := by
  intro h_step
  simpa [PairWorldStep] using h_step

-- tama: discharges=pair_closed_world_transferFrom_preserves_pool
theorem closed_world_transferFrom_preserves_pool
    (spender fromAddr toAddr : Address) (amount : Nat)
    (before after : PairWorldState) :
  pair_closed_world_transferFrom_preserves_pool
    spender fromAddr toAddr amount before after := by
  intro h_step
  simpa [PairWorldStep] using h_step

theorem pairWorldShareBookkeepingPath_preserves_pool_state
    {before after : PairWorldState} :
  PairWorldPathShareBookkeeping before after →
    after.balance0 = before.balance0 ∧
    after.balance1 = before.balance1 ∧
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1 ∧
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity := by
  intro h_path
  induction h_path with
  | refl =>
      simp
  | approve ownerAddr spender amount h_prefix h_step ih =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ih
  | transfer fromAddr toAddr amount h_prefix h_step ih =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ih
  | transferFrom spender fromAddr toAddr amount h_prefix h_step ih =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ih

/-- LP token bookkeeping is only bookkeeping. Across any finite sequence made
solely of approvals, direct LP transfers, and delegated LP transfers, the AMM
state is unchanged: token balances, cached reserves, total LP supply, and the
permanently locked liquidity amount all end exactly where they started. This is
the trace-level version of the ERC20-share claim above, and it is what lets the
economic sections ignore pure share movements as price- or reserve-changing
actions. -/
def pair_closed_world_share_bookkeeping_path_preserves_pool_state
    (before after : PairWorldState) : Prop :=
  PairWorldPathShareBookkeeping before after →
    after.balance0 = before.balance0 ∧
    after.balance1 = before.balance1 ∧
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1 ∧
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

theorem closed_world_share_bookkeeping_path_preserves_pool_state
    (before after : PairWorldState) :
  pair_closed_world_share_bookkeeping_path_preserves_pool_state before after := by
  exact pairWorldShareBookkeepingPath_preserves_pool_state

/-- Economic corollary of the share-bookkeeping invariant. If a history only
moves LP approvals or LP balances between accounts, then it cannot change the
pool's cached K, reserve-denominated spot value, or actual-token-balance spot
value. Pure ownership bookkeeping is therefore not an AMM profit path. -/
def pair_closed_world_share_bookkeeping_path_preserves_k_and_value
    (before after : PairWorldState) : Prop :=
  PairWorldPathShareBookkeeping before after →
    PairWorldK after = PairWorldK before ∧
    PairWorldSpotValueNum before after =
      PairWorldSpotValueNum before before ∧
    PairWorldBalanceSpotValueNum before after =
      PairWorldBalanceSpotValueNum before before

theorem closed_world_share_bookkeeping_path_preserves_k_and_value
    (before after : PairWorldState) :
  pair_closed_world_share_bookkeeping_path_preserves_k_and_value before after := by
  intro h_path
  rcases pairWorldShareBookkeepingPath_preserves_pool_state h_path with
    ⟨h_balance0, h_balance1, h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  simp [pair_closed_world_share_bookkeeping_path_preserves_k_and_value,
    PairWorldK, PairWorldSpotValueNum, PairWorldBalanceSpotValueNum,
    h_balance0, h_balance1, h_reserve0, h_reserve1]

-- tama: discharges=pair_closed_world_first_mint_locks_minimum_liquidity
theorem closed_world_first_mint_locks_minimum_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_first_mint_locks_minimum_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step h_first
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, h_supply, h_locked, _h_ratio⟩
  simp [h_first] at h_supply h_locked
  exact ⟨h_locked, h_supply⟩

-- tama: discharges=pair_closed_world_first_mint_keeps_locked_share
theorem closed_world_first_mint_keeps_locked_share
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_first_mint_keeps_locked_share
    amount0 amount1 liquidity before after := by
  intro h_step h_first
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, h_supply, h_locked, _h_ratio⟩
  simp [h_first] at h_supply h_locked
  constructor
  · rw [h_locked, h_supply]
    unfold minimumLiquidityNat
    omega
  · rw [h_supply]
    unfold minimumLiquidityNat
    omega

-- tama: discharges=pair_closed_world_subsequent_mint_preserves_locked_liquidity
theorem closed_world_subsequent_mint_preserves_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_subsequent_mint_preserves_locked_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step h_subsequent
  have h_totalSupply_ne : ¬ before.totalSupply = 0 := h_subsequent
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, h_supply, h_locked, _h_ratio⟩
  simp [h_totalSupply_ne] at h_supply h_locked
  exact ⟨h_locked, h_supply⟩

-- tama: discharges=pair_closed_world_mint_strictly_increases_supply
theorem closed_world_mint_strictly_increases_supply
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_strictly_increases_supply
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_ratio⟩
  by_cases h_first : before.totalSupply = 0
  · simp [h_first] at h_supply
    rw [h_supply, h_first]
    omega
  · simp [h_first] at h_supply
    rw [h_supply]
    omega

-- tama: discharges=pair_closed_world_mint_adds_exact_deposits_to_reserves
theorem closed_world_mint_adds_exact_deposits_to_reserves
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_adds_exact_deposits_to_reserves
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, h_before_balance0,
    h_before_balance1, _h_after_balance0, _h_after_balance1, h_after_reserve0,
    h_after_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
  constructor
  · rw [h_after_reserve0, h_before_balance0]
  · rw [h_after_reserve1, h_before_balance1]




-- tama: discharges=pair_first_mint_success_uses_canonical_liquidity_formula
theorem first_mint_success_uses_canonical_liquidity_formula
    (toAddr : Address) (s : ContractState) :
  pair_first_mint_success_uses_canonical_liquidity_formula
    toAddr s ((mint toAddr).run s) := by
  intro _h_run _h_success _h_supply_zero _h_reserve0 _h_reserve1
    _h_amount0 _h_amount1 _h_product h_root
  have h_root_le : minimumLiquidity.val ≤ (mintFirstRoot s).val :=
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
  constructor
  · rw [h_liquidity_eq, h_min_val]
    have h_root_le_nat : minimumLiquidityNat ≤ (mintFirstRoot s).val := by
      rw [← h_min_val]
      exact h_root_le
    omega
  constructor
  · simp [pairWorldAfterFirstMintRun]
  · rw [h_liquidity_eq, h_min_val]
    simp [pairWorldAfterFirstMintRun]
    have h_root_le_nat : minimumLiquidityNat ≤ (mintFirstRoot s).val := by
      rw [← h_min_val]
      exact h_root_le
    omega



-- tama: discharges=pair_closed_world_burn_reduces_supply_by_liquidity
theorem closed_world_burn_reduces_supply_by_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_reduces_supply_by_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  exact h_supply

-- tama: discharges=pair_closed_world_burn_removes_exact_redemptions_from_balances
theorem closed_world_burn_removes_exact_redemptions_from_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_removes_exact_redemptions_from_balances
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, h_amount0_le, h_amount1_le, _h_liquidity_le,
    _h_locked_remaining, h_balance0, h_balance1, h_reserve0, h_reserve1,
    _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · exact h_reserve0
  · exact h_reserve1


-- tama: discharges=pair_closed_world_burn_never_increases_supply
theorem closed_world_burn_never_increases_supply
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_never_increases_supply
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  rw [h_supply]
  exact Nat.sub_le before.totalSupply liquidity

-- tama: discharges=pair_closed_world_burn_cannot_redeem_locked_liquidity
theorem closed_world_burn_cannot_redeem_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_cannot_redeem_locked_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    h_supply, h_locked, _h_ratio0, _h_ratio1⟩
  rw [h_supply]
  exact ⟨h_locked_remaining, h_locked⟩


-- tama: discharges=pair_closed_world_burn_preserves_positive_balances
theorem closed_world_burn_preserves_positive_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_preserves_positive_balances
    amount0 amount1 liquidity before after := by
  intro h_good h_step h_before_balance0 h_before_balance1
  rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply_good⟩
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    h_supply_pos, h_amount0_le, h_amount1_le, _h_liquidity_le,
    h_locked_remaining, h_balance0, h_balance1, _h_reserve0, _h_reserve1,
    _h_bound0, _h_bound1, _h_supply, _h_locked, h_ratio0, h_ratio1⟩
  have h_locked : before.lockedLiquidity = minimumLiquidityNat := by
    rcases h_supply_good with h_empty | h_nonempty
    · exact False.elim (Nat.ne_of_gt h_supply_pos h_empty.1)
    · exact h_nonempty.2.1
  have h_locked_remaining_min :
      minimumLiquidityNat ≤ before.totalSupply - liquidity := by
    simpa [h_locked] using h_locked_remaining
  have h_liquidity_lt_supply : liquidity < before.totalSupply := by
    have h_sub_pos : 0 < before.totalSupply - liquidity := by
      exact Nat.lt_of_lt_of_le (by norm_num [minimumLiquidityNat])
        h_locked_remaining_min
    exact Nat.sub_pos_iff_lt.mp h_sub_pos
  have h_amount0_lt : amount0 < before.balance0 := by
    by_contra h_not_lt
    have h_ge : before.balance0 ≤ amount0 := Nat.le_of_not_gt h_not_lt
    have h_eq : amount0 = before.balance0 := le_antisymm h_amount0_le h_ge
    have h_ratio0' :
        before.balance0 * before.totalSupply ≤ liquidity * before.balance0 := by
      simpa [h_eq] using h_ratio0
    have h_balance_pos_int : (0 : Int) < before.balance0 := by
      exact_mod_cast h_before_balance0
    have h_liquidity_lt_int : (liquidity : Int) < before.totalSupply := by
      exact_mod_cast h_liquidity_lt_supply
    have h_ratio0_int :
        (before.balance0 : Int) * before.totalSupply ≤
          (liquidity : Int) * before.balance0 := by
      exact_mod_cast h_ratio0'
    nlinarith
  have h_amount1_lt : amount1 < before.balance1 := by
    by_contra h_not_lt
    have h_ge : before.balance1 ≤ amount1 := Nat.le_of_not_gt h_not_lt
    have h_eq : amount1 = before.balance1 := le_antisymm h_amount1_le h_ge
    have h_ratio1' :
        before.balance1 * before.totalSupply ≤ liquidity * before.balance1 := by
      simpa [h_eq] using h_ratio1
    have h_balance_pos_int : (0 : Int) < before.balance1 := by
      exact_mod_cast h_before_balance1
    have h_liquidity_lt_int : (liquidity : Int) < before.totalSupply := by
      exact_mod_cast h_liquidity_lt_supply
    have h_ratio1_int :
        (before.balance1 : Int) * before.totalSupply ≤
          (liquidity : Int) * before.balance1 := by
      exact_mod_cast h_ratio1'
    nlinarith
  constructor
  · rw [h_balance0]
    omega
  · rw [h_balance1]
    omega


theorem pairWorldStep_positive_reserves_preserved
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      0 < before.reserve0 →
        0 < before.reserve1 →
          PairWorldStep action before after →
            0 < after.reserve0 ∧
            0 < after.reserve1 := by
  intro h_good h_supply_pos h_reserve0_pos h_reserve1_pos h_step
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      rw [h_reserve0, h_reserve1]
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨h_amount0_pos, h_amount1_pos, _h_liquidity_pos,
        h_before_balance0, h_before_balance1, _h_after_balance0,
        _h_after_balance1, h_after_reserve0, h_after_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
      constructor
      · rw [h_after_reserve0, h_before_balance0]
        omega
      · rw [h_after_reserve1, h_before_balance1]
        omega
  | burn amount0 amount1 liquidity =>
      have h_good_copy := h_good
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1,
        _h_supply_good⟩
      have h_balance0_pos : 0 < before.balance0 :=
        Nat.lt_of_lt_of_le h_reserve0_pos h_back0
      have h_balance1_pos : 0 < before.balance1 :=
        Nat.lt_of_lt_of_le h_reserve1_pos h_back1
      have h_balances :=
        closed_world_burn_preserves_positive_balances
          amount0 amount1 liquidity before after
          h_good_copy h_step h_balance0_pos h_balance1_pos
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
        _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity,
        _h_locked_remaining, h_balance0, h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
      constructor
      · rw [h_reserve0]
        exact h_balances.1
      · rw [h_reserve1]
        exact h_balances.2
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, h_liq0, h_liq1, _h_enough0, _h_enough1,
        _h_input, h_balance0, h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1,
        _h_adjusted_k⟩
      constructor
      · rw [h_reserve0, h_balance0]
        exact Nat.sub_pos_of_lt (by omega)
      · rw [h_reserve1, h_balance1]
        exact Nat.sub_pos_of_lt (by omega)
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      rw [h_reserve0, h_reserve1]
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | sync =>
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1,
        _h_supply_good⟩
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        h_reserve0, h_reserve1, _h_supply, _h_locked⟩
      constructor
      · rw [h_reserve0]
        exact Nat.lt_of_lt_of_le h_reserve0_pos h_back0
      · rw [h_reserve1]
        exact Nat.lt_of_lt_of_le h_reserve1_pos h_back1

theorem pairWorldReachable_positive_supply_positive_reserves
    {w : PairWorldState} :
  PairWorldReachable w →
    0 < w.totalSupply →
      0 < w.reserve0 ∧
      0 < w.reserve1 := by
  intro h_reachable
  induction h_reachable with
  | init =>
      intro h_positive
      simp [PairWorldInitial] at h_positive
  | step action h_before h_step ih =>
      intro h_positive_after
      rename_i before after
      have h_step_original := h_step
      cases action with
      | approve ownerAddr spender amount =>
          simp [PairWorldStep] at h_step
          subst after
          exact ih h_positive_after
      | transfer fromAddr toAddr amount =>
          simp [PairWorldStep] at h_step
          subst after
          exact ih h_positive_after
      | transferFrom spender fromAddr toAddr amount =>
          simp [PairWorldStep] at h_step
          subst after
          exact ih h_positive_after
      | donate amount0 amount1 =>
          simp [PairWorldStep] at h_step
          rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, h_supply, _h_locked⟩
          have h_positive_before : 0 < before.totalSupply := by
            rwa [h_supply] at h_positive_after
          have h_before_reserves := ih h_positive_before
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_positive_before h_before_reserves.1 h_before_reserves.2
            h_step_original
      | mint amount0 amount1 liquidity =>
          simp [PairWorldStep, PairWorldMintStep] at h_step
          rcases h_step with ⟨h_amount0_pos, h_amount1_pos, _h_liquidity_pos,
            h_before_balance0, h_before_balance1, _h_after_balance0,
            _h_after_balance1, h_after_reserve0, h_after_reserve1,
            _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
          constructor
          · rw [h_after_reserve0, h_before_balance0]
            omega
          · rw [h_after_reserve1, h_before_balance1]
            omega
      | burn amount0 amount1 liquidity =>
          simp [PairWorldStep, PairWorldBurnStep] at h_step
          rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
            h_supply_before_pos, _h_amount0, _h_amount1, _h_liquidity,
            _h_locked_remaining, _h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
            _h_ratio0, _h_ratio1⟩
          have h_before_reserves := ih h_supply_before_pos
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_supply_before_pos h_before_reserves.1 h_before_reserves.2
            h_step_original
      | swap amount0In amount1In amount0Out amount1Out =>
          simp [PairWorldStep, PairWorldSwapStep] at h_step
          rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
            _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked,
            _h_fee0, _h_fee1, _h_adjusted_k⟩
          have h_positive_before : 0 < before.totalSupply := by
            rwa [h_supply] at h_positive_after
          have h_before_reserves := ih h_positive_before
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_positive_before h_before_reserves.1 h_before_reserves.2
            h_step_original
      | skim =>
          simp [PairWorldStep, PairWorldSkimStep] at h_step
          rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, h_supply, _h_locked⟩
          have h_positive_before : 0 < before.totalSupply := by
            rwa [h_supply] at h_positive_after
          have h_before_reserves := ih h_positive_before
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_positive_before h_before_reserves.1 h_before_reserves.2
            h_step_original
      | sync =>
          simp [PairWorldStep, PairWorldSyncStep] at h_step
          rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
            _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
          have h_positive_before : 0 < before.totalSupply := by
            rwa [h_supply] at h_positive_after
          have h_before_reserves := ih h_positive_before
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_positive_before h_before_reserves.1 h_before_reserves.2
            h_step_original

theorem pairWorldPath_positive_reserves_preserved
    {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      0 < before.reserve0 →
        0 < before.reserve1 →
          PairWorldPath before after →
            0 < after.reserve0 ∧
            0 < after.reserve1 := by
  intro h_good h_supply_pos h_reserve0_pos h_reserve1_pos h_path
  induction h_path with
  | refl =>
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | step action h_prefix h_step ih =>
      have h_good_before := pairWorldPath_preserves_good h_good h_prefix
      have h_supply_before :=
        pairWorldPath_positive_supply_preserved h_good h_supply_pos h_prefix
      have h_reserves_before := ih
      exact pairWorldStep_positive_reserves_preserved
        h_good_before h_supply_before
        h_reserves_before.1 h_reserves_before.2 h_step



-- tama: discharges=pair_closed_world_donate_preserves_reserves_and_supply
theorem closed_world_donate_preserves_reserves_and_supply
    (amount0 amount1 : Nat)
    (before after : PairWorldState) :
  pair_closed_world_donate_preserves_reserves_and_supply
    amount0 amount1 before after := by
  intro h_step
  simp [PairWorldStep] at h_step
  rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
    h_supply, h_locked⟩
  exact ⟨h_reserve0, h_reserve1, h_supply, h_locked⟩

-- tama: discharges=pair_closed_world_donate_preserves_k
theorem closed_world_donate_preserves_k
    (amount0 amount1 : Nat)
    (before after : PairWorldState) :
  pair_closed_world_donate_preserves_k amount0 amount1 before after := by
  intro h_step
  simp [PairWorldStep] at h_step
  rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  unfold PairWorldK
  rw [h_reserve0, h_reserve1]

-- tama: discharges=pair_closed_world_donation_increases_surplus_exactly
theorem closed_world_donation_increases_surplus_exactly
    (amount0 amount1 : Nat)
    (before after : PairWorldState) :
  pair_closed_world_donation_increases_surplus_exactly
    amount0 amount1 before after := by
  intro h_good h_step
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  simp [PairWorldStep] at h_step
  rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  unfold PairWorldSurplus0 PairWorldSurplus1
  constructor <;> omega

/-- No non-donation action can create new reserve surplus. Share bookkeeping
preserves any existing surplus; mint, burn, swap, skim, and sync either account
for balances as reserves or remove surplus; none of them can increase
`balance - reserve` without an explicit external token donation. -/
def pair_closed_world_non_donation_step_never_increases_surplus
    (action : PairWorldAction)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1, action ≠ PairWorldAction.donate amount0 amount1) →
        PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
        PairWorldSurplus1 after ≤ PairWorldSurplus1 before

theorem closed_world_non_donation_step_never_increases_surplus
    (action : PairWorldAction)
    (before after : PairWorldState) :
  pair_closed_world_non_donation_step_never_increases_surplus
    action before after := by
  intro h_good h_step h_not_donation
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ⟨le_rfl, le_rfl⟩
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ⟨le_rfl, le_rfl⟩
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ⟨le_rfl, le_rfl⟩
  | donate amount0 amount1 =>
      exact False.elim (h_not_donation amount0 amount1 rfl)
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_before_balance0, _h_before_balance1, h_after_balance0,
        h_after_balance1, h_after_reserve0, h_after_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_after_reserve0, h_after_reserve1, h_after_balance0, h_after_balance1]
      omega
  | burn amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
        _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity,
        _h_locked_remaining, h_balance0, h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_reserve0, h_reserve1]
      omega
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
        _h_enough1, _h_input, h_balance0, h_balance1, h_reserve0,
        h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
        _h_fee0, _h_fee1, _h_adjusted_k⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_reserve0, h_reserve1]
      omega
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_balance0, h_balance1, h_reserve0, h_reserve1]
      omega
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
        h_reserve0, h_reserve1, _h_supply, _h_locked⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_balance0, h_balance1, h_reserve0, h_reserve1]
      omega

theorem pairWorldNoDonationPath_never_increases_surplus
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPathNoDonation before after →
      PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
      PairWorldSurplus1 after ≤ PairWorldSurplus1 before := by
  intro h_good h_path
  induction h_path with
  | refl =>
      exact ⟨le_rfl, le_rfl⟩
  | step action h_prefix h_step h_not_donation ih =>
      have h_good_mid :=
        pairWorldPath_preserves_good h_good
          (pairWorldPath_of_noDonation h_prefix)
      have h_step_surplus :=
        closed_world_non_donation_step_never_increases_surplus
          action _ _ h_good_mid h_step h_not_donation
      exact ⟨Nat.le_trans h_step_surplus.1 ih.1,
        Nat.le_trans h_step_surplus.2 ih.2⟩

/-- Trace-level surplus isolation. Across any finite successful history with no
direct donation step, reserve surplus on either token side cannot increase. -/
def pair_closed_world_no_donation_path_never_increases_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoDonation before after →
      PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
      PairWorldSurplus1 after ≤ PairWorldSurplus1 before

theorem closed_world_no_donation_path_never_increases_surplus
    (before after : PairWorldState) :
  pair_closed_world_no_donation_path_never_increases_surplus before after := by
  exact pairWorldNoDonationPath_never_increases_surplus

-- tama: discharges=pair_closed_world_reachable_no_donation_path_never_increases_surplus
theorem closed_world_reachable_no_donation_path_never_increases_surplus
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_donation_path_never_increases_surplus
    before after := by
  intro h_reachable h_path
  exact pairWorldNoDonationPath_never_increases_surplus
    (pairWorldReachable_good before h_reachable) h_path






-- tama: discharges=pair_burn_success_pays_exact_pro_rata_amounts
theorem burn_success_pays_exact_pro_rata_amounts
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_pays_exact_pro_rata_amounts
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success _h_liquidity_pos _h_supply_pos
  simp [burnAmount0, burnAmount1, burnAmount0Product, burnAmount1Product,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure]

-- tama: discharges=pair_burn_success_caches_post_redemption_balances
theorem burn_success_caches_post_redemption_balances
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_caches_post_redemption_balances
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success _h_liquidity_pos _h_supply_pos
    _h_amount0_le _h_amount1_le
  simp [pairWorldAfterBurnRun]


-- tama: discharges=pair_swap_success_accounts_for_input_and_output
theorem swap_success_accounts_for_input_and_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_accounts_for_input_and_output
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_k
  dsimp [pair_swap_success_accounts_for_input_and_output,
    pairWorldFromConcreteState, pairWorldAfterSwapRun]
  constructor
  · have h_cover0 :
        amount0Out.val ≤
          (s.storage reserve0Slot.slot).val +
            (swapAmount0In amount0Out balance0Now s).val := by
      have h_liq0_val :
          amount0Out.val < (s.storage reserve0Slot.slot).val := by
        simpa [Verity.Core.Uint256.lt_def] using h_liq0
      omega
    calc
      balance0Now.val + amount0Out.val
          = ((s.storage reserve0Slot.slot).val +
                (swapAmount0In amount0Out balance0Now s).val -
              amount0Out.val) + amount0Out.val := by rw [h_balance0]
      _ = (s.storage reserve0Slot.slot).val +
            (swapAmount0In amount0Out balance0Now s).val := by
          exact Nat.sub_add_cancel h_cover0
  · have h_cover1 :
        amount1Out.val ≤
          (s.storage reserve1Slot.slot).val +
            (swapAmount1In amount1Out balance1Now s).val := by
      have h_liq1_val :
          amount1Out.val < (s.storage reserve1Slot.slot).val := by
        simpa [Verity.Core.Uint256.lt_def] using h_liq1
      omega
    calc
      balance1Now.val + amount1Out.val
          = ((s.storage reserve1Slot.slot).val +
                (swapAmount1In amount1Out balance1Now s).val -
              amount1Out.val) + amount1Out.val := by rw [h_balance1]
      _ = (s.storage reserve1Slot.slot).val +
            (swapAmount1In amount1Out balance1Now s).val := by
          exact Nat.sub_add_cancel h_cover1

-- tama: discharges=pair_swap_success_charges_k_against_final_balances
theorem swap_success_charges_k_against_final_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_charges_k_against_final_balances
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_run h_success h_post _h_liq0 _h_liq1 _h_balance0 _h_balance1
  have h_guards :=
    finishSwapChecked_success_implies_guards
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      ((swap amount0Out amount1Out toAddr data).run s) h_run h_success h_post
  rcases h_guards with
    ⟨h_input, h_bound0, h_bound1, h_fee0, h_fee1, h_k⟩
  constructor
  · exact h_input
  constructor
  · exact h_bound0
  constructor
  · exact h_bound1
  constructor
  · exact h_fee0
  constructor
  · exact h_fee1
  · simpa [pair_swap_success_charges_k_against_final_balances,
      pairWorldFromConcreteState, pairWorldAfterSwapRun] using h_k

/- One valid action cannot dilute existing LP shares: measured
as reserve product per squared LP supply, the pool is at least as strong after
the step as before it. -/
def pair_closed_world_step_k_per_supply_never_decreases
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep action before after →
        PairWorldKPerSupplyNondecreasing before after

theorem closed_world_step_k_per_supply_never_decreases
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_step_k_per_supply_never_decreases action before after := by
  exact pairWorldStep_k_per_supply_never_decreases

/- The one-step dilution bound composes over every finite path. This is the
main sequence invariant: no combination of transfers, donations, mint, burn,
swap, skim, or sync can reduce LP-normalized K from a good positive-supply
state. -/
def pair_closed_world_path_k_per_supply_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        PairWorldKPerSupplyNondecreasing before after

theorem closed_world_path_k_per_supply_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_path_k_per_supply_never_decreases before after := by
  exact pairWorldPath_k_per_supply_never_decreases

-- tama: discharges=pair_closed_world_reachable_path_lp_share_backing_never_decreases
theorem closed_world_reachable_path_lp_share_backing_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_lp_share_backing_never_decreases before after := by
  intro h_reachable h_positive h_path
  exact pairWorldPath_k_per_supply_never_decreases
    (pairWorldReachable_good before h_reachable) h_positive h_path


end TamaUniV2.Proof.UniswapV2PairProof
