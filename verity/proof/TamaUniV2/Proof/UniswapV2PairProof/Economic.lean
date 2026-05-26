import TamaUniV2.Proof.UniswapV2PairProof.ClosedWorld

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
attribute [local simp] pairWalletWithStepFlows

theorem pairWalletStep_pairPath
    {action : PairWalletAction} {before after : PairWalletWorldState} :
  PairWalletStep action before after →
    PairWorldPath before.pair after.pair := by
  intro h_step
  cases action <;>
    simp [PairWalletStep] at h_step
  · rw [h_step.1]
    exact PairWorldPath.refl before.pair
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.2.2.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.2.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.1

theorem pairWalletHistory_pairPath
    {before after : PairWalletWorldState} :
  PairWalletHistory before after →
    PairWorldPath before.pair after.pair := by
  intro h_history
  induction h_history with
  | refl => exact PairWorldPath.refl before.pair
  | step action h_prefix h_step ih =>
      cases action <;>
        simp [PairWalletStep] at h_step
      · rw [h_step.1]
        exact ih
      · exact PairWorldPath.step (PairWorldAction.donate _ _) ih h_step.2.2.1
      · exact PairWorldPath.step PairWorldAction.skim ih h_step.1
      · exact PairWorldPath.step
          (PairWorldAction.swap _ _ _ _) ih h_step.1
      · exact PairWorldPath.step
          (PairWorldAction.mint _ _ _) ih h_step.1
      · exact PairWorldPath.step
          (PairWorldAction.burn _ _ _) ih h_step.2.1
      · exact PairWorldPath.step PairWorldAction.sync ih h_step.1

theorem ordinaryPairWalletHistory_history
    {before after : PairWalletWorldState} :
  OrdinaryPairWalletHistory before after →
    PairWalletHistory before after := by
  intro h_history
  induction h_history with
  | refl _h_flow =>
      exact PairWalletHistory.refl _
  | step action h_prefix h_step _h_ordinary ih =>
      exact PairWalletHistory.step action ih h_step

theorem pairWalletStep_total_value_conserved
    (spot : PairWorldState) {action : PairWalletAction}
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    PairWalletActionOrdinary action before after →
    PairWalletStep action before after →
      PairWalletTotalTokenValueAtSpot spot before =
        PairWalletTotalTokenValueAtSpot spot after := by
  intro h_good h_ordinary h_step
  rcases h_good with ⟨h_pair_good, _h_wallet⟩
  rcases h_pair_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  cases action <;>
    simp [PairWalletStep, PairWorldStep, PairWorldMintStep, PairWorldBurnStep,
      PairWorldSwapStep, PairWorldSkimStep, PairWorldSyncStep] at h_step
  · rcases h_step with
      ⟨h_pair, h_caller0, h_caller1, _h_callerLp, _h_pairLp, _h_flows⟩
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_pair, h_caller0, h_caller1]
  · rcases h_step with ⟨h_token0, h_token1, h_pair, h_caller0, h_caller1, _h_lp⟩
    rename_i amount0 amount1
    rcases h_pair with ⟨h_balance0, h_balance1, _h_reserve0, _h_reserve1,
      _h_supply, _h_locked⟩
    have h_caller0_add : after.callerToken0 + amount0 = before.callerToken0 := by
      rw [h_caller0]
      omega
    have h_caller1_add : after.callerToken1 + amount1 = before.callerToken1 := by
      rw [h_caller1]
      omega
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_balance0, h_balance1]
    nlinarith
  · rcases h_step with ⟨h_pair, h_amount0, h_amount1, h_caller0, h_caller1, _h_lp⟩
    rcases h_pair with ⟨h_balance0, h_balance1, _h_reserve0, _h_reserve1,
      _h_supply, _h_locked⟩
    have h_surplus0 :
        before.pair.balance0 =
          before.pair.reserve0 + PairWorldSurplus0 before.pair := by
      unfold PairWorldSurplus0
      omega
    have h_surplus1 :
        before.pair.balance1 =
          before.pair.reserve1 + PairWorldSurplus1 before.pair := by
      unfold PairWorldSurplus1
      omega
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1, h_balance0, h_balance1, h_amount0, h_amount1,
      h_surplus0, h_surplus1]
    nlinarith
  · simp [PairWalletActionOrdinary] at h_ordinary
    rcases h_ordinary with ⟨h_give0, h_give1⟩
    rcases h_step with ⟨h_pair, h_caller0, h_caller1, _h_lp⟩
    rename_i amount0In amount1In amount0Out amount1Out
    rcases h_pair with ⟨_h_output, _h_liq0, _h_liq1, h_enough0, h_enough1,
      _h_input, h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
      _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_k⟩
    have h_before_balance0 :
        before.pair.balance0 =
          before.pair.reserve0 + PairWorldSurplus0 before.pair := by
      unfold PairWorldSurplus0
      omega
    have h_before_balance1 :
        before.pair.balance1 =
          before.pair.reserve1 + PairWorldSurplus1 before.pair := by
      unfold PairWorldSurplus1
      omega
    have h_after_plus0 :
        after.pair.balance0 + amount0Out =
          before.pair.reserve0 + PairWorldSurplus0 before.pair := by
      rw [h_balance0, Nat.sub_add_cancel h_enough0]
      omega
    have h_after_plus1 :
        after.pair.balance1 + amount1Out =
          before.pair.reserve1 + PairWorldSurplus1 before.pair := by
      rw [h_balance1, Nat.sub_add_cancel h_enough1]
      omega
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1, h_before_balance0, h_before_balance1]
    have h_token0_value :
        before.callerToken0 * spot.reserve1 +
            (before.pair.reserve0 + PairWorldSurplus0 before.pair) * spot.reserve1 =
          (before.callerToken0 + amount0Out) * spot.reserve1 +
            after.pair.balance0 * spot.reserve1 := by
      rw [← Nat.add_mul, ← Nat.add_mul]
      congr 1
      omega
    have h_token1_value :
        before.callerToken1 * spot.reserve0 +
            (before.pair.reserve1 + PairWorldSurplus1 before.pair) * spot.reserve0 =
          (before.callerToken1 + amount1Out) * spot.reserve0 +
            after.pair.balance1 * spot.reserve0 := by
      rw [← Nat.add_mul, ← Nat.add_mul]
      congr 1
      omega
    omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, h_caller0,
      h_caller1, _h_lp⟩
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_balance0_before, _h_balance1_before, h_balance0, h_balance1,
      _h_reserve0, _h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
      _h_ratio⟩
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1, h_balance0, h_balance1]
  · rcases h_step with ⟨_h_lp_enough, h_pair, h_caller0, h_caller1, _h_lp⟩
    rename_i amount0 amount1 transferredLiquidity burnedLiquidity
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_supply_pos, h_amount0_le, h_amount1_le, _h_liq_le, _h_locked_le,
      h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
      _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
    have h_balance0_add : after.pair.balance0 + amount0 = before.pair.balance0 := by
      rw [h_balance0]
      omega
    have h_balance1_add : after.pair.balance1 + amount1 = before.pair.balance1 := by
      rw [h_balance1]
      omega
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1]
    have h_token0_value :
        before.callerToken0 * spot.reserve1 +
            before.pair.balance0 * spot.reserve1 =
          (before.callerToken0 + amount0) * spot.reserve1 +
            after.pair.balance0 * spot.reserve1 := by
      rw [← Nat.add_mul, ← Nat.add_mul]
      congr 1
      omega
    have h_token1_value :
        before.callerToken1 * spot.reserve0 +
            before.pair.balance1 * spot.reserve0 =
          (before.callerToken1 + amount1) * spot.reserve0 +
            after.pair.balance1 * spot.reserve0 := by
      rw [← Nat.add_mul, ← Nat.add_mul]
      congr 1
      omega
    omega
  · rcases h_step with ⟨h_pair, h_caller0, h_caller1, _h_lp⟩
    rcases h_pair with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
      _h_reserve0, _h_reserve1, _h_supply, _h_locked⟩
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1, h_balance0, h_balance1]

theorem pairWalletStep_flow_token_conserved
    (spot : PairWorldState) {action : PairWalletAction}
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    PairWalletStep action before after →
      after.recv0 * spot.reserve1 + after.recv1 * spot.reserve0 +
            PairWorldBalanceSpotValueNum spot after.pair +
            (before.give0 * spot.reserve1 + before.give1 * spot.reserve0) =
        before.recv0 * spot.reserve1 + before.recv1 * spot.reserve0 +
            PairWorldBalanceSpotValueNum spot before.pair +
            (after.give0 * spot.reserve1 + after.give1 * spot.reserve0) := by
  intro h_good h_step
  rcases h_good with ⟨h_pair_good, _h_wallet⟩
  rcases h_pair_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  cases action <;>
    simp [PairWalletStep, PairWorldStep, PairWorldMintStep, PairWorldBurnStep,
      PairWorldSwapStep, PairWorldSkimStep, PairWorldSyncStep] at h_step
  · rcases h_step with
      ⟨h_pair, _h_caller0, _h_caller1, _h_callerLp, _h_pairLp, h_flows⟩
    rcases h_flows with
      ⟨h_recv0, h_recv1, _h_recvLp, h_give0, h_give1, _h_giveLp⟩
    unfold PairWorldBalanceSpotValueNum
    rw [h_pair, h_recv0, h_recv1, h_give0, h_give1]
  · rcases h_step with ⟨_h_token0, _h_token1, h_pair, _h_caller0,
      _h_caller1, h_lp⟩
    rename_i amount0 amount1
    rcases h_pair with ⟨h_balance0, h_balance1, _h_reserve0, _h_reserve1,
      _h_supply, _h_locked⟩
    rcases h_lp with
      ⟨_h_callerLp, _h_pairLp, h_recv0, h_recv1, _h_recvLp, h_give0,
        h_give1, _h_giveLp⟩
    unfold PairWorldBalanceSpotValueNum
    rw [h_balance0, h_balance1, h_recv0, h_recv1, h_give0, h_give1]
    nlinarith
  · rcases h_step with ⟨h_pair, h_amount0, h_amount1, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_pair with ⟨h_balance0, h_balance1, _h_reserve0, _h_reserve1,
      _h_supply, _h_locked⟩
    rcases h_lp with
      ⟨_h_callerLp, _h_pairLp, h_recv0, h_recv1, _h_recvLp, h_give0,
        h_give1, _h_giveLp⟩
    have h_surplus0 :
        before.pair.balance0 =
          before.pair.reserve0 + PairWorldSurplus0 before.pair := by
      unfold PairWorldSurplus0
      omega
    have h_surplus1 :
        before.pair.balance1 =
          before.pair.reserve1 + PairWorldSurplus1 before.pair := by
      unfold PairWorldSurplus1
      omega
    unfold PairWorldBalanceSpotValueNum
    rw [h_balance0, h_balance1, h_recv0, h_recv1, h_amount0, h_amount1,
      h_give0, h_give1, h_surplus0, h_surplus1]
    nlinarith
  · rcases h_step with ⟨h_pair, _h_caller0, _h_caller1, h_lp⟩
    rename_i give0 give1 amount0Out amount1Out
    rcases h_pair with ⟨_h_output, _h_liq0, _h_liq1, h_enough0, h_enough1,
      _h_input, h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
      _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_k⟩
    rcases h_lp with
      ⟨_h_callerLp, _h_pairLp, h_recv0, h_recv1, _h_recvLp, h_give0,
        h_give1, _h_giveLp⟩
    have h_before_balance0 :
        before.pair.balance0 =
          before.pair.reserve0 + PairWorldSurplus0 before.pair := by
      unfold PairWorldSurplus0
      omega
    have h_before_balance1 :
        before.pair.balance1 =
          before.pair.reserve1 + PairWorldSurplus1 before.pair := by
      unfold PairWorldSurplus1
      omega
    have h_after_plus0 :
        after.pair.balance0 + amount0Out =
          before.pair.reserve0 + (give0 + PairWorldSurplus0 before.pair) := by
      rw [h_balance0, Nat.sub_add_cancel h_enough0]
    have h_after_plus1 :
        after.pair.balance1 + amount1Out =
          before.pair.reserve1 + (give1 + PairWorldSurplus1 before.pair) := by
      rw [h_balance1, Nat.sub_add_cancel h_enough1]
    unfold PairWorldBalanceSpotValueNum
    rw [h_recv0, h_recv1, h_give0, h_give1, h_before_balance0,
      h_before_balance1]
    have h_token0_value :
        (before.recv0 + amount0Out) * spot.reserve1 +
            after.pair.balance0 * spot.reserve1 +
            before.give0 * spot.reserve1 =
          before.recv0 * spot.reserve1 +
            (before.pair.reserve0 + PairWorldSurplus0 before.pair) *
              spot.reserve1 +
            (before.give0 + give0) * spot.reserve1 := by
      repeat rw [← Nat.add_mul]
      congr 1
      omega
    have h_token1_value :
        (before.recv1 + amount1Out) * spot.reserve0 +
            after.pair.balance1 * spot.reserve0 +
            before.give1 * spot.reserve0 =
          before.recv1 * spot.reserve0 +
            (before.pair.reserve1 + PairWorldSurplus1 before.pair) *
              spot.reserve0 +
            (before.give1 + give1) * spot.reserve0 := by
      repeat rw [← Nat.add_mul]
      congr 1
      omega
    omega
  · rcases h_step with ⟨h_pair, h_amount0, h_amount1, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_balance0_before, _h_balance1_before, h_balance0, h_balance1,
      _h_reserve0, _h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
      _h_ratio⟩
    rcases h_lp with
      ⟨_h_callerLp, _h_pairLp, h_recv0, h_recv1, _h_recvLp, h_give0,
        h_give1, _h_giveLp⟩
    have h_before_balance0 :
        before.pair.balance0 =
          before.pair.reserve0 + PairWorldSurplus0 before.pair := by
      unfold PairWorldSurplus0
      omega
    have h_before_balance1 :
        before.pair.balance1 =
          before.pair.reserve1 + PairWorldSurplus1 before.pair := by
      unfold PairWorldSurplus1
      omega
    unfold PairWorldBalanceSpotValueNum
    rw [h_balance0, h_balance1, h_recv0, h_recv1, h_give0, h_give1]
  · rcases h_step with ⟨_h_lp_enough, h_pair, _h_caller0, _h_caller1, h_lp⟩
    rename_i amount0 amount1 transferredLiquidity burnedLiquidity
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_supply_pos, h_amount0_le, h_amount1_le, _h_liq_le, _h_locked_le,
      h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
      _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
    rcases h_lp with
      ⟨_h_callerLp, _h_pairLp, h_recv0, h_recv1, _h_recvLp, h_give0,
        h_give1, _h_giveLp⟩
    have h_balance0_add : after.pair.balance0 + amount0 = before.pair.balance0 := by
      rw [h_balance0]
      omega
    have h_balance1_add : after.pair.balance1 + amount1 = before.pair.balance1 := by
      rw [h_balance1]
      omega
    unfold PairWorldBalanceSpotValueNum
    rw [h_recv0, h_recv1, h_give0, h_give1]
    have h_token0_value :
        (before.recv0 + amount0) * spot.reserve1 +
            after.pair.balance0 * spot.reserve1 =
          before.recv0 * spot.reserve1 +
            before.pair.balance0 * spot.reserve1 := by
      repeat rw [← Nat.add_mul]
      congr 1
      omega
    have h_token1_value :
        (before.recv1 + amount1) * spot.reserve0 +
            after.pair.balance1 * spot.reserve0 =
          before.recv1 * spot.reserve0 +
            before.pair.balance1 * spot.reserve0 := by
      repeat rw [← Nat.add_mul]
      congr 1
      omega
    omega
  · rcases h_step with ⟨h_pair, _h_caller0, _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
      _h_reserve0, _h_reserve1, _h_supply, _h_locked⟩
    rcases h_lp with
      ⟨_h_callerLp, _h_pairLp, h_recv0, h_recv1, _h_recvLp, h_give0,
        h_give1, _h_giveLp⟩
    unfold PairWorldBalanceSpotValueNum
    rw [h_balance0, h_balance1, h_recv0, h_recv1, h_give0, h_give1]

theorem pairWalletStep_flow_lp_conserved
    {action : PairWalletAction} {before after : PairWalletWorldState} :
  0 < before.pair.totalSupply →
    PairWalletStep action before after →
      after.recvLp + before.giveLp + after.pairLp + before.pair.totalSupply =
        before.recvLp + after.giveLp + before.pairLp + after.pair.totalSupply := by
  intro h_positive h_step
  cases action <;>
    simp [PairWalletStep, PairWorldStep, PairWorldMintStep, PairWorldBurnStep,
      PairWorldSwapStep, PairWorldSkimStep, PairWorldSyncStep] at h_step
  · rcases h_step with
      ⟨h_pair, _h_caller0, _h_caller1, _h_callerLp, h_pairLp, h_flows⟩
    rcases h_flows with
      ⟨_h_recv0, _h_recv1, h_recvLp, _h_give0, _h_give1, h_giveLp⟩
    rw [h_pair, h_pairLp, h_recvLp, h_giveLp]
  · rcases h_step with ⟨_h_token0, _h_token1, h_pair, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, _h_locked⟩
    rcases h_lp with
      ⟨_h_callerLp, h_pairLp, _h_recv0, _h_recv1, h_recvLp, _h_give0,
        _h_give1, h_giveLp⟩
    rw [h_pairLp, h_recvLp, h_giveLp, h_supply]
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, _h_locked⟩
    rcases h_lp with
      ⟨_h_callerLp, h_pairLp, _h_recv0, _h_recv1, h_recvLp, _h_give0,
        _h_give1, h_giveLp⟩
    rw [h_pairLp, h_recvLp, h_giveLp, h_supply]
  · rcases h_step with ⟨h_pair, _h_caller0, _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
      _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
      _h_bound1, h_supply, _h_locked, _h_fee0, _h_fee1, _h_k⟩
    rcases h_lp with
      ⟨_h_callerLp, h_pairLp, _h_recv0, _h_recv1, h_recvLp, _h_give0,
        _h_give1, h_giveLp⟩
    rw [h_pairLp, h_recvLp, h_giveLp, h_supply]
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0,
      _h_caller1, h_lp⟩
    rename_i amount0 amount1 liquidity
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_balance0_before, _h_balance1_before, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked,
      _h_ratio⟩
    rcases h_lp with
      ⟨_h_callerLp, h_pairLp, _h_recv0, _h_recv1, h_recvLp, _h_give0,
        _h_give1, h_giveLp⟩
    rw [if_neg (Nat.ne_of_gt h_positive)] at h_supply
    rw [h_pairLp, h_recvLp, h_giveLp, h_supply]
    omega
  · rcases h_step with ⟨_h_lp_enough, h_pair, _h_caller0, _h_caller1, h_lp⟩
    rename_i amount0 amount1 transferredLiquidity burnedLiquidity
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liq_le, _h_locked_le,
      _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
      h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
    rcases h_lp with
      ⟨_h_callerLp, h_pairLp, _h_recv0, _h_recv1, h_recvLp, _h_give0,
        _h_give1, h_giveLp⟩
    rw [h_recvLp, h_giveLp, h_supply]
    omega
  · rcases h_step with ⟨h_pair, _h_caller0, _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
    rcases h_lp with
      ⟨_h_callerLp, h_pairLp, _h_recv0, _h_recv1, h_recvLp, _h_give0,
        _h_give1, h_giveLp⟩
    rw [h_pairLp, h_recvLp, h_giveLp, h_supply]

theorem pairWorldGood_positive_supply_locked_pos
    {w : PairWorldState} :
  PairWorldGood w →
    0 < w.totalSupply →
      0 < w.lockedLiquidity := by
  intro h_good h_positive
  rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply_good⟩
  rcases h_supply_good with h_empty | h_nonempty
  · omega
  · rcases h_nonempty with ⟨_h_supply, h_locked, _h_min⟩
    rw [h_locked]
    norm_num [minimumLiquidityNat]

theorem pairWalletStep_preserves_good_and_positive
    {action : PairWalletAction} {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletStep action before after →
        PairWalletGood after ∧
          0 < after.pair.totalSupply ∧
          after.pair.lockedLiquidity = before.pair.lockedLiquidity := by
  intro h_good h_positive h_step
  rcases h_good with ⟨h_pair_good, h_wallet⟩
  cases action <;>
    simp [PairWalletStep, PairWorldStep, PairWorldMintStep, PairWorldBurnStep,
      PairWorldSwapStep, PairWorldSkimStep, PairWorldSyncStep] at h_step
  · rcases h_step with
      ⟨h_pair, _h_caller0, _h_caller1, h_callerLp, h_pairLp, _h_flows⟩
    constructor
    · constructor
      · simpa [h_pair] using h_pair_good
      · rw [h_callerLp, h_pairLp, h_pair]
        exact h_wallet
    · constructor
      · rwa [h_pair]
      · rw [h_pair]
  · rcases h_step with ⟨_h_token0, _h_token1, h_pair, _h_caller0, _h_caller1,
      h_lp⟩
    rename_i amount0 amount1
    rcases h_lp with ⟨h_callerLp, h_pairLp, _h_flows⟩
    have h_pair_step :
        PairWorldStep (PairWorldAction.donate amount0 amount1) before.pair after.pair := by
      simpa [PairWorldStep] using h_pair
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, h_locked⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0, _h_caller1,
      h_lp⟩
    rcases h_lp with ⟨h_callerLp, h_pairLp, _h_flows⟩
    have h_pair_step : PairWorldStep PairWorldAction.skim before.pair after.pair := by
      simpa [PairWorldStep, PairWorldSkimStep] using h_pair
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, h_locked⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega
  · rcases h_step with ⟨h_pair, _h_amount0In, _h_amount1In, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_lp with ⟨h_callerLp, h_pairLp, _h_flows⟩
    rename_i amount0In amount1In amount0Out amount1Out
    have h_pair_step :
        PairWorldStep
          (PairWorldAction.swap
            (amount0In + PairWorldSurplus0 before.pair)
            (amount1In + PairWorldSurplus1 before.pair)
            amount0Out amount1Out)
          before.pair after.pair := by
      simpa [PairWorldStep, PairWorldSwapStep] using h_pair
    rcases h_pair with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
      _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
      _h_bound1, h_supply, h_locked, _h_fee0, _h_fee1, _h_k⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_lp with ⟨h_callerLp, h_pairLp, _h_flows⟩
    rename_i amount0 amount1 liquidity
    have h_pair_step :
        PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity)
          before.pair after.pair := by
      simpa [PairWorldStep, PairWorldMintStep] using h_pair
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_balance0_before, _h_balance1_before, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, _h_bound0, _h_bound1, h_supply, h_locked,
      _h_ratio⟩
    rw [if_neg (Nat.ne_of_gt h_positive)] at h_supply
    rw [if_neg (Nat.ne_of_gt h_positive)] at h_locked
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega
  · rcases h_step with ⟨h_lp_enough, h_pair, _h_caller0, _h_caller1, h_lp⟩
    rcases h_lp with ⟨h_callerLp, h_pairLp, _h_flows⟩
    rename_i amount0 amount1 transferredLiquidity burnedLiquidity
    have h_pair_step :
        PairWorldStep (PairWorldAction.burn amount0 amount1 burnedLiquidity)
          before.pair after.pair := by
      simpa [PairWorldStep, PairWorldBurnStep] using h_pair
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liq_le, h_locked_le,
      _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
      h_supply, h_locked, _h_ratio0, _h_ratio1⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    have h_locked_pos := pairWorldGood_positive_supply_locked_pos h_pair_good h_positive
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · constructor
      · omega
      · exact h_locked
  · rcases h_step with ⟨h_pair, _h_caller0, _h_caller1, h_lp⟩
    rcases h_lp with ⟨h_callerLp, h_pairLp, _h_flows⟩
    have h_pair_step : PairWorldStep PairWorldAction.sync before.pair after.pair := by
      simpa [PairWorldStep, PairWorldSyncStep] using h_pair
    rcases h_pair with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, h_supply, h_locked⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega

/- If a finite path returns to the same LP supply, LP normalization cancels.
The pool's raw reserve product therefore cannot be lower than where it began. -/
def pair_closed_world_same_supply_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldK before ≤ PairWorldK after

theorem closed_world_same_supply_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_same_supply_path_never_decreases_k before after := by
  exact pairWorldSameSupplyPath_never_decreases_k

/- Constant-product arithmetic: once raw K is known not to fall, the final
reserves cannot be worth less than the initial reserves at the initial spot
price. This lemma is kept parameterized by the K fact so other sequence
arguments can reuse the geometric conversion directly. -/
def pair_closed_world_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldPath before after →
    PairWorldGood before →
      before.totalSupply = after.totalSupply →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldK before ≤ PairWorldK after →
              PairWorldNoSpotProfit before after

theorem closed_world_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_same_supply_path_no_spot_profit before after := by
  intro _h_path _h_good _h_supply h_reserve0 h_reserve1 h_k
  unfold PairWorldNoSpotProfit PairWorldSpotValueNum PairWorldK at *
  by_contra h_not
  have h_lt :
      after.reserve0 * before.reserve1 + after.reserve1 * before.reserve0 <
        2 * (before.reserve0 * before.reserve1) :=
    Nat.lt_of_not_ge h_not
  have h_reserve0_int : (0 : Int) < before.reserve0 := by
    exact_mod_cast h_reserve0
  have h_reserve1_int : (0 : Int) < before.reserve1 := by
    exact_mod_cast h_reserve1
  let a : Int := before.reserve0
  let b : Int := before.reserve1
  let c : Int := after.reserve0
  let d : Int := after.reserve1
  have ha : 0 < a := by simpa [a] using h_reserve0_int
  have hb : 0 < b := by simpa [b] using h_reserve1_int
  have hc : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast Nat.zero_le after.reserve0
  have hd : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast Nat.zero_le after.reserve1
  have hk : a * b ≤ c * d := by
    dsimp [a, b, c, d]
    exact_mod_cast h_k
  have hlt : c * b + d * a < 2 * (a * b) := by
    dsimp [a, b, c, d]
    exact_mod_cast h_lt
  have hsq : 0 ≤ (c * b - d * a) ^ 2 := sq_nonneg _
  have hamgm : 4 * c * d * a * b ≤ (c * b + d * a) ^ 2 := by
    nlinarith [hsq]
  have hab_pos : 0 < a * b := by
    nlinarith [ha, hb]
  have hkscaled : 4 * a * b * a * b ≤ 4 * c * d * a * b := by
    nlinarith [hk, hab_pos]
  have hsum_nonneg : 0 ≤ c * b + d * a := by
    nlinarith [ha, hb, hc, hd]
  have htarget_pos : 0 < 2 * (a * b) := by
    nlinarith [ha, hb]
  have hlt_sq : (c * b + d * a) ^ 2 < (2 * (a * b)) ^ 2 := by
    nlinarith [hlt, hsum_nonneg, htarget_pos]
  nlinarith [hamgm, hkscaled, hlt_sq]

/- The complete same-supply no-profit theorem for the closed-world pool model:
from any good positive-supply state with nonzero reserves, every finite path
that ends with the same LP supply has no spot-price profit. This version allows
mint/burn round trips because it relies on LP-normalized K rather than the older
no-burn K theorem. -/
def pair_closed_world_positive_supply_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
            0 < before.reserve1 →
              PairWorldNoSpotProfit before after

theorem closed_world_positive_supply_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_positive_supply_same_supply_path_no_spot_profit before after := by
  intro h_good h_positive h_path h_supply h_reserve0 h_reserve1
  have h_k :
      PairWorldK before ≤ PairWorldK after :=
    pairWorldSameSupplyPath_never_decreases_k h_good h_positive h_path h_supply
  exact closed_world_same_supply_path_no_spot_profit before after
    h_path h_good h_supply h_reserve0 h_reserve1 h_k






/- The reachable-state version of the same-supply K theorem is the one most
callers should cite: from any actually reachable nonempty pool, any finite
successful sequence that returns LP supply to its starting value cannot reduce
raw reserve product. -/
def pair_closed_world_reachable_same_supply_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldK before ≤ PairWorldK after

theorem closed_world_reachable_same_supply_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_never_decreases_k before after := by
  intro h_reachable h_positive h_path h_supply
  exact pairWorldSameSupplyPath_never_decreases_k
    (pairWorldReachable_good before h_reachable) h_positive h_path h_supply

/- The reachable-state no-profit theorem states the economic conclusion in the
language of the contract user. Starting from any reachable nonempty pool with a
defined spot price, any finite successful sequence that leaves LP supply
unchanged leaves the pool worth at least as much at the initial spot price.
Without an external gift to the caller, that rules out spot-price profit. -/
def pair_closed_world_reachable_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
            0 < before.reserve1 →
              PairWorldNoSpotProfit before after

theorem closed_world_reachable_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_no_spot_profit before after := by
  intro h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  exact closed_world_positive_supply_same_supply_path_no_spot_profit before after
    (pairWorldReachable_good before h_reachable)
    h_positive h_path h_supply h_reserve0 h_reserve1


/-- Caller-facing form of the same theorem. `PairWorld` tracks pool-side token
balances and LP supply, not arbitrary external wallet balances, so the
closed-world no-profit claim is stated as absence of pool value extraction: if a
finite successful history returns LP supply to its starting value, the final pool
cannot be worth less at the initial spot price. Any positive closed-world caller
profit would have to appear as that missing pool value; external gifts are
outside this theorem's closed-world premise. -/
def pair_closed_world_reachable_same_supply_path_no_spot_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldSpotValueNum before before ≤
              PairWorldSpotValueNum before after

theorem closed_world_reachable_same_supply_path_no_spot_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_no_spot_value_extraction before after := by
  intro h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  have h_no_profit :=
    closed_world_reachable_same_supply_path_no_spot_profit
      before after h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  unfold PairWorldNoSpotProfit PairWorldSpotValueNum PairWorldK at h_no_profit
  unfold PairWorldSpotValueNum
  nlinarith



theorem pairWorldSpotValue_le_balanceSpotValue
    {spot pool : PairWorldState} :
  PairWorldGood pool →
    PairWorldSpotValueNum spot pool ≤
      PairWorldBalanceSpotValueNum spot pool := by
  intro h_good
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  unfold PairWorldSpotValueNum PairWorldBalanceSpotValueNum
  exact Nat.add_le_add
    (Nat.mul_le_mul_right spot.reserve1 h_back0)
    (Nat.mul_le_mul_right spot.reserve0 h_back1)

theorem pairWorldBalanceSpotValue_eq_spot_plus_surplus
    {spot pool : PairWorldState} :
  PairWorldGood pool →
    PairWorldBalanceSpotValueNum spot pool =
      PairWorldSpotValueNum spot pool +
        PairWorldSurplusSpotValueNum spot pool := by
  intro h_good
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  have h_balance0 :
      pool.balance0 = pool.reserve0 + PairWorldSurplus0 pool := by
    unfold PairWorldSurplus0
    omega
  have h_balance1 :
      pool.balance1 = pool.reserve1 + PairWorldSurplus1 pool := by
    unfold PairWorldSurplus1
    omega
  unfold PairWorldBalanceSpotValueNum PairWorldSpotValueNum
    PairWorldSurplusSpotValueNum
  rw [h_balance0, h_balance1]
  nlinarith

theorem pairWalletHistory_preserves_good_and_positive
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletHistory before after →
        PairWalletGood after ∧
          0 < after.pair.totalSupply ∧
          after.pair.lockedLiquidity = before.pair.lockedLiquidity := by
  intro h_good h_positive h_history
  revert h_good h_positive
  induction h_history with
  | refl =>
      intro h_good h_positive
      exact ⟨h_good, h_positive, rfl⟩
  | step action h_prefix h_step ih =>
      intro h_good h_positive
      rcases ih h_good h_positive with
        ⟨h_mid_good, h_mid_positive, h_mid_locked⟩
      rcases pairWalletStep_preserves_good_and_positive
          h_mid_good h_mid_positive h_step with
        ⟨h_after_good, h_after_positive, h_after_locked⟩
      exact ⟨h_after_good, h_after_positive, by rw [h_after_locked, h_mid_locked]⟩

theorem pairWalletHistory_flow_token_conserved
    (spot : PairWorldState) {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletHistory before after →
        after.recv0 * spot.reserve1 + after.recv1 * spot.reserve0 +
              PairWorldBalanceSpotValueNum spot after.pair +
              (before.give0 * spot.reserve1 + before.give1 * spot.reserve0) =
          before.recv0 * spot.reserve1 + before.recv1 * spot.reserve0 +
              PairWorldBalanceSpotValueNum spot before.pair +
              (after.give0 * spot.reserve1 + after.give1 * spot.reserve0) := by
  intro h_good h_positive h_history
  revert h_good h_positive
  induction h_history with
  | refl =>
      intro _h_good _h_positive
      rfl
  | step action h_prefix h_step ih =>
      intro h_good h_positive
      have h_prefix_eq := ih h_good h_positive
      rcases pairWalletHistory_preserves_good_and_positive
          h_good h_positive h_prefix with
        ⟨h_mid_good, _h_mid_positive, _h_mid_locked⟩
      have h_step_eq :=
        pairWalletStep_flow_token_conserved spot h_mid_good h_step
      nlinarith [h_prefix_eq, h_step_eq]

theorem pairWalletHistory_flow_lp_conserved
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletHistory before after →
        after.recvLp + before.giveLp + after.pairLp + before.pair.totalSupply =
          before.recvLp + after.giveLp + before.pairLp +
            after.pair.totalSupply := by
  intro h_good h_positive h_history
  revert h_good h_positive
  induction h_history with
  | refl =>
      intro _h_good _h_positive
      rfl
  | step action h_prefix h_step ih =>
      intro h_good h_positive
      have h_prefix_eq := ih h_good h_positive
      rcases pairWalletHistory_preserves_good_and_positive
          h_good h_positive h_prefix with
        ⟨_h_mid_good, h_mid_positive, _h_mid_locked⟩
      have h_step_eq :=
        pairWalletStep_flow_lp_conserved h_mid_positive h_step
      omega

theorem pairWalletHistory_total_value_conserved
    (spot : PairWorldState) {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      OrdinaryPairWalletHistory before after →
        PairWalletTotalTokenValueAtSpot spot before =
          PairWalletTotalTokenValueAtSpot spot after := by
  intro h_good h_positive h_history
  revert h_good h_positive
  induction h_history with
  | refl =>
      intro _h_good _h_positive
      rfl
  | step action h_prefix h_step h_ordinary ih =>
      intro h_good h_positive
      have h_prefix_value := ih h_good h_positive
      have h_prefix_history := ordinaryPairWalletHistory_history h_prefix
      rcases pairWalletHistory_preserves_good_and_positive
          h_good h_positive h_prefix_history with
        ⟨h_mid_good, _h_mid_positive, _h_mid_locked⟩
      have h_step_value :=
        pairWalletStep_total_value_conserved spot h_mid_good h_ordinary h_step
      exact h_prefix_value.trans h_step_value

theorem pairWalletPortfolio_plus_unowned_eq_total
    (spot : PairWorldState) (w : PairWalletWorldState) :
  PairWalletGood w →
    PairWalletPortfolioValueNumeratorAtSpot spot w +
        (w.pair.totalSupply - w.callerLp) * PairWorldSpotValueNum spot w.pair =
      PairWalletTotalTokenValueAtSpot spot w * w.pair.totalSupply := by
  intro h_good
  rcases h_good with ⟨h_pair_good, h_wallet⟩
  have h_balance_eq :=
    pairWorldBalanceSpotValue_eq_spot_plus_surplus
      (spot := spot) (pool := w.pair) h_pair_good
  have h_le : w.callerLp ≤ w.pair.totalSupply := by omega
  unfold PairWalletPortfolioValueNumeratorAtSpot PairWalletTotalTokenValueAtSpot
    PairWalletCallerTokenValueAtSpot PairWalletSkimmableValueAtSpot
  rw [h_balance_eq]
  have h_split :
      (w.pair.totalSupply - w.callerLp) * PairWorldSpotValueNum spot w.pair +
          w.callerLp * PairWorldSpotValueNum spot w.pair =
        w.pair.totalSupply * PairWorldSpotValueNum spot w.pair := by
    rw [← Nat.add_mul]
    congr 1
    omega
  nlinarith [h_split]

theorem pairWorldKPerSupply_spot_value_per_supply
    {spot after : PairWorldState} :
  0 < spot.totalSupply →
    0 < after.totalSupply →
      0 < spot.reserve0 →
        0 < spot.reserve1 →
          PairWorldKPerSupplyNondecreasing spot after →
            PairWorldSpotValueNum spot spot * after.totalSupply ≤
              PairWorldSpotValueNum spot after * spot.totalSupply := by
  intro h_spot_supply h_after_supply h_reserve0 h_reserve1 h_k_scaled
  unfold PairWorldKPerSupplyNondecreasing PairWorldSpotValueNum PairWorldK at *
  by_contra h_not
  have h_lt :
      (after.reserve0 * spot.reserve1 + after.reserve1 * spot.reserve0) *
          spot.totalSupply <
        (spot.reserve0 * spot.reserve1 + spot.reserve1 * spot.reserve0) *
          after.totalSupply :=
    Nat.lt_of_not_ge h_not
  have h_reserve0_int : (0 : Int) < spot.reserve0 := by
    exact_mod_cast h_reserve0
  have h_reserve1_int : (0 : Int) < spot.reserve1 := by
    exact_mod_cast h_reserve1
  have h_spot_supply_int : (0 : Int) < spot.totalSupply := by
    exact_mod_cast h_spot_supply
  have h_after_supply_int : (0 : Int) < after.totalSupply := by
    exact_mod_cast h_after_supply
  let a : Int := spot.reserve0
  let b : Int := spot.reserve1
  let c : Int := after.reserve0
  let d : Int := after.reserve1
  let s0 : Int := spot.totalSupply
  let s1 : Int := after.totalSupply
  have ha : 0 < a := by simpa [a] using h_reserve0_int
  have hb : 0 < b := by simpa [b] using h_reserve1_int
  have hc : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast Nat.zero_le after.reserve0
  have hd : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast Nat.zero_le after.reserve1
  have hs0 : 0 < s0 := by simpa [s0] using h_spot_supply_int
  have hs1 : 0 < s1 := by simpa [s1] using h_after_supply_int
  have hk :
      a * b * s1 * s1 ≤ c * d * s0 * s0 := by
    dsimp [a, b, c, d, s0, s1]
    exact_mod_cast h_k_scaled
  have hlt :
      (c * b + d * a) * s0 < (a * b + b * a) * s1 := by
    dsimp [a, b, c, d, s0, s1]
    exact_mod_cast h_lt
  have hsq : 0 ≤ (c * b * s0 - d * a * s0) ^ 2 := sq_nonneg _
  have hamgm :
      4 * c * d * a * b * s0 * s0 ≤
        ((c * b + d * a) * s0) ^ 2 := by
    nlinarith [hsq]
  have hab_pos : 0 < a * b := by
    nlinarith [ha, hb]
  have hkscaled :
      4 * a * b * a * b * s1 * s1 ≤
        4 * c * d * a * b * s0 * s0 := by
    nlinarith [hk, hab_pos]
  have hsum_nonneg : 0 ≤ (c * b + d * a) * s0 := by
    have hcb_nonneg : 0 ≤ c * b := mul_nonneg hc (le_of_lt hb)
    have hda_nonneg : 0 ≤ d * a := mul_nonneg hd (le_of_lt ha)
    exact mul_nonneg (add_nonneg hcb_nonneg hda_nonneg) (le_of_lt hs0)
  have htarget_pos : 0 < (a * b + b * a) * s1 := by
    have hab_pos' : 0 < a * b := mul_pos ha hb
    have hba_pos : 0 < b * a := mul_pos hb ha
    exact mul_pos (add_pos hab_pos' hba_pos) hs1
  have hlt_sq :
      ((c * b + d * a) * s0) ^ 2 <
        ((a * b + b * a) * s1) ^ 2 := by
    nlinarith [hlt, hsum_nonneg, htarget_pos]
  nlinarith [hamgm, hkscaled, hlt_sq]

theorem pairWalletStep_preserves_unowned
    {action : PairWalletAction} {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletActionOrdinary action before after →
      PairWalletStep action before after →
        after.pair.totalSupply - after.callerLp =
          before.pair.totalSupply - before.callerLp := by
  intro h_good h_positive h_ordinary h_step
  rcases h_good with ⟨_h_pair_good, h_wallet⟩
  cases action <;>
    simp [PairWalletStep, PairWorldStep, PairWorldMintStep, PairWorldBurnStep,
      PairWorldSwapStep, PairWorldSkimStep, PairWorldSyncStep] at h_step
  · rcases h_step with
      ⟨h_pair, _h_caller0, _h_caller1, h_callerLp, _h_pairLp, _h_flows⟩
    rw [h_pair, h_callerLp]
  · rcases h_step with ⟨_h_token0, _h_token1, h_pair, _h_caller0, _h_caller1,
      h_lp⟩
    rcases h_lp with ⟨h_callerLp, _h_pairLp, _h_flows⟩
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, _h_locked⟩
    omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0, _h_caller1,
      h_lp⟩
    rcases h_lp with ⟨h_callerLp, _h_pairLp, _h_flows⟩
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, _h_locked⟩
    omega
  · rcases h_step with ⟨h_pair, _h_amount0In, _h_amount1In, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_lp with ⟨h_callerLp, _h_pairLp, _h_flows⟩
    rcases h_pair with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
      _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
      _h_bound1, h_supply, _h_locked, _h_fee0, _h_fee1, _h_k⟩
    omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_lp with ⟨h_callerLp, _h_pairLp, _h_flows⟩
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_balance0_before, _h_balance1_before, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked,
      _h_ratio⟩
    rw [if_neg (Nat.ne_of_gt h_positive)] at h_supply
    omega
  · rcases h_step with ⟨h_lp_enough, h_pair, _h_caller0, _h_caller1, h_lp⟩
    simp [PairWalletActionOrdinary] at h_ordinary
    have h_transfer_eq_burn := h_ordinary
    rcases h_lp with ⟨h_callerLp, _h_pairLp, _h_flows⟩
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_supply_pos, _h_amount0_le, _h_amount1_le, h_liq_le, _h_locked_le,
      _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
      h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
    omega
  · rcases h_step with ⟨h_pair, _h_caller0, _h_caller1, h_lp⟩
    rcases h_lp with ⟨h_callerLp, _h_pairLp, _h_flows⟩
    rcases h_pair with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
    omega

theorem pairWalletHistory_preserves_unowned
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      OrdinaryPairWalletHistory before after →
        after.pair.totalSupply - after.callerLp =
          before.pair.totalSupply - before.callerLp := by
  intro h_good h_positive h_history
  revert h_good h_positive
  induction h_history with
  | refl =>
      intro _h_good _h_positive
      rfl
  | step action h_prefix h_step h_ordinary ih =>
      intro h_good h_positive
      have h_mid := ih h_good h_positive
      have h_prefix_history := ordinaryPairWalletHistory_history h_prefix
      rcases pairWalletHistory_preserves_good_and_positive
          h_good h_positive h_prefix_history with
        ⟨h_mid_good, h_mid_positive, _h_mid_locked⟩
      have h_step_eq :=
        pairWalletStep_preserves_unowned h_mid_good h_mid_positive
          h_ordinary h_step
      rw [h_step_eq]; exact h_mid

theorem pairWalletHistory_no_portfolio_profit
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          OrdinaryPairWalletHistory before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply := by
  intro h_good h_supply h_reserve0 h_reserve1 h_history
  have h_wallet_history := ordinaryPairWalletHistory_history h_history
  have h_path := pairWalletHistory_pairPath h_wallet_history
  rcases pairWalletHistory_preserves_good_and_positive
      h_good h_supply h_wallet_history with
    ⟨h_good_after, h_supply_after, _h_locked_after⟩
  have h_total :=
    pairWalletHistory_total_value_conserved before.pair
      h_good h_supply h_history
  have h_unowned :=
    pairWalletHistory_preserves_unowned h_good h_supply h_history
  have h_k_scaled :=
    pairWorldPath_k_per_supply_never_decreases
      h_good.1 h_supply h_path
  have h_spot_per_supply :=
    pairWorldKPerSupply_spot_value_per_supply
      h_supply h_supply_after h_reserve0 h_reserve1 h_k_scaled
  have h_before_identity :=
    pairWalletPortfolio_plus_unowned_eq_total before.pair before h_good
  have h_after_identity :=
    pairWalletPortfolio_plus_unowned_eq_total before.pair after h_good_after
  rw [← h_total] at h_after_identity
  rw [h_unowned] at h_after_identity
  have h_unowned_spot :=
    Nat.mul_le_mul_left (before.pair.totalSupply - before.callerLp)
      h_spot_per_supply
  nlinarith [h_before_identity, h_after_identity, h_unowned_spot]

theorem pairWalletPortfolio_in_token1_eq_numerator
    (spot : PairWorldState) (w : PairWalletWorldState) :
    0 < spot.reserve0 → 0 < w.pair.totalSupply →
      PairWalletPortfolioValueInToken1 spot w =
        (PairWalletPortfolioValueNumeratorAtSpot spot w : ℚ) /
          ((w.pair.totalSupply : ℚ) * (spot.reserve0 : ℚ)) := by
  intro h_reserve0 h_supply
  have h_reserve0_rat : (spot.reserve0 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp h_reserve0
  have h_supply_rat : (w.pair.totalSupply : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp h_supply
  unfold PairWalletPortfolioValueInToken1 PairWorldTokenValueRat
    PairWorldSpotPriceRat PairWalletPortfolioValueNumeratorAtSpot
    PairWalletCallerTokenValueAtSpot PairWalletSkimmableValueAtSpot
    PairWorldSurplusSpotValueNum PairWorldSpotValueNum
  field_simp
  ring

def pair_wallet_single_caller_history_no_portfolio_profit
    (before after : PairWalletWorldState) : Prop :=
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          OrdinaryPairWalletHistory before after →
            PairWalletPortfolioValueInToken1 before.pair after ≤
              PairWalletPortfolioValueInToken1 before.pair before

theorem wallet_single_caller_history_no_portfolio_profit
    (before after : PairWalletWorldState) :
  pair_wallet_single_caller_history_no_portfolio_profit before after := by
  intro h_good h_supply h_reserve0 h_reserve1 h_history
  have h_nat := pairWalletHistory_no_portfolio_profit
    h_good h_supply h_reserve0 h_reserve1 h_history
  have h_wallet_history := ordinaryPairWalletHistory_history h_history
  rcases pairWalletHistory_preserves_good_and_positive h_good h_supply h_wallet_history
    with ⟨_h_after_good, h_after_supply, _h_after_locked⟩
  have h_before := pairWalletPortfolio_in_token1_eq_numerator
    before.pair before h_reserve0 h_supply
  have h_after := pairWalletPortfolio_in_token1_eq_numerator
    before.pair after h_reserve0 h_after_supply
  rw [h_before, h_after]
  have h_reserve0_rat : (0 : ℚ) < (before.pair.reserve0 : ℚ) := by
    exact_mod_cast h_reserve0
  have h_before_supply_rat : (0 : ℚ) < (before.pair.totalSupply : ℚ) := by
    exact_mod_cast h_supply
  have h_after_supply_rat : (0 : ℚ) < (after.pair.totalSupply : ℚ) := by
    exact_mod_cast h_after_supply
  have h_nat_rat :
      (PairWalletPortfolioValueNumeratorAtSpot before.pair after : ℚ) *
          (before.pair.totalSupply : ℚ) ≤
        (PairWalletPortfolioValueNumeratorAtSpot before.pair before : ℚ) *
          (after.pair.totalSupply : ℚ) := by
    exact_mod_cast h_nat
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h_nat_rat, h_reserve0_rat]

theorem wallet_single_caller_history_no_extraction
    (before after : PairWalletWorldState) :
  pair_wallet_single_caller_history_no_extraction before after := by
  intro h_good h_flowEmpty h_supply h_reserve0 h_reserve1 h_history
  rcases h_flowEmpty with
    ⟨h_before_recv0, h_before_recv1, h_before_recvLp, h_before_give0,
      h_before_give1, h_before_giveLp⟩
  rcases pairWalletHistory_preserves_good_and_positive
      h_good h_supply h_history with
    ⟨h_after_good, h_after_supply, _h_after_locked⟩
  have h_token_raw :=
    pairWalletHistory_flow_token_conserved before.pair
      h_good h_supply h_history
  have h_balance_before :=
    pairWorldBalanceSpotValue_eq_spot_plus_surplus
      (spot := before.pair) (pool := before.pair) h_good.1
  have h_balance_after :=
    pairWorldBalanceSpotValue_eq_spot_plus_surplus
      (spot := before.pair) (pool := after.pair) h_after_good.1
  have h_token_nat :
      after.recv0 * before.pair.reserve1 +
            after.recv1 * before.pair.reserve0 +
            PairWorldSurplusSpotValueNum before.pair after.pair +
            PairWorldSpotValueNum before.pair after.pair =
        PairWorldSpotValueNum before.pair before.pair +
            PairWorldSurplusSpotValueNum before.pair before.pair +
            (after.give0 * before.pair.reserve1 +
              after.give1 * before.pair.reserve0) := by
    rw [h_balance_before, h_balance_after] at h_token_raw
    nlinarith
  have h_lp_raw :=
    pairWalletHistory_flow_lp_conserved h_good h_supply h_history
  have h_lp_nat :
      after.recvLp + after.pairLp + before.pair.totalSupply =
        after.giveLp + before.pairLp + after.pair.totalSupply := by
    nlinarith
  have h_path := pairWalletHistory_pairPath h_history
  have h_k_scaled :=
    pairWorldPath_k_per_supply_never_decreases
      h_good.1 h_supply h_path
  have h_spot_per_supply :=
    pairWorldKPerSupply_spot_value_per_supply
      h_supply h_after_supply h_reserve0 h_reserve1 h_k_scaled
  have h_pairLp_le_supply : before.pairLp ≤ before.pair.totalSupply := by
    rcases h_good with ⟨_h_pair_good, h_wallet⟩
    omega
  let recvN : ℚ :=
    (after.recv0 * before.pair.reserve1 +
      after.recv1 * before.pair.reserve0 : ℚ)
  let giveN : ℚ :=
    (after.give0 * before.pair.reserve1 +
      after.give1 * before.pair.reserve0 : ℚ)
  let surplusF : ℚ :=
    (PairWorldSurplusSpotValueNum before.pair after.pair : ℚ)
  let surplusI : ℚ :=
    (PairWorldSurplusSpotValueNum before.pair before.pair : ℚ)
  let a : ℚ := (PairWorldSpotValueNum before.pair before.pair : ℚ)
  let b : ℚ := (PairWorldSpotValueNum before.pair after.pair : ℚ)
  let s0 : ℚ := (before.pair.reserve0 : ℚ)
  let tSi : ℚ := (before.pair.totalSupply : ℚ)
  let tSf : ℚ := (after.pair.totalSupply : ℚ)
  let rL : ℚ := (after.recvLp : ℚ)
  let gL : ℚ := (after.giveLp : ℚ)
  let pLi : ℚ := (before.pairLp : ℚ)
  let pLf : ℚ := (after.pairLp : ℚ)
  let cLi : ℚ := (before.callerLp : ℚ)
  have h_s0_pos : 0 < s0 := by
    dsimp [s0]
    exact_mod_cast h_reserve0
  have h_tSi_pos : 0 < tSi := by
    dsimp [tSi]
    exact_mod_cast h_supply
  have h_tSf_pos : 0 < tSf := by
    dsimp [tSf]
    exact_mod_cast h_after_supply
  have h_token_eq : recvN + surplusF + b = a + surplusI + giveN := by
    dsimp [recvN, giveN, surplusF, surplusI, a, b]
    exact_mod_cast h_token_nat
  have h_lp_eq : rL + pLf + tSi = gL + pLi + tSf := by
    dsimp [rL, gL, pLi, pLf, tSi, tSf]
    exact_mod_cast h_lp_nat
  have h_k_rat : a * tSf ≤ b * tSi := by
    dsimp [a, b, tSi, tSf]
    exact_mod_cast h_spot_per_supply
  have h_pLi_le_tSi : pLi ≤ tSi := by
    dsimp [pLi, tSi]
    exact_mod_cast h_pairLp_le_supply
  have h_received :
      PairWalletFlowReceivedValueAtSpot before.pair after =
        recvN / s0 + rL * (b / (tSf * s0)) + surplusF / s0 := by
    simp [PairWalletFlowReceivedValueAtSpot, PairWorldTokenValueRat,
      PairWorldLpValueRat, PairWorldSurplusValueRat, PairWorldSpotPriceRat,
      PairWorldSpotValueNum, PairWorldSurplusSpotValueNum, recvN, surplusF,
      b, rL, tSf, s0]
    field_simp [ne_of_gt h_s0_pos, ne_of_gt h_tSf_pos]
  have h_given :
      PairWalletFlowGivenValueAtSpot before.pair after =
        giveN / s0 + gL * (b / (tSf * s0)) := by
    simp [PairWalletFlowGivenValueAtSpot, PairWorldTokenValueRat,
      PairWorldLpValueRat, PairWorldSpotPriceRat, PairWorldSpotValueNum,
      giveN, b, gL, tSf, s0]
    field_simp [ne_of_gt h_s0_pos, ne_of_gt h_tSf_pos]
  have h_initial :
      PairWalletInitialClaimValueAtSpot before.pair before =
        (cLi + pLi) * (a / (tSi * s0)) + surplusI / s0 := by
    simp [PairWalletInitialClaimValueAtSpot, PairWorldLpValueRat,
      PairWorldSurplusValueRat, PairWorldTokenValueRat, PairWorldSpotPriceRat,
      PairWorldSpotValueNum, PairWorldSurplusSpotValueNum, cLi, pLi, a, tSi,
      s0, surplusI]
    field_simp [ne_of_gt h_s0_pos, ne_of_gt h_tSi_pos]
  have h_nonneg_b : 0 ≤ b := by
    dsimp [b]
    positivity
  have h_nonneg_a : 0 ≤ a := by
    dsimp [a]
    positivity
  have h_nonneg_pLi : 0 ≤ pLi := by
    dsimp [pLi]
    positivity
  have h_nonneg_pLf : 0 ≤ pLf := by
    dsimp [pLf]
    positivity
  have h_nonneg_cLi : 0 ≤ cLi := by
    dsimp [cLi]
    positivity
  have h_core :
      recvN / s0 + rL * (b / (tSf * s0)) + surplusF / s0 ≤
        giveN / s0 + gL * (b / (tSf * s0)) +
          ((cLi + pLi) * (a / (tSi * s0)) + surplusI / s0) := by
    have h_scaled :
        (recvN + surplusF) * tSi * tSf + rL * b * tSi ≤
          (giveN + surplusI) * tSi * tSf + gL * b * tSi +
            (cLi + pLi) * a * tSf := by
      have h_diff :
          ((recvN + surplusF) * tSi * tSf + rL * b * tSi) -
              ((giveN + surplusI) * tSi * tSf + gL * b * tSi +
                (cLi + pLi) * a * tSf) =
            a * tSi * tSf - (tSi - pLi) * b * tSi -
              pLf * b * tSi - (cLi + pLi) * a * tSf := by
        have h_token_rearr :
            recvN + surplusF = a + surplusI + giveN - b := by
          nlinarith [h_token_eq]
        have h_lp_rearr :
            rL = gL + pLi + tSf - pLf - tSi := by
          nlinarith [h_lp_eq]
        rw [h_token_rearr, h_lp_rearr]
        ring
      have h_nonneg_unowned : 0 ≤ tSi - pLi := by
        nlinarith [h_pLi_le_tSi]
      have h_unowned_k :
          (tSi - pLi) * a * tSf ≤ (tSi - pLi) * b * tSi := by
        nlinarith [h_k_rat, h_nonneg_unowned]
      have h_rhs_nonpos :
          a * tSi * tSf - (tSi - pLi) * b * tSi -
              pLf * b * tSi - (cLi + pLi) * a * tSf ≤ 0 := by
        have h_split_nonpos :
            a * tSi * tSf - (tSi - pLi) * b * tSi -
                pLi * a * tSf ≤ 0 := by
          nlinarith [h_unowned_k]
        have h_pLf_term : 0 ≤ pLf * b * tSi := by
          exact mul_nonneg (mul_nonneg h_nonneg_pLf h_nonneg_b)
            (le_of_lt h_tSi_pos)
        have h_cLi_term : 0 ≤ cLi * a * tSf := by
          exact mul_nonneg (mul_nonneg h_nonneg_cLi h_nonneg_a)
            (le_of_lt h_tSf_pos)
        nlinarith [h_split_nonpos, h_pLf_term, h_cLi_term]
      linarith [h_diff, h_rhs_nonpos]
    have h_lhs :
        recvN / s0 + rL * (b / (tSf * s0)) + surplusF / s0 =
          ((recvN + surplusF) * tSi * tSf + rL * b * tSi) /
            (s0 * tSi * tSf) := by
      field_simp [ne_of_gt h_s0_pos, ne_of_gt h_tSi_pos,
        ne_of_gt h_tSf_pos]
      ring
    have h_rhs :
        giveN / s0 + gL * (b / (tSf * s0)) +
            ((cLi + pLi) * (a / (tSi * s0)) + surplusI / s0) =
          ((giveN + surplusI) * tSi * tSf + gL * b * tSi +
              (cLi + pLi) * a * tSf) / (s0 * tSi * tSf) := by
      field_simp [ne_of_gt h_s0_pos, ne_of_gt h_tSi_pos,
        ne_of_gt h_tSf_pos]
      ring
    rw [h_lhs, h_rhs]
    exact div_le_div_of_nonneg_right h_scaled (by positivity)
  rw [h_received, h_given, h_initial]
  exact h_core

theorem pairEconomicActionConcreteStep_wallet
    {caller : Address} {before after : PairWalletWorldState} :
  PairEconomicActionConcreteStep caller before after →
    ∃ action, PairWalletStep action before after ∧
      PairWalletActionOrdinary action before after := by
  intro h_step
  cases h_step with
  | mint toAddr preTokens s result liquidity hRun hSuccess hBefore
      hAfter hToAddr hReserve0 hReserve1 hAmount0 hAmount1
      hFirstExternal hLaterExternal hFirstGuards hLaterGuards =>
      subst before
      subst after
      subst result
      refine ⟨PairWalletAction.callerMint
        (mintAmount0 s).val (mintAmount1 s).val liquidity.val, ?_, by trivial⟩
      have hPair :
          PairWorldStep
            (PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val liquidity.val)
            (pairWorldFromConcreteAndTokens preTokens s)
            (pairWorldFromConcreteAndTokens
              (pairTokenWorldAfterCall preTokens s ((mint toAddr).run s))
              ((mint toAddr).run s).snd) := by
        by_cases hSupplyZero : s.storage totalSupplySlot.slot = 0
        · rcases hFirstGuards hSupplyZero with
            ⟨hLiquidity, hProduct, hRoot⟩
          have hSuccessFirst :
              (mint toAddr).run s =
                ContractResult.success (mintFirstLiquidity s)
                  ((mint toAddr).run s).snd := by
            simpa [hLiquidity] using hSuccess
          simpa [hLiquidity] using
            (first_mint_success_reaches_expected_pair_state
              toAddr preTokens s rfl hSuccessFirst (hFirstExternal hSupplyZero)
              hSupplyZero hReserve0 hReserve1 hAmount0 hAmount1 hProduct hRoot)
        · rcases hLaterGuards hSupplyZero with
            ⟨hSupplyPos, hReserve0Pos, hReserve1Pos, hLiquidity,
              hRatio0, hRatio1⟩
          exact later_mint_success_reaches_expected_pair_state
            toAddr preTokens s liquidity rfl hSuccess
            (hLaterExternal hSupplyZero) hSupplyPos hReserve0Pos hReserve1Pos
            hReserve0 hReserve1 hAmount0 hAmount1 hLiquidity hRatio0 hRatio1
      have hBeforeTokens :
          pairTokenBalancesMatchWorld preTokens s (pairWorldBeforeMintRun s) := by
        by_cases hSupplyZero : s.storage totalSupplySlot.slot = 0
        · exact (hFirstExternal hSupplyZero).1
        · exact (hLaterExternal hSupplyZero).1
      have hBeforeWorld :
          pairWorldFromConcreteAndTokens preTokens s =
            pairWorldBeforeMintRun s := by
        exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
          (pairWorldBeforeMintRun s) hBeforeTokens
          (by simp [pairConcreteStorageMatchesWorld, pairWorldBeforeMintRun])
      have hTransfers :
          pairTransfersAfterCall s ((mint toAddr).run s) = [] := by
        exact mint_success_pairTransfers toAddr s liquidity hSuccess
          hReserve0 hReserve1 hAmount0 hAmount1 hFirstGuards
          (by
            intro hSupplyNonzero
            rcases hLaterGuards hSupplyNonzero with
              ⟨_hSupplyPos, hReserve0Pos, hReserve1Pos, hLiquidity,
                _hRatio0, _hRatio1⟩
            exact ⟨hReserve0Pos, hReserve1Pos, hLiquidity⟩)
      have hTokens :
          pairTokenWorldAfterCall preTokens s ((mint toAddr).run s) =
            preTokens := by
        rw [pairTokenWorldAfterCall_eq_pairTransfers, hTransfers]
        simp [pairTokenWorldAfterPairTransfers]
      have hToken0Addr :
          ((mint toAddr).run s).snd.storageAddr token0Slot.slot =
            s.storageAddr token0Slot.slot := by
        exact mint_run_storageAddr_frame toAddr s token0Slot.slot
      have hToken1Addr :
          ((mint toAddr).run s).snd.storageAddr token1Slot.slot =
            s.storageAddr token1Slot.slot := by
        exact mint_run_storageAddr_frame toAddr s token1Slot.slot
      have hLp :
          (((mint toAddr).run s).snd.storageMap balancesSlot.slot caller).val =
            (s.storageMap balancesSlot.slot caller).val + liquidity.val := by
        exact mint_success_caller_lp_add toAddr caller s liquidity hToAddr
          hSuccess hReserve0 hReserve1 hAmount0 hAmount1 hFirstGuards
          (by
            intro hSupplyNonzero
            rcases hLaterGuards hSupplyNonzero with
              ⟨_hSupplyPos, hReserve0Pos, hReserve1Pos, hLiquidity,
                _hRatio0, _hRatio1⟩
            exact ⟨hReserve0Pos, hReserve1Pos, hLiquidity⟩)
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using hPair
      constructor
      · change
          (mintAmount0 s).val =
            PairWorldSurplus0 (pairWorldFromConcreteAndTokens preTokens s)
        rw [hBeforeWorld]
        simpa [pairWalletFromConcreteAndTokens, pairWorldBeforeMintRun,
          PairWorldSurplus0, mintAmount0] using
          (Verity.Core.Uint256.sub_eq_of_le
            (a := observedBalance0 s) (b := s.storage reserve0Slot.slot)
            hReserve0)
      constructor
      · change
          (mintAmount1 s).val =
            PairWorldSurplus1 (pairWorldFromConcreteAndTokens preTokens s)
        rw [hBeforeWorld]
        simpa [pairWalletFromConcreteAndTokens, pairWorldBeforeMintRun,
          PairWorldSurplus1, mintAmount1] using
          (Verity.Core.Uint256.sub_eq_of_le
            (a := observedBalance1 s) (b := s.storage reserve1Slot.slot)
            hReserve1)
      constructor
      · simp only [pairWalletFromConcreteAndTokens, callerTokenBalance0, pairToken0,
          pairWalletWithStepFlows, hTokens]
        rw [hToken0Addr]
      constructor
      · simp only [pairWalletFromConcreteAndTokens, callerTokenBalance1, pairToken1,
          pairWalletWithStepFlows, hTokens]
        rw [hToken1Addr]
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using hLp
      · simp [pairWalletFromConcreteAndTokens]
  | burn toAddr preTokens s transferLiquidity transferResult burnResult
      hTransferRun _hTransferSuccess hBurnRun hSuccess hBefore hAfter hToAddr
      hSender hCallerNeSelf hPairSelfNoLp hTransferBalance hTransferNoOverflow
      hExternal hPostBalances hLiquidityPos hSupplyPos hLiquidityLe
      hLockedRemaining hAmount0Pos hAmount1Pos hAmount0Le hAmount1Le hBound0
      hBound1 hRatio0 hRatio1 hTokenDistinct hCallerToken0Add
      hCallerToken1Add =>
      subst before
      subst after
      subst toAddr
      refine ⟨PairWalletAction.callerBurn
        (burnAmount0 transferResult.snd).val
        (burnAmount1 transferResult.snd).val
        (burnLiquidity transferResult.snd).val
        (burnLiquidity transferResult.snd).val, ?_, by
          simp [PairWalletActionOrdinary]⟩
      have hTransferStorage :
          transferResult.snd.storage = s.storage := by
        rw [hTransferRun]
        exact transfer_keeps_pool_storage (pairSelf s) transferLiquidity s
      have hTransferToken0Addr :
          transferResult.snd.storageAddr token0Slot.slot =
            s.storageAddr token0Slot.slot := by
        rw [hTransferRun]
        exact transfer_run_storageAddr_frame (pairSelf s) transferLiquidity s
          token0Slot.slot
      have hTransferToken1Addr :
          transferResult.snd.storageAddr token1Slot.slot =
            s.storageAddr token1Slot.slot := by
        rw [hTransferRun]
        exact transfer_run_storageAddr_frame (pairSelf s) transferLiquidity s
          token1Slot.slot
      have hTransferThis :
          transferResult.snd.thisAddress = s.thisAddress := by
        rw [hTransferRun]
        exact transfer_run_thisAddress_frame (pairSelf s) transferLiquidity s
      have hTransferToken0AddrRaw :
          transferResult.snd.storageAddr 1 = s.storageAddr 1 := by
        simpa [token0Slot, UniswapV2PairBase.token0Slot] using hTransferToken0Addr
      have hTransferToken1AddrRaw :
          transferResult.snd.storageAddr 2 = s.storageAddr 2 := by
        simpa [token1Slot, UniswapV2PairBase.token1Slot] using hTransferToken1Addr
      have hPairSelfTransfer :
          pairSelf transferResult.snd = pairSelf s := by
        simp [pairSelf, hTransferThis]
      have hCallerNeSelfTransfer :
          caller ≠ pairSelf transferResult.snd := by
        rwa [hPairSelfTransfer]
      have hSelfNeCallerTransfer :
          pairSelf transferResult.snd ≠ caller := by
        intro h_eq
        exact hCallerNeSelfTransfer h_eq.symm
      have hTransferPairWorld :
          pairWorldFromConcreteAndTokens preTokens s =
            pairWorldFromConcreteAndTokens preTokens transferResult.snd := by
        simp [pairWorldFromConcreteAndTokens, pairTokenBalance0,
          pairTokenBalance1, pairToken0, pairToken1, pairSelf,
          pairWorldLockedLiquidity, hTransferStorage, hTransferToken0Addr,
          hTransferToken1Addr, hTransferThis]
        constructor
        · rw [hTransferToken0AddrRaw]
        · rw [hTransferToken1AddrRaw]
      have hPair :
          PairWorldStep
            (PairWorldAction.burn
              (burnAmount0 transferResult.snd).val
              (burnAmount1 transferResult.snd).val
              (burnLiquidity transferResult.snd).val)
            (pairWorldFromConcreteAndTokens preTokens s)
            (pairWorldFromConcreteAndTokens
              (pairTokenWorldAfterCall preTokens transferResult.snd burnResult)
              burnResult.snd) := by
        have hExternalRun :
            pairBurnExternalTokenBalancesMatchCall preTokens transferResult.snd
              ((burn caller).run transferResult.snd) := by
          rw [← hBurnRun]
          exact hExternal
        have hPostBalancesRun :
            pairPostCallSelfBalancesMatch transferResult.snd
              ((burn caller).run transferResult.snd).snd
              (burnBalance0After transferResult.snd)
              (burnBalance1After transferResult.snd) := by
          rw [← hBurnRun]
          exact hPostBalances
        have hBurnSuccessRun :
            (burn caller).run transferResult.snd =
              ContractResult.success
                (burnAmount0 transferResult.snd, burnAmount1 transferResult.snd)
                ((burn caller).run transferResult.snd).snd := by
          rw [← hBurnRun]
          exact hSuccess
        have hBurnPair :=
          burn_success_reaches_expected_pair_state caller preTokens
            transferResult.snd rfl hBurnSuccessRun hExternalRun
            hPostBalancesRun hLiquidityPos hSupplyPos hLiquidityLe hLockedRemaining
            hAmount0Pos hAmount1Pos hAmount0Le hAmount1Le hBound0 hBound1
            hRatio0 hRatio1
        have hBurnPairResult :
            PairWorldStep
              (PairWorldAction.burn
                (burnAmount0 transferResult.snd).val
                (burnAmount1 transferResult.snd).val
                (burnLiquidity transferResult.snd).val)
              (pairWorldFromConcreteAndTokens preTokens transferResult.snd)
              (pairWorldFromConcreteAndTokens
                (pairTokenWorldAfterCall preTokens transferResult.snd burnResult)
                burnResult.snd) := by
          rw [hBurnRun]
          exact hBurnPair
        rwa [hTransferPairWorld]
      have hBurnSuccessRun :
          (burn caller).run transferResult.snd =
            ContractResult.success
              (burnAmount0 transferResult.snd, burnAmount1 transferResult.snd)
              ((burn caller).run transferResult.snd).snd := by
        rw [← hBurnRun]
        exact hSuccess
      have hTransfers :
          pairTransfersAfterCall transferResult.snd burnResult =
            [{ token := pairToken0 transferResult.snd,
               fromAddr := pairSelf transferResult.snd, toAddr := caller,
               amount := burnAmount0 transferResult.snd },
             { token := pairToken1 transferResult.snd,
               fromAddr := pairSelf transferResult.snd, toAddr := caller,
               amount := burnAmount1 transferResult.snd }] := by
        rw [hBurnRun]
        exact burn_success_pairTransfers caller transferResult.snd
          hBurnSuccessRun hPostBalances hLiquidityPos hSupplyPos hLiquidityLe
          hLockedRemaining hAmount0Pos hAmount1Pos hAmount0Le hAmount1Le hBound0
          hBound1
      have hTokens :
          pairTokenWorldAfterCall preTokens transferResult.snd burnResult =
            pairTokenWorldAfterPairTransfers preTokens
              [{ token := pairToken0 transferResult.snd,
                 fromAddr := pairSelf transferResult.snd, toAddr := caller,
                 amount := burnAmount0 transferResult.snd },
               { token := pairToken1 transferResult.snd,
                 fromAddr := pairSelf transferResult.snd, toAddr := caller,
                 amount := burnAmount1 transferResult.snd }] := by
        rw [pairTokenWorldAfterCall_eq_pairTransfers, hTransfers]
      have hBurnToken0Addr :
          burnResult.snd.storageAddr token0Slot.slot =
            transferResult.snd.storageAddr token0Slot.slot := by
        rw [hBurnRun]
        exact burn_run_storageAddr_frame caller transferResult.snd token0Slot.slot
      have hBurnToken1Addr :
          burnResult.snd.storageAddr token1Slot.slot =
            transferResult.snd.storageAddr token1Slot.slot := by
        rw [hBurnRun]
        exact burn_run_storageAddr_frame caller transferResult.snd token1Slot.slot
      have hBurnLpFrame :
          burnResult.snd.storageMap balancesSlot.slot caller =
            transferResult.snd.storageMap balancesSlot.slot caller := by
        rw [hBurnRun]
        exact burn_success_caller_lp_frame caller caller transferResult.snd
          hBurnSuccessRun hPostBalances hLiquidityPos hSupplyPos hLiquidityLe
          hLockedRemaining hAmount0Pos hAmount1Pos hAmount0Le hAmount1Le hBound0
          hBound1 hCallerNeSelfTransfer
      have hTransferLpSub :
          transferResult.snd.storageMap balancesSlot.slot caller =
            s.storageMap balancesSlot.slot caller - transferLiquidity := by
        rw [hTransferRun]
        exact transfer_caller_lp_sub caller transferLiquidity s hSender
          hCallerNeSelf hTransferBalance hTransferNoOverflow
      have hTransferPairLpAdd :
          transferResult.snd.storageMap balancesSlot.slot (pairSelf s) =
            s.storageMap balancesSlot.slot (pairSelf s) + transferLiquidity := by
        rw [hTransferRun]
        exact transfer_pairSelf_lp_add caller transferLiquidity s hSender
          hCallerNeSelf hTransferBalance hTransferNoOverflow
      have hBurnLiquidityEq :
          burnLiquidity transferResult.snd =
            s.storageMap balancesSlot.slot (pairSelf s) + transferLiquidity := by
        unfold burnLiquidity
        rw [hPairSelfTransfer]
        exact hTransferPairLpAdd
      have hBurnLiquidityValEq :
          (burnLiquidity transferResult.snd).val = transferLiquidity.val := by
        have h_val := congrArg (fun x : Uint256 => x.val) hBurnLiquidityEq
        rw [hPairSelfNoLp] at h_val
        simpa using h_val
      have hTokenDistinctSymm :
          pairToken1 transferResult.snd ≠ pairToken0 transferResult.snd := by
        intro h_eq
        exact hTokenDistinct h_eq.symm
      have hCallerNeSelfRaw :
          caller ≠ transferResult.snd.thisAddress := by
        simpa [pairSelf] using hCallerNeSelfTransfer
      have hSelfNeCallerRaw :
          transferResult.snd.thisAddress ≠ caller := by
        simpa [pairSelf] using hSelfNeCallerTransfer
      have hTokenDistinctRaw :
          transferResult.snd.storageAddr 1 ≠ transferResult.snd.storageAddr 2 := by
        simpa [pairToken0, pairToken1, token0Slot, token1Slot,
          UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot]
          using hTokenDistinct
      have hTokenDistinctRawSymm :
          transferResult.snd.storageAddr 2 ≠ transferResult.snd.storageAddr 1 := by
        intro h_eq
        exact hTokenDistinctRaw h_eq.symm
      have hCaller0Before :
          (callerTokenBalance0 caller preTokens transferResult.snd).val =
            (callerTokenBalance0 caller preTokens s).val := by
        simp only [callerTokenBalance0, pairToken0]
        rw [hTransferToken0Addr]
      have hCaller1Before :
          (callerTokenBalance1 caller preTokens transferResult.snd).val =
            (callerTokenBalance1 caller preTokens s).val := by
        simp only [callerTokenBalance1, pairToken1]
        rw [hTransferToken1Addr]
      have hCaller0 :
          (callerTokenBalance0 caller
            (pairTokenWorldAfterCall preTokens transferResult.snd burnResult)
            burnResult.snd).val =
            (callerTokenBalance0 caller preTokens transferResult.snd).val +
              (burnAmount0 transferResult.snd).val := by
        have h_add :=
          Core.Uint256.add_eq_of_lt
            (a := callerTokenBalance0 caller preTokens transferResult.snd)
            (b := burnAmount0 transferResult.snd) hCallerToken0Add
        simp only [callerTokenBalance0, pairToken0, hTokens]
        rw [hBurnToken0Addr]
        simpa [pairTokenWorldAfterPairTransfers, pairTokenWorldAfterPairTransfer,
          pairTokenWorldAfterTransfer, hSelfNeCallerTransfer,
          hCallerNeSelfTransfer, hTokenDistinct, hTokenDistinctSymm,
          hSelfNeCallerRaw, hCallerNeSelfRaw, hTokenDistinctRaw,
          hTokenDistinctRawSymm, callerTokenBalance0, pairToken0]
          using h_add
      have hCaller1 :
          (callerTokenBalance1 caller
            (pairTokenWorldAfterCall preTokens transferResult.snd burnResult)
            burnResult.snd).val =
            (callerTokenBalance1 caller preTokens transferResult.snd).val +
              (burnAmount1 transferResult.snd).val := by
        have h_add :=
          Core.Uint256.add_eq_of_lt
            (a := callerTokenBalance1 caller preTokens transferResult.snd)
            (b := burnAmount1 transferResult.snd) hCallerToken1Add
        simp only [callerTokenBalance1, pairToken1, hTokens]
        rw [hBurnToken1Addr]
        simpa [pairTokenWorldAfterPairTransfers, pairTokenWorldAfterPairTransfer,
          pairTokenWorldAfterTransfer, hSelfNeCallerTransfer,
          hCallerNeSelfTransfer, hTokenDistinct, hTokenDistinctSymm,
          hSelfNeCallerRaw, hCallerNeSelfRaw, hTokenDistinctRaw,
          hTokenDistinctRawSymm, callerTokenBalance1, pairToken1]
          using h_add
      have hLp :
          (burnResult.snd.storageMap balancesSlot.slot caller).val =
            (s.storageMap balancesSlot.slot caller).val -
              (burnLiquidity transferResult.snd).val := by
        have hBurnLpFrameVal :=
          congrArg (fun x : Uint256 => x.val) hBurnLpFrame
        have hTransferLpSubVal :=
          congrArg (fun x : Uint256 => x.val) hTransferLpSub
        have hSubVal :
            (s.storageMap balancesSlot.slot caller - transferLiquidity).val =
              (s.storageMap balancesSlot.slot caller).val -
                transferLiquidity.val := by
          exact Core.Uint256.sub_eq_of_le
            (a := s.storageMap balancesSlot.slot caller)
            (b := transferLiquidity) hTransferBalance
        calc
          (burnResult.snd.storageMap balancesSlot.slot caller).val =
              (transferResult.snd.storageMap balancesSlot.slot caller).val := by
                simpa using hBurnLpFrameVal
          _ = (s.storageMap balancesSlot.slot caller - transferLiquidity).val := by
                simpa using hTransferLpSubVal
          _ = (s.storageMap balancesSlot.slot caller).val -
                transferLiquidity.val := hSubVal
          _ = (s.storageMap balancesSlot.slot caller).val -
                (burnLiquidity transferResult.snd).val := by
                rw [hBurnLiquidityValEq]
      constructor
      · change (s.storageMap balancesSlot.slot caller).val ≥
          (burnLiquidity transferResult.snd).val
        rw [hBurnLiquidityValEq]
        exact hTransferBalance
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using hPair
      constructor
      · simpa [pairWalletFromConcreteAndTokens, hCaller0Before] using hCaller0
      constructor
      · simpa [pairWalletFromConcreteAndTokens, hCaller1Before] using hCaller1
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using hLp
      · simp [pairWalletFromConcreteAndTokens, hBurnLiquidityValEq]
  | swap amount0Out amount1Out toAddr data balance0Now balance1Now preTokens
      s result hRun hSuccess hBefore hAfter hExternal hObserved0 hObserved1
      hToAddr hCallerNeSelf hTokenDistinct hCallerToken0Add hCallerToken1Add
      hPostBalances hAmount0OutLt hAmount1OutLt hInput hBalance0 hBalance1
      hBound0 hBound1 hFee0 hFee1 hAdjustedK =>
      subst before
      subst after
      subst result
      subst toAddr
      refine ⟨PairWalletAction.callerSwap
        0 0 amount0Out.val amount1Out.val, ?_, by
          simp [PairWalletActionOrdinary]⟩
      have hPair :
          PairWorldStep
            (PairWorldAction.swap
              (swapAmount0In amount0Out balance0Now s).val
              (swapAmount1In amount1Out balance1Now s).val
              amount0Out.val amount1Out.val)
            (pairWorldFromConcreteAndTokens preTokens s)
            (pairWorldFromConcreteAndTokens
              (pairTokenWorldAfterCall preTokens s
                ((swap amount0Out amount1Out caller data).run s))
              ((swap amount0Out amount1Out caller data).run s).snd) := by
        exact swap_success_reaches_expected_pair_state
          amount0Out amount1Out caller data balance0Now balance1Now preTokens s
          rfl hSuccess hExternal hPostBalances hAmount0OutLt hAmount1OutLt
          hInput hBalance0 hBalance1 hBound0 hBound1 hFee0 hFee1 hAdjustedK
      have hBeforeWorld :
          pairWorldFromConcreteAndTokens preTokens s =
            pairWorldFromConcreteState s := by
        exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
          (pairWorldFromConcreteState s) hExternal.1
          (by simp [pairConcreteStorageMatchesWorld, pairWorldFromConcreteState])
      have hTransfers :
          pairTransfersAfterCall s
              ((swap amount0Out amount1Out caller data).run s) =
            (if amount0Out > 0 then
              [{ token := pairToken0 s, fromAddr := pairSelf s, toAddr := caller,
                 amount := amount0Out }]
            else []) ++
            (if amount1Out > 0 then
              [{ token := pairToken1 s, fromAddr := pairSelf s, toAddr := caller,
                 amount := amount1Out }]
            else []) := by
        exact swap_success_pairTransfers amount0Out amount1Out caller data s hSuccess
      have hTokens :
          pairTokenWorldAfterCall preTokens s
              ((swap amount0Out amount1Out caller data).run s) =
            pairTokenWorldAfterPairTransfers preTokens
              ((if amount0Out > 0 then
                [{ token := pairToken0 s, fromAddr := pairSelf s, toAddr := caller,
                   amount := amount0Out }]
              else []) ++
              (if amount1Out > 0 then
                [{ token := pairToken1 s, fromAddr := pairSelf s, toAddr := caller,
                   amount := amount1Out }]
              else [])) := by
        rw [pairTokenWorldAfterCall_eq_pairTransfers, hTransfers]
      have hToken0Addr :
          ((swap amount0Out amount1Out caller data).run s).snd.storageAddr
              token0Slot.slot =
            s.storageAddr token0Slot.slot := by
        exact swap_run_storageAddr_frame amount0Out amount1Out caller data s
          token0Slot.slot
      have hToken1Addr :
          ((swap amount0Out amount1Out caller data).run s).snd.storageAddr
              token1Slot.slot =
            s.storageAddr token1Slot.slot := by
        exact swap_run_storageAddr_frame amount0Out amount1Out caller data s
          token1Slot.slot
      have hLp :
          ((swap amount0Out amount1Out caller data).run s).snd.storageMap
              balancesSlot.slot caller =
            s.storageMap balancesSlot.slot caller := by
        exact swap_caller_lp_frame amount0Out amount1Out caller caller data s
      have hSelfNeCaller : pairSelf s ≠ caller := by
        intro h_eq
        exact hCallerNeSelf h_eq.symm
      have hTokenDistinctSymm : pairToken1 s ≠ pairToken0 s := by
        intro h_eq
        exact hTokenDistinct h_eq.symm
      have hCallerNeSelfRaw : caller ≠ s.thisAddress := by
        simpa [pairSelf] using hCallerNeSelf
      have hSelfNeCallerRaw : s.thisAddress ≠ caller := by
        simpa [pairSelf] using hSelfNeCaller
      have hTokenDistinctRaw : s.storageAddr 1 ≠ s.storageAddr 2 := by
        simpa [pairToken0, pairToken1, token0Slot, token1Slot,
          UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot]
          using hTokenDistinct
      have hTokenDistinctRawSymm : s.storageAddr 2 ≠ s.storageAddr 1 := by
        intro h_eq
        exact hTokenDistinctRaw h_eq.symm
      have hAccounts :=
        swap_success_accounts_for_input_and_output
          amount0Out amount1Out caller data balance0Now balance1Now s
          rfl hSuccess hAmount0OutLt hAmount1OutLt hInput hBalance0 hBalance1
          hBound0 hBound1 hFee0 hFee1 hAdjustedK
      have hBalance0Account :
          balance0Now.val + amount0Out.val =
            (s.storage reserve0Slot.slot).val +
              (swapAmount0In amount0Out balance0Now s).val := by
        simpa [pairWorldAfterSwapRun, pairWorldFromConcreteState] using hAccounts.1
      have hBalance1Account :
          balance1Now.val + amount1Out.val =
            (s.storage reserve1Slot.slot).val +
              (swapAmount1In amount1Out balance1Now s).val := by
        simpa [pairWorldAfterSwapRun, pairWorldFromConcreteState] using hAccounts.2
      have hObserved0Account :
          (observedBalance0 s).val =
            (s.storage reserve0Slot.slot).val +
              (swapAmount0In amount0Out balance0Now s).val := by
        omega
      have hObserved1Account :
          (observedBalance1 s).val =
            (s.storage reserve1Slot.slot).val +
              (swapAmount1In amount1Out balance1Now s).val := by
        omega
      have hCaller0 :
          (callerTokenBalance0 caller
            (pairTokenWorldAfterCall preTokens s
              ((swap amount0Out amount1Out caller data).run s))
            ((swap amount0Out amount1Out caller data).run s).snd).val =
            (callerTokenBalance0 caller preTokens s).val + amount0Out.val := by
        by_cases h0 : amount0Out > 0
        · by_cases h1 : amount1Out > 0
          · have h_add :=
              Core.Uint256.add_eq_of_lt
                (a := amount0Out)
                (b := callerTokenBalance0 caller preTokens s)
                (by simpa [Nat.add_comm] using hCallerToken0Add)
            simp only [callerTokenBalance0, pairToken0, hTokens]
            rw [hToken0Addr]
            simpa [pairTokenWorldAfterPairTransfers,
              pairTokenWorldAfterPairTransfer, pairTokenWorldAfterTransfer,
              h0, h1, hSelfNeCaller, hCallerNeSelf, hTokenDistinct,
              hTokenDistinctSymm, hSelfNeCallerRaw, hCallerNeSelfRaw,
              hTokenDistinctRaw, hTokenDistinctRawSymm, callerTokenBalance0,
              pairToken0, Nat.add_comm] using h_add
          · have h_add :=
              Core.Uint256.add_eq_of_lt
                (a := amount0Out)
                (b := callerTokenBalance0 caller preTokens s)
                (by simpa [Nat.add_comm] using hCallerToken0Add)
            simp only [callerTokenBalance0, pairToken0, hTokens]
            rw [hToken0Addr]
            simpa [pairTokenWorldAfterPairTransfers,
              pairTokenWorldAfterPairTransfer, pairTokenWorldAfterTransfer,
              h0, h1, hSelfNeCaller, hCallerNeSelf, hTokenDistinct,
              hTokenDistinctSymm, hSelfNeCallerRaw, hCallerNeSelfRaw,
              hTokenDistinctRaw, hTokenDistinctRawSymm, callerTokenBalance0,
              pairToken0, Nat.add_comm] using h_add
        · have h0Val : amount0Out.val = 0 := by
            by_contra h_ne
            have h_pos : amount0Out > 0 := by
              change 0 < amount0Out.val
              omega
            exact h0 h_pos
          by_cases h1 : amount1Out > 0
          · simp only [callerTokenBalance0, pairToken0, hTokens]
            rw [hToken0Addr]
            simp [pairTokenWorldAfterPairTransfers,
              pairTokenWorldAfterPairTransfer, pairTokenWorldAfterTransfer,
              h0, h1, hSelfNeCaller, hCallerNeSelf, hTokenDistinct,
              hTokenDistinctSymm, hSelfNeCallerRaw, hCallerNeSelfRaw,
              hTokenDistinctRaw, hTokenDistinctRawSymm, callerTokenBalance0,
              pairToken0, h0Val]
          · simp only [callerTokenBalance0, pairToken0, hTokens]
            rw [hToken0Addr]
            simp [pairTokenWorldAfterPairTransfers,
              pairTokenWorldAfterPairTransfer, pairTokenWorldAfterTransfer,
              h0, h1, hSelfNeCaller, hCallerNeSelf, hTokenDistinct,
              hTokenDistinctSymm, hSelfNeCallerRaw, hCallerNeSelfRaw,
              hTokenDistinctRaw, hTokenDistinctRawSymm, callerTokenBalance0,
              pairToken0, h0Val]
      have hCaller1 :
          (callerTokenBalance1 caller
            (pairTokenWorldAfterCall preTokens s
              ((swap amount0Out amount1Out caller data).run s))
            ((swap amount0Out amount1Out caller data).run s).snd).val =
            (callerTokenBalance1 caller preTokens s).val + amount1Out.val := by
        by_cases h0 : amount0Out > 0
        · by_cases h1 : amount1Out > 0
          · have h_add :=
              Core.Uint256.add_eq_of_lt
                (a := amount1Out)
                (b := callerTokenBalance1 caller preTokens s)
                (by simpa [Nat.add_comm] using hCallerToken1Add)
            simp only [callerTokenBalance1, pairToken1, hTokens]
            rw [hToken1Addr]
            simpa [pairTokenWorldAfterPairTransfers,
              pairTokenWorldAfterPairTransfer, pairTokenWorldAfterTransfer,
              h0, h1, hSelfNeCaller, hCallerNeSelf, hTokenDistinct,
              hTokenDistinctSymm, hSelfNeCallerRaw, hCallerNeSelfRaw,
              hTokenDistinctRaw, hTokenDistinctRawSymm, callerTokenBalance1,
              pairToken1, Nat.add_comm] using h_add
          · have h1Val : amount1Out.val = 0 := by
              by_contra h_ne
              have h_pos : amount1Out > 0 := by
                change 0 < amount1Out.val
                omega
              exact h1 h_pos
            simp only [callerTokenBalance1, pairToken1, hTokens]
            rw [hToken1Addr]
            simp [pairTokenWorldAfterPairTransfers,
              pairTokenWorldAfterPairTransfer, pairTokenWorldAfterTransfer,
              h0, h1, hSelfNeCaller, hCallerNeSelf, hTokenDistinct,
              hTokenDistinctSymm, hSelfNeCallerRaw, hCallerNeSelfRaw,
              hTokenDistinctRaw, hTokenDistinctRawSymm, callerTokenBalance1,
              pairToken1, h1Val]
        · by_cases h1 : amount1Out > 0
          · have h_add :=
              Core.Uint256.add_eq_of_lt
                (a := amount1Out)
                (b := callerTokenBalance1 caller preTokens s)
                (by simpa [Nat.add_comm] using hCallerToken1Add)
            simp only [callerTokenBalance1, pairToken1, hTokens]
            rw [hToken1Addr]
            simpa [pairTokenWorldAfterPairTransfers,
              pairTokenWorldAfterPairTransfer, pairTokenWorldAfterTransfer,
              h0, h1, hSelfNeCaller, hCallerNeSelf, hTokenDistinct,
              hTokenDistinctSymm, hSelfNeCallerRaw, hCallerNeSelfRaw,
              hTokenDistinctRaw, hTokenDistinctRawSymm, callerTokenBalance1,
              pairToken1, Nat.add_comm] using h_add
          · have h1Val : amount1Out.val = 0 := by
              by_contra h_ne
              have h_pos : amount1Out > 0 := by
                change 0 < amount1Out.val
                omega
              exact h1 h_pos
            simp only [callerTokenBalance1, pairToken1, hTokens]
            rw [hToken1Addr]
            simp [pairTokenWorldAfterPairTransfers,
              pairTokenWorldAfterPairTransfer, pairTokenWorldAfterTransfer,
              h0, h1, hSelfNeCaller, hCallerNeSelf, hTokenDistinct,
              hTokenDistinctSymm, hSelfNeCallerRaw, hCallerNeSelfRaw,
              hTokenDistinctRaw, hTokenDistinctRawSymm, callerTokenBalance1,
              pairToken1, h1Val]
      have hAmount0InSurplus :
          (swapAmount0In amount0Out balance0Now s).val =
            PairWorldSurplus0 (pairWorldFromConcreteAndTokens preTokens s) := by
        rw [hBeforeWorld]
        change
          (swapAmount0In amount0Out balance0Now s).val =
            (observedBalance0 s).val - (s.storage reserve0Slot.slot).val
        omega
      have hAmount1InSurplus :
          (swapAmount1In amount1Out balance1Now s).val =
            PairWorldSurplus1 (pairWorldFromConcreteAndTokens preTokens s) := by
        rw [hBeforeWorld]
        change
          (swapAmount1In amount1Out balance1Now s).val =
            (observedBalance1 s).val - (s.storage reserve1Slot.slot).val
        omega
      constructor
      · convert hPair using 1
        rw [hAmount0InSurplus, hAmount1InSurplus]
        simp [pairWalletFromConcreteAndTokens]
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using hCaller0
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using hCaller1
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using congrArg (fun x => x.val) hLp
      · simp [pairWalletFromConcreteAndTokens]
  | skim toAddr preTokens s result hRun hSuccess hBefore hAfter
      hExternal hToAddr hCallerNeSelf hTokenDistinct hCallerToken0Add
      hCallerToken1Add =>
      subst before
      subst after
      subst result
      subst toAddr
      refine ⟨PairWalletAction.callerSkimReceive
        (PairWorldSurplus0 (pairWorldFromConcreteAndTokens preTokens s))
        (PairWorldSurplus1 (pairWorldFromConcreteAndTokens preTokens s)), ?_,
        by trivial⟩
      have hPair :
          PairWorldStep PairWorldAction.skim
            (pairWorldFromConcreteAndTokens preTokens s)
            (pairWorldFromConcreteAndTokens
              (pairTokenWorldAfterCall preTokens s ((skim caller).run s))
              ((skim caller).run s).snd) := by
        exact skim_success_reaches_expected_pair_state caller preTokens s
          ((skim caller).run s) rfl hSuccess hExternal
      have hBeforeWorld :
          pairWorldFromConcreteAndTokens preTokens s =
            pairWorldFromConcreteState s := by
        exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
          (pairWorldFromConcreteState s) hExternal.1
          (by simp [pairConcreteStorageMatchesWorld, pairWorldFromConcreteState])
      rcases skim_success_run_implies_balances_back_reserves caller s
          ((skim caller).run s) rfl hSuccess with ⟨hReserve0, hReserve1⟩
      have hSurplus0 :
          PairWorldSurplus0 (pairWorldFromConcreteAndTokens preTokens s) =
            (skimExcess0 s).val := by
        rw [hBeforeWorld]
        symm
        simpa [pairWorldFromConcreteState, PairWorldSurplus0, skimExcess0] using
          (Core.Uint256.sub_eq_of_le
            (a := observedBalance0 s) (b := s.storage reserve0Slot.slot)
            hReserve0)
      have hSurplus1 :
          PairWorldSurplus1 (pairWorldFromConcreteAndTokens preTokens s) =
            (skimExcess1 s).val := by
        rw [hBeforeWorld]
        symm
        simpa [pairWorldFromConcreteState, PairWorldSurplus1, skimExcess1] using
          (Core.Uint256.sub_eq_of_le
            (a := observedBalance1 s) (b := s.storage reserve1Slot.slot)
            hReserve1)
      have hTransfers :
          pairTransfersAfterCall s ((skim caller).run s) =
            [{ token := pairToken0 s, fromAddr := pairSelf s,
               toAddr := caller, amount := skimExcess0 s },
             { token := pairToken1 s, fromAddr := pairSelf s,
               toAddr := caller, amount := skimExcess1 s }] := by
        exact skim_success_pairTransfers caller s hSuccess
      have hTokens :
          pairTokenWorldAfterCall preTokens s ((skim caller).run s) =
            pairTokenWorldAfterPairTransfers preTokens
              [{ token := pairToken0 s, fromAddr := pairSelf s,
                 toAddr := caller, amount := skimExcess0 s },
               { token := pairToken1 s, fromAddr := pairSelf s,
                 toAddr := caller, amount := skimExcess1 s }] := by
        rw [pairTokenWorldAfterCall_eq_pairTransfers, hTransfers]
      have hToken0Addr :
          ((skim caller).run s).snd.storageAddr token0Slot.slot =
            s.storageAddr token0Slot.slot := by
        exact skim_run_storageAddr_frame caller s token0Slot.slot
      have hToken1Addr :
          ((skim caller).run s).snd.storageAddr token1Slot.slot =
            s.storageAddr token1Slot.slot := by
        exact skim_run_storageAddr_frame caller s token1Slot.slot
      have hLp :
          ((skim caller).run s).snd.storageMap balancesSlot.slot caller =
            s.storageMap balancesSlot.slot caller := by
        exact skim_caller_lp_frame caller caller s
      have hSelfNeCaller : pairSelf s ≠ caller := by
        intro h_eq
        exact hCallerNeSelf h_eq.symm
      have hTokenDistinctSymm : pairToken1 s ≠ pairToken0 s := by
        intro h_eq
        exact hTokenDistinct h_eq.symm
      have hCallerNeSelfRaw : caller ≠ s.thisAddress := by
        simpa [pairSelf] using hCallerNeSelf
      have hSelfNeCallerRaw : s.thisAddress ≠ caller := by
        simpa [pairSelf] using hSelfNeCaller
      have hTokenDistinctRaw : s.storageAddr 1 ≠ s.storageAddr 2 := by
        simpa [pairToken0, pairToken1, token0Slot, token1Slot,
          UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot]
          using hTokenDistinct
      have hTokenDistinctRawSymm : s.storageAddr 2 ≠ s.storageAddr 1 := by
        intro h_eq
        exact hTokenDistinctRaw h_eq.symm
      have hCaller0 :
          (callerTokenBalance0 caller
            (pairTokenWorldAfterCall preTokens s ((skim caller).run s))
            ((skim caller).run s).snd).val =
            (callerTokenBalance0 caller preTokens s).val + (skimExcess0 s).val := by
        have h_add :=
          Core.Uint256.add_eq_of_lt
            (a := callerTokenBalance0 caller preTokens s)
            (b := skimExcess0 s) hCallerToken0Add
        simp only [callerTokenBalance0, pairToken0, hTokens]
        rw [hToken0Addr]
        simpa [pairTokenWorldAfterPairTransfers, pairTokenWorldAfterPairTransfer,
          pairTokenWorldAfterTransfer, hSelfNeCaller, hCallerNeSelf,
          hTokenDistinct, hTokenDistinctSymm, hSelfNeCallerRaw,
          hCallerNeSelfRaw, hTokenDistinctRaw, hTokenDistinctRawSymm,
          callerTokenBalance0, pairToken0]
          using h_add
      have hCaller1 :
          (callerTokenBalance1 caller
            (pairTokenWorldAfterCall preTokens s ((skim caller).run s))
            ((skim caller).run s).snd).val =
            (callerTokenBalance1 caller preTokens s).val + (skimExcess1 s).val := by
        have h_add :=
          Core.Uint256.add_eq_of_lt
            (a := callerTokenBalance1 caller preTokens s)
            (b := skimExcess1 s) hCallerToken1Add
        simp only [callerTokenBalance1, pairToken1, hTokens]
        rw [hToken1Addr]
        simpa [pairTokenWorldAfterPairTransfers, pairTokenWorldAfterPairTransfer,
          pairTokenWorldAfterTransfer, hSelfNeCaller, hCallerNeSelf,
          hTokenDistinct, hTokenDistinctSymm, hSelfNeCallerRaw,
          hCallerNeSelfRaw, hTokenDistinctRaw, hTokenDistinctRawSymm,
          callerTokenBalance1, pairToken1]
          using h_add
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using hPair
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rw [hSurplus0]
        simpa [pairWalletFromConcreteAndTokens] using hCaller0
      constructor
      · rw [hSurplus1]
        simpa [pairWalletFromConcreteAndTokens] using hCaller1
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using congrArg (fun x => x.val) hLp
      · simp [pairWalletFromConcreteAndTokens, hSurplus0, hSurplus1]
  | sync preTokens s result hRun hSuccess hBefore hAfter hExternal =>
      subst before
      subst after
      refine ⟨PairWalletAction.callerSync, ?_, by trivial⟩
      have hPair :
          PairWorldStep PairWorldAction.sync
            (pairWorldFromConcreteAndTokens preTokens s)
            (pairWorldFromConcreteAndTokens
              (pairTokenWorldAfterCall preTokens s result) result.snd) := by
        exact sync_success_reaches_expected_pair_state
          preTokens s result hRun hSuccess hExternal
      have hTokens :
          pairTokenWorldAfterCall preTokens s result = preTokens := by
        rw [hRun]
        exact sync_run_token_world_unchanged preTokens s
      have hToken0Addr :
          result.snd.storageAddr token0Slot.slot = s.storageAddr token0Slot.slot := by
        rw [hRun]
        exact sync_run_storageAddr_frame s token0Slot.slot
      have hToken1Addr :
          result.snd.storageAddr token1Slot.slot = s.storageAddr token1Slot.slot := by
        rw [hRun]
        exact sync_run_storageAddr_frame s token1Slot.slot
      have hLp :
          result.snd.storageMap balancesSlot.slot caller =
            s.storageMap balancesSlot.slot caller := by
        rw [hRun]
        exact sync_run_balances_frame s caller
      have hToken0AddrRaw :
          result.snd.storageAddr 1 = s.storageAddr 1 := by
        simpa [token0Slot, UniswapV2PairBase.token0Slot] using hToken0Addr
      have hToken1AddrRaw :
          result.snd.storageAddr 2 = s.storageAddr 2 := by
        simpa [token1Slot, UniswapV2PairBase.token1Slot] using hToken1Addr
      have hLpRaw :
          result.snd.storageMap 9 caller = s.storageMap 9 caller := by
        simpa [balancesSlot, UniswapV2PairBase.balancesSlot] using hLp
      constructor
      · simpa [pairWalletFromConcreteAndTokens] using hPair
      constructor
      · simp [pairWalletFromConcreteAndTokens, callerTokenBalance0, pairToken0,
          hTokens, hToken0AddrRaw]
      constructor
      · simp [pairWalletFromConcreteAndTokens, callerTokenBalance1, pairToken1,
          hTokens, hToken1AddrRaw]
      · simp [pairWalletFromConcreteAndTokens, hLpRaw]

theorem pairEconomicActionConcretePath_walletHistory
    {caller : Address} {before after : PairWalletWorldState} :
  PairEconomicActionConcretePath caller before after →
    PairWalletHistory before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWalletHistory.refl before
  | step h_prefix h_step ih =>
      rcases pairEconomicActionConcreteStep_wallet h_step with
        ⟨action, h_wallet, _h_ordinary⟩
      exact PairWalletHistory.step action ih h_wallet

theorem pairEconomicActionConcretePath_ordinaryWalletHistory
    {caller : Address} {before after : PairWalletWorldState} :
  PairWalletFlowEmpty before →
    PairEconomicActionConcretePath caller before after →
      OrdinaryPairWalletHistory before after := by
  intro h_flow h_path
  induction h_path with
  | refl =>
      exact OrdinaryPairWalletHistory.refl before h_flow
  | step h_prefix h_step ih =>
      rcases pairEconomicActionConcreteStep_wallet h_step with
        ⟨action, h_wallet, h_ordinary⟩
      exact OrdinaryPairWalletHistory.step action ih h_wallet h_ordinary

-- tama: discharges=pair_actual_execution_no_free_lunch
theorem actual_execution_no_free_lunch
    (caller : Address) (initialTokens : PairTokenBalances)
    (initialState : ContractState) (after : PairWalletWorldState) :
  pair_actual_execution_no_free_lunch caller initialTokens initialState after := by
  intro h_good h_supply h_reserve0 h_reserve1 h_path
  exact wallet_single_caller_history_no_portfolio_profit
    (pairWalletFromConcreteAndTokens caller initialTokens initialState)
    after h_good h_supply h_reserve0 h_reserve1
    (pairEconomicActionConcretePath_ordinaryWalletHistory
      (by simp [PairWalletFlowEmpty, pairWalletFromConcreteAndTokens])
      h_path)

-- tama: discharges=pair_wallet_history_preserves_good
theorem wallet_history_preserves_good
    (before after : PairWalletWorldState) :
  pair_wallet_history_preserves_good before after := by
  intro h_good h_supply h_hist
  rcases pairWalletHistory_preserves_good_and_positive h_good h_supply h_hist
    with ⟨h_after_good, _h_after_supply, _h_after_locked⟩
  exact h_after_good

-- tama: discharges=pair_wallet_history_total_value_conserved
theorem wallet_history_total_value_conserved
    (spot : PairWorldState) (before after : PairWalletWorldState) :
  pair_wallet_history_total_value_conserved spot before after := by
  intro h_good h_supply h_hist
  exact pairWalletHistory_total_value_conserved spot h_good h_supply h_hist

-- tama: discharges=pair_wallet_history_preserves_unowned
theorem wallet_history_preserves_unowned
    (before after : PairWalletWorldState) :
  pair_wallet_history_preserves_unowned before after := by
  intro h_good h_supply h_hist
  exact pairWalletHistory_preserves_unowned h_good h_supply h_hist

/-- Non-liquidity histories are the common operational case: swaps, surplus
management, donations, and LP-token bookkeeping, but no mint and no burn. The
supply firewall above makes these histories same-supply histories, so the
same no-extraction conclusion applies directly. -/
def pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPathNoMintBurn before after →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldSpotValueNum before before ≤
              PairWorldSpotValueNum before after

theorem closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    before after := by
  intro h_reachable h_positive h_path h_reserve0 h_reserve1
  have h_supply :=
    (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_same_supply_path_no_spot_value_extraction
    before after h_reachable h_positive
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm h_reserve0 h_reserve1



def pair_closed_world_non_burn_step_never_decreases_k
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
        PairWorldK before ≤ PairWorldK after

theorem closed_world_non_burn_step_never_decreases_k
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_burn_step_never_decreases_k action before after := by
  exact pairWorldNonBurnStep_never_decreases_k


def pair_closed_world_no_burn_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoBurn before after →
      PairWorldK before ≤ PairWorldK after

theorem closed_world_no_burn_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_no_burn_path_never_decreases_k before after := by
  exact pairWorldNoBurnPath_never_decreases_k



def pair_closed_world_no_burn_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoBurn before after →
      before.totalSupply = after.totalSupply →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldNoSpotProfit before after

theorem closed_world_no_burn_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_no_burn_same_supply_path_no_spot_profit before after := by
  intro h_good h_path h_supply h_reserve0 h_reserve1
  have h_k :
      PairWorldK before ≤ PairWorldK after :=
    pairWorldNoBurnPath_never_decreases_k h_good h_path
  exact closed_world_same_supply_path_no_spot_profit before after
    (pairWorldPath_of_noBurn h_path) h_good h_supply h_reserve0 h_reserve1 h_k


-- tama: discharges=pair_closed_world_skim_removes_surplus
theorem closed_world_skim_removes_surplus
    (before after : PairWorldState) :
  pair_closed_world_skim_removes_surplus before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  exact ⟨h_balance0, h_balance1, h_reserve0, h_reserve1⟩


-- tama: discharges=pair_closed_world_skim_removes_exact_surplus_value
theorem closed_world_skim_removes_exact_surplus_value
    (before after : PairWorldState) :
  pair_closed_world_skim_removes_exact_surplus_value before after := by
  intro h_good h_step
  have h_remove := closed_world_skim_removes_surplus before after h_step
  have h_after_value :
      PairWorldBalanceSpotValueNum before after =
        PairWorldSpotValueNum before before := by
    unfold PairWorldBalanceSpotValueNum PairWorldSpotValueNum
    rw [h_remove.1, h_remove.2.1]
  have h_before_decomp :=
    pairWorldBalanceSpotValue_eq_spot_plus_surplus
      (spot := before) (pool := before) h_good
  rw [h_before_decomp, h_after_value]


-- tama: discharges=pair_closed_world_skim_token_balance_value_never_increases_at_spot
theorem closed_world_skim_token_balance_value_never_increases_at_spot
    (spot before after : PairWorldState) :
  pair_closed_world_skim_token_balance_value_never_increases_at_spot
    spot before after := by
  intro h_good h_step
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  have h_remove := closed_world_skim_removes_surplus before after h_step
  unfold PairWorldBalanceSpotValueNum
  rw [h_remove.1, h_remove.2.1]
  exact Nat.add_le_add
    (Nat.mul_le_mul_right spot.reserve1 h_back0)
    (Nat.mul_le_mul_right spot.reserve0 h_back1)

-- tama: discharges=pair_closed_world_skim_preserves_balanced_pool
theorem closed_world_skim_preserves_balanced_pool
    (before after : PairWorldState) :
  pair_closed_world_skim_preserves_balanced_pool before after := by
  intro h_good h_step h_surplus0 h_surplus1
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
  have h_balance0_before : before.balance0 = before.reserve0 := by
    unfold PairWorldSurplus0 at h_surplus0
    omega
  have h_balance1_before : before.balance1 = before.reserve1 := by
    unfold PairWorldSurplus1 at h_surplus1
    omega
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
    h_supply, h_locked⟩
  constructor
  · rw [h_balance0, h_balance0_before]
  constructor
  · rw [h_balance1, h_balance1_before]
  exact ⟨h_reserve0, h_reserve1, h_supply, h_locked⟩



-- tama: discharges=pair_closed_world_sync_sets_reserves_to_balances
theorem closed_world_sync_sets_reserves_to_balances
    (before after : PairWorldState) :
  pair_closed_world_sync_sets_reserves_to_balances before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
    h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  exact ⟨h_reserve0, h_reserve1, h_balance0, h_balance1⟩

-- tama: discharges=pair_closed_world_sync_preserves_token_balances
theorem closed_world_sync_preserves_token_balances
    (before after : PairWorldState) :
  pair_closed_world_sync_preserves_token_balances before after := by
  intro h_step
  have h_sync := closed_world_sync_sets_reserves_to_balances before after h_step
  exact ⟨h_sync.2.2.1, h_sync.2.2.2⟩


-- tama: discharges=pair_closed_world_reserve_write_sets_reserves_to_balances
theorem closed_world_reserve_write_sets_reserves_to_balances
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_reserve_write_sets_reserves_to_balances action before after := by
  intro h_action h_step
  rcases h_action with h_mint | h_burn | h_swap | h_sync
  · rcases h_mint with ⟨amount0, amount1, liquidity, h_action⟩
    subst action
    simp [PairWorldStep, PairWorldMintStep] at h_step
    rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
      _h_before0, _h_before1, h_balance0, h_balance1, h_reserve0,
      h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
    exact ⟨by rw [h_reserve0, h_balance0], by rw [h_reserve1, h_balance1]⟩
  · rcases h_burn with ⟨amount0, amount1, liquidity, h_action⟩
    subst action
    simp [PairWorldStep, PairWorldBurnStep] at h_step
    rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
      _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liq_le,
      _h_locked_le, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
      _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
    exact ⟨h_reserve0, h_reserve1⟩
  · rcases h_swap with ⟨amount0In, amount1In, amount0Out, amount1Out, h_action⟩
    subst action
    simp [PairWorldStep, PairWorldSwapStep] at h_step
    rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_cover0,
      _h_cover1, _h_input, _h_balance0, _h_balance1, h_reserve0,
      h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
      _h_fee0, _h_fee1, _h_k⟩
    exact ⟨h_reserve0, h_reserve1⟩
  · subst action
    have h_sync_step := closed_world_sync_sets_reserves_to_balances before after h_step
    constructor
    · rw [h_sync_step.1, h_sync_step.2.2.1]
    · rw [h_sync_step.2.1, h_sync_step.2.2.2]


theorem closed_world_sync_preserves_token_balance_value
    (spot before after : PairWorldState) :
  PairWorldStep PairWorldAction.sync before after →
    PairWorldBalanceSpotValueNum spot after =
      PairWorldBalanceSpotValueNum spot before := by
  intro h_step
  have h_sync := closed_world_sync_preserves_token_balances before after h_step
  unfold PairWorldBalanceSpotValueNum
  rw [h_sync.1, h_sync.2]

theorem closed_world_sync_preserves_balanced_pool
    (before after : PairWorldState) :
  PairWorldGood before →
    PairWorldStep PairWorldAction.sync before after →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity := by
  intro h_good h_step h_surplus0 h_surplus1
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  have h_balance0_before : before.balance0 = before.reserve0 := by
    unfold PairWorldSurplus0 at h_surplus0
    omega
  have h_balance1_before : before.balance1 = before.reserve1 := by
    unfold PairWorldSurplus1 at h_surplus1
    omega
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
    h_reserve0, h_reserve1, h_supply, h_locked⟩
  constructor
  · exact h_balance0
  constructor
  · exact h_balance1
  constructor
  · rw [h_reserve0, h_balance0_before]
  constructor
  · rw [h_reserve1, h_balance1_before]
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
theorem closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
    (spot : PairWorldState) (action : PairWorldAction)
    (before after : PairWorldState) :
  pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
    spot action before after := by
  intro h_action h_good h_step
  rcases h_action with h_skim | h_sync
  · subst action
    exact closed_world_skim_token_balance_value_never_increases_at_spot
      spot before after h_good h_step
  · subst action
    have h_value :=
      closed_world_sync_preserves_token_balance_value spot before after h_step
    rw [h_value]





theorem pairWorldSkimSyncPath_preserves_balanced_pool
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathSkimSync before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity := by
  intro h_good h_surplus0 h_surplus1 h_path
  induction h_path with
  | refl =>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | skim h_prefix h_step ih =>
      rename_i mid final
      rcases ih with
        ⟨h_balance0_prefix, h_balance1_prefix, h_reserve0_prefix,
          h_reserve1_prefix, h_supply_prefix, h_locked_prefix⟩
      have h_good_prefix : PairWorldGood mid := by
        simpa [PairWorldGood, PairWorldSupplyGood, h_balance0_prefix,
          h_balance1_prefix, h_reserve0_prefix, h_reserve1_prefix,
          h_supply_prefix, h_locked_prefix] using h_good
      have h_surplus0_prefix : PairWorldSurplus0 mid = 0 := by
        simpa [PairWorldSurplus0, h_balance0_prefix, h_reserve0_prefix]
          using h_surplus0
      have h_surplus1_prefix : PairWorldSurplus1 mid = 0 := by
        simpa [PairWorldSurplus1, h_balance1_prefix, h_reserve1_prefix]
          using h_surplus1
      rcases closed_world_skim_preserves_balanced_pool
          mid final h_good_prefix h_step h_surplus0_prefix h_surplus1_prefix with
        ⟨h_balance0_step, h_balance1_step, h_reserve0_step,
          h_reserve1_step, h_supply_step, h_locked_step⟩
      constructor
      · rw [h_balance0_step, h_balance0_prefix]
      constructor
      · rw [h_balance1_step, h_balance1_prefix]
      constructor
      · rw [h_reserve0_step, h_reserve0_prefix]
      constructor
      · rw [h_reserve1_step, h_reserve1_prefix]
      constructor
      · rw [h_supply_step, h_supply_prefix]
      · rw [h_locked_step, h_locked_prefix]
  | sync h_prefix h_step ih =>
      rename_i mid final
      rcases ih with
        ⟨h_balance0_prefix, h_balance1_prefix, h_reserve0_prefix,
          h_reserve1_prefix, h_supply_prefix, h_locked_prefix⟩
      have h_good_prefix : PairWorldGood mid := by
        simpa [PairWorldGood, PairWorldSupplyGood, h_balance0_prefix,
          h_balance1_prefix, h_reserve0_prefix, h_reserve1_prefix,
          h_supply_prefix, h_locked_prefix] using h_good
      have h_surplus0_prefix : PairWorldSurplus0 mid = 0 := by
        simpa [PairWorldSurplus0, h_balance0_prefix, h_reserve0_prefix]
          using h_surplus0
      have h_surplus1_prefix : PairWorldSurplus1 mid = 0 := by
        simpa [PairWorldSurplus1, h_balance1_prefix, h_reserve1_prefix]
          using h_surplus1
      rcases closed_world_sync_preserves_balanced_pool
          mid final h_good_prefix h_step h_surplus0_prefix h_surplus1_prefix with
        ⟨h_balance0_step, h_balance1_step, h_reserve0_step,
          h_reserve1_step, h_supply_step, h_locked_step⟩
      constructor
      · rw [h_balance0_step, h_balance0_prefix]
      constructor
      · rw [h_balance1_step, h_balance1_prefix]
      constructor
      · rw [h_reserve0_step, h_reserve0_prefix]
      constructor
      · rw [h_reserve1_step, h_reserve1_prefix]
      constructor
      · rw [h_supply_step, h_supply_prefix]
      · rw [h_locked_step, h_locked_prefix]

/-- The same no-change claim holds for any finite history made only of `skim`
and `sync`. Starting from a good pool with no excess balances above cached
reserves, repeated cleanup calls preserve token balances, cached reserves, LP
supply, and the permanent liquidity lock exactly. -/
def pair_closed_world_balanced_skim_sync_path_preserves_pool
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathSkimSync before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity

theorem closed_world_balanced_skim_sync_path_preserves_pool
    (before after : PairWorldState) :
  pair_closed_world_balanced_skim_sync_path_preserves_pool before after := by
  exact pairWorldSkimSyncPath_preserves_balanced_pool

theorem pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity := by
  intro h_good h_surplus0 h_surplus1 h_path
  induction h_path with
  | refl =>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | approve ownerAddr spender amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | transfer fromAddr toAddr amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | transferFrom spender fromAddr toAddr amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | skim h_prefix h_step ih =>
      rename_i mid final
      rcases ih with
        ⟨h_balance0_prefix, h_balance1_prefix, h_reserve0_prefix,
          h_reserve1_prefix, h_supply_prefix, h_locked_prefix⟩
      have h_good_prefix : PairWorldGood mid := by
        simpa [PairWorldGood, PairWorldSupplyGood, h_balance0_prefix,
          h_balance1_prefix, h_reserve0_prefix, h_reserve1_prefix,
          h_supply_prefix, h_locked_prefix] using h_good
      have h_surplus0_prefix : PairWorldSurplus0 mid = 0 := by
        simpa [PairWorldSurplus0, h_balance0_prefix, h_reserve0_prefix]
          using h_surplus0
      have h_surplus1_prefix : PairWorldSurplus1 mid = 0 := by
        simpa [PairWorldSurplus1, h_balance1_prefix, h_reserve1_prefix]
          using h_surplus1
      rcases closed_world_skim_preserves_balanced_pool
          mid final h_good_prefix h_step h_surplus0_prefix h_surplus1_prefix with
        ⟨h_balance0_step, h_balance1_step, h_reserve0_step,
          h_reserve1_step, h_supply_step, h_locked_step⟩
      constructor
      · rw [h_balance0_step, h_balance0_prefix]
      constructor
      · rw [h_balance1_step, h_balance1_prefix]
      constructor
      · rw [h_reserve0_step, h_reserve0_prefix]
      constructor
      · rw [h_reserve1_step, h_reserve1_prefix]
      constructor
      · rw [h_supply_step, h_supply_prefix]
      · rw [h_locked_step, h_locked_prefix]
  | sync h_prefix h_step ih =>
      rename_i mid final
      rcases ih with
        ⟨h_balance0_prefix, h_balance1_prefix, h_reserve0_prefix,
          h_reserve1_prefix, h_supply_prefix, h_locked_prefix⟩
      have h_good_prefix : PairWorldGood mid := by
        simpa [PairWorldGood, PairWorldSupplyGood, h_balance0_prefix,
          h_balance1_prefix, h_reserve0_prefix, h_reserve1_prefix,
          h_supply_prefix, h_locked_prefix] using h_good
      have h_surplus0_prefix : PairWorldSurplus0 mid = 0 := by
        simpa [PairWorldSurplus0, h_balance0_prefix, h_reserve0_prefix]
          using h_surplus0
      have h_surplus1_prefix : PairWorldSurplus1 mid = 0 := by
        simpa [PairWorldSurplus1, h_balance1_prefix, h_reserve1_prefix]
          using h_surplus1
      rcases closed_world_sync_preserves_balanced_pool
          mid final h_good_prefix h_step h_surplus0_prefix h_surplus1_prefix with
        ⟨h_balance0_step, h_balance1_step, h_reserve0_step,
          h_reserve1_step, h_supply_step, h_locked_step⟩
      constructor
      · rw [h_balance0_step, h_balance0_prefix]
      constructor
      · rw [h_balance1_step, h_balance1_prefix]
      constructor
      · rw [h_reserve0_step, h_reserve0_prefix]
      constructor
      · rw [h_reserve1_step, h_reserve1_prefix]
      constructor
      · rw [h_supply_step, h_supply_prefix]
      · rw [h_locked_step, h_locked_prefix]

/-- LP approvals/transfers only move LP-token claims, not pool assets. Combining
those bookkeeping actions with `skim`/`sync` on a pool that has no excess token
balances therefore preserves the pool exactly across any finite history made
only of `approve`, `transfer`, `transferFrom`, `skim`, and `sync`. -/
def pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity

theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool before after := by
  exact pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool

/-- The cached reserve product is unchanged by the same histories. Since token
balances and cached reserves are unchanged, the pool's `reserve0 * reserve1`
value is unchanged too; this lets economic arguments cite the K consequence
directly. -/
def pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          PairWorldK after = PairWorldK before

theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k before after := by
  intro h_good h_surplus0 h_surplus1 h_path
  rcases pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
      h_good h_surplus0 h_surplus1 h_path with
    ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  simp [PairWorldK, h_reserve0, h_reserve1]

/-- Clean pools stay clean under LP bookkeeping plus `skim`/`sync`. Those
actions cannot create new excess token balances above cached reserves when none
existed at the start. -/
def pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          PairWorldSurplus0 after = 0 ∧
          PairWorldSurplus1 after = 0

theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus
    before after := by
  intro h_good h_surplus0 h_surplus1 h_path
  rcases pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
      h_good h_surplus0 h_surplus1 h_path with
    ⟨h_balance0, h_balance1, h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  constructor
  · simpa [PairWorldSurplus0, h_balance0, h_reserve0] using h_surplus0
  · simpa [PairWorldSurplus1, h_balance1, h_reserve1] using h_surplus1

/-- Economic reading of the no-change theorem above. If a clean balanced pool
only goes through LP approval/transfer bookkeeping plus `skim`/`sync`, the
actual token balances held by the pool have exactly the same spot-priced value
at the end as they had at the start. This is the concise no-extraction
consequence of the stronger state-preservation theorem above. -/
def pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          PairWorldBalanceSpotValueNum before after =
            PairWorldBalanceSpotValueNum before before

theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value
    before after := by
  intro h_good h_surplus0 h_surplus1 h_path
  rcases pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
      h_good h_surplus0 h_surplus1 h_path with
    ⟨h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_supply, _h_locked⟩
  simp [PairWorldBalanceSpotValueNum, h_balance0, h_balance1]

theorem pairWorldLpBookkeepingSkimSyncPath_token_balance_value_never_increases_at_spot
    {spot before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPathLpBookkeepingSkimSync before after →
      PairWorldGood after ∧
      PairWorldBalanceSpotValueNum spot after ≤
        PairWorldBalanceSpotValueNum spot before := by
  intro h_good h_path
  induction h_path with
  | refl =>
      exact ⟨h_good, le_rfl⟩
  | approve ownerAddr spender amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | transfer fromAddr toAddr amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | transferFrom spender fromAddr toAddr amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | skim h_prefix h_step ih =>
      rename_i mid final
      rcases ih with ⟨h_good_mid, h_value_prefix⟩
      have h_step_value :=
        closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
          spot PairWorldAction.skim mid final (Or.inl rfl) h_good_mid h_step
      exact ⟨pairWorldStep_preserves_good h_good_mid h_step,
        Nat.le_trans h_step_value h_value_prefix⟩
  | sync h_prefix h_step ih =>
      rename_i mid final
      rcases ih with ⟨h_good_mid, h_value_prefix⟩
      have h_step_value :=
        closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
          spot PairWorldAction.sync mid final (Or.inr rfl) h_good_mid h_step
      exact ⟨pairWorldStep_preserves_good h_good_mid h_step,
        Nat.le_trans h_step_value h_value_prefix⟩

/-- Without the zero-surplus assumption, LP bookkeeping plus `skim`/`sync` may
remove donated excess via skim, but it still cannot increase the pair's actual
token-balance value at the starting spot price. -/
def pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathLpBookkeepingSkimSync before after →
      PairWorldBalanceSpotValueNum before after ≤
        PairWorldBalanceSpotValueNum before before

theorem closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    (before after : PairWorldState) :
  pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    before after := by
  intro h_good h_path
  exact
    (pairWorldLpBookkeepingSkimSyncPath_token_balance_value_never_increases_at_spot
      (spot := before) h_good h_path).2



end TamaUniV2.Proof.UniswapV2PairProof
