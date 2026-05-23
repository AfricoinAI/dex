import TamaUniV2.Spec.UniswapV2PairSpec
import Verity.Proofs.Stdlib.Automation

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

theorem pairWorldFromConcreteAndTokens_eq_of_parts
    (tokens : PairTokenBalances) (s : ContractState)
    (expected : PairWorldState) :
  pairTokenBalancesMatchWorld tokens s expected →
    pairConcreteStorageMatchesWorld s expected →
      pairWorldFromConcreteAndTokens tokens s = expected := by
  intro h_tokens h_storage
  rcases h_tokens with ⟨h_balance0, h_balance1⟩
  rcases h_storage with ⟨h_reserve0, h_reserve1, h_supply, h_locked⟩
  cases expected
  simp [pairWorldFromConcreteAndTokens, pairTokenBalancesMatchWorld,
    pairConcreteStorageMatchesWorld] at *
  exact ⟨h_balance0, h_balance1, h_reserve0, h_reserve1, h_supply, h_locked⟩

axiom sqrt_run_success_frames_state (x : Uint256) (s : ContractState) :
  Tamago.Utils.FixedPointMathLibBase.sqrt x s =
    ContractResult.success (sqrtValue x s) s

attribute [local simp] sqrt_run_success_frames_state

theorem uint256_bne_true_of_ne {a b : Uint256} (h : a ≠ b) :
    (a != b) = true := by
  simpa [bne_iff_ne] using h

theorem uint256_pos_of_ne_zero {a : Uint256} (h : a ≠ 0) :
    a > 0 := by
  change 0 < a.val
  by_contra h_not_pos
  have h_val_zero : a.val = 0 := by
    omega
  apply h
  cases a with
  | mk val isLt =>
      simp at h_val_zero
      subst val
      rfl

theorem addressOfNat_toNat_mod_uint256 (a : Address) :
    Core.Address.ofNat (Core.Address.toNat a % Core.Uint256.modulus) = a := by
  apply Core.Address.toNat_injective
  have h_lt_uint : Core.Address.toNat a < Core.Uint256.modulus := by
    have h_lt_addr : Core.Address.toNat a < Core.Address.modulus :=
      Core.Address.val_lt_modulus a
    have h_addr_lt_uint : Core.Address.modulus < Core.Uint256.modulus := by
      decide
    exact Nat.lt_trans h_lt_addr h_addr_lt_uint
  have h_uint_mod : Core.Address.toNat a % Core.Uint256.modulus = Core.Address.toNat a :=
    Nat.mod_eq_of_lt h_lt_uint
  have h_addr_mod : Core.Address.toNat a % Core.Address.modulus = Core.Address.toNat a := by
    simp [Core.Address.toNat, Core.Address.val_mod_modulus]
  simp [h_uint_mod, h_addr_mod]

end TamaUniV2.Proof.UniswapV2PairProof
