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

theorem observedBalance0_balanceOf_run_nf (s : ContractState) :
    ((Contracts.balanceOf (s.storageAddr token0Slot.slot) s.thisAddress).run s).fst =
      observedBalance0 s := by
  rfl

theorem observedBalance1_balanceOf_run_nf (s : ContractState) :
    ((Contracts.balanceOf (s.storageAddr token1Slot.slot) s.thisAddress).run s).fst =
      observedBalance1 s := by
  rfl

theorem mintAmount0_balanceOf_run_nf (s : ContractState) :
    Verity.EVM.Uint256.sub
        ((Contracts.balanceOf (s.storageAddr token0Slot.slot) s.thisAddress).run s).fst
        (s.storage reserve0Slot.slot) =
      mintAmount0 s := by
  rfl

theorem mintAmount1_balanceOf_run_nf (s : ContractState) :
    Verity.EVM.Uint256.sub
        ((Contracts.balanceOf (s.storageAddr token1Slot.slot) s.thisAddress).run s).fst
        (s.storage reserve1Slot.slot) =
      mintAmount1 s := by
  rfl

theorem observedBalance0_balanceOf_run_success_nf (s : ContractState) :
    (Contracts.balanceOf (s.storageAddr token0Slot.slot) s.thisAddress).run s =
      ContractResult.success (observedBalance0 s) s := by
  rfl

theorem observedBalance1_balanceOf_run_success_nf (s : ContractState) :
    (Contracts.balanceOf (s.storageAddr token1Slot.slot) s.thisAddress).run s =
      ContractResult.success (observedBalance1 s) s := by
  rfl

theorem mintLockedState_storage_reserve0 (s : ContractState) :
    (mintLockedState s).storage reserve0Slot.slot = s.storage reserve0Slot.slot := by
  simp [mintLockedState, reserve0Slot, unlockedSlot]

theorem mintLockedState_storage_reserve1 (s : ContractState) :
    (mintLockedState s).storage reserve1Slot.slot = s.storage reserve1Slot.slot := by
  simp [mintLockedState, reserve1Slot, unlockedSlot]

theorem mintLockedState_storage_totalSupply (s : ContractState) :
    (mintLockedState s).storage totalSupplySlot.slot =
      s.storage totalSupplySlot.slot := by
  simp [mintLockedState, totalSupplySlot, unlockedSlot]

theorem mintLockedState_storage_unlocked (s : ContractState) :
    (mintLockedState s).storage unlockedSlot.slot = 0 := by
  simp [mintLockedState, unlockedSlot]

theorem mintLockedState_storageAddr (s : ContractState) :
    (mintLockedState s).storageAddr = s.storageAddr := by
  rfl

theorem mintLockedState_sender (s : ContractState) :
    (mintLockedState s).sender = s.sender := by
  rfl

theorem mintLockedState_thisAddress (s : ContractState) :
    (mintLockedState s).thisAddress = s.thisAddress := by
  rfl

theorem mintLockedState_blockTimestamp (s : ContractState) :
    (mintLockedState s).blockTimestamp = s.blockTimestamp := by
  rfl

theorem observedBalance0_mintLockedState (s : ContractState) :
    observedBalance0 (mintLockedState s) = observedBalance0 s := by
  rfl

theorem observedBalance1_mintLockedState (s : ContractState) :
    observedBalance1 (mintLockedState s) = observedBalance1 s := by
  rfl

theorem observedBalance0_balanceOf_mintLockedState_run_success_nf
    (s : ContractState) :
    (Contracts.balanceOf ((mintLockedState s).storageAddr token0Slot.slot)
        (mintLockedState s).thisAddress).run (mintLockedState s) =
      ContractResult.success (observedBalance0 s) (mintLockedState s) := by
  rfl

theorem observedBalance1_balanceOf_mintLockedState_run_success_nf
    (s : ContractState) :
    (Contracts.balanceOf ((mintLockedState s).storageAddr token1Slot.slot)
        (mintLockedState s).thisAddress).run (mintLockedState s) =
      ContractResult.success (observedBalance1 s) (mintLockedState s) := by
  rfl

theorem mintAmount0_mintLockedState (s : ContractState) :
    mintAmount0 (mintLockedState s) = mintAmount0 s := by
  simp only [mintAmount0, observedBalance0_mintLockedState,
    mintLockedState_storage_reserve0]

theorem mintAmount1_mintLockedState (s : ContractState) :
    mintAmount1 (mintLockedState s) = mintAmount1 s := by
  simp only [mintAmount1, observedBalance1_mintLockedState,
    mintLockedState_storage_reserve1]

/-- Fold a deposit amount computed from the already-folded observed balance back
to `mintAmount0`.  Holds by definition (`mintAmount0 s := sub (observedBalance0 s) …`)
and is needed once the balance read has folded to `observedBalance0 s` rather than the
raw `((balanceOf …).run s).fst` form. -/
theorem mintAmount0_observed_nf (s : ContractState) :
    Verity.EVM.Uint256.sub (observedBalance0 s) (s.storage reserve0Slot.slot) =
      mintAmount0 s := rfl

theorem mintAmount1_observed_nf (s : ContractState) :
    Verity.EVM.Uint256.sub (observedBalance1 s) (s.storage reserve1Slot.slot) =
      mintAmount1 s := rfl

/-- Taking the reentrancy lock (`setStorage unlockedSlot 0`) yields exactly
`mintLockedState s`, letting the entrypoint reduction continue on a state the
`mintLockedState` frame/read lemmas recognise (instead of an opaque record). -/
theorem setStorage_unlockedSlot_run_mintLockedState (s : ContractState) :
    (setStorage unlockedSlot (0 : Uint256)).run s =
      ContractResult.success () (mintLockedState s) := rfl

/-! Application-form ("`c state`", not "`c.run state`") variants of the lock/read
folds.  Reducing a public entrypoint with `bind`/`Contract.run` unfolded leaves the
primitive operations applied directly to the threaded state, so these are the forms
that actually fire in the entrypoint prefix reduction. -/

theorem setStorage_unlockedSlot_app_mintLockedState (s : ContractState) :
    setStorage unlockedSlot (0 : Uint256) s =
      ContractResult.success () (mintLockedState s) := rfl

theorem observedBalance0_balanceOf_mintLockedState_app_nf (s : ContractState) :
    Contracts.balanceOf ((mintLockedState s).storageAddr token0Slot.slot)
        (mintLockedState s).thisAddress (mintLockedState s) =
      ContractResult.success (observedBalance0 s) (mintLockedState s) := rfl

theorem observedBalance1_balanceOf_mintLockedState_app_nf (s : ContractState) :
    Contracts.balanceOf ((mintLockedState s).storageAddr token1Slot.slot)
        (mintLockedState s).thisAddress (mintLockedState s) =
      ContractResult.success (observedBalance1 s) (mintLockedState s) := rfl

theorem pairPostCallSelfBalancesMatch_balance0_app_nf
    {s post readState : ContractState} {b0 b1 : Uint256} :
    pairPostCallSelfBalancesMatch s post b0 b1 →
      TamaUniV2.erc20BalanceOf (pairToken0 s) (pairSelf s) readState =
        ContractResult.success b0 readState := by
  intro h_match
  rcases h_match with ⟨h0, _h1⟩
  simpa [pairPostCallSelfBalancesMatch, TamaUniV2.erc20BalanceOf,
    Contracts.balanceOf, Contract.run, ContractResult.fst, Verity.pure,
    Pure.pure] using h0

theorem pairPostCallSelfBalancesMatch_balance1_app_nf
    {s post readState : ContractState} {b0 b1 : Uint256} :
    pairPostCallSelfBalancesMatch s post b0 b1 →
      TamaUniV2.erc20BalanceOf (pairToken1 s) (pairSelf s) readState =
        ContractResult.success b1 readState := by
  intro h_match
  rcases h_match with ⟨_h0, h1⟩
  simpa [pairPostCallSelfBalancesMatch, TamaUniV2.erc20BalanceOf,
    Contracts.balanceOf, Contract.run, ContractResult.fst, Verity.pure,
    Pure.pure] using h1

/-- Generic public-entrypoint rollback collapse, over an *abstract* path result `D`.
The public `Contract.run` rolls a path revert back to the pre-call state `s`, while
the path itself reverts from the locked state `ls`; on success both keep the path
post-state.  Proving it over an abstract `D` keeps the `cases` cheap, so applying it
closes the entrypoint adapter without the kernel reducing the (large) concrete path
term. -/
theorem run_rollback_collapse {α : Type} (D : ContractResult α) (s ls : ContractState) :
    (match D with
      | ContractResult.success a s' => ContractResult.success a s'
      | ContractResult.revert msg _ => ContractResult.revert msg s) =
      (match
          (match D with
            | ContractResult.success a s' => ContractResult.success a s'
            | ContractResult.revert msg _ => ContractResult.revert msg ls) with
        | ContractResult.success a s' => ContractResult.success a s'
        | ContractResult.revert msg _ => ContractResult.revert msg s) := by
  cases D <;> rfl

theorem contract_bind_success {α β : Type}
    (ma : Contract α) (f : α → Contract β)
    (s s' : ContractState) (a : α)
    (h : ma s = ContractResult.success a s') :
    (Bind.bind ma f) s = f a s' := by
  dsimp only [Bind.bind, Verity.bind]
  rw [h]

end TamaUniV2.Proof.UniswapV2PairProof
