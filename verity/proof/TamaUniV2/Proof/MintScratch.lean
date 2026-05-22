import TamaUniV2.Proof.UniswapV2PairProof

/-!
WIP scratch for bridging `mint` to actual execution (companion of skim/sync).

Status / findings so far:
* `mint`'s `run` reduces under `simp only` with all huge literals folded
  (`-maxUint112`, `-q112`, `-uint32Modulus`, oracle helpers) WITHOUT triggering
  the Lean kernel "deep recursion" that blocks `swap`. The reduction leaves the
  nested guard match-tree (lock, OVERFLOW, INSUFFICIENT_AMOUNT, amount>0,
  first-vs-subsequent branch, MINT_OVERFLOW, LIQUIDITY_MINTED, SUPPLY/BALANCE
  overflow via `safeAdd`/`requireSomeUint`).
* `mint`'s closed-world model uses the freshly observed balance directly
  (`pairWorldAfter{First,Subsequent}MintRun.reserve0 = observedBalance0 s`), so —
  unlike `burn` — `mint` SHOULD bridge cleanly like `sync`: the frozen-stub
  reserve write equals the modeled reserve.

Remaining work (the open `sorry` below):
* Discharge the guard match-tree. Plan: split first/subsequent on
  `s.storage totalSupplySlot.slot = 0`; reduce goal + `h_success` in lockstep,
  then drive the case analysis (`split_ifs` after unfolding `safeAdd` /
  `requireSomeUint`, keeping `MAX_UINT256` folded) and close each revert branch
  by contradiction with `h_success`. The first-mint branch additionally threads
  `FixedPointMathLibBase.sqrt`; keep it opaque and relate the written
  `totalSupply` to `mintFirstRoot s` by definition (`sqrtValue`).
* Then assemble the per-field facts (reserve0/reserve1/supply/obs0/obs1) into
  `pairWorldFromConcreteState result.snd = pairWorldAfter{First,Subsequent}MintRun s`,
  add the spec obligation + `tama: discharges` + `[coverage.proof_only]` entry,
  and port into `UniswapV2PairProof.lean`.
-/

namespace MintScratch

set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

open Verity
open Verity.EVM.Uint256
open TamaUniV2
open TamaUniV2.Spec.UniswapV2PairSpec
open TamaUniV2.UniswapV2Pair
open TamaUniV2.Common.UniswapV2PairConcrete
open TamaUniV2.Common.UniswapV2PairGhost
open TamaUniV2.Proof.UniswapV2PairProof

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

-- Verified: this `simp only` reduces `mint`'s run to the guard match-tree with
-- no kernel deep recursion. The remaining guard discharge + assembly is `sorry`.
theorem mint_post_reserve0
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256)
    (h_run : result = (mint toAddr).run s)
    (h_success : ∃ liq, result = ContractResult.success liq result.snd) :
    result.snd.storage reserve0Slot.slot = observedBalance0 s := by
  obtain ⟨liq, h_success⟩ := h_success
  subst h_run
  simp only [mint, UniswapV2PairBase.mint, getStorage, getStorageAddr, setStorage,
    getMapping, setMapping, Verity.contractAddress, Verity.blockTimestamp, Verity.msgSender,
    Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore, Contracts.emit, emitEvent,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed] at h_success ⊢
  -- TODO: discharge guard match-tree via lockstep split + `h_success` contradiction,
  -- then read slot 3 = balance0Now = observedBalance0 s.
  sorry

end MintScratch
