import TamaUniV2.UniswapV2Pair
import TamaUniV2.Common.UniswapV2PairGhost

/-!
Concrete helper formulas for Uniswap V2 pair specs.

This module intentionally lives outside `verity/spec`: Tama treats public
top-level definitions in spec modules as candidate obligations. The definitions
here mirror Tamago's ERC4626 helper modules and keep balance-read formulas
available to public specs without turning helper names into obligations.
-/

namespace TamaUniV2.Common.UniswapV2PairConcrete

open Verity
open TamaUniV2.UniswapV2Pair
open TamaUniV2.Common.UniswapV2PairGhost
open Tamago.Utils

def pairSelf (s : ContractState) : Address :=
  s.thisAddress

def pairToken0 (s : ContractState) : Address :=
  s.storageAddr token0Slot.slot

def pairToken1 (s : ContractState) : Address :=
  s.storageAddr token1Slot.slot

def observedBalance0 (s : ContractState) : Uint256 :=
  ((TamaUniV2.erc20BalanceOf (pairToken0 s) (pairSelf s)).run s).fst

def observedBalance1 (s : ContractState) : Uint256 :=
  ((TamaUniV2.erc20BalanceOf (pairToken1 s) (pairSelf s)).run s).fst

def pairTraceContains (event : Event) (events : List Event) : Prop :=
  event ∈ events

def pairLpApprovalEvent
    (owner spender : Address) (amount : Uint256) : Event :=
  { name := "Approval"
    args := [addressToWord owner, addressToWord spender, amount]
    indexedArgs := [] }

def pairLpTransferEvent
    (fromAddr toAddr : Address) (amount : Uint256) : Event :=
  { name := "Transfer"
    args := [addressToWord fromAddr, addressToWord toAddr, amount]
    indexedArgs := [] }

def pairMintEvent
    (sender : Address) (amount0 amount1 : Uint256) : Event :=
  { name := "Mint"
    args := [addressToWord sender, amount0, amount1]
    indexedArgs := [] }

def pairBurnEvent
    (sender : Address) (amount0 amount1 : Uint256) (toAddr : Address) : Event :=
  { name := "Burn"
    args := [addressToWord sender, amount0, amount1, addressToWord toAddr]
    indexedArgs := [] }

def pairSwapEvent
    (sender : Address)
    (amount0In amount1In amount0Out amount1Out : Uint256)
    (toAddr : Address) : Event :=
  { name := "Swap"
    args := [
      addressToWord sender,
      amount0In,
      amount1In,
      amount0Out,
      amount1Out,
      addressToWord toAddr
    ]
    indexedArgs := [] }

def pairSyncEvent (reserve0 reserve1 : Uint256) : Event :=
  { name := "Sync"
    args := [reserve0, reserve1]
    indexedArgs := [] }

def hasPairSafeTransferTrace
    (token fromAddr toAddr : Address) (amount : Uint256)
    (s : ContractState) : Prop :=
  pairTraceContains
    (TamaUniV2.pairTokenSafeTransferEvent token fromAddr toAddr amount)
    s.events

def mintAmount0 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance0 s) (s.storage reserve0Slot.slot)

def mintAmount1 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance1 s) (s.storage reserve1Slot.slot)

def mintFirstProduct (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mul (mintAmount0 s) (mintAmount1 s)

def mintLockedState (s : ContractState) : ContractState :=
  { s with «storage» := fun slotIdx =>
      if slotIdx = unlockedSlot.slot then 0 else s.storage slotIdx }

def sqrtValue (x : Uint256) (s : ContractState) : Uint256 :=
  ((FixedPointMathLibBase.sqrt x).run s).fst

def mintFirstRoot (s : ContractState) : Uint256 :=
  sqrtValue (mintFirstProduct s) (mintLockedState s)

def mintFirstLiquidity (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (mintFirstRoot s) minimumLiquidity

def pairWorldLockedLiquidity (supply : Uint256) : Nat :=
  if supply.val = 0 then 0 else minimumLiquidityNat

def pairWorldBeforeMintRun (s : ContractState) : PairWorldState :=
  { balance0 := (observedBalance0 s).val
    balance1 := (observedBalance1 s).val
    reserve0 := (s.storage reserve0Slot.slot).val
    reserve1 := (s.storage reserve1Slot.slot).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairWorldAfterFirstMintRun (s : ContractState) : PairWorldState :=
  { balance0 := (observedBalance0 s).val
    balance1 := (observedBalance1 s).val
    reserve0 := (observedBalance0 s).val
    reserve1 := (observedBalance1 s).val
    totalSupply := (mintFirstRoot s).val
    lockedLiquidity := minimumLiquidityNat }

def timestamp32 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mod s.blockTimestamp uint32Modulus

def skimExcess0 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance0 s) (s.storage reserve0Slot.slot)

def skimExcess1 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance1 s) (s.storage reserve1Slot.slot)

def swapExpected0 (amount0Out : Uint256) (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (s.storage reserve0Slot.slot) amount0Out

def swapExpected1 (amount1Out : Uint256) (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (s.storage reserve1Slot.slot) amount1Out

def swapAmount0In (amount0Out : Uint256) (balance0Now : Uint256) (s : ContractState) :
    Uint256 :=
  if balance0Now > swapExpected0 amount0Out s then
    Verity.EVM.Uint256.sub balance0Now (swapExpected0 amount0Out s)
  else
    0

def swapAmount1In (amount1Out : Uint256) (balance1Now : Uint256) (s : ContractState) :
    Uint256 :=
  if balance1Now > swapExpected1 amount1Out s then
    Verity.EVM.Uint256.sub balance1Now (swapExpected1 amount1Out s)
  else
    0

end TamaUniV2.Common.UniswapV2PairConcrete
