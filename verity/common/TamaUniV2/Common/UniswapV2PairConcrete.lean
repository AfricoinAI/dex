import TamaUniV2.UniswapV2Pair

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
