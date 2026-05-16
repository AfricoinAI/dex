import TamaUniV2.UniswapV2Factory

/-!
Concrete helper formulas for Uniswap V2 factory specs.

Helpers live outside `verity/spec` so only the public behavior obligations are
treated as Tama spec targets.
-/

namespace TamaUniV2.Common.UniswapV2FactoryConcrete

open Verity
open TamaUniV2.UniswapV2Factory

def factoryToken0 (tokenA tokenB : Address) : Address :=
  if (addressToWord tokenA) < (addressToWord tokenB) then tokenA else tokenB

def factoryToken1 (tokenA tokenB : Address) : Address :=
  if (addressToWord tokenA) < (addressToWord tokenB) then tokenB else tokenA

def factoryCreate2Word (tokenA tokenB : Address) : Uint256 :=
  externalCall "uniswapV2PairCreate2"
    [factoryToken0 tokenA tokenB, factoryToken1 tokenA tokenB]

def factoryLengthAfter (s : ContractState) : Uint256 :=
  s.storage allPairsLengthSlot.slot + 1

def factoryPairCreatedEvent
    (token0Value token1Value pair : Address) (lengthAfter : Uint256) : Event :=
  { name := "PairCreated"
    args := [
      addressToWord token0Value,
      addressToWord token1Value,
      addressToWord pair,
      lengthAfter
    ]
    indexedArgs := [] }

def factoryTraceContains (event : Event) (events : List Event) : Prop :=
  event ∈ events

end TamaUniV2.Common.UniswapV2FactoryConcrete
