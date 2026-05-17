import TamaUniV2.UniswapV2Factory
import TamaUniV2.Common.UniswapV2FactoryConcrete

/-!
Closed-world ghost model for Uniswap V2 factory invariants.

The executable factory crosses two external boundaries during `createPair`:
CREATE2 deployment and pair initialization. This model abstracts those
boundaries to a successful `(token0, token1, pair)` creation step and proves the
factory-local consequences over every finite sequence of such steps.
-/

namespace TamaUniV2.Common.UniswapV2FactoryGhost

open Verity
open TamaUniV2.Common.UniswapV2FactoryConcrete

structure FactoryWorldPair where
  token0 : Address
  token1 : Address
  pair : Address
  deriving Repr, BEq

structure FactoryWorldState where
  pairs : List FactoryWorldPair
  pairCount : Nat
  deriving Repr, BEq

def FactoryWorldPairGood (entry : FactoryWorldPair) : Prop :=
  entry.token0 ≠ entry.token1 ∧
  entry.token0 ≠ zeroAddress ∧
  entry.token1 ≠ zeroAddress ∧
  addressToWord entry.token0 < addressToWord entry.token1 ∧
  entry.pair ≠ zeroAddress

def FactoryWorldNoDuplicateSortedPairs (pairs : List FactoryWorldPair) : Prop :=
  ∀ a b,
    a ∈ pairs →
      b ∈ pairs →
        a.token0 = b.token0 →
          a.token1 = b.token1 →
            a = b

def FactoryWorldGood (w : FactoryWorldState) : Prop :=
  (∀ entry, entry ∈ w.pairs → FactoryWorldPairGood entry) ∧
  FactoryWorldNoDuplicateSortedPairs w.pairs ∧
  w.pairCount = w.pairs.length

def FactoryWorldContainsPair
    (w : FactoryWorldState) (tokenA tokenB pair : Address) : Prop :=
  ∃ entry,
    entry ∈ w.pairs ∧
    ((entry.token0 = tokenA ∧ entry.token1 = tokenB) ∨
      (entry.token0 = tokenB ∧ entry.token1 = tokenA)) ∧
    entry.pair = pair

def FactoryWorldCreatePairStep
    (tokenA tokenB pair : Address)
    (before after : FactoryWorldState) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  tokenA ≠ tokenB ∧
  tokenA ≠ zeroAddress ∧
  tokenB ≠ zeroAddress ∧
  ((token0Value = tokenA ∧ token1Value = tokenB) ∨
    (token0Value = tokenB ∧ token1Value = tokenA)) ∧
  FactoryWorldPairGood {
    token0 := token0Value
    token1 := token1Value
    pair := pair
  } ∧
  (∀ entry, entry ∈ before.pairs →
    entry.token0 ≠ token0Value ∨ entry.token1 ≠ token1Value) ∧
  after.pairs = before.pairs ++ [{
    token0 := token0Value
    token1 := token1Value
    pair := pair
  }] ∧
  after.pairCount = before.pairCount + 1

inductive FactoryWorldAction where
  | createPair (tokenA tokenB pair : Address)

def FactoryWorldStep
    (action : FactoryWorldAction)
    (before after : FactoryWorldState) : Prop :=
  match action with
  | FactoryWorldAction.createPair tokenA tokenB pair =>
      FactoryWorldCreatePairStep tokenA tokenB pair before after

def FactoryWorldInitial : FactoryWorldState :=
  { pairs := []
    pairCount := 0 }

inductive FactoryWorldReachable : FactoryWorldState → Prop where
  | init : FactoryWorldReachable FactoryWorldInitial
  | step {before after : FactoryWorldState} (action : FactoryWorldAction) :
      FactoryWorldReachable before →
      FactoryWorldStep action before after →
      FactoryWorldReachable after

inductive FactoryWorldPath : FactoryWorldState → FactoryWorldState → Prop where
  | refl (w : FactoryWorldState) : FactoryWorldPath w w
  | step {start before after : FactoryWorldState} (action : FactoryWorldAction) :
      FactoryWorldPath start before →
      FactoryWorldStep action before after →
      FactoryWorldPath start after

end TamaUniV2.Common.UniswapV2FactoryGhost
