-- SPDX-License-Identifier: AGPL-3.0-only
import TamaUniV2.UniswapV2Factory
import TamaUniV2.Common.UniswapV2FactoryConcrete

/-!
Closed-world ghost model for Uniswap V2 factory invariants.

The executable factory crosses two external boundaries during `createPair`:
CREATE2 deployment and pair initialization. This model abstracts those
boundaries to a successful `(token0, token1, pair)` creation step and proves the
factory-local consequences over every finite sequence of such steps.

The factory model is deliberately smaller than the Pair model because the
factory has only one economic action: append a new pair. That smallness is the
security argument. If every valid step appends one sorted nonzero pair and the
path relation is just finite repetition of that step, then no successful
history can delete, reorder, or overwrite an existing unordered pair lookup.
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

def FactoryWorldEntryStored
    (s : ContractState) (entry : FactoryWorldPair) : Prop :=
  wordToAddress
      (s.storageMap2 TamaUniV2.UniswapV2Factory.pairForSlot.slot
        entry.token0 entry.token1) = entry.pair ∧
  wordToAddress
      (s.storageMap2 TamaUniV2.UniswapV2Factory.pairForSlot.slot
        entry.token1 entry.token0) = entry.pair

def FactoryWorldArrayEntryStored
    (s : ContractState) (index : Nat) (entry : FactoryWorldPair) : Prop :=
  wordToAddress
      (s.storageMapUint TamaUniV2.UniswapV2Factory.allPairsSlot.slot
        (Core.Uint256.ofNat index)) = entry.pair

/-!
`FactoryWorldMatchesStorage` is the bridge from public factory storage to the
closed-world history model. It deliberately says only what the factory itself
stores: the length slot matches the modeled pair count, every modeled pair has
both mapping directions written, and every modeled list index is present in the
public `allPairs` array. Pair addresses are compared through the same
`wordToAddress` decoding used by the public views, so this bridge does not need
an extra assumption that the CREATE2 ECM returns a canonical address word.
-/
def FactoryWorldMatchesStorage
    (s : ContractState) (w : FactoryWorldState) : Prop :=
  w.pairCount =
    (s.storage TamaUniV2.UniswapV2Factory.allPairsLengthSlot.slot).val ∧
  (∀ entry, entry ∈ w.pairs → FactoryWorldEntryStored s entry) ∧
  (∀ index entry,
    w.pairs[index]? = some entry →
      FactoryWorldArrayEntryStored s index entry)

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

/-!
Concrete create histories are the simulation boundary between executable
factory storage and the closed-world model above. A step records a successful
public `createPair` run and the corresponding modeled append action; it does
not assert the storage/world correspondence that the specs are meant to prove.
-/
def FactoryConcreteCreateStep
    (tokenA tokenB : Address)
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  let pair := wordToAddress (factoryCreate2Word tokenA tokenB)
  sBefore.storageMap2
      TamaUniV2.UniswapV2Factory.pairForSlot.slot
      (factoryToken0 tokenA tokenB)
      (factoryToken1 tokenA tokenB) = 0 ∧
  (sBefore.storage
      TamaUniV2.UniswapV2Factory.allPairsLengthSlot.slot).val + 1 ≤
        Verity.Stdlib.Math.MAX_UINT256 ∧
  (TamaUniV2.UniswapV2Factory.createPair tokenA tokenB).run sBefore =
    ContractResult.success pair sAfter ∧
  FactoryWorldStep
    (FactoryWorldAction.createPair tokenA tokenB pair)
    wBefore
    wAfter

inductive FactoryConcreteCreatePath :
    ContractState → FactoryWorldState → ContractState → FactoryWorldState → Prop where
  | refl (s : ContractState) (w : FactoryWorldState) :
      FactoryConcreteCreatePath s w s w
  | step
      {sStart sBefore sAfter : ContractState}
      {wStart wBefore wAfter : FactoryWorldState}
      (tokenA tokenB : Address) :
      FactoryConcreteCreatePath sStart wStart sBefore wBefore →
      FactoryConcreteCreateStep tokenA tokenB sBefore sAfter wBefore wAfter →
      FactoryConcreteCreatePath sStart wStart sAfter wAfter

end TamaUniV2.Common.UniswapV2FactoryGhost
