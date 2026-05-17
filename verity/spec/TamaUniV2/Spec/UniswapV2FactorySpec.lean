import TamaUniV2.UniswapV2Factory
import TamaUniV2.Common.UniswapV2FactoryConcrete
import TamaUniV2.Common.UniswapV2FactoryGhost

namespace TamaUniV2.Spec.UniswapV2FactorySpec

open Verity
open Verity.EVM.Uint256
open TamaUniV2.UniswapV2Factory
open TamaUniV2.Common.UniswapV2FactoryConcrete
open TamaUniV2.Common.UniswapV2FactoryGhost

/-!
Behavior specs for the fee-off Uniswap v2 factory.

The factory assurance argument is:

1. Views expose the pair mapping and append-only pair array.
2. `createPair` rejects invalid input before crossing CREATE2.
3. A successful create stores both mapping directions, appends exactly one pair,
   increments length exactly once, and emits `PairCreated`.
4. Closed-world factory specs express the global consequence: every reachable
   factory state has symmetric pair lookup, unique sorted pairs, and array
   length equal to the number of created pairs.

The actual CREATE2 deployment and pair initialization are external boundaries;
the specs only assume those calls at that boundary and prove factory-local
storage behavior directly.
-/

/-!
## Views

These specs tie each public view to the storage location it is supposed to read.
`getPair` is a bidirectional mapping once creation succeeds; `allPairs` is
defined only below the current length.
-/

def factory_getPair_spec (tokenA tokenB result : Address) (s : ContractState) : Prop :=
  result = wordToAddress (s.storageMap2 pairForSlot.slot tokenA tokenB)

def factory_allPairsLength_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage allPairsLengthSlot.slot

def factory_allPairs_success_spec (index : Uint256) (result : Address) (s : ContractState) : Prop :=
  index < s.storage allPairsLengthSlot.slot →
    result = wordToAddress (s.storageMapUint allPairsSlot.slot index)

/-!
## Create-Pair Transition

Successful pair creation crosses the CREATE2 and pair-initialize boundaries.
Factory-local storage and ordering behavior should still be specified directly;
only the external deployment/call effects belong at those boundaries.

The success spec is intentionally compact: once all guards pass and CREATE2
returns a nonzero pair, the post-state has the sorted and reverse mapping
entries, the new pair is appended at the old length, the length increments by
one, and the canonical event is present.
-/

def factory_allPairs_reverts_out_of_bounds
    (index : Uint256) (s : ContractState) (result : ContractResult Address) : Prop :=
  ¬ index < s.storage allPairsLengthSlot.slot →
    result = ContractResult.revert "UniswapV2: INDEX_OUT_OF_BOUNDS" s

def factory_createPair_rejects_identical_addresses
    (tokenA tokenB : Address) (s : ContractState) (result : ContractResult Address) : Prop :=
  tokenA = tokenB →
    result = ContractResult.revert "UniswapV2: IDENTICAL_ADDRESSES" s

def factory_createPair_rejects_zero_address
    (tokenA tokenB : Address) (s : ContractState) (result : ContractResult Address) : Prop :=
  tokenA ≠ tokenB →
    (tokenA = zeroAddress ∨ tokenB = zeroAddress) →
      result = ContractResult.revert "UniswapV2: ZERO_ADDRESS" s

def factory_createPair_rejects_duplicates
    (tokenA tokenB : Address) (s : ContractState) (result : ContractResult Address) : Prop :=
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot
          (if (addressToWord tokenA) < (addressToWord tokenB) then tokenA else tokenB)
          (if (addressToWord tokenA) < (addressToWord tokenB) then tokenB else tokenA) ≠ 0 →
          result = ContractResult.revert "UniswapV2: PAIR_EXISTS" s

def factory_createPair_success_updates_storage_and_emits
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  let pairWord := factoryCreate2Word tokenA tokenB
  let pair := wordToAddress pairWord
  let lengthBefore := s.storage allPairsLengthSlot.slot
  let lengthAfter := factoryLengthAfter s
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot token0Value token1Value = 0 →
          pair ≠ zeroAddress →
            lengthBefore.val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
              (createPair tokenA tokenB).run s =
                ContractResult.success pair ((createPair tokenA tokenB).run s).snd ∧
              ((createPair tokenA tokenB).run s).snd.storageMap2
                pairForSlot.slot token0Value token1Value = pairWord ∧
              ((createPair tokenA tokenB).run s).snd.storageMap2
                pairForSlot.slot token1Value token0Value = pairWord ∧
              ((createPair tokenA tokenB).run s).snd.storageMapUint
                allPairsSlot.slot lengthBefore = pairWord ∧
              ((createPair tokenA tokenB).run s).snd.storage
                allPairsLengthSlot.slot = lengthAfter ∧
              factoryTraceContains
                (factoryPairCreatedEvent token0Value token1Value pair lengthAfter)
                ((createPair tokenA tokenB).run s).snd.events

/--
The first successful `createPair` run is the executable base case for the
closed-world factory model. When the concrete guards pass from an empty public
pair array, the run creates exactly the one modeled sorted pair entry that the
finite-trace invariants start from.
-/
def factory_createPair_first_success_refines_closed_world
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  let pair := wordToAddress (factoryCreate2Word tokenA tokenB)
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storage allPairsLengthSlot.slot = 0 →
          s.storageMap2 pairForSlot.slot token0Value token1Value = 0 →
            pair ≠ zeroAddress →
              (s.storage allPairsLengthSlot.slot).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
                (createPair tokenA tokenB).run s =
                  ContractResult.success pair ((createPair tokenA tokenB).run s).snd →
                  FactoryWorldStep
                    (FactoryWorldAction.createPair tokenA tokenB pair)
                    FactoryWorldInitial
                    { pairs := [{
                        token0 := token0Value
                        token1 := token1Value
                        pair := pair
                      }]
                      pairCount := 1 }

/--
The general success bridge adds the correspondence needed for nonempty factory
histories. If a modeled factory state has the same public pair count as the
concrete pre-state and contains no entry for the sorted token pair, then a
successful executable `createPair` run instantiates the closed-world create
transition by appending exactly that sorted pair entry.
-/
def factory_createPair_success_refines_closed_world
    (tokenA tokenB : Address) (s : ContractState)
    (before : FactoryWorldState) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  let pair := wordToAddress (factoryCreate2Word tokenA tokenB)
  let after : FactoryWorldState :=
    { pairs := before.pairs ++ [{
        token0 := token0Value
        token1 := token1Value
        pair := pair
      }]
      pairCount := before.pairCount + 1 }
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        FactoryWorldGood before →
          before.pairCount = (s.storage allPairsLengthSlot.slot).val →
            s.storageMap2 pairForSlot.slot token0Value token1Value = 0 →
              (∀ entry, entry ∈ before.pairs →
                entry.token0 ≠ token0Value ∨ entry.token1 ≠ token1Value) →
                pair ≠ zeroAddress →
                  (s.storage allPairsLengthSlot.slot).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
                    (createPair tokenA tokenB).run s =
                      ContractResult.success pair ((createPair tokenA tokenB).run s).snd →
                      FactoryWorldStep
                        (FactoryWorldAction.createPair tokenA tokenB pair)
                        before
                        after

/-!
## Exact Guard Runs

These specs state canonical guard priority as exact executable run results.
Each branch supplies hypotheses that earlier guards have passed, so a proof of
the spec fixes both the revert payload and original-state frame for that guard.
-/

def factory_allPairs_run_revert_out_of_bounds
    (index : Uint256) (s : ContractState) : Prop :=
  ¬ index < s.storage allPairsLengthSlot.slot →
    (allPairs index).run s =
      ContractResult.revert "UniswapV2: INDEX_OUT_OF_BOUNDS" s

def factory_createPair_run_revert_identical_addresses
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  tokenA = tokenB →
    (createPair tokenA tokenB).run s =
      ContractResult.revert "UniswapV2: IDENTICAL_ADDRESSES" s

def factory_createPair_run_revert_zero_address
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  tokenA ≠ tokenB →
    (tokenA = zeroAddress ∨ tokenB = zeroAddress) →
      (createPair tokenA tokenB).run s =
        ContractResult.revert "UniswapV2: ZERO_ADDRESS" s

def factory_createPair_run_revert_duplicates
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot
          (if (addressToWord tokenA) < (addressToWord tokenB) then tokenA else tokenB)
          (if (addressToWord tokenA) < (addressToWord tokenB) then tokenB else tokenA) ≠ 0 →
          (createPair tokenA tokenB).run s =
            ContractResult.revert "UniswapV2: PAIR_EXISTS" s

def factory_createPair_run_revert_create2_failed
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot token0Value token1Value = 0 →
          factoryCreate2Word tokenA tokenB = 0 →
            (createPair tokenA tokenB).run s =
              ContractResult.revert "UniswapV2: CREATE2_FAILED" s

def factory_createPair_run_revert_pair_count_overflow
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot token0Value token1Value = 0 →
          wordToAddress (factoryCreate2Word tokenA tokenB) ≠ zeroAddress →
            (s.storage allPairsLengthSlot.slot).val + 1 > Verity.Stdlib.Math.MAX_UINT256 →
              (createPair tokenA tokenB).run s =
                ContractResult.revert "UniswapV2: PAIR_COUNT_OVERFLOW" s

def factory_createPair_revert_keeps_factory_state
    (tokenA tokenB : Address) (s : ContractState)
    (result : ContractResult Address) : Prop :=
  result = (createPair tokenA tokenB).run s →
    (∃ reason, result = ContractResult.revert reason s) →
      result.snd.storageMap2 pairForSlot.slot =
        s.storageMap2 pairForSlot.slot ∧
      result.snd.storageMapUint allPairsSlot.slot =
        s.storageMapUint allPairsSlot.slot ∧
      result.snd.storage allPairsLengthSlot.slot =
        s.storage allPairsLengthSlot.slot ∧
      result.snd.events = s.events

/-!
## Closed-World Factory Invariants

The executable success spec above proves one concrete `createPair` run writes
the right local storage. The closed-world specs below lift that single-step idea
to arbitrary finite histories of successful creates.

The intended reader story is:

* Every successful create appends one sorted `(token0, token1, pair)` entry.
* The sorted token pair is unique, so the factory cannot create two pairs for
  the same unordered token pair.
* Lookup is symmetric because the model records unordered membership.
* The public array length is exactly the number of created pairs in the modeled
  history.
* The path-level specs lift those one-step facts to any finite suffix from a
  good factory state: created pairs remain present, the list remains coherent,
  and length keeps matching the number of created pairs.

Together with the executable create/revert specs, these are the global factory
facts that users and routers depend on: deterministic uniqueness, no hidden
overwrite, and append-only enumeration.
-/

def factory_closed_world_step_preserves_good
    (action : FactoryWorldAction)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldGood before →
    FactoryWorldStep action before after →
      FactoryWorldGood after

def factory_closed_world_reachable_good
    (w : FactoryWorldState) : Prop :=
  FactoryWorldReachable w →
    FactoryWorldGood w

def factory_closed_world_path_preserves_good
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldGood before →
    FactoryWorldPath before after →
      FactoryWorldGood after

def factory_closed_world_created_pairs_are_sorted_and_nonzero
    (w : FactoryWorldState) : Prop :=
  FactoryWorldReachable w →
    ∀ entry, entry ∈ w.pairs → FactoryWorldPairGood entry

def factory_closed_world_sorted_pair_unique
    (w : FactoryWorldState) : Prop :=
  FactoryWorldReachable w →
    FactoryWorldNoDuplicateSortedPairs w.pairs

def factory_closed_world_lookup_symmetric
    (w : FactoryWorldState) (tokenA tokenB pair : Address) : Prop :=
  FactoryWorldReachable w →
    FactoryWorldContainsPair w tokenA tokenB pair →
      FactoryWorldContainsPair w tokenB tokenA pair

/-- The user-facing uniqueness theorem for factory lookup. In any reachable
factory history, an unordered token pair can name at most one pair address. This
is the closed-world version of the property routers rely on when they use
`getPair(tokenA, tokenB)` and `getPair(tokenB, tokenA)` interchangeably. -/
def factory_closed_world_unordered_pair_address_unique
    (w : FactoryWorldState) (tokenA tokenB pairA pairB : Address) : Prop :=
  FactoryWorldReachable w →
    FactoryWorldContainsPair w tokenA tokenB pairA →
      FactoryWorldContainsPair w tokenA tokenB pairB →
        pairA = pairB

def factory_closed_world_create_appends_one_pair
    (tokenA tokenB pair : Address)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldCreatePairStep tokenA tokenB pair before after →
    after.pairs.length = before.pairs.length + 1 ∧
    after.pairCount = before.pairCount + 1

def factory_closed_world_create_adds_symmetric_lookup
    (tokenA tokenB pair : Address)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldCreatePairStep tokenA tokenB pair before after →
    FactoryWorldContainsPair after tokenA tokenB pair ∧
    FactoryWorldContainsPair after tokenB tokenA pair

def factory_closed_world_create_preserves_existing_pairs
    (tokenA tokenB pair existing0 existing1 existingPair : Address)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldContainsPair before existing0 existing1 existingPair →
    FactoryWorldCreatePairStep tokenA tokenB pair before after →
      FactoryWorldContainsPair after existing0 existing1 existingPair

def factory_closed_world_path_preserves_existing_pairs
    (existing0 existing1 existingPair : Address)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldContainsPair before existing0 existing1 existingPair →
    FactoryWorldPath before after →
      FactoryWorldContainsPair after existing0 existing1 existingPair

def factory_closed_world_length_matches_created_pairs
    (w : FactoryWorldState) : Prop :=
  FactoryWorldReachable w →
    w.pairCount = w.pairs.length

def factory_closed_world_path_length_matches_created_pairs
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldGood before →
    FactoryWorldPath before after →
      after.pairCount = after.pairs.length

end TamaUniV2.Spec.UniswapV2FactorySpec
