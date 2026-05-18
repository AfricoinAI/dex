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

The factory spec is intentionally smaller than the Pair spec because the
factory's security job is narrower: it must create at most one pair for each
unordered token pair, make that pair discoverable in either token order, and
never rewrite earlier pair records. Correctness is the sorted append/write
behavior of a successful `createPair`; security is duplicate prevention and
state atomicity on failure; completeness is the finite-history guarantee that
all router-visible lookup and enumeration surfaces keep those properties
forever.

The assurance argument is:

1. Views expose the pair mapping and append-only pair array.
2. `createPair` rejects invalid input before crossing CREATE2.
3. A successful create stores both mapping directions, appends exactly one pair,
   increments length exactly once, and emits `PairCreated`.
4. The closed-world model lifts those one-step facts to every finite factory
   history: pair keys are sorted and unique, lookup is symmetric, old pairs are
   never overwritten, and array length equals the number of created pairs.

Read as a proof outline, the factory specs show that the public-call boundary
can either fail without changing factory-local state or append one new sorted
pair. Since the ghost model has no transition that rewrites old entries, the
finite-history theorems give routers the property they actually rely on:
unordered lookup is stable and unique forever.

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

/-- `getPair` is an exact read of the decoded bidirectional mapping entry and
does not mutate factory state. -/
def factory_getPair_run_success_frames_state
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  (getPair tokenA tokenB).run s =
    ContractResult.success
      (wordToAddress (s.storageMap2 pairForSlot.slot tokenA tokenB))
      s

/-- `allPairsLength` is an exact read of the append-only array length and does
not mutate factory state. -/
def factory_allPairsLength_run_success_frames_state
    (s : ContractState) : Prop :=
  (allPairsLength).run s =
    ContractResult.success (s.storage allPairsLengthSlot.slot) s

def factory_allPairs_success_spec (index : Uint256) (result : Address) (s : ContractState) : Prop :=
  index < s.storage allPairsLengthSlot.slot →
    result = wordToAddress (s.storageMapUint allPairsSlot.slot index)

/-- In-bounds enumeration is an exact read. If `index` is below
`allPairsLength`, the real public `allPairs(index)` run succeeds with the
decoded storage entry and leaves the factory state unchanged. Together with the
out-of-bounds exact revert below, this pins the complete router-visible array
boundary. -/
def factory_allPairs_run_success_in_bounds
    (index : Uint256) (s : ContractState) : Prop :=
  index < s.storage allPairsLengthSlot.slot →
    (allPairs index).run s =
      ContractResult.success
        (wordToAddress (s.storageMapUint allPairsSlot.slot index))
        s

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
The first successful `createPair` run is the base case for the
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

/-- The first successful real `createPair` from an empty public pair array
creates a one-pair factory history that already satisfies the factory
invariant: the pair entry is sorted and nonzero, there are no duplicates, and
the modeled count is exactly one. -/
def factory_createPair_first_success_preserves_good
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
              (s.storage allPairsLengthSlot.slot).val + 1 ≤
                Verity.Stdlib.Math.MAX_UINT256 →
                (createPair tokenA tokenB).run s =
                  ContractResult.success pair ((createPair tokenA tokenB).run s).snd →
                  FactoryWorldGood
                    { pairs := [{
                        token0 := token0Value
                        token1 := token1Value
                        pair := pair
                      }]
                      pairCount := 1 }

/-- In a nonempty factory, if the modeled state has the same public pair count
as storage and contains no entry for the sorted token pair, then a successful
`createPair` run appends exactly that sorted pair entry. -/
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

/-- A successful real `createPair` that matches a good modeled factory history
appends one new sorted pair and leaves the global factory invariant true:
entries remain sorted and nonzero, sorted token pairs remain unique, and the
modeled count still matches the list. -/
def factory_createPair_success_preserves_good
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
                  (s.storage allPairsLengthSlot.slot).val + 1 ≤
                    Verity.Stdlib.Math.MAX_UINT256 →
                    (createPair tokenA tokenB).run s =
                      ContractResult.success pair ((createPair tokenA tokenB).run s).snd →
                      FactoryWorldGood after

/-!
## Exact Guard Runs

These specs state canonical guard priority as exact public-call results.
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

/-- A successful `createPair` run proves that the early ordered guards passed
before the CREATE2 boundary: the token addresses were distinct, neither token
was zero, and the sorted pair mapping was empty. -/
def factory_createPair_success_implies_pre_create_guards
    (tokenA tokenB : Address) (s : ContractState)
    (result : ContractResult Address) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  result = (createPair tokenA tokenB).run s →
    (∃ pair, result = ContractResult.success pair result.snd) →
      tokenA ≠ tokenB ∧
      tokenA ≠ zeroAddress ∧
      tokenB ≠ zeroAddress ∧
      s.storageMap2 pairForSlot.slot token0Value token1Value = 0

/-!
## Concrete Storage Reconstruction

The closed-world factory model is useful only if a reader can connect it back
to real factory storage. This section states that connection in small pieces.
Given a reconstructed world that matches factory storage, the public length,
unordered pair mapping, and indexed `allPairs` array all agree with that world.
These facts let later append-only and uniqueness theorems speak about concrete
router-visible lookup behavior. Pair addresses are compared after the same
`wordToAddress` decoding used by the public views, avoiding any extra CREATE2
canonical-word assumption.
-/

def factory_concrete_world_length_matches_storage
    (s : ContractState) (w : FactoryWorldState) : Prop :=
  FactoryWorldMatchesStorage s w →
    w.pairCount = (s.storage allPairsLengthSlot.slot).val

def factory_concrete_world_lookup_matches_storage
    (s : ContractState) (w : FactoryWorldState)
    (tokenA tokenB pair : Address) : Prop :=
  FactoryWorldMatchesStorage s w →
    FactoryWorldContainsPair w tokenA tokenB pair →
      wordToAddress (s.storageMap2 pairForSlot.slot tokenA tokenB) = pair

/--
Concrete storage inherits the reachable factory validity invariant. If a
reconstructed reachable factory history contains an unordered token-pair entry,
then the decoded mapping slot for that token order returns the modeled pair,
the pair address is nonzero, and the two token addresses are distinct and
nonzero. This is the direct storage-facing version of the lookup property a
router relies on.
-/
def factory_concrete_reachable_lookup_is_valid
    (s : ContractState) (w : FactoryWorldState)
    (tokenA tokenB pair : Address) : Prop :=
  FactoryWorldReachable w →
    FactoryWorldMatchesStorage s w →
      FactoryWorldContainsPair w tokenA tokenB pair →
        wordToAddress (s.storageMap2 pairForSlot.slot tokenA tokenB) = pair ∧
        pair ≠ zeroAddress ∧
        tokenA ≠ tokenB ∧
        tokenA ≠ zeroAddress ∧
        tokenB ≠ zeroAddress

def factory_concrete_world_allPairs_matches_storage
    (s : ContractState) (w : FactoryWorldState)
    (index : Nat) (entry : FactoryWorldPair) : Prop :=
  FactoryWorldMatchesStorage s w →
    w.pairs[index]? = some entry →
      wordToAddress
        (s.storageMapUint allPairsSlot.slot (Core.Uint256.ofNat index)) =
          entry.pair

/-- A successful concrete `createPair` run preserves storage/model agreement.
If the pre-state factory storage is represented by a good closed-world history,
then the post-state storage is represented by that history with exactly the new
sorted pair appended. After one real success, the finite-history theorems still
describe concrete router-visible storage. -/
def factory_createPair_success_preserves_concrete_world_match
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
          FactoryWorldMatchesStorage s before →
            s.storageMap2 pairForSlot.slot token0Value token1Value = 0 →
              (∀ entry, entry ∈ before.pairs →
                entry.token0 ≠ token0Value ∨ entry.token1 ≠ token1Value) →
                pair ≠ zeroAddress →
                  (s.storage allPairsLengthSlot.slot).val + 1 ≤
                    Verity.Stdlib.Math.MAX_UINT256 →
                    (createPair tokenA tokenB).run s =
                      ContractResult.success pair ((createPair tokenA tokenB).run s).snd →
                      FactoryWorldMatchesStorage
                        ((createPair tokenA tokenB).run s).snd
                        after

/--
Successful creation installs the new pair in the concrete decoded lookup table
for both token orders. This is the router-facing consequence of the lower-level
storage writes: callers see the same pair from `getPair(tokenA, tokenB)` and
`getPair(tokenB, tokenA)`.
-/
def factory_createPair_success_adds_decoded_lookup
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  let pair := wordToAddress (factoryCreate2Word tokenA tokenB)
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot token0Value token1Value = 0 →
          pair ≠ zeroAddress →
            (s.storage allPairsLengthSlot.slot).val + 1 ≤
              Verity.Stdlib.Math.MAX_UINT256 →
              (createPair tokenA tokenB).run s =
                ContractResult.success pair ((createPair tokenA tokenB).run s).snd →
                wordToAddress
                    (((createPair tokenA tokenB).run s).snd.storageMap2
                      pairForSlot.slot tokenA tokenB) = pair ∧
                wordToAddress
                    (((createPair tokenA tokenB).run s).snd.storageMap2
                      pairForSlot.slot tokenB tokenA) = pair

/--
Successful creation cannot overwrite an existing reconstructed lookup. If the
pre-state storage/world correspondence says an unordered token pair already
resolves to `existingPair`, then after creating some other absent pair, the
post-state decoded mapping for that existing lookup still resolves to the same
address.
-/
def factory_createPair_success_preserves_existing_decoded_lookup
    (tokenA tokenB existing0 existing1 existingPair : Address)
    (s : ContractState) (before : FactoryWorldState) : Prop :=
  let token0Value := factoryToken0 tokenA tokenB
  let token1Value := factoryToken1 tokenA tokenB
  let pair := wordToAddress (factoryCreate2Word tokenA tokenB)
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        FactoryWorldGood before →
          FactoryWorldMatchesStorage s before →
            FactoryWorldContainsPair before existing0 existing1 existingPair →
              s.storageMap2 pairForSlot.slot token0Value token1Value = 0 →
                (∀ entry, entry ∈ before.pairs →
                  entry.token0 ≠ token0Value ∨ entry.token1 ≠ token1Value) →
                  pair ≠ zeroAddress →
                    (s.storage allPairsLengthSlot.slot).val + 1 ≤
                      Verity.Stdlib.Math.MAX_UINT256 →
                      (createPair tokenA tokenB).run s =
                        ContractResult.success pair ((createPair tokenA tokenB).run s).snd →
                        wordToAddress
                            (((createPair tokenA tokenB).run s).snd.storageMap2
                              pairForSlot.slot existing0 existing1) =
                          existingPair

/-!
## Concrete Factory Histories

The one-step storage/model agreement is useful because it composes. A finite
sequence of successful concrete `createPair` calls should keep the closed-world
factory history aligned with real storage at every endpoint. These specs are
the global version of that simulation argument.

The first fact says the correspondence itself is invariant across any concrete
create history. The next two facts project that invariant into the two surfaces
routers use: unordered `getPair` lookup and indexed `allPairs` enumeration.
Together they say successful creation may append new pairs, but every old
router-visible lookup and array entry remains stable for the rest of the
factory's lifetime.
-/

def factory_concrete_create_path_preserves_world_match
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
        FactoryWorldGood wAfter ∧
        FactoryWorldMatchesStorage sAfter wAfter

/--
Concrete create histories inherit the closed-world append-only length property.
If a real sequence of successful `createPair` calls starts from storage that is
represented by a good factory world, then the public `allPairsLength` value in
storage cannot go down by the end of that sequence. This is the router-visible
version of "successful factory operation only appends pairs."
-/
def factory_concrete_create_path_allPairsLength_never_decreases
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
        (sBefore.storage allPairsLengthSlot.slot).val ≤
          (sAfter.storage allPairsLengthSlot.slot).val

def factory_concrete_create_path_preserves_existing_decoded_lookup
    (existing0 existing1 existingPair : Address)
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryWorldContainsPair wBefore existing0 existing1 existingPair →
        FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
          wordToAddress
              (sAfter.storageMap2 pairForSlot.slot existing0 existing1) =
            existingPair

/--
Endpoint lookup validity for concrete create histories. If real successful
`createPair` calls take reconstructed storage from a reachable factory world to
a later world, then every unordered lookup contained in that endpoint world
decodes from storage to a nonzero pair for two distinct nonzero token
addresses. This is the finite-history version of the concrete lookup theorem
above.
-/
def factory_concrete_create_path_reachable_lookup_is_valid
    (tokenA tokenB pair : Address)
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  FactoryWorldReachable wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
        FactoryWorldContainsPair wAfter tokenA tokenB pair →
          wordToAddress (sAfter.storageMap2 pairForSlot.slot tokenA tokenB) = pair ∧
          pair ≠ zeroAddress ∧
          tokenA ≠ tokenB ∧
          tokenA ≠ zeroAddress ∧
          tokenB ≠ zeroAddress

def factory_concrete_create_path_preserves_existing_allPairs_entry
    (index : Nat) (entry : FactoryWorldPair)
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      wBefore.pairs[index]? = some entry →
        FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
          wordToAddress
              (sAfter.storageMapUint allPairsSlot.slot
                (Core.Uint256.ofNat index)) =
            entry.pair

/--
Concrete same-length histories are real no-op histories at the factory model
boundary. A successful concrete create path can only append pairs; therefore,
if the public `allPairsLength` storage value is the same at both endpoints,
the reconstructed closed-world factory state is identical. This is the storage
counterpart of the closed-world "same count means no hidden array or lookup
change" theorem below.
-/
def factory_concrete_same_length_create_path_preserves_world
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
        (sBefore.storage allPairsLengthSlot.slot).val =
          (sAfter.storage allPairsLengthSlot.slot).val →
          wAfter = wBefore

/--
Concrete same-length histories preserve the reconstructed lookup relation.
This is the router-facing reading of the no-op theorem above: if a real
successful create history leaves `allPairsLength` unchanged, then the
reconstructed unordered lookup table contains exactly the same pairs at both
endpoints. No hidden create, overwrite, or deletion can be hiding behind an
unchanged public pair count.
-/
def factory_concrete_same_length_create_path_preserves_reconstructed_lookups
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
        (sBefore.storage allPairsLengthSlot.slot).val =
          (sAfter.storage allPairsLengthSlot.slot).val →
          ∀ tokenA tokenB pair,
            FactoryWorldContainsPair wAfter tokenA tokenB pair ↔
              FactoryWorldContainsPair wBefore tokenA tokenB pair

/-!
## Closed-World Factory Invariants

The concrete `createPair` specs above prove one real call writes the right local
storage. The closed-world specs below lift that single-step idea to arbitrary
finite histories of successful creates.

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

Together with the concrete create/revert specs, these are the global factory
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

/-- Reachability is closed under finite successful factory histories. Once a
factory state is reachable, appending any modeled sequence of successful
creates still ends in a reachable state. This is the trace-closure fact that
lets later invariants talk about suffixes of already-live factories. -/
def factory_closed_world_path_preserves_reachability
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldReachable before →
    FactoryWorldPath before after →
      FactoryWorldReachable after

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

/--
Reachable lookups never point at junk. If a factory history says an unordered
token pair has a pair address, then the address is nonzero and the token pair is
a valid Uniswap pair key: two distinct nonzero token addresses.

This is the small invariant that sits between the lower-level sorted-entry
facts and the way routers actually use the factory. A router does not care
which order the tokens were supplied in; it cares that any discovered pair is a
real pair for a real two-token market.
-/
def factory_closed_world_reachable_lookup_is_valid
    (w : FactoryWorldState) (tokenA tokenB pair : Address) : Prop :=
  FactoryWorldReachable w →
    FactoryWorldContainsPair w tokenA tokenB pair →
      pair ≠ zeroAddress ∧
      tokenA ≠ tokenB ∧
      tokenA ≠ zeroAddress ∧
      tokenB ≠ zeroAddress

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

/-- Router-facing lookup stability over histories. Once an unordered token pair
has a pair address in a reachable factory state, any later finite successful
create history still contains that same lookup. Pair creation can append new
pairs, but it cannot erase or overwrite old ones. -/
def factory_closed_world_reachable_path_preserves_pair_lookup
    (existing0 existing1 existingPair : Address)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldReachable before →
    FactoryWorldContainsPair before existing0 existing1 existingPair →
      FactoryWorldPath before after →
        FactoryWorldContainsPair after existing0 existing1 existingPair

/-- The factory pair array is append-only over every finite successful history.
There is always some suffix of newly created pairs such that the final array is
the initial array followed by that suffix, and the public pair count advances by
exactly the suffix length. This is the global version of "create does not
overwrite or reorder existing pairs." -/
def factory_closed_world_path_is_append_only
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldPath before after →
    ∃ suffix,
      after.pairs = before.pairs ++ suffix ∧
      after.pairCount = before.pairCount + suffix.length

/-- Pair enumeration is monotone over finite histories. Since successful
creation only appends, a later factory state cannot have a smaller public pair
count than an earlier state on the same modeled path. -/
def factory_closed_world_path_pair_count_never_decreases
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldPath before after →
    before.pairCount ≤ after.pairCount

/-- The append-only theorem in its audit-facing contrapositive shape. Along a
finite successful factory history, any change to the pair list must show up as
a larger pair count. Therefore a path whose pair count is unchanged cannot have
hidden writes, overwrites, or reordering in the pair array. -/
def factory_closed_world_same_count_path_preserves_pair_list
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldPath before after →
    before.pairCount = after.pairCount →
      after.pairs = before.pairs

/-- Same-count histories preserve the factory behavior routers actually see.
If a finite successful factory history leaves pair count unchanged, every
unordered token lookup is identical before and after the history. This is the
lookup-level version of "no hidden overwrite, no hidden deletion, no hidden
reorder." -/
def factory_closed_world_same_count_path_preserves_all_lookups
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldPath before after →
    before.pairCount = after.pairCount →
      ∀ tokenA tokenB pair,
        FactoryWorldContainsPair after tokenA tokenB pair ↔
          FactoryWorldContainsPair before tokenA tokenB pair

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
