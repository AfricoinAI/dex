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
Behavior specs for the Uniswap v2 factory.

The factory's job is narrower than the pair's: it must create at most one pair
for each unordered token pair, make that pair discoverable in either token
order, and never rewrite earlier records. The specs below split that job into
nine numbered properties; the body sections §1–§9 each prove exactly one
property. Supporting trace-closure facts are collected at the bottom.

## Properties

### Tier 1 — Security

1. **Unordered pair uniqueness** — each unordered token pair maps to at most
   one pair address in any reachable factory history.
2. **Append-only history** — across any finite successful create history, old
   pair entries are never overwritten, reordered, or deleted; the pair list
   only grows.

### Tier 2 — Correctness

3. **Symmetric lookup** — `getPair(A, B)` and `getPair(B, A)` return the same
   pair.
4. **Pair entries are well-formed** — every recorded pair has `token0 < token1`,
   two distinct nonzero token addresses, and a nonzero pair address.
5. **Length tracks created pairs** — `allPairsLength` equals the number of
   created pair entries.
6. **`createPair` appends exactly one new sorted pair on success** — storage
   writes, length, array entry, and event are all pinned in one bundle.
7. **`createPair` rejects invalid input with canonical reverts** — identical
   addresses, zero address, duplicates, CREATE2 failure, and length overflow
   each revert with the right payload; any revert leaves storage unchanged.

### Tier 3 — Transparency

8. **View functions are pure storage reads** — `getPair`, `allPairsLength`,
   in-bounds `allPairs`, and out-of-bounds `allPairs` reverts.
9. **Closed-world matching** — concrete factory storage agrees with the
   modeled history at every reachable state; successful create histories
   preserve that agreement and propagate router-visible facts (lookups, array
   entries, length) into real storage.

The actual CREATE2 deployment and pair initialization are external boundaries;
the specs only assume those calls at that boundary and prove factory-local
storage behavior directly.
-/

/-!
## 1. Unordered pair uniqueness
-/

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

/-!
## 2. Append-only history
-/

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

def factory_closed_world_path_preserves_existing_pairs
    (existing0 existing1 existingPair : Address)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldContainsPair before existing0 existing1 existingPair →
    FactoryWorldPath before after →
      FactoryWorldContainsPair after existing0 existing1 existingPair

/-- The append-only theorem in its audit-facing contrapositive shape. Along a
finite successful factory history, any change to the pair list must show up as
a larger pair count. Therefore a path whose pair count is unchanged cannot have
hidden writes, overwrites, or reordering in the pair array. -/
def factory_closed_world_same_count_path_preserves_pair_list
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldPath before after →
    before.pairCount = after.pairCount →
      after.pairs = before.pairs

/-!
## 3. Symmetric lookup
-/

def factory_closed_world_lookup_symmetric
    (w : FactoryWorldState) (tokenA tokenB pair : Address) : Prop :=
  FactoryWorldReachable w →
    FactoryWorldContainsPair w tokenA tokenB pair →
      FactoryWorldContainsPair w tokenB tokenA pair

def factory_closed_world_create_adds_symmetric_lookup
    (tokenA tokenB pair : Address)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldCreatePairStep tokenA tokenB pair before after →
    FactoryWorldContainsPair after tokenA tokenB pair ∧
    FactoryWorldContainsPair after tokenB tokenA pair

/-!
## 4. Pair entries are well-formed
-/

def factory_closed_world_created_pairs_are_sorted_and_nonzero
    (w : FactoryWorldState) : Prop :=
  FactoryWorldReachable w →
    ∀ entry, entry ∈ w.pairs → FactoryWorldPairGood entry

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

/-!
## 5. Length tracks created pairs
-/

def factory_closed_world_path_length_matches_created_pairs
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldGood before →
    FactoryWorldPath before after →
      after.pairCount = after.pairs.length

/-!
## 6. `createPair` appends exactly one new sorted pair on success
-/

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

/-- In a nonempty factory, if the modeled state has the same public pair count
as storage and contains no entry for the sorted token pair, then a successful
`createPair` run appends exactly that sorted pair entry. -/
def factory_createPair_success_matches_closed_world_step
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

def factory_closed_world_create_appends_one_pair
    (tokenA tokenB pair : Address)
    (before after : FactoryWorldState) : Prop :=
  FactoryWorldCreatePairStep tokenA tokenB pair before after →
    after.pairs.length = before.pairs.length + 1 ∧
    after.pairCount = before.pairCount + 1

/-!
## 7. `createPair` rejects invalid input
-/

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
## 8. View functions are pure storage reads
-/

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

def factory_allPairs_run_revert_out_of_bounds
    (index : Uint256) (s : ContractState) : Prop :=
  ¬ index < s.storage allPairsLengthSlot.slot →
    (allPairs index).run s =
      ContractResult.revert "UniswapV2: INDEX_OUT_OF_BOUNDS" s

/-!
## 9. Closed-world matching
-/

def factory_concrete_world_length_matches_storage
    (s : ContractState) (w : FactoryWorldState) : Prop :=
  FactoryWorldMatchesStorage s w →
    w.pairCount = (s.storage allPairsLengthSlot.slot).val

def factory_concrete_world_allPairs_matches_storage
    (s : ContractState) (w : FactoryWorldState)
    (index : Nat) (entry : FactoryWorldPair) : Prop :=
  FactoryWorldMatchesStorage s w →
    w.pairs[index]? = some entry →
      wordToAddress
        (s.storageMapUint allPairsSlot.slot (Core.Uint256.ofNat index)) =
          entry.pair

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

def factory_concrete_create_path_preserves_world_match
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) : Prop :=
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
        FactoryWorldGood wAfter ∧
        FactoryWorldMatchesStorage sAfter wAfter

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
Successful creation is immediately visible through the public `getPair` view.

This is the concrete router-facing form of the symmetric storage update: after
`createPair(tokenA, tokenB)` succeeds, both `getPair(tokenA, tokenB)` and
`getPair(tokenB, tokenA)` return the newly created pair in the post-state.
-/
def factory_createPair_success_getPair_views_return_new_pair
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
                let post := ((createPair tokenA tokenB).run s).snd
                (getPair tokenA tokenB).run post =
                  ContractResult.success pair post ∧
                (getPair tokenB tokenA).run post =
                  ContractResult.success pair post

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

/-!
## Closed-World Foundations

Trace-closure facts about the modeled factory history. These are the building
blocks the numbered properties above rest on: any finite sequence of valid
modeled creates preserves reachability and preserves the well-formedness of
the pair list.
-/

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

end TamaUniV2.Spec.UniswapV2FactorySpec
