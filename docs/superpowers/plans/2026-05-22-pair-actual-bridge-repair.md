# Pair Actual Bridge Repair Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the public headline theorem quantify over actual successful pair
executions rather than freely supplied ghost transitions, and finish with zero
assumptions about the pair contract's own storage/accounting behavior. The only
remaining assumptions should be explicit external-boundary facts for ERC20
tokens and callbacks.

**Architecture:** Treat this as two axes. The primary axis is ghost-vs-actual:
`pair_actual_execution_no_free_lunch` must consume concrete steps that include
`hRun : result = (op).run s` and `hSuccess`, and it must construct the
`PairWalletStep` instead of accepting one. The secondary axis is
proved-vs-assumed storage: each action bridge splits pair-internal storage facts
from field-level ERC20 token facts, proving storage from `.run` where tractable
and treating any remaining pair-storage assumption as unfinished work, not as an
acceptable final state.

**Tech Stack:** Lean 4, Verity/Tama specs, `lake build`, `/Users/zefram/.tama/bin/tama build`, `/Users/zefram/.tama/bin/tama test`, Foundry mirror tests.

---

## File Structure

- Modify `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
  - Replace whole-world `pairTokensBehaveNormallyForCall` with field-level projections of the existing ERC20 ECM boundary.
  - Add reusable pair-storage projection helpers.
  - Refactor `PairEconomicActionConcreteStep` so it records actual execution evidence and narrow external-token assumptions, not a supplied `PairWalletStep`.

- Modify `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
  - Update the six public `pair_<action>_success_reaches_expected_pair_state` specs to use narrow token assumptions.
  - Update `pair_actual_execution_no_free_lunch` to quantify over concrete economic histories that construct wallet steps from execution evidence.
  - Keep wording honest: the ERC20 trust boundary is about token0/token1 balance reads/transfers only.

- Modify `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
  - Add pair-storage post-state lemmas for mint, burn, and swap.
  - Wire existing skim/sync concrete lemmas into public bridges.
  - Rebuild public bridge proofs without whole-world post rewrites.
  - Construct `PairWalletStep` from concrete economic steps rather than accepting it as a field.

- Modify `verity/src/TamaUniV2/UniswapV2Pair.lean` only behind an explicit
  source-refactor decision gate. The helper names recorded in
  `docs/agent-progress.md` (`finishMintNoElapsed`, `burnNoElapsedPath`,
  `swapNoElapsedPath`, `completeBurnNoElapsed`, etc.) do not exist in the
  current tree. Reintroducing them changes generated Yul/bytecode and must be
  treated as a source change, not a proof-only reuse step.

- Modify `src/generated/verity/UniswapV2PairIface.sol` if `tama build`
  regenerates it. In particular, preserve the canonical `Sync(uint112,uint112)`
  event signature.

- Modify `tama.toml` and `tama.lock` only if the public spec surface changes.

- Modify mirror tests only 1-to-1 with changed public specs. Do not point several mirrors at one aggregate spec.

---

## Execution Order

Do not follow numeric task order blindly. The first complete vertical slice is:

1. Task 0: confirm helper/source-refactor status.
2. Task 1: split whole-world token predicates into storage and ERC20 fields.
3. Tasks 2-3: fix sync and skim bridges using existing concrete storage lemmas.
4. Task 7: rebuild concrete economic steps without supplied `hWalletStep`,
   initially for sync and skim, then extend to the other actions.
5. Task 9 non-vacuity checks for that slice.

That slice demonstrates the main goal: the headline theorem is about actual
successful executions and cannot be satisfied by a free ghost wallet step.
Tasks 4-6 then upgrade mint/burn/swap along the second axis by proving more
pair-storage arithmetic from `.run`; if a storage proof is intractable, the
remaining assumption must be explicit and named, while the concrete step still
requires actual `hRun`/`hSuccess`.

Final acceptance is stricter than the fallback: no public theorem should retain
an assumption about the pair's own reserve, LP supply, locked-liquidity, LP
balance, or lock-storage updates. The fallback exists only to keep intermediate
work honest if a proof route blocks.

---

### Task 0: Confirm Proof Infrastructure And Decide Source-Refactor Scope

**Files:**
- Read: `verity/src/TamaUniV2/UniswapV2Pair.lean`
- Read: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Read: `docs/agent-progress.md`
- Modify: `docs/agent-progress.md`

- [ ] **Step 1: Verify helper availability**

Run:

```bash
rg -n "finishMintNoElapsed|finishBurnNoElapsed|finishSwapNoElapsed|burnNoElapsedPath|swapNoElapsedPath|completeBurnNoElapsed" verity
```

Expected: no matches in the current tree. Treat any plan step that says "use
existing helper/suffix route" as stale unless this command proves otherwise.

- [ ] **Step 2: Choose the initial proof route**

Default route: no source change. First try storage post-state lemmas against the
current public `mint`, `burn`, and `swap` bodies using small private lemmas and
bounded reductions.

Forbidden route: do not silently reintroduce `*NoElapsedPath` or
`finish*NoElapsed` source helpers. If a storage theorem again hits Lean kernel
recursion or deterministic timeout, stop the task and record the exact failing
goal in `docs/agent-progress.md`.

- [ ] **Step 3: Source-refactor decision gate**

Only after a failed no-source proof attempt, decide whether to reintroduce
internal source helpers. If yes, create a separate source-refactor task before
continuing:

```text
Decision: Reintroduce internal helper(s) for [mint|burn|swap].
Reason: [exact theorem and failure mode].
Expected source impact: generated Yul/bytecode may change; CREATE2 salts and
mirror tests must be checked.
Required verification: lake build, tama build, tama test, forge build, generated
interface diff review, mirror alignment.
```

- [ ] **Step 4: Define fallback semantics**

If a storage proof remains intractable and source refactor is not accepted, do
not keep or rename the old whole-world post assumption, and do not present that
action as having a fully proved storage bridge. Instead, expose an honestly
named storage-write assumption such as:

```lean
pair_<action>_success_matches_modeled_pair_storage_assumption
```

The concrete economic step may still be actual-execution based if it requires
`hRun` and `hSuccess`; it is then actual execution modulo an explicit storage
assumption for that action. Wording must say that plainly.

---

### Task 1: Replace Whole-World Token Predicate With Narrow ERC20-Boundary Projections

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`

- [ ] **Step 1: Add pair-storage and token-balance helper predicates**

Add these definitions near the existing `pairWorldFromConcreteAndTokens` helpers:

```lean
def pairConcreteStorageMatchesWorld
    (s : ContractState) (w : PairWorldState) : Prop :=
  (s.storage reserve0Slot.slot).val = w.reserve0 ∧
  (s.storage reserve1Slot.slot).val = w.reserve1 ∧
  (s.storage totalSupplySlot.slot).val = w.totalSupply ∧
  pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) = w.lockedLiquidity

def pairTokenBalancesMatchWorld
    (tokens : PairTokenBalances) (s : ContractState)
    (w : PairWorldState) : Prop :=
  (pairTokenBalance0 tokens s).val = w.balance0 ∧
  (pairTokenBalance1 tokens s).val = w.balance1

def pairExternalTokenBalancesMatchCall {α : Type}
    (preTokens : PairTokenBalances) (s : ContractState)
    (result : ContractResult α)
    (before after : PairWorldState) : Prop :=
  let postTokens := pairTokenWorldAfterCall preTokens s result
  pairTokenBalancesMatchWorld preTokens s before ∧
  pairTokenBalancesMatchWorld postTokens result.snd after
```

This is not a new axiom. It is the field-level Lean projection of the existing
ERC20 `balanceOf`/`transfer` trust boundary already documented in `tama.toml`.
It must never mention reserve storage, total supply, locked liquidity, or LP
balances.

- [ ] **Step 2: Add action-specific narrow ERC20-boundary predicates**

Replace the current action predicates so they call `pairExternalTokenBalancesMatchCall`, not `pairTokensBehaveNormallyForCall`:

```lean
def pairFirstMintExternalTokenBalancesMatchCall
    (preTokens : PairTokenBalances) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  pairExternalTokenBalancesMatchCall preTokens s result
    (pairWorldBeforeMintRun s)
    (pairWorldAfterFirstMintRun s)
```

Repeat the same shape for later mint, burn, swap, skim, and sync using their existing expected world helpers.

- [ ] **Step 3: Delete the old whole-world predicate**

Remove public uses of:

```lean
pairTokensBehaveNormallyForCall
pairFirstMintTokensBehaveNormallyForCall
pairLaterMintTokensBehaveNormallyForCall
pairBurnTokensBehaveNormallyForCall
pairSwapTokensBehaveNormallyForCall
pairSkimTokensBehaveNormallyForCall
pairSyncTokensBehaveNormallyForCall
```

Do not keep a renamed private copy of the old whole-world predicate. Any proof
that needs it has not fixed the bridge.

- [ ] **Step 4: Add a reconstruction lemma**

Add a private theorem in `UniswapV2PairProof.lean`:

```lean
private theorem pairWorldFromConcreteAndTokens_eq_of_parts
    (tokens : PairTokenBalances) (s : ContractState)
    (expected : PairWorldState) :
  pairTokenBalancesMatchWorld tokens s expected →
    pairConcreteStorageMatchesWorld s expected →
      pairWorldFromConcreteAndTokens tokens s = expected := by
  intro h_tokens h_storage
  rcases h_tokens with ⟨h_balance0, h_balance1⟩
  rcases h_storage with ⟨h_reserve0, h_reserve1, h_supply, h_locked⟩
  cases expected
  simp [pairWorldFromConcreteAndTokens,
    pairTokenBalancesMatchWorld, pairConcreteStorageMatchesWorld] at *
  grind
```

- [ ] **Step 5: Run focused build**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
```

Expected: compilation failures only at bridge specs/proofs that still reference the old predicate. Fix imports/names before moving on.

---

### Task 2: Fix Sync Bridge Using Existing Concrete Storage Lemma

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`

- [ ] **Step 1: Update public sync spec premise**

Change the sync bridge premise from:

```lean
pairSyncTokensBehaveNormallyForCall preTokens s result →
```

to:

```lean
pairSyncExternalTokenBalancesMatchCall preTokens s result →
```

- [ ] **Step 2: Add storage extraction from the existing concrete lemma**

Add:

```lean
private theorem sync_success_run_storage_matches_world
    (s : ContractState) (result : ContractResult Unit) :
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      pairConcreteStorageMatchesWorld result.snd (pairWorldAfterSyncRun s) := by
  intro h_run h_success
  have h_world := sync_success_run_reaches_world s result h_run h_success
  unfold pairConcreteStorageMatchesWorld pairWorldFromConcreteState pairWorldAfterSyncRun
  constructor
  · exact congrArg PairWorldState.reserve0 h_world
  constructor
  · exact congrArg PairWorldState.reserve1 h_world
  constructor
  · exact congrArg PairWorldState.totalSupply h_world
  · exact congrArg PairWorldState.lockedLiquidity h_world
```

- [ ] **Step 3: Rewrite the sync bridge proof**

The proof must destruct only token fields:

```lean
rcases h_tokens with ⟨h_before_tokens, h_after_tokens⟩
have h_before :
    pairWorldFromConcreteAndTokens preTokens s = pairWorldFromConcreteState s := by
  exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
    (pairWorldFromConcreteState s) h_before_tokens (by simp [pairConcreteStorageMatchesWorld, pairWorldFromConcreteState])
have h_after :
    pairWorldFromConcreteAndTokens
      (pairTokenWorldAfterCall preTokens s result) result.snd =
        pairWorldAfterSyncRun s := by
  exact pairWorldFromConcreteAndTokens_eq_of_parts
    (pairTokenWorldAfterCall preTokens s result) result.snd
    (pairWorldAfterSyncRun s) h_after_tokens
    (sync_success_run_storage_matches_world s result h_run h_success)
rw [h_before, h_after]
exact sync_success_run_matches_closed_world_step_from_run s result h_run h_success
```

- [ ] **Step 4: Verify no whole-world post rewrite remains for sync**

Run:

```bash
rg -n "sync_success_reaches_expected_pair_state|rw \\[h_before, h_post\\]|pairSyncTokensBehaveNormallyForCall" verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean
```

Expected: no `h_post` rewrite in the sync bridge and no old sync predicate.

- [ ] **Step 5: Build**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
```

Expected: sync bridge compiles.

---

### Task 3: Fix Skim Bridge Using Existing Concrete Storage Lemma

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`

- [ ] **Step 1: Update public skim spec premise**

Change the skim bridge premise to:

```lean
pairSkimExternalTokenBalancesMatchCall preTokens s result →
```

- [ ] **Step 2: Add storage extraction from `skim_success_run_preserves_world`**

Add:

```lean
private theorem skim_success_run_storage_matches_world
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      pairConcreteStorageMatchesWorld result.snd (pairWorldAfterSkimRun s) := by
  intro h_run h_success
  have h_world := skim_success_run_preserves_world toAddr s result h_run h_success
  unfold pairConcreteStorageMatchesWorld pairWorldAfterSkimRun pairWorldFromConcreteState
  constructor
  · exact congrArg PairWorldState.reserve0 h_world
  constructor
  · exact congrArg PairWorldState.reserve1 h_world
  constructor
  · exact congrArg PairWorldState.totalSupply h_world
  · exact congrArg PairWorldState.lockedLiquidity h_world
```

- [ ] **Step 3: Rewrite skim bridge like sync**

Use `pairWorldFromConcreteAndTokens_eq_of_parts`, `h_before_tokens`, `h_after_tokens`, and `skim_success_run_storage_matches_world`. Do not destruct a whole post-world equality.

- [ ] **Step 4: Build and grep**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
rg -n "skim_success_reaches_expected_pair_state|rw \\[h_before, h_post\\]|pairSkimTokensBehaveNormallyForCall" verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean
```

Expected: build passes and no old skim bridge pattern remains.

---

### Task 4: Prove Mint Concrete Storage Post-State

**Files:**
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Do not modify source in this task. If the proof cannot be completed against
  the current source, return to Task 0 Step 3 and create a separate source
  refactor task.

- [ ] **Step 1: Add first-mint storage theorem**

Add a private theorem:

```lean
private def pair_first_mint_success_run_storage_matches_world
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  result = (mint toAddr).run s →
    result = ContractResult.success (mintFirstLiquidity s) result.snd →
      s.storage totalSupplySlot.slot = 0 →
        pairConcreteStorageMatchesWorld result.snd (pairWorldAfterFirstMintRun s)
```

Prove it from the current actual `mint.run`. There is no existing mint suffix
helper in the current tree. Use small private lemmas to reduce only the
successful first-mint branch and avoid a single full-body `simp` through the
sqrt bind. If the proof hits kernel recursion, record the exact reduced goal
and stop; do not add a whole-world post assumption.

- [ ] **Step 2: Add later-mint storage theorem**

Add:

```lean
private def pair_later_mint_success_run_storage_matches_world
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        pairConcreteStorageMatchesWorld result.snd
          (pairWorldAfterSubsequentMintRun liquidity s)
```

Prove it against the current source with the same bounded-reduction discipline.
Do not refer to `finishMintNoElapsed` unless Task 0 has explicitly introduced a
source-refactor task and that helper exists in `verity/src`.

- [ ] **Step 3: Update first and later mint public bridge specs**

Replace:

```lean
pairFirstMintTokensBehaveNormallyForCall preTokens s result →
pairLaterMintTokensBehaveNormallyForCall preTokens s liquidity result →
```

with:

```lean
pairFirstMintExternalTokenBalancesMatchCall preTokens s result →
pairLaterMintExternalTokenBalancesMatchCall preTokens s liquidity result →
```

- [ ] **Step 4: Rebuild mint bridges from token and storage pieces**

Use `pairWorldFromConcreteAndTokens_eq_of_parts` for before and after worlds. The after storage input must be `pair_first_mint_success_run_storage_matches_world` or `pair_later_mint_success_run_storage_matches_world`, not a premise.

- [ ] **Step 5: Focused verification**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
rg -n "pairFirstMintTokensBehaveNormallyForCall|pairLaterMintTokensBehaveNormallyForCall|first_mint_success_reaches_expected_pair_state|later_mint_success_reaches_expected_pair_state|rw \\[h_before, h_post\\]" verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean
```

Expected: build passes and mint bridges no longer use whole-world post assumptions.

---

### Task 5: Prove Burn Concrete Storage Post-State

**Files:**
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Do not modify source in this task. If current-source proof fails because of
  known public-body recursion, return to Task 0 Step 3.

- [ ] **Step 1: Add burn storage theorem**

Add:

```lean
private def pair_burn_success_run_storage_matches_world
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      pairConcreteStorageMatchesWorld result.snd (pairWorldAfterBurnRun s)
```

Prove it from the current actual `burn.run`. The helpers `burnNoElapsedPath` and
`completeBurnNoElapsed` do not exist in the current tree; do not reference them
unless a separate source-refactor task has added them and completed codegen
verification. The theorem must prove reserve0, reserve1, totalSupply, and
lockedLiquidity from pair storage writes. If the current-source proof is
intractable, stop at the Task 0 source-refactor decision gate.

- [ ] **Step 2: Update burn public bridge spec**

Replace:

```lean
pairBurnTokensBehaveNormallyForCall preTokens s result →
```

with:

```lean
pairBurnExternalTokenBalancesMatchCall preTokens s result →
```

- [ ] **Step 3: Rebuild burn bridge**

Use:

- `pairWorldFromConcreteAndTokens_eq_of_parts` for the pre-world.
- `pair_burn_success_run_storage_matches_world` for post storage.
- `h_after_tokens` from `pairBurnExternalTokenBalancesMatchCall` for post token balances.
- `burn_success_run_matches_closed_world_step` for the ghost step.

- [ ] **Step 4: Focused verification**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
rg -n "pairBurnTokensBehaveNormallyForCall|burn_success_reaches_expected_pair_state|rw \\[h_before, h_post\\]" verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean
```

Expected: build passes and burn bridge no longer uses whole-world post assumptions.

---

### Task 6: Prove Swap Concrete Storage Post-State With Explicit Post-Callback Final-Read Assumption

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Do not modify source in this task. If the proof needs a named post-callback
  helper state, return to Task 0 Step 3 before adding one to source.

- [ ] **Step 1: Add a narrow post-callback final-balance-read predicate**

Do not define this predicate over the pre-call state `s`. In the current source,
`swap` reads `balance0Now` and `balance1Now` after optimistic transfers and
after `uniswapV2CallbackModule` returns, immediately before input/K checks and
reserve writes. The predicate must be tied to that exact read point.

Add a predicate whose state argument is explicitly the post-callback read state:

```lean
def pairSwapFinalBalanceReadsMatch
    (postCallbackReadState : ContractState)
    (balance0Now balance1Now : Uint256) : Prop :=
  observedBalance0 postCallbackReadState = balance0Now ∧
  observedBalance1 postCallbackReadState = balance1Now
```

Then add or identify a proof-only relation that connects
`postCallbackReadState` to the actual successful `swap` prefix up to that read
point. If the current source cannot expose that point without a source helper,
stop and use Task 0 Step 3. The final-read predicate must mention only ERC20
balance reads, never pair reserve/supply storage.

The binding of `postCallbackReadState` is not an assumption. It must be derived
from the actual `swap` run or defined as a deterministic proof helper computed
from the same public-run prefix. Do not universally quantify over a caller-
chosen `postCallbackReadState`, and do not accept a premise that merely says a
convenient state is "the" post-callback read state.

- [ ] **Step 2: Add swap storage theorem**

Add:

```lean
private def pair_swap_success_run_storage_matches_world
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256)
    (s postCallbackReadState : ContractState)
    (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      pairSwapPostCallbackReadStateFromRun
        amount0Out amount1Out toAddr data s postCallbackReadState →
      pairSwapFinalBalanceReadsMatch postCallbackReadState balance0Now balance1Now →
        pairConcreteStorageMatchesWorld result.snd
          (pairWorldAfterSwapRun balance0Now balance1Now s)
```

Prove it against the current source or stop at the Task 0 source-refactor gate.
The proof may use the final-read predicate to rewrite the local values the pair
caches as reserves. It must not assume
`result.snd.storage reserve0Slot.slot = balance0Now` directly, and it must not
use a pre-state balance read as a substitute for the post-callback read.

`pairSwapPostCallbackReadStateFromRun` must itself be proved or definitionally
computed from the swap prefix. It is forbidden to prove it by assumption or add
it as an unconstrained constructor field.

- [ ] **Step 3: Update swap bridge spec**

Add the final-read premise and replace the old whole-world token predicate:

```lean
pairSwapFinalBalanceReadsMatch postCallbackReadState balance0Now balance1Now →
pairSwapExternalTokenBalancesMatchCall preTokens s balance0Now balance1Now result →
```

- [ ] **Step 4: Rebuild swap bridge**

Use `pair_swap_success_run_storage_matches_world` for post storage and `h_after_tokens` for post token balances. Keep the existing K-check and input/output premises.

- [ ] **Step 5: Focused verification**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
rg -n "pairSwapTokensBehaveNormallyForCall|swap_success_reaches_expected_pair_state|rw \\[h_before, h_post\\]" verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean
```

Expected: build passes and swap bridge no longer uses whole-world post assumptions.

---

### Task 7: Rebuild Concrete Economic Steps Without Supplied Wallet Steps

This is the load-bearing task for the headline theorem. Do it immediately after
Tasks 1-3 for a sync/skim vertical slice, before investing in the harder
mint/burn/swap storage proofs. The key success condition is that a concrete
path step cannot be built from a ghost transition alone; it must include actual
successful contract execution.

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`

- [ ] **Step 1: Replace `hWalletStep` fields**

Remove every constructor field named `hWalletStep` from
`PairEconomicActionConcreteStep`.

- [ ] **Step 2: Add concrete evidence fields by action**

First define field-level caller-token movement predicates. These are the wallet
side of the existing ERC20 boundary and must not mention `PairWalletStep` or
pair storage:

```lean
def callerExternalTokenBalancesMatch
    (caller : Address) (tokens : PairTokenBalances) (s : ContractState)
    (token0Value token1Value : Nat) : Prop :=
  (callerTokenBalance0 caller tokens s).val = token0Value ∧
  (callerTokenBalance1 caller tokens s).val = token1Value

def callerExternalTokenDeltaMatches
    (caller : Address) (preTokens postTokens : PairTokenBalances)
    (preState postState : ContractState)
    (before after : PairWalletWorldState) : Prop :=
  callerExternalTokenBalancesMatch caller preTokens preState
    before.callerToken0 before.callerToken1 ∧
  callerExternalTokenBalancesMatch caller postTokens postState
    after.callerToken0 after.callerToken1
```

Then use action-specific evidence:

- Mint: actual `mint caller` success, external token deposit facts for caller token0/token1 decreases, and the first/later mint bridge.
- Burn: actual LP `transfer pairSelf liquidity` success by the caller, actual `burn caller` success, external token payout facts for caller token0/token1 increases, and the burn bridge.
- Swap: external token input/callback repayment facts, actual `swap amount0Out amount1Out caller data` success, final-read facts, and the swap bridge.
- Skim: actual `skim caller` success, external token payout facts, and the skim bridge.
- Sync: actual `sync` success and the sync bridge.

Do not model burn as a bare `burn` call that magically decreases caller LP. The
caller LP decrease comes from the actual LP transfer to the pair before burn,
proved using the pair's internal LP `transfer` storage facts.

- [ ] **Step 2a: Add explicit LP storage lemmas needed by wallet steps**

These are required for the headline to be actual-execution based. They are low
recursion risk compared with AMM reserve arithmetic because they target LP
storage writes, not sqrt/oracle/K branches.

Add or reuse focused lemmas with these statements:

```lean
private def pair_mint_success_run_credits_recipient_lp
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256)
    (liquidity : Uint256) : Prop :=
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      (result.snd.storageMap balancesSlot.slot toAddr).val =
        (s.storageMap balancesSlot.slot toAddr).val + liquidity.val

private def pair_transfer_success_run_moves_lp_between_accounts
    (fromAddr toAddr : Address) (amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result = (transfer toAddr amount).run { s with sender := fromAddr } →
    result = ContractResult.success true result.snd →
      (result.snd.storageMap balancesSlot.slot fromAddr).val =
        (s.storageMap balancesSlot.slot fromAddr).val - amount.val ∧
      (result.snd.storageMap balancesSlot.slot toAddr).val =
        (s.storageMap balancesSlot.slot toAddr).val + amount.val
```

Prove the mint lemma from the actual LP mint storage write. Prove the transfer
lemma from the existing LP `transfer` run specs where possible. Neither proof may
use `PairWalletStep`.

For burn, construct the economic action from the caller's actual LP transfer to
the pair plus the successful `burn caller`; do not infer caller LP movement from
the burn call alone.

- [ ] **Step 3: Prove action constructors produce `PairWalletStep`**

Replace `pairEconomicActionConcreteStep_wallet` with proofs that construct `PairWalletStep` from:

- the corresponding public bridge theorem for `before.pair -> after.pair`;
- LP balance facts from pair storage for mint and LP transfer/burn;
- external token movement facts for token0/token1 wallet deltas.

For each constructor, add a focused non-vacuity lemma that exhibits a simple
consistent field assignment for the required caller-token predicate. These
lemmas are not economic safety theorems; they prevent the repair from replacing
the old whole-world assumption with an impossible wallet-side premise.

- [ ] **Step 4: Keep `PairEconomicActionConcretePath_walletHistory`**

After Step 3, the path projection may keep the same inductive-recursion shape:
case-split the concrete path, call `pairEconomicActionConcreteStep_wallet` on
each concrete step, and append the constructed wallet step to
`PairWalletHistory`. The difference is that
`pairEconomicActionConcreteStep_wallet` now proves the wallet step instead of
projecting a supplied field.

- [ ] **Step 5: Verify no supplied wallet-step field remains**

Run:

```bash
rg -n "hWalletStep|PairWalletStep .*before after\\)" verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean
```

Expected: no constructor field named `hWalletStep`; `PairWalletStep` remains only in theorem conclusions/proof targets.

---

### Task 8: Update Public Wording, Mirrors, And Metadata

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `tama.toml`
- Modify: `tama.lock`
- Modify: `src/generated/verity/UniswapV2PairIface.sol` if regenerated by Tama.
- Modify mirror tests only when their corresponding public spec changes.

- [ ] **Step 1: Update section wording**

Section 15 should say:

```text
Each successful public mutating call reaches the expected pair state by combining
pair-internal storage postconditions proved from the actual run with field-level
token-balance facts tied to the existing ERC20 balanceOf/transfer trust boundary.
```

- [ ] **Step 2: Update no-free-lunch wording**

Property 1 should say:

```text
The concrete economic path records actual pair calls, actual LP-share operations
performed by the pair, and field-level token0/token1 balance movement facts tied
to the existing ERC20 trust boundary. The theorem then projects that path to the
closed-world wallet history used by the model theorem.
```

- [ ] **Step 3: Update Tama metadata**

Run:

```bash
/Users/zefram/.tama/bin/tama build
```

Expected: metadata is regenerated for the renamed specs. If generated
`src/generated/verity/UniswapV2PairIface.sol` changes the `Sync` event from
`uint112` to `uint256`, restore the canonical `uint112` signature before
committing.

- [ ] **Step 4: Check mirror alignment**

For every changed public spec name, ensure exactly one mirror points to it. Remove mirrors for removed specs. Do not repoint obsolete mirrors to unrelated aggregate properties.

Run:

```bash
rg -n "pair_(first_mint|later_mint|burn|swap|skim|sync).*success_reaches_expected_pair_state|actual_execution_no_free_lunch" test verity tama.toml tama.lock
```

Expected: each public bridge has at most one corresponding mirror test, and no removed spec name appears.

---

### Task 9: Regression Verification

**Files:**
- No source edits unless a verification command exposes a real issue.

- [ ] **Step 1: Run anti-pattern grep**

Run:

```bash
rg -n "pairWorldFromConcreteAndTokens .*result\\.snd =|rw \\[h_before, h_post\\]|TokensBehaveNormallyForCall|hWalletStep|sorry|admit|axiom|native_decide" verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean
```

Expected:

- no whole-world post equality premise over `result.snd`;
- no bridge proof solved by `rw [h_before, h_post]`;
- no old `TokensBehaveNormallyForCall` names;
- no `hWalletStep` constructor field;
- no public theorem premise assuming pair-owned reserve, total-supply,
  locked-liquidity, LP balance, or lock-storage postconditions;
- no `sorry`, `admit`, `axiom`, or `native_decide`.

- [ ] **Step 2: Run non-vacuity checks**

Each bridge must have either:

- a focused Lean witness lemma showing the narrow token/caller-token predicates
  can be satisfied with concrete field assignments; or
- a 1-to-1 fuzz/invariant mirror that exercises the corresponding successful
  action with ordinary mock ERC20s.

Fill in this checklist before final verification:

```text
first_mint: witness lemma or mirror = <exact name/path>
later_mint: witness lemma or mirror = <exact name/path>
burn: witness lemma or mirror = <exact name/path>
swap: witness lemma or mirror = <exact name/path>
skim: witness lemma or mirror = <exact name/path>
sync: witness lemma or mirror = <exact name/path>
```

Then run targeted checks for the exact names in the checklist. Do not use a
broad keyword grep that matches the bridge theorem names themselves.

- [ ] **Step 3: Run swap final-read anti-pattern checks**

Run:

```bash
rg -n "pairSwapFinalBalanceReadsMatch s|postCallbackReadState.*→.*pairSwapFinalBalanceReadsMatch|hPostCallbackReadState|chosen postCallbackReadState" verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean
```

Expected: no pre-state final-read predicate, and no unconstrained premise that
lets the caller choose `postCallbackReadState`.

- [ ] **Step 4: Run focused Lean build**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
```

Expected: success.

- [ ] **Step 5: Run Tama build and tests**

Run:

```bash
/Users/zefram/.tama/bin/tama build
/Users/zefram/.tama/bin/tama test
```

Expected: both pass.

- [ ] **Step 6: Run Foundry build**

Run:

```bash
forge build
```

Expected: success with only existing warnings.

- [ ] **Step 7: Commit**

Run:

```bash
git add verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean src/generated/verity/UniswapV2PairIface.sol tama.toml tama.lock test docs/agent-progress.md docs/superpowers/plans/2026-05-22-pair-actual-bridge-repair.md
git commit -m "Prove pair bridges from actual storage postconditions"
```

Expected: one coherent commit containing the full bridge repair.

---

## Self-Review

- Spec coverage: Tasks 1-6 fix the six public pair-state bridges. Task 7 fixes the no-free-lunch path gap. Task 8 keeps public docs, Tama metadata, and mirrors aligned. Task 9 blocks the exact anti-pattern that caused the failed repair.
- Placeholder scan: the plan avoids whole-world post assumptions and names the exact predicates, files, and verification commands to use.
- Risk: mint/burn/swap storage lemmas are the hard part and previous helper
  routes are not present in the current tree. If current-source proofs expand
  too deeply, stop at the source-refactor decision gate; do not pretend those
  helpers already exist, and do not keep a renamed whole-world assumption.
