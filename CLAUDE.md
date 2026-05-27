# Lessons for future Claude sessions on this repo

## Public theorem text must add independent evidence

Never treat "the public theorem now mentions X" as proof that the corpus establishes X. Audit-facing conjuncts must be independently derived from runtime execution, verifier/circuit facts, storage state, or explicit trusted assumptions. They must not merely repackage a premise field, alias a premise, unfold to the same predicate, or discharge by `exact hPre.foo` / `simpa using hPre.foo`.

Before committing a theorem-shape change, run the first-principles check manually:
- Unfold every new public spec conjunct and compare it to the available hypotheses. If conclusion == premise, delete it or derive it from lower-level evidence.
- For every new helper theorem, ask what new information it adds after unfolding. Projection lemmas are fine only when the public theorem makes clear that the property is caller-supplied / trusted; they are not fine as "observed runtime proof" claims.
- Empty or constant contexts (ignored `_pre/_post`, zeroed contributions) do not carry meaning. Keep them out of audit-facing `_meets_spec` conclusions unless the claim is explicitly "no obligation."
- Build green is not evidence of theorem meaning. Add/strengthen semantic anti-tautology gates when a branch changes public theorem surfaces, axiom shapes, or audit claims.

## Heartbeat budget is non-negotiable

`maxHeartbeats` is a structural signal, not a knob. One file proof run target: <30s, hard ceiling 3min. Default `200000` heartbeats. NEVER permanently bump beyond that — not 400k, not 1M, definitely not 4M. If a proof times out, the shape is wrong; reshape via parametric helpers, named tail lemmas, normalized-form bind/match shape lemmas, or staged rewrites. Bumping heartbeats temporarily is OK ONLY as a diagnostic to confirm proof structure is sound (just slow); revert before commit. A heartbeats-pumped proof is a latent failure, not a finished one.

## A correct proof is fast

If a proof is taking minutes (or a build "hangs"), suspect a pathological reduction, not a slow machine. A `(kernel) deterministic timeout` means the proof *term* forces the kernel to reduce something expensive (e.g. casing/`rfl` over a large stuck application whose body pulls in heavy math). `maxHeartbeats` bounds the elaborator, NOT the kernel — a kernel timeout won't be caught by a heartbeat cap. Fix by keeping the expensive term abstract: `generalize <bigterm> = d` before `cases d`, so the case analysis is over a variable and the kernel never reduces the body.

## Fast iteration over slow rebuilds

When debugging one slow/failing declaration, do NOT iterate by rebuilding the whole module (which re-elaborates every heavy theorem and only reports at end-of-file). Isolate: copy the failing theorem into a scratch file that imports the (cached) dependencies and stubs the module-internal lemmas it uses as `axiom`s. Building the scratch recompiles only it — seconds, not minutes — and gives a tight loop on the actual problem. A whole-module rebuild gives zero feedback until it finishes, which is the opposite of debugging.

## Don't bail on "lots of work"

N hand copies / N-day proof = wrong-shape signal. Find parametric / induction / macro shape that makes proof O(1). "5 days of typing N lemmas" = failure mode, not workload.

## Work fits in a single turn

NEVER stop because you think the work won't fit in a single-turn window. Just do what needs to be done. Lots of work fits one turn when shape is right; if shape is wrong, fix the shape, don't punt.

## Time estimates are ~100x too long

Tasks framed as "~5 days" usually take hours. Discount aggressively. Commit + iterate, don't pre-emptively scope down.

## First principles over brute force

2000-line unrolled refinement / 100-lemma chain = problem statement too narrow. Reshape the problem, not the labor.

## Implementation flow

**File-disjoint per component**:
1. Plan first: per-component sections (Purpose / Storage / API / Security props with theorem witnesses / gaps) in a plan doc. Iterate plan with codex review until READY.
2. `general-purpose` agents per component, `isolation: "worktree"`, `run_in_background: true`. Each: implement → simplify (`code-simplifier` agent for TS/JS surfaces; codex direct CLI scoped to dead-code / duplication / proof tightening for Lean/Yul) → commit.
3. Commit is mandatory for general-purpose agents — say so explicitly + verify with `git log -1 --oneline` before returning.
4. Orchestrator-level codex review per-component after commits land. Tight prompts.
5. Holistic review across components for cross-cutting issues (slot collisions, axiom drift, pattern divergence).
6. PR off branch.

**File-shared phased work**:
1. Plan locks every phase boundary. Adversarial codex review × 2 before execution. Pin architectural decisions as numbered "Decision N" entries the executor cites verbatim.
2. One codex per phase. Codex edits, orchestrator commits (codex sandbox blocks `.git`).
3. Split phases >500 LOC preemptively into Xa/Xb.
4. Build green = only fitness signal. No partial-phase commits.
5. Mid-stream review every 3-4 phases (see "Mid-execution review checkpoints"). Holistic review at plan end.

## Plan file standard

Location: `docs/<TOPIC>_PLAN.md`. ALL_CAPS topic, `_PLAN.md` suffix.

Three sections, in order:
1. **Purpose** — one paragraph. What the plan is about and the user-facing reason it exists. No history, no alternatives considered.
2. **Steps** — numbered list. Each step is a concrete, actionable change citing exact files (and line numbers when stable). Decisions only — no "we could", no tradeoffs, no fallbacks.
3. **End state** — bulleted list of observable post-conditions. Each bullet is a checkable fact about the repo after the plan executes (file deleted, theorem provable, build green, ABI surface, etc.).

Forbidden in plan files:
- Time estimates ("~1 day", "5 hours").
- Speculation ("might", "could", "if X then maybe Y").
- Pros/cons or tradeoff tables — pick one path and commit.
- Deliberation text — no "we considered X but chose Y".
- Status/progress notes — plans are forward-looking specs, not journals.
- Roadmap / future-work asides — split into a separate plan if needed.

A reader should be able to execute the plan top-to-bottom without making design decisions. If a decision still needs to be made, resolve it before writing the plan.

## Slot parameterization day one

Every storage component: a `<Component>Config` record with per-slot fields, default `slot 0`. Pair with an `example : <config>.xSlot = 0 := rfl` sanity check so downstream composition can reassign without re-proving. Retrofitting later = whole fix batch.

## Preserve theorem names from plan verbatim

Manifest couples plan → Lean → Foundry by exact string match. Renames silently break coverage.

## Monitor long-running work

Monitor tool watching mtimes / git HEAD / output sizes / PID. Heartbeat 5-15min for proofs (60-120s silence normal during simp tuning), 30-60s for build / process-liveness. Two monitors: commit-watcher + per-task PID-watcher. Cross-check ledger PID with `kill -0 <pid>` — stale entries fire DONE prematurely.

## Code comments = invariants, not history

No phase / commit hash / session names in code. WHY-historical → commit message. Default = no comment.

## Document what exists, not what's coming

"Production X will…" / "future Y swap-in…" = overreach. Roadmap belongs in plan docs, not READMEs. Placeholder = state plainly + stop.

## "What the reader CANNOT conclude" = unproven first-principle properties only

When a README has a "What the reader can / CANNOT conclude" section, the CANNOT side is the easiest to bloat and the easiest to make useless. Discipline:

**Keep ONLY**: first-principle security properties an auditor would reasonably expect to be proven by this component but ARE NOT, with a stated reason (Verity macro restriction, deferred to composition, pure-scope only with no harness wrapper, etc.).

**Move to Trust block**: cryptographic axioms, idealizations, caller-conditional properties supplied by composers, EVM semantics inherited. These are explicit trust surface, not "things the reader can't conclude."

**Drop entirely**: random architectural facts that aren't security properties ("component doesn't own namespaced storage", "tests use mocks", "this is a library not a contract").

Each kept item is one unprovable security property + the structural reason it's unprovable. If you can't state the gap in one sentence with a structural reason, it doesn't belong in this section. Bloat = "the component doesn't prove world peace either" — useless. Discipline = each gap is concrete and audit-actionable.

## No placeholders to audit surface

Placeholder claiming a formal property it doesn't enforce = NOT-SECURE. Either upgrade to real or keep out of the source/spec/proof aggregates until real.

## Verity EDSL footguns

- `ite / logicalAnd / logicalOr` with call-like operands → call duplicated into branches, all execute. Use `if do … else do …` statement-level.
- Nested `Stmt.ite` → `pickFreshName` collision against compiler-generated `__ite_cond` temp. Flat empty-else `if` chain with early `return`.
- Dynamic array params can't ride `externalCall` → pass `(static args, arrayLength)`, Yul helper decodes from calldata.
- Selector depends on param type spelling. `Array Uint256` → `foo(uint256[])`; `Array Bytes32` → `foo(bytes32[])`.

## Standalone vs component ABI

Standalone = ABI public commitment, can't drop an arg Lean ignores. Inlined = ABI internal, reshapeable. Decide before harness.

## Bridge axioms pin stub returns

`∀ x, OpaquePred x` = tautology dressed as bridge. Correct: `externalCallWords sym args = f args`. Caller proves stub returned specific value before invoking opaque. Cross-check every `externalCall_eq_*` axiom has stub-return form.

## Generic-predicate projections weaken theorems

"For arbitrary `ctx.f = g`, the conclusion holds" = vacuous. Pin to the mode-specific shape (e.g. `+depositedAmount` / `-withdrawnAmount`) and add the corresponding hypothesis. A projection over an unconstrained context proves nothing.

## Tautology check `↔` theorems

`A ↔ B` where both unfold to the same def = `rfl`, not a theorem. Fix: distinct opaque content per side, or delete.

## Foundry tests = observable effects, not dispatch shape

`assertEq(ret, 0)` witnesses nothing. Need balance delta / event field check / `vm.getNonce` / selector-matched `expectRevert`. A test that passes against a zero-returning contract isn't behavioral.

## Retire components that can't be standalone

If a component needs structured calldata only a composer owns → don't ship Yul stubs returning constants. Retire `externalCall` sites, express as Lean predicates over harness params. Contract theorems become caller-conditional but honest. Document the shift.

## Don't trust success sentinels as real

Yul `{ mstore(0x40, 0); ret := 1 }` = liar, not stub. Returns a success word without doing the named work. Foundry tests asserting success pass trivially.

Two guardrails:
1. Function-aware stub detector in CI, allowlist via `// AUDIT-OK-STUB: <reason>`.
2. Behavioral tests, not dispatch-shape.

Placeholders OK only if (a) `AUDIT-OK-STUB` rationale names the real callee, (b) contract theorems explicitly caller-conditional ("IF deployed helper does X THEN theorem").

## Kill only your own processes

The user runs codex/lean sessions in parallel from other terminals and other repos. `pkill -f 'codex exec'` or `pkill -f 'lean'` blanket-kills theirs too. When killing, target SPECIFIC PIDs you started (track them at launch) — not bare pattern matches. Identify yours by either: (a) cwd/`-C` path matching this repo's worktree, (b) the PID returned at launch, (c) `ps -ax -o ppid,command` and only kill children of your shell. Scope `pkill` patterns to this repo's path (`pkill -9 -f 'lean.*tama-uni-v2.*Bridges'`, not `pkill -9 -f 'lean'`). Note: `pkill -f 'lake build'` does NOT kill the `lean` worker child it spawned — a runaway elaboration survives and starves every later build until killed by its own PID.

## Verify agent commit before trusting report

Subagent reports = narrative, not proof. Run `git status --short` + `git log --oneline` after. If files uncommitted, orchestrator commits with a message recording the agent's scope. Recurring failure mode: agent reports "complete, all gates green" while leaving touched files in the working tree.

## Codex plugin can't commit; direct CLI for execution

Plugin sandbox = `workspace-write`, blocks `.git`. Two shapes:
1. Codex edits, orchestrator commits.
2. Direct CLI — same can't-commit, but faster, more visible, bypasses plugin watchdog:
   ```bash
   codex exec --sandbox workspace-write --skip-git-repo-check \
     --color never -C <repo> --output-last-message <final.txt> \
     < prompt.txt > log 2>&1 &
   ```

## Codex plugin 10-min watchdog hands off async

The codex-rescue subagent has a ~600s watchdog. Beyond it, it returns a "task running in background ID X" handle, work continues async, with NO completion signal. A reported wall ≈ 10-11min is a suspected hand-off. Direct `codex exec` sidesteps this entirely.

## Network failures during long codex sessions are survivable

The WebSocket to the backend disconnects under sustained load — typically after a session exceeds ~1M tokens or ~60 min wall. Log ends `failed to connect to websocket`, no `--output-last-message`, PID exits clean-less. BUT: file edits are intact + the build is usually green at disconnect (codex flushes incrementally).

Recovery: confirm green, commit as `<phase>a` partial, spawn `<phase>b` for the rest. Prompt always includes "after edits, run build, return only when green."

## Phases >500 LOC split preemptively

Heuristic: a phase touching >5 files OR introducing >20 theorems OR reproving >20 → ship as Xa/Xb from the start. Splitting after-the-fact works but is more work.

## Codex factors well via shared predicates when prompted

Without an explicit hint, codex inlines the same conjunct N times across N specs. With a "factor through a shared predicate" prompt, it writes a single helper. Use this every time a phase touches multiple specs that share structure.

## Shell var name `status` is read-only in zsh

zsh's `$status` mirrors `$?` and is read-only. `status=$(jq ...)` fails immediately. Rename to `jstatus` / `cur_status`.

## Manifest re-key part of theorem refactoring

Renaming / deleting an audit-facing Lean theorem → update the matching `verity/spec/*Spec.lean`, `verity/proof/*Proof.lean`, and Foundry `// tama: mirrors=...` / `// tama: discharges=...` tags in the same commit. `tama` coverage catches obligation ↔ discharger ↔ mirror drift.

## Anti-tautology gates must be semantic, not regex

Regex on a literal premise = one rename away from bypass. Codex routinely introduces aliases (a typed abbrev / record-field projection unfold-equal to the forbidden conjunction) that dodge a literal substring match.

Need: a Lean linter unfolding premise definitions vs a literal substring match. Stopgap: enumerate every known alias in the regex (literal premise + typed-binder aliases + record-field projections of the same type) and update per new alias. Semantic version preferred — the next codex turn picks yet another alias to dodge.

## Codex per-phase deferrals must bind to follow-up phases

Codex is honest about deferrals in per-phase reports ("scalar bridge stays as-is", "runtime-witness boundary not fully expanded"). Orchestrators commit each "best effort" + move on. Net: deferrals filed in early phases become critical / high findings at the post-lift review.

Hard rule: any "deferral" / "weakened" / "partial" / "deferred" in a codex report → either (a) a follow-up phase scheduled before the next phase commits, or (b) explicit user-confirmed acceptance with a closing path. Parse `Deviations` + `Known deferred` sections from each codex final message → TaskCreate + commit message. Don't queue the next phase until deferrals are dispositioned.

## Mid-execution review checkpoints

Plan-review runs before any execution; post-lift review runs after the last phase. With many phases between, two reviews bracket execution with no feedback. Codex is stateless across turns; the same drift repeats.

Mitigation: every 3-4 phases, a read-only codex review. Scope: cross-phase consistency, compounding deferrals, bridge axioms drifting from runtime, theorem-shape weaknesses. Signal not edit — produces a list the orchestrator either schedules as follow-ups or explicitly accepts before continuing.

For 8+ phase runs, budget ~ceiling(N/3) mid-stream passes. Cheap vs landing critical findings post-lift.

## Build-green is necessary but not sufficient

Static gates check structural drift; few check theorem shape (and regex anti-tautology is bypassable).

Theorem-shape gates needed:
- No premise unfolds to conclusion (semantic anti-tautology).
- Every audit theorem cites a runtime / circuit observation in its proof body.
- Bridge axioms have `BridgeEq` / `BridgeNonzeroImplies` shape, not free `OpaquePred`.
- Per-property "must-conclude-X" gates (e.g. a per-key delta-verify must mention the post-balance observation).

Without these, "build/audit green + gates" can ship a vacuous proof corpus.

## Live proof graph before audit claims

Do not treat theorem arguments, helper names, imports, or README prose as evidence. Check the conclusion and proof closure: if a spec says observed balances matter, the public theorem must consume a predicate that actually constrains those observed values. Ignored parameters, dead helpers, or imported-but-unused bridge files are audit smoke, not proof.

## No dormant bridge/proof surfaces

Never add AXIOMS.md entries, Trust-block text, README claims, or helper modules for bridge axioms that are not consumed by a public theorem. If a bridge or observed-vs-declared predicate is not wired into the meets-spec chain now, either wire it or keep it out of the audit surface. Before claiming consumption, `rg` each bridge/helper name from docs/AXIOMS into `verity/proof/**`.

## Bridge axioms must be observation-indexed

Do not quantify asset-move bridge conclusions over arbitrary balance maps or arbitrary keys. A nonzero external-call success word may justify only the concrete runtime call, asset key, and pre/post snapshot observations it is tied to. A shape like "success implies this delta for all `preBals postBals key`" is a latent inconsistency/vacuity trap once any nonzero witness is in scope.

## Don't assume contract storage/accounting

Prove contract storage/accounting from the actual `.run` execution; never assume it as a premise. Only external boundaries (ERC20 `balanceOf`/`transfer`, callbacks, and explicitly-approved math axioms like `sqrt`) may be assumed. A spec conditional on an assumed post-state is where tautologies and vacuity creep in.

## Runtime simplification must not outrun spec strength

Do not remove runtime balance checks or other safety gates as "proof simplification" until an equal-or-stronger live theorem path is already wired and reviewed. Exact ERC-20 receipt checks are runtime security properties; removing them before proving the replacement path weakens the audited claim and can make proof work harder, not simpler.

## Delete comment-only proof modules

If a proof file loses all declarations, delete it and update imports/docs. A namespace wrapper with comments is not a proof surface. Empty aggregate files need an explicit allowlist and a CI gate; otherwise stale files hide proof erosion.

## Lean bridge axioms lift alongside Yul ABI

A Yul ABI change (e.g., scalar verifier call → array verifier call) → the Lean bridge MUST lift in the same phase. "Yul lifts, Lean stays as-is to preserve the proof corpus" creates a permanent Lean ↔ Yul gap.

Concrete failure mode: runtime call signature changes; the Lean bridge axiom asserts equality against args the runtime helper now ignores. Accept lemmas in dependent files inherit hypotheses the new runtime never enforces. Soundness gap. Reproof cost is one-time; the gap is permanent until closed.

## Persistent codex sessions via `codex exec resume`

Multi-phase orchestration: don't spawn fresh sessions every phase. Resume.

Storage: `~/.codex/sessions/YYYY/MM/DD/rollout-<ts>-<UUID>.jsonl`. Each turn appends. Header = `session_meta` event with UUID.

```bash
# initial turn
codex exec --sandbox workspace-write --skip-git-repo-check \
  --color never -C <repo> --output-last-message /tmp/turn1.txt \
  < prompt1.txt > log1.txt 2>&1
# capture UUID
UUID=$(grep -m1 '"session_meta"' log1.txt | jq -r '.payload.id')
# resume
codex exec resume "$UUID" --output-last-message /tmp/turn2.txt < prompt2.txt > log2.txt 2>&1
```

Codex keeps prior reasoning, tool-call results, file reads. Phase N+1 prompts go terse instead of 3000-word context rebuilds. Caveats: long sessions hit lossy compaction; network failure may corrupt the session ledger (fallback = fresh session); the plugin variant doesn't share resume — direct CLI only. When NOT to resume: independent review / simplifier / adversarial pass — fresh context preferred.
