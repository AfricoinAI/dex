# UniswapV2PairSpec Simplification Plan

## Goal

Reduce `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean` from **5,365 lines / 360 specs** to roughly **3,000–3,600 lines / 130–170 specs** without weakening any security guarantee. The current spec file is the public contract of formal obligations; the proof file (`verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`, 7,850 lines, 360 theorems) discharges them. All 360 specs are cited by the proof, so this is a coordinated refactor of both files.

`docs/spec-coverage.md` is the authoritative description of what the spec covers and explicitly says: "Public specs should be short security and correctness properties" and "The Lean spec files should be readable without opening the proof files first." The current spec is heavy with stepping-stone reformulations that violate both principles. This plan brings the file in line with its stated design.

## Non-goals

- No change to contract source (`verity/src/`), Foundry tests, or factory spec.
- No change to verified properties: every security claim listed in `docs/spec-coverage.md` "Current Implemented Coverage" must still hold and be cited by name (possibly with a renamed canonical form).
- No new axioms or trust surfaces.
- No churn for its own sake: specs that are genuinely the strongest reader-facing form stay verbatim.

## Coordinated artifacts

Every spec rename or removal touches three artifacts in the **end state**. The plan treats them as a single unit; no phase commit may leave any of them out of sync:

1. `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean` — the `def pair_X` definition AND the surrounding assurance-argument prose (section docstrings, top-of-file overview). At the end of the refactor, the spec file is the sole reader-facing essay describing what is covered and why; there is no companion markdown.
2. `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean` — the matching `theorem X_meets_spec` (private when moved).
3. `tama.toml` — public specs are expected to have an entry under `[coverage.proof_only]` (format `"UniswapV2Pair.pair_X" = "one-line description"`). Current baseline: **338 `UniswapV2Pair.pair_*` rows** against **360 public `pair_*` defs**, i.e. **22 public defs have no row**. These are a pre-existing inconsistency, not introduced by this refactor; Phase 0 records them as the baseline exemption list and does not attempt to close the gap (that is out of scope for simplification). When a spec is deleted or made `private`, its row (if any) is removed. When a spec is renamed, its row is renamed and its description is rewritten. The 22 exempt defs may be deleted/moved/renamed without any `tama.toml` action — they have no row to update.

`docs/spec-coverage.md` is consulted as a reference **only during planning phases 1–6**, where the plan uses its "Current Implemented Coverage" enumeration to identify which specs are public coverage. Phase 7 (Renarrate) does **not** transfer its verbose prose into the spec file. Instead, Phase 7 confirms the spec file's existing top-of-file overview and section docstrings already form a self-contained assurance argument, polishes them as needed for the trimmed structure, and then **deletes `docs/spec-coverage.md`**. After the refactor, the spec file is the single source of truth; the markdown does not return.

Phase 1's inventory adds a column `tama.toml row to remove / rename` so the cleanup is mechanical.

## Constraints derived from docs/spec-coverage.md

All line numbers in this section refer to `docs/spec-coverage.md` as it exists at the Phase 0 snapshot. The file is deleted in Phase 7; the obligations below are the contents of the Phase 1 anchor table after that.

The coverage doc names specific public obligations that **must remain public** (named in the spec file, theorem-anchored in the proof file). The plan treats these as a non-negotiable allowlist:

- ERC20 boundary trace replay coverage (lines 53–58 of spec-coverage.md): `pair_safeTransfer_traces_token_transfer`, `pair_safeTransfer_event_replay_moves_token_balance`, `pair_two_safeTransfer_events_replay_move_distinct_token_balances`.
- Mint/burn/swap arithmetic input coverage (lines 161–177 and 271–295 of spec-coverage.md): `pair_first_mint_uses_balance_increase_as_deposit`, `pair_later_mint_uses_balance_increase_as_deposit`, `pair_burn_uses_pair_lp_balance_and_total_supply`, `pair_burn_leaves_remaining_token_balances`, `pair_swap_uses_final_balances_to_compute_input`, `pair_swap_checks_k_against_final_balances`.
- Finite-path-from-good-state preservation (line 171 of spec-coverage.md): `pair_closed_world_path_preserves_good`, `pair_closed_world_path_preserves_reachability`, and the matching `_path_*` forms for supply, reserves, locked liquidity, and the K direction classifier.
- Donated-surplus exception coverage (lines 320–340 of spec-coverage.md): `pair_closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus`, `pair_closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus`, `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit`, `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction`, `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit`.

For Phase 6, the strongest reader-facing same-supply / no-extraction forms are the `_positive_supply_` ones because they drop the explicit reserve-positive premises that reachability already supplies. The canonical-keep list is anchored on those:

- `pair_closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction`
- `pair_closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction`
- the matching `_no_caller_spot_profit` and `_pool_value_never_decreases` forms when they exist with the same premise shape.

## Counts that drive the plan

Measured by grep on the current file:

- View pairs (`_spec` raw equality + `_run_success_frames_state`): **12 pairs** (24 specs) — `decimals`, `totalSupply`, `balanceOf`, `allowance`, `factory`, `token0`, `token1`, `minimumLiquidity`, `getReserves`, `price0CumulativeLast`, `price1CumulativeLast`, `kLast`.
- `_from_run` lifts: **41**.
- `_run_success` raw forms: **17**.
- `closed_world_*` specs: **158** (of which: `_step_` 5, `_path_*` 70, `reachable_*` 56).
- `reachable_same_supply_*` variants: **8**.
- `no_mint_burn` + qualifier combinations: **11**.
- Total `pair_*` defs: **360**.

## Classification (eight buckets, A–H)

Every spec is placed into one of eight buckets. Buckets A–D stay public; E–H either rename, merge, or move. Bucket H is restricted to specs that are **not** named in `docs/spec-coverage.md` as public obligations.

| Bucket | Treatment | Rough count |
|---|---|---|
| A. Security-essential public obligation: revert frames, exact-guard reverts, ERC20 boundary traces, reentrancy lock + global blocking statement, view `_run_success_frames_state`. | Keep verbatim. | ~50 |
| B. Per-call accounting rules cited by `docs/spec-coverage.md`: first/later mint deposit, burn redemption + reserve cache, swap final-balance/K, skim surplus, sync reserve write, plus the arithmetic-input specs listed in the constraint allowlist above. | Keep verbatim. | ~25 |
| C. Reader-facing reachable-path invariants: `pair_closed_world_reachable_*_path_*` for `good`, `reserves_backed`, `reserves_fit_uint112`, `locked_liquidity_*`, `positive_supply_*`, plus the canonical-keep no-extraction list from the Constraints section. | Keep. Rename only if a current `_positive_supply_` form supersedes a weaker keeper. | ~30 |
| D. Public good-state path preservation forms (`_path_preserves_good`, `_path_preserves_reachability`, `_path_supply_good`, etc.) explicitly listed in `docs/spec-coverage.md` line 171. | Keep verbatim. | ~10 |
| E. View `_spec` (raw equality) strictly subsumed by its paired `_run_success_frames_state` in Bucket A. | Delete from spec; delete `_meets_spec` theorem from proof. | 12 |
| F. `_run_success` raw form + `_matches_closed_world_step` lift + `_matches_closed_world_step_from_run` lift for the same call. Keep ONE canonical `_matches_closed_world_step_from_run` per call; the others become `private theorem` lemmas in the proof. | Spec count drops from ~25 to ~6. | ~25 → ~6 |
| G. `_preserves_X_from_run` cascade per mutating call. For each call, keep only the `_from_run` corollaries explicitly cited as public coverage in `docs/spec-coverage.md` ("Public-call theorems now expose …" paragraphs). The remainder move to proof as `private theorem` with the same name. | Spec count drops from ~70 to ~25. | ~70 → ~25 |
| H. Pure proof scaffolding: specs that are **not** named anywhere in `docs/spec-coverage.md` and are not cited by any other doc; representative candidates only — final list comes from Phase 1 inventory cross-referenced against the doc. Currently includes the `_step_` invariant lemmas (`pair_closed_world_step_preserves_good` etc.) and one-step `non_donation_step_never_increases_surplus`-style classifiers when their reachable/path counterparts already cover the public story. | Move to proof as `private theorem` (or `private def` + `private theorem`) with the same name. | ~15 |

Target spec count: **~140 specs**, target line count: **~3,300 ± 400 lines**.

## Pre-implementation gate

The plan must not move any spec without an explicit subsumption argument. For each spec marked E, F, G, or H, the inventory row records:

1. The canonical Bucket A–D spec name that subsumes it (or, for E, the paired `_run_success_frames_state`).
2. A one-sentence subsumption argument (e.g., "weaker premise: drops `reachable` for `good`, supplied by the kept `_path_*_from_good` form").
3. The doc location (line number in `docs/spec-coverage.md`) that the canonical spec satisfies, if any.

If a Phase 1 row cannot fill all three fields, the spec stays public (gets re-bucketed into A–D). This is the hard guardrail: the plan refuses to drop a spec unless the inventory row proves a strictly stronger or equally strong public spec is keeping the coverage.

## Execution phases

### Phase 0 — Snapshot & baseline (1 commit)

1. Run the full CI pipeline locally and record results:
   - `tama doctor`
   - `tama check`
   - `tama build --locked`
   - `tama test`
   - `tama audit`
   - `lake build TamaUniV2.Proof` (already covered by `tama build`, but logged separately for the line-count delta baseline).
2. Record the current baseline as:
   - `tama.toml` `[coverage.proof_only]` rows for `UniswapV2Pair.pair_*`: **338**.
   - `UniswapV2PairSpec.lean` line count: **5,365**, public def count: **360**.
   - Pre-existing `tama.toml` exemption list: the **22** public defs without a row, computed as `LC_ALL=C` sorted set difference between spec defs and `tama.toml` rows; checked in as `docs/plans/pair-spec-simplification-tama-exemptions.txt`. The file is sorted under `LC_ALL=C` (byte order) so Phase 8 `comm` / `diff` checks are reproducible. This list does not grow during the refactor: every kept spec already on the list stays exempt; every kept spec not on the list keeps its row.
3. Commit this plan to `docs/plans/pair-spec-simplification.md`.
4. No code change in this commit.

### Phase 1 — Inventory (1 commit, doc-only)

Produce `docs/plans/pair-spec-simplification-inventory.md` (machine-friendly table): for each of the 360 `pair_*` defs, one row with the following columns:

1. `name` — spec name.
2. `bucket` — one of A–H.
3. `rationale` — ≤10 words.
4. `subsumed-by` — surviving canonical spec name (Buckets E/F/G/H), or `n/a (canonical)` (Buckets A–D), or `n/a (paired _run_success_frames_state)` (Bucket E).
5. `spec-coverage.md line` — line number anchor in the Phase 0 snapshot of `docs/spec-coverage.md` (the file is deleted in Phase 7; the line number is preserved here for audit), or `n/a`.
6. `tama.toml action` — one of `delete row "UniswapV2Pair.pair_X"`, `rename row to "UniswapV2Pair.pair_Y"`, `keep row`, or `none (exempt — no row in baseline)` for the 22 specs in the Phase 0 exemption list.

Bucket H rows must have a non-empty `subsumed-by`; A–D rows leave it as `n/a (canonical)`.

Phase 1 also produces `docs/plans/pair-spec-simplification-coverage-anchors.md` — a side table mapping every bullet in the Phase 0 snapshot of `docs/spec-coverage.md` "Current Implemented Coverage" to at least one spec that stays in Buckets A–D. The Phase 1 commit checks this file in alongside the inventory so Phase 7 (which deletes `docs/spec-coverage.md`) and Phase 8 (which verifies coverage) can both rely on it. If a bullet has no surviving anchor, the plan is wrong and the corresponding spec is reclassified to A–D before code movement begins.

Phase 1 additionally produces a `tama.toml` cleanup script: a deterministic mapping from each removed/moved spec name to the exact `tama.toml` row that must be deleted, and from each renamed spec to the row that must be renamed (with new description). The script is checked in alongside the inventory so phases 2–6 can run it incrementally.

### Phase 1.5 — Terminology rename: `_refines_closed_world` → `_matches_closed_world_step`

The `refines` verb in identifiers like `pair_X_run_success_refines_closed_world` is jargon-y and reads as meaningless in context. The intent of these specs is: a successful concrete call corresponds to a step in the closed-world (mathematical model) transition relation. Rename to `_matches_closed_world_step` so the name reads literally.

In-scope renames (mechanical, one-pass `sed -i ''` substitution per file):

1. Across `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`, `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`, `verity/spec/TamaUniV2/Spec/UniswapV2FactorySpec.lean`, `verity/proof/TamaUniV2/Proof/UniswapV2FactoryProof.lean`, and `tama.toml`: replace every `_refines_closed_world` substring with `_matches_closed_world_step`. This handles both the bare suffix and the `_refines_closed_world_from_run` lifted suffix.
2. In `verity/proof/TamaUniV2/Proof/UniswapV2FactoryProof.lean`: rename the private lemma `factoryConcreteCreatePath_refines_world_path` to `factoryConcreteCreatePath_matches_world_path` (6 occurrences, file-local).
3. In `docs/spec-coverage.md`: no prose changes needed (the file does not use "refines" as a verb at any line).
4. In `docs/agent-progress.md`: leave alone. It is a dated historical log; the existing entries refer to the old identifier names as the names that were in effect at the time of writing. Future entries will use the new names.
5. In `docs/plans/pair-spec-simplification.md` (this file): already uses the post-rename names in the keep lists; no further plan edits needed.

Expected baseline occurrence counts (used as a precondition check for the rename script):

- `UniswapV2PairSpec.lean`: 19 occurrences of `_refines_closed_world`.
- `UniswapV2PairProof.lean`: 114 occurrences.
- `UniswapV2FactorySpec.lean`: 2 occurrences.
- `UniswapV2FactoryProof.lean`: 18 occurrences (12 `_refines_closed_world` + 6 `_refines_world_path`).
- `tama.toml`: 18 occurrences.

End-of-phase verification: `tama check && tama build --locked && tama test && tama audit` all green; `git diff` for the active files shows only the rename (no semantic edits).

This is a standalone phase because the rename is independent of the simplification: it leaves the set of public specs unchanged, only renaming them. Doing it as its own commit makes the simplification phases that follow read cleanly against the new names.

### Phase 2 — Collapse view `_spec` duplicates (Bucket E, 12 specs)

For each of the 12 views:

1. Delete `pair_view_spec` from the spec file.
2. Delete `theorem view_meets_spec` from the proof file.
3. Delete the matching `"UniswapV2Pair.pair_view_spec" = …` row from `tama.toml` `[coverage.proof_only]`.
4. Keep `pair_view_run_success_frames_state` and its theorem.
5. Update `docs/spec-coverage.md` view bullet (lines 47–53) to cite the surviving form.

End-of-phase verification: `tama check && tama build --locked && tama test && tama audit` all green; `git diff -- tama.lock lakefile.toml lake-manifest.json` empty.

The `_run_success_frames_state` form already establishes `(view).run s = ContractResult.success v s` with `v` the storage cell expression, which strictly implies the deleted equation.

### Phase 3 — Move pure scaffolding (Bucket H)

For each Bucket H spec (final list from Phase 1):

1. Move the `def pair_X` body verbatim into `UniswapV2PairProof.lean` as `private def pair_X` placed just above the theorem that currently uses it. (Keep `def` rather than collapsing into a lemma — preserves the call sites without rewriting them.)
2. Delete the `def pair_X` from the spec file.
3. The theorem `theorem X_meets_spec : pair_X …` in the proof file becomes `private theorem X_meets_spec : pair_X …` with the same body.
4. Delete the matching `"UniswapV2Pair.pair_X" = …` row from `tama.toml` `[coverage.proof_only]` — privatized specs are no longer public coverage obligations.

End-of-phase verification: `tama check && tama build --locked && tama test && tama audit` all green. Per-spec change is mechanical and self-contained.

### Phase 4 — Collapse `_run_success` / `_matches_closed_world_step` cascade (Bucket F, ~25 → ~6)

Per mutating call, identify the canonical "from successful public run" spec. The exact name differs by call because some calls have a distinct `_from_run` suffix and burn does not:

- `mint` (first):   canonical = `pair_mint_first_success_run_matches_closed_world_step_from_run`.
- `mint` (subsequent): canonical = `pair_mint_subsequent_success_run_matches_closed_world_step_from_run`.
- `burn`: canonical = `pair_burn_success_run_matches_closed_world_step` (this form already takes `result` and asserts `result = (burn …).run s ∧ result = success …`, so it is the `_from_run`-shape; no separate `_from_run` exists, and none is added).
- `swap`: canonical = `pair_swap_success_run_matches_closed_world_step_from_run`.
- `skim`: canonical = `pair_skim_success_run_matches_closed_world_step_from_run`.
- `sync`: canonical = `pair_sync_success_run_matches_closed_world_step_from_run`.

For each call:

1. Keep the canonical spec verbatim. Do not rename.
2. Move the corresponding `_expected_matches_closed_world_step` and (where they exist) `_run_success_matches_closed_world_step` non-`_from_run` lifts into the proof file as `private def` + `private theorem` named the same.
3. Delete the matching `tama.toml` rows for each privatized name.
4. Update `docs/spec-coverage.md` if it cites the moved name; otherwise no doc change.

End-of-phase verification: full `tama check && tama build --locked && tama test && tama audit` green.

### Phase 5 — Collapse `_preserves_X_from_run` cascade (Bucket G, ~70 → ~25)

For each mutating call:

1. Read `docs/spec-coverage.md` "Public-call theorems now expose …" paragraphs (lines 161–177 and 271–295) to enumerate which `_from_run` corollaries are public coverage.
2. Keep those verbatim as Bucket B; do not touch them.
3. Move every other `_preserves_X_from_run` for that call into the proof file as `private theorem`, same name.
4. Delete the matching `tama.toml` rows for each privatized name.

Hard rule: if Phase 1 cannot fill the "subsumed-by" cell for a candidate `_from_run`, it stays public.

End-of-phase verification: full `tama check && tama build --locked && tama test && tama audit` green.

### Phase 6 — Consolidate same-supply / no-mint-burn / no-extraction cascade (~30 → ~15)

Keep these canonical reachable-form theorems verbatim. Each is the strongest reader-facing form for its specific shape — there are two valuation modes (cached reserves vs. actual token balances) and three premise shapes (free, balanced-only, zero-surplus-only); the keep list covers each combination.

Spot-value (reserve-valued) anchors. The two `_positive_supply_` forms are the strongest because reachability + positive supply already supplies reserve-positivity, so no redundant `0 < reserve` premises are needed:

- `pair_closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction`
- `pair_closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction`
- `pair_closed_world_reachable_no_mint_burn_path_no_caller_spot_profit`
- `pair_closed_world_reachable_same_supply_path_no_caller_spot_profit`

Premise-rich reader-facing exceptions. These two forms carry explicit `0 < reserve0 / reserve1` premises **and have no `_positive_supply_` counterpart in the current file**. They are kept as the strongest existing public reader form for their specific valuation; the Phase 6 keep-list otherwise prefers the `_positive_supply_` shape:

- `pair_closed_world_reachable_same_supply_path_pool_value_never_decreases`
- `pair_closed_world_reachable_same_supply_path_no_token1_denominated_profit`

Same-LP-supply actual-token-balance anchors (donated-surplus exception coverage, spec-coverage.md lines 320–340). The pool-value, surplus-bounded, and caller-no-profit forms are all kept so the same-supply story is symmetric across pool-value and caller-value framings:

- `pair_closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus`
- `pair_closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus`
- `pair_closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction`
- `pair_closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit`

No-mint-no-burn actual-token-balance anchors (same coverage paragraph, common operational shape). Both the pool-value and caller-no-profit forms are kept for the same symmetry reason:

- `pair_closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus`
- `pair_closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus`
- `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction`
- `pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit`
- `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction`
- `pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit`

Balanced-start actual-token-balance anchors (the common operational form when a router enters a clean pool, spec-coverage.md lines 320–325):

- `pair_closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction`
- `pair_closed_world_reachable_balanced_no_mint_burn_path_no_token_balance_value_extraction`

Move the older `reachable_same_supply_path_no_spot_value_extraction` (with explicit reserve-positive premises) and the older `reachable_no_mint_burn_path_no_spot_value_extraction` into the proof file as private corollaries of the kept `_positive_supply_` forms. Do **not** blanket-move other `balanced_…` or premise-qualified variants: the Phase 1 inventory must name an equally strong surviving public anchor before any such spec can be reclassified, per the Pre-implementation gate.

For each moved spec, delete the corresponding `tama.toml` row. For each kept spec that is renamed, rename its row and rewrite its one-line description.

End-of-phase verification: full `tama check && tama build --locked && tama test && tama audit` green.

### Phase 7 — Renarrate spec and delete the external coverage doc (1 commit, prose-heavy)

The spec file's existing top-of-file overview and section docstrings already form an assurance argument — that structure is preserved, not replaced. This phase polishes them against the trimmed spec content and then deletes the now-redundant external doc.

1. Walk each section in `UniswapV2PairSpec.lean`. For each section, trim the docstring to fit the now-shorter `def` list (5–15 specs per section is the target), make sure each `def` corresponds to a sentence in the preceding prose, and remove any docstring sentences whose underlying specs were moved to Buckets E–H.
2. Update the top-of-file overview to reflect the trimmed assurance argument flow.
3. Confirm the spec file is self-contained: a reader can understand which security and correctness properties are covered by reading the spec file alone, without `docs/spec-coverage.md`.
4. Delete `docs/spec-coverage.md`. Do not transcribe its prose into the spec file — the spec's own docstrings are the SSoT; `docs/spec-coverage.md` was a more verbose secondary description and is not retained in any form.
5. Run a final `grep -rln "spec-coverage.md" .` and remove any remaining repo references to the deleted file (CLAUDE.md, READMEs, plan doc cross-references — except this plan, which can keep historical references since it is itself transient).

End-of-phase verification: `tama check && tama build --locked && tama test && tama audit` all green. No occurrence of `docs/spec-coverage.md` outside this plan doc.

### Phase 8 — Verify

Full CI parity from a clean cache:

1. `tama doctor` (no fixups required after the refactor).
2. `git diff --exit-code -- tama.lock lakefile.toml lake-manifest.json` — the refactor must not touch dependency state.
3. `tama check`.
4. `tama build --locked` (proof + spec + src).
5. `tama test` (Foundry mirror suite plus any Lean tests).
6. `tama audit` (no new issues; existing axioms list unchanged).
7. Every security/correctness obligation present in the Phase 0 baseline `docs/spec-coverage.md` "Current Implemented Coverage" enumeration still maps to at least one named non-`private` `def pair_X` in `UniswapV2PairSpec.lean` — verified by the Phase 1 anchor table `docs/plans/pair-spec-simplification-coverage-anchors.md` (the table is checked in as part of the plan inventory and survives the deletion of the source doc).
8. Forward cross-check: every surviving `tama.toml` `[coverage.proof_only]` row resolves to a `def pair_X` that exists in `UniswapV2PairSpec.lean` and is non-`private`. No orphan rows.
9. Reverse cross-check: every surviving non-`private` `def pair_X` in `UniswapV2PairSpec.lean` either has a `tama.toml` row or appears in `docs/plans/pair-spec-simplification-tama-exemptions.txt` (the baseline 22-spec exemption list). No new public specs lacking rows beyond the baseline.
10. `docs/spec-coverage.md` is no longer present in the tree; `git log` shows its deletion was the Phase 7 commit.
11. `git log` shows each phase as a separate commit so any single phase can be reverted.
12. The diff for `verity/src/` and `test/verity/` is empty.

## Commit strategy

One commit per phase. Each commit message lists the buckets touched and the spec/proof line delta. No squashing — the per-phase history is the audit trail. If any phase exceeds 800 lines of net spec deletion, split it.

## Risk & mitigation

- **Risk**: a "moved-to-proof" spec turns out to be cited by `docs/agent-progress.md` or elsewhere. Mitigation: `grep -rn` for each name across `docs/` and `test/` before moving, in Phase 1.
- **Risk**: a security bullet in `docs/spec-coverage.md` loses its named anchor. Mitigation: Phase 1 side table proves a 1:N mapping from doc bullets to surviving specs before code movement; if any bullet has no anchor, the candidate spec is reclassified.
- **Risk**: collapsing Bucket G corollaries forces the proof file to re-derive them at every call site (multiplying proof length, not reducing it). Mitigation: corollaries that are cited from multiple proof theorems remain as `private theorem` in the proof file — the work doesn't disappear, it just stops being a public obligation. Spec-file simplification, not proof-file simplification, is the only stated goal.
- **Risk**: the build breaks mid-phase. Mitigation: each spec move is a single self-contained edit; the full `tama check && tama build --locked && tama test && tama audit` pipeline runs at the end of every phase; the per-phase commit boundary is the rollback point.
- **Risk**: `tama.toml` falls out of sync with the spec file (orphan rows pointing at deleted defs, or surviving defs without rows). Mitigation: Phase 8 step 8 cross-checks every `[coverage.proof_only]` row against `def pair_X` in the spec file. The Phase 1 cleanup script is the single source of truth for which row corresponds to which move.
- **Risk**: collapsing two specs with subtly different premises (e.g., `good` vs `reachable`, with or without `_positive_supply_`) silently weakens a public guarantee. Mitigation: the Pre-implementation gate makes every removal carry an explicit subsumption argument naming the surviving canonical spec; if the argument requires a strictly stronger premise to be added to the canonical spec, the move is rejected and the spec stays.

## Exit criterion

- Spec file ≤ 3,600 lines, ≤ 170 `def pair_*`.
- Proof file builds clean.
- `UniswapV2PairSpec.lean` is self-sufficient as the SSoT: its top-of-file overview and section docstrings form a complete assurance argument; no external coverage markdown is needed.
- `docs/spec-coverage.md` is deleted from the tree. No repo file outside this plan references it.
- The Phase 1 anchor table `docs/plans/pair-spec-simplification-coverage-anchors.md` shows every Phase-0-snapshot security/correctness obligation maps to a surviving named non-`private` `def pair_X`.
- Phase 1 inventory file is checked in; auditors can replay the subsumption argument for every removed spec.
