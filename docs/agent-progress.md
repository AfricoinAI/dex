# Agent Progress Notes

This file is a handoff checkpoint for long proof work. Update it before large
edits, after verification results, and whenever a proof attempt changes
direction so context compaction does not cause repeated work.

## Current Objective

Bring the Uniswap V2 Pair and Factory specs/proofs to Certora-style coverage,
using Tamago ERC4626 as the reference pattern: concrete entrypoint run
postconditions plus closed-world economic invariants connected by explicit
postconditions/traces. Avoid new axioms or trust surfaces unless they are true
external boundaries.

## Lessons From Failed Pair Bridge Repair

- Do not treat a cleaner public theorem shape as proof-strengthening. The
  failed bridge repair removed the old tautological post-state conjunct from the
  conclusion, but kept the whole concrete post-world equality inside
  `pair*TokensBehaveNormallyForCall`. The proof still rewrote the actual
  endpoint with that premise and then applied the same ghost-world step lemma.
- Always unfold boundary predicates component-by-component before accepting
  their names. `pairTokensBehaveNormallyForCall` sounded like an external ERC20
  assumption, but it also assumed pair-owned storage writes: reserves,
  `totalSupply`, and locked-liquidity interpretation.
- Keep ERC20 behavior and pair storage correctness separate. It is reasonable
  to assume honest external token balance/transfer semantics. It is not
  reasonable to assume the pair's own reserve/supply/lock storage updates when
  the purpose of the bridge is to prove them from the actual pair call.
- Dead concrete lemmas are a red flag. `skim_success_run_preserves_world` and
  `sync_success_run_reaches_world` were proven but unused, which should have
  blocked any claim that the public skim/sync bridges were actual-execution
  bridges.
- The no-free-lunch headline must not consume a caller-supplied
  `PairWalletStep` as the decisive evidence of execution. Either construct the
  wallet step from the actual successful call plus explicit external-token
  assumptions, or state honestly that the theorem is over model histories
  already equipped with wallet-step evidence.
- Regression guardrail for future bridge work: a public bridge proof should not
  solve the actual endpoint by destructing a premise of the form
  `pairWorldFromConcreteAndTokens ... result.snd = expected` and then rewriting
  with it. If that pattern appears, the storage half of the bridge is still
  assumed, not proven.

## Active Pair Bridge Repair Gate 2026-05-22

- Task 0 helper check confirmed the old source helper names are absent from the
  current `verity/` tree:
  `finishMintNoElapsed`, `finishBurnNoElapsed`, `finishSwapNoElapsed`,
  `burnNoElapsedPath`, `swapNoElapsedPath`, and `completeBurnNoElapsed`.
- Task 1/2/3 vertical-slice work started: the old whole-world
  `pair*TokensBehaveNormallyForCall` predicates were split into field-level
  token-balance predicates plus separate pair-storage matching predicates, and
  the existing `skim_success_run_preserves_world` /
  `sync_success_run_reaches_world` lemmas were wired into storage extraction
  lemmas.
- The first no-source direct storage proof attempted was first mint:
  `mint_first_success_run_storage_matches_world`, over the current public
  `(mint toAddr).run s`, using the same public guard facts already required by
  `pair_first_mint_success_reaches_expected_pair_state`.
- Result: focused `lake build TamaUniV2.Proof.UniswapV2PairProof` ran for more
  than two minutes inside that direct first-mint reduction with no diagnostics
  and had to be killed. This repeats the previously recorded failure mode: full
  public `mint` reduction expands through the Tamago sqrt / LP-mint / oracle
  suffix and produces kernel-sized work.
- Do not continue by adding a whole-world post-state premise, a hidden storage
  assumption, `sorry`, `axiom`, or a renamed `TokensBehaveNormallyForCall`.
  The next step is the explicit source-refactor decision gate from the plan:
  either introduce bounded internal helper paths and accept the generated-code
  verification burden, or stop with the bridges honestly marked incomplete.
- User approved source edits. Added clean internal helper factoring in
  `verity/src/TamaUniV2/UniswapV2Pair.lean`:
  `updateReservesAndEmitSync`, `finishFirstMint`, `finishLaterMint`,
  `firstMintPath`, and `laterMintPath`. The public `mint` body now performs the
  entry guards and dispatches to the first/later mint helper path. The final
  `UniswapV2Pair.spec` filters these helper selectors out of the exposed
  function list while retaining generated internal helper specs.
- Verified after that source refactor:
  `lake build TamaUniV2.UniswapV2Pair TamaUniV2.Spec.UniswapV2PairSpec` passes.
- The existing proof script for `mint_first_success_run_storage_matches_world`
  still unfolds too much of the public mint run and stalls in
  `lake build TamaUniV2.Proof.UniswapV2PairProof`. Next proof attempt should
  not use the monolithic `simp [mint, UniswapV2PairBase.mint, ...]` body.
  Instead, prove small success-state postconditions for `finishFirstMint` and
  `firstMintPath` first, then adapt the public `mint` prefix to the helper run.
- Source factoring was extended one level further for first mint: the
  recipient LP-balance overflow check now happens before writes in
  `finishFirstMintChecked`, and the deterministic storage/log/update suffix is
  isolated in `finishFirstMint`. The source/spec build still passes after this
  refactor.
- Focused proof snippets can prove the deterministic `finishFirstMint` suffix
  storage postcondition and the success-gated `finishFirstMintChecked`
  postcondition without introducing storage assumptions.
- Hard blocker for completing the zero-assumption first-mint public bridge:
  adapting the public `mint`/`firstMintPath` run to the checked suffix requires
  crossing `Tamago.Utils.FixedPointMathLibBase.sqrt`. A standalone frame lemma
  with statement
  `((Tamago.Utils.FixedPointMathLibBase.sqrt x).run s).snd = s` was tested and
  immediately expanded the full Tamago sqrt body, producing a kernel
  deep-recursion failure. The Tamago proof package has private sqrt run lemmas,
  but no exported frame lemma usable here. Without such a public lemma (or an
  accepted source-level replacement for the sqrt call), the first-mint storage
  bridge cannot be completed with zero pair-storage assumptions.
- User accepted making the Tamago sqrt execution fact an explicit assumption.
  Added the narrow local axiom in `UniswapV2PairProof.lean`:
  `(Tamago.Utils.FixedPointMathLibBase.sqrt x).run s =
  ContractResult.success (sqrtValue x s) s`. This trusts only that the verified
  Tamago math helper returns normally and frames `ContractState`; it does not
  assume any Uniswap pair storage writes.
- After adding the sqrt axiom, the old monolithic public first-mint storage
  proof still stalls. Focused snippets show the next proof should be a
  success-gated `firstMintPath`/public-prefix adapter; a non-success-gated
  `firstMintPath` storage statement leaves revert branches open and is the wrong
  target.

## Completed In Current Worktree

- Corrected `PairWorldMintStep` so mint models already-donated token balances:
  `before.balance = before.reserve + amount`, mint then updates reserves to the
  observed balances.
- Added concrete first-mint helpers in
  `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`.
- Proved `pair_mint_first_expected_refines_closed_world`.
- Verified `lake build TamaUniV2.Proof.UniswapV2PairProof` passed after that
  expected-state bridge, before the later actual-run mint proof attempt.
- Added durable seven-gap plan:
  `docs/superpowers/plans/2026-05-16-uniswap-v2-certora-level-spec-coverage.md`.
- Added Pair event helper constructors in
  `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`.
- Added and proved LP event obligations:
  `pair_approve_emits_approval`, `pair_transfer_emits_transfer`, and
  `pair_transferFrom_emits_transfer`.
- Verified `lake build TamaUniV2.Proof.UniswapV2PairProof` passes after the LP
  event obligations.
- Attempted a broad actual-run `sync` success proof. Do not repeat it as one
  monolithic simp: the TWAP branches expand to a large residual goal and expose
  an internal ERC20 read stub name that is not stable to reference directly.
  Next attempt should factor a helper lemma that rewrites the balance-read guard
  from `observedBalance0/1` before unfolding the whole sync body.
- Added and proved `pair_skim_run_success_transfers_excess_and_restores_unlocked`:
  actual successful `skim` transfers exact token0/token1 surplus via pair-local
  token-transfer traces, leaves reserves unchanged, and restores `unlocked = 1`.
- Verified after skim success proof: `lake build`, `tama check`, `tama build`,
  `tama test`, and `tama audit` all passed.
- Refactored factory CREATE2 through executable helper `pairCreate2Word` with a
  compilation model that still lowers to the existing CREATE2 ECM. This makes
  nonzero factory success runs modelable without adding a new trust surface.
- Added factory concrete helpers in
  `verity/common/TamaUniV2/Common/UniswapV2FactoryConcrete.lean`.
- Added and proved `factory_createPair_success_updates_storage_and_emits`:
  actual successful `createPair` sorts tokens, consumes the nonzero CREATE2
  result boundary, writes both pair mappings, appends to `allPairs`, increments
  length, and emits `PairCreated`.
- Added and proved exact ordered factory reverts:
  `factory_createPair_run_revert_create2_failed` and
  `factory_createPair_run_revert_pair_count_overflow`.
- Verified focused factory proof:
  `lake build TamaUniV2.Proof.UniswapV2FactoryProof`.
- Proved executable `sync` no-elapsed success coverage in
  `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`:
  success, reserve0/reserve1 update to observed balances, timestamp update,
  price cumulative preservation, `unlocked = 1` restoration, and `Sync` event
  emission. The proof route uses `syncNoElapsedPath_props` plus the
  result-indexed wrapper `syncNoElapsedPostOf`.
- Verified after the sync no-elapsed proof:
  `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- Added internal no-elapsed finish helpers in
  `verity/src/TamaUniV2/UniswapV2Pair.lean` for guarded success paths:
  `finishMintNoElapsed`, `finishBurnNoElapsed`, and `finishSwapNoElapsed`.
  These are excluded from the public ABI alongside other internal helper
  functions and preserve the same no-elapsed reserve/event effects while giving
  proofs smaller suffixes to target.
- Verified after adding those helper functions:
  `lake build TamaUniV2.UniswapV2Pair TamaUniV2.Spec.UniswapV2PairSpec` and
  `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- Added and proved the small executable suffix specs for
  `finishMintNoElapsed`, `finishBurnNoElapsed`, and `finishSwapNoElapsed`.
  These prove reserve/timestamp writes, cumulative preservation, `unlocked = 1`
  restoration, `Sync` emission, and the corresponding `Mint`/`Burn`/`Swap`
  event emission without unfolding the whole public entrypoint.
- Verified after the suffix specs:
  `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- Added Tamago-style pair-token ghost balance reconstruction from pair-local
  transfer trace events and exact revert-frame specs for `mint`, `burn`, `swap`,
  `skim`, and `sync`. These prove that if a run reverts with the original state,
  no durable pair-token transfer trace can change the ghost token world.
- Verified after revert-frame trace specs:
  `lake build TamaUniV2.Proof.UniswapV2PairProof`.

## Current WIP

- 2026-05-16 PDT: resumed after compaction with the user-requested Task 7 in
  scope: add closed-world K monotonicity/liquidity-ratio specs and a same-LP-
  supply spot-value no-profit spec. Do not restart the older burn adapter or
  aggregate swap success routes. Immediate target is the existing
  `pair_closed_world_same_supply_path_no_spot_profit` proof plus any stale
  public swap adapter residue left after the source refactor.
- 2026-05-16 16:08 PDT: continuing invariant-first execution after compaction.
  Do not restart earlier proof work. Tasks 1-5 of
  `docs/superpowers/plans/2026-05-17-invariant-first-uniswap-v2-specs.md` are
  implemented and focused Pair proof builds passed. Current Task 6 issue:
  `tama build` reaches manifest adaptation and needs `coverage.proof_only`
  reasons for formal-only obligations (closed-world invariants, concrete-state
  projections, revert-frame token-world preservation, and internal helper/path
  adapters). This is metadata, not a new trust surface.
- 2026-05-16 16:13 PDT: manifest wiring is clean. `tama build` now reaches
  solc and fails because generated Yul reuses Verity's temporary `__ite_cond`
  for nested `if/else` shapes in Pair. Source repair in progress: replace the
  timestamp wrap branch in `updateReserves` with arithmetic modulo elapsed time
  and factor mint's post-liquidity timestamp branch into
  `finishMintAfterLiquidity`, preserving behavior while avoiding nested
  generated `if/else` temporaries.
- 2026-05-16 16:22 PDT: threading `Bytes data` through swap helpers was tried
  and rejected by Verity helper lowering, confirming the old note. Current
  source route keeps dynamic calldata use in the public `swap` function, adds a
  static `swapOutputPath` helper for output transfers, and lets public `swap`
  perform the flash callback once before the final no-elapsed/elapsed reserve
  update branch. This preserves callback parity and avoids helper-local
  `data_length` Yul references.
- 2026-05-16 16:30 PDT: user requested two additional invariant specs: swaps
  never decrease K and mint/burn modify liquidity only at correct ratios; any
  same-LP-supply call sequence should not yield caller profit at the initial
  spot price. Added Task 7 to the invariant-first plan before Lean edits. The
  current focused Pair proof failure is from the earlier swap source refactor
  invalidating old helper-to-public adapters; do not confuse it with Task 7.
- 2026-05-16 16:43 PDT: added the Task 7 closed-world vocabulary/specs/proofs
  and removed the stale aggregate public no-elapsed swap-success obligation.
  Rationale: public `swap` now keeps the flash callback in the ABI entrypoint
  for correct bytecode parity, so the old helper-to-public adapter no longer
  describes the source shape. Keep the smaller internal swap suffix/path facts
  plus the new K/no-profit invariants.
- 2026-05-16 14:27 PDT: restarting from notes after compaction. The mistake to
  avoid is trusting transient context over this file; the active route is the
  public burn no-elapsed adapter, built only from the verified
  `completeBurnNoElapsed` suffix theorem plus a narrow public-prefix rewrite.
- 2026-05-16 14:36 PDT: the public burn adapter route was attempted before
  this note was fully updated. That was a process error. Current build status:
  `lake build TamaUniV2.Proof.UniswapV2PairProof` fails in the new burn adapter.
  The failure reduces the public prefix close to the helper call, but the public
  entrypoint wraps inner helper reverts back to the original state while the
  helper theorem describes the locked helper state. A direct equality between
  `(burn toAddr).run s` and the helper run is therefore the wrong shape. The
  latest attempt also hit kernel recursion around the adapter, so do not keep
  adding simp facts to that theorem.
- Next correction before more proof work: either revert the unstable public
  adapter edits or replace them with a smaller helper-wrapper lemma that proves
  only the success case after pattern matching the helper result. Do this after
  restoring a passing focused build, then update this file again.
- 2026-05-16 14:41 PDT: removed the unstable public burn adapter proof block
  while preserving the verified `completeBurnNoElapsed` suffix theorem and the
  public spec definition. Verified the stable point with
  `lake build TamaUniV2.Proof.UniswapV2PairProof`, which now passes again. The
  public burn success spec remains undischarged.
- Next burn route should be source-factored, not proof-stuffed: add a narrow
  internal no-elapsed burn path helper so the public entrypoint reduces to
  `match helper.run lockedState with success => success ... | revert => revert
  ...`, then prove helper success and use a small public wrapper theorem. Do not
  reintroduce the removed monolithic `burn_no_elapsed_properties_after_run`.
- 2026-05-16 14:43 PDT: added internal source helper `burnNoElapsedPath`
  containing the guarded no-elapsed burn prefix plus `completeBurnNoElapsed`.
  Public `burn` now branches to this helper immediately after taking the lock
  when `timestamp32 == previousTimestamp`; elapsed burn keeps the previous inline
  logic. Verified with
  `lake build TamaUniV2.UniswapV2Pair TamaUniV2.Spec.UniswapV2PairSpec`.
- Next proof step: add/prove a helper-level executable spec for
  `burnNoElapsedPath`. Only after that should the public `burn` wrapper theorem
  be reintroduced.
- 2026-05-16 14:48 PDT: added and proved
  `pair_burnNoElapsedPath_run_success_transfers_pro_rata_and_restores_unlocked`.
  The proof case-splits the base `completeBurnNoElapsed` result directly, then
  uses the existing suffix theorem in the success branch. Verified with
  `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- Next proof step: reintroduce the public no-elapsed burn theorem as a small
  wrapper over `burnNoElapsedPath`, reducing only the lock/timestamp branch and
  using the helper theorem for the successful helper result.
- 2026-05-16 14:52 PDT: reintroduced and proved
  `pair_burn_run_success_no_elapsed_transfers_pro_rata_and_restores_unlocked`.
  The public proof now only reduces the lock/timestamp branch to
  `burnNoElapsedPath` on the locked state, case-splits the helper result to
  reconcile wrapper rollback states, and projects the helper theorem. Verified
  with `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- 2026-05-16 14:53 PDT: `/Users/zefram/.tama/bin/tama audit` passes after the
  burn work: structure, selectors, storage layout, coverage, and trust-boundary
  checks all report ok. This does not close the remaining Certora-level coverage
  gaps; it only confirms the current public obligations are wired cleanly.
- 2026-05-16 14:55 PDT: added source helper `swapNoElapsedPath` for the
  no-elapsed swap path and refactored public `swap` to branch to it after
  reading the timestamp and taking the lock. The helper omits the public `data`
  parameter because the current callback ECM does not consume it and Verity
  helper lowering rejects that `Bytes` helper parameter. Verified source/spec
  with `lake build TamaUniV2.UniswapV2Pair TamaUniV2.Spec.UniswapV2PairSpec`.
- Next likely repair: existing swap revert proofs may need a small timestamp
  prefix reduction because public `swap` now reads timestamp before the output
  and liquidity guards.
- Current route: build the public no-elapsed success adapters on top of the
  proved suffix helpers and narrow prefix facts. Do not unfold whole
  `mint`/`burn`/`swap` bodies unless the prefix has first been reduced to the
  helper call.
- Immediate next route: add successful `burn` and `swap` trace-world specs over
  pair-local transfer events before attempting larger arithmetic success
  adapters.
- A direct public `burn` no-elapsed success proof was attempted and failed for a
  useful reason: the no-elapsed timestamp guard was after transfer/memory state
  rewrites, so the simplifier could not use the pre-call timestamp equality and
  expanded the elapsed/TWAP branch. Do not retry that direct proof shape. Refactor
  the source so the no-elapsed branch is selected before those rewrites, then
  target the bounded helper path.
- Burn source refactor status: added `completeBurnNoElapsed`, moved burn's
  timestamp/previous-timestamp read before the lock write, and verified
  `lake build TamaUniV2.UniswapV2Pair` passes.
- A second direct public burn proof still exceeded kernel recursion limits even
  after exact guard-shape hypotheses. Do not retry it. The next burn route must
  prove `completeBurnNoElapsed` as its own small executable postcondition and
  then connect `burn` to that helper with a thin adapter.
- Added and proved `pair_completeBurnNoElapsed_run_success_suffix`, including
  LP burn `Transfer`, token0/token1 safe-transfer traces, reserve/timestamp
  writes, cumulative preservation, `unlocked = 1`, and `Sync`/`Burn` events.
- Verified after the helper theorem:
  `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- Added `pair_mint_first_success_run_refines_closed_world`, a
  success-conditional bridge over the actual `(mint toAddr).run s`. It proves
  that a successful first-mint run returning the expected liquidity refines the
  closed-world mint step.
- Verified `lake build TamaUniV2.Proof.UniswapV2PairProof` passes with this
  bridge.
- A stronger direct proof of actual first-mint success was attempted and should
  not be repeated naively. Expanding the full eventful `mint` run after the
  Tamago sqrt bind causes deep simplifier recursion/stack pressure, even after
  reducing the postcondition to success plus the closed-world step.
- Also attempted ordered swap reverts for insufficient liquidity and invalid
  `to` with direct branch-case `simp`. That still elaborated too heavily.
  Retry by first adding small result-parameter adapter specs or private lemmas
  that normalize only the prefix through the target guard, then expose the exact
  run-result theorem through the public Tama marker.
- A fresh direct first-mint success scratch attempt was made after adding the
  no-elapsed finish helpers. It repeated the known bad pattern: full expansion
  of `mint` still exposes the sqrt bind and LP mint branch as a huge goal.
  Do not repeat `scratch/MintScratch.lean` or any theorem that unfolds all of
  `mint` directly. The correct route is bounded helper lemmas first.

## Proof Discipline Guardrail

- Before starting a new proof route, check this file for forbidden attempts.
- After a proof route succeeds or fails, update this file immediately before
  moving to the next route.
- Scratch files are temporary only. Do not leave scratch files in the worktree
  after a route is either ported or abandoned.
- For mint/burn/swap, do not start from a public full-body success theorem.
  Start from internal suffix helpers or narrow prefix guards, verify each helper
  with focused `lake` commands, then expose public specs through small adapters.

## Next Move

Next optimal proof work:

1. Clean abandoned scratch files.
2. Use those helper facts as the suffix layer for mint/burn/swap success rather
   than unfolding each whole entrypoint.

## Tamago Best-Practice Additions To The Plan

- Keep concrete helper formulas, ghost state, and trace interpreters in
  `verity/common`; public `verity/spec` definitions should be actual
  obligations, not scaffolding.
- Prove small executable postconditions over actual runs before leaning on the
  closed-world model. For Pair, this means first-mint and subsequent-mint run
  facts before using `PairWorldMintStep`, then burn/swap/skim/sync run facts
  before their corresponding ghost transitions.
- Model external token movement with trace events emitted after successful ECM
  calls, following Tamago's asset-transfer trace style. Pair specs should check
  token0/token1 address, from, to, and amount for mint/burn/swap/skim paths.
- Add revert-frame specs that consume the actual reverted run state and prove no
  durable token-transfer trace or storage change survives a revert.
- Add adversarial sequence specs after one-step postconditions are in place:
  donation before mint, donation plus skim/sync, flash-swap callback then repay,
  and round trips that should not create value beyond explicit donations.
- Reuse Tamago FixedPointMathLib sqrt specs/proofs for first-mint reasoning;
  do not add new sqrt assumptions or duplicate the library proof.

## Current Seven-Gap Status

1. Executable mint success: still the highest-priority open proof slice.
2. Executable swap success: open.
3. Executable burn success: no-elapsed public burn success bridge is proved.
   Remaining burn work is elapsed-path coverage and any stronger event/trace
   variants that are not implied by the no-elapsed bridge.
4. Factory createPair success: executable storage/event success and CREATE2/
   length-overflow ordered reverts are proved; explicit initialize-call trace
   remains optional final-hardening coverage.
5. Reentrancy success restoration: `skim` success restoration is proved; `sync`
   no-elapsed success restoration is proved. Mint, burn, swap, and elapsed sync
   restoration remain open.
6. Events/traces: LP ERC20 approve/transfer/transferFrom event obligations are
   proved. Skim token-transfer trace coverage is proved. `sync` no-elapsed
   `Sync` event coverage is proved. Revert-frame token-world preservation is
   proved for mint/burn/swap/skim/sync. Pair mint/burn/swap event obligations,
   elapsed sync event coverage, and burn/swap successful token-transfer trace
   coverage remain open.
7. Ordered reverts: existing exact guard reverts remain; exact reverted runs now
   also have token-world preservation. The full ordered pair matrix is still
   open.

## Active Checkpoint 2026-05-16

- Resume point: the current task-list item is closing remaining executable
  mint/swap bridges plus event/reentrancy obligations, not restarting notes or
  burn work.
- `burnNoElapsedPath` and the public no-elapsed `burn` adapter are already
  proved. Do not rework or replace that route unless a later verification
  failure directly implicates it.
- `swapNoElapsedPath` has been added to source and source/spec compilation
  passed. The immediate regression is the existing exact insufficient-output
  swap revert proof, which now needs a timestamp-branch normalization fix.
- Next proof route: restore `lake build TamaUniV2.Proof.UniswapV2PairProof`,
  then add the executable swap no-elapsed success bridge.
- The first timestamp-normalization attempt still caused kernel deep recursion
  when the public revert proof unfolded the whole no-elapsed swap helper. The
  active fix is to add a small private helper for the `0,0` output guard and
  have the public theorem reduce only the prefix.
- The better route is to keep the official `INSUFFICIENT_OUTPUT_AMOUNT` guard
  in the public `swap` prefix after the lock is set. That preserves ordered
  public revert behavior, avoids proving the first guard through the helper
  branch, and leaves the helper's own guard available for direct helper specs.
- After the public-prefix guard change, the proof is shallow but the generated
  public `swap` term still exceeds Lean's default kernel recursion depth. Follow
  the existing Tamago proof-file pattern and raise `maxRecDepth`; this is a
  proof-environment setting, not a new assumption.
- Raising recursion depth did not fully fix the public proof because the
  continuation after the output guard still contains the complete elapsed swap
  body. Next source refactor: move the elapsed branch into `swapElapsedPath`,
  leaving public `swap` as lock + timestamp + output guard + branch dispatch.
- Done: `swapElapsedPath` now owns the elapsed swap body and is excluded from
  the public ABI; public `swap` keeps the ordered lock and insufficient-output
  gates before dispatch. `lake build TamaUniV2.Proof.UniswapV2PairProof` passes
  again. Continue with the executable no-elapsed swap success bridge.
- Starting executable swap success bridge. Route: add concrete fee-adjusted K
  helper formulas in `verity/common`, add a no-elapsed helper success spec over
  the actual `swapNoElapsedPath` run, prove that helper first, then adapt public
  `swap` no-elapsed through the same locked-state wrapper pattern as burn.
- Direct proof attempt showed the mutable `amount0In`/`amount1In` assignments
  lower into multiple branches that obscure the final expressions. Refactor both
  swap helpers to compute amount-in values with direct `if` expressions matching
  the concrete spec helpers before retrying the proof.
- Direct `if` expressions are not supported in `verity_contract` bodies. Revised
  route: add an internal `computeSwapAmountIn` helper using supported mutable
  syntax, prove its exact run once, and call it from both swap helpers so the
  main swap proof can rewrite a helper call instead of expanding branchy mutable
  assignment twice.
- 2026-05-16 continuation checkpoint: source/spec build passed after adding
  `computeSwapAmountIn` and concrete adjusted-K helpers. The focused pair proof
  is currently in the helper-level `swapNoElapsedPath` success theorem; the
  known failure is local simplification of raw balance-bound guards, not a
  reason to revisit burn, suffix helpers, or public swap guard ordering.
- Follow-up checkpoint: the first direct `swapNoElapsedPath` proof still hit
  kernel recursion because it unfolded transfer branches, K arithmetic, and the
  final reserve/event suffix all at once. Source has now been factored with
  `completeSwapNoElapsed`, and
  `lake build TamaUniV2.UniswapV2Pair TamaUniV2.Spec.UniswapV2PairSpec` passes.
  Next proof route is a suffix theorem for `completeSwapNoElapsed`, then a
  wrapper theorem for `swapNoElapsedPath`.
- Current proof checkpoint: `completeSwapNoElapsed` suffix proof has the right
  guard facts and reuses `finishSwapNoElapsed`; remaining build failures are
  proof-term size in that suffix plus the still-direct `swapNoElapsedPath`
  wrapper. Do not add new assumptions; finish by making the path wrapper call
  the suffix theorem instead of unfolding K arithmetic in every output branch.
- 2026-05-16 later checkpoint: `checkSwapNoElapsed` now owns the input,
  overflow, adjusted-product, required-product, K, and uint112 gates for the
  no-elapsed swap suffix. Source/spec build passes after this factoring. Next
  proof step is to prove the `checkSwapNoElapsed` run once, then have
  `completeSwapNoElapsed` and `swapNoElapsedPath` reuse that proof rather than
  unfolding all K arithmetic.
- Proof route update: `checkSwapNoElapsed` and `completeSwapNoElapsed` are now
  proved in the focused build. The remaining `swapNoElapsedPath` failure is the
  outer wrapper proving transfer-prefix traces after safe-transfer events. The
  reusable suffix specs now include preservation of pre-existing events so the
  wrapper can call the suffix theorem instead of re-expanding the suffix.
- Completed checkpoint: `lake build TamaUniV2.Proof.UniswapV2PairProof` passes
  after the wrapper refactor. `swapNoElapsedPath` now proves executable
  no-elapsed success, transfer-prefix traces, reserve updates, unchanged
  cumulatives, restored unlock, and `Sync`/`Swap` events through the actual run.
  Do not return to the direct branch-unfolding proof.
- Next route: add the public no-elapsed `swap` adapter over the verified
  `swapNoElapsedPath` theorem. Match the public burn adapter shape: lock state,
  timestamp guard, helper success case, wrapper rollback reconciliation.
- 2026-05-16 active proof note: the first public `swap` adapter attempt reduced
  to the helper success case but did not simplify the public output guard that
  wraps `swapNoElapsedPath`. The failing branch had the base helper success
  equation and only needed the raw `amount0Out/amount1Out` output guard in the
  final simplification. Do not restart swap arithmetic or the helper proof.
- Follow-up: even after the semantic mismatch was fixed, the public wrapper
  theorem hit Lean's deterministic kernel timeout while normalizing the full
  public `swap` body. Source has been factored with internal
  `swapNoElapsedAfterOutputPath` so the public no-elapsed proof should use:
  public lock/timestamp/output prefix -> dispatch helper run -> verified
  `swapNoElapsedPath` run. Do not retry full public-body simplification.
- Completed: `swapNoElapsedEntryPath` and `swapNoElapsedAfterOutputPath` now
  factor the public no-elapsed branch. The public no-elapsed `swap` success
  theorem is proved over the actual `(swap ...).run s`, including reserve
  updates, unchanged cumulatives, `unlocked = 1`, output transfer traces, and
  `Sync`/`Swap` events. The successful proof route uses
  `Contract.eq_of_run_success` to convert successful helper `.run` facts to raw
  contract-call facts before simplifying callers. `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes after this route.
- The public swap source factoring moved the insufficient-output guard into the
  no-elapsed entry branch and the elapsed branch. The exact zero-output revert
  proof now case-splits the timestamp branch and still proves the same public
  revert payload/state. This is intentional and verified by the focused pair
  proof build.
- Mint route update: added internal `mintFirstLiquidityPath` for the first-mint
  sqrt/liquidity/accounting branch and restructured public `mint` so first and
  subsequent branches each return through their own timestamp/finalization
  suffix. This avoids unsupported monadic assignment into a mutable local and
  keeps future first-mint proofs off the old full-body expansion route. Source,
  spec, and focused pair proof builds pass after this refactor.
- 2026-05-16 active continuation: current first task is still notes hygiene,
  then the active proof route is the helper-level
  `pair_mintFirstLiquidityPath_run_success` obligation. Do not expand public
  `mint` yet; prove the bounded helper first, verify focused pair proof, then
  build the public first-mint wrapper from that helper plus
  `finishMintNoElapsed_run_success_suffix`.
- Progress update: the helper spec and Tama marker are now in
  `UniswapV2PairProof.lean`. A direct proof over the full Tamago sqrt return
  term was too large, so the current proof route only proves/run-reuses the
  actual Tamago sqrt state-preservation fact and then case-splits the sqrt run.
  The last focused build was manually interrupted before a result; no repo-local
  lake/lean process remained afterward. Continue by rerunning
  `lake build TamaUniV2.Proof.UniswapV2PairProof` and fixing only the local
  helper proof obligations.
- Invariant-first route correction: stopped the failed aggregate
  `pair_mintFirstLiquidityPath_run_success` proof. Public specs should be short
  invariants and preservation lemmas; executable run facts are now proof
  adapters, not the main public spec style.
- Public spec strategy is now invariant-first. The intended assurance argument
  is: actual function runs imply small `PairWorldStep` facts; every finite
  sequence of `PairWorldStep`s preserves `PairWorldGood`; projections of
  `PairWorldGood` give reserve backing, uint112 bounds, minimum-liquidity lock,
  and K/accounting properties. Added public global and per-action preservation
  specs plus concrete-state reserve projection specs; focused Pair proof builds
  pass after each slice.
- 2026-05-16 18:46 PDT: user clarified that `docs/agent-progress.md` is
  append-only historical context. Future updates may add timestamped checkpoints
  at the end, but must not prune, rewrite, or reorder older entries while
  cleaning outdated active docs. API parity is not a formal spec category; it is
  only a build/review constraint. Active spec work should target behavioral
  properties from canonical Uniswap V2: TWAP/oracle updates, flash-callback
  atomicity/lock/K checks, full mint/burn/swap accounting and guard coverage,
  skim/sync reconciliation, fee-off `kLast = 0`, and factory uniqueness
  invariants.
- 2026-05-16 18:49 PDT: documentation cleanup checkpoint. Removed the
  superseded remediation and executable-success plan files from active
  `docs/superpowers/plans`, rewrote the active invariant-first plan as the sole
  forward plan, and rewrote `docs/spec-coverage.md` to separate current
  implemented coverage from active gaps. This log remains historical; do not use
  older entries as the current route when they conflict with the active plan and
  coverage docs.
- 2026-05-16 19:01 PDT: resumed spec work from the active invariant-first plan.
  Backed up `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean` to
  `/private/tmp/UniswapV2PairSpec.before-restore-public-obligations.lean`
  before restoring missing Pair spec predicates referenced by the existing proof
  exports. The restore is limited to bridge predicates and closed-world
  invariant/action predicates; no contract API/source helpers are being added.
- 2026-05-16 19:11 PDT: Pair public spec/proof coherence restored. Focused
  `lake build TamaUniV2.Proof.UniswapV2PairProof`, `/Users/zefram/.tama/bin/tama
  check`, `/Users/zefram/.tama/bin/tama build`, and `/Users/zefram/.tama/bin/tama
  audit` all pass. The only proof patch beyond spec restoration was making the
  same-supply no-spot-profit arithmetic proof use an explicit positive
  `a * b` fact; no contract source/API changes were made in this slice.
- 2026-05-16 19:16 PDT: added concise public bridge specs proving successful
  `skim` refines the closed-world skim transition and same-block `sync` refines
  the closed-world sync transition. Added common after-state helpers only in
  `verity/common`, not contract source. Backups were written to `/private/tmp`
  before edits. Focused Pair proof, `tama check`, `tama build`, and `tama audit`
  all pass for this slice.
- 2026-05-16 19:23 PDT: user correctly identified that `UniswapV2Pair.lean`
  still contains proof-convenience helper functions inside the contract source.
  Those helpers must be removed from the contract itself, not hidden with ABI
  filters, and must not be reintroduced. Future specs/proofs should target the
  canonical Pair entrypoints directly or use helpers only outside contract
  source, such as spec/common/proof lemmas.
- 2026-05-16 19:50 PDT: Pair source-helper cleanup completed and verified.
  Removed the proof-only helper functions from `UniswapV2Pair.lean`, inlined
  their behavior back into canonical public entrypoints, removed the ABI filter
  workaround, and pruned stale helper/no-elapsed public obligations plus their
  proof adapters. A helper-name scan over `verity/src`, `verity/common`,
  `verity/spec`, `verity/proof`, and `tama.toml` is empty. `lake build
  TamaUniV2.UniswapV2Pair`, focused Pair spec/proof builds, `tama check`,
  `tama build`, and `tama audit` pass. Coverage note: the pruned bridge facts
  must now be rebuilt directly over canonical public functions or through
  closed-world transition lemmas outside contract source.
- 2026-05-16 19:57 PDT: user superseded the old seven-gap checklist. Current
  spec work must follow the newer standard: short, composable Lean properties
  about contract invariants, transition constraints, finite-trace economic
  safety, and narrow public-entrypoint bridges to those facts. Do not use the
  earlier seven-gap checklist as a task source after this point.
- 2026-05-16 20:04 PDT: shifted spec files toward a paper-like assurance flow.
  `UniswapV2PairSpec.lean` now has section narratives for views, ERC20 boundary
  traces, revert frames, local entrypoints, exact guard runs, and closed-world
  economic invariants. Added short Pair closed-world specs/proofs for zero
  supply/locked-liquidity coherence, locked liquidity never exceeding supply,
  donation preserving cached reserves/K, swap/skim/sync LP-supply preservation,
  skim K preservation, and sync K nondecrease from reserve backing. Added
  `UniswapV2FactoryGhost.lean` and Factory spec/proofs for finite successful
  create histories: sorted nonzero pair entries, sorted-pair uniqueness,
  symmetric membership, append-one creation, preservation of existing pairs, and
  pair-count/list-length consistency. Focused Pair proof, focused Factory proof,
  and `tama check` pass. No Pair contract helpers were reintroduced.
- 2026-05-16 20:08 PDT: added explicit atomicity specs. Pair now proves that
  any reverted mint, burn, swap, skim, or sync run leaves pair storage, LP
  balance/allowance maps, and events unchanged. Factory now proves that any
  reverted createPair run leaves pair mappings, allPairs storage, length, and
  events unchanged. Focused Pair proof, focused Factory proof, full
  `lake build TamaUniV2.Proof`, and `tama check` pass after these additions.
- 2026-05-16 20:12 PDT: attempted to restore the direct exact public
  zero-output swap revert spec over `(swap 0 0 to data).run s`. The statement is
  desirable, but direct inlining of canonical public `swap` currently triggers
  Lean kernel deep-recursion during proof reduction. Backed the attempted public
  obligation out so the proof suite stays green. Future route should be a
  proof-local decomposition lemma or ordered-prefix adapter, never a contract
  source helper.
- 2026-05-16 20:17 PDT: fixed a stale factory CREATE2 embedded Pair bytecode
  constant after `tama test` caught a deterministic address mismatch. Backed up
  `verity/src/TamaUniV2/UniswapV2Factory.lean` to
  `/private/tmp/UniswapV2Factory.lean.before-pair-code-refresh`, regenerated
  only `pairCreationCodeLength` and `pairCreationCodeChunks` from
  `artifacts/bytecode/UniswapV2Pair.bin`, and rebuilt generated outputs. Current
  verification after this fix: `lake build TamaUniV2.UniswapV2Factory`, `tama
  build`, `tama test` (26/26), `tama check`, and `tama audit` all pass. Lesson:
  after Pair bytecode changes, always refresh and test the Factory's embedded
  CREATE2 creation code before claiming Factory parity.
- 2026-05-16 20:28 PDT: added the next Tamago-style closed-world Pair spec
  slice. New public obligations prove arbitrary finite paths from a good
  PairWorld preserve the core invariant and reserve backing, only mint/burn can
  change LP total supply, any non-burn step cannot decrease cached K, any
  no-burn finite path cannot decrease cached K, and any same-LP-supply no-burn
  path cannot create spot-price value. Updated active docs to distinguish this
  theorem from the still-open full caller-ledger no-profit theorem for arbitrary
  mint/burn round trips. Verification: focused Pair proof, full
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26),
  and `tama audit` all pass.
- 2026-05-16 20:32 PDT: committed the prior green checkpoint as `4283d1f`
  (`Strengthen Uniswap V2 specs and refresh pair create2 bytecode`). Current
  task focus is the user's updated spec standard: spec files should read like a
  coherent assurance essay, with small composable invariants, transition facts,
  narrow executable bridges, and sequence-level economic consequences. Reviewed
  Tamago ERC4626 closed-world specs again for structure: public spec sections
  describe properties/security conclusions; ghost/helper definitions live
  outside `verity/spec`; finite trace models use actual step relations; and
  caller-wealth/no-profit arguments are explicit closed-world consequences
  rather than aggregate function-body restatements.
- 2026-05-16 20:37 PDT: added a Pair spec readability/invariant slice without
  touching contract source. `UniswapV2PairSpec.lean` now breaks the
  closed-world argument into numbered reader sections: reachability invariants,
  concrete projections, LP supply discipline, donation framing, liquidity
  creation/redemption, swap safety, sequence-level economics, and skim/sync.
  New public obligations prove path-wide supply coherence, path-wide uint112
  reserve bounds, path-wide locked-liquidity coverage, share-only action
  framing, first/subsequent mint lock behavior, burn supply/locked-liquidity
  discipline, and swap positive-input/output plus output-below-reserve facts.
  Verification: focused Pair proof, full `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), and `tama audit` all pass.
  This improves the narrative and invariant explicitness; it does not claim the
  full caller-ledger mint/burn round-trip no-profit theorem is complete.
- 2026-05-16 20:44 PDT: added a narrow `sync` bridge without adding source
  helpers. Public specs now prove the expected concrete sync state refines the
  closed-world sync transition, and a success-conditional bridge ties that fact
  to the actual public `(sync).run s` result when success is supplied. An
  attempted all-branches executable sync postcondition was backed out because
  reducing the full elapsed-oracle branch caused Lean kernel recursion; keep
  future executable sync/TWAP work proof-local and decomposed, not by adding
  contract helpers. Verification: focused Pair proof, full `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), and
  `tama audit` all pass.
- 2026-05-16 20:59 PDT: in progress on the next Pair economic assurance slice.
  Added public specs/proofs for LP-normalized K: each successful closed-world
  step from a good positive-supply state cannot decrease `K / totalSupply^2`,
  the property composes over arbitrary finite paths, same-LP-supply paths
  therefore cannot reduce raw K, and same-LP-supply paths cannot reduce the
  pool's value at the initial spot price. This directly addresses mint/burn
  round trips without changing contract source or adding proof helper APIs.
  Focused `lake build TamaUniV2.Proof.UniswapV2PairProof` passes; Tama metadata
  and docs have been updated and full verification is next.
- 2026-05-16 21:01 PDT: full verification for the LP-normalized K slice passes:
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit`. `tama build` refreshed `tama.lock` only for the
  `tama.toml` hash; no contract source or public API helper was added.
- 2026-05-16 21:10 PDT: in progress on the next bridge slice. Added
  `Common` expected-state helpers and public specs/proofs showing subsequent
  mint, burn, and swap concrete arithmetic facts refine the corresponding
  closed-world PairWorld transitions. These are conditional bridge obligations,
  not aggregate function-body specs: they keep helper formulas out of
  `verity/spec` and let the closed-world invariant section consume concise
  transition facts. Focused `lake build TamaUniV2.Proof.UniswapV2PairProof`
  passes after the new proofs. Full Tama verification is next.
- 2026-05-16 21:11 PDT: full verification for the bridge slice passes:
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit`. The only build warning remains Foundry's sandboxed
  signature-cache write; it does not affect compile/test/audit success.
- 2026-05-16 21:17 PDT: resumed after compaction with the user's clarified
  spec standard front and center. The obsolete seven-gap checklist is no longer
  the organizing frame. Current task is a small oracle/TWAP sync slice written
  as readable assurance claims: same-timestamp reserve updates do not change
  cumulative prices, and elapsed updates with nonzero old reserves add exactly
  the Uniswap V2 fixed-point price times elapsed time. Existing WIP is failing
  only in the new proofs around reduction of the monadic `blockTimestamp`
  primitive; contract source/API must not be changed to make the proof easier.
- 2026-05-16 21:34 PDT: adjusted the oracle/TWAP slice after testing the
  executable `sync.run` proof path. The monolithic executable proof reduced to
  the right branches but produced kernel-deep proof terms, so it was not a good
  maintainable obligation. Kept the existing executable `sync` reserve bridge
  intact, added small oracle arithmetic helpers in `Common`, and added readable
  public specs/proofs for same-timestamp cumulative immutability and elapsed
  fixed-point price-time accumulation. Focused
  `lake build TamaUniV2.Proof.UniswapV2PairProof` now passes.
- 2026-05-16 21:37 PDT: full verification for the oracle/TWAP arithmetic slice
  passes: `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). Also updated active docs so the current
  route is clear: same-timestamp and elapsed oracle cases are valid concise
  specs, while proof-convenience helpers must stay out of the contract/API.
- 2026-05-16 21:38 PDT: committed the oracle/TWAP arithmetic slice as
  `0f1a414` (`Add Pair oracle arithmetic specs`). Continuing with the next small
  security-relevant spec slice: exact `sync` overflow reverts when either
  observed token balance exceeds the uint112 reserve bound. This strengthens the
  public sync boundary without changing contract source or adding trust.
- 2026-05-16 21:41 PDT: added and proved exact run-result `sync` overflow
  reverts for token0 and token1 observed balances above `maxUint112`, wired the
  obligations into `tama.toml`, and completed verification: focused Pair proof,
  full `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). No contract source/API change.
- 2026-05-16 21:43 PDT: continuing the invariant-first spec work with the
  reader-facing standard explicitly in force: specs should read like a
  correctness/security essay made of concise formal claims. Next slice is exact
  `mint` reserve-overflow revert coverage, chosen because it strengthens the
  uint112 reserve-bound story at a canonical public boundary without changing
  the contract API or adding helper functions to the source.
- 2026-05-16 21:43 PDT: added public `mint` reserve-overflow obligations for
  token0 and token1 with comment blocks explaining their role in the reserve
  domain argument. These specs are exact run-result guard claims over the real
  `mint` entrypoint and are wired in `tama.toml`; proof/verification is next.
- 2026-05-16 21:47 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes for the mint overflow slice. A
  first broad `simp` proof over `mint` was too expensive, so the final proof
  uses explicit proof-local boolean facts for the early overflow guard and does
  not unfold through later liquidity/sqrt/oracle branches.
- 2026-05-16 21:57 PDT: full verification passes for the mint overflow slice:
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The recurring Foundry signature-cache
  warning is sandbox-only and did not affect build/test/audit success.
- 2026-05-16 21:57 PDT: committed the mint reserve-overflow slice as
  `a7c0d2b` (`Prove mint reserve overflow reverts`). Continuing the ordered
  revert matrix with the next burn boundary: a burn must fail with
  `INSUFFICIENT_LIQUIDITY_BURNED` before pro-rata redemption if the pair holds
  no LP tokens to burn, or if total supply is zero.
- 2026-05-16 21:58 PDT: added the two burn insufficient-liquidity obligations
  with comment blocks: no pair-held LP liquidity, and positive pair-held LP
  liquidity with zero total supply. Both are exact run-result specs over the
  real `burn` entrypoint and are now wired in `tama.toml`; proof build is next.
- 2026-05-16 22:03 PDT: backed out the uncommitted burn insufficient-liquidity
  WIP after two focused proof attempts showed the direct exact-run proof was
  reducing too much of burn's long pre-guard prefix. This guard is still a
  valuable future target, but it needs a proof-local decomposition of the burn
  prefix instead of a monolithic `simp only` proof. Switching next to earlier
  swap guard obligations so the ordered revert matrix continues with green,
  coherent commits.
- 2026-05-16 22:04 PDT: added the zero-output swap exact-run obligation with a
  reader-facing comment explaining that it is the first economic swap
  precondition after the lock. This proves a swap cannot reach transfers,
  callbacks, or K checks unless at least one output amount is positive.
- 2026-05-16 22:07 PDT: backed out the uncommitted zero-output swap exact-run
  WIP after the proof reduced to the right small expression but produced a
  kernel-deep proof term. Exact-run guards past the simplest lock/overflow
  prefixes should be handled later with a reusable prefix adapter. Switching to
  a closed-world K invariant now so the spec suite gains a useful composable
  economic fact without widening the contract or trust surface.
- 2026-05-16 22:08 PDT: added `pair_closed_world_mint_never_decreases_k`.
  Plain-language role: a valid mint adds token balances and then caches those
  balances as reserves, so minting liquidity cannot reduce raw cached K. This
  complements the existing swap/sync/donation K facts and keeps the public spec
  narrative focused on composable economic consequences.
- 2026-05-16 22:09 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes for the mint-K invariant. The
  proof unfolds only the closed-world `PairWorldMintStep` and uses monotonicity
  of multiplication over `reserve + amount` on each side.
- 2026-05-16 22:14 PDT: full verification passes for the mint-K invariant:
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 22:15 PDT: committed the mint-K invariant as `06955c2`
  (`Prove mint K nondecrease invariant`). Starting a small LP-supply discipline
  slice: make explicit that valid mints strictly increase total LP supply and
  valid burns never increase total LP supply, so the spec narrative states the
  monotonic consequences rather than forcing readers to infer them.
- 2026-05-16 22:16 PDT: added two LP-supply consequence obligations:
  `pair_closed_world_mint_strictly_increases_supply` and
  `pair_closed_world_burn_never_increases_supply`. They sit in the LP supply
  discipline section as short reader-facing claims derived from the existing
  exact mint/burn supply formulas.
- 2026-05-16 22:19 PDT: full verification passes for the LP-supply
  monotonicity slice: focused `lake build TamaUniV2.Proof.UniswapV2PairProof`,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 22:22 PDT: committed the LP-supply monotonicity slice as
  `a641cf0` (`Prove LP supply monotonicity invariants`). Starting a
  reader-facing reachable-economics slice inspired by Tamago's ERC4626 pattern:
  keep the reusable path machinery, then expose compact theorems a maintainer
  can cite directly for all finite reachable positive-supply paths.
- 2026-05-16 22:25 PDT: added reachable-economics public obligations:
  positive-supply paths remain positive, reachable same-supply paths cannot
  reduce raw K, and reachable same-supply paths cannot create spot-price value.
  Full verification passes: focused `lake build TamaUniV2.Proof.UniswapV2PairProof`,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 22:27 PDT: committed reachable same-supply economics as
  `fce64a7` (`Expose reachable same-supply economics`). Starting a K-direction
  classifier slice: prove that any one-step raw K decrease from a good state
  must be a burn, so swaps/sync/skim/donations/share-only actions cannot be the
  source of K loss.
- 2026-05-16 22:29 PDT: added and proved
  `pair_closed_world_k_decrease_requires_burn`. Full verification passes:
  focused `lake build TamaUniV2.Proof.UniswapV2PairProof`, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 22:30 PDT: committed the K-direction classifier as `de2fba1`
  (`Prove K decrease requires burn`). Starting factory finite-path invariants:
  path preservation from any good factory state, path-wide length/list
  consistency, and append-only preservation of existing pair membership.
- 2026-05-16 22:32 PDT: added and proved factory path obligations:
  `factory_closed_world_path_preserves_good`,
  `factory_closed_world_path_preserves_existing_pairs`, and
  `factory_closed_world_path_length_matches_created_pairs`. Full verification
  passes: focused `lake build TamaUniV2.Proof.UniswapV2FactoryProof`, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 22:34 PDT: refreshing active guidance docs only:
  `docs/spec-coverage.md` and the invariant-first plan now record the reachable
  economics, K-decrease classifier, and factory finite-path invariants. No
  historical log entries were edited; this entry records the doc refresh.
- 2026-05-16 22:35 PDT: refreshed the Pair spec's closed-world narrative block
  so it describes the current LP-normalized K and reachable same-supply
  no-profit theorem, with the no-burn theorem framed as a simpler corollary.
  Focused `lake build TamaUniV2.Spec.UniswapV2PairSpec` passes.
- 2026-05-16 22:36 PDT: starting a burn locked-liquidity consequence slice:
  prove that from a good positive-token state, a valid burn cannot drain either
  modeled token balance to zero. This complements the existing supply-side lock
  facts with the token-side economic consequence.
- 2026-05-16 22:37 PDT: while adding that token-side burn consequence, found a
  real ghost-model gap: `PairWorldBurnStep` did not require positive liquidity,
  positive supply, or positive redeemed token amounts even though executable
  burn does. Tightening the closed-world burn step first, then repairing proofs.
- 2026-05-16 22:43 PDT: tightened `PairWorldBurnStep` to require positive
  redeemed amounts, positive burned liquidity, and positive pre-burn supply;
  added and proved `pair_closed_world_burn_preserves_positive_balances`, which
  states the token-side consequence of the minimum-liquidity lock. Full
  verification passes: focused `lake build TamaUniV2.Proof.UniswapV2PairProof`,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 22:46 PDT: committed the burn ghost-model tightening as
  `e815c75` (`Tighten burn ghost model`). Starting the next narrative spec
  slice: expose mint/burn LP-share safety explicitly, so readers do not have to
  infer from the generic LP-normalized K theorem that liquidity changes cannot
  dilute the remaining pool share.
- 2026-05-16 22:46 PDT: added reader-facing mint/burn LP-share obligations:
  `pair_closed_world_mint_does_not_dilute_existing_lp_share` and
  `pair_closed_world_burn_does_not_dilute_remaining_lp_share`. They reuse the
  existing LP-normalized K theorem but make the economic ratio conclusion
  explicit in the spec narrative.
- 2026-05-16 22:49 PDT: full verification passes for the mint/burn LP-share
  narrative slice: focused `lake build TamaUniV2.Proof.UniswapV2PairProof`,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 22:50 PDT: committed the LP-share safety slice as `23e4c1f`
  (`Expose mint burn LP share safety`). Starting the flash-swap/reentrancy
  slice: identify concise Lean specs that state callback gating, lock exposure
  during callback, atomic callback failure, and post-callback K checking without
  adding any contract helpers or new trust surfaces.
- 2026-05-16 22:50 PDT: source read shows the callback `data.length` gate lives
  inside the callback ECM's Yul compile template, while the Lean `ecmDo` model
  abstracts the recipient call as `pure ()`. Added specs for the facts Lean can
  state honestly now: the ECM compile template gates the callback under
  `data_length > 0`, and the closed-world swap transition accounts for final
  balances as reserves minus output plus inferred input before K is checked.
- 2026-05-16 22:56 PDT: full verification passes for the flash-boundary slice:
  focused `lake build TamaUniV2.Proof.UniswapV2PairProof`, whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), and
  `tama audit` (0 issues). The Foundry signature-cache warning remains
  sandbox-only.
- 2026-05-16 22:56 PDT: committed the flash-boundary slice as `b61541d`
  (`Specify flash swap boundary accounting`). Starting an ordered swap-guard
  slice: add exact executable revert obligations for the canonical
  pre-interaction swap guards, so the spec narrative covers the checks before
  any optimistic output transfer or callback boundary is reached.
- 2026-05-16 22:56 PDT: added exact run-result swap guard specs for zero
  output, insufficient liquidity, and invalid token-address recipient. These
  are deliberately ordered after the lock gate and before any external
  transfer/callback boundary.
- 2026-05-16 23:08 PDT: direct Lean proofs for those three swap guard specs
  were attempted by unfolding `swap`, but the monolithic reduction hit kernel
  depth limits. The current slice keeps the concise public specs and mirrors
  them with exact Foundry revert-message checks; a later proof pass should
  decompose the ordered prefix proof locally rather than adding contract
  helpers or weakening the public spec shape.
- 2026-05-16 23:08 PDT: refined that slice after `tama build` correctly
  rejected public obligations without Lean dischargers. Kept the zero-output
  swap guard as a public Lean obligation and added its direct proof. Kept exact
  Foundry revert-message checks for insufficient liquidity and invalid
  recipient, but removed their public Lean obligations until the proof can be
  decomposed without monolithic swap unfolding.
- 2026-05-16 23:22 PDT: verification passed for the zero-output swap guard
  slice: focused `lake build TamaUniV2.Proof.UniswapV2PairProof`, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 23:23 PDT: committed the zero-output swap guard slice as
  `baa8d2b` (`Prove swap zero output guard`). Starting a readability pass over
  the Pair/Factory spec files only: improve narrative section comments and
  reader-facing explanations without changing contract source, public ABI, or
  proof meanings.
- 2026-05-16 23:24 PDT: Pair spec readability pass added plain-language guide
  blocks for initialization, LP approval/transfer accounting, reusable guard
  adapters, exact executable guards, skim/sync bridges, and mint/burn/swap
  bridges. Focused `lake build TamaUniV2.Spec.UniswapV2PairSpec` passes.
- 2026-05-16 23:25 PDT: committed the Pair spec narrative pass as `b57bbf0`
  (`Clarify pair spec narrative`). Starting a factory bridge slice: add a short
  public spec/proof that a successful executable `createPair` run refines the
  closed-world factory create transition, tying concrete storage/event success
  to the finite-trace factory invariants.
- 2026-05-16 23:28 PDT: added and proved
  `factory_createPair_first_success_refines_closed_world`. The proof required a
  local `addressToWord` injectivity lemma, derived from the 160-bit Address
  bound inside the 256-bit Uint domain, not a new axiom. Focused `lake build
  TamaUniV2.Proof.UniswapV2FactoryProof` passes.
- 2026-05-16 23:31 PDT: full verification passed for the factory first-create
  bridge slice: whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-16 23:32 PDT: committed the factory first-create bridge as
  `2d1baea` (`Bridge first factory create`). Continuing the same factory bridge
  track by generalizing from the empty initial factory to an arbitrary modeled
  factory history whose count and no-existing-pair facts correspond to the
  concrete pre-state.
- 2026-05-16 23:33 PDT: added and proved
  `factory_createPair_success_refines_closed_world`, the general factory
  success bridge for any modeled pre-history with matching pair count and no
  existing sorted pair. Focused `lake build
  TamaUniV2.Proof.UniswapV2FactoryProof` passes.
- 2026-05-16 23:35 PDT: full verification passed for the generalized factory
  bridge slice: whole `lake build TamaUniV2.Proof`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-16 23:36 PDT: committed the generalized factory bridge as `965afd9`
  (`Generalize factory create bridge`). Starting an oracle arithmetic slice:
  add the missing no-op branch showing cumulative prices stay unchanged when
  the elapsed-price branch is inactive, even if the timestamp comparison branch
  is entered.
- 2026-05-16 23:42 PDT: added and proved
  `pair_sync_oracle_inactive_elapsed_keeps_price_cumulatives`. The spec is a
  small oracle invariant, not an executable helper: entering the timestamp
  changed branch still leaves cumulative prices unchanged when elapsed time is
  zero or either old reserve is zero. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes. Full verification is next.
- 2026-05-16 23:43 PDT: full verification passed for the inactive oracle
  branch slice: whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-16 23:44 PDT: committed the inactive oracle branch slice as
  `200a546` (`Cover inactive oracle update branch`). Continuing with the
  highest-value oracle bridge work: connect a successful public reserve-update
  entrypoint, starting with `sync`, to the concise oracle arithmetic facts
  already proved. Keep this as a narrow bridge, not a whole-function aggregate
  postcondition and not a contract helper.
- 2026-05-16 23:58 PDT: attempted a direct executable `sync` to oracle-storage
  bridge, first as one all-branch theorem and then as three short same-timestamp
  / active-elapsed / inactive-elapsed bridge specs. The statements were
  conceptually right, but reducing the full monadic storage/event path generated
  proof terms that hit Lean kernel recursion even after branch splitting. Backed
  out the uncommitted bridge specs/proofs/toml entries to keep the tree green.
  Do not retry this with brute-force `simp` over `(sync).run`; the next viable
  route needs a smaller proof-local post-state lemma or a Tamago-style trace
  bridge for reserve updates.
- 2026-05-17 00:05 PDT: tried the same direct-prefix approach for the early
  `burn` no-liquidity guard. Although the property is valuable, the ad hoc
  full-entrypoint simplification again wandered into a large reduction and had
  to be killed. Backed out the uncommitted spec/proof/toml entry. Lesson:
  executable guard expansion needs factored prefix adapters before adding more
  public run-result obligations beyond the ones already proved.
- 2026-05-17 00:13 PDT: after compaction, confirmed the attempted
  `pair_burn_run_revert_no_liquidity` proof was still the same monolithic
  executable route: Lean expanded into the full successful burn continuation
  after the target guard instead of closing on the failing branch. Removed the
  uncommitted spec/proof/toml entry again and will switch back to reader-facing
  invariant/economic specs plus narrow bridges only when they have a factored
  proof route.
- 2026-05-17 00:20 PDT: adding a small reader-facing no-profit obligation,
  `pair_closed_world_reachable_same_supply_path_pool_value_never_decreases`.
  It does not aggregate a whole function. It restates the existing same-LP-supply
  finite-path economics as a direct pool-value comparison at the initial spot
  price, matching the desired paper-like spec narrative.
- 2026-05-17 00:22 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes with the new reader-facing
  pool-value theorem. This is a good example of the current direction: short
  public property, clear comment, proof reuses the existing finite-path theorem
  instead of expanding executable contract bodies.
- 2026-05-17 00:23 PDT: `tama check` passes after adding the pool-value
  theorem and manifest entry.
- 2026-05-17 00:24 PDT: full verification passes for the reader-facing
  no-profit theorem slice: whole `lake build TamaUniV2.Proof`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 00:28 PDT: added and proved
  `factory_closed_world_unordered_pair_address_unique`. It is the factory-side
  version of the paper-like spec direction: a short theorem saying any reachable
  unordered token pair can resolve to at most one pair address. Focused
  `lake build TamaUniV2.Proof.UniswapV2FactoryProof` passes.
- 2026-05-17 00:29 PDT: `tama check` passes after adding the factory unordered
  uniqueness theorem and manifest entry.
- 2026-05-17 00:30 PDT: full verification passes for the factory unordered
  uniqueness theorem slice: whole `lake build TamaUniV2.Proof`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 00:33 PDT: added and proved
  `factory_closed_world_path_is_append_only`. It states that every finite
  factory path appends a suffix of new pair entries, preserves order, and
  advances pair count by exactly the suffix length. Focused `lake build
  TamaUniV2.Proof.UniswapV2FactoryProof` passes.
- 2026-05-17 00:35 PDT: full verification passes for the factory append-only
  path theorem slice: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 00:38 PDT: added and proved
  `pair_closed_world_reachable_path_lp_share_backing_never_decreases`. It states
  the global LP-share invariant directly: every finite path from a reachable
  positive-supply pool preserves or improves reserve product per squared LP
  supply. Focused `lake build TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 00:40 PDT: full verification passes for the reachable LP-share
  backing theorem slice: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 00:41 PDT: adding the reader-facing reachable-path reserve
  backing theorem. This is the invariant shape the spec narrative should expose:
  from any reachable pool state, every finite successful modeled history ends
  with cached reserves backed by actual token balances. It composes the existing
  reachability and path preservation lemmas instead of expanding executable
  contract bodies.
- 2026-05-17 00:42 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes for the reachable-path reserve
  backing theorem. The active coverage doc and invariant-first plan now describe
  this as part of the reader-facing closed-world safety argument.
- 2026-05-17 00:43 PDT: full verification passes for the reachable-path
  reserve-backing theorem slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 00:44 PDT: adding two more reader-facing finite-trace Pair
  invariants in the same style: every path from a reachable state keeps cached
  reserves inside `uint112`, and every such path preserves the minimum-liquidity
  lock shape. These are short theorem statements over the existing closed-world
  model, not new executable helpers or aggregate function summaries.
- 2026-05-17 00:45 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes for the reachable-path uint112 and
  minimum-liquidity-lock invariants. The coverage doc and active plan now name
  these as direct finite-trace invariants, not hidden consequences a reader has
  to reconstruct.
- 2026-05-17 00:46 PDT: full verification passes for the reachable-path uint112
  and minimum-liquidity-lock invariant slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 00:47 PDT: after checking Tamago's ERC4626 closed-world wealth
  pattern, exposing the Pair no-profit result with a caller-facing theorem name:
  same-LP-supply reachable paths cannot extract positive spot-value from the
  pool at the initial price. This deliberately reuses the existing pool-value
  theorem rather than adding an unsound dummy caller wallet ledger.
- 2026-05-17 00:48 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes for the caller-facing
  no-spot-value-extraction theorem.
- 2026-05-17 00:49 PDT: full verification passes for the caller-facing
  no-spot-value-extraction theorem slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 00:50 PDT: cleaning active docs to prevent future compaction
  amnesia: the active plan no longer treats a vague "full caller ledger" as the
  next task. It now records the sound current stance: PairWorld proves
  pool-value no-extraction for same-LP-supply histories, and any future external
  wallet ledger must model real ownership changes rather than a dummy wealth
  field.
- 2026-05-17 00:51 PDT: adding a reader-facing no-burn K finite-trace theorem:
  from any reachable pool state, any successful modeled path with no burn cannot
  reduce cached K. This is the path-level form of the "K decreases only through
  liquidity redemption" argument.
- 2026-05-17 00:52 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes for the reachable no-burn K path
  theorem. Full verification is next.
- 2026-05-17 00:53 PDT: full verification passes for the reachable no-burn K
  path theorem slice: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 00:54 PDT: committing the reachable no-burn K path theorem slice.
  Next high-risk work remains the executable bridge/revert layer; avoid
  monolithic entrypoint reductions and only add public obligations when there is
  a factored proof route.
- 2026-05-17 00:55 PDT: adding a reader-facing factory lookup stability theorem:
  once an unordered token pair resolves to a pair in a reachable factory state,
  any later finite successful create history still contains that same lookup.
  This exposes the existing preservation lemma in the form routers care about.
- 2026-05-17 00:56 PDT: first focused Factory proof build failed because the
  new theorem called the existing path-preservation helper with explicit
  arguments where Lean expected the membership proof. Fixed the call to pass
  `h_existing h_path` directly; rerunning focused verification.
- 2026-05-17 00:57 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2FactoryProof` passes for the reachable factory lookup
  stability theorem. Full verification is next.
- 2026-05-17 00:58 PDT: full verification passes for the reachable factory
  lookup stability theorem slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 01:01 PDT: attempting the next ordered swap guard with a narrow
  pre-interaction proof route: after lock and nonzero-output gates pass, an
  output amount that is not below reserves should exactly revert with
  `UniswapV2: INSUFFICIENT_LIQUIDITY` before any transfer or callback. Also
  added the missing proof-only manifest entry for the already-proved zero-output
  exact run obligation.
- 2026-05-17 01:02 PDT: backed out the attempted public
  `pair_swap_run_revert_insufficient_liquidity` obligation. Even though the
  guard is pre-interaction, the direct proof still reduced through the whole
  swap continuation and hit Lean kernel recursion. Keep this out until there is
  a factored prefix adapter; the zero-output manifest entry remains because that
  theorem was already proved.
- 2026-05-17 01:04 PDT: retrying the insufficient-liquidity guard with the same
  proof shape used by the successful skim guard proofs: derive the failing
  proposition over `.val` reserve comparisons, not a separate Bool conjunction.
  This may let simplification stop at the guard instead of reducing the swap
  continuation.
- 2026-05-17 01:05 PDT: the Prop-shaped retry still hit Lean kernel recursion,
  so the insufficient-liquidity exact-run obligation is backed out again. Do not
  retry direct `simp` on `swap` for this guard in future contexts. A factored
  prefix adapter is required before adding it as a public Lean obligation.
- 2026-05-17 01:06 PDT: removed the `pair_swap_run_revert_zero_output`
  proof-only manifest entry. That obligation already has a Foundry mirror, and
  `tama build` correctly rejects obligations that are both mirrored and listed
  under `coverage.proof_only`.
- 2026-05-17 01:08 PDT: focused Pair proof build and `tama build` both pass
  after the manifest cleanup. Continuing with narrative-first spec work: short
  composable properties with plain-language comment blocks, not aggregate
  executable summaries.
- 2026-05-17 01:10 PDT: next slice is the `sync` executable bridge, split into
  small properties: successful `sync` sets reserves to observed balances,
  updates TWAP cumulatives by the existing oracle formula, restores the
  reentrancy lock, and emits `Sync`. This is a narrow public-entrypoint bridge,
  not a new contract helper or whole-function summary.
- 2026-05-17 01:12 PDT: first focused build of the `sync` executable bridge
  failed because monolithic `simp` over `sync` expanded all timestamp/oracle
  branches and hit kernel recursion. Switching immediately to a factored proof
  by timestamp branch and active/inactive elapsed branch; do not keep retrying
  the monolithic shape.
- 2026-05-17 01:23 PDT: backed out the direct public `sync.run` success bridge
  slice after the factored branch proof still left large nested `Contract.run`
  goals. This keeps the public spec suite aligned with the invariant-first
  standard: short composable properties plus narrow bridges only when the proof
  route is clean and local.
- 2026-05-17 01:25 PDT: added the reachable positive-supply finite-trace
  invariant. This exposes the existing minimum-liquidity/positive-supply
  argument in the reader-facing form: once a reachable pool is nonempty, no
  finite successful modeled history can return it to zero LP supply.
- 2026-05-17 01:31 PDT: compared the local Tamago ERC4626 closed-world spec
  structure and tightened the Pair spec narrative around sequence economics,
  surplus, and sync. The comments now explicitly separate properties specified
  from security conclusions, matching the paper-like flow requested for spec
  readers.
- 2026-05-17 01:33 PDT: full verification passes for the reachable
  positive-supply and narrative-spec slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 01:38 PDT: added and focused-built the finite-history LP supply
  firewall. The ghost model now has `PairWorldPathNoMintBurn`, and the public
  Pair specs prove that any successful modeled path with no mint and no burn
  preserves both total LP supply and locked liquidity.
- 2026-05-17 01:39 PDT: full verification passes for the no-mint/no-burn LP
  supply firewall slice: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 01:43 PDT: added and focused-built the reader-facing no-liquidity
  no-extraction corollary. Reachable paths containing no mint and no burn now
  prove the same spot-value no-extraction conclusion directly, by combining the
  supply firewall with the existing same-supply theorem.
- 2026-05-17 01:44 PDT: full verification passes for the no-liquidity
  no-extraction corollary slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 01:46 PDT: added and focused-built a reader-facing factory
  pair-count monotonicity invariant. It is the direct finite-path corollary of
  append-only creation: successful factory histories cannot decrease modeled
  public pair count.
- 2026-05-17 01:49 PDT: full verification passes for the factory pair-count
  monotonicity slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 01:54 PDT: selected the next invariant slice: reachable pools with
  positive LP supply should have positive reserves on both token sides, and
  finite successful modeled histories from such pools should preserve that
  nondegenerate reserve shape. This tightens the logical lead-in to the
  spot-price no-profit theorems without changing contract APIs or adding helper
  entrypoints.
- 2026-05-17 01:58 PDT: implemented and focused-built the positive-reserve
  invariant slice. The new public specs state that reachable nonempty pools
  have positive reserves on both token sides, and that finite successful paths
  from such pools preserve positive reserves. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 01:59 PDT: full verification passes for the positive-reserve
  invariant slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 02:00 PDT: committed the positive-reserve slice as `43295f9`.
  Next selected slice: strengthen the reader-facing same-supply no-extraction
  theorem so a reachable positive-supply pool no longer needs separate positive
  reserve hypotheses; those now follow from the invariant layer.
- 2026-05-17 02:01 PDT: implemented the stronger same-supply no-extraction
  wrapper. The public spec now reads in the desired theorem shape: any reachable
  positive-supply finite path that ends with the same LP supply cannot extract
  spot value from the pool at the initial price.
- 2026-05-17 02:02 PDT: full verification passes for the stronger same-supply
  no-extraction wrapper: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof`, `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 02:03 PDT: selected the next bridge slice: prove a narrow
  concrete `sync` lock-restoration fact. This is not a helper-function
  addition and not a broad executable summary; it states that when the lock
  gate and uint112 balance bounds pass, public `sync` succeeds and restores the
  reentrancy lock to `1`.
- 2026-05-17 02:09 PDT: backed out the attempted public `sync` lock-restoration
  obligation before commit. Even the success-only version forced Lean into the
  inline oracle/update branch structure and left a brittle monolithic reduction
  goal. Do not keep pushing this shape without first extracting a proof-local
  reserve-update adapter; continue with compositional closed-world specs unless
  that adapter is built deliberately.
- 2026-05-17 02:10 PDT: selected the next compositional slice: strengthen the
  no-mint/no-burn no-extraction corollary so reachable positive supply is
  enough. It will reuse the same-supply no-extraction wrapper plus the
  no-mint/no-burn supply firewall, avoiding any public-entrypoint unfolding.
- 2026-05-17 02:11 PDT: implemented the stronger no-mint/no-burn no-extraction
  corollary. The public theorem now states the common operational case without
  reserve-positive side premises: a reachable nonempty pool, no mint, and no
  burn imply no spot-value extraction at the initial price.
- 2026-05-17 02:12 PDT: full verification passes for the stronger no-mint/no-burn
  no-extraction corollary: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof`, `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 02:13 PDT: selected a small ordered-revert bridge next: exact
  `burn` insufficient-liquidity revert after the lock gate. This branch is
  before token transfers and should stay prefix-local, unlike the attempted
  `sync` success-lock proof.
- 2026-05-17 02:14 PDT: implemented the exact `burn`
  insufficient-liquidity revert spec/proof. The branch states that once the
  lock gate is open, `burn` reverts with
  `UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED` if the pair has no LP liquidity to
  burn or total supply is not positive.
- 2026-05-17 02:20 PDT: backed out the attempted public `burn`
  insufficient-liquidity obligation before commit. The naive proof did not stay
  prefix-local: Lean expanded past the intended early guard into transfer and
  oracle paths. This should also wait for a proof-local ordered-prefix adapter
  rather than more monolithic unfolding.
- 2026-05-17 02:21 PDT: updated the active plan and coverage docs with the same
  lesson, not only this historical log. Future bridge/revert work should build
  proof-local reserve-update and ordered-prefix adapters before reintroducing
  those public obligations.
- 2026-05-17 02:22 PDT: selected the next compositional factory invariant
  slice. The target spec is reader-facing: every lookup in a reachable factory
  state must point to a nonzero pair for two distinct nonzero tokens. This
  strengthens the factory story without changing contracts, adding helpers, or
  unfolding full executable entrypoints.
- 2026-05-17 02:23 PDT: implemented and focused-built the reachable factory
  lookup-validity theorem. The spec is documented in the factory spec narrative
  and the proof derives it directly from `FactoryWorldGood`; focused `lake
  build TamaUniV2.Proof.UniswapV2FactoryProof` passes.
- 2026-05-17 02:25 PDT: full verification passes for the factory lookup-validity
  slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 02:26 PDT: committed the factory lookup-validity slice as
  `8f231ea`. Next selected Pair slice: make the finite-history K classifier
  explicit. If a reachable path ends with lower cached K, that endpoint cannot
  be reachable by a burn-free history; this states "K loss requires LP
  redemption" at the same trace level as the no-profit theorems.
- 2026-05-17 02:28 PDT: implemented and focused-built the finite-history K
  classifier. The new public spec states the contrapositive directly:
  reachable lower-K endpoints exclude burn-free histories. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 02:29 PDT: full verification passes for the finite-history K
  classifier slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 02:31 PDT: committed the finite-history K classifier as
  `f634c0e`. Next selected flash-swap boundary slice: strengthen the existing
  callback ECM proof from "nonempty-data gated" to "gated canonical callback
  call encoding forwards selector, sender, output amounts, and target." This
  reduces callback-boundary ambiguity without adding a new axiom or modifying
  contract code.
- 2026-05-17 02:35 PDT: implemented and focused-built the stronger flash
  callback boundary spec. It now proves the generated gated ECM body contains
  the canonical selector write, sender and output amount calldata writes, and
  the call to the recipient target. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 02:36 PDT: full verification passes for the stronger flash
  callback boundary slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 02:37 PDT: committed the stronger flash callback boundary spec as
  `def038d`. Next selected adjacent boundary slice: prove the generated
  callback body does not swallow callback failure. It checks
  `iszero(__uv2_cb_success)`, copies returndata, and executes `revert`; this is
  boundary-level evidence toward callback failure atomicity without pretending
  the external callee is modeled in Lean.
- 2026-05-17 02:39 PDT: implemented and focused-built the callback failure
  boundary spec. The new public obligation proves the generated callback ECM
  body contains the low-level-call failure branch that copies returndata and
  reverts, so callback failure is not silently ignored. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 02:41 PDT: full verification passes for the callback failure
  boundary slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 02:42 PDT: next selected slice is a factory reader-facing
  append-only corollary: over any successful factory history, if the pair count
  is unchanged, the pair list is unchanged. This is a compact global
  no-overwrite/no-reorder invariant that strengthens the factory story without
  adding any contract helper or trust assumption.
- 2026-05-17 02:43 PDT: implemented and focused-built the factory same-count
  append-only corollary. Focused `lake build
  TamaUniV2.Proof.UniswapV2FactoryProof` passes without warnings from the new
  proof.
- 2026-05-17 02:45 PDT: full verification passes for the factory same-count
  append-only slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 02:47 PDT: next selected pair slice is a narrow executable `sync`
  success bridge. The target spec should state the reader-facing facts that
  matter after a successful `sync`: reserves equal observed balances, timestamp
  is the uint32 block timestamp, `Sync` is emitted, and the reentrancy lock is
  restored. This is deliberately not a whole-function aggregate spec.
- 2026-05-17 02:50 PDT: backed out the direct public `sync` success bridge
  attempt before committing it. Focused build showed the proof expands into the
  full inline oracle/update tail, matching the earlier warning in the active
  plan. The correct next route is a proof-local reserve-update adapter, not a
  monolithic entrypoint proof.
- 2026-05-17 02:52 PDT: selected a clean factory corollary instead of forcing
  the `sync` proof. Since same-count factory histories preserve the pair list,
  the next spec will state the router-facing consequence directly: every
  unordered pair lookup is identical before and after such a history.
- 2026-05-17 02:53 PDT: implemented and focused-built the factory same-count
  lookup corollary. It states that if pair count is unchanged across a finite
  successful factory history, every unordered lookup is identical before and
  after. Focused `lake build TamaUniV2.Proof.UniswapV2FactoryProof` passes.
- 2026-05-17 02:55 PDT: full verification passes for the factory same-count
  lookup corollary slice: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 02:57 PDT: selected a Pair contract-level reentrancy invariant.
  Instead of adding trust or callback axioms, the new reader-facing spec will
  package the existing exact locked-entrypoint proofs: when `unlocked != 1`,
  every mutating Pair entrypoint rejects with `UniswapV2: LOCKED`.
- 2026-05-17 02:59 PDT: implemented and focused-built the Pair reentrancy
  invariant. It composes the existing exact locked-run proofs for `mint`,
  `burn`, `swap`, `skim`, and `sync`; no new axiom or trust surface was added.
  Focused `lake build TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 02:59 PDT: full verification passes for the Pair reentrancy
  invariant slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 03:00 PDT: selected a one-step LP-supply firewall to improve the
  narrative flow before the finite-history no-mint/no-burn theorem. The new
  spec will state directly that any modeled action other than mint or burn
  preserves total LP supply and the permanently locked liquidity amount.
- 2026-05-17 03:01 PDT: implemented and focused-built the one-step LP-supply
  firewall. The proof constructs the one-step no-mint/no-burn path and reuses
  the existing finite-path preservation lemma, keeping the public spec short
  and the proof aligned with the trace model. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 03:04 PDT: full verification passes for the one-step LP-supply
  firewall slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 03:09 PDT: selected and implemented the directional no-burn
  supply invariant slice. The new reader-facing specs state that any modeled
  action other than burn cannot decrease total LP supply, and every finite
  successful no-burn history from a reachable state preserves or increases LP
  supply. This strengthens the essay flow beside the existing no-burn K
  theorem: without LP redemption, neither supply nor cached K moves in the
  extraction direction.
- 2026-05-17 03:11 PDT: focused build passes for the directional no-burn
  supply invariant slice after filling the first-mint Nat bound in the private
  proof helper. `lake build TamaUniV2.Proof.UniswapV2PairProof` succeeds.
- 2026-05-17 03:12 PDT: full verification passes for the directional no-burn
  supply invariant slice: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 03:13 PDT: selected the symmetric no-mint supply invariant slice.
  The target reader-facing claim is: without a mint step, a finite successful
  PairWorld history cannot increase LP supply. This complements the committed
  no-burn theorem and makes LP issuance/redemption isolation explicit in both
  directions.
- 2026-05-17 03:15 PDT: implemented and focused-built the no-mint supply
  invariant slice. Added a tiny `PairWorldPathNoMint` trace predicate plus
  reader-facing one-step, finite-path, and reachable finite-path obligations.
  `lake build TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 03:16 PDT: full verification passes for the no-mint supply
  invariant slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 03:17 PDT: selected the locked-liquidity monotonicity slice. The
  target reader-facing invariant is that from any good/reachable PairWorld
  state, finite successful histories cannot reduce the permanently locked
  liquidity amount; first mint may establish it, but no later modeled action
  can unwind it.
- 2026-05-17 03:19 PDT: implemented and focused-built locked-liquidity
  monotonicity. The public obligations cover one step from a good state,
  arbitrary finite paths from a good state, and reachable finite paths.
  `lake build TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 03:21 PDT: full verification passes for the locked-liquidity
  monotonicity slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 03:25 PDT: after the latest user clarification, reset the active
  spec-writing standard explicitly: spec files should read like a paper, with a
  clear argument that small invariants, transition facts, economic theorems, and
  narrow executable bridges together imply correctness/security. The next pass
  will improve reader-facing comments and add only short composable obligations,
  not aggregate whole-function summaries.
- 2026-05-17 03:27 PDT: updated the active invariant-first plan,
  `docs/spec-coverage.md`, the Pair/Factory spec introductions, and the
  Pair/Factory ghost-model introductions to preserve the essay-like assurance
  standard across future resumes. These are comment/doc changes only; no
  contract source or API was changed.
- 2026-05-17 03:31 PDT: tried to add exact executable mint under-backed-balance
  guard obligations, but the proof expanded past the intended ordered prefix
  after the lock write. Backed that public obligation out rather than force a
  monolithic entrypoint proof. The right future route is still a proof-local
  prefix adapter for lock-write/reserve-read guards.
- 2026-05-17 03:32 PDT: added a clean Tamago-style common-case K theorem
  instead: reachable finite histories with no mint and no burn cannot decrease
  cached K. This proves by embedding `PairWorldPathNoMintBurn` into the existing
  no-burn path theorem, so it does not touch executable contract source or add
  trust.
- 2026-05-17 03:34 PDT: focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes for the narrative/comment updates
  and the common-case no-mint/no-burn K theorem.
- 2026-05-17 03:46 PDT: full verification passes for the essay-style spec
  narrative/comment updates and the common-case no-mint/no-burn K theorem:
  `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The Foundry signature-cache warning
  remains sandbox-only.
- 2026-05-17 03:49 PDT: after committing the narrative/K slice, selected the
  next assurance gap: strengthen the executable-to-model bridge for public
  `sync()`. The target spec is a short actual-run property saying that, under
  the real lock and uint112 guards, `sync` succeeds, caches observed balances as
  reserves, restores the reentrancy lock, and emits `Sync`.
- 2026-05-17 04:01 PDT: backed out the attempted public `sync` success bridge
  and exact later-swap guard obligations after focused builds showed they still
  expand too much executable tail and create kernel-sized proof terms. Added a
  cleaner reader-facing theorem instead: same-LP-supply reachable histories have
  no token1-denominated spot-price profit at the initial `reserve1 / reserve0`
  price. Focused `lake build TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 04:03 PDT: full verification passes for the token1-denominated
  no-profit slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama
  build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 04:04 PDT: selected the next invariant-first gap: factory
  concrete-history reconstruction. The next small slice will introduce a
  storage/world correspondence relation for `allPairsLength`, pair mappings,
  reverse mappings, and indexed `allPairs` entries, then expose short specs
  showing concrete storage lookup agrees with the closed-world factory model.
- 2026-05-17 04:09 PDT: implemented and fully verified the first factory
  concrete reconstruction bridge. Added `FactoryWorldMatchesStorage` plus
  public length, unordered lookup, and indexed `allPairs` agreement specs.
  `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues) pass. The Foundry signature-cache
  warning remains sandbox-only.
- 2026-05-17 04:11 PDT: selected the next bridge slice: prove successful
  concrete `createPair` runs preserve `FactoryWorldMatchesStorage` after
  appending the newly created sorted pair. This is the direct link from real
  factory storage transitions to the closed-world append-only invariants.
- 2026-05-17 04:24 PDT: focused factory proof build passes for the createPair
  correspondence-preservation slice. During the proof, tightened
  `FactoryWorldMatchesStorage` to compare decoded `wordToAddress` storage
  values to modeled pair addresses, matching public factory views and avoiding
  any new CREATE2 canonical-word axiom. Added private frame lemmas for
  unrelated pair lookups and old `allPairs` indices, then proved successful
  `createPair` preserves the storage/world correspondence for the appended
  world.
- 2026-05-17 04:25 PDT: full verification passes for the createPair
  correspondence-preservation slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit` (0
  issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 04:27 PDT: after cleaning two local proof lints, re-ran affected
  verification: whole `lake build TamaUniV2.Proof`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues) pass. The Foundry signature-cache
  warning remains sandbox-only.
- 2026-05-17 04:28 PDT: selected the next concrete factory consequence slice:
  expose reader-facing specs that a successful `createPair` installs the new
  decoded lookup in both directions and preserves every existing reconstructed
  decoded lookup. This turns the storage/world bridge into the concrete
  no-hidden-overwrite argument routers care about.
- 2026-05-17 04:30 PDT: implemented and focused-built the concrete factory
  lookup consequence slice. Added public specs/proofs for decoded new-pair
  lookup installation in both token orders and preservation of existing decoded
  reconstructed lookups across successful `createPair`.
- 2026-05-17 04:31 PDT: full verification passes for the concrete factory
  lookup consequence slice: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 04:35 PDT: resuming after the essay-style spec clarification.
  The active next slice is factory finite-history concrete reconstruction:
  lift the one-step `createPair` storage/world correspondence preservation to
  arbitrary finite concrete create histories, so the Factory spec reads as a
  global router-visible invariant rather than isolated create facts.
- 2026-05-17 04:39 PDT: implemented the factory finite-history concrete
  reconstruction slice and the focused `lake build
  TamaUniV2.Proof.UniswapV2FactoryProof` passes. Added a concrete create path
  relation that records real successful `createPair` runs plus modeled append
  steps, then proved that such paths preserve storage/world correspondence,
  existing decoded unordered lookups, and existing indexed `allPairs` entries.
- 2026-05-17 04:43 PDT: full verification passes for the factory
  finite-history concrete reconstruction slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit` (0
  issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 04:45 PDT: committed the factory finite-history concrete
  reconstruction slice as `6996870`. The next selected Pair slice is the
  executable `sync` oracle bridge: prove that an unlocked successful `sync`
  with uint112-sized observed balances writes cumulative price slots according
  to the existing concise TWAP/oracle formulas, then expose same-timestamp,
  active-elapsed, and inactive-elapsed corollaries if the direct bridge stays
  tractable.
- 2026-05-17 04:55 PDT: the direct public `sync` oracle bridge did not stay
  tractable. I tried the whole-entrypoint unfolding route, backed out the public
  specs/proofs after Lean hit kernel deep-recursion limits, and confirmed the
  focused Pair proof build passes again after removal. Do not repeat that route:
  reserve-update bridge work needs proof-local prefix/update adapters first,
  with only short reader-facing obligations exposed afterward.
- 2026-05-17 05:01 PDT: implemented a stronger swap K slice. Added a public
  theorem that the canonical fee-adjusted swap K inequality implies raw cached
  K nondecrease once reserves equal the final balances, and removed raw K
  nondecrease as a premise from the public concrete-to-closed-world swap bridge.
  Focused `lake build TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 05:03 PDT: full verification passes for the strengthened swap K
  slice: `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`, `tama
  test` (26/26), and `tama audit` (0 issues). The Foundry signature-cache
  warning remains sandbox-only.
- 2026-05-17 05:04 PDT: committed the strengthened swap K slice as `18eda72`.
  Next target: remove raw cached-K nondecrease from the ghost swap transition
  itself, so the closed-world model assumes only canonical fee-adjusted K and
  derives raw K wherever the invariant stack needs it.
- 2026-05-17 05:07 PDT: removed raw K nondecrease from `PairWorldSwapStep`.
  The ghost swap transition now carries only the canonical fee-adjusted K
  inequality, while raw K nondecrease is derived in the closed-world K proofs
  using the new arithmetic lemma. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes.
- 2026-05-17 05:08 PDT: full verification passes for the canonicalized ghost
  swap step: `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 05:10 PDT: committed the canonicalized ghost swap step as
  `7a30b96`. Next selected slice: add an exact Lean run-result proof for the
  swap insufficient-liquidity guard. This guard is pre-transfer/pre-callback,
  immediately after the already-proved zero-output guard, so try it as a short
  ordered-prefix proof and back out if it expands into the later swap tail.
- 2026-05-17 05:14 PDT: backed out the uncommitted swap
  insufficient-liquidity Lean obligation after the focused Pair build again
  expanded into the later swap tail and hit kernel deep-recursion. Do not retry
  direct `simp`/whole-entrypoint unfolding for later swap guards; this still
  needs a true proof-local ordered-prefix adapter.
- 2026-05-17 05:15 PDT: selected a model-level economic slice instead of
  forcing later executable guards. Target: add a same-LP-supply no-extraction
  theorem over actual pool token balances, with an explicit balanced-start
  premise (`balance == reserve` on both sides). This avoids the false stronger
  claim that pre-existing donated surplus can never be skimmed.
- 2026-05-17 05:19 PDT: implemented and fully verified the actual token-balance
  no-extraction slice. Added `PairWorldBalanceSpotValueNum` and a reader-facing
  theorem: from a reachable positive-supply balanced start, any finite
  successful same-LP-supply history leaves the pair's actual token-balance value
  nondecreasing at the initial spot price. Verification passed: `tama check`,
  whole `lake build TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and
  `tama audit` (0 issues). The Foundry signature-cache warning remains
  sandbox-only.
- 2026-05-17 05:20 PDT: committed the token-balance no-extraction theorem as
  `b1bbbdb`. Next small corollary: common no-mint/no-burn histories from a
  balanced reachable start also cannot reduce actual token-balance value,
  because the existing supply firewall makes them same-LP-supply histories.
- 2026-05-17 05:24 PDT: implemented and fully verified the no-mint/no-burn
  token-balance no-extraction corollary. The new public theorem states the
  common operational form directly: from a reachable positive-supply balanced
  start, any finite successful history with no mint and no burn cannot reduce
  actual token-balance value at the initial spot price. Verification passed:
  `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues).
- 2026-05-17 05:25 PDT: committed the no-mint/no-burn token-balance
  no-extraction corollary as `9067d34`. Next active pass is spec narrative and
  coverage hygiene, then a small high-value invariant or bridge theorem.
- 2026-05-17 05:31 PDT: implemented the oracle narrative/spec lift: added
  generic reserve-update TWAP obligations for same-timestamp, active-elapsed,
  and inactive-elapsed cases, while keeping the existing `sync` bridge names as
  direct public-entrypoint corollaries. Focused Pair proof build passes:
  `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- 2026-05-17 05:31 PDT: full verification passes for the oracle narrative/spec
  lift: `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 05:32 PDT: committed the oracle reserve-update spec lift as
  `c1ec30e`. Next target should be another concise reader-facing property,
  preferably one that strengthens the bridge between canonical public behavior
  and the closed-world invariant/economic layer without whole-entrypoint
  unfolding.
- 2026-05-17 05:33 PDT: started a Tamago-style closed-world invariant slice:
  token-side no-drain from reachable nonempty pools. The new spec composes the
  existing positive-reserve finite-trace invariant with reserve backing to state
  directly that both actual token balances remain positive after any finite
  successful modeled history.
- 2026-05-17 05:35 PDT: focused Pair proof build passes for the token-side
  no-drain invariant: `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- 2026-05-17 05:36 PDT: full verification passes for the token-side no-drain
  invariant: `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 05:37 PDT: committed the token-side no-drain invariant as
  `4f98f65`. Next work should keep following the same pattern: short
  reader-facing invariants or narrow bridges, with no contract-source helpers.
- 2026-05-17 05:37 PDT: refreshed `docs/spec-coverage.md` so the active
  remaining-work section no longer reads like old broad mint/burn/swap
  checklists. It now points future work at executable bridge gaps, TWAP bridges,
  ordered guard prefixes, and explicit callback trace semantics.
- 2026-05-17 05:40 PDT: tried a narrow direct `sync` success bridge for
  reserves, oracle cumulatives, timestamp, and lock restoration. Focused Pair
  proof failed with Lean kernel deep recursion after expanding the inline
  reserve-update tail. Backed out the uncommitted spec/proof/manifest attempt.
  Do not retry direct public `sync` unfolding; the bridge needs a proof-local
  reserve-update adapter first.
- 2026-05-17 05:43 PDT: user confirmed the active spec style: spec files should
  read like papers or essays with a clear assurance argument for correctness,
  completeness, and security. Continue adding concise invariants, transition
  constraints, and bridge facts with plain-language comments that explain why
  each property matters. Do not revive stale aggregate executable-success
  specs, API-parity spec categories, or contract-source proof helpers.
- 2026-05-17 05:47 PDT: implemented the next narrative-style invariant slice:
  a finite-history LP share-bookkeeping theorem. The new closed-world path
  predicate covers histories made only of `approve`, `transfer`, and
  `transferFrom`; the public spec states these histories leave token balances,
  cached reserves, total LP supply, and locked liquidity unchanged. This closes
  the gap between one-step ERC20-share facts and the reader-facing sequence
  story without touching contract source or adding trust assumptions.
- 2026-05-17 05:49 PDT: focused Pair proof build passes for the share
  bookkeeping finite-history invariant: `lake build
  TamaUniV2.Proof.UniswapV2PairProof`. Next step is the full verification loop
  before committing.
- 2026-05-17 05:50 PDT: full verification passes for the share bookkeeping
  finite-history invariant: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 05:52 PDT: added the reader-facing economic corollary for pure LP
  share bookkeeping histories: if a finite path contains only LP approvals,
  transfers, and transferFroms, then cached K, reserve-denominated spot value,
  and actual token-balance spot value are unchanged. This keeps the spec file's
  narrative explicit: LP ownership movement is not an AMM profit path.
- 2026-05-17 05:54 PDT: focused Pair proof build passes for the share
  bookkeeping K/value corollary: `lake build
  TamaUniV2.Proof.UniswapV2PairProof`.
- 2026-05-17 05:55 PDT: full verification passes for the share bookkeeping
  K/value corollary: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 05:58 PDT: started a concrete factory-history bridge slice. Added
  a reader-facing spec/proof target saying successful concrete `createPair`
  histories cannot decrease router-visible `allPairsLength` storage, by
  composing the existing concrete storage/world match with the closed-world
  append-only path theorem. This is not an API-parity claim; it is a storage
  monotonicity invariant over real create histories.
- 2026-05-17 05:59 PDT: focused Factory proof build passes for concrete
  `allPairsLength` monotonicity: `lake build
  TamaUniV2.Proof.UniswapV2FactoryProof`.
- 2026-05-17 06:00 PDT: full verification passes for concrete factory
  `allPairsLength` monotonicity: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 06:01 PDT: refreshed `docs/spec-coverage.md` to include the new
  pure LP share-bookkeeping finite-history invariants and the concrete factory
  `allPairsLength` monotonicity theorem. This is current-guidance maintenance,
  not historical-log rewriting.
- 2026-05-17 06:04 PDT: trying the swap insufficient-liquidity exact revert
  again, but with the narrower ordered-prefix shape: lock already passed,
  nonzero-output guard is stated as its exact boolean success fact, and the
  liquidity guard is stated as its exact boolean failure fact. If this expands
  past the guard into the later swap body, back it out and do not force it.
- 2026-05-17 06:06 PDT: backed out the swap insufficient-liquidity exact Lean
  obligation again. Even with exact boolean prefix facts, simplification reduced
  past the liquidity guard into the later transfer/callback/K/oracle body and
  hit Lean kernel deep recursion. Do not retry this as a direct public
  entrypoint proof. It needs a real proof-local ordered-prefix adapter or a
  Verity proof tactic that can stop at the failing `require`.
- 2026-05-17 06:07 PDT: selected the next Tamago-style invariant slice:
  reserve surplus. The plan is to add ghost-only surplus helpers and a
  no-donation finite-path predicate, then expose reader-facing specs proving
  donations increase unaccounted reserve surplus exactly while histories with
  no donation cannot create new surplus. This strengthens the no-profit story
  without adding contract helpers, new trust assumptions, or aggregate
  executable summaries.
- 2026-05-17 06:12 PDT: implemented and focused-verified the reserve-surplus
  invariant slice. Added `PairWorldSurplus0/1`, `PairWorldPathNoDonation`,
  public Pair specs for exact donation surplus and no-donation surplus
  monotonicity, proof markers, and manifest entries. `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passes. Next step is full verification,
  docs refresh, and commit.
- 2026-05-17 06:15 PDT: full verification passes for the reserve-surplus
  invariant slice: `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The Foundry
  signature-cache warning remains sandbox-only.
- 2026-05-17 06:18 PDT: continuing from the verified surplus slice into the
  actual-token-balance no-profit story. Next target is a reader-facing theorem
  saying same-LP-supply histories can reduce token-balance spot value only by
  at most the surplus that already existed above cached reserves at the start.
  This avoids a dummy wallet ledger and explains the `skim` exception
  precisely.
- 2026-05-17 06:21 PDT: focused Pair proof build passes for the
  surplus-bounded actual-token-balance theorem and its no-mint/no-burn
  corollary: `lake build TamaUniV2.Proof.UniswapV2PairProof`.
- 2026-05-17 06:24 PDT: full verification passes for the surplus-bounded
  actual-token-balance theorem: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). The theorem says same-LP-supply histories can reduce actual
  token-balance spot value by at most the surplus already above cached reserves
  at the start; no-mint/no-burn histories inherit that bound automatically.
- 2026-05-17 06:25 PDT: continuing with the newer essay-style spec standard.
  Next proof slice is a reader-facing zero-initial-surplus corollary of the
  surplus-bounded actual-balance theorem: if a reachable nonempty pool starts
  with no donated surplus, then same-LP-supply finite histories cannot reduce
  the pair's actual token-balance value at the initial spot price. This is a
  narrative-strengthening theorem over the existing closed-world model, not a
  contract helper, API parity claim, or new trust surface.
- 2026-05-17 06:28 PDT: implemented and verified the zero-surplus
  actual-balance no-extraction corollaries. Added one same-LP-supply theorem
  and one no-mint/no-burn theorem, both proved from the surplus-bounded theorem
  by showing the starting surplus value is zero. Full verification passed:
  focused Pair proof build, `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The usual
  Foundry signature-cache warning remains sandbox-only.
- 2026-05-17 06:29 PDT: starting the next surplus-isolation corollary. Target:
  from a reachable state with zero token-side reserve surplus, every finite
  modeled history with no direct donation step preserves zero surplus exactly.
  This is the concise invariant form of "ordinary pair mechanics cannot create
  skimmable donated balance"; it should be proved from the existing
  no-donation surplus monotonicity theorem.
- 2026-05-17 06:31 PDT: implemented and verified the no-donation
  zero-surplus preservation theorem. Full verification passed again: focused
  Pair proof build, `tama check`, whole `lake build TamaUniV2.Proof`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). The theorem
  says a clean reachable state remains clean across any finite successful
  modeled history that contains no direct donation step.
- 2026-05-17 06:32 PDT: starting a readability corollary over the same
  surplus layer. Target: from a reachable clean start, no-donation histories
  end balanced in the direct sense that modeled token balances equal cached
  reserves on both sides. This should follow from zero-surplus preservation plus
  the existing reserve-backing/good-state invariant.
- 2026-05-17 06:34 PDT: implemented and verified the clean-start endpoint
  balance corollary. It proves that a reachable zero-surplus start followed by
  any finite no-donation history ends with `balance0 = reserve0` and
  `balance1 = reserve1`. Full verification passed: focused Pair proof build,
  `tama check`, whole `lake build TamaUniV2.Proof`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues).
- 2026-05-17 06:35 PDT: attempting a narrow executable bridge for `sync`.
  Public statement should stay short: with the lock open and observed token
  balances inside uint112 bounds, a successful real `sync` run stores those
  balances as reserves, records the current uint32 timestamp, emits `Sync`, and
  restores the lock. If direct unfolding blows up again, back out the public
  obligation and record that this still needs a proof-local adapter.
- 2026-05-17 06:37 PDT: backed out the direct public `sync` success bridge.
  Focused Pair proof failed with the known kernel deep-recursion pattern:
  simplification expanded into the shared reserve-update/oracle tail instead of
  stopping at the postcondition. Do not reintroduce this as a direct
  whole-entrypoint proof; it needs a proof-local reserve-update suffix adapter
  first.
## 2026-05-17

- 2026-05-17 06:43 PDT: resumed after context compaction with the current
  standard front and center: Pair and Factory spec files should read as
  assurance essays whose short Lean propositions compose into correctness,
  completeness, and security claims. Current slice is a comments-and-active-docs
  cleanup only: clarify the narrative flow, avoid checklist/API-parity framing,
  and preserve all contract source, ABI, theorem statements, trust surfaces, and
  proof obligations.
- 2026-05-17 06:47 PDT: completed the reader-facing narrative cleanup. Pair
  spec now opens by defining correctness/security/completeness as the reading
  frame, clarifies that executable bridge specs are one-step simulation links
  rather than aggregate behavior summaries, and describes oracle formulas as
  contract-level reserve-update rules factored outside the source. Factory spec
  now opens with the narrower factory assurance job: unique unordered markets,
  symmetric lookup, append-only enumeration, and failure atomicity. Active
  coverage docs now require spec files to be readable before opening proofs.
  Verification passed: `lake build TamaUniV2.Spec`, `tama check`, and
  `lake build TamaUniV2.Proof`.
- 2026-05-17 06:47 PDT: started the next proof-coverage slice on Pair
  initialization rather than a reserve-update path. Added the public spec
  `pair_initialize_run_success_sets_tokens`: if the factory calls a fresh pair,
  the actual `initialize` run succeeds and records `token0`/`token1`. This is a
  small executable lifecycle fact paired with the existing non-factory and
  already-initialized exact reverts; it does not touch contract source or add
  helper APIs.
- 2026-05-17 06:49 PDT: initialization success slice verified. Full loop
  passed: focused Pair proof build, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The only runtime warning remains the
  known Foundry signature-cache permission warning.
- 2026-05-17 06:51 PDT: briefly retried the direct public swap
  insufficient-liquidity guard after proving initialization. It failed in the
  known way: simplification passed the failing guard and expanded transfer,
  callback, K, and oracle tails, ending in kernel deep recursion. Backed out the
  public spec/proof immediately. Do not retry this as a direct whole-swap proof;
  it still needs a proof-local prefix adapter that stops at the ordered guard.
- 2026-05-17 06:54 PDT: added a second small initialization success property:
  `pair_initialize_run_success_keeps_amm_accounting`. It states that successful
  identity setup does not change reserves, total LP supply, LP balance/allowance
  maps, or events. This keeps initialization out of the AMM economic transition
  story and complements the token-write success theorem.
- 2026-05-17 06:56 PDT: initialization frame slice verified. Full loop
  passed: focused Pair proof build, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The known Foundry signature-cache
  permission warning remains non-blocking.
- 2026-05-17 06:58 PDT: added a factory view-boundary spec
  `factory_allPairs_run_success_in_bounds`: in-bounds `allPairs(index)` returns
  the decoded stored pair entry and leaves factory state unchanged. This pairs
  with the existing out-of-bounds exact revert, so the router-visible pair array
  boundary is now stated as exact success plus exact failure.
- 2026-05-17 07:00 PDT: factory view-boundary slice verified. Full loop
  passed: focused Factory proof build, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The known Foundry signature-cache
  permission warning remains non-blocking.
- 2026-05-17 07:01 PDT: added the remaining exact factory view success/frame
  specs: `factory_getPair_run_success_frames_state` and
  `factory_allPairsLength_run_success_frames_state`. Together with the exact
  in-bounds/out-of-bounds `allPairs` facts, the Factory view section now states
  all router-facing reads as exact state-framing runs.
- 2026-05-17 07:02 PDT: factory view-frame completion verified. Full loop
  passed: focused Factory proof build, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues). The known Foundry signature-cache
  permission warning remains non-blocking.
- 2026-05-17 07:04 PDT: added `pair_getReserves_run_success_frames_state`.
  This keeps the Pair view work focused on the security-relevant reserve
  surface: the actual `getReserves` run returns cached reserve0/reserve1 and the
  last timestamp, with pair state unchanged.
- 2026-05-17 07:06 PDT: Pair `getReserves` view-frame slice verified. Full
  loop passed: focused Pair proof build, `tama check`, `tama build`, `tama
  test` (26/26), and `tama audit` (0 issues). The known Foundry signature-cache
  permission warning remains non-blocking.
- 2026-05-17 07:15 PDT: resumed with the essay-style spec standard active.
  Found one uncommitted private swap insufficient-liquidity prefix adapter. A
  focused Pair proof build still hit Lean kernel deep recursion before any
  public obligation was added, so I removed the private adapter rather than
  leaving broken proof plumbing in the tree. Next work should stay on short,
  reader-facing specs/proofs that build cleanly, or on a genuinely factored
  prefix adapter outside the public spec layer.
- 2026-05-17 07:18 PDT: started a tractable Pair view-boundary slice. Added
  short, commented run-level specs for the observable Pair reads other than
  `getReserves`: LP supply, LP balances, allowances, factory, token identities,
  `MINIMUM_LIQUIDITY`, price accumulators, decimals, and fee-off `kLast`. These
  are framed as observable-state correctness facts, not API-parity obligations.
- 2026-05-17 07:21 PDT: Pair view-boundary slice verified. Focused Pair proof
  build, `tama check`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues) all passed. The known Foundry signature-cache permission warning
  remains non-blocking.
- 2026-05-17 07:25 PDT: started the next exact guard slice for `burn`. Added a
  short public spec for the early `INSUFFICIENT_LIQUIDITY_BURNED` branch: with
  the lock open, if the pair holds no LP liquidity or total LP supply is zero,
  the actual burn run must revert before token transfers. This targets the
  ordered revert matrix without touching contract source.
- 2026-05-17 07:29 PDT: backed out the attempted public burn
  `INSUFFICIENT_LIQUIDITY_BURNED` obligation. The statement was right, but the
  direct proof still failed to stop at the guard and expanded into burn overflow,
  transfer, and oracle suffixes. Do not reintroduce this as a whole-entrypoint
  simp proof; it needs a real prefix adapter first.
- 2026-05-17 07:33 PDT: started a closed-world surplus reconciliation slice
  instead of another fragile exact-run branch. Added short specs/proofs in
  progress for the reader-facing consequence that both `skim` and `sync` leave
  no modeled surplus above cached reserves at the endpoint.
- 2026-05-17 07:37 PDT: surplus reconciliation slice verified. Added and
  proved `pair_closed_world_skim_eliminates_surplus` and
  `pair_closed_world_sync_eliminates_surplus`. Full loop passed: focused Pair
  proof build, `tama check`, `tama build`, `tama test` (26/26), and
  `tama audit` (0 issues). The known Foundry signature-cache permission warning
  remains non-blocking.
- 2026-05-17 07:39 PDT: started the companion sync/K refinement. The new spec
  states that from a backed zero-surplus state, a closed-world sync preserves
  cached reserve product exactly; any sync K increase must therefore come from
  pre-existing token balances above cached reserves.
- 2026-05-17 07:42 PDT: sync/K zero-surplus refinement verified. Added and
  proved `pair_closed_world_sync_preserves_k_without_surplus`, updated coverage
  notes and manifest text, and ran the full loop: focused Pair proof build,
  `tama check`, `tama build`, `tama test` (26/26), and `tama audit` (0 issues).
- 2026-05-17 07:47 PDT: started the next bridge slice. Target is a narrow
  successful-`sync` executable fact: from an open lock and in-bound observed
  token balances, the real public `sync` call caches those balances as reserves
  and restores the reentrancy lock. This is an executable-to-invariant bridge,
  not a no-elapsed helper and not a contract-source change.
- 2026-05-17 07:54 PDT: backed out the public successful-`sync` bridge attempt.
  Even after splitting same-timestamp/active/inactive oracle branches, the proof
  term still hit Lean kernel recursion while expanding the public entrypoint.
  Do not reintroduce this as another whole-entrypoint proof; it needs a smaller
  proof-local adapter before becoming a public obligation.
- 2026-05-17 07:57 PDT: switched to a closed-world reserve-change classifier.
  The new reader-facing spec states that cached reserves can change only on
  mint, burn, swap, or sync; LP bookkeeping, donations, and skim cannot secretly
  rewrite router-visible reserves.
- 2026-05-17 08:01 PDT: reserve-change classifier verified. Focused Pair proof
  build, `tama check`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues) all passed. The known sandbox cache/signature warnings remain
  non-blocking.
- 2026-05-17 08:03 PDT: started the finite-history reserve-isolation follow-up.
  Plan is to add a ghost-only no-reserve-update path outside the spec namespace
  and expose a short reader-facing theorem: histories with no mint, burn, swap,
  or sync preserve cached reserves exactly.
- 2026-05-17 08:06 PDT: finite-history reserve isolation focused proof passed.
  Added `PairWorldPathNoReserveUpdate` as ghost-model support outside the public
  spec namespace and proved
  `pair_closed_world_no_reserve_update_path_preserves_reserves`.
- 2026-05-17 08:08 PDT: finite-history reserve isolation verified end to end.
  Focused Pair proof build, `tama check`, `tama build`, `tama test` (26/26),
  and `tama audit` (0 issues) all passed. The known sandbox cache/signature
  warnings remain non-blocking.
- 2026-05-17 08:10 PDT: started the reserve-isolation economic corollary. The
  next spec should say that histories with no reserve-update action preserve
  cached K and reserve-denominated spot value, while deliberately not claiming
  actual token-balance value preservation because donations and skim can affect
  surplus.
- 2026-05-17 08:12 PDT: focused proof passed for the reserve-isolation economic
  corollary. Added and proved
  `pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value`.
- 2026-05-17 08:13 PDT: reserve-isolation economic corollary verified end to
  end. Focused Pair proof build, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues) all passed. The known sandbox
  cache/signature warnings remain non-blocking.
- 2026-05-17 08:14 PDT: started the next ordered-guard slice. Target is mint's
  post-lock backing/amount guards: after balance overflow checks pass, a
  public `mint` run must exactly revert with `UniswapV2: INSUFFICIENT_AMOUNT`
  when observed token balances are below cached reserves or when either inferred
  deposit amount is zero.
- 2026-05-17 08:22 PDT: continuing the mint ordered-guard slice after
  compaction. The first focused build failed because the proof did not stop at
  the intended prefix; tightened the proof-local boolean guard lemmas and the
  lock-gate rewrite before making one more focused build attempt. If this still
  expands into the mint suffix, back it out instead of normalizing a huge
  aggregate proof.
- 2026-05-17 08:27 PDT: backed out the attempted public mint
  `INSUFFICIENT_AMOUNT` ordered-guard obligations. The second focused build
  again entered the large mint suffix, so the right next bridge work remains a
  proof-local ordered-prefix adapter rather than more whole-entrypoint
  normalization.
- 2026-05-17 08:33 PDT: started a smaller closed-world first-mint security
  slice. Instead of another executable guard, add a reader-facing theorem that
  the first mint leaves a strictly positive permanently locked LP share, so the
  first liquidity provider cannot own the entire total supply.
- 2026-05-17 08:34 PDT: focused Pair proof passed for the first-mint locked
  share theorem. Added `pair_closed_world_first_mint_keeps_locked_share`, which
  packages the minimum-liquidity lock as the reader-facing anti-initial-owner
  dominance consequence.
- 2026-05-17 08:34 PDT: first-mint locked-share slice verified end to end:
  focused Pair proof build, `tama check`, `tama build`, `tama test` (26/26),
  and `tama audit` (0 issues) all passed. The known sandbox cache/signature
  warnings remain non-blocking.
- 2026-05-17 08:35 PDT: started a sync surplus/K consequence slice. The target
  theorem states the converse of the zero-surplus sync fact: if a good
  closed-world `sync` increases cached K, that increase must come from
  pre-existing surplus over cached reserves.
- 2026-05-17 08:36 PDT: focused Pair proof passed for the sync surplus/K
  converse. Added `pair_closed_world_sync_k_increase_requires_surplus`, keeping
  sync's role explicit: it can account surplus, but it cannot manufacture
  cached liquidity value.
- 2026-05-17 08:38 PDT: sync surplus/K converse verified end to end: focused
  Pair proof build, `tama check`, `tama build`, `tama test` (26/26), and
  `tama audit` (0 issues) all passed. The known sandbox cache/signature
  warnings remain non-blocking.
- 2026-05-17 08:40 PDT: started the companion skim surplus-value slice. The
  target theorem states that closed-world `skim` removes exactly the
  pre-existing surplus value at the initial spot price, while accounted reserve
  value remains untouched.
- 2026-05-17 08:42 PDT: focused Pair proof passed for the skim exact
  surplus-value theorem. Added
  `pair_closed_world_skim_removes_exact_surplus_value` as the token-balance
  value companion to the existing reserve/K framing facts.
- 2026-05-17 08:43 PDT: skim exact surplus-value slice verified end to end:
  focused Pair proof build, `tama check`, `tama build`, `tama test` (26/26),
  and `tama audit` (0 issues) all passed. The known sandbox cache/signature
  warnings remain non-blocking.
- 2026-05-17 08:47 PDT: started the balanced-skim no-op slice. The target
  theorem states the direct reader-facing security fact: if a good pool has no
  surplus above cached reserves, `skim` leaves token balances, reserves, total
  LP supply, and locked liquidity unchanged.
- 2026-05-17 08:48 PDT: focused Pair proof passed for the balanced-skim no-op
  theorem. Added `pair_closed_world_skim_preserves_balanced_pool` as the clean
  no-surplus companion to the surplus-value theorem.
- 2026-05-17 08:50 PDT: balanced-skim no-op slice verified end to end:
  focused Pair proof build, `tama check`, `tama build`, `tama test` (26/26),
  and `tama audit` (0 issues) all passed. The known sandbox cache/signature
  warnings remain non-blocking.
- 2026-05-17 08:52 PDT: started the concrete `sync` reserve-update bridge
  slice. The target is a set of short reader-facing facts, not a giant
  function summary: successful `sync` records observed balances as reserves,
  records the uint32 timestamp, restores the lock, and emits the matching
  `Sync` event.
- 2026-05-17 08:56 PDT: backed out the attempted concrete `sync` success
  bridge before committing. Even split into short facts, proving actual
  successful `sync` still forced the whole oracle/update suffix into a kernel
  recursion blowup. Keep this as adapter work: first factor proof-local
  reserve-update suffix lemmas, then expose the short public obligations.
- 2026-05-17 09:01 PDT: started the balanced-sync no-op slice. This is the
  closed-world counterpart to the balanced-skim theorem: when a good pool has
  no surplus above cached reserves, `sync` should preserve token balances,
  cached reserves, total LP supply, and locked liquidity exactly.
- 2026-05-17 09:02 PDT: focused Pair proof passed for the balanced-sync no-op
  theorem. Added `pair_closed_world_sync_preserves_balanced_pool`, keeping the
  surplus/reconciliation section symmetric: skim and sync are both no-ops on a
  balanced pool.
- 2026-05-17 09:04 PDT: balanced-sync no-op slice verified end to end:
  focused Pair proof build, `tama check`, `tama build`, `tama test` (26/26),
  and `tama audit` (0 issues) all passed. The known sandbox cache/signature
  warnings remain non-blocking.
- 2026-05-17 09:05 PDT: started the reserve-management fixed-point slice. The
  target is an overall-behavior theorem: for the two reserve-management
  actions, `skim` and `sync`, a good balanced pool is a fixed point on token
  balances, cached reserves, LP supply, and locked liquidity.
- 2026-05-17 09:06 PDT: focused Pair proof passed for the reserve-management
  fixed-point theorem. Added
  `pair_closed_world_balanced_reserve_management_preserves_pool`, composing
  the skim and sync balanced no-op facts into one action-family invariant.
- 2026-05-17 09:08 PDT: reserve-management fixed-point slice verified end to
  end: focused Pair proof build, `tama check`, `tama build`, `tama test`
  (26/26), and `tama audit` (0 issues) all passed. The known sandbox
  cache/signature warnings remain non-blocking.
- 2026-05-17 09:12 PDT: started the finite-history reserve-management
  fixed-point slice. The helper will live in the ghost model, outside
  `verity/spec`, and the public theorem will state that any finite path made
  only of `skim` and `sync` preserves a good balanced pool exactly.
- 2026-05-17 09:14 PDT: focused Pair proof passed for the finite-history
  reserve-management fixed-point theorem. Added the ghost-only
  `PairWorldPathReserveManagement` helper and proved the public trace-level
  invariant by induction over skim/sync paths.
- 2026-05-17 09:19 PDT: finite-history reserve-management fixed-point slice
  verified end to end: focused Pair proof build, `tama check`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues) all passed. The known
  sandbox cache/signature warnings remain non-blocking.
- 2026-05-17 09:20 PDT: started the balanced maintenance trace invariant. The
  target path family combines LP share bookkeeping with reserve management
  (`approve`, `transfer`, `transferFrom`, `skim`, and `sync`) and proves that
  any finite path of those passive actions preserves a good balanced pool.
- 2026-05-17 09:24 PDT: focused Pair proof passed for the balanced
  passive-maintenance path theorem. Added the ghost-only
  `PairWorldPathMaintenance` helper and proved
  `pair_closed_world_balanced_maintenance_path_preserves_pool`, keeping the
  public spec as a short finite-history invariant while the induction lives in
  the proof layer.
- 2026-05-17 09:26 PDT: balanced passive-maintenance slice verified end to
  end: whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues) all passed. The known
  unused-variable and sandbox cache/signature warnings remain non-blocking.
- 2026-05-17 09:28 PDT: started the executable same-timestamp `sync` bridge.
  This is the smallest real reserve-update path: under the lock/bounds guards
  and with no 32-bit timestamp advance, successful `sync` should record
  observed balances as reserves, leave TWAP cumulatives unchanged, restore the
  lock, and emit `Sync`.
- 2026-05-17 09:37 PDT: backed out the direct same-timestamp `sync` bridge
  attempt before committing code. Even after reshaping the statements into
  success-conditional facts and splitting post-state fields, directly unfolding
  `sync` still made Lean expand the full reserve-update/event suffix and hit
  kernel recursion. Do not repeat direct `sync` unfolding; the next executable
  reserve-update bridge needs a proof-local adapter for the shared suffix first.
- 2026-05-17 09:38 PDT: started the `swap` insufficient-liquidity ordered
  prefix proof instead. This guard occurs before token transfers, callbacks,
  and reserve updates, so it should be provable as an exact run-result revert
  without unfolding the difficult suffix.
- 2026-05-17 09:48 PDT: focused build reproduced the `swap` proof failure.
  The semantic false-liquidity fact was correct, but it did not match the raw
  guard shape after `swap` writes `unlocked = 0`. Trying a proof-local raw guard
  bridge; contract code and public API remain untouched.
- 2026-05-17 09:58 PDT: backing out the uncommitted direct `swap`
  insufficient-liquidity exact-run proof. Multiple local rewrites proved the
  guard false, but Lean still expanded the transfer/callback/K-check suffix
  before short-circuiting the generated `require`. This should be revisited via
  a reusable proof adapter for failed post-lock `require` branches, not by
  repeatedly unfolding the full `swap` body.
- 2026-05-17 10:01 PDT: started a small reader-facing consequence of the
  balanced maintenance invariant. The new public spec will state that a
  clean balanced pool undergoing only LP bookkeeping plus `skim`/`sync`
  preserves actual token-balance value exactly at the initial spot price.
- 2026-05-17 10:03 PDT: focused Pair proof build passed for
  `pair_closed_world_balanced_maintenance_path_preserves_token_balance_value`.
  The proof reuses the passive-maintenance fixed-point theorem and exposes the
  economic no-extraction reading as its own short public obligation.
- 2026-05-17 10:04 PDT: full verification passed for the passive-maintenance
  token-balance-value slice: whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). Known
  unused-variable and sandbox cache/signature warnings remain non-blocking.
- 2026-05-17 10:05 PDT: started the sibling passive-maintenance zero-surplus
  invariant. This will state directly that LP bookkeeping plus `skim`/`sync`
  cannot create surplus from a clean balanced pool.
- 2026-05-17 10:07 PDT: focused Pair proof build passed for
  `pair_closed_world_balanced_maintenance_path_preserves_zero_surplus` after
  using the folded surplus hypotheses directly.
- 2026-05-17 10:09 PDT: full verification passed for the passive-maintenance
  zero-surplus slice: whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). Known
  warnings remain the same unused-variable and sandbox cache/signature noise.
- 2026-05-17 10:11 PDT: started the passive-maintenance cached-K fixed-point
  slice. This is a reader-facing consequence of the balanced maintenance
  theorem: if the path only performs LP bookkeeping plus `skim`/`sync` from a
  clean balanced pool, the cached reserve product should be unchanged.
- 2026-05-17 10:14 PDT: passive-maintenance cached-K slice verified end to
  end: focused Pair proof build, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues) all passed. Known warnings remain limited to existing
  unused-variable and sandbox cache/signature messages.
- 2026-05-17 10:17 PDT: started a Tamago-style burn asset-movement slice. The
  target is a short public spec saying successful `burn` sends the computed
  pro-rata token0 and token1 amounts from the pair to the recipient via the
  ERC20 transfer trace, complementing the existing skim trace.
- 2026-05-17 10:25 PDT: backed out the unverified direct burn asset-movement
  obligation before committing. The statement is still valuable, but direct
  full-entrypoint unfolding stalls in the burn reserve-update/event suffix. The
  next attempt should factor a proof-local transfer-prefix adapter first, then
  expose the short public trace property.
- 2026-05-17 10:27 PDT: started the burn transfer-prefix adapter route. The
  immediate target is private proof infrastructure showing that, after burn's
  transfer point and post-transfer bounds check, the reserve-update/event suffix
  preserves the earlier ERC20 transfer trace events.
- 2026-05-17 10:35 PDT: focused Pair proof build failed for the uncommitted
  burn transfer-prefix adapter. Removed that unverified helper from the proof
  file rather than leaving a broken proof state, and rewrote current-facing
  spec/plan/audit text away from the confusing "fixed point" and "passive
  maintenance" wording. The proved property should be described plainly:
  LP bookkeeping plus `skim`/`sync` cannot change a clean balanced pool's
  balances, cached reserves, LP supply, locked liquidity, cached K, zero-surplus
  status, or spot-priced token-balance value.
- 2026-05-17 10:43 PDT: added and focused-built the Factory concrete
  same-length no-hidden-change theorem. New public obligation:
  if a finite concrete history of successful `createPair` runs leaves
  `allPairsLength` storage unchanged, the reconstructed factory world is
  unchanged. Focused `lake build TamaUniV2.Proof.UniswapV2FactoryProof` passed.
- 2026-05-17 10:45 PDT: full verification passed for the Factory same-length
  concrete-history slice and wording cleanup: whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), and
  `tama audit` (0 issues). Known warnings remain unused-variable lints plus
  sandbox cache/signature write warnings.
- 2026-05-17 10:49 PDT: added Pair executable LP-bookkeeping storage-frame
  specs/proofs. New obligations state that actual `approve`, `transfer`, and
  `transferFrom` runs cannot change scalar AMM storage: reserves, cumulative
  prices, total supply, token identities, or lock state. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 10:51 PDT: full verification passed for the Pair
  LP-bookkeeping storage-frame slice: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). Known warnings remain unused-variable lints plus sandbox
  cache/signature write warnings.
- 2026-05-17 10:54 PDT: added Pair executable LP-bookkeeping token-world frame
  specs/proofs. New obligations state that actual `approve`, `transfer`, and
  `transferFrom` runs leave pair-local token0/token1 balances unchanged when
  replayed through the pair-local ERC20 transfer trace model. Focused
  `lake build TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 10:56 PDT: full verification passed for the Pair
  LP-bookkeeping token-world frame slice: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). Known warnings remain unused-variable lints plus sandbox
  cache/signature write warnings.
- 2026-05-17 11:04 PDT: added the Pair executable `skim` token-balance bridge.
  New public obligation states that successful real `skim`, when replayed
  through the pair-local ERC20 transfer trace model, moves exactly the
  token0/token1 surplus above cached reserves from the pair to the recipient.
  Also corrected current-facing wording to avoid invented proof jargon; use
  plain terms such as token-balance effects, reserve accounting, and
  no-extraction properties.
- 2026-05-17 11:07 PDT: full verification passed for the Pair `skim`
  token-balance bridge slice: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), and `tama audit`
  (0 issues). Known warnings remain unused-variable lints plus sandbox
  cache/signature write warnings.
- 2026-05-17 11:14 PDT: attempted a direct executable `sync` token-balance
  frame proof, then backed it out cleanly after focused Pair proof hit Lean
  kernel recursion in the full oracle-update tail. Do not retry by unfolding
  all of `sync`; factor a small event-trace adapter first, or choose a smaller
  reader-facing obligation.
- 2026-05-17 11:16 PDT: added and focused-built the reusable pair-token
  transfer event replay fact. New public obligation states that replaying a
  recorded pair-local safe-transfer event moves exactly the recorded token
  amount between the recorded accounts in the ghost token-balance world.
- 2026-05-17 11:18 PDT: full verification passed for the pair-token transfer
  event replay slice: whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), and `tama audit` (0 issues). Known
  warnings remain unused-variable lints plus sandbox cache/signature write
  warnings.
- 2026-05-17 11:23 PDT: attempted exact Lean obligations for the `swap`
  insufficient-liquidity prefix, then backed them out after focused Pair proof
  still expanded into the full transfer/callback/K/oracle tail and hit Lean
  kernel recursion. Do not retry direct full-entrypoint unfolding here; add a
  factored prefix adapter first if this revert is promoted to public Lean.
- 2026-05-17 11:25 PDT: renamed current-facing ghost/spec/proof identifiers
  that used vague wording. `skim`/`sync` histories are now named directly, and
  LP-bookkeeping plus `skim`/`sync` histories are named directly. Active docs
  and manifest text no longer use the rejected phrasing; old occurrences remain
  only in historical log entries.
- 2026-05-17 11:30 PDT: full verification passed for the plain-language
  naming cleanup: whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`. Known warnings remain unused-variable lints plus sandbox
  cache/signature write warnings.
- 2026-05-17 11:38 PDT: attempted a direct exact Lean obligation for the
  `swap` invalid-recipient guard, then backed it out after focused Pair proof
  again unfolded into the later transfer/callback/K tail and hit Lean kernel
  recursion. Do not retry these later `swap` guards by direct full-entrypoint
  simplification; first build a small proof-local prefix adapter or keep the
  existing Foundry exact-revert coverage until that adapter exists.
- 2026-05-17 11:41 PDT: added and focused-built the Pair closed-world
  reachability-closure invariant. New public obligation states that if a
  PairWorld state is reachable, appending any finite successful modeled path
  produces another reachable state. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 11:42 PDT: full verification passed for the Pair
  reachability-closure slice: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit`
  (0 issues), and `git diff --check`. Known warnings remain unused-variable
  lints plus sandbox cache/signature write warnings.
- 2026-05-17 11:45 PDT: added and focused-built the Factory closed-world
  reachability-closure invariant, and rewrote current-facing Factory wording
  away from "executable success" to "concrete `createPair` specs." Focused
  `lake build TamaUniV2.Proof.UniswapV2FactoryProof` passed.
- 2026-05-17 11:46 PDT: full verification passed for the Factory
  reachability-closure slice: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit`
  (0 issues), and `git diff --check`. Known warnings remain unused-variable
  lints plus sandbox cache/signature write warnings.
- 2026-05-17 11:50 PDT: added and focused-built the concrete Factory reachable
  lookup validity theorem. It composes storage reconstruction with the
  closed-world reachable lookup invariant, proving reconstructed lookups decode
  to nonzero pairs for distinct nonzero token addresses. Focused `lake build
  TamaUniV2.Proof.UniswapV2FactoryProof` passed.
- 2026-05-17 11:51 PDT: full verification passed for the concrete Factory
  reachable lookup validity slice: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit`
  (0 issues), and `git diff --check`. Known warnings remain unused-variable
  lints plus sandbox cache/signature write warnings.
- 2026-05-17 11:55 PDT: added and focused-built the finite concrete Factory
  endpoint lookup validity theorem. If real successful `createPair` calls move
  reconstructed storage from a reachable factory world to a later world, every
  endpoint lookup in that later world decodes to a nonzero pair for distinct
  nonzero tokens. Focused `lake build TamaUniV2.Proof.UniswapV2FactoryProof`
  passed.
- 2026-05-17 11:58 PDT: full verification passed for the finite concrete
  Factory endpoint lookup validity slice: `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`. Known warnings remain unused-variable lints plus
  sandbox cache/signature write warnings.
- 2026-05-17 12:17 PDT: attempted to add public `sync` success/storage/oracle
  bridge obligations directly over `(sync).run s`. The proof again expanded the
  oracle/event suffix and hit Lean kernel recursion, so the obligations were
  backed out rather than left half-proved. Focused Pair proof is back to green.
  Next `sync`/mint/burn/swap executable work should first introduce small
  proof-local adapters for the shared reserve-update suffix, then expose only
  the short reader-facing property that the adapter can prove.
- 2026-05-17 12:20 PDT: added and focused-built
  `pair_closed_world_swap_no_spot_value_extraction`. The spec says that from a
  good live pool with a defined starting spot price, a valid closed-world swap
  cannot leave the pool worth less at that starting spot price. Proof reuses the
  existing finite-history no-profit theorem via a one-step swap path; focused
  `lake build TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 12:22 PDT: cleaned active spec/plan/audit wording after user
  feedback about confusing category names. The active docs and Tama labels now
  use plain Uniswap terms and `UQ112x112 encoded price`; the old wording remains
  only in historical append-only progress entries.
- 2026-05-17 12:26 PDT: full verification passed for the swap no-extraction
  theorem and wording cleanup slice: `lake build TamaUniV2.Proof`, `tama
  check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`. Known warnings remain unused-variable lints plus sandbox
  cache/signature write warnings.
- 2026-05-17 12:31 PDT: added the reader-facing reachable one-swap
  no-extraction theorem. It removes the manual good-state and positive-reserve
  premises from the public swap economic statement by deriving them from
  reachability plus positive LP supply.
- 2026-05-17 12:32 PDT: full verification passed for the reachable one-swap
  no-extraction theorem: focused Pair proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`. Known warnings remain unchanged.
- 2026-05-17 12:38 PDT: added the reachable burn no-drain theorem. It states
  directly that a valid burn from a reachable nonempty pool cannot empty either
  token side, deriving the pre-burn token-balance premises from reachability.
- 2026-05-17 12:39 PDT: full verification passed for the reachable burn
  no-drain theorem: focused Pair proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`. Known warnings remain unchanged.
- 2026-05-17 12:47 PDT: cleaned active wording after noticing the shorthand
  "no-drain" had crept into spec comments and Tama labels. Active docs/spec
  text now says the precise property directly: reachable nonempty histories
  keep token balances positive, and reachable burns cannot empty either token
  side. Earlier progress entries remain historical.
- 2026-05-17 12:55 PDT: attempted a direct public Lean proof for the
  post-lock swap insufficient-liquidity revert. Like the earlier burn/sync
  attempts, unfolding the whole public entrypoint after the lock gate expanded
  into later swap logic instead of stopping at the target guard, so the attempt
  was backed out. The next exact post-lock revert work should use a small
  proof-local ordered-prefix adapter before adding public obligations.
- 2026-05-17 12:55 PDT: added and focused-built the two-transfer token trace
  replay theorem. It states that replaying two pair-local safe-transfer events
  for distinct tokens moves exactly each underlying token amount from the pair
  account to the recipient. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 12:59 PDT: full verification passed for the two-transfer token
  trace replay slice: focused Pair proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`. Known warnings remain unused-variable lints plus
  sandbox cache/signature write warnings.
- 2026-05-17 14:05 PDT: after the computer restart, rechecked the worktree and
  resumed from the uncommitted caller no-profit slice. Added and focused-built
  `pair_closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit`.
  The theorem states that, for a reachable zero-surplus same-LP-supply history,
  if caller value plus pair token-balance value is unchanged except for
  redistribution at the initial spot price, then the caller cannot finish with
  more value. Focused `lake build TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 14:07 PDT: full verification passed for the caller no-profit
  consequence slice: focused Pair proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`. Known warnings remain unused-variable lints plus
  sandbox cache/signature write warnings.
- 2026-05-17 14:14 PDT: attempted a direct public `sync` success
  lock-restoration theorem. Even after splitting the real gates and oracle
  branches, Lean hit a kernel deep-recursion limit while unfolding the shared
  reserve-update/event tail. Backed the obligation out and confirmed focused
  `lake build TamaUniV2.Proof.UniswapV2PairProof` is green again. Future
  success-side lock proofs should use a proof-local adapter for the shared
  tail instead of direct whole-entrypoint unfolding.
- 2026-05-17 14:16 PDT: added and focused-built the common no-mint/no-burn
  caller no-profit theorem. It derives the caller-value conclusion from the
  same-supply theorem plus the LP-supply firewall, so callers do not need to
  restate same LP supply for histories with no mint and no burn. Focused `lake
  build TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 14:18 PDT: full verification passed for the common
  no-mint/no-burn caller no-profit theorem: focused Pair proof, whole `lake
  build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26),
  `tama audit` (0 issues), and `git diff --check`. Known warnings remain
  unused-variable lints plus sandbox cache/signature write warnings.
- 2026-05-17 14:20 PDT: resumed after another computer restart. The worktree
  was clean at resume. The next work should not repeat the committed
  no-profit/economic slices; active remaining Pair work is bridge/oracle/revert
  coverage, preferably through small proof-local adapters rather than direct
  whole-entrypoint unfolding.
- 2026-05-17 14:25 PDT: added and focused-built passive reconciliation value
  facts. The new specs say `sync` preserves actual token balances and every
  spot-price valuation of those balances, `skim` cannot increase token-balance
  value at the starting spot price, and either `skim` or `sync` cannot increase
  that value. Focused `lake build TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 14:27 PDT: full verification passed for the passive
  reconciliation value slice: `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`. Known warnings remain unused-variable lints plus sandbox
  cache/signature write warnings.
- 2026-05-17 14:30 PDT: added and focused-built the finite-history passive
  reconciliation value theorem. It lifts the one-step `skim`/`sync` value facts
  to any path made only of LP approval/transfer/transferFrom bookkeeping plus
  `skim`/`sync`, proving such histories cannot increase actual token-balance
  value at the starting spot price. Focused `lake build
  TamaUniV2.Proof.UniswapV2PairProof` passed.
- 2026-05-17 14:32 PDT: full verification passed for the finite-history
  passive reconciliation value theorem: `lake build TamaUniV2.Proof`, `tama
  check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`. Known warnings remain unused-variable lints plus sandbox
  cache/signature write warnings.
- 2026-05-17 14:35 PDT: added the reachable-state version of the passive
  finite-history value theorem and ran full verification: `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), `tama
  audit` (0 issues), and `git diff --check`. Known warnings remain unchanged.
- 2026-05-17 14:39 PDT: added and fully verified the shared reserve-write
  theorem. It states that mint, burn, swap, and sync reserve writes set cached
  reserves to the pair's actual token balances. Full verification passed:
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 14:44 PDT: added and fully verified the shared concrete
  reserve-write oracle bridge. Once a mint, burn, swap, or sync transition is
  connected to a concrete state, it exposes both reserve-to-balance writes and
  all three generic TWAP update cases. Full verification passed: `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), `tama
  audit` (0 issues), and `git diff --check`.
- 2026-05-17 14:48 PDT: attempted a direct public Lean proof for swap
  `INVALID_TO` after the output and liquidity guards. The proof again expanded
  into the later transfer/callback/K/oracle tail instead of stopping at the
  target guard, so the obligation was backed out. The next ordered swap revert
  work should first introduce a proof-local prefix adapter that stops at the
  invalid-recipient require.
- 2026-05-17 14:50 PDT: added and focused-built the narrow public `sync`
  success-to-oracle bridge. The theorem composes the existing successful-run
  transition bridge with the shared concrete reserve-write theorem, so a real
  successful `sync` run now yields reserve-to-balance writes plus all three
  generic TWAP arithmetic cases without re-unfolding the full entrypoint.
- 2026-05-17 15:00 PDT: extended the success-to-oracle bridge pattern to first
  mint, subsequent mint, burn, and swap. The first draft incorrectly treated
  expected-bridge predicates as completed steps; focused build caught it. The
  final specs now state the concrete arithmetic premises explicitly, then prove
  reserve-to-balance writes plus the generic TWAP cases by composing existing
  transition proofs with the shared reserve-write theorem.
- 2026-05-17 15:03 PDT: cleaned up stale remaining-work wording after the
  oracle bridge commits. The active docs now mark the TWAP/oracle spec item
  complete; remaining executable bridge work is about deriving more concrete
  premises from successful runs, not reconnecting reserve writers to the shared
  oracle rule again.
- 2026-05-17 15:09 PDT: attempted a `sync` success-implies-uint112-bounds
  premise-derivation theorem using existing exact overflow reverts. Even after
  changing the success premise to an existential post-state and avoiding
  `simp`, focused Pair proof hit Lean stack overflows in the constructor
  contradiction path. Backed the obligation out. Retried the route with a tiny
  proof-local `ContractResult.revert ≠ ContractResult.success` helper; focused
  Pair proof still hit a stack overflow. Future premise-derivation work should
  use a more structural adapter that avoids composing equality proofs over the
  full `sync.run` term.
- 2026-05-17 15:16 PDT: resumed after computer restart with a clean worktree at
  `317f055`. Re-read the active coverage and invariant-first plan before
  making edits, to avoid repeating already committed no-profit, surplus, and
  oracle-bridge work.
- 2026-05-17 15:22 PDT: attempted a direct executable `sync` success theorem
  for lock restoration. The statement was security-relevant and small, but the
  proof again forced Lean to compare the whole reserve-update success term and
  hit kernel deep recursion even after timestamp-branch case splits. Backed the
  obligation out; future lock-restoration work needs a factored Verity
  adapter, not direct whole-run equality over `sync`.
- 2026-05-17 15:30 PDT: added a compositional caller-facing one-swap no-profit
  spec and proof. It reuses the existing reachable one-swap pool-value theorem:
  if a valid swap only redistributes starting-spot value between the caller and
  the pool, then the caller cannot finish with more value.
- 2026-05-17 15:32 PDT: focused Pair proof build passed for the one-swap
  caller no-profit theorem. Known unused-variable warnings remain unchanged.
- 2026-05-17 15:34 PDT: full verification passed for the one-swap caller
  no-profit theorem: whole `lake build TamaUniV2.Proof`, `tama check`, `tama
  build`, `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`.
  Known warnings remain unused-variable lints plus sandbox cache/signature
  write warnings.
- 2026-05-17 15:27 PDT: continuing after commit `664c4ac` with another
  compositional one-swap theorem. Added the actual-token-balance caller
  no-profit statement for reachable zero-surplus pools; it specializes the
  existing same-supply no-profit theorem using the fact that swaps preserve LP
  supply.
- 2026-05-17 15:30 PDT: full verification passed for the zero-surplus
  one-swap caller token-balance no-profit theorem: focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`. Known warnings
  remain unchanged.
- 2026-05-17 15:31 PDT: resumed after another restart with a clean worktree at
  `c11d579`. Re-read the active spec coverage and invariant-first plan before
  choosing the next slice. The stale seven-gap checklist remains obsolete; the
  current target is concise, reader-facing invariants and narrow bridges that
  connect canonical public entrypoints to those invariants.
- 2026-05-17 15:40 PDT: tried to promote the later swap insufficient-liquidity
  and invalid-recipient guards to exact original-state Lean revert obligations.
  This repeated the known lock-before-later-guard issue: the Verity reduction
  reaches a revert after the lock has been set to 0, so direct exact
  original-state equality is not the right public Lean shape without a factored
  transactional adapter. Backed the attempted specs/proofs out and kept the
  scope to verifiable short obligations.
- 2026-05-17 15:46 PDT: briefly added `pair_swap_run_revert_zero_output` under
  `coverage.proof_only`; `tama build` correctly rejected it because that
  obligation already has a Foundry mirror. Removed the manifest entry. Future
  coverage hygiene must check both Lean markers and `// tama: mirrors=...`
  before adding `coverage.proof_only`.
- 2026-05-17 15:52 PDT: added a short same-LP-supply caller no-profit theorem
  over cached reserve value. It projects the existing pool-value invariant into
  the external-wallet statement: if caller-plus-pool spot value is merely
  redistributed across a same-supply history, the caller cannot finish richer.
  Focused Pair proof build passed; full Tama pipeline still pending.
- 2026-05-17 15:55 PDT: full verification passed for the same-LP-supply
  caller reserve-value no-profit theorem: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`. Known warnings remain unchanged.
- 2026-05-17 15:58 PDT: committed `ed186bc`. Next slice is the common
  operational form of the same caller no-profit theorem: histories with no mint
  and no burn preserve LP supply, so the caller reserve-value no-profit result
  should be available without asking readers to compose the supply firewall
  themselves.
- 2026-05-17 16:02 PDT: added and verified the common no-mint/no-burn caller
  reserve-value no-profit theorem. Full verification passed: focused Pair
  proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama
  test` (26/26), `tama audit` (0 issues), and `git diff --check`. Known
  warnings remain unchanged.
- 2026-05-17 16:05 PDT: committed `0633850`. Next economic slice is the
  non-balanced caller bound: existing specs prove pair actual-token-balance
  value can fall by at most starting surplus, so expose the external-wallet
  consequence that caller profit is bounded by that same surplus.
- 2026-05-17 16:09 PDT: added and verified caller token-balance profit bounds
  for same-LP-supply histories and no-mint/no-burn histories. These state that
  if caller-plus-pair actual token-balance value is merely redistributed, caller
  profit cannot exceed starting surplus above cached reserves. Full verification
  passed: focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and `git diff
  --check`. Known warnings remain unchanged.
- 2026-05-17 15:52 PDT: after clean commit `42d889d`, started a narrow public
  swap economic bridge. The spec does not unfold the whole swap entrypoint; it
  states that once a successful public swap run has been connected to its
  modeled swap step, the existing reachable one-swap caller no-profit theorem
  applies directly.
- 2026-05-17 15:57 PDT: verified the narrow public swap economic bridge after
  restart. Full verification passed: whole `lake build TamaUniV2.Proof`, `tama
  check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`. Known warnings remain unchanged.
- 2026-05-17 15:59 PDT: committed `fe9ec29`. Next slice is a compact
  flash-swap accounting theorem: make explicit that the fee-adjusted K check is
  charged against final post-output, post-repayment balances, so callback
  repayments are included in the swap safety argument without unfolding the
  public swap entrypoint.
- 2026-05-17 16:02 PDT: added and verified the compact flash-swap K theorem.
  The new public spec states that a swap's final post-output/post-repayment
  balances both account for inferred input and are the balances charged by the
  fee-adjusted K inequality. Full verification passed: focused Pair proof,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`. Known warnings
  remain unchanged.
- 2026-05-17 16:04 PDT: committed `3603599`. Next slice is deriving a concrete
  `sync` arithmetic premise from the actual run: use the exact overflow revert
  specs to prove that a successful open-lock `sync` necessarily observed both
  token balances inside the uint112 reserve domain, then bridge that directly
  to the closed-world sync transition.
- 2026-05-17 16:07 PDT: added and verified the stronger executable `sync`
  bridge. Successful open-lock `sync` now implies both observed balances fit
  the uint112 reserve domain, and therefore refines the closed-world sync
  transition without separate bound assumptions. Full verification passed:
  focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama
  build`, `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`.
  Known warnings remain unchanged.
- 2026-05-17 16:08 PDT: committed `b2cb909`. Tightening that same bridge one
  step further: a successful `sync` should imply the lock gate was open, so the
  public bound/refinement bridge should not require an explicit open-lock
  premise.
- 2026-05-17 16:12 PDT: strengthened and verified the `sync` bridge so success
  itself implies the open-lock fact, then derives the uint112 balance bounds and
  closed-world sync transition. Full verification passed: focused Pair proof,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`. Known warnings
  remain unchanged.
- 2026-05-17 16:13 PDT: committed `743afd3`. Next slice extends the same
  premise-derivation pattern to `mint`: successful mutating calls should imply
  the lock gate passed, and successful mint should imply observed balances fit
  the uint112 reserve domain by contradiction with the exact overflow reverts.
- 2026-05-17 16:17 PDT: added and verified success-side lock bridges for
  `mint`, `burn`, `swap`, and `skim`, plus the successful-mint uint112 balance
  bound derived from exact overflow reverts. Full verification passed: focused
  Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`. Known
  warnings remain unchanged.
- 2026-05-17 16:19 PDT: after machine restart, confirmed the worktree was
  clean at `c109297`. Continuing with a small mint bridge slice: successful
  real `mint` runs should refine the first/subsequent closed-world mint
  transitions using the lock and uint112 bounds already derived from success,
  rather than asking readers to supply those premises separately.
- 2026-05-17 16:23 PDT: added first-mint and subsequent-mint successful-run
  bridges that derive lock/bound premises from exact success-side facts and
  then reuse the concise closed-world mint transition specs. Focused Pair proof
  build passed from the repo root; full Tama pipeline is next.
- 2026-05-17 16:24 PDT: full verification passed for the mint successful-run
  bridge slice: whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`. Known
  warnings remain unchanged.
- 2026-05-17 16:25 PDT: committed `af5a269`. Continuing with the mint
  reserve/oracle bridge: the existing oracle facts for first and subsequent
  mint still ask for lock and uint112 premises, so the next slice will derive
  those from successful `mint` runs and leave only the economic arithmetic
  premises visible.
- 2026-05-17 16:28 PDT: added reader-facing first/subsequent mint
  reserve-oracle bridge facts that reuse the new successful-run transition
  bridges. Focused Pair proof build passed; full verification is next.
- 2026-05-17 16:29 PDT: full verification passed for the mint reserve/oracle
  bridge slice: whole `lake build TamaUniV2.Proof`, `tama check`, `tama
  build`, `tama test` (26/26), `tama audit` (0 issues), and `git diff
  --check`. Known warnings remain unchanged.
- 2026-05-17 16:31 PDT: committed `46540e4`. Next target is the ordered swap
  guard matrix, starting with the insufficient-liquidity guard that follows the
  nonzero-output check and precedes token transfers/callbacks.
- 2026-05-17 16:39 PDT: attempted the direct Lean exact-run proof for swap
  insufficient liquidity and backed it out before committing. Even with
  explicit guard booleans, unfolding `swap` at that guard forces Lean to keep
  the full post-guard transfer/callback/K tail in the proof term and hits
  kernel-depth limits. The right next step is a small ordered-prefix adapter
  for post-lock swap guards, not another monolithic unfold.
- 2026-05-17 16:40 PDT: added `sync` successful-run reserve/oracle bridge
  without separate lock or reserve-bound premises, reusing the already-proved
  successful-run sync transition. Focused Pair proof build passed; full
  verification is next.
- 2026-05-17 16:41 PDT: full verification passed for the `sync`
  successful-run reserve/oracle bridge: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`. Known warnings remain unchanged.
- 2026-05-17 16:45 PDT: added successful-run `skim` bridges. Successful
  `skim` now derives reserve backing from the exact under-reserve reverts,
  proves the lock is restored on return, and refines the closed-world skim
  transition without separate lock/balance premises. Focused Pair proof build
  passed; full verification is next.
- 2026-05-17 16:46 PDT: full verification passed for successful-run `skim`
  bridges: whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`. Known
  warnings remain unchanged.
- 2026-05-17 16:50 PDT: after restart, killed the interrupted focused Lean
  build and inspected the only dirty changes. The uncommitted direct
  `burn` no-liquidity exact-run proof had the same bad shape as the failed
  direct `swap` ordered-guard proof: it tried to simplify too much of the real
  entrypoint after the target guard. I removed that uncommitted slice before
  continuing. Future post-lock ordered reverts should be proved through small
  proof-local prefix helpers/adapters, not by adding contract helpers or by
  unfolding the entire public function.
- 2026-05-17 16:58 PDT: attempted a direct successful-`sync` lock-restoration
  bridge and removed it before committing. The statement is useful, but the
  proof again tried to normalize the whole reserve/TWAP tail and hit a Lean
  stack overflow. The right proof shape is a reusable storage-write helper for
  "final successful write to `unlocked` is `1`"; do not keep brute-force
  branch-splitting proofs for this.
- 2026-05-17 17:02 PDT: switched to a clean factory-history slice. Added a
  reader-facing concrete theorem that any successful create history with
  unchanged `allPairsLength` preserves the reconstructed unordered lookup
  relation exactly. This strengthens the factory no-hidden-overwrite story
  without adding new trust assumptions or touching contract code.
- 2026-05-17 17:05 PDT: full verification passed for the factory same-length
  lookup slice: focused Factory proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`. Known cache/signature permission warnings remain
  unchanged.
- 2026-05-17 17:10 PDT: after re-checking Tamago ERC4626 closed-world style,
  started a Pair surplus-value slice. The new target is a short trace-wide
  consequence: no-donation histories cannot increase the spot value of
  skimmable surplus, so skim profit must be paid for by surplus already present
  at the start.
- 2026-05-17 17:14 PDT: full verification passed for the Pair surplus-value
  slice: focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`. Known cache/signature permission warnings remain
  unchanged.
- 2026-05-17 17:06 PDT: after restart, resumed from a clean worktree and
  selected a narrow swap bridge that avoids the previously-failed whole
  entrypoint proof shape. Added the public success-side fact that any successful
  real `swap` must have at least one nonzero output amount, proved by composing
  the exact zero-output revert with the existing lock-open success bridge.
- 2026-05-17 17:09 PDT: full verification passed for the swap nonzero-output
  bridge slice: focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama
  check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`. Known cache/signature permission warnings remain
  unchanged.
- 2026-05-17 17:10 PDT: starting the next compositional swap bridge slice:
  use the just-proved successful-swap nonzero-output fact to remove the manual
  output premise from the public swap-to-closed-world and swap-oracle bridge
  statements. This should stay proof-local and avoid unfolding the post-callback
  swap tail.
- 2026-05-17 17:15 PDT: full verification passed for the refined swap bridge
  slice. Successful swap refinement and swap reserve/oracle bridge specs now
  derive the nonzero-output gate from the actual run; focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check` all passed. Known
  cache/signature permission warnings remain unchanged.
- 2026-05-17 17:16 PDT: starting the next economic bridge slice. The target is
  a direct successful-swap no-caller-profit theorem that derives the
  `PairWorldStep` from the actual run plus final-balance/K facts, instead of
  asking readers to provide that modeled step manually.
- 2026-05-17 17:19 PDT: full verification passed for the successful-swap
  economic bridge. The spec now states directly that a successful real swap,
  with final-balance/K facts and caller-plus-pool redistribution at the
  starting spot price, cannot leave the caller richer. Focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check` all passed.
- 2026-05-17 17:23 PDT: cleaned active spec/coverage/manifest wording to avoid
  the confusing "passive reconciliation" phrasing. Current reader-facing text
  now says `skim`/`sync` directly. Left the historical progress log intact
  except for this new checkpoint. Verification passed: whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`.
- 2026-05-17 17:24 PDT: updated the active spec coverage document to reflect
  the newly-added direct successful-swap no-caller-profit bridge, so the
  remaining-work section no longer says the reader must supply a modeled swap
  step for that economic conclusion.
- 2026-05-17 17:25 PDT: starting a burn economic bridge slice. The target is a
  direct successful-run theorem saying a real `burn`, once connected to its
  concrete redemption facts, preserves or improves remaining LP backing
  (`K / totalSupply^2`) through the existing closed-world burn invariant.
- 2026-05-17 17:29 PDT: resumed after restart. The focused Pair proof failed
  because the new burn bridge proof wrapper referenced a later theorem in the
  same file. I moved only that public proof wrapper after the closed-world burn
  invariant proof; the spec statement and contract source are unchanged.
- 2026-05-17 17:32 PDT: burn economic bridge verified end to end. Added
  `pair_burn_success_run_preserves_remaining_lp_share`, proving that a
  successful real `burn`, once connected to its concrete redemption facts,
  preserves or improves remaining LP backing (`K / totalSupply^2`). Verification
  passed: focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`.
- 2026-05-17 17:34 PDT: started the next ordered swap-revert slice. Added
  short public obligations for the two pre-external-call swap guards after
  nonzero output: outputs must be below reserves, and `to` must not be either
  token contract. These are exact run-result specs, not aggregate swap behavior.
- 2026-05-17 17:39 PDT: backed out the ordered swap-revert obligations before
  committing them. Focused proof again expanded beyond the intended prefix into
  the transfer/callback/K tail and hit the known kernel-recursion failure. The
  right route remains a proof-local prefix adapter, not public obligations that
  cannot yet be discharged cleanly.
- 2026-05-17 17:41 PDT: started the symmetric mint economic bridge. The target
  is a short successful-run theorem saying that a nonempty-pool `mint`, once
  connected to its pro-rata arithmetic facts, cannot dilute existing LP backing.
- 2026-05-17 17:45 PDT: mint economic bridge verified end to end. Added
  `pair_mint_subsequent_success_run_preserves_existing_lp_share`, proving that
  a successful later `mint`, once connected to concrete pro-rata facts, preserves
  or improves LP backing (`K / totalSupply^2`). Verification passed: focused
  Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 17:47 PDT: started a successful-swap supply bridge. The target is
  a short public theorem saying that a successful `swap`, once connected to its
  final-balance and K facts, preserves LP total supply and locked liquidity.
- 2026-05-17 17:50 PDT: successful-swap supply bridge verified end to end.
  Added `pair_swap_success_run_preserves_liquidity_supply_from_run`, proving
  that successful swaps connected to their final-balance/K facts preserve LP
  total supply and locked liquidity. Verification passed: focused Pair proof,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 17:51 PDT: started the matching successful `skim`/`sync` supply
  bridge slice. The goal is direct public theorems saying that successful
  cleanup/accounting calls preserve LP total supply and locked liquidity.
- 2026-05-17 17:55 PDT: successful `skim`/`sync` supply bridge verified end to
  end. Added direct public theorems for both calls preserving LP total supply
  and locked liquidity. Verification passed: focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26),
  `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 17:58 PDT: tried a proof-local
  `swap_run_revert_insufficient_liquidity_prefix` adapter with no public spec
  or manifest entry. Even the private prefix theorem forced Lean to elaborate
  the generated `swap` term deeply enough to hit kernel recursion at theorem
  elaboration. Removed the scratch theorem. Next ordered-revert work likely
  needs a smaller generated/harnessed prefix term or a reusable contract-monad
  lemma that avoids mentioning the full `swap` term in the theorem conclusion.
- 2026-05-17 18:04 PDT: resumed after machine restart and completed the
  executable mint/burn supply-movement bridge slice. Added public Pair specs
  and proofs showing successful first and later `mint` runs strictly increase
  LP total supply, and successful `burn` runs reduce LP total supply exactly by
  the burned liquidity, once connected to their concrete arithmetic facts.
  Verification passed: focused Pair proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`. Existing unused-variable warnings and sandbox cache-write
  warnings remain unchanged.
- 2026-05-17 18:08 PDT: starting the executable swap K bridge. Closed-world
  swaps already prove raw cached K cannot decrease from the canonical
  fee-adjusted K check; this slice exposes the same conclusion for successful
  public `swap` runs once their final-balance and K facts are supplied.
- 2026-05-17 18:08 PDT: executable swap K bridge verified end to end. Added
  `pair_swap_success_run_never_decreases_k_from_run`, proving that a successful
  real `swap`, connected to final-balance and fee-adjusted-K facts, cannot
  decrease raw cached reserve product. Verification passed: focused Pair proof,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 18:11 PDT: starting the executable mint K bridge. The goal is the
  mint-side companion to the swap K bridge: successful first and later public
  `mint` runs should expose raw cached-K nondecrease once connected to their
  existing arithmetic facts.
- 2026-05-17 18:11 PDT: executable mint K bridge verified end to end. Added
  `pair_mint_first_success_run_never_decreases_k_from_run` and
  `pair_mint_subsequent_success_run_never_decreases_k_from_run`, proving that
  successful initial and later `mint` runs cannot decrease raw cached reserve
  product once connected to their arithmetic facts. Verification passed:
  focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`.
- 2026-05-17 18:16 PDT: starting a short burn reserve-write split. The existing
  burn oracle bridge packages reserve writes with TWAP cases; this slice adds a
  separate reader-facing fact that successful `burn` writes cached reserves to
  the post-transfer token balances represented by the model.
- 2026-05-17 18:16 PDT: burn reserve-write split verified end to end. Added
  `pair_burn_success_run_updates_reserves_to_balances_from_run`, proving that a
  successful real `burn`, connected to its redemption facts, caches the
  post-transfer token balances as reserves. Verification passed: focused Pair
  proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 18:20 PDT: starting the matching mint reserve-write split. The
  target is separate first-mint and later-mint facts saying successful public
  `mint` runs cache the observed token balances as reserves, without bundling
  that simple statement together with the TWAP/oracle cases.
- 2026-05-17 18:20 PDT: mint reserve-write split verified end to end. Added
  `pair_mint_first_success_run_updates_reserves_to_balances_from_run` and
  `pair_mint_subsequent_success_run_updates_reserves_to_balances_from_run`,
  proving that successful initial and later `mint` runs cache observed token
  balances as reserves once connected to their arithmetic facts. Verification
  passed: focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`.
- 2026-05-17 18:24 PDT: starting the swap reserve-write split. The target is a
  short successful-run fact saying that after optimistic outputs and callback
  repayment, the final balances used for the K check are exactly the balances
  cached as reserves.
- 2026-05-17 18:24 PDT: swap reserve-write split verified end to end. Added
  `pair_swap_success_run_updates_reserves_to_balances_from_run`, proving that a
  successful real `swap`, connected to final-balance and fee-adjusted-K facts,
  caches final post-output/post-callback balances as reserves. Verification
  passed: focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`.
- 2026-05-17 18:28 PDT: starting the sync reserve-write split. The target is a
  short successful-run fact saying `sync` caches the current observed token
  balances as reserves, without bundling that statement with TWAP cases.
- 2026-05-17 18:28 PDT: sync reserve-write split verified end to end. Added
  `pair_sync_success_run_updates_reserves_to_balances_from_run`, proving that a
  successful real `sync` caches current observed token balances as reserves.
  Verification passed: focused Pair proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`.
- 2026-05-17 18:41 PDT: starting AMM event coverage with the smallest complete
  slice: successful public `sync` should emit the canonical `Sync` event carrying
  the observed token balances that become reserves. This follows the canonical
  Uniswap Pair behavior and should be a short executable-boundary fact, not a
  whole-function summary.
- 2026-05-17 18:45 PDT: backed out the attempted public `sync` event obligation
  before committing it. The direct proof still unfolds the whole oracle/update
  suffix and hits Lean kernel-depth limits, so AMM event coverage needs a
  factored suffix adapter before becoming public. Moving next to short ordered
  swap guard proofs, which stop before external transfers and the oracle suffix.
- 2026-05-17 18:48 PDT: starting the ordered swap invalid-recipient guard. This
  is a canonical pre-transfer guard: after the lock, nonzero-output, and
  liquidity checks pass, `swap` must reject `to == token0` or `to == token1`
  with `UniswapV2: INVALID_TO` before any optimistic transfer or callback.
- 2026-05-17 18:52 PDT: backed out the uncommitted invalid-recipient guard proof
  attempt. Even with exact raw guard hypotheses, direct simplification expands
  the later transfer/callback/K/oracle tail and hits kernel-depth limits. This
  should return only after introducing a private, reusable swap-prefix adapter.
- 2026-05-17 18:58 PDT: checked proof markers against `tama.toml`. Several
  already-proved short Pair ERC20/initialize obligations were not registered in
  the manifest, including basic approve/transfer/transferFrom facts and the
  zero-output swap guard. Registering those now is a real coverage fix: it makes
  existing Lean proofs visible to Tama without adding duplicate specs.
- 2026-05-17 19:02 PDT: manifest coverage pass completed locally. The
  proof-marker/manifest diff is empty for Pair and Factory after registering the
  missing Pair ERC20/init/zero-output obligations and Factory guard/view helper
  obligations.
- 2026-05-17 19:08 PDT: corrected the manifest pass before committing. `tama
  build` rejected those additions because the same obligations already have
  `// tama: mirrors=...` Foundry metadata, and Tama forbids an obligation from
  having both runtime mirrors and `coverage.proof_only` text. Removed the
  uncommitted manifest additions; the durable lesson is to compare Lean markers,
  proof-only entries, and mirrors together, not only markers against
  `tama.toml`.
- 2026-05-17 19:12 PDT: post-restart docs/coverage hygiene verified. No code or
  spec obligations changed in this slice; the durable updates are the explicit
  coverage wording that swap zero-output has a Foundry mirror and the progress
  notes documenting the blocked event/swap-prefix attempts. Verification passed:
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26),
  `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 19:15 PDT: starting a private swap-prefix adapter experiment. The
  goal is not to add a public obligation yet; it is to prove the invalid
  recipient branch with an exact `simp only` prefix that stops before
  transfer/callback/K/oracle code. If this still expands the tail, it should be
  backed out immediately.
- 2026-05-17 19:18 PDT: backed out the private swap-prefix adapter experiment.
  `simp only` still left the invalid-recipient branch under enough state binders
  that Lean expanded the transfer/callback/K/oracle tail and hit kernel depth.
  Do not repeat direct simplification for later swap guards; the next viable
  route needs a different proof technique or a non-public generated/proof
  factoring of the monadic prefix.
- 2026-05-17 18:57 PDT post-restart: resumed from a clean worktree and
  re-read the current Pair spec, Pair proof, proof-only manifest entries, and
  recent blocker notes. The next slice is intentionally not another direct
  public-entrypoint unfold. It will add a short reader-facing closed-world
  economics theorem that composes existing no-donation balance facts with
  existing no-mint/no-burn no-extraction facts.
- 2026-05-17 19:01 PDT: clean non-liquidity economics slice verified. Added
  two short public Pair specs and Lean proofs: a reachable zero-surplus
  no-donation/no-mint/no-burn history ends balanced and cannot reduce actual
  token-balance value at the initial spot price; the caller-facing companion
  adds no caller profit under the explicit caller-plus-pair redistribution
  premise. Verification passed: focused Pair proof, whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26),
  `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 19:06 PDT: starting the next non-blocked invariant slice. The
  target is a short reader-facing theorem that any finite successful modeled
  history from a reachable Pair state ends in `PairWorldGood`. This packages the
  reserve-backing, uint112-bound, and LP-supply-lock invariant without
  restating an entire public function body.
- 2026-05-17 19:09 PDT: reachable finite-history core invariant verified.
  Added `pair_closed_world_reachable_path_good`, a short public spec and proof
  that every finite successful modeled Pair history from a reachable state
  preserves `PairWorldGood`: reserve backing, uint112 reserve bounds, and
  LP-supply lock coherence. Verification passed: focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 19:11 PDT: starting a narrow executable bridge slice for `skim`
  and `sync`. Both calls already have success-run bridges into the closed-world
  model without extra premises. The next specs will expose the direct consequence:
  if the concrete pre-state projects to `PairWorldGood` and the real call
  succeeds, the modeled post-state also satisfies `PairWorldGood`.
- 2026-05-17 19:15 PDT: skim/sync executable core-invariant bridge verified.
  Added `pair_skim_success_run_preserves_good_from_run` and
  `pair_sync_success_run_preserves_good_from_run`, proving that successful real
  `skim` and `sync` calls preserve the projected `PairWorldGood` invariant from
  good concrete pre-state projections. Verification passed: focused Pair proof,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 19:16 PDT: starting the matching executable core-invariant bridge
  for `mint`, `burn`, and `swap`. These specs will keep the existing arithmetic
  premises from the refinement lemmas and add only the direct consequence that
  a good projected pre-state remains good after the modeled successful run.
- 2026-05-17 19:22 PDT: primary-entrypoint executable core-invariant bridge
  verified. Added success-run `PairWorldGood` preservation specs and proofs for
  first mint, later mint, burn, and swap, each composed from the existing
  executable refinement lemma and the closed-world one-step preservation
  theorem. Verification passed: focused Pair proof, whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26),
  `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 19:25 PDT: resumed after computer restart from a clean worktree.
  Next narrow target is the missing ordered swap guard layer: exact Lean
  run-result specs for insufficient liquidity and invalid recipient. This is a
  prefix proof attempt only; do not expand the transfer/callback/K/oracle tail,
  and back out if the proof starts reproducing the earlier direct-simp failure.
- 2026-05-17 19:27 PDT: backed out the direct swap insufficient-liquidity and
  invalid-recipient proof attempt. It reproduced the same kernel-depth failure:
  even with explicit output/liquidity/recipient guard facts, simplification did
  not stop at the target guard and expanded the transfer/callback/K/oracle tail.
  Do not retry this direct public-entrypoint simplification route.
- 2026-05-17 19:28 PDT: switching to a compositional factory slice instead of
  another direct Pair prefix proof. Target: expose the direct reader-facing
  consequence of the existing createPair executable bridge, namely that a
  successful real create from a good modeled factory history preserves
  `FactoryWorldGood` for the appended history.
- 2026-05-17 19:31 PDT: factory create invariant bridge verified. Added
  `factory_createPair_success_preserves_good`, proving a successful real
  `createPair` from a good modeled pre-history preserves the factory invariant
  after appending the new sorted pair. Verification passed: focused Factory
  proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 19:33 PDT: starting the matching factory base-case bridge. Target:
  first successful real `createPair` from an empty public pair array directly
  establishes `FactoryWorldGood` for the one-pair modeled history, so the
  invariant story has an executable starting point as well as an inductive
  preservation step.
- 2026-05-17 19:35 PDT: factory first-create invariant bridge verified. Added
  `factory_createPair_first_success_preserves_good`, proving the first
  successful real `createPair` establishes the good factory-world invariant for
  the one-pair modeled history. Verification passed: focused Factory proof,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 19:36 PDT: starting the Pair first-mint base-case bridge. Target:
  remove the extra `PairWorldGood` pre-state premise for initial mint by
  deriving the empty-pool good-state facts directly from the concrete premises
  already needed by the successful first-mint refinement.
- 2026-05-17 19:43 PDT: Pair first-mint base-case bridge verified. Added
  `pair_mint_first_success_run_establishes_good_from_run`, proving a
  successful first mint establishes `PairWorldGood` for the post-mint modeled
  state from concrete empty-pool premises rather than an assumed good pre-state.
  Verification passed: focused Pair proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`.
- 2026-05-17 19:45 PDT: starting executable first-mint lock slice. Target:
  expose at the successful public `mint` boundary that the first mint locks
  `MINIMUM_LIQUIDITY` and leaves strictly less than the whole LP supply
  attributable to the first provider, by composing existing first-mint
  refinement with closed-world lock theorems.
- 2026-05-17 19:52 PDT: executable first-mint lock slice verified. Added
  `pair_mint_first_success_run_locks_minimum_liquidity_from_run` and
  `pair_mint_first_success_run_keeps_locked_share_from_run`, proving that a
  successful public first mint exposes the locked `MINIMUM_LIQUIDITY` floor,
  exact lock-plus-user-liquidity supply shape, and first-LP less-than-total
  share fact. Verification passed: focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 19:54 PDT: starting executable later-mint lock-preservation
  slice. Target: expose the companion public-call fact that once the first-mint
  lock exists, a successful later `mint` preserves locked liquidity exactly.
- 2026-05-17 19:56 PDT: executable later-mint lock-preservation slice
  verified. Added
  `pair_mint_subsequent_success_run_preserves_locked_liquidity_from_run`,
  proving that a successful public later mint preserves the locked-liquidity
  value exactly and makes total supply old supply plus returned user liquidity.
  Verification passed: focused Pair proof, whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`.
- 2026-05-17 19:58 PDT: starting executable burn lock-retention slice.
  Target: expose at the successful public `burn` boundary that burns cannot
  redeem below the permanently locked liquidity floor and preserve the
  locked-liquidity value exactly.
- 2026-05-17 20:01 PDT: executable burn lock-retention slice verified. Added
  `pair_burn_success_run_cannot_redeem_locked_liquidity_from_run`, proving
  that a successful public burn leaves post-burn supply covering the locked
  liquidity floor and preserves the locked-liquidity value exactly once the run
  is connected to its redemption facts. Verification passed: focused Pair
  proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 20:02 PDT: starting executable burn positive-balance slice.
  Target: expose at the successful public `burn` boundary that a burn from a
  good state with positive token balances cannot empty either token side.
- 2026-05-17 20:05 PDT: executable burn positive-balance slice verified.
  Added `pair_burn_success_run_preserves_positive_balances_from_run`, proving
  that a successful public burn from a good state with positive token balances
  leaves both modeled post-burn token balances positive once the run is
  connected to its redemption facts. Verification passed: focused Pair proof,
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 20:08 PDT: starting executable swap final-balance safety slice.
  Target: expose the flash-swap accounting fact at the public `swap` boundary:
  once a successful run is connected to final post-callback balances and K
  facts, those same final balances account for input/output and are the balances
  charged by the fee-adjusted K check.
- 2026-05-17 20:11 PDT: executable swap final-balance safety slice verified.
  Added `pair_swap_success_run_k_uses_final_balances_from_run`, proving that a
  successful public swap connected to final balance and K facts uses those final
  post-callback balances both for input/output accounting and for the
  fee-adjusted K inequality. Verification passed: focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 20:13 PDT: starting factory success-implies-pre-guards slice.
  Target: expose that successful `createPair` execution proves the early
  ordered guards passed: distinct tokens, nonzero tokens, and absent sorted
  pair mapping before CREATE2.
- 2026-05-17 20:18 PDT: factory success-implies-pre-guards slice verified.
  Added `factory_createPair_success_implies_pre_create_guards`, proving from
  exact ordered revert theorems that a successful public `createPair` run
  implies distinct tokens, nonzero tokens, and an absent sorted pair mapping
  before CREATE2. Verification passed: whole `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test` (26/26), `tama audit` (0 issues),
  and `git diff --check`.
- 2026-05-17 20:22 PDT: starting mint success-to-deposit-facts slice. Target:
  expose that successful public `mint` execution proves observed balances back
  cached reserves and that both deposited token amounts are positive, using
  exact ordered revert facts instead of adding contract helpers.
- 2026-05-17 20:28 PDT: narrowed current mint slice after focused proof build
  hung in the direct zero-deposit path. Keeping the reserve-backing bridge in
  this slice; positive-deposit success facts need a separate factored prefix
  proof instead of direct whole-mint simplification.
- 2026-05-17 20:31 PDT: abandoned the direct mint reserve-backing bridge after
  the narrowed proof route also hung. Removed the unverified public obligations
  from the spec, proof, and Tama registry. Future mint-boundary strengthening
  should first factor a private prefix lemma, then expose only the short reader
  property once the proof route is known to terminate.
- 2026-05-17 20:32 PDT: starting trace-level LP supply classifier slice. Target:
  expose existing no-mint/no-burn path invariants in the reader-facing
  contrapositive direction: LP supply increases require mint, LP supply
  decreases require burn, and any supply-changing endpoint cannot be explained
  by a history with neither liquidity operation.
- 2026-05-17 20:36 PDT: trace-level LP supply classifier slice verified.
  Added reader-facing finite-history classifiers for supply increase requiring
  mint, supply decrease requiring burn, and any supply change requiring mint or
  burn. Verification passed: focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 20:36 PDT: starting trace-level reserve classifier slice. Target:
  expose the existing reserve-isolation invariant in the reader-facing
  contrapositive direction: if cached reserves change, the history cannot be one
  with no mint, burn, swap, or sync.
- 2026-05-17 20:39 PDT: trace-level reserve classifier slice verified. Added
  `pair_closed_world_reachable_reserve_change_requires_reserve_update`, proving
  that a reachable endpoint with changed cached reserves cannot be reached by a
  no-reserve-update history. Verification passed: focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 20:40 PDT: starting trace-level surplus classifier slice. Target:
  expose the no-donation surplus invariant in the reader-facing direction:
  if skimmable surplus increases on either token side, a donation step is
  necessary somewhere in the history.
- 2026-05-17 20:43 PDT: trace-level surplus classifier slice verified. Added
  `pair_closed_world_reachable_surplus_increase_requires_donation`, proving
  that a reachable endpoint with increased token-side surplus cannot be reached
  by a no-donation history. Verification passed: focused Pair proof, whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 20:46 PDT: starting successful-swap actual-token-balance
  no-profit bridge. Target: expose at the public `swap` boundary that a
  successful run from a zero-surplus reachable pool cannot increase caller
  actual-token-balance value when caller-plus-pair value is only redistributed.
- 2026-05-17 20:50 PDT: successful-swap actual-token-balance no-profit bridge
  verified. Added `pair_swap_success_run_no_caller_token_balance_profit_from_run`,
  connecting a successful public swap plus final-balance/K facts to the
  zero-surplus actual-token-balance caller no-profit theorem. Verification
  passed: focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`,
  `tama build`, `tama test` (26/26), `tama audit` (0 issues), and
  `git diff --check`.
- 2026-05-17 20:52 PDT: starting successful-skim clean-pool no-profit bridge.
  Target: expose at the public `skim` boundary that a successful skim from a
  zero-surplus reachable pool leaves pair token-balance value unchanged, so
  caller-plus-pair redistribution cannot leave the caller richer.
- 2026-05-17 20:56 PDT: successful-skim clean-pool no-profit bridge verified.
  Added `pair_skim_success_run_no_caller_token_balance_profit_from_run`,
  connecting a successful public skim from a zero-surplus reachable pool to
  caller actual-token-balance no-profit. Verification passed: focused Pair
  proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`.
- 2026-05-17 20:58 PDT: starting successful-sync clean-pool no-profit bridge.
  Target: expose the sync-side twin of the skim bridge: from a zero-surplus
  reachable pool, a successful public `sync` leaves actual pair token balances
  unchanged, so caller-plus-pair redistribution cannot make the caller richer.
- 2026-05-17 21:19 PDT: starting plain-English spec cleanup before adding more
  claims. Target: remove proof-jargon from public spec comments, coverage docs,
  and manifest descriptions so the specs read as contract guarantees and
  invariants rather than proof plumbing.
- 2026-05-17 21:29 PDT: plain-English cleanup plus successful-sync clean-pool
  no-profit theorem verified. Added
  `pair_sync_success_run_no_caller_token_balance_profit_from_run`, kept the
  public comments/descriptions focused on contract guarantees, and updated the
  coverage guide to name sync's direct caller no-profit guarantee. Verification
  passed: whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), public wording scans, and
  `git diff --check`.
- 2026-05-17 21:36 PDT: starting direct successful-mint arithmetic slice.
  Target: add short public claims that successful first mints use the canonical
  square-root-minus-lock formula and successful later mints use the smaller
  pro-rata share, then prove those claims from existing mint-success facts or
  narrowly factored entrypoint reasoning without modifying the contract.
- 2026-05-17 21:44 PDT: reviewed the direct successful-mint theorem shape
  against Tamago ERC4626 success-path specs. A theorem that assumes
  `result = success (mintFirstLiquidity s) ...` is tautological, while a
  theorem over an arbitrary returned value needs a private helper that computes
  the relevant `mint` branch under explicit success preconditions. Updated the
  active plan to make those private helpers the first step for Task 3.
- 2026-05-17 21:49 PDT: resumed execution after restart and removed the
  uncommitted monolithic first-mint success helper. Focused Pair proof is green
  again. Do not retry full public `mint` unfolding; the next mint work must be a
  short reader-facing security claim proved from existing accounting facts or a
  narrowly bounded proof-local helper.
- 2026-05-17 21:58 PDT: added the first-mint formula claim
  `pair_first_mint_success_uses_canonical_liquidity_formula`. It states the
  reader-facing fairness rule directly: successful initial mint accounting makes
  total LP supply equal to the square-root liquidity measure, while the provider
  receives that amount minus the permanently locked `MINIMUM_LIQUIDITY`.
  Focused Pair proof passes.
- 2026-05-17 21:59 PDT: first-mint formula slice verified end to end: whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), public wording scan, and
  `git diff --check` all pass.
- 2026-05-17 22:02 PDT: started burn redemption formula slice after committing
  the first-mint formula. Added reader-facing burn specs for exact floor
  pro-rata payout amounts and caching reserves to post-redemption balances.
- 2026-05-17 22:05 PDT: burn redemption formula focused proof passes. The
  proof only unfolds the local burn arithmetic helpers and post-burn projected
  state; it does not unfold the public `burn` body.
- 2026-05-17 22:06 PDT: burn redemption formula slice verified end to end:
  whole `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), public wording scan, and
  `git diff --check` all pass.
- 2026-05-17 22:09 PDT: started swap final-balance/K slice. Added two short
  reader-facing swap specs: final balances account for optimistic output plus
  inferred input, and the fee-adjusted K check is charged against those same
  final post-repayment balances.
- 2026-05-17 22:12 PDT: swap final-balance/K focused proof passes. The new
  public claims unpack the existing combined swap accounting theorem into two
  plain statements for readers.
- 2026-05-17 22:14 PDT: swap final-balance/K slice verified end to end: whole
  `lake build TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`
  (26/26), `tama audit` (0 issues), public wording scan, and
  `git diff --check` all pass.
- 2026-05-17 22:17 PDT: started ordered-failure slice with swap
  insufficient-liquidity guards. Added exact run-result specs for rejecting
  token0 or token1 output at or above cached reserves before transfer/callback
  side effects.
- 2026-05-17 22:14 PDT: backed out the uncommitted swap reserve-output
  exact-revert slice after focused proof attempts repeatedly expanded into the
  transfer/callback/K tail and hit Lean kernel-depth limits. Do not retry this
  with broad public `swap` simplification; the next exact ordered-failure work
  needs a proof-local prefix lemma that stops at the target guard.
- 2026-05-17 22:16 PDT: started AMM event correctness with the `sync` event.
  Target: state the small observable guarantee that a successful public `sync`
  emits `Sync(observedBalance0, observedBalance1)` while keeping the proof
  bounded to the sync path.
- 2026-05-17 22:23 PDT: backed out the uncommitted `sync` event proof after
  focused attempts normalized the guard and oracle branches but still hit Lean
  kernel recursion at the public-run theorem. Do not prove AMM event coverage by
  broad reserve-update entrypoint simplification; event work needs a smaller
  proof-local lemma over the common reserve-write tail or an existing trace
  abstraction.
- 2026-05-17 22:27 PDT: refreshed the active plan's restart point after
  compaction. Confirmed the committed slices are plain-language cleanup plus
  sync no-profit, first-mint formula, burn redemption formula, and swap
  final-balance/K formula. Remaining proof-heavy work should start from bounded
  helper lemmas, not broad public-entrypoint simplification.
- 2026-05-17 22:30 PDT: started a low-risk public metadata cleanup before the
  next proof slice. Reworded manifest descriptions that exposed internal
  `PairWorldGood`/proof-model terms so they describe reserve backing, uint112
  reserve bounds, and LP-supply lock coherence in plain language.
- 2026-05-17 22:33 PDT: completed the public manifest wording cleanup pass.
  The remaining proof-surface descriptions avoid `PairWorldGood`,
  `Tamago-style`, `ghost`, and `obligation` wording, while leaving theorem
  identifiers unchanged to avoid needless proof churn.
- 2026-05-17 22:41 PDT: retried swap output-at-reserve exact revert with a
  more bounded proof that exposed the concrete reserve/unlocked slots and the
  false liquidity guard. Lean still expanded the generated post-guard tail and
  hit kernel recursion. Backed out the uncommitted spec/proof/manifest slice;
  focused Pair proof is green again. Do not retry this exact revert without a
  new proof-local abstraction over the generated `require` prefix.
- 2026-05-17 22:43 PDT: added a clean Factory success slice instead. New public
  specs state that successful `createPair` increments `allPairsLength` exactly
  once and appends the new pair at the old length index. Proofs reuse the
  existing successful-create storage/event theorem; focused Factory proof
  passes.
- 2026-05-17 22:54 PDT: tried to add Lean exact-revert coverage for the swap
  invalid-recipient guard (`to == token0` / `to == token1`) plus the
  success-side consequence that successful swaps use a non-token recipient.
  Even with lock, nonzero-output, and liquidity premises exposed, Lean unfolded
  the post-recipient transfer/callback/K tail and hit kernel recursion. Backed
  the uncommitted slice out. Do not retry this by direct public `swap`
  simplification; it needs a proof-local prefix lemma that stops at the
  recipient guard.
- 2026-05-17 22:56 PDT: added a bounded Factory router-facing success spec
  instead. New public theorem states that immediately after successful
  `createPair`, the actual `getPair` view returns the created pair in both
  token orders. Focused Factory proof build passes.
- 2026-05-17 23:02 PDT: added two small Pair model accounting specs. Valid
  mints now state that cached reserves increase by exactly the deposited token
  amounts; valid burns state that redeemed token amounts are exactly removed
  from token balances before the remaining balances are cached as reserves.
  Focused Pair proof build passes.
- 2026-05-18 12:30 PDT: resumed on branch `codex-critical-pair-spec-gaps`
  to execute the critical Pair spec plan. Starting with the small successful
  mint boundary facts: first and later mints should plainly state that deposited
  amounts are the pair's token balance increases over cached reserves.
- 2026-05-18 12:34 PDT: Task 1 complete. Added and proved first/later mint
  balance-increase specs, mirrored them in Foundry mint tests instead of adding
  normal obligations to `tama.toml`, and verified with `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test`, `tama audit`, and
  `git diff --check`.
- 2026-05-18 12:41 PDT: Task 2 complete. Added and proved burn specs stating
  that public `burn` uses the LP balance held by the pair and current total
  supply, and that successful burn leaves token balances equal to previous
  balances minus redeemed amounts. Added Foundry mirror assertions to the
  pro-rata burn test and verified with `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test`, `tama audit`, and `git diff --check`.
- 2026-05-18 12:46 PDT: Task 3 complete. Added and proved short swap specs
  stating that inferred input is computed from final post-output/post-callback
  balances and that the fee-adjusted K check is charged against those same
  final balances. During plan review, rejected the stronger proposed balance
  equality without an extra no-shortfall premise because it is not true for
  every possible final balance. Added Foundry mirror tags and arithmetic checks
  to the swap K/reserve test, then verified with `lake build TamaUniV2.Proof`,
  `tama check`, `tama build`, `tama test`, `tama audit`, and `git diff --check`.
- 2026-05-18 12:52 PDT: Task 4 complete. Moved the proof-only locked-state
  helper into the Pair concrete helper module, added callback-time lock specs,
  and proved that any nested `mint`, `burn`, `swap`, `skim`, or `sync` call
  during a flash callback hits the normal `UniswapV2: LOCKED` guard. Expanded
  the Foundry callback mirror to attempt all five mutating entrypoints and
  verified with `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test`, `tama audit`, and `git diff --check`.
- 2026-05-18 13:19 PDT: Task 5 proof slice is focused-build green. Added the
  single-caller wallet model, with the caller owning all LP supply except
  permanently locked liquidity; modeled fresh transfers as `callerDonate` and
  made public `mint`/`swap` consume already-visible pair surplus. Proved the
  central finite-history theorem that the single caller's portfolio value at
  the initial spot price cannot increase, plus one-step versions for swap,
  mint, burn, skim, and passive actions. Focused proof build
  `lake build TamaUniV2.Proof.UniswapV2PairProof` passes; full Tama
  verification and commit are next.
- 2026-05-18 13:19 PDT: `tama build` proof-check and codegen passed, then
  manifest adaptation correctly required coverage metadata for the model-only
  single-caller wallet specs. Added narrow `coverage.proof_only` explanations
  for those six Lean-only economic obligations; no trust surface or axiom was
  added.
- 2026-05-18 13:24 PDT: Task 5 complete and ready to commit. Full verification
  passed with `lake build TamaUniV2.Proof`, `tama check`, `tama build`,
  `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`. The
  only warnings observed were existing unused-variable/cache-write warnings.
- 2026-05-18 13:38 PDT: Task 6 focused proof slice is green. Added caller-wallet
  model links for successful first mint, later mint, burn, prepaid-input swap,
  skim, and sync. The swap link is intentionally scoped to the case where
  inferred input is already visible as pair surplus at call entry; flash
  repayment timing should be represented by composing caller token movement
  with the same swap accounting rule rather than overclaiming this one-step
  theorem. Focused `lake build TamaUniV2.Proof.UniswapV2PairProof` passes; full
  verification and commit are next.
- 2026-05-18 13:40 PDT: Task 6 complete and ready to commit. Added proof-only
  coverage explanations for the six Lean-only caller-wallet link obligations;
  no trust entries were added. Full verification passed with `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26),
  `tama audit` (0 issues), and `git diff --check`.
- 2026-05-18 13:44 PDT: Task 7 final assurance pass complete. Updated the Pair
  spec opening argument to name the caller-wallet theorem layer, confirmed the
  stale-wording scan only hits historical `docs/agent-progress.md` entries,
  marked the active plan complete, and verified again with `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26),
  `tama audit` (0 issues), and `git diff --check`.
- 2026-05-22 16:38 PDT: Phase A #1 progressed: `updateReservesAndEmitSync_run_storage_matches_world` no longer appears in focused `lake build TamaUniV2.Proof.UniswapV2PairProof` errors; build remains red at mint-first composition plus later mint/burn/swap bridge rewrites.
- 2026-05-22 17:35 PDT: Mint-first storage proof time-box stopped after six focused builds. I made a narrow local reduction attempt inside `firstMintPath_run_storage_matches_world`, but the lemma is still not green. Last focused command: `lake build TamaUniV2.Proof.UniswapV2PairProof`. Exact remaining first unsolved goal:

```text
error: verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean:2727:43: unsolved goals
toAddr sender : Address
original : ContractState
h_product :
  (mintAmount0 original == 0 || div (mintFirstProduct original) (mintAmount0 original) == mintAmount1 original) = true
h_root : mintFirstRoot original > minimumLiquidity
h_success :
  (UniswapV2PairBase.firstMintPath toAddr sender (observedBalance0 original) (observedBalance1 original)
          (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot) (mintAmount0 original)
          (mintAmount1 original)).run
      (mintLockedState original) =
    ContractResult.success (mintFirstLiquidity original)
      ((UniswapV2PairBase.firstMintPath toAddr sender (observedBalance0 original) (observedBalance1 original)
              (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot) (mintAmount0 original)
              (mintAmount1 original)).run
          (mintLockedState original)).snd
checked : ContractResult Uint256 :=
  (UniswapV2PairBase.finishFirstMintChecked toAddr sender (observedBalance0 original) (observedBalance1 original)
        (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot) (mintAmount0 original)
        (mintAmount1 original) (mintFirstRoot original) (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
        (if (5 == 11) = true then 0 else original.storage 5)).run
    (mintLockedState original)
h_product_raw :
  (mintAmount0 original == 0 ||
      div (mul (mintAmount0 original) (mintAmount1 original)) (mintAmount0 original) == mintAmount1 original) =
    true
h_root_val :
  Core.Uint256.val 1000 < (sqrtValue (mul (mintAmount0 original) (mintAmount1 original)) (mintLockedState original)).val
h_root_val2 :
  Core.Uint256.val 1000 <
    (sqrtValue
        (mul
          (sub ((Contracts.balanceOf (original.storageAddr 1) original.thisAddress).run original).fst
            (original.storage 3))
          (sub ((Contracts.balanceOf (original.storageAddr 2) original.thisAddress).run original).fst
            (original.storage 4)))
        { «storage» := fun slotIdx => if slotIdx = 11 then 0 else original.storage slotIdx,
          transientStorage := original.transientStorage, storageAddr := original.storageAddr,
          storageMap := original.storageMap, storageMapUint := original.storageMapUint,
          storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
          thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
          blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber, chainId := original.chainId,
          blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize, calldata := original.calldata,
          memory := original.memory, knownAddresses := original.knownAddresses, events := original.events }).val
h_root_guard :
  Core.Uint256.val 1000 <
    (sqrtValue (mul (mintAmount0 original) (mintAmount1 original))
        { «storage» := fun slotIdx => if (slotIdx == 11) = true then 0 else original.storage slotIdx,
          transientStorage := original.transientStorage, storageAddr := original.storageAddr,
          storageMap := original.storageMap, storageMapUint := original.storageMapUint,
          storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
          thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
          blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber, chainId := original.chainId,
          blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize, calldata := original.calldata,
          memory := original.memory, knownAddresses := original.knownAddresses, events := original.events }).val
h_product_fold :
  sub
        (Contracts.erc20ReadStubWord✝ "balanceOf"
          [Core.Uint256.ofNat (Core.Address.toNat (original.storageAddr 1)),
            Core.Uint256.ofNat (Core.Address.toNat original.thisAddress)])
        (original.storage 3) =
      0 ∨
    div
        (mul
          (sub
            (Contracts.erc20ReadStubWord✝ "balanceOf"
              [Core.Uint256.ofNat (Core.Address.toNat (original.storageAddr 1)),
                Core.Uint256.ofNat (Core.Address.toNat original.thisAddress)])
            (original.storage 3))
          (sub
            (Contracts.erc20ReadStubWord✝ "balanceOf"
              [Core.Uint256.ofNat (Core.Address.toNat (original.storageAddr 2)),
                Core.Uint256.ofNat (Core.Address.toNat original.thisAddress)])
            (original.storage 4)))
        (sub
          (Contracts.erc20ReadStubWord✝ "balanceOf"
            [Core.Uint256.ofNat (Core.Address.toNat (original.storageAddr 1)),
              Core.Uint256.ofNat (Core.Address.toNat original.thisAddress)])
          (original.storage 3)) =
      sub
        (Contracts.erc20ReadStubWord✝ "balanceOf"
          [Core.Uint256.ofNat (Core.Address.toNat (original.storageAddr 2)),
            Core.Uint256.ofNat (Core.Address.toNat original.thisAddress)])
        (original.storage 4)
pathResult : ContractResult Uint256 :=
  (UniswapV2PairBase.firstMintPath toAddr sender (observedBalance0 original) (observedBalance1 original)
        (original.storage reserve0Slot.slot) (original.storage reserve1Slot.slot) (mintAmount0 original)
        (mintAmount1 original)).run
    (mintLockedState original)
⊢ (match
      match
        UniswapV2PairBase.finishFirstMintChecked toAddr sender (observedBalance0 original) (observedBalance1 original)
          (original.storage 3) (original.storage 4) (mintAmount0 original) (mintAmount1 original)
          (sqrtValue (mul (mintAmount0 original) (mintAmount1 original))
            { «storage» := fun slotIdx => if (slotIdx == 11) = true then 0 else original.storage slotIdx,
              transientStorage := original.transientStorage, storageAddr := original.storageAddr,
              storageMap := original.storageMap, storageMapUint := original.storageMapUint,
              storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
              thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
              blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber,
              chainId := original.chainId, blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize,
              calldata := original.calldata, memory := original.memory, knownAddresses := original.knownAddresses,
              events := original.events })
          (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
          (if (5 == 11) = true then 0 else original.storage 5)
          { «storage» := fun slotIdx => if (slotIdx == 11) = true then 0 else original.storage slotIdx,
            transientStorage := original.transientStorage, storageAddr := original.storageAddr,
            storageMap := original.storageMap, storageMapUint := original.storageMapUint,
            storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
            thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
            blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber, chainId := original.chainId,
            blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize, calldata := original.calldata,
            memory := original.memory, knownAddresses := original.knownAddresses, events := original.events } with
      | ContractResult.success a s' => ContractResult.success a s'
      | ContractResult.revert msg s' => ContractResult.revert msg s' with
    | ContractResult.success a s' => ContractResult.success a s'
    | ContractResult.revert msg a =>
      ContractResult.revert msg
        { «storage» := fun slotIdx => if (slotIdx == 11) = true then 0 else original.storage slotIdx,
          transientStorage := original.transientStorage, storageAddr := original.storageAddr,
          storageMap := original.storageMap, storageMapUint := original.storageMapUint,
          storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
          thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
          blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber, chainId := original.chainId,
          blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize, calldata := original.calldata,
          memory := original.memory, knownAddresses := original.knownAddresses, events := original.events }) =
    match
      match
        match
          UniswapV2PairBase.finishFirstMintChecked toAddr sender (observedBalance0 original) (observedBalance1 original)
            (original.storage 3) (original.storage 4) (mintAmount0 original) (mintAmount1 original)
            (sqrtValue (mul (mintAmount0 original) (mintAmount1 original))
              { «storage» := fun slotIdx => if (slotIdx == 11) = true then 0 else original.storage slotIdx,
                transientStorage := original.transientStorage, storageAddr := original.storageAddr,
                storageMap := original.storageMap, storageMapUint := original.storageMapUint,
                storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
                thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
                blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber,
                chainId := original.chainId, blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize,
                calldata := original.calldata, memory := original.memory, knownAddresses := original.knownAddresses,
                events := original.events })
            (mod original.blockTimestamp UniswapV2PairBase.uint32Modulus)
            (if (5 == 11) = true then 0 else original.storage 5)
            { «storage» := fun slotIdx => if (slotIdx == 11) = true then 0 else original.storage slotIdx,
              transientStorage := original.transientStorage, storageAddr := original.storageAddr,
              storageMap := original.storageMap, storageMapUint := original.storageMapUint,
              storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
              thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
              blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber,
              chainId := original.chainId, blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize,
              calldata := original.calldata, memory := original.memory, knownAddresses := original.knownAddresses,
              events := original.events } with
        | ContractResult.success a s' => ContractResult.success a s'
        | ContractResult.revert msg a =>
          ContractResult.revert msg
            { «storage» := fun slotIdx => if (slotIdx == 11) = true then 0 else original.storage slotIdx,
              transientStorage := original.transientStorage, storageAddr := original.storageAddr,
              storageMap := original.storageMap, storageMapUint := original.storageMapUint,
              storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
              thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
              blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber,
              chainId := original.chainId, blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize,
              calldata := original.calldata, memory := original.memory, knownAddresses := original.knownAddresses,
              events := original.events } with
      | ContractResult.success a s' => ContractResult.success a s'
      | ContractResult.revert msg s' => ContractResult.revert msg s' with
    | ContractResult.success a s' => ContractResult.success a s'
    | ContractResult.revert msg a =>
      ContractResult.revert msg
        { «storage» := fun slotIdx => if (slotIdx == 11) = true then 0 else original.storage slotIdx,
          transientStorage := original.transientStorage, storageAddr := original.storageAddr,
          storageMap := original.storageMap, storageMapUint := original.storageMapUint,
          storageMap2 := original.storageMap2, storageArray := original.storageArray, sender := original.sender,
          thisAddress := original.thisAddress, msgValue := original.msgValue, selfBalance := original.selfBalance,
          blockTimestamp := original.blockTimestamp, blockNumber := original.blockNumber, chainId := original.chainId,
          blobBaseFee := original.blobBaseFee, calldataSize := original.calldataSize, calldata := original.calldata,
          memory := original.memory, knownAddresses := original.knownAddresses, events := original.events }
```
