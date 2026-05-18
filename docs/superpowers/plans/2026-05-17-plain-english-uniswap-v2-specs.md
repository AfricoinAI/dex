# Plain-English Uniswap V2 Spec Remediation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the Lean specs read as a plain security argument for the Pair and Factory, then close the most important remaining security gaps without adding contract helpers or proof-only public claims.

**Architecture:** Keep the contract source unchanged. Public specs should state what the contract guarantees, while proof-local lemmas may do whatever technical work is needed to prove those guarantees. Work in small verified commits so a restart cannot confuse completed work with planned work.

**Tech Stack:** Lean 4, Verity EDSL, Tama, Foundry mirrors, Tamago-style closed-world reasoning.

---

## Files And Responsibilities

- `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
  - Public Pair security claims and reader-facing explanation.
  - Must use plain English comments.
  - Must not describe proof technique as a spec category.
- `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
  - Proofs for Pair claims.
  - May contain technical helper names, but public Tama discharge markers
    theorem names should correspond to understandable claims.
- `verity/spec/TamaUniV2/Spec/UniswapV2FactorySpec.lean`
  - Public Factory security claims and reader-facing explanation.
  - Same plain-language standard as Pair.
- `verity/proof/TamaUniV2/Proof/UniswapV2FactoryProof.lean`
  - Proofs for Factory claims.
- `tama.toml`
  - Public obligation descriptions.
  - Must describe security properties in plain language.
  - Avoid words that name proof technique instead of contract behavior:
    `bridge`, `refines`, `executable`, `from_run`, `expected-state`,
    `closed-world` unless the phrase is explicitly explaining the internal
    model and not a user-facing guarantee.
- `docs/spec-coverage.md`
  - Active coverage guide.
  - Must summarize implemented and missing security properties, not proof
    mechanics.
- `docs/agent-progress.md`
  - Append-only historical log.
  - Add timestamped entries only at the end.
- `docs/superpowers/plans/2026-05-17-invariant-first-uniswap-v2-specs.md`
  - Historical active plan with stale wording.
  - Do not rewrite history. Add a short supersession note at the top if needed.
- `test/verity/UniswapV2Core.t.sol`
  - Runtime mirrors for exact bytecode behavior, especially events, reverts,
    and flash/reentrancy behavior.

---

## Task 1: Freeze The Current WIP And Clean The Spec Vocabulary

**Files:**
- Modify: `docs/agent-progress.md`
- Modify: `docs/spec-coverage.md`
- Modify: `tama.toml`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2FactorySpec.lean`

- [ ] **Step 1: Record a restart-safe note**

  Run:

  ```bash
  date '+%Y-%m-%d %H:%M %Z'
  ```

  Append to `docs/agent-progress.md`:

  ```markdown
  - YYYY-MM-DD HH:MM TZ: starting plain-English spec cleanup. Target: remove
    proof-jargon from public spec comments, coverage docs, and manifest
    descriptions before adding more claims.
  ```

- [ ] **Step 2: Inventory bad public wording**

  Run:

  ```bash
  rg -n "bridge|refines|from_run|expected-state|executable|public-entrypoint consequence|success-side" docs/spec-coverage.md tama.toml verity/spec/TamaUniV2/Spec
  ```

  Expected: matches in `docs/spec-coverage.md`, `tama.toml`, and Pair/Factory
  spec comments. Do not mechanically rewrite with Ruby or Perl. Use targeted
  `apply_patch` edits.

- [ ] **Step 3: Replace reader-facing categories with plain claims**

  Apply these wording rules:

  - Replace proof-connection labels with the contract behavior being claimed.
  - When the mathematical model must be mentioned, say which accounting rule
    the contract satisfies.
  - Replace indirect success labels with a direct sentence starting “When this
    public call succeeds,” followed by the actual guarantee.
  - Replace “from run” in prose with “when the public call succeeds”.
  - Keep “closed-world” only in sections that explicitly discuss finite modeled
    histories.

  Example replacement in `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`:

  ```lean
  /--
  When `sync` succeeds from a clean reachable pool, it cannot transfer value to
  the caller.

  A clean pool has no token balance above cached reserves. In that state,
  `sync` only records balances that are already accounted for, so the pair's
  actual token balances do not change. If caller value plus pair value is only
  redistributed at the starting spot price, the caller cannot finish richer.
  -/
  ```

- [ ] **Step 4: Remove proof-plumbing claims from the coverage narrative**

  In `docs/spec-coverage.md`, the “Remaining Spec Work” section should use this
  shape:

  ```markdown
  - Direct arithmetic from successful calls: prove that successful `mint`,
    `burn`, and `swap` establish their own liquidity, redemption, input, and K
    facts, instead of asking later theorems to take those facts as premises.
  - Exact ordered failures: prove in Lean that each canonical guard fails with
    the expected reason and leaves state unchanged.
  - External-call safety: prove or explicitly mirror the lock behavior during
    flash callbacks and token transfers.
  - Events: prove successful Mint, Burn, Swap, and Sync logs match the canonical
    behavior and state changes.
  ```

- [ ] **Step 5: Verify no bad wording remains in public prose**

  Run:

  ```bash
  rg -n "bridge|public-entrypoint consequence|success-side|expected-state" docs/spec-coverage.md verity/spec/TamaUniV2/Spec tama.toml
  ```

  Expected: no matches in reader-facing comments or docs. Remaining matches in
  Lean identifiers are allowed only if they are not exposed as the explanation
  of a public security claim. If a `tama.toml` description still uses one of
  those words, rewrite the description.

- [ ] **Step 6: Verify**

  Run:

  ```bash
  lake build TamaUniV2.Proof
  /Users/zefram/.tama/bin/tama check
  git diff --check
  ```

  Expected: all pass. Existing unused-variable and sandbox cache warnings are
  acceptable.

- [ ] **Step 7: Commit**

  Run:

  ```bash
  git add docs/agent-progress.md docs/spec-coverage.md tama.toml verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/spec/TamaUniV2/Spec/UniswapV2FactorySpec.lean
  git commit -m "Use plain language for public specs"
  ```

---

## Task 2: Decide Whether The Current `sync` No-Profit Claim Belongs Publicly

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`

- [ ] **Step 1: Restate the current WIP in plain English**

  The current uncommitted theorem should be judged by this claim:

  ```text
  When `sync` succeeds from a reachable pool with no surplus token balances,
  it cannot make the caller richer if caller value plus pair token-balance
  value is only redistributed at the starting spot price.
  ```

- [ ] **Step 2: Keep it only if it remains short**

  Keep the theorem if its formal statement remains close to:

  ```lean
  def pair_sync_success_run_no_caller_token_balance_profit
      (s : ContractState) (result : ContractResult Unit)
      (callerValueBefore callerValueAfter : Nat) : Prop :=
    let before := pairWorldFromConcreteState s
    let after := pairWorldAfterSyncRun s
    result = (sync).run s →
      result = ContractResult.success () result.snd →
        PairWorldReachable before →
          PairWorldSurplus0 before = 0 →
            PairWorldSurplus1 before = 0 →
              callerValueBefore + PairWorldBalanceSpotValueNum before before =
                callerValueAfter + PairWorldBalanceSpotValueNum before after →
                callerValueAfter ≤ callerValueBefore
  ```

  If proving it requires adding helper functions to the contract or a large
  aggregate summary of `sync`, delete this WIP and do not replace it.

- [ ] **Step 3: Rename only if the rename is cheap and local**

  Prefer the shorter public name:

  ```lean
  pair_sync_success_run_no_caller_token_balance_profit
  ```

  If the existing `_from_run` name is deeply woven into generated tooling, keep
  the identifier for now but make every comment and `tama.toml` description
  plain.

- [ ] **Step 4: Update the manifest description**

  Use this `tama.toml` wording:

  ```toml
  "UniswapV2Pair.pair_sync_success_run_no_caller_token_balance_profit" = "When sync succeeds from a reachable pool with no surplus token balances, caller-plus-pair value redistribution cannot leave the caller richer."
  ```

  If the identifier is not renamed, use the existing key with the same
  description text.

- [ ] **Step 5: Verify**

  Run:

  ```bash
  lake build TamaUniV2.Proof.UniswapV2PairProof
  lake build TamaUniV2.Proof
  /Users/zefram/.tama/bin/tama check
  /Users/zefram/.tama/bin/tama build
  /Users/zefram/.tama/bin/tama test
  /Users/zefram/.tama/bin/tama audit
  git diff --check
  ```

  Expected: all pass; `tama test` reports 26/26 tests passing; `tama audit`
  reports 0 issues.

- [ ] **Step 6: Commit**

  Run:

  ```bash
  git add docs/agent-progress.md docs/spec-coverage.md tama.lock tama.toml verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean
  git commit -m "State sync clean-pool no-profit plainly"
  ```

---

## Task 3: Prove Successful Mint Arithmetic Directly From The Contract Call

**Security reason:** Minting is the only way LP supply increases. The specs
already prove that the formulas are safe once the arithmetic facts are known;
the missing strength is proving that a successful public `mint` established
those facts itself.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Modify: `docs/spec-coverage.md`
- Test mirror if needed: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Add first-mint formula claim**

  Add a public claim named
  `pair_first_mint_success_uses_canonical_liquidity_formula` in the mint
  section. Its comment must be:

  ```lean
  /--
  When the first `mint` succeeds, total LP supply equals the square-root
  liquidity measure and the caller receives exactly that amount minus
  `MINIMUM_LIQUIDITY`.

  This is the first-deposit fairness rule: the permanent lock is created once,
  and the first LP cannot own the entire supply.
  -/
  ```

  The proposition must quantify `toAddr : Address`, `s : ContractState`, and
  `result : ContractResult Uint256`; assume `result = (mint toAddr).run s` and
  a successful returned liquidity value; conclude the existing first-mint
  arithmetic equalities already used by the current
  `pair_mint_first_success_run_locks_minimum_liquidity_from_run` and
  `pair_mint_first_success_run_keeps_locked_share_from_run` proofs.

- [ ] **Step 2: Add later-mint formula claim**

  Add a public claim named
  `pair_later_mint_success_uses_minimum_pro_rata_liquidity`. Its comment must
  be:

  ```lean
  /--
  When a later `mint` succeeds, the minted LP amount is the smaller pro-rata
  share of the two deposited tokens.

  This prevents a liquidity provider from minting shares against only the
  cheaper side of the pool.
  -/
  ```

  The proposition must quantify `toAddr : Address`, `s : ContractState`, and
  `result : ContractResult Uint256`; assume `result = (mint toAddr).run s`, a
  successful returned liquidity value, nonzero existing supply, and existing
  reserves; conclude the same min-pro-rata relationship already used by
  `pair_mint_subsequent_success_run_preserves_existing_lp_share`.

- [ ] **Step 3: Prove both from existing mint execution facts**

  In `UniswapV2PairProof.lean`, prove each theorem by composing existing
  mint-success facts. Do not unfold the whole contract body if that reproduces
  kernel-depth failures. If a small private helper is needed, put it near the
  mint proofs and keep it unregistered in `tama.toml`.

- [ ] **Step 4: Verify and commit**

  Run the full command set from Task 2 Step 5.

  Commit:

  ```bash
  git add docs/agent-progress.md docs/spec-coverage.md tama.lock tama.toml verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean test/verity/UniswapV2Core.t.sol
  git commit -m "Prove mint liquidity formulas from successful calls"
  ```

---

## Task 4: Prove Successful Burn Arithmetic Directly From The Contract Call

**Security reason:** Burning is the only legitimate way to reduce raw pool K.
The specs should prove that successful burns pay the exact pro-rata amounts and
cannot redeem the permanently locked liquidity.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Modify: `docs/spec-coverage.md`

- [ ] **Step 1: Add burn payout claim**

  Add a public claim named `pair_burn_success_pays_exact_pro_rata_amounts`.
  Its comment must be:

  ```lean
  /--
  When `burn` succeeds, the paid token amounts are exactly the burned LP share
  of the pair's token balances before the payout.

  This is the LP redemption rule: a burner can receive only their pro-rata
  share, and the remaining LPs are not diluted.
  -/
  ```

  The proposition must quantify `toAddr : Address`, `s : ContractState`, and
  `result : ContractResult (Uint256 × Uint256)`; assume
  `result = (burn toAddr).run s` and successful returned token amounts; conclude
  the same pro-rata redemption equations used by
  `pair_burn_success_run_preserves_remaining_lp_share`.

- [ ] **Step 2: Add post-burn reserve claim**

  Add a public claim named `pair_burn_success_caches_post_redemption_balances`.
  Its comment must be:

  ```lean
  /--
  When `burn` succeeds, cached reserves become the token balances left after the
  redemption transfers.
  -/
  ```

  The proposition must quantify `toAddr : Address`, `s : ContractState`, and
  `result : ContractResult (Uint256 × Uint256)`; assume a successful public
  burn and the existing redemption arithmetic facts; conclude the existing
  reserve-write property from
  `pair_burn_success_run_updates_reserves_to_balances_from_run`.

- [ ] **Step 3: Prove without whole-function unfolding**

  Reuse the existing burn redemption and reserve-write facts. If the proof
  needs ordered guards, prove only the failing prefix privately and stop before
  external transfers.

- [ ] **Step 4: Verify and commit**

  Run the full command set from Task 2 Step 5.

  Commit:

  ```bash
  git add docs/agent-progress.md docs/spec-coverage.md tama.lock tama.toml verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean
  git commit -m "Prove burn redemption formulas from successful calls"
  ```

---

## Task 5: Prove Successful Swap Economic Checks Directly From The Contract Call

**Security reason:** Swap is the highest-risk entrypoint. The specs already
state the K rule and no-profit consequences, but some theorems still ask for
final-balance and K facts as inputs. Those facts should come from successful
`swap` execution whenever possible.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Modify: `docs/spec-coverage.md`
- Test mirror if needed: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Add final-balance accounting claim**

  Add a public claim named `pair_swap_success_accounts_for_input_and_output`.
  Its comment must be:

  ```lean
  /--
  When `swap` succeeds, the final token balances account for the optimistic
  output and any input paid back before the K check.
  -/
  ```

  The proposition must quantify `amount0Out amount1Out : Uint256`,
  `toAddr : Address`, `data : ByteArray`, `s : ContractState`, and
  `result : ContractResult Unit`; assume `result = (swap amount0Out amount1Out
  toAddr data).run s` and success; conclude the input/output balance equations
  currently used by `pair_swap_success_run_k_uses_final_balances_from_run`.

- [ ] **Step 2: Add K-check claim**

  Add a public claim named `pair_swap_success_charges_k_against_final_balances`.
  Its comment must be:

  ```lean
  /--
  When `swap` succeeds, the fee-adjusted constant-product check held on the
  final balances, after optimistic output and after any callback repayment.
  -/
  ```

  The proposition must quantify the same arguments as Step 1; assume successful
  `swap`; conclude the `FeeAdjustedKCheck` fact currently supplied as a premise
  to swap safety theorems.

- [ ] **Step 3: Add no-profit claim with fewer premises**

  Add or strengthen a public claim named
  `pair_swap_success_from_clean_pool_cannot_profit`. Its comment must be:

  ```lean
  /--
  When `swap` succeeds from a reachable clean pool, and caller value plus pair
  token-balance value is only redistributed at the starting spot price, the
  caller cannot finish richer.
  -/
  ```

  The proposition must quantify the swap arguments plus
  `callerValueBefore callerValueAfter : Nat`; assume successful `swap`,
  reachability, no starting surplus, and caller-plus-pair value redistribution;
  conclude `callerValueAfter ≤ callerValueBefore`.

- [ ] **Step 4: Verify and commit**

  Run the full command set from Task 2 Step 5.

  Commit:

  ```bash
  git add docs/agent-progress.md docs/spec-coverage.md tama.lock tama.toml verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean test/verity/UniswapV2Core.t.sol
  git commit -m "Prove swap K facts from successful calls"
  ```

---

## Task 6: Complete Exact Ordered Failures In Lean

**Security reason:** Guard order prevents side effects before failure. Exact
Lean reverts should prove both the reason and the unchanged state.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Check: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Add swap ordered failures**

  Add plain claims for:

  ```text
  swap rejects zero output before transfers.
  swap rejects output at or above reserves before transfers.
  swap rejects recipient equal to token0 or token1 before transfers.
  swap rejects no input after output/callback accounting.
  swap rejects fee-adjusted K violation.
  swap rejects final balances above uint112.
  ```

- [ ] **Step 2: Add burn ordered failures**

  Add plain claims for:

  ```text
  burn rejects zero LP liquidity or zero total supply before transfers.
  burn rejects zero redeemed token amount before transfers.
  burn rejects post-transfer balances above uint112.
  ```

- [ ] **Step 3: Add mint ordered failures**

  Add plain claims for:

  ```text
  mint rejects observed balances above uint112.
  first mint rejects liquidity at or below MINIMUM_LIQUIDITY.
  later mint rejects zero minted liquidity.
  mint rejects LP supply or LP balance overflow.
  ```

- [ ] **Step 4: Prove with ordered-prefix helpers**

  Do not unfold past the target guard. Create private proof helpers that reduce
  only the prefix needed to reach the guard, then expose the public theorem as a
  short exact run-result equality.

- [ ] **Step 5: Verify and commit**

  Run the full command set from Task 2 Step 5.

  Commit:

  ```bash
  git add docs/agent-progress.md docs/spec-coverage.md tama.lock tama.toml verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean test/verity/UniswapV2Core.t.sol
  git commit -m "Prove ordered Pair failures"
  ```

---

## Task 7: Prove External-Call Lock Safety

**Security reason:** Flash callbacks and ERC20 token transfers are external
calls. The pair must remain locked while those calls are in progress, so a
nested call cannot reenter a mutating Pair function.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Possibly modify: `verity/src/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Check: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: State the callback lock claim plainly**

  Add a public claim named `pair_flash_callback_runs_while_pair_is_locked`.
  Its comment must be:

  ```lean
  /--
  During a flash callback, the pair is locked.

  Any nested attempt to call `mint`, `burn`, `swap`, `skim`, or `sync` must see
  the closed lock and revert before changing state.
  -/
  ```

  The proposition must talk about the callback trace or ECM call site, not a
  helper function in the contract. It must imply the existing
  `pair_reentrancy_guard_blocks_all_mutating_entrypoints` condition for nested
  pair calls during callback execution.

- [ ] **Step 2: State the token-transfer lock claim plainly**

  Add a public claim named `pair_external_token_transfers_run_while_pair_is_locked`.
  Its comment must be:

  ```lean
  /--
  During token transfers performed by `burn`, `swap`, or `skim`, the pair is
  locked.

  A malicious token contract cannot use the transfer callback path to reenter a
  mutating Pair function.
  -/
  ```

  The proposition must talk about the token-transfer trace or ECM call site, not
  a helper function in the contract. It must imply the existing
  `pair_reentrancy_guard_blocks_all_mutating_entrypoints` condition for nested
  pair calls during token transfer execution.

- [ ] **Step 3: Choose proof route**

  First try to prove this from existing lock writes around the ECM calls. If the
  current ECM trace cannot express “lock is closed during the call,” add a
  small internal trace predicate in the common concrete model. Do not add a new
  contract helper or public ABI.

- [ ] **Step 4: Verify and commit**

  Run:

  ```bash
  lake build TamaUniV2.Proof.UniswapV2PairProof
  /Users/zefram/.tama/bin/tama test
  /Users/zefram/.tama/bin/tama audit
  git diff --check
  ```

  Commit:

  ```bash
  git add docs/agent-progress.md docs/spec-coverage.md tama.lock tama.toml verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean verity/src/TamaUniV2/Common/UniswapV2PairConcrete.lean test/verity/UniswapV2Core.t.sol
  git commit -m "Prove pair lock during external calls"
  ```

---

## Task 8: Add Event Correctness Claims For Successful AMM Calls

**Security reason:** Events are part of the canonical observable behavior. They
matter for indexers, routers, monitoring, and parity with Uniswap V2 behavior.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Check: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: State successful Mint event claim**

  ```text
  When `mint` succeeds, it emits Transfer for locked liquidity when first
  minting, Transfer for user LP tokens, Sync with the new reserves, and Mint
  with the deposited token amounts.
  ```

- [ ] **Step 2: State successful Burn event claim**

  ```text
  When `burn` succeeds, it emits Transfer for burned LP tokens, token transfer
  traces for both outputs, Sync with post-redemption reserves, and Burn with the
  redeemed amounts.
  ```

- [ ] **Step 3: State successful Swap event claim**

  ```text
  When `swap` succeeds, it emits token transfer traces for outputs, Sync with
  final balances, and Swap with output and inferred input amounts.
  ```

- [ ] **Step 4: State successful Sync event claim**

  ```text
  When `sync` succeeds, it emits Sync with the cached reserve values.
  ```

- [ ] **Step 5: Verify and commit**

  Run the full command set from Task 2 Step 5.

  Commit:

  ```bash
  git add docs/agent-progress.md docs/spec-coverage.md tama.lock tama.toml verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean test/verity/UniswapV2Core.t.sol
  git commit -m "Prove AMM event correctness"
  ```

---

## Task 9: Final Coverage Review

**Files:**
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`

- [ ] **Step 1: Review against canonical Uniswap behavior**

  Read local source and tests:

  ```bash
  rg -n "function|require|emit|uniswapV2Call|MINIMUM_LIQUIDITY|kLast" verity/src/TamaUniV2/UniswapV2Pair.lean verity/src/TamaUniV2/UniswapV2Factory.lean test/verity/UniswapV2Core.t.sol
  ```

  Check each behavior has one of:

  ```text
  proved in Lean
  mirrored in Foundry because it is an external boundary
  intentionally out of scope because fee-on/admin/metadata/permit are omitted
  ```

- [ ] **Step 2: Run full verification**

  ```bash
  lake build TamaUniV2.Proof
  /Users/zefram/.tama/bin/tama check
  /Users/zefram/.tama/bin/tama build
  /Users/zefram/.tama/bin/tama test
  /Users/zefram/.tama/bin/tama audit
  git diff --check
  ```

- [ ] **Step 3: Commit**

  ```bash
  git add docs/spec-coverage.md docs/agent-progress.md tama.lock
  git commit -m "Document final spec coverage"
  ```

---

## Self-Review

### Spec Coverage

- The plan covers the immediate readability problem first. That is necessary
  because public specs currently contain proof-jargon that obscures the
  security argument.
- The plan covers the most important remaining Pair security gap: successful
  mint, burn, and swap should establish their own arithmetic facts.
- The plan covers exact ordered failures, which are important because failure
  before side effects is a concrete security property.
- The plan covers external-call lock safety, the most important remaining
  reentrancy property beyond the already-proved closed-lock entrypoint facts.
- The plan covers event correctness, which is lower risk than K/reentrancy but
  important for canonical observable behavior.
- The Factory is not a major focus because its uniqueness, append-only, lookup,
  and failed-create atomicity properties are already well covered. The final
  review still checks it for drift.

### Placeholder Scan

No task uses prohibited placeholder phrases or ellipsis placeholders. Future
theorem bodies are specified by plain contract claims plus the exact existing
facts they must eliminate or conclude; during execution, each claim must be
written as a concrete Lean proposition before any proof work starts.

### Type And Naming Consistency

- `ContractState`, `ContractResult`, `Uint256`, `Address`, `ByteArray`,
  `PairWorldReachable`, `PairWorldSurplus0`, `PairWorldSurplus1`, and
  `PairWorldBalanceSpotValueNum` are existing project names.
- The proposed public names intentionally drop `_from_run` where the rename is
  cheap. If a rename creates churn in Tama markers or generated metadata, keep
  the old identifier temporarily but make the prose plain.
- The plan does not require changing contract source or adding public helper
  functions.

### Plan Review Verdict

The plan is coherent with the current spec standard. The only risk is scope:
Tasks 3 through 7 are proof-heavy and should be executed in separate commits.
The next immediate task should be Task 1, then Task 2 only after the prose is
plain enough that the theorem reads like a contract guarantee rather than proof
plumbing.
