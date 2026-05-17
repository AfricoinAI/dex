# Invariant-First Uniswap V2 Spec Plan

This is the active plan. It supersedes the older remediation and
executable-success plans that were removed from `docs/superpowers/plans`.

## Goal

Build a formal spec suite that lets us reason that the supported fee-off
Uniswap V2 Pair and Factory are correct, complete, and secure by logical
deduction from concise properties.

This plan is governed by the current spec standard: specs should be small,
composable statements about invariants, transition constraints, sequence-level
economics, and narrow bridges from canonical public entrypoints to those facts.

## Ground Rules

- API parity is a build/review constraint, not a formal spec category.
- Public specs should be short invariants, preservation lemmas, guard/revert
  facts, bridge facts, and economic safety statements.
- Executable run facts may exist as private or narrow bridge lemmas, but should
  not become large public aggregate specs for whole functions.
- Do not change contract source or public model functions for proof convenience.
- Do not add axioms or trust surfaces for internal logic.
- Use Tamago's installed sqrt facts; do not duplicate sqrt proofs.
- `docs/agent-progress.md` is append-only historical context. Add timestamped
  checkpoints at the end only.

## Canonical Behavior Sources

- Pair source: https://github.com/Uniswap/v2-core/blob/master/contracts/UniswapV2Pair.sol
- Pair tests: https://github.com/Uniswap/v2-core/blob/master/test/UniswapV2Pair.spec.ts
- Factory source: https://github.com/Uniswap/v2-core/blob/master/contracts/UniswapV2Factory.sol
- Factory tests: https://github.com/Uniswap/v2-core/blob/master/test/UniswapV2Factory.spec.ts

The implementation intentionally omits canonical fee-on/admin behavior:
protocol-fee minting, `feeTo`, `feeToSetter`, LP `name`, LP `symbol`, and
`permit`.

## Work Plan

- [x] **1. Restore a coherent public spec/proof manifest**

  Align `verity/spec`, `verity/proof`, and `tama.toml` so every listed public
  obligation exists, is intentionally named, and is either proved or clearly
  mirrored. Remove stale manifest entries for obligations that no longer exist.

  2026-05-16 19:11 PDT checkpoint: `lake build
  TamaUniV2.Proof.UniswapV2PairProof`, `tama check`, `tama build`, and
  `tama audit` pass after restoring missing Pair spec predicates and keeping the
  bridge-heavy predicates scoped to proof plumbing.

- [ ] **2. Expose global closed-world invariants**

  Public specs should state that every reachable Pair world preserves reserve
  backing, uint112 bounds, minimum-liquidity locking, LP-supply coherence, and
  lock restoration at call boundaries. These should be finite-trace invariants,
  not one large function postcondition.

  2026-05-16 20:17 PDT checkpoint: Pair now has one-step, reachable-state, and
  arbitrary finite-path preservation from any good state, plus backed-reserve,
  uint112, minimum-liquidity, LP-supply, and no-burn K/nonprofit path facts.
  Remaining work here is to connect lock restoration across all concrete public
  success paths, not just selected entrypoints.

- [x] **3. Strengthen action transitions**

  Add concise specs for each action family:

  - Mint: first-mint lock and subsequent min pro-rata liquidity.
  - Burn: pro-rata redemption and reserve update to post-transfer balances.
  - Swap: input inference, fee-adjusted K, raw K nondecrease, and reserve update.
  - Skim: surplus-only transfer and unchanged reserves.
  - Sync: reserves become observed balances subject to uint112 bounds.

  2026-05-16 22:32 PDT checkpoint: the closed-world action family specs now
  cover mint reserve/K/supply effects, burn reserve/supply/pro-rata effects,
  swap input/output/K/reserve/supply effects, skim surplus/K/supply effects,
  sync reserve/K/supply effects, and the one-step K classifier that any raw K
  decrease from a good state must be a burn.

- [ ] **4. Bridge real entrypoints to transitions**

  Prove successful public `mint`, `burn`, `swap`, `skim`, and `sync` runs imply
  the corresponding closed-world transition. Keep bridge lemmas narrow; split
  same-block, elapsed/TWAP, and flash-callback cases only as proof structure,
  not as user-facing spec categories.

- [ ] **5. Add TWAP/oracle specs**

  For every reserve-update path, prove cumulative prices update exactly when
  elapsed time is positive and old reserves are nonzero, preserve otherwise, and
  use canonical uint32 timestamp wrap behavior.

  2026-05-16 21:34 PDT checkpoint: Pair now has small public oracle arithmetic
  specs for the two meaningful reserve-update cases: same-timestamp cumulative
  immutability, and elapsed fixed-point price-time accumulation with nonzero old
  reserves. Remaining work is to bridge every concrete public reserve-update
  path to those arithmetic facts without adding contract helpers.

- [ ] **6. Add flash-swap specs**

  Prove callback iff `data` is nonempty, callback revert is atomic, the
  reentrancy lock is held through callback execution, and the K check is applied
  after callback-visible token balance changes.

- [ ] **7. Complete the ordered revert matrix**

  Add exact run-result revert specs for canonical guard priority in mint, burn,
  swap, skim, sync, and factory. Revert specs should prove the exact payload and
  original-state frame.

- [ ] **8. Add sequence-level economic safety**

  Strengthen the closed-world model with a caller ledger so any finite sequence
  with identical LP supply before and after cannot yield positive caller profit
  at the initial spot price, excluding exogenous gifts to the caller.

  2026-05-16 20:17 PDT checkpoint: closed-world no-burn paths now prove K
  nondecrease and same-LP-supply spot-price no-profit. The full caller-ledger
  theorem for arbitrary mint/burn round trips remains open.

  2026-05-16 22:32 PDT checkpoint: reachable same-LP-supply paths from positive
  reachable states now prove raw K nondecrease and no spot-price profit using
  LP-normalized K, so mint/burn round trips are covered at the pool-value level.
  The full caller-ledger theorem remains open if we decide to model external
  caller holdings directly.

- [x] **9. Add factory-world invariants**

  Model pair creation as a finite factory trace and prove sorted-token
  uniqueness, symmetric `getPair`, append/length consistency, nonzero create
  boundary, initialization boundary, `PairCreated`, and failed-create atomicity.

  2026-05-16 22:32 PDT checkpoint: the factory closed-world model now proves
  one-step, reachable, and arbitrary finite-path preservation from any good
  state, sorted nonzero entries, sorted-pair uniqueness, symmetric membership,
  append-only creation, existing-pair preservation, and count/list consistency.
  Executable `createPair` success and failure storage/event behavior is covered
  separately by concrete specs.

- [ ] **10. Verify and commit in coherent slices**

  After each slice run focused `lake build`. Before claiming completion run
  `lake build`, `tama check`, `tama build`, `tama test`, and `tama audit`.
  Commit related spec/proof/doc changes together.

## Non-Goals

- Do not reintroduce formal API parity specs.
- Do not resurrect old aggregate executable-success plans.
- Do not add proof-convenience helper functions to the public contract or
  public ABI. Same-timestamp and elapsed oracle cases are valid public specs
  when stated as mathematical reserve-update behavior.
