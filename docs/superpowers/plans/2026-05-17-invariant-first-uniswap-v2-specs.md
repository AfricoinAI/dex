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
- Spec modules should read like an assurance argument. Each section needs to
  explain the security/correctness role of the facts that follow, so a reader
  can see why the collection implies the fee-off pair/factory are correct,
  complete, and secure.
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

- [x] **0. Keep the spec narrative coherent**

  This is an ongoing hygiene constraint rather than a separate proof milestone.
  The Pair and Factory spec files should read like papers: start from the
  contract's trust boundaries, build local storage/accounting facts, bridge real
  entrypoints into concise ghost transitions, then state global finite-history
  invariants and economic consequences.

  2026-05-17 03:25 PDT checkpoint: after user clarification, this standard is
  explicit in the active plan. Future spec additions should include
  plain-language section/comment blocks and avoid aggregate function summaries.

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

  2026-05-17 00:42 PDT checkpoint: added the reader-facing reachable-path
  reserve-backing theorem. It states the invariant in the natural finite-trace
  form: starting from any reachable pool state, every finite successful modeled
  history ends with cached reserves no larger than the pair's token balances.

  2026-05-17 00:45 PDT checkpoint: added the matching reader-facing
  reachable-path uint112 and minimum-liquidity-lock invariants. The invariant
  layer now has direct finite-trace statements for reserve backing, reserve
  bounds, and locked LP supply, rather than requiring readers to mentally
  compose reachability with good-state preservation.

  2026-05-17 01:25 PDT checkpoint: added the reader-facing reachable
  positive-supply invariant. From any reachable nonempty pool, every finite
  successful modeled history remains nonempty, making the minimum-liquidity
  argument explicit at the trace level.

  2026-05-17 05:33 PDT checkpoint: adding the token-side positive-balance
  consequence of the positive-reserve and reserve-backing invariants. From any
  reachable nonempty pool, every finite successful modeled history leaves both
  actual token balances positive.

  2026-05-17 11:40 PDT checkpoint: added explicit trace closure for the
  closed-world Pair model. If a state is reachable and a finite successful path
  starts there, the endpoint is reachable too, making later reachable-state
  invariants apply directly after appended histories.

  2026-05-17 01:38 PDT checkpoint: added the finite-history LP supply
  firewall. A path containing no mint and no burn preserves total LP supply and
  locked liquidity exactly, with a reachable reader-facing theorem for the same
  statement.

  2026-05-17 03:00 PDT checkpoint: adding the one-step LP supply firewall that
  the finite-history theorem iterates. Any successful modeled action other than
  mint or burn preserves total LP supply and the permanently locked liquidity
  amount.

  2026-05-17 03:09 PDT checkpoint: adding the directional no-burn supply
  invariant. Any successful modeled action other than burn cannot decrease LP
  supply, and therefore every finite successful no-burn history preserves or
  increases total LP supply.

  2026-05-17 03:13 PDT checkpoint: adding the symmetric no-mint supply
  invariant. Any successful modeled action other than mint cannot increase LP
  supply, and therefore every finite successful no-mint history preserves or
  decreases total LP supply.

  2026-05-17 03:17 PDT checkpoint: adding locked-liquidity monotonicity. From
  any good/reachable PairWorld state, successful modeled histories cannot
  reduce the permanently locked liquidity amount.

  2026-05-17 01:43 PDT checkpoint: added the reader-facing no-liquidity
  no-extraction corollary. Reachable paths with no mint and no burn now prove
  no spot-value extraction directly by combining unchanged LP supply with the
  existing same-supply theorem.

  2026-05-17 01:54 PDT checkpoint: added the positive-reserve invariant slice.
  Any reachable pool with positive LP supply now proves positive reserves on
  both token sides, and finite successful modeled histories from such pools
  preserve that nondegenerate reserve shape. This makes the spot-price
  preconditions in the economic layer derivable from reachability plus
  nonempty supply.

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

  2026-05-17 00:51 PDT checkpoint: added the reachable finite-trace no-burn K
  theorem. From any reachable pool state, a successful modeled path containing
  no burn cannot decrease cached K, making the one-step K classifier visible at
  the history level.

  2026-05-17 02:26 PDT checkpoint: adding the contrapositive finite-history K
  classifier. If a reachable successful path ends with lower cached K, that
  endpoint cannot also be reached by a burn-free history, making "K loss
  requires LP redemption" explicit for readers.

  2026-05-17 03:31 PDT checkpoint: added the common-case no-mint/no-burn K
  theorem. Reachable finite histories made only of LP bookkeeping, donations,
  swaps, skim, and sync cannot decrease cached K; this is the K-side companion
  to the common-case no-extraction theorem.

  2026-05-17 05:01 PDT checkpoint: strengthened the swap K layer so raw K
  nondecrease is derived from the canonical fee-adjusted K check once reserves
  equal final balances. The public swap bridge no longer takes raw K
  nondecrease as an input premise.

  2026-05-17 05:07 PDT checkpoint: removed raw K nondecrease from the ghost
  swap transition itself. The closed-world model now assumes the canonical
  fee-adjusted K guard only, and every raw-K invariant proof derives raw K from
  that guard plus the reserve-to-final-balance equations.

  2026-05-17 12:20 PDT checkpoint: added the one-swap no-extraction theorem.
  From a good live pool with a defined spot price, a valid swap cannot leave the
  pool worth less at the starting spot price. The proof reuses the existing
  finite-history no-profit theorem through a one-step path, rather than
  unfolding the public swap entrypoint.

  2026-05-17 12:31 PDT checkpoint: added the reachable nonempty-pool form of
  the same one-swap theorem. Reachability supplies the good-state and
  positive-reserve premises, so the public statement reads directly: a valid
  swap from a reachable nonempty pool cannot reduce pool value at the starting
  spot price.

  2026-05-17 18:04 PDT checkpoint: added executable mint/burn supply-movement
  bridges. Successful initial and later public `mint` runs now connect to the
  closed-world strict supply-increase theorem, and successful public `burn`
  runs connect to exact LP-supply reduction by the burned liquidity.

  2026-05-17 18:08 PDT checkpoint: added the executable successful-swap K
  bridge. A successful public `swap`, once connected to the same final-balance
  and fee-adjusted-K facts used by the swap transition, now proves raw cached K
  cannot decrease.

  2026-05-17 18:11 PDT checkpoint: added executable first/subsequent mint K
  bridges. Successful public `mint` runs now prove raw cached K cannot decrease
  once connected to their first-mint or pro-rata later-mint arithmetic facts.

  2026-05-17 18:16 PDT checkpoint: split out the executable burn reserve-write
  fact from the larger burn oracle bridge. Successful public `burn` runs now
  state directly that cached reserves are set to post-transfer token balances
  once connected to their redemption arithmetic facts.

  2026-05-17 18:20 PDT checkpoint: split out the executable first/subsequent
  mint reserve-write facts from the larger mint oracle bridge. Successful
  public `mint` runs now state directly that cached reserves are set to the
  observed token balances once connected to their arithmetic facts.

  2026-05-17 18:24 PDT checkpoint: split out the executable swap reserve-write
  fact from the larger swap oracle bridge. Successful public `swap` runs now
  state directly that the final post-output, post-callback balances are cached
  as reserves once the final-balance/K facts are supplied.

  2026-05-17 07:59 PDT checkpoint: added the reserve-change classifier. Cached
  reserves can change only through mint, burn, swap, or sync; share
  bookkeeping, direct donation, and skim cannot secretly rewrite router-visible
  reserves.

  2026-05-17 08:06 PDT checkpoint: lifted reserve-change isolation to finite
  histories with a ghost-only no-reserve-update path. Any history with no mint,
  burn, swap, or sync preserves cached reserves exactly.

  2026-05-17 08:12 PDT checkpoint: added the cached economic corollary of
  finite reserve isolation. No-reserve-update histories preserve cached K and
  reserve-denominated spot value; the statement intentionally avoids actual
  token-balance value because donation and skim affect surplus.

  2026-05-17 08:34 PDT checkpoint: added the first-mint locked-share
  consequence. The minimum-liquidity lock is now stated not only as a supply
  formula, but as the security fact that the first LP cannot own the entire LP
  supply.

  2026-05-17 08:35 PDT checkpoint: adding the sync surplus/K converse. A good
  closed-world sync that increases cached K must be accounting pre-existing
  surplus above reserves, complementing the zero-surplus theorem that sync
  preserves K exactly.

  2026-05-17 08:40 PDT checkpoint: adding the companion skim surplus-value
  theorem. At the initial spot price, skim removes exactly pre-existing surplus
  token-balance value and leaves accounted reserve value untouched.

  2026-05-17 08:47 PDT checkpoint: adding the balanced-skim no-op theorem.
  From a good zero-surplus state, skim must preserve token balances, cached
  reserves, LP supply, and locked liquidity exactly.

  2026-05-17 09:01 PDT checkpoint: adding the balanced-sync no-op theorem.
  From a good zero-surplus state, sync must preserve token balances, cached
  reserves, LP supply, and locked liquidity exactly.

  2026-05-17 09:05 PDT checkpoint: adding the `skim`/`sync` no-change
  theorem. The action family `{skim, sync}` preserves a good balanced pool's
  token balances, cached reserves, LP supply, and locked liquidity exactly.

  2026-05-17 09:12 PDT checkpoint: adding the finite-history `skim`/`sync`
  no-change theorem. Any path made only of `skim` and `sync` preserves a good
  balanced pool's token balances, cached reserves, LP supply, and locked
  liquidity exactly.

  2026-05-17 09:20 PDT checkpoint: adding the balanced LP-bookkeeping plus
  `skim`/`sync` path theorem. Any path made only of LP share bookkeeping plus
  `skim` and `sync` preserves a good balanced pool's token balances, cached
  reserves, LP supply, and locked liquidity exactly.

  2026-05-17 14:25 PDT checkpoint: added shared `skim`/`sync` value facts.
  `sync` is now stated directly as custody-preserving accounting, and the
  shared `skim`/`sync` theorem says either action cannot increase actual
  token-balance value at the starting spot price.

  2026-05-17 14:30 PDT checkpoint: lifted the shared `skim`/`sync` value
  nonincrease theorem to finite histories. A path made only of LP
  approval/transfer/transferFrom bookkeeping plus `skim`/`sync` cannot increase
  actual token-balance value at the starting spot price.

  2026-05-17 14:35 PDT checkpoint: added the reachable-state version of the
  same theorem, so readers can cite reachability directly instead of separately
  proving the good-state invariant.

  2026-05-17 14:39 PDT checkpoint: added the shared reserve-write theorem.
  Every mint, burn, swap, or sync reserve write sets cached reserves to actual
  token balances, making the common accounting rule explicit for later bridge
  and oracle arguments.

  2026-05-17 14:44 PDT checkpoint: added the shared concrete reserve-write
  oracle bridge. Once a mint, burn, swap, or sync transition is connected to a
  concrete state, the proof now exposes both the reserve-to-balance write fact
  and all three generic TWAP update cases together.

  2026-05-17 10:49 PDT checkpoint: added executable LP-bookkeeping storage
  frame facts. The actual `approve`, `transfer`, and `transferFrom` runs may
  update LP allowance/balance maps and emit ERC20 events, but they cannot
  change scalar AMM storage such as reserves, price accumulators, total supply,
  token identities, or lock state.

  2026-05-17 10:54 PDT checkpoint: added executable LP-bookkeeping token-world
  frame facts. Replaying the pair-local ERC20 transfer trace across actual
  `approve`, `transfer`, and `transferFrom` runs leaves token0/token1 balances
  unchanged; LP events are local share-ledger events, not underlying asset
  movement.

  2026-05-17 11:04 PDT checkpoint: added the executable `skim` token-balance
  bridge. A successful real `skim` run, replayed through the pair-local ERC20
  transfer trace model, moves exactly the token0/token1 surplus above cached
  reserves from the pair to the recipient.

  2026-05-17 11:16 PDT checkpoint: added the reusable pair-token transfer
  event replay fact. The trace model now states directly that a recorded
  safe-transfer event moves exactly the recorded amount between the recorded
  accounts, which future `burn` and `swap` bridges can cite.

  2026-05-17 10:04 PDT checkpoint: added the economic reading of the balanced
  LP-bookkeeping plus `skim`/`sync` path theorem. The public spec now states
  directly that any such history from a clean balanced pool preserves actual
  token-balance value at the initial spot price.

  2026-05-17 10:09 PDT checkpoint: added the sibling clean-state theorem.
  Histories made only of LP bookkeeping plus `skim`/`sync` from a good
  zero-surplus pool preserve zero surplus, making the no-extraction value
  corollary read as a consequence of a directly stated invariant.

  2026-05-17 10:11 PDT checkpoint: adding the cached-K reading of the same
  no-change theorem. Histories made only of LP bookkeeping plus `skim`/`sync`
  from a clean balanced pool preserve the reserve product exactly, so later
  economic arguments can cite unchanged K directly.

  2026-05-16 22:43 PDT checkpoint: the closed-world burn step was tightened to
  match executable burn success by requiring positive redeemed amounts, positive
  burned liquidity, and positive pre-burn supply. A new token-side lock theorem
  proves a valid burn from a good positive-token state cannot empty either token
  balance.

  2026-05-17 12:38 PDT checkpoint: added the reachable form of the burn
  positive-balance theorem. From any reachable nonempty pool, a valid burn cannot empty
  either token side; reachability supplies the good-state and pre-burn token
  balance premises.

  2026-05-16 22:46 PDT checkpoint: mint/burn ratio safety is now stated in
  LP-share terms too. Positive-supply mints cannot dilute existing LPs, and
  burns cannot over-extract from remaining LPs, because both preserve or improve
  reserve product per squared LP supply.

- [ ] **4. Bridge real entrypoints to transitions**

  Prove successful public `mint`, `burn`, `swap`, `skim`, and `sync` runs imply
  the corresponding closed-world transition. Keep bridge lemmas narrow; split
  same-block, elapsed/TWAP, and flash-callback cases only as proof structure,
  not as user-facing spec categories.

  2026-05-17 02:20 PDT checkpoint: do not add more public executable-success or
  ordered-prefix obligations by directly unfolding whole entrypoints. Attempts
  to prove `sync` lock restoration and burn insufficient-liquidity this way
  expanded into inline oracle/transfer tails. The next bridge work should first
  introduce proof-local adapters for the shared reserve-update and ordered-guard
  prefixes, then expose only short reader-facing obligations.

  2026-05-17 02:57 PDT checkpoint: adding the reader-facing Pair reentrancy
  invariant by composing existing exact lock-gate proofs. This avoids any new
  trust surface: when `unlocked != 1`, `mint`, `burn`, `swap`, `skim`, and
  `sync` all return the exact `LOCKED` revert before side effects.

  2026-05-17 12:55 PDT checkpoint: added the two-transfer token trace replay
  fact. Replaying the two underlying ERC20 transfer events used by burn and
  two-sided swap accounting moves exactly the two token amounts from the pair
  account to the recipient, assuming distinct tokens and a recipient different
  from the pair.

  2026-05-17 14:14 PDT checkpoint: attempted a direct public `sync` success
  lock-restoration proof and backed it out after Lean hit kernel-depth limits
  while unfolding the oracle/update tail. The next concrete success-side lock
  work should first factor the shared reserve-update tail into a proof-local
  adapter, then expose only the short public property.

  2026-05-17 14:50 PDT checkpoint: added the narrow public `sync`
  success-to-oracle bridge by composing the existing successful-run transition
  proof with the shared concrete reserve-write rule. This connects a real
  successful `sync` call to reserve-to-balance writes and the generic TWAP
  arithmetic facts without unfolding the whole entrypoint again.

  2026-05-17 15:00 PDT checkpoint: extended the same bridge shape to first
  mint, subsequent mint, burn, and swap. These theorems stay narrow: they
  compose successful-run transition facts with the shared reserve-write/oracle
  rule once each action's concrete arithmetic premises are available.

  2026-05-17 16:04 PDT checkpoint: tightened the `sync` executable bridge.
  Successful `sync` now derives the open-lock fact and uint112 observed-balance
  bounds from exact revert facts and therefore refines the closed-world sync
  transition without asking readers to supply those premises separately.

  2026-05-17 16:13 PDT checkpoint: added success-side lock bridges for mint,
  burn, swap, and skim, matching the existing `sync` bridge. Successful `mint`
  also now derives the uint112 observed-balance bounds from exact overflow
  revert facts.

  2026-05-17 16:23 PDT checkpoint: added first-mint and subsequent-mint
  successful-run bridges that use those derived premises. A reader can now cite
  a successful real `mint` run as a closed-world mint transition without
  separately assuming the lock gate or uint112 reserve bounds.

  2026-05-17 16:28 PDT checkpoint: extended that successful-run bridge to
  first/subsequent mint reserve-write and oracle facts. The mint TWAP bridge
  now exposes only the economic arithmetic premises; successful execution
  supplies the shared gates.

  2026-05-17 16:40 PDT checkpoint: did the same cleanup for `sync`. The
  reader-facing successful-run sync oracle fact now follows directly from
  success, with lock and uint112 bounds derived by the earlier exact-revert
  bridge.

  2026-05-17 16:39 PDT checkpoint: a direct exact-run proof for the next swap
  guard, insufficient liquidity, was attempted and backed out uncommitted after
  reproducing the known kernel-depth failure. Future ordered swap reverts need
  a proof-local ordered-prefix adapter before public obligations are added.

  2026-05-17 16:45 PDT checkpoint: added successful-run `skim` bridges. Success
  now derives the reserve-backing premises from exact under-reserve reverts,
  proves final lock restoration, and connects the run to the closed-world skim
  transition without extra reader-supplied execution premises.

  2026-05-17 17:06 PDT checkpoint: added the success-side nonzero-output swap
  bridge. It composes existing exact-run facts instead of unfolding the full
  swap tail: if a real `swap` succeeds, it cannot be the zero-output case.

  2026-05-17 17:09 PDT checkpoint: full verification passed for that bridge:
  focused Pair proof, whole `lake build TamaUniV2.Proof`, `tama check`, `tama
  build`, `tama test` (26/26), `tama audit` (0 issues), and `git diff --check`.

  2026-05-17 17:10 PDT checkpoint: next bridge target is the direct
  composition of that fact into swap refinement/oracle specs, so readers no
  longer need to supply the nonzero-output premise separately for successful
  real swaps.

  2026-05-17 17:15 PDT checkpoint: implemented and verified that target.
  Successful swap-to-model and swap-oracle bridge statements now discharge the
  nonzero-output guard from the actual run while keeping the post-callback
  balance and K facts explicit.

  2026-05-17 17:16 PDT checkpoint: next target is the economic consequence of
  that bridge: a successful real swap, once supplied with final-balance and K
  facts, should imply caller no-profit directly without a separate modeled-step
  premise.

  2026-05-17 17:19 PDT checkpoint: implemented and verified that economic
  consequence. Successful real swaps now connect directly to the caller
  no-profit theorem once their post-callback balance and K facts are supplied.

  2026-05-17 17:23 PDT checkpoint: cleaned this active plan and related
  reader-facing spec/coverage/manifest text to say `skim`/`sync` directly
  instead of using the confusing "passive reconciliation" wording. Historical
  progress entries were left append-only.

  2026-05-17 17:32 PDT checkpoint: added and fully verified the burn economic
  bridge. A successful real `burn`, once connected to its concrete redemption
  facts, now directly proves that remaining LP backing is preserved or
  improved (`K / totalSupply^2` does not decrease).

  2026-05-17 17:45 PDT checkpoint: added and fully verified the matching
  nonempty-pool mint economic bridge. A successful later `mint`, once connected
  to its pro-rata arithmetic facts, now directly proves that existing LP backing
  is not diluted.

  2026-05-17 17:50 PDT checkpoint: added and fully verified a successful-swap
  supply bridge. A successful `swap`, once connected to its final-balance/K
  facts, now directly proves that LP total supply and locked liquidity are
  unchanged.

  2026-05-17 17:55 PDT checkpoint: added and fully verified the matching
  successful `skim`/`sync` supply bridges. Successful cleanup/accounting calls
  now directly prove LP total supply and locked liquidity are unchanged.

- [x] **5. Add TWAP/oracle specs**

  For every reserve-update path, prove cumulative prices update exactly when
  elapsed time is positive and old reserves are nonzero, preserve otherwise, and
  use canonical uint32 timestamp wrap behavior.

  2026-05-16 21:34 PDT checkpoint: Pair now has small public oracle arithmetic
  specs for the two meaningful reserve-update cases: same-timestamp cumulative
  immutability, and elapsed UQ112x112 price-time accumulation with nonzero old
  reserves. Remaining work is to bridge every concrete public reserve-update
  path to those arithmetic facts without adding contract helpers.

  2026-05-16 23:42 PDT checkpoint: the no-op side of the elapsed branch is now
  also covered as a public arithmetic spec: if the timestamp comparison branch
  is entered but elapsed time or either old reserve is zero, cumulative prices
  remain unchanged. Remaining work is still bridge-oriented: prove the public
  reserve-update entrypoints reuse these arithmetic facts.

  2026-05-17 05:31 PDT checkpoint: lifted the TWAP arithmetic specs into
  generic reserve-update obligations before the `sync` bridge names. This makes
  the Pair spec read as contract-level oracle behavior shared by mint, burn,
  swap, and sync; the still-open work is executable bridge coverage for the
  mint/burn/swap reserve-update paths.

  2026-05-17 14:50 PDT checkpoint: the `sync` side of that executable bridge
  now exists as a short public theorem. Remaining oracle bridge work should
  focus on mint, burn, and swap, preferably through proof-local adapters that
  expose the shared reserve-update suffix rather than full-entrypoint
  unfoldings.

  2026-05-17 15:00 PDT checkpoint: the mint, burn, and swap bridge facts are
  now present too. Remaining TWAP work, if pursued, should be about deriving
  more concrete arithmetic premises from actual successful runs, not restating
  the reserve-update rule.

- [ ] **6. Add flash-swap specs**

  Prove callback iff `data` is nonempty, callback revert is atomic, the
  reentrancy lock is held through callback execution, and the K check is applied
  after callback-visible token balance changes.

  2026-05-16 22:50 PDT checkpoint: the callback `data.length > 0` gate is now
  stated at the ECM compile-template boundary, which is where this behavior
  currently lives. The closed-world swap model also states the post-output plus
  inferred-input balance equations used by the K check. Callback failure
  atomicity and in-callback lock observations still need either an explicit
  Lean callback trace model or mirrored runtime-boundary coverage.

  2026-05-17 02:31 PDT checkpoint: strengthening the callback boundary spec so
  the gated ECM body is not just present under `data_length > 0`, but also
  encodes the canonical `uniswapV2Call` selector, sender, output amounts, and
  recipient target call.

  2026-05-17 02:37 PDT checkpoint: adding the callback failure boundary fact.
  The ECM-generated body checks the low-level call result, copies returndata,
  and executes `revert` on failure; this is the Lean-side evidence that callback
  failure is not swallowed.

  2026-05-17 16:02 PDT checkpoint: added the compact flash-swap K theorem.
  The closed-world swap section now states directly that the fee-adjusted K
  check uses the final post-output, post-repayment balances, and those same
  balances account for inferred input.

- [ ] **7. Complete the ordered revert matrix**

  Add exact run-result revert specs for canonical guard priority in mint, burn,
  swap, skim, sync, and factory. Revert specs should prove the exact payload and
  original-state frame.

  2026-05-16 23:08 PDT checkpoint: swap now has a public Lean spec/proof and
  exact Foundry mirror for the zero-output guard after the lock gate.
  Insufficient-liquidity and invalid-recipient checks have exact Foundry
  revert-message coverage, but their public Lean obligations are deferred until
  the ordered-prefix proof is decomposed without monolithic swap unfolding.

  2026-05-17 02:20 PDT checkpoint: the same warning applies to burn. A direct
  proof attempt for the post-lock insufficient-liquidity guard also expanded
  past the target guard. Build an ordered-prefix adapter before reintroducing
  these public Lean obligations.

- [x] **8. Add sequence-level economic safety**

  Prove that finite successful Pair histories cannot extract spot-priced value
  from the pool when LP supply starts and ends at the same value. The Pair ghost
  model tracks pool-side balances/reserves and LP supply, not arbitrary external
  wallets, so the sound theorem is pool-value no-extraction at the initial spot
  price. A detailed external-wallet ledger is not a standing task unless it is
  modeled explicitly and tied to actual action-level token/LP ownership changes.

  2026-05-16 20:17 PDT checkpoint: closed-world no-burn paths now prove K
  nondecrease and same-LP-supply spot-price no-profit.

  2026-05-16 22:32 PDT checkpoint: reachable same-LP-supply paths from positive
  reachable states now prove raw K nondecrease and no spot-price profit using
  LP-normalized K, so mint/burn round trips are covered at the pool-value level.

  2026-05-17 00:20 PDT checkpoint: added a reader-facing pool-value theorem for
  the same economic fact. For any reachable positive-supply finite path that
  returns to the same LP supply, the final pool value at the initial spot price
  is at least the initial pool value. This keeps the public obligation short but
  makes the no-profit conclusion easier to read.

  2026-05-17 00:38 PDT checkpoint: added the reachable LP-share backing theorem.
  From any reachable positive-supply pool, every finite successful path preserves
  or improves reserve product per squared LP supply. This is the concise global
  mint/burn ratio statement that the same-supply no-profit theorem builds on.

  2026-05-17 00:47 PDT checkpoint: after comparing Tamago's closed-world wealth
  pattern, added a caller-facing no-extraction theorem name for the existing
  same-LP-supply pool-value result. The Pair model tracks pool-side value rather
  than arbitrary external wallets, so the theorem states the sound closed-world
  claim directly: same-LP-supply reachable histories cannot extract positive
  spot-value from the pool at the initial price.

  2026-05-17 02:00 PDT checkpoint: strengthened the reader-facing same-supply
  no-extraction theorem so reachable positive supply is enough. Positive
  reserve premises are now discharged by the invariant layer, making the
  economic story read as: nonempty reachable pool, same ending LP supply, no
  spot-value extraction.

  2026-05-17 02:10 PDT checkpoint: strengthened the no-mint/no-burn
  no-extraction corollary the same way. The common operational history now
  reads directly as: reachable nonempty pool, no mint, no burn, no spot-value
  extraction.

  2026-05-17 04:01 PDT checkpoint: added the token1-denominated no-profit
  theorem. This is the same pool-value comparison as the no-extraction theorem,
  but stated in the initial `reserve1 / reserve0` spot-price denomination that
  a reader would use to reason about caller profit, with the expression scaled
  by `reserve0` to avoid division.

  2026-05-17 05:15 PDT checkpoint: adding the actual-token-balance
  no-extraction theorem. It keeps the statement truthful by requiring a
  balanced start state with no surplus over cached reserves; donated surplus is
  an external gift and can be removed by `skim`.

  2026-05-17 05:20 PDT checkpoint: adding the common no-mint/no-burn corollary
  for actual token balances. The LP-supply firewall supplies same-supply, so
  the statement reads directly as balanced start plus no liquidity issuance or
  redemption implies no token-balance value extraction.

  2026-05-17 14:05 PDT checkpoint: added the caller no-profit consequence for
  zero-surplus same-LP-supply histories. The spec states the external-wallet
  reading directly: if caller value plus pair token-balance value is unchanged
  except for redistribution at the initial spot price, then the caller cannot
  finish with more value.

  2026-05-17 14:16 PDT checkpoint: added the common no-mint/no-burn caller
  no-profit consequence. The LP-supply firewall supplies same-supply, so a
  zero-surplus history with no liquidity issuance or redemption cannot increase
  caller spot value when caller-plus-pair value is only redistributed.

  2026-05-17 15:55 PDT checkpoint: added the reserve-value caller no-profit
  consequence for arbitrary same-LP-supply histories. If caller-plus-pool
  cached spot value is merely redistributed, the caller cannot finish richer;
  token-balance versions remain the zero-surplus facts above.

  2026-05-17 16:02 PDT checkpoint: added the common no-mint/no-burn form of
  the reserve-value caller theorem. Ordinary non-liquidity histories now expose
  a direct caller no-profit statement without requiring readers to compose the
  LP-supply firewall themselves.

  2026-05-17 16:09 PDT checkpoint: added the non-balanced caller-profit bound.
  Same-LP-supply histories, and the common no-mint/no-burn histories that
  imply same supply, can increase caller actual-token-balance value only by
  consuming surplus that was already donated above cached reserves at the
  start.

  2026-05-17 17:14 PDT checkpoint: added the spot-valued no-donation surplus
  theorem, following the Tamago ERC4626 trace-wide pattern. Any finite
  no-donation PairWorld history cannot increase the starting-spot value of
  skimmable surplus, so later skim profit must be explained by surplus already
  present at the start.

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

  2026-05-16 23:28 PDT checkpoint: factory now has an executable first-create
  bridge: a successful `createPair` run from an empty public pair array
  instantiates the closed-world factory create transition. The remaining bridge
  work is a general concrete-history correspondence for nonempty factories.

  2026-05-16 23:33 PDT checkpoint: the bridge is generalized to arbitrary
  modeled factory histories whose pair count matches the concrete state and
  whose history contains no existing sorted pair. The remaining work is richer
  reconstruction of that modeled history from concrete `allPairs` storage.

  2026-05-17 00:28 PDT checkpoint: added a reader-facing unordered uniqueness
  theorem: in any reachable factory history, `tokenA/tokenB` can resolve to at
  most one pair address. This is a short consequence of sorted entries plus the
  no-duplicate invariant, but it reads like the router-facing guarantee.

  2026-05-17 00:33 PDT checkpoint: added an append-only finite-history theorem.
  Any factory path has a suffix of newly created pairs such that the final
  public pair list equals the initial list followed by that suffix, and pair
  count increases by exactly the suffix length.

  2026-05-17 01:46 PDT checkpoint: added the reader-facing pair-count
  monotonicity corollary. Along any finite successful factory create history,
  modeled public pair count cannot decrease.

  2026-05-17 00:55 PDT checkpoint: added a reader-facing reachable lookup
  stability theorem. Once a reachable factory state contains an unordered token
  pair lookup, every later finite successful create history preserves that same
  lookup.

  2026-05-17 02:22 PDT checkpoint: adding a reader-facing reachable lookup
  validity theorem. Any unordered lookup in a reachable factory state must
  point to a nonzero pair for two distinct nonzero tokens, making the
  router-facing consequence of the sorted-entry invariant explicit.

  2026-05-17 02:42 PDT checkpoint: adding a reader-facing same-count path
  theorem. Since factory histories are append-only, a history that leaves pair
  count unchanged must leave the pair array unchanged; this makes "no hidden
  overwrite or reorder" a direct spec instead of an inference from append-only
  machinery.

  2026-05-17 02:52 PDT checkpoint: adding the router-facing same-count lookup
  corollary. If pair count is unchanged across a successful factory history,
  every unordered token lookup is identical before and after, making the
  no-hidden-change argument visible at the `getPair` level.

  2026-05-17 04:06 PDT checkpoint: added the first concrete factory
  reconstruction bridge. `FactoryWorldMatchesStorage` ties modeled pair count,
  both-direction pair mappings, and indexed `allPairs` entries back to factory
  storage, and public specs expose the length, lookup, and array agreement
  facts.

  2026-05-17 04:24 PDT checkpoint: added the successful-create preservation
  bridge. The reconstruction relation now compares decoded storage words to
  modeled pair addresses, matching public factory views without a new CREATE2
  canonical-word axiom. A successful concrete `createPair` run preserves
  `FactoryWorldMatchesStorage` for the world with the new sorted pair appended.

  2026-05-17 04:30 PDT checkpoint: added concrete lookup consequences from the
  bridge. Successful `createPair` now has reader-facing specs proving the
  decoded new-pair lookup is installed in both token orders and every existing
  reconstructed decoded lookup is preserved.

  2026-05-17 04:39 PDT checkpoint: added the finite-history concrete factory
  reconstruction bridge. A concrete create path records actual successful
  `createPair` runs plus modeled append steps, and public specs now prove that
  any such finite path preserves storage/world correspondence, existing
  decoded unordered lookups, and existing indexed `allPairs` entries.

  2026-05-17 10:43 PDT checkpoint: added the concrete same-length factory
  no-hidden-change theorem. If a finite sequence of real successful
  `createPair` calls leaves public `allPairsLength` storage unchanged, then
  the reconstructed factory world is unchanged.

  2026-05-17 11:45 PDT checkpoint: added explicit trace closure for the
  closed-world Factory model. If a factory state is reachable and a finite
  successful create path starts there, the endpoint is reachable too.

  2026-05-17 11:49 PDT checkpoint: adding the concrete reachable lookup
  validity theorem. Reconstructed factory storage now exposes the router-facing
  consequence directly: a modeled reachable lookup decodes to a nonzero pair
  for two distinct nonzero token addresses.

  2026-05-17 11:53 PDT checkpoint: lifting concrete lookup validity across
  finite concrete create histories. If real successful `createPair` calls move
  reconstructed storage from a reachable factory world to a later world, every
  endpoint lookup in that later world decodes to a nonzero pair for two
  distinct nonzero tokens.

  2026-05-17 17:05 PDT checkpoint: added the concrete same-length lookup
  preservation theorem. If a finite sequence of real successful `createPair`
  calls leaves public `allPairsLength` unchanged, then the reconstructed
  unordered lookup relation is exactly the same at both endpoints. This is the
  router-facing version of the existing same-length world-preservation theorem.

- [ ] **10. Verify and commit in coherent slices**

  After each slice run focused `lake build`. Before claiming completion run
  `lake build`, `tama check`, `tama build`, `tama test`, and `tama audit`.
  Commit related spec/proof/doc changes together.

  2026-05-17 04:09 PDT checkpoint: full verification passes for the first
  factory concrete reconstruction bridge: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit` (0
  issues). The Foundry signature-cache warning remains sandbox-only.

  2026-05-17 04:25 PDT checkpoint: full verification passes for the
  successful-create correspondence-preservation bridge: `tama check`, whole
  `lake build TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama
  audit` (0 issues). The Foundry signature-cache warning remains sandbox-only.

  2026-05-17 04:27 PDT checkpoint: after a proof-lint cleanup, the affected
  verification still passes: whole `lake build TamaUniV2.Proof`, `tama build`,
  `tama test` (26/26), and `tama audit` (0 issues).

  2026-05-17 04:31 PDT checkpoint: full verification passes for the concrete
  factory lookup consequence slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit` (0
  issues).

  2026-05-17 04:43 PDT checkpoint: full verification passes for the factory
  finite-history concrete reconstruction slice: `tama check`, whole `lake build
  TamaUniV2.Proof`, `tama build`, `tama test` (26/26), and `tama audit` (0
  issues). The Foundry signature-cache warning remains sandbox-only.

  2026-05-17 12:59 PDT checkpoint: full verification passes for the
  two-transfer token trace replay slice: focused Pair proof, whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), `tama
  audit` (0 issues), and `git diff --check`. Known warnings remain
  unused-variable lints plus sandbox cache/signature write warnings.

  2026-05-17 14:07 PDT checkpoint: full verification passes for the caller
  no-profit consequence slice: focused Pair proof, whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), `tama
  audit` (0 issues), and `git diff --check`. Known warnings remain
  unused-variable lints plus sandbox cache/signature write warnings.

  2026-05-17 14:18 PDT checkpoint: full verification passes for the common
  no-mint/no-burn caller no-profit slice: focused Pair proof, whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), `tama
  audit` (0 issues), and `git diff --check`. Known warnings remain
  unused-variable lints plus sandbox cache/signature write warnings.

  2026-05-17 17:05 PDT checkpoint: full verification passes for the factory
  same-length lookup slice: focused Factory proof, whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), `tama
  audit` (0 issues), and `git diff --check`. Known warnings remain
  unused-variable lints plus sandbox cache/signature write warnings.

  2026-05-17 17:14 PDT checkpoint: full verification passes for the Pair
  surplus-value no-donation slice: focused Pair proof, whole `lake build
  TamaUniV2.Proof`, `tama check`, `tama build`, `tama test` (26/26), `tama
  audit` (0 issues), and `git diff --check`. Known warnings remain
  unused-variable lints plus sandbox cache/signature write warnings.

## Non-Goals

- Do not reintroduce formal API parity specs.
- Do not resurrect old aggregate executable-success plans.
- Do not add proof-convenience helper functions to the public contract or
  public ABI. Same-timestamp and elapsed oracle cases are valid public specs
  when stated as mathematical reserve-update behavior.
