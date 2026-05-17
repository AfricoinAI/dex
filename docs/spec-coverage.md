# Spec Coverage Strategy

This is the active spec guidance. Historical proof attempts live in
`docs/agent-progress.md`; do not treat old plan files or old log entries as the
current route.

## Principles

- API parity is not a formal spec category. Keep the supported canonical ABI as
  a build/review constraint, but do not add obligations whose only claim is that
  a function exists or does not exist.
- Public specs should be short security and correctness properties: accounting,
  reserve backing, guarded reverts, oracle updates, reentrancy, K preservation,
  and sequence-level economic safety.
- Executable run lemmas are bridge/proof plumbing. They are useful only when
  they connect a real entrypoint run to a small invariant or transition fact.
- Do not modify the contract API or source shape to satisfy a proof. Specs and
  proofs serve the contract.
- Do not add axioms or trust surfaces for internal logic. Trust belongs only at
  actual external boundaries such as ERC20 calls, flash callbacks, and CREATE2.

## Canonical References

Behavioral coverage should be checked against:

- Pair source: https://github.com/Uniswap/v2-core/blob/master/contracts/UniswapV2Pair.sol
- Pair tests: https://github.com/Uniswap/v2-core/blob/master/test/UniswapV2Pair.spec.ts
- Factory source: https://github.com/Uniswap/v2-core/blob/master/contracts/UniswapV2Factory.sol
- Factory tests: https://github.com/Uniswap/v2-core/blob/master/test/UniswapV2Factory.spec.ts

The project intentionally keeps the fee-off subset and omits factory admin,
protocol-fee minting, LP `name`, LP `symbol`, and `permit`.

## Current Implemented Coverage

Pair:

- Storage-backed view specs for LP balances, allowances, reserves, cumulative
  prices, factory, tokens, `MINIMUM_LIQUIDITY`, decimals, and fee-off `kLast`.
- LP ERC20 approve/transfer/transferFrom accounting, allowance, overflow, and
  event specs.
- Exact run-result reverts for initialization, LP transfer guards, locked
  mutating entrypoints, and skim under-reserve guards. The swap zero-output
  pre-interaction guard is now a public Lean spec and proof. The later
  insufficient-liquidity and invalid-recipient guards have exact Foundry
  revert-message coverage, but are not public Lean obligations until their
  ordered-prefix proofs are decomposed enough to avoid kernel-depth blowups.
- Revert-frame token-balance preservation specs for mint, burn, swap, skim, and
  sync using pair-local transfer traces.
- Pair-local atomicity specs showing reverted mint, burn, swap, skim, and sync
  runs leave storage, LP accounting maps, and event logs unchanged.
- `skim` success spec for exact surplus transfer traces, unchanged reserves,
  restored lock, and refinement to the closed-world skim transition.
- Mint/burn/swap closed-world bridge predicates for expected concrete states:
  first mint, subsequent mint, burn, and swap all refine the corresponding
  PairWorld transition once the concrete amount, liquidity, post-callback
  balance, and K facts are available.
- `sync` expected-state and success-conditional bridge predicates showing that
  observed balances inside uint112 bounds refine the closed-world sync
  transition when the public run succeeds.
- TWAP/oracle arithmetic obligations for reserve updates: same-timestamp
  updates leave cumulative prices unchanged, elapsed updates with nonzero old
  reserves add the canonical fixed-point price times elapsed time, and elapsed
  branches with zero elapsed time or a zero old reserve leave cumulative prices
  unchanged. The remaining work is to bridge every public reserve-update
  entrypoint to these oracle arithmetic facts.
- Closed-world `PairWorldGood` preservation for one step and all finite
  reachable traces, plus finite-path preservation from any good state. The
  reader-facing reachable-path reserve-backing theorem now states the central
  safety invariant directly: from any reachable pool state, every finite
  successful modeled history ends with cached reserves backed by actual token
  balances. Matching reader-facing finite-trace theorems now also state that
  every such history keeps cached reserves inside the uint112 reserve domain and
  preserves the minimum-liquidity lock shape, that reachable nonempty pools
  remain nonempty, that reachable nonempty pools have positive reserves on both
  token sides and preserve those positive reserves across finite successful
  histories, and that finite histories containing no mint and no burn preserve
  total LP supply and locked liquidity exactly. The same layer also covers
  path-wide LP-supply coherence, path-wide locked-liquidity coverage,
  share-only action framing, reserve-update projections for
  mint/burn/swap/skim/sync, raw swap-K nondecrease, fee-adjusted K projection
  for swaps, positive-input/output and output-below-reserve swap facts,
  post-output plus inferred-input balance accounting for swaps, donation
  reserve/K framing, LP-supply preservation for swap/skim/sync, the action
  classifier that only mint/burn can change LP total supply, the K-direction
  classifier that any one-step raw K decrease from a good state must be a burn,
  and the reachable finite-trace theorem that any no-burn path cannot decrease
  cached K.
- Flash-swap callback gating is covered at the ECM compile-template boundary:
  the generated callback call sits under a `data_length > 0` Yul guard. The
  remaining callback-failure and in-callback lock semantics are runtime/ECM
  boundary behaviors unless the callback ECM gains a richer Lean trace model.
- Mint/burn closed-world supply discipline now explicitly states first-mint
  `MINIMUM_LIQUIDITY` locking, subsequent-mint locked-liquidity preservation,
  every valid mint strictly increasing total supply, exact burn supply
  reduction, burns never increasing supply, and the fact that burns cannot
  redeem the locked liquidity floor. The burn ghost transition itself now
  requires positive liquidity, positive pre-burn supply, and positive redeemed
  token amounts, and the token-side lock consequence proves burns from good
  positive-token states cannot drain either token balance to zero. Mint and
  burn now also have explicit LP-share safety obligations: existing positive
  pools cannot be diluted by mints, and burns cannot over-extract from the
  remaining LPs, because each preserves or improves K per squared LP supply.
- Same-LP-supply spot-value no-profit projection from reserve-product
  nondecrease. The stronger closed-world LP-normalized K theorem now covers
  arbitrary finite paths from good positive-supply states: each step preserves
  or improves `K / totalSupply^2`, the fact composes across paths, same-supply
  paths cannot reduce raw K, same-supply paths cannot reduce the pool's value
  at the initial spot price, and a reader-facing value-comparison theorem states
  that conclusion directly for any reachable positive-supply same-LP-supply
  finite path. A caller-facing no-extraction theorem names the same economic
  conclusion explicitly: within the closed-world Pair model, same-LP-supply
  histories cannot extract positive spot-value from the pool at the initial
  price. A reachable LP-share theorem now also states the normalized backing
  invariant directly for all finite paths from reachable positive-supply states.
  The strongest same-supply no-extraction theorem now needs only reachable
  positive supply; the positive-reserve invariant supplies the spot-price
  premises. A no-liquidity corollary states the most common operational case
  directly with the same strength: reachable positive-supply histories with no
  mint and no burn preserve LP supply and therefore cannot extract spot value
  at the initial price, without separate reserve-positive hypotheses. This
  allows mint/burn round trips rather than relying only on the older no-burn
  path theorem.

Factory:

- Storage-backed view specs for `getPair`, `allPairs`, and `allPairsLength`.
- Exact create-pair reverts for identical tokens, zero token, duplicates,
  CREATE2 failure, and length overflow.
- Failed-create atomicity spec showing reverted `createPair` runs leave pair
  mappings, pair array, length, and events unchanged.
- Create-pair success spec for sorted tokens, bidirectional mapping writes,
  append/length update, nonzero pair boundary, and `PairCreated`.
- Executable create bridges showing successful `createPair` runs instantiate
  the closed-world factory create transition: one base-case bridge for an empty
  public pair array, and one general bridge for a modeled pre-history with
  matching pair count and no existing sorted pair.
- Closed-world factory model for finite successful create histories, proving
  sorted nonzero pair entries, sorted-pair uniqueness, symmetric membership,
  reachable lookup validity for distinct nonzero token pairs and nonzero pair
  addresses, unordered token-pair address uniqueness,
  append-only creation, append-only finite histories, pair-count monotonicity,
  preservation of existing pairs, reader-facing reachable lookup stability,
  pair-count/list length consistency, and path-level preservation from any good
  factory state.

## Current Spec Work

These are the current standards for the next Lean work. They are behavioral
properties, not API-surface properties.

- Mint formulas: prove first mint locks `MINIMUM_LIQUIDITY`, subsequent mints
  mint no more than the minimum pro-rata share, and successful `mint` runs imply
  the corresponding closed-world mint transition.
- Burn formulas: prove burns redeem no more than pro-rata token balances,
  update reserves to post-transfer balances, restore the lock, emit the expected
  events, and imply the closed-world burn transition.
- Swap formulas: prove input inference from final balances, exact output
  transfers, fee-adjusted K, raw K nondecrease, lock restoration, events, and
  the closed-world swap transition.
- TWAP/oracle updates: the arithmetic cases now cover same timestamp, active
  elapsed update, and inactive elapsed no-op behavior. The remaining work is to
  connect those concise arithmetic claims to every public reserve-update path.
- Flash swaps: callback gating is now proved at the ECM compile-template
  boundary, and closed-world swap accounting now states that K is checked
  against final balances after output plus inferred repayment. Remaining work:
  model callback failure atomicity and in-callback lock semantics with an
  explicit Lean trace or keep them as mirrored runtime boundary coverage.
- Skim/sync bridge: `sync` has uint112 overflow reverts and a closed-world
  transition bridge. The remaining work is a narrow bridge from successful
  reserve-update runs to the TWAP/oracle arithmetic facts.
- Ordered revert matrix: cover canonical guard priority for mint, burn, swap,
  skim, sync, and factory, with exact revert payload/state.
  Swap now has a public Lean proof for the zero-output guard after the lock
  gate. Insufficient-liquidity and invalid-recipient runtime checks are exact in
  Foundry, but still need proof-local ordered-prefix Lean proofs before they
  should be reintroduced as public obligations. Direct full-entrypoint unfolding
  has now failed for both `sync` lock restoration and burn
  insufficient-liquidity because it expands into later oracle/transfer tails;
  the next Lean route should factor those prefixes privately first.
- Sequence-level economics: the closed-world no-extraction theorem is now the
  active caller-facing story. Same-LP-supply reachable histories cannot reduce
  pool value at the initial spot price, and LP-normalized K explains why
  mint/burn round trips are covered. Do not add a dummy caller ledger; only add
  an external-wallet model if it tracks real action-level token and LP ownership
  changes.
- Factory invariants: the closed-world reachable and path invariants are now in
  place, failed-create atomicity is proved, and successful create is bridged
  into the factory-world transition for both the empty base case and arbitrary
  modeled pre-histories with matching count/no-existing-pair correspondence.
  The remaining work is a richer concrete-history reconstruction relation from
  the public `allPairs` array and pair mapping.

## Non-Goals

- No formal API parity specs.
- No public or contract-level helper functions added only for proof convenience.
- No aggregate public specs that restate an entire function body field-by-field.
- No local sqrt proof duplication; use Tamago's installed sqrt facts.
