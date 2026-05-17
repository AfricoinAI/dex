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
  mutating entrypoints, and skim under-reserve guards.
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
- Closed-world `PairWorldGood` preservation for one step and all finite
  reachable traces, plus finite-path preservation from any good state, reserve
  backing, uint112 reserve bounds, path-wide LP-supply coherence, path-wide
  locked-liquidity coverage, minimum-liquidity lock, share-only action framing,
  reserve-update projections for mint/burn/swap/skim/sync, raw swap-K
  nondecrease, fee-adjusted K projection for swaps, positive-input/output and
  output-below-reserve swap facts, donation reserve/K framing, LP-supply
  preservation for swap/skim/sync, and the action classifier that only mint/burn
  can change LP total supply.
- Mint/burn closed-world supply discipline now explicitly states first-mint
  `MINIMUM_LIQUIDITY` locking, subsequent-mint locked-liquidity preservation,
  exact burn supply reduction, and the fact that burns cannot redeem the locked
  liquidity floor.
- Same-LP-supply spot-value no-profit projection from reserve-product
  nondecrease. The stronger closed-world LP-normalized K theorem now covers
  arbitrary finite paths from good positive-supply states: each step preserves
  or improves `K / totalSupply^2`, the fact composes across paths, same-supply
  paths cannot reduce raw K, and same-supply paths cannot reduce the pool's
  value at the initial spot price. This allows mint/burn round trips rather
  than relying only on the older no-burn path theorem.

Factory:

- Storage-backed view specs for `getPair`, `allPairs`, and `allPairsLength`.
- Exact create-pair reverts for identical tokens, zero token, duplicates,
  CREATE2 failure, and length overflow.
- Failed-create atomicity spec showing reverted `createPair` runs leave pair
  mappings, pair array, length, and events unchanged.
- Create-pair success spec for sorted tokens, bidirectional mapping writes,
  append/length update, nonzero pair boundary, and `PairCreated`.
- Closed-world factory model for finite successful create histories, proving
  sorted nonzero pair entries, sorted-pair uniqueness, symmetric membership,
  append-only creation, preservation of existing pairs, and pair-count/list
  length consistency.

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
- TWAP/oracle updates: for every reserve update path, prove cumulative prices
  increment exactly when elapsed time is positive and old reserves are nonzero,
  and remain unchanged otherwise.
- Flash swaps: prove callback iff `data` is nonempty, callback failure is
  atomic, the lock is held through the callback, and K is checked after callback
  effects.
- Skim/sync bridge: `sync` still needs public-entrypoint bridge facts for the
  closed-world transition, uint112 overflow reverts, and TWAP/oracle updates.
- Ordered revert matrix: cover canonical guard priority for mint, burn, swap,
  skim, sync, and factory, with exact revert payload/state.
- Sequence-level economics: strengthen the conditional mint/burn/swap bridge
  obligations into direct executable success/accounting proofs where Lean can
  reduce the public entrypoint without kernel-recursion issues. Keep any
  decomposition proof-local; do not add contract helpers.
- Factory invariants: bridge successful executable `createPair` runs into the
  factory-world transition and add failed-create atomicity as a global frame
  property.

## Non-Goals

- No formal API parity specs.
- No public or contract-level helper functions added only for proof convenience.
- No aggregate public specs that restate an entire function body field-by-field.
- No local sqrt proof duplication; use Tamago's installed sqrt facts.
