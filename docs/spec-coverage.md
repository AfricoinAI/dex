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
- Spec files should read as assurance arguments. Each section should say why
  the following facts matter, how they compose with the previous section, and
  what security conclusion they support.
- The Lean spec files should be readable without opening the proof files first:
  section comments should introduce the informal claim, each `def` should be
  the short formal version of that claim, and later sections should explicitly
  explain how earlier claims compose into trace-wide safety.
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
- Exact Pair view success/frame coverage now states that the actual public
  reads for LP supply, LP balances, allowances, factory, token identities,
  `MINIMUM_LIQUIDITY`, cumulative prices, decimals, and fee-off `kLast` return
  the expected observable value without mutating pair state.
- Exact `getReserves` success coverage now states the router-facing reserve
  read returns cached reserve0/reserve1/timestamp and frames pair state.
- Pair-token transfer boundary coverage now proves both sides of the trace
  model: the pair's safe-transfer wrapper emits a pair-local token-transfer
  event, replaying one such event moves exactly the recorded token amount
  between the recorded accounts, and replaying two events for distinct tokens
  moves exactly both token amounts from the pair-side account to the recipient.
- LP ERC20 approve/transfer/transferFrom accounting, allowance, overflow, and
  event specs. The executable LP-bookkeeping layer now also has scalar
  AMM-storage frame facts: approve, transfer, and transferFrom cannot change
  reserves, cumulative prices, total supply, token identities, or the lock. It
  also has pair-local token-balance frame facts: those LP bookkeeping calls do
  not emit the pair-local ERC20 transfer trace used to model token0/token1
  movement.
- Exact run-result reverts for initialization, LP transfer guards, locked
  mutating entrypoints, and skim under-reserve guards. The swap zero-output
  pre-interaction guard is now a public Lean spec and proof with a Foundry
  mirror. The later
  insufficient-liquidity and invalid-recipient guards have exact Foundry
  revert-message coverage, but are not public Lean obligations until their
  ordered-prefix proofs are decomposed enough to avoid kernel-depth blowups.
- Exact successful initialization coverage now states the positive side of the
  same lifecycle: a factory call into a fresh pair succeeds and records the two
  token addresses that define the market. The matching success-frame theorem
  shows initialization is identity-only: it does not mutate reserves, LP supply,
  LP accounting maps, or events.
- A reader-facing Pair reentrancy invariant packages the locked-entrypoint
  facts directly: if the lock is closed, every state-changing AMM entrypoint
  reverts with `UniswapV2: LOCKED` before durable side effects.
- The success-side lock bridge is now explicit for mint, burn, swap, skim, and
  sync: if any of those public calls succeeds, the initial lock gate must have
  been open.
- Revert-frame token-balance preservation specs for mint, burn, swap, skim, and
  sync using pair-local transfer traces.
- Pair-local atomicity specs showing reverted mint, burn, swap, skim, and sync
  runs leave storage, LP accounting maps, and event logs unchanged.
- `skim` success spec for exact surplus transfer traces, exact pair-local
  token-balance effects when those traces are replayed, unchanged reserves,
  restored lock, and refinement to the closed-world skim transition.
- Mint/burn/swap closed-world bridge predicates for expected concrete states:
  first mint, subsequent mint, burn, and swap all refine the corresponding
  PairWorld transition once the concrete amount, liquidity, post-callback
  balance, and K facts are available. Swap now also exposes the economic bridge
  from a successful public run plus final-balance/K facts directly to the
  one-swap caller no-profit theorem.
- `sync` expected-state and success-conditional bridge predicates showing that
  observed balances inside uint112 bounds refine the closed-world sync
  transition when the public run succeeds.
- Closed-world surplus reconciliation now states the direct cleanup consequence
  for both balance-reconciliation entrypoints: `skim` and `sync` end with no
  modeled surplus above cached reserves. Skim also has an exact value theorem:
  at the initial spot price it removes precisely the pre-existing surplus
  token-balance value, not accounted reserve value, plus the direct consequence
  that skim cannot increase token-balance value at the starting spot price.
  Sync now states the complementary custody fact directly: it changes cached
  accounting, not token balances, so every spot-price valuation of actual token
  balances is unchanged. Together, the shared `skim`/`sync` value theorem
  states that either action cannot increase actual token-balance value at the
  starting spot price, and the finite-history theorem lifts that to any
  reachable history made only of LP approvals/transfers plus `skim`/`sync`. The
  balanced-pool theorem states the clean
  no-surplus case directly: `skim` is a no-op on token
  balances, cached reserves, LP supply, and locked liquidity. The matching sync
  balanced-pool theorem states that zero-surplus sync is also a no-op on token
  balances, cached reserves, LP supply, and locked liquidity. The aggregate
  theorem packages those two facts: any `skim`/`sync` history from a good
  balanced pool leaves token balances, cached reserves, LP supply, and locked
  liquidity unchanged. The broader no-change invariant adds LP share
  bookkeeping to that path family: any `approve`/`transfer`/`transferFrom` plus
  `skim`/`sync` history from a good balanced pool is unchanged in the same
  fields. The same section names the cached-K consequence directly, then
  exposes the clean-state invariant: those histories preserve zero surplus, so
  they cannot create new excess token balances above cached reserves. Its
  reader-facing economic corollary states the same fact in no-extraction terms:
  those histories from a clean balanced pool preserve actual token-balance
  value exactly at the initial spot price. The sync/K
  refinement states that sync preserves cached K exactly when the start state
  has no surplus, and the converse reader-facing theorem states that any
  sync-driven K increase requires pre-existing excess token balances.
- TWAP/oracle arithmetic obligations for reserve updates are now stated in the
  generic contract-level form first: same-timestamp updates leave cumulative
  prices unchanged, elapsed updates with nonzero old reserves add the canonical
  UQ112x112 encoded price times elapsed time, and elapsed branches with zero elapsed
  time or a zero old reserve leave cumulative prices unchanged. Each
  reserve-writing action family now has a success-run bridge into that rule:
  first mint, subsequent mint, burn, swap, and sync all expose
  reserve-to-balance writes plus the generic TWAP cases once their existing
  concrete arithmetic premises are established. For `mint`, success now derives
  the uint112 observed-balance bounds directly from exact overflow reverts. For
  `sync`, success derives both the open-lock fact and the uint112 balance bounds
  directly from exact revert specs, so the closed-world sync transition can be
  cited without separate lock or reserve-bound assumptions. Successful `sync`
  now also exposes the reserve-write conclusion directly: it caches the current
  observed token balances as reserves. The shared concrete reserve-write bridge
  packages the same facts for any mint, burn, swap, or sync transition from a
  concrete state. The executable bridge layer now also exposes core-invariant
  preservation for first mint, later mint, burn, swap, skim, and sync once each
  call is connected to its existing closed-world transition facts. Initial mint
  now has the base-case version too: the concrete empty-pool premises plus a
  successful public run establish `PairWorldGood` for the post-mint state
  without assuming the projected pre-state was already good. Remaining work is
  deriving more of the arithmetic premises directly from successful mint, burn,
  and swap runs where that can be done with small adapters.
- Closed-world `PairWorldGood` preservation for one step and all finite
  reachable traces, finite-path preservation from any good state, and
  reachability closure for appending finite successful paths. The
  reader-facing reachable-path reserve-backing theorem now states the central
  safety invariant directly: from any reachable pool state, every finite
  successful modeled history ends with cached reserves backed by actual token
  balances. Matching reader-facing finite-trace theorems now also state that
  every such history keeps cached reserves inside the uint112 reserve domain and
  preserves the minimum-liquidity lock shape, that reachable nonempty pools
  remain nonempty, that reachable nonempty pools have positive reserves on both
  token sides and preserve those positive reserves across finite successful
  histories, and that finite histories containing no mint and no burn preserve
  total LP supply and locked liquidity exactly. Locked liquidity is also proved
  monotone from good/reachable states: once established, finite successful
  histories cannot reduce it. The central reachable-path theorem now packages
  the core invariant directly: every finite successful modeled history from a
  reachable state ends with backed reserves, uint112 reserve bounds, and
  coherent LP-supply locking. The invariant layer now also exposes the
  token-side positive-balance consequence directly: from any reachable nonempty
  pool, every finite successful modeled history leaves both actual token
  balances positive. The same layer also covers the one-step LP-supply firewall
  for any action other than mint or burn, executable successful-run bridges
  proving that `swap`, `skim`, and `sync` preserve total LP supply and locked
  liquidity once their existing transition premises are available. Successful
  public `skim` and `sync` now also bridge directly back to the core invariant:
  from any concrete state whose projection is `PairWorldGood`, a successful run
  has a modeled post-state that is still `PairWorldGood`. The same layer covers
  one-step and finite-history
  supply-direction invariants showing no-burn histories cannot decrease LP
  supply and no-mint histories cannot increase LP supply,
  path-wide LP-supply coherence,
  path-wide locked-liquidity coverage,
  share-only action framing, finite-history pure-share-bookkeeping invariants
  showing LP approvals/transfers/transferFroms leave token balances, cached
  reserves, total LP supply, locked liquidity, cached K, and spot-value
  measurements unchanged, reserve-update projections for
  mint/burn/swap/skim/sync, the reserve-change classifier proving only
  mint/burn/swap/sync can rewrite cached reserves, the finite-history reserve
  isolation theorem for histories with no reserve-update action, the shared
  reserve-write theorem that mint/burn/swap/sync write cached reserves to the
  pair's actual token balances, the matching cached-K and reserve spot-value
  preservation corollary, canonical
  fee-adjusted K for swaps plus the arithmetic theorem that the fee-adjusted
  check implies raw cached-K
  nondecrease once reserves equal final balances, positive-input/output and
  output-below-reserve swap facts, an executable successful-swap bridge that
  states both reserve-write and raw cached-K nondecrease from the real public
  run once the final-balance/K facts are supplied, the one-swap economic
  consequence that a
  valid swap from a good live pool cannot reduce pool value at the starting spot
  price, and the reader-facing reachable form of that same swap theorem,
  post-output plus inferred-input balance accounting for swaps, an explicit
  flash-swap theorem that the fee-adjusted K check uses those final
  post-repayment balances, donation
  reserve/K framing, exact donation-created reserve surplus, finite-history
  no-donation surplus isolation, zero-surplus preservation for no-donation
  histories, clean-start no-donation endpoint balance, LP-supply preservation
  for swap/skim/sync,
  the action classifier that only mint/burn can change LP total supply, the K-direction
  classifier that any one-step raw K decrease from a good state must be a burn,
  the reachable finite-trace theorem that any no-burn path cannot decrease
  cached K, and the common-case reachable theorem that histories with no mint
  and no burn cannot decrease cached K. The contrapositive reader-facing theorem
  is also stated directly:
  if a reachable successful path ends with lower cached K, the same endpoint
  cannot be reached by any burn-free history.
- Flash-swap callback gating is covered at the ECM compile-template boundary:
  the generated callback call sits under a `data_length > 0` Yul guard, and the
  gated body encodes the canonical `uniswapV2Call` selector, sender, output
  amounts, and target call. Callback failure is also covered at the same
  boundary: the generated body checks call failure, copies returndata, and
  executes `revert` instead of silently continuing. In-callback lock observation
  remains a runtime/ECM boundary behavior unless the callback ECM gains a richer
  Lean trace model.
- Mint/burn closed-world supply discipline now explicitly states first-mint
  `MINIMUM_LIQUIDITY` locking, subsequent-mint locked-liquidity preservation,
  the strict locked-share consequence that the first LP cannot own the entire
  supply, every valid mint strictly increasing total supply, exact burn supply
  reduction, burns never increasing supply, and the fact that burns cannot
  redeem the locked liquidity floor. The reachable burn theorem states directly
  that a valid burn from a reachable nonempty pool cannot empty either token
  side. The burn ghost transition itself now requires positive liquidity,
  positive pre-burn supply, and positive redeemed token amounts, and the
  token-side lock consequence proves burns from good positive-token states
  cannot empty either token balance. The executable burn layer now also exposes
  the reserve-write fact directly: successful public burns, once connected to
  their redemption facts, cache the post-transfer token balances as reserves.
  Mint and burn now also have explicit
  LP-share safety obligations: existing positive pools cannot be diluted by
  mints, and burns cannot over-extract from the remaining LPs, because each
  preserves or improves K per squared LP supply. The public executable layer now
  exposes both economic consequences directly for successful nonempty-pool mints
  and successful burns once their concrete pro-rata/redemption facts are
  available. The same executable layer also exposes the supply-movement facts
  directly: successful initial and later mints strictly increase LP total
  supply, and successful burns reduce LP total supply exactly by the burned
  liquidity. Successful initial and later mints now also expose the matching
  reserve-write and raw cached-K facts directly: once connected to their
  arithmetic facts, each public mint path caches observed token balances as
  reserves and cannot decrease the cached reserve product.
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
  price. A token1-denominated no-profit theorem states the same value
  comparison in the units a user would naturally use for the initial
  `reserve1 / reserve0` spot price, scaled by `reserve0` to avoid division. A
  reachable LP-share theorem now also states the normalized backing invariant
  directly for all finite paths from reachable positive-supply states.
  The strongest same-supply no-extraction theorem now needs only reachable
  positive supply; the positive-reserve invariant supplies the spot-price
  premises. A no-liquidity corollary states the most common operational case
  directly with the same strength: reachable positive-supply histories with no
  mint and no burn preserve LP supply and therefore cannot extract spot value
  at the initial price, without separate reserve-positive hypotheses. This
  allows mint/burn round trips rather than relying only on the older no-burn
  path theorem. A caller-facing reserve-value theorem states the same
  same-LP-supply conclusion as an external-wallet no-profit fact: if
  caller-plus-pool spot value is only redistributed, the caller cannot finish
  richer. A token-balance version now connects the reserve theorem back
  to actual ERC20 balances: from a reachable balanced start state with no
  surplus over cached reserves, same-LP-supply histories cannot reduce the
  pair's token-balance value at the initial spot price. The common no-mint and
  no-burn history shape has the same actual-balance theorem without requiring a
  separate same-supply premise, because the LP-supply firewall supplies it. The
  reserve-value caller theorem has the same common-case corollary for
  no-mint/no-burn histories, so ordinary non-liquidity operation exposes a
  direct caller no-profit statement. The non-balanced case is now explicit too:
  same-LP-supply histories can reduce actual token-balance value by at most the
  starting surplus above cached reserves, caller profit is bounded by that same
  starting surplus when caller-plus-pair value is redistributed, and
  no-mint/no-burn histories inherit both bounds automatically.
  The reader-facing zero-surplus corollaries spell out the clean operational
  conclusion directly: from a reachable nonempty state with no donated surplus
  above reserves, same-LP-supply histories, and in particular histories with no
  mint and no burn, cannot reduce the pair's actual token-balance value at the
  initial spot price. The same section now includes the caller-value
  consequence: when a caller ledger's spot-priced value plus the pair's
  spot-priced token-balance value is unchanged except for redistribution
  between them, the caller cannot finish with more value. A clean non-liquidity
  theorem now composes the no-donation and no-mint/no-burn premises in the
  form a reader usually wants: starting from a reachable clean pool, such
  histories end with balances equal to reserves and cannot reduce actual
  token-balance value; the paired caller theorem adds the same no-profit
  conclusion under the explicit caller-plus-pair redistribution premise.

Factory:

- Storage-backed view specs for `getPair`, `allPairs`, and `allPairsLength`.
- Exact view success coverage now states that `getPair` and `allPairsLength`
  are state-framing reads, and in-bounds `allPairs(index)` returns the decoded
  stored pair while framing factory state; the out-of-bounds exact revert covers
  the other side of the array boundary.
- Exact create-pair reverts for identical tokens, zero token, duplicates,
  CREATE2 failure, and length overflow.
- Failed-create atomicity spec showing reverted `createPair` runs leave pair
  mappings, pair array, length, and events unchanged.
- Create-pair success spec for sorted tokens, bidirectional mapping writes,
  append/length update, nonzero pair boundary, and `PairCreated`.
- Executable create bridges showing successful `createPair` runs instantiate
  the closed-world factory create transition: one base-case bridge for an empty
  public pair array, and one general bridge for a modeled pre-history with
  matching pair count and no existing sorted pair. Both bridges now expose the
  direct invariant consequence: first real creation establishes, and later real
  creation preserves, the good factory-world invariant covering sorted nonzero
  entries, uniqueness, and pair-count/list coherence.
- Closed-world factory model for finite successful create histories, proving
  sorted nonzero pair entries, sorted-pair uniqueness, symmetric membership,
  reachable lookup validity for distinct nonzero token pairs and nonzero pair
  addresses, unordered token-pair address uniqueness,
  append-only creation, append-only finite histories, pair-count monotonicity,
  same-count histories preserving the pair array and all unordered lookups,
  preservation of existing pairs, reader-facing reachable lookup stability,
  pair-count/list length consistency, and path-level preservation from any good
  factory state, plus trace closure when a finite path is appended to an
  already reachable factory state.
- Concrete factory reconstruction bridge: a `FactoryWorldMatchesStorage`
  relation now ties a modeled factory world back to real storage. Public specs
  state that reconstructed worlds agree with `allPairsLength`, decoded
  both-direction pair mapping lookup, and decoded indexed `allPairs` storage
  entries. The concrete lookup layer now also states the reachable validity
  consequence directly: reconstructed lookups decode to nonzero pairs for two
  distinct nonzero tokens. A successful concrete `createPair` run now preserves
  that correspondence after appending the new sorted pair, so the closed-world
  append-only invariants continue to describe router-visible storage after real
  factory successes. Reader-facing concrete consequences now state that
  successful creation installs the decoded new-pair lookup in both token orders
  and preserves every existing reconstructed decoded lookup. The bridge now
  composes over finite concrete create histories: any successful sequence of
  real `createPair` runs preserves the storage/world correspondence at the
  endpoint, preserves every pre-existing decoded unordered lookup, and
  preserves every pre-existing indexed `allPairs` entry. Endpoint lookups in
  reconstructed reachable histories are also proved valid: they decode to
  nonzero pairs for two distinct nonzero token addresses. Such concrete create
  histories also cannot decrease router-visible `allPairsLength` storage. The
  same concrete-history layer now has the same-length no-hidden-change theorem:
  if public `allPairsLength` is unchanged across a successful concrete create
  history, the reconstructed factory world itself is unchanged.

## Remaining Spec Work

These are the current standards for the next Lean work. They are behavioral
properties, not API-surface properties. The broad closed-world invariant and
economic story is now in place; remaining Pair work should mainly strengthen
the executable bridge from canonical public entrypoints to that story.

- Mint, burn, and swap executable bridges: closed-world formulas already cover
  minimum-liquidity locking, pro-rata mint/burn discipline, fee-adjusted swap K,
  derived raw-K nondecrease, reserve updates, LP-supply effects, and no-profit
  consequences. Successful later mints and successful burns now bridge directly
  to their LP-share economic conclusions once their concrete arithmetic facts
  are supplied. Successful swaps derive the zero-output guard, prove LP supply
  and locked liquidity are unchanged, and connect directly to the one-swap
  caller no-profit theorem once final-balance/K facts are supplied. Successful
  first mint, later mint, burn, swap, skim, and sync now also expose core
  `PairWorldGood` preservation at the executable boundary once their existing
  transition facts are supplied; `skim` and `sync` need no extra arithmetic
  premises beyond success. The remaining bridge work is to derive more of
  the arithmetic premises directly from successful public runs, in small
  prefix/suffix lemmas rather than one aggregate function summary.
- Concrete success-path restoration and events: Foundry mirrors cover Mint,
  Burn, Swap, Sync, and lock restoration at runtime. Lean should expose only
  short obligations here, preferably via factored proof-local adapters for the
  shared lock and reserve-update suffixes.
- TWAP/oracle updates: the arithmetic cases now cover same timestamp, active
  elapsed update, and inactive elapsed no-op behavior as generic reserve-update
  obligations. Sync, first mint, subsequent mint, burn, and swap all have
  successful-run bridge facts into those claims once their concrete arithmetic
  premises are available. Remaining work is only to derive more of those
  concrete premises directly from successful public runs, where that can be
  done without monolithic entrypoint unfolding.
- Flash swaps: callback gating is now proved at the ECM compile-template
  boundary, and closed-world swap accounting now states that K is checked
  against final balances after output plus inferred repayment. The ECM template
  now also proves callback call failure reaches a returndata-preserving revert.
  Remaining work: model in-callback lock semantics with an explicit Lean trace
  or keep it as mirrored runtime boundary coverage.
- Skim/sync bridge: `skim` has exact surplus-transfer and closed-world
  transition coverage. `sync` has uint112 overflow reverts, a closed-world
  transition bridge, and a successful-run bridge to reserve-to-balance writes
  plus the generic TWAP/oracle arithmetic facts. The same oracle bridge shape
  now exists for mint, burn, and swap once their concrete arithmetic premises
  are available.
- Ordered revert matrix: cover canonical guard priority for mint, burn, swap,
  skim, sync, and factory, with exact revert payload/state.
  Swap now has a public Lean proof for the zero-output guard after the lock
  gate. Insufficient-liquidity and invalid-recipient runtime checks are exact in
  Foundry, but still need proof-local ordered-prefix Lean proofs before they
  should be reintroduced as public obligations. Direct full-entrypoint unfolding
  has now failed for both `sync` lock restoration and burn
  insufficient-liquidity because it expands into later oracle/transfer tails;
  the next Lean route should factor those prefixes privately first.
- Sequence-level economics: same-LP-supply reachable histories cannot reduce
  pool value at the initial spot price, and LP-normalized K explains why
  mint/burn round trips are covered. The actual token-balance theorem requires
  either a balanced/zero-surplus start state or the surplus-bounded form:
  pre-existing donated surplus is an external gift that `skim` can legitimately
  remove, but any actual-balance value loss is bounded by that starting surplus.
  The caller no-profit theorem is now stated as the explicit external-wallet
  consequence: if caller value plus pair token-balance value is unchanged except
  for redistribution between them, the caller cannot finish with more value.
  The common no-mint/no-burn form derives the same caller conclusion without a
  separate same-supply premise, and the clean no-donation/no-mint/no-burn form
  also proves the endpoint remains balanced. Only add a richer external-wallet
  model if it tracks real action-level token and LP ownership changes.
- Donation surplus: the closed-world model now tracks token-side reserve
  surplus directly. Donations increase surplus exactly, and finite successful
  histories with no donation step cannot create new surplus. The zero-surplus
  corollary states the exact clean-start invariant: no-donation histories
  preserve zero skimmable surplus on both token sides, and the endpoint-balance
  corollary states the same fact in direct accounting form: balances equal
  reserves at the end. This is the Tamago-style premise that makes the
  balanced-start token-balance no-profit theorem honest: `skim` can remove an
  external gift, but ordinary pair mechanics cannot manufacture that gift
  internally.
- Factory invariants: the closed-world reachable and path invariants are now in
  place, failed-create atomicity is proved, and successful create is bridged
  into the factory-world transition for both the empty base case and arbitrary
  modeled pre-histories with matching count/no-existing-pair correspondence.
  A concrete-history reconstruction bridge is now in place for length, decoded
  pair mappings, reverse mappings, and indexed pair-array entries, and
  successful concrete `createPair` runs preserve that correspondence across one
  append. Concrete new-lookup installation and existing-lookup preservation are
  now exposed directly. The one-step correspondence has also been lifted to
  longer reconstructed concrete histories, with reader-facing corollaries for
  stable decoded lookups, stable indexed pair-array entries, and valid endpoint
  decoded lookups. Remaining work should return to the Pair bridge/oracle/revert
  layers unless a new
  factory-specific behavioral gap is identified.

## Non-Goals

- No formal API parity specs.
- No public or contract-level helper functions added only for proof convenience.
- No aggregate public specs that restate an entire function body field-by-field.
- No local sqrt proof duplication; use Tamago's installed sqrt facts.
