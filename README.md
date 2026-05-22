# Tamaswap

Tamaswap is the **first provably unhackable DEX**.

Tamaswap is modeled after Uniswap v2. The `UniswapV2Pair` and `UniswapV2Factory` contracts are
written in [Verity](https://veritylang.com), compiled to Solidity-equivalent
Yul, and **mathematically proven correct in Lean** — every property below is a
theorem, not a test case.

Built on [Tama](https://tama.tools) (the secure-by-construction Ethereum
toolchain) and [Tamago](https://github.com/Bacon-labs/tamago) (Verity's
standard contract suite). The proved specs are double-checked by Foundry
mirror tests that connect each property to the generated EVM bytecode.

Use Tamaswap at [swap.tama.tools](https://swap.tama.tools).

## What is proved

The full specification lives in
[`verity/spec/TamaUniV2/Spec/`](verity/spec/TamaUniV2/Spec). It is split into
two contracts, each organized into tiers from headline guarantees down to
boundary mechanics. Every spec listed below has a matching Lean proof.

### `UniswapV2Pair` — 15 properties

**Economic safety.**

1. **No free lunch** — no finite sequence of valid actions can increase any
   caller's initial-spot-price portfolio value. The pool cannot be drained,
   sandwiched for free, or otherwise gamed by a sequence of valid calls.
2. **LP-share backing** — reserve product per squared LP supply is monotone
   non-decreasing across every finite reachable history.

**Structural invariants.**

3. **Reserve backing** — cached reserves are always covered by the pair's
   actual ERC20 balances.
4. **uint112 reserve domain** — cached reserves never exceed the canonical
   `uint112` bound.
5. **Minimum-liquidity lock** — once positive LP supply exists,
   `MINIMUM_LIQUIDITY` is permanently locked and never redeemable.
6. **LP supply discipline** — LP total supply changes only on `mint` or
   `burn`.
7. **Reentrancy lock** — once the lock is closed, every mutating entrypoint
   reverts before any durable side effect.
8. **Donations and surplus** — donations are the only source of skimmable
   surplus.
9. **Oracle update rule** — every reserve update advances cumulative prices
   by the canonical UQ112x112-encoded price times elapsed time.

**Boundary mechanics.**

10. **Exact-revert guards** — every guarded failure has a canonical revert
    payload and leaves the pre-call state unchanged.
11. **ERC20 trace boundary** — token movement is modeled by pair-local ERC20
    trace events bridged to the real ERC20 boundary.
12. **LP ERC20 share ledger** — LP `approve` / `transfer` / `transferFrom`
    move share claims only; AMM state, reserves, and token balances are
    unchanged.
13. **Initialization** — factory-only and one-shot; token identities are
    fixed after the first `initialize`.
14. **Views** — view functions return exactly one storage cell (or a
    constant) without mutating state.
15. **Public-call matching** — each successful public mutating call matches
    its closed-world transition, bridging the contract boundary into the
    models used by properties 1–14.

### `UniswapV2Factory` — 9 properties

**Security.**

1. **Unordered pair uniqueness** — each unordered token pair maps to **at
   most one** pair address in any reachable factory history.
2. **Append-only history** — old pair entries are never overwritten,
   reordered, or deleted.

**Correctness.**

3. **Symmetric lookup** — `getPair(A, B)` and `getPair(B, A)` return the same
   address.
4. **Pair entries are well-formed** — every recorded pair has
   `token0 < token1`, two distinct nonzero token addresses, and a nonzero
   pair address.
5. **Length tracks created pairs** — `allPairsLength` equals the number of
   created pairs.
6. **`createPair` appends exactly one new sorted pair** — storage, length,
   array entry, and event are pinned in one bundle on success.
7. **`createPair` rejects invalid input** — identical addresses, the zero
   address, duplicates, CREATE2 failure, and length overflow each revert
   with the right payload; any revert leaves storage unchanged.

**Transparency.**

8. **View functions are pure storage reads** — `getPair`, `allPairsLength`,
   and in/out-of-bounds `allPairs`.
9. **Closed-world matching** — concrete factory storage agrees with the
   modeled history at every reachable state.

## How the proof connects to deployed bytecode

Three layers, kept in lockstep:

- **Source** ([`verity/src/`](verity/src)) — the Verity implementation that
  compiles to Yul, then to deployable Solidity contracts in
  [`src/generated/verity/`](src/generated/verity).
- **Spec** ([`verity/spec/`](verity/spec)) — the properties above, stated as
  Lean propositions against a closed-world model of the pair and factory.
- **Proof** ([`verity/proof/`](verity/proof)) — the Lean theorems that
  discharge each spec against the compiled source.
- **Mirror tests** ([`test/verity/`](test/verity)) — Foundry fuzz and
  invariant tests tagged `tama: mirrors=…` that re-check each proved property
  against the actual EVM artifacts.

Trusted boundaries — CREATE2 deployment, ERC20 `transfer` / `balanceOf`, and
the flash-swap callback — are declared as ECM axioms in `tama.toml` and
documented at the call site. The pair's 0.3% swap fee is on; the optional
protocol-fee `kLast` mint is left off.

## Run

```sh
tama doctor   # check toolchain + generated files
tama check    # type-check the Lean proofs
tama build    # build Verity sources + generated Solidity
tama test     # run Foundry mirror tests
tama audit structure
tama audit storage-layout
tama audit coverage
tama audit trust-boundary
forge test    # run mirror, router, and frontend tests
```

The full `tama audit` suite currently fails only on the `selectors` check
because the pinned Tama selector audit does not accept the canonical Uniswap V2
`Sync(uint112,uint112)` event field type. CI still runs the other audit checks:
`structure`, `storage-layout`, `coverage`, and `trust-boundary`. The pair
bytecode and checked-in interface use the canonical topic, and `tama test`
covers the emitted event signature.

## Periphery and Onchain Frontend

The repo includes a minimal V2 router in `src/TamaRouter.sol` and an
onchain HTML dapp in `src/TamaSwapFrontend.sol`.

- `TamaRouter` supports pool creation through `addLiquidity`, LP mint/burn,
  exact-input and exact-output swaps, native ETH through WETH, wrapping and
  unwrapping, and V2 quote helpers. It intentionally omits permits and
  fee-on-transfer variants.
- `html/tamaswap.html` is the canonical frontend source.
- `script/build-tamaswap.mjs` embeds that HTML into `TamaSwapFrontend`, split
  into data contracts and served through ERC-5219 for `web3://` gateways.

Regenerate the frontend contract after editing the HTML:

```sh
node script/build-tamaswap.mjs
forge test --match-path 'test/periphery/*'
```

Run the browser-backed local frontend test:

```sh
npm run test:e2e
```

The E2E runner starts Anvil, deploys the factory, router, frontend, and two
test ERC20s, serves the generated frontend against those addresses, injects a
minimal EIP-1193 wallet, and drives connection, token-list selection,
liquidity, swap, and DeFiLlama fallback behavior with Playwright. Install
`playwright` or set `PLAYWRIGHT_PATH` if it is not already available locally.

## Repository layout

```text
.
|-- verity/
|   |-- src/TamaUniV2/         # UniswapV2Pair.lean, UniswapV2Factory.lean
|   |-- spec/TamaUniV2/Spec/   # Property specs (pair + factory)
|   |-- proof/TamaUniV2/Proof/ # Lean proofs discharging the specs
|   `-- common/TamaUniV2/      # Shared concrete + ghost models
|-- src/generated/verity/      # Generated Solidity deployers + interfaces
|-- src/TamaRouter.sol         # Minimal V2 router
|-- src/TamaSwapFrontend.sol   # Generated onchain HTML frontend wrapper
|-- html/tamaswap.html         # Canonical frontend source
|-- test/verity/               # Foundry mirror tests (`tama: mirrors=…`)
|-- test/periphery/            # Router and frontend tests
`-- tama.toml                  # Trust surface + coverage configuration
```

## Continuous integration

`.github/workflows/ci.yml` runs `tama doctor --fix` for checkout-only
generated directories, verifies tracked dependency files did not change, then
runs `tama doctor`, `tama build --locked`, `tama test`, and every `tama audit`
check except `selectors` on each push and pull request. The selector audit is
intentionally omitted until Tama supports `uint112` event fields.

## License

Released under the MIT License. See [LICENSE](LICENSE).
