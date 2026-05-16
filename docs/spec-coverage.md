# Uniswap V2 Spec Coverage Target

This project targets Certora-style coverage for the supported Uniswap V2 core
surface: every public method should have executable success postconditions,
ordered revert obligations, event/trace obligations, and cross-call invariants.

Intentionally out of scope versus canonical Uniswap V2 core:

- Protocol-fee minting and `feeTo` / `feeToSetter`.
- LP token `name`, `symbol`, and `permit`.

## Pair

| Area | Current coverage | Gap to full coverage |
| --- | --- | --- |
| Views | Direct storage/value specs for `decimals`, supply, balances, allowances, factory/tokens, reserves, cumulatives, `kLast == 0`. | None for supported view surface. |
| LP ERC20 | Executable approve/transfer/transferFrom success and revert specs for balances, allowances, max allowance, and overflow cases. | Add event-shape assertions for all LP ERC20 paths as first-class specs. |
| Reentrancy guard | Exact run-result reverts for locked `mint`, `burn`, `swap`, `skim`, and `sync`. | Add success invariant that unlocked is restored to `1` after every successful guarded entrypoint. |
| Mint | Closed-world invariant covers reserve backing and minimum-liquidity lock. | Add executable first-mint and subsequent-mint postconditions: sqrt/pro-rata liquidity, supply/balance updates, reserve/TWAP update, events, and ordered reverts for overflow, insufficient amount, insufficient liquidity, supply overflow, and recipient balance overflow. |
| Burn | Closed-world invariant covers reserve backing after burn. | Add executable burn postconditions: pro-rata token amounts, LP balance burn, totalSupply decrease, token transfer traces, reserve/TWAP update, events, and ordered reverts. |
| Swap | Closed-world invariant covers reserve updates and fee-adjusted K. Exact run-result covers locked and zero-output guards. | Add executable swap postconditions for liquidity, invalid `to`, callback path, amount-in derivation, K check, overflow guards, reserve/TWAP update, token transfer traces, and events. |
| Skim | Closed-world invariant covers surplus removal; executable reverts cover locked and balance-below-reserve. | Add executable success spec: transfers exactly `balance - reserve` for both tokens and leaves reserves unchanged. |
| Sync/TWAP | Closed-world invariant covers reserves set to balances; executable overflow/locked reverts exist. | Add executable success spec for reserve update, timestamp wrap, and cumulative-price formula. |

## Factory

| Area | Current coverage | Gap to full coverage |
| --- | --- | --- |
| Views | Direct storage/value specs for `getPair`, `allPairs`, and `allPairsLength`; out-of-bounds exact revert. | None for supported view surface. |
| Create pair guards | Exact run-result reverts for identical, zero, and duplicate pairs. | Add ordered reverts for CREATE2 failure and pair-count overflow. |
| Create pair success | Not yet specified at full executable level. | Add sorting, bidirectional pair mapping, append/length update, deterministic nonzero pair result assumption boundary, pair initialize call, and `PairCreated` event obligations. |

## Global Invariants

- Reserves stay within `uint112`.
- Successful mint/burn/swap/sync leave reserves equal to modeled pair token balances.
- Fee-adjusted swap invariant is preserved.
- Nonzero LP supply permanently includes locked `MINIMUM_LIQUIDITY`.
- `kLast()` is always `0` for the fee-off-only target.
- Pair token addresses remain immutable after initialization.
- Factory pair mapping is symmetric and no duplicate sorted pair can be created.

Foundry tests should mirror these public obligations at bytecode level, but they
do not replace the Lean specs.
