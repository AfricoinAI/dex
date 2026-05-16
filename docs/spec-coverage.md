# Uniswap V2 Spec Coverage Target

This project targets Certora-style coverage for the supported Uniswap V2 core
surface: every public method should have executable success postconditions,
ordered revert obligations, event/trace obligations, and cross-call invariants.
The spec structure should follow Tamago's ERC4626 pattern: keep helper models
outside `verity/spec`, prove executable call postconditions first, use trace
events to connect external-token movement to concrete runs, and then connect
those run-level facts to trace-wide closed-world economic invariants.

Intentionally out of scope versus canonical Uniswap V2 core:

- Protocol-fee minting and `feeTo` / `feeToSetter`.
- LP token `name`, `symbol`, and `permit`.

## Pair

| Area | Current coverage | Gap to full coverage |
| --- | --- | --- |
| Views | Direct storage/value specs for `decimals`, supply, balances, allowances, factory/tokens, reserves, cumulatives, `kLast == 0`. | None for supported view surface. |
| LP ERC20 | Executable approve/transfer/transferFrom success and revert specs for balances, allowances, max allowance, overflow cases, and first-class LP Approval/Transfer event obligations. | Add revert-frame/no-event specs for failed LP ERC20 paths if needed by the final ordered revert matrix. |
| Reentrancy guard | Exact run-result reverts for locked `mint`, `burn`, `swap`, `skim`, and `sync`. | Add success invariant that unlocked is restored to `1` after every successful guarded entrypoint. |
| Mint | Closed-world invariant covers reserve backing and minimum-liquidity lock. Event helper constructors exist. | Add executable first-mint and subsequent-mint postconditions: sqrt/pro-rata liquidity, supply/balance updates, reserve/TWAP update, events, and ordered reverts for overflow, insufficient amount, insufficient liquidity, supply overflow, and recipient balance overflow. |
| Burn | Closed-world invariant covers reserve backing after burn. Event helper constructors exist. | Add executable burn postconditions: pro-rata token amounts, LP balance burn, totalSupply decrease, token transfer traces, reserve/TWAP update, events, and ordered reverts. |
| Swap | Closed-world invariant covers reserve updates and fee-adjusted K. Exact run-result covers locked and zero-output guards. Event helper constructors exist. | Add executable swap postconditions for liquidity, invalid `to`, callback path, amount-in derivation, K check, overflow guards, reserve/TWAP update, token transfer traces, and events. |
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

## Tamago Patterns To Preserve

- Helper definitions belong in `verity/common`, not public spec modules, unless
  they are intended to be Tama obligations.
- Each mutating entrypoint needs small executable specs over the actual
  `(entrypoint ...).run s`: success result, concrete storage deltas, event
  shape, and revert-frame behavior.
- External ERC20/token effects should be modeled with local trace events emitted
  only after the ECM/helper succeeds. Specs should check the exact token,
  sender, receiver, and amount so an omitted or misrouted external call fails.
- Closed-world invariants should quantify over finite reachable traces, but
  each action family should be backed by executable postconditions for the real
  entrypoint path before relying on the ghost transition economically.
- Include adversarial sequence properties, not only one-step invariants. For
  Uniswap V2 that means donation/mint/burn/swap sequences, skim/sync after
  donations, flash-swap callback paths, and round-trip no-free-profit checks.
- For library math, consume Tamago's proved properties where available. Do not
  duplicate sqrt proofs or add assumptions for local convenience.

Foundry tests should mirror these public obligations at bytecode level, but they
do not replace the Lean specs.
