import TamaUniV2.UniswapV2Pair
import TamaUniV2.Common.UniswapV2PairConcrete
import TamaUniV2.Common.UniswapV2PairGhost

namespace TamaUniV2.Spec.UniswapV2PairSpec

open Verity
open Verity.EVM.Uint256
open TamaUniV2.UniswapV2Pair
open TamaUniV2.Common.UniswapV2PairConcrete
open TamaUniV2.Common.UniswapV2PairGhost

/-!
# UniswapV2Pair — Behavior Specification

Specs follow Tamago's ERC4626 style: local storage/accounting obligations
are proved directly, external-token movement is connected through pair-local
ghost transfer traces, and the remaining assumptions sit at ERC20 calls,
callbacks, and CREATE2 deployment. The 0.3% swap fee is enabled; the
optional protocol fee mint (which would write `kLast`) is not, so `kLast`
is the constant zero read.

## Properties

### Tier 1 — Economic safety

1. From any reachable state, no finite sequence of valid actions can
   increase a single caller's initial-spot-price portfolio value (wallet
   tokens + LP-claimed reserves + skimmable surplus).

2. Pool spot value over cached reserves cannot decrease across same-LP-supply
   paths.

3. Cached K can only fall via burn.

4. Actual token-balance value loss across same-LP-supply or no-mint-no-burn
   paths is bounded by initial surplus over cached reserves. With zero
   surplus and no donation, the path preserves actual-balance value exactly.

### Tier 2 — Structural invariants

5. Cached reserves are covered by actual ERC20 balances along every finite
   reachable history.

6. Cached reserves never exceed the uint112 bound.

7. Once positive LP supply exists, the locked `MINIMUM_LIQUIDITY` floor is
   monotone non-decreasing and never redeemable.

8. LP supply changes only on mint or burn.

9. Once the reentrancy lock is closed, every mutating entrypoint reverts
   before durable side effects.

10. Donations are the only source of skimmable surplus.

### Tier 3 — Boundary mechanics

11. Each successful public mutating call matches its closed-world transition,
    so the closed-world theorems apply at the contract boundary.

12. Every guarded failure has a canonical revert payload and leaves the
    pre-call state unchanged.

13. Token movement is modeled by pair-local ERC20 trace events.

14. LP approve/transfer/transferFrom move share claims only; AMM state,
    reserves, and token balances are unchanged.

15. Initialization is factory-only and one-shot; after the first
    `initialize`, token identities are fixed.

16. Views return exactly one storage cell (or a constant) without mutating
    state.
-/

/-!
## Closed-World Economic Invariants

Quantification is over every finite successful transition sequence in
`PairWorldReachable`. External ERC20 movement is represented by explicit
mint/burn/swap/donate/skim/sync steps; assumptions live only at the ERC20,
callback, and CREATE2 boundaries.
-/

/-!
### 1. Single-Caller Portfolio Safety

When one caller owns every LP token except the permanently locked minimum
liquidity, no finite sequence of valid interactions can make the caller
richer at the initial spot price. The portfolio is wallet tokens + LP claim
on cached reserves + skimmable surplus. `callerDonate` models fresh token
inflows; `mint` and `swap` consume surplus already visible to the pair.
-/

/-- A valid single-caller swap cannot increase the caller's portfolio value at
the starting spot price. -/
def pair_wallet_swap_does_not_increase_portfolio_value
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWalletWorldState) : Prop :=
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletStep
              (PairWalletAction.callerSwap amount0In amount1In amount0Out amount1Out)
              before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-- A valid single-caller mint cannot increase the caller's portfolio value at
the starting spot price. It converts already-visible surplus into LP ownership
using the pool's pro-rata mint rule. -/
def pair_wallet_mint_does_not_increase_portfolio_value
    (amount0 amount1 liquidity : Nat)
    (before after : PairWalletWorldState) : Prop :=
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletStep
              (PairWalletAction.callerMint amount0 amount1 liquidity)
              before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-- A valid single-caller burn cannot increase the caller's portfolio value at
the starting spot price. It turns LP ownership into wallet tokens using the
pool's pro-rata redemption rule. -/
def pair_wallet_burn_does_not_increase_portfolio_value
    (amount0 amount1 liquidity : Nat)
    (before after : PairWalletWorldState) : Prop :=
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletStep
              (PairWalletAction.callerBurn amount0 amount1 liquidity)
              before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-- `skim` moves already-skimmable surplus into the caller wallet. Because that
surplus was already counted as caller-controlled value, `skim` cannot increase
portfolio value. -/
def pair_wallet_skim_does_not_increase_portfolio_value
    (before after : PairWalletWorldState) : Prop :=
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletStep
              (PairWalletAction.callerSkimReceive
                (PairWorldSurplus0 before.pair)
                (PairWorldSurplus1 before.pair))
              before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-- `approve`, direct donations, and `sync` cannot increase caller portfolio
value. Donations only move wallet value into skimmable surplus, and `sync` can
only move surplus into reserves where the caller owns no more than the unlocked
LP share. -/
def pair_wallet_passive_action_does_not_increase_portfolio_value
    (action : PairWalletAction) (before after : PairWalletWorldState) : Prop :=
  (action = PairWalletAction.callerApprove ∨
    action = PairWalletAction.callerSync ∨
    ∃ amount0 amount1, action = PairWalletAction.callerDonate amount0 amount1) →
    PairWalletGood before →
      0 < before.pair.totalSupply →
        0 < before.pair.reserve0 →
          0 < before.pair.reserve1 →
            PairWalletStep action before after →
              PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                  before.pair.totalSupply ≤
                PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                  after.pair.totalSupply

/--
Single-caller portfolio no-profit theorem.

Assume the caller is the only LP owner other than the permanent minimum
liquidity lock. After any finite sequence of valid caller actions, the caller's
portfolio value at the initial spot price is no greater than it was at the
start.

The theorem does not assume the caller's LP balance or the pool's total LP
supply is unchanged. Mint and burn may change both; their ratio discipline is
handled by the LP-normalized reserve-backing invariant above.
-/
def pair_wallet_single_caller_history_no_portfolio_profit
    (before after : PairWalletWorldState) : Prop :=
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletHistory before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-!
### 2. Successful Calls As Caller-Wallet Steps

A successful public call identifies a single caller-wallet step. The swap
link is the prepaid-input case: input visible as surplus at call entry.
Flash repayment composes caller token movement with the swap rule.
-/

/-- A successful first `mint`, after its public-call accounting facts are known,
is one caller-wallet mint step. -/
def pair_successful_first_mint_matches_caller_wallet_mint
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256)
    (before after : PairWalletWorldState) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    before.pair = pairWorldBeforeMintRun s →
                      after.pair = pairWorldAfterFirstMintRun s →
                        amount0.val = PairWorldSurplus0 before.pair →
                          amount1.val = PairWorldSurplus1 before.pair →
                            after.callerToken0 = before.callerToken0 →
                              after.callerToken1 = before.callerToken1 →
                                after.callerLp = before.callerLp + liquidity.val →
                                  PairWalletStep
                                    (PairWalletAction.callerMint
                                      amount0.val amount1.val liquidity.val)
                                    before after

/-- A successful later `mint`, after its public-call accounting facts are known,
is one caller-wallet mint step. -/
def pair_successful_subsequent_mint_matches_caller_wallet_mint
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256)
    (liquidity : Uint256) (before after : PairWalletWorldState) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot > 0 →
          s.storage reserve1Slot.slot > 0 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          before.pair = pairWorldBeforeMintRun s →
                            after.pair = pairWorldAfterSubsequentMintRun liquidity s →
                              amount0.val = PairWorldSurplus0 before.pair →
                                amount1.val = PairWorldSurplus1 before.pair →
                                  after.callerToken0 = before.callerToken0 →
                                    after.callerToken1 = before.callerToken1 →
                                      after.callerLp = before.callerLp + liquidity.val →
                                        PairWalletStep
                                          (PairWalletAction.callerMint
                                            amount0.val amount1.val liquidity.val)
                                          before after

/-- A successful `burn`, after its public-call accounting facts are known, is
one caller-wallet burn step. -/
def pair_successful_burn_matches_caller_wallet_burn
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256))
    (before after : PairWalletWorldState) : Prop :=
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (amount0, amount1) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          liquidity.val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
              amount0 > 0 →
                amount1 > 0 →
                  amount0 ≤ observedBalance0 s →
                    amount1 ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          amount0.val * (burnSupply s).val ≤
                              liquidity.val * (observedBalance0 s).val →
                            amount1.val * (burnSupply s).val ≤
                                liquidity.val * (observedBalance1 s).val →
                              before.pair = pairWorldFromConcreteState s →
                                after.pair = pairWorldAfterBurnRun s →
                                  before.callerLp ≥ liquidity.val →
                                    after.callerToken0 =
                                        before.callerToken0 + amount0.val →
                                      after.callerToken1 =
                                          before.callerToken1 + amount1.val →
                                        after.callerLp =
                                            before.callerLp - liquidity.val →
                                          PairWalletStep
                                            (PairWalletAction.callerBurn
                                              amount0.val amount1.val liquidity.val)
                                            before after

/-- A successful prepaid-input `swap`, after its public-call accounting facts
are known, is one caller-wallet swap step. -/
def pair_successful_swap_matches_caller_wallet_swap
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit)
    (before after : PairWalletWorldState) : Prop :=
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                          before.pair = pairWorldFromConcreteState s →
                            after.pair = pairWorldAfterSwapRun balance0Now balance1Now s →
                              amount0In.val = PairWorldSurplus0 before.pair →
                                amount1In.val = PairWorldSurplus1 before.pair →
                                  after.callerToken0 =
                                      before.callerToken0 + amount0Out.val →
                                    after.callerToken1 =
                                        before.callerToken1 + amount1Out.val →
                                      after.callerLp = before.callerLp →
                                        PairWalletStep
                                          (PairWalletAction.callerSwap
                                            amount0In.val amount1In.val
                                            amount0Out.val amount1Out.val)
                                          before after

/-- A successful `skim` is one caller-wallet skim step: it moves already-counted
surplus to the caller wallet. -/
def pair_successful_skim_matches_caller_wallet_skim
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit)
    (before after : PairWalletWorldState) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      before.pair = pairWorldFromConcreteState s →
        after.pair = pairWorldAfterSkimRun s →
          after.callerToken0 =
              before.callerToken0 + PairWorldSurplus0 before.pair →
            after.callerToken1 =
                before.callerToken1 + PairWorldSurplus1 before.pair →
              after.callerLp = before.callerLp →
                PairWalletStep
                  (PairWalletAction.callerSkimReceive
                    (PairWorldSurplus0 before.pair)
                    (PairWorldSurplus1 before.pair))
                  before after

/-- A successful `sync` is one caller-wallet sync step: token balances stay in
the pair and the caller wallet is unchanged. -/
def pair_successful_sync_matches_caller_wallet_sync
    (s : ContractState) (result : ContractResult Unit)
    (before after : PairWalletWorldState) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      before.pair = pairWorldFromConcreteState s →
        after.pair = pairWorldAfterSyncRun s →
          after.callerToken0 = before.callerToken0 →
            after.callerToken1 = before.callerToken1 →
              after.callerLp = before.callerLp →
                PairWalletStep PairWalletAction.callerSync before after



/-- The same no-profit theorem written as a direct pool-value comparison.
`PairWorldSpotValueNum before w` is the value of pool `w` at the initial
`before.reserve1 / before.reserve0` spot price, multiplied by
`before.reserve0` to avoid division. If this value cannot decrease, a caller who
ends with the same LP supply cannot have extracted positive spot-value profit
from the pool inside the closed-world trace. -/
def pair_closed_world_reachable_same_supply_path_pool_value_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
            0 < before.reserve1 →
              PairWorldSpotValueNum before before ≤
                PairWorldSpotValueNum before after


/--
The same no-profit theorem in the denomination a user would use for an
economic sanity check. `PairWorldSpotValueNum before pool` is the token1 value
of `pool`, using the initial spot price `before.reserve1 / before.reserve0`,
multiplied by `before.reserve0` to avoid division. If LP supply ends where it
started, every finite successful closed-world history leaves that
token1-denominated pool value nondecreasing; a caller cannot make positive
spot-value profit without an external gift.
-/
def pair_closed_world_reachable_same_supply_path_no_token1_denominated_profit
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
            0 < before.reserve1 →
              PairWorldSpotValueNum before before ≤
                PairWorldSpotValueNum before after

/--
Actual-balance no-profit with the `skim` exception made explicit. Cached
reserve value is the AMM's economic invariant, but actual ERC20 balances may
include donated surplus above reserves. A same-LP-supply history may remove
that pre-existing surplus with `skim`; what it cannot do is remove more
token1-denominated value than the initial surplus was worth at the initial
spot price. This is the non-balanced generalization of the token-balance
no-extraction theorem below.
-/
def pair_closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldBalanceSpotValueNum before before ≤
            PairWorldBalanceSpotValueNum before after +
              PairWorldSurplusSpotValueNum before before

/--
Caller profit bounded by starting surplus for same-supply histories.

Actual token balances may include donations above cached reserves. The pool
theorem above says a same-LP-supply history can reduce actual token-balance
value only by consuming that starting surplus. This theorem states the
corresponding caller-facing bound: if caller-plus-pair actual token-balance
value is merely redistributed, the caller's gain cannot exceed the surplus that
was already outside the AMM's cached reserves at the start.
-/
def pair_closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          callerValueBefore + PairWorldBalanceSpotValueNum before before =
            callerValueAfter + PairWorldBalanceSpotValueNum before after →
            callerValueAfter ≤
              callerValueBefore + PairWorldSurplusSpotValueNum before before

/-- Zero-surplus actual-balance no-extraction, stated in invariant language.

The bounded theorem above says any actual-token-balance loss must come out of
surplus that was already sitting above cached reserves at the start. This is
the clean corollary a maintainer wants to read: if there is no such starting
surplus on either token side, then a same-LP-supply finite history cannot make
the pair's actual ERC20 token balances worth less at the initial spot price.

Donations may still appear later in the history; they are external gifts. The
claim is that the pair mechanics cannot turn a zero-surplus starting point into
net extraction when LP supply returns to its starting value. -/
def pair_closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          PairWorldPath before after →
            before.totalSupply = after.totalSupply →
              PairWorldBalanceSpotValueNum before before ≤
                PairWorldBalanceSpotValueNum before after

/--
Caller no-profit as the external-wallet reading of the pool-value theorem.

The Pair model tracks the pair's token balances directly. It does not invent a
wallet ledger for every possible external caller. Instead, this short theorem
states the exact logical step a caller ledger would need: if the caller's
spot-priced value plus the pair's spot-priced token-balance value is the same
before and after a same-LP-supply history, then the caller cannot finish with
more value.

This is intentionally a small consequence, not a replacement for the pool
invariants above. The zero-surplus premise rules out treating a pre-existing
donation as pair-owned value; the equality premise says the history only
redistributes value between the caller and the pair at the initial spot price.
-/
def pair_closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          PairWorldPath before after →
            before.totalSupply = after.totalSupply →
              callerValueBefore + PairWorldBalanceSpotValueNum before before =
                callerValueAfter + PairWorldBalanceSpotValueNum before after →
                callerValueAfter ≤ callerValueBefore

/--
Caller no-profit over cached reserve value for arbitrary same-supply histories.

The pool-side theorem says the pair's reserve-denominated value cannot go down
when LP supply starts and ends at the same value. This short consequence is the
external-wallet reading of that fact: if the caller's spot-priced value plus
the pair's reserve-priced value is only redistributed across the history, then
the caller cannot finish richer. It is stated separately from the token-balance
version because reserve value is the AMM invariant; actual token-balance value
needs the zero-surplus premise handled above.
-/
def pair_closed_world_reachable_same_supply_path_no_caller_spot_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          callerValueBefore + PairWorldSpotValueNum before before =
            callerValueAfter + PairWorldSpotValueNum before after →
            callerValueAfter ≤ callerValueBefore

/-- The strongest reader-facing same-supply no-extraction statement. For a
reachable nonempty pool, positive reserves are no longer an extra assumption;
they follow from the nondegeneracy invariant above. Therefore any finite
successful history that returns LP supply to its starting value leaves the pool
worth at least as much at the initial spot price. -/
def pair_closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldSpotValueNum before before ≤
            PairWorldSpotValueNum before after

/-- Actual token-balance no-extraction under the right closed-world premise.

Reserve-value no-profit is the core AMM theorem, but users naturally think in
terms of the pair's ERC20 token balances. This theorem makes that connection
explicit without smuggling in a false claim about donated surplus: if the start
state has no surplus over cached reserves, then any finite successful history
that returns LP supply to its starting value leaves the pair's actual token
balances worth at least as much at the initial spot price. If the start state
already contains surplus, a later `skim` may remove that external gift; that is
why the balanced-start premise is part of the statement. -/
def pair_closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      before.balance0 = before.reserve0 →
        before.balance1 = before.reserve1 →
          PairWorldPath before after →
            before.totalSupply = after.totalSupply →
              PairWorldBalanceSpotValueNum before before ≤
                PairWorldBalanceSpotValueNum before after

/-- Common operational form of actual token-balance no-extraction. If the
history contains no mint and no burn, the LP-supply firewall proves the
same-supply premise automatically. Starting from a balanced pool, ordinary LP
bookkeeping, donations, swaps, skim, and sync cannot reduce the pair's actual
token-balance value at the initial spot price. -/
def pair_closed_world_reachable_balanced_no_mint_burn_path_no_token_balance_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      before.balance0 = before.reserve0 →
        before.balance1 = before.reserve1 →
          PairWorldPathNoMintBurn before after →
            PairWorldBalanceSpotValueNum before before ≤
              PairWorldBalanceSpotValueNum before after

/-- Common operational form of the surplus-bounded token-balance theorem. If a
history contains no mint and no burn, LP supply preservation supplies the
same-supply premise automatically. Such histories cannot reduce actual
token-balance value by more than the start state's donated surplus. -/
def pair_closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPathNoMintBurn before after →
        PairWorldBalanceSpotValueNum before before ≤
          PairWorldBalanceSpotValueNum before after +
            PairWorldSurplusSpotValueNum before before

/--
Common operational caller bound with donated surplus made explicit. Histories
with no mint and no burn preserve LP supply, so the same caller-profit bound
applies without restating a same-supply premise: ordinary pair operation can
only increase caller actual-token-balance value by consuming surplus that was
already donated above cached reserves.
-/
def pair_closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPathNoMintBurn before after →
        callerValueBefore + PairWorldBalanceSpotValueNum before before =
          callerValueAfter + PairWorldBalanceSpotValueNum before after →
          callerValueAfter ≤
            callerValueBefore + PairWorldSurplusSpotValueNum before before

/-- Common operational zero-surplus no-extraction theorem. Histories with no
mint and no burn preserve LP supply by the supply firewall, so the same
actual-balance no-extraction conclusion applies without restating a same-supply
premise. This is the most direct closed-world expression of "ordinary pair
operation cannot profitably reduce actual token balances from a clean starting
state." -/
def pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          PairWorldPathNoMintBurn before after →
            PairWorldBalanceSpotValueNum before before ≤
              PairWorldBalanceSpotValueNum before after

/--
Common operational caller no-profit. Histories with no mint and no burn preserve
LP supply, so the caller no-profit theorem above applies without making the
reader restate the same-supply premise. If a zero-surplus reachable pool goes
through only non-liquidity actions and caller-plus-pair spot value is merely
redistributed, the caller cannot finish with more value.
-/
def pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          PairWorldPathNoMintBurn before after →
            callerValueBefore + PairWorldBalanceSpotValueNum before before =
              callerValueAfter + PairWorldBalanceSpotValueNum before after →
              callerValueAfter ≤ callerValueBefore

/--
Clean non-liquidity histories preserve the whole accounting story.

This is the everyday successful-operation case stated without extra machinery:
start from a reachable pool whose actual token balances match its cached
reserves, run any finite history with no direct token donation into the pair and
no mint or burn, and the endpoint is still balanced. In the same trace, the
pair's actual token balances cannot be worth less at the initial spot price.

The two premises rule out the two ways this statement could otherwise be
misread. `NoDonation` excludes new surplus that later `skim` could transfer
away; `NoMintBurn` excludes intentional liquidity provision or redemption.
-/
def pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          PairWorldPathNoDonation before after →
            PairWorldPathNoMintBurn before after →
              after.balance0 = after.reserve0 ∧
              after.balance1 = after.reserve1 ∧
              PairWorldBalanceSpotValueNum before before ≤
                PairWorldBalanceSpotValueNum before after

/--
Caller-facing form of the clean non-liquidity theorem.

The previous theorem is pool-side: the pair stays balanced and does not lose
spot-priced token-balance value. This short consequence says what that means
for an external caller ledger. If the caller's value plus the pair's actual
token-balance value is merely redistributed across such a clean non-liquidity
history, then the caller cannot finish richer.
-/
def pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          PairWorldPathNoDonation before after →
            PairWorldPathNoMintBurn before after →
              callerValueBefore + PairWorldBalanceSpotValueNum before before =
                callerValueAfter + PairWorldBalanceSpotValueNum before after →
                after.balance0 = after.reserve0 ∧
                after.balance1 = after.reserve1 ∧
                callerValueAfter ≤ callerValueBefore

/--
Common operational caller no-profit over cached reserve value.

Most live pair activity that is not liquidity provision or redemption leaves LP
supply unchanged. This theorem exposes that common case directly: for any
reachable nonempty pool, a history with no mint and no burn cannot make a caller
richer at the initial spot price if caller-plus-pool reserve value is merely
redistributed. It is the reserve-value counterpart to the zero-surplus
token-balance theorem above.
-/
def pair_closed_world_reachable_no_mint_burn_path_no_caller_spot_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPathNoMintBurn before after →
        callerValueBefore + PairWorldSpotValueNum before before =
          callerValueAfter + PairWorldSpotValueNum before after →
          callerValueAfter ≤ callerValueBefore


/-- Common-case no-extraction without extra spot-price premises. A reachable
nonempty pool already has positive reserves, and a history with no mint and no
burn preserves LP supply. Therefore share transfers, donations, swaps, skim,
and sync cannot extract spot value from the pool at the initial price. -/
def pair_closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPathNoMintBurn before after →
        PairWorldSpotValueNum before before ≤
          PairWorldSpotValueNum before after

/-- Common-case K preservation for non-liquidity histories. A reachable path
with no mint and no burn is made of LP bookkeeping, donations, swaps, skim, and
sync. None of those actions can reduce cached reserve product, so K is monotone
over the whole finite history. -/
def pair_closed_world_reachable_no_mint_burn_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoMintBurn before after →
      PairWorldK before ≤ PairWorldK after


/- Raw K may rise because of swaps, donations, or reserve synchronization, and
it may fall when LP shares are intentionally redeemed. This classifier states
the security-critical direction: if K falls across one valid step from a good
state, the step must have been a burn. -/
def pair_closed_world_k_decrease_requires_burn
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      PairWorldK after < PairWorldK before →
        ∃ amount0 amount1 liquidity,
          action = PairWorldAction.burn amount0 amount1 liquidity


/-- The path-level K classifier in reader-facing form. From any reachable pool
state, a finite successful history with no burn step cannot reduce cached K.
Equivalently, any finite-history K decrease must include liquidity redemption
somewhere in the path. -/
def pair_closed_world_reachable_no_burn_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoBurn before after →
      PairWorldK before ≤ PairWorldK after

/--
The contrapositive K classifier, stated the way an auditor usually asks the
question. Suppose a reachable pool has some successful finite history whose
endpoint has lower cached K. Then that same endpoint cannot also be reached by a
burn-free history. In other words, K loss is not a swap/skim/sync/transfer
phenomenon; it requires LP redemption somewhere in the history.
-/
def pair_closed_world_reachable_k_decrease_excludes_burn_free_path
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      PairWorldK after < PairWorldK before →
        ¬ PairWorldPathNoBurn before after


/-!
### 3. Sequence-Level Economic Consequences

No-burn histories never decrease cached K. Mint and burn may change raw K,
but valid pro-rata transitions cannot decrease `K / totalSupply^2` while LP
supply is positive, so a finite path starting and ending with the same
positive LP supply cannot reduce raw K. Constant-product geometry then
turns that K bound into a spot-value no-profit statement.
-/


/-- The reachable-state version of the LP-share backing theorem. Starting from
any actually reachable pool with positive LP supply, every finite successful
path leaves reserve product per squared LP supply at least as strong as it was
at the start. This is the global mint/burn ratio guarantee in one sentence. -/
def pair_closed_world_reachable_path_lp_share_backing_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        PairWorldKPerSupplyNondecreasing before after

/-!
### 4. Swap Safety

A successful swap must actually send output, must receive input, must keep each
output below the cached reserve, and must satisfy both the fee-adjusted K check
and raw cached-K nondecrease. This is the heart of the constant-product safety
argument for the fee-off pair.
-/

def pair_closed_world_swap_updates_reserves_to_balances
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
    after.reserve0 = after.balance0 ∧
    after.reserve1 = after.balance1

def pair_closed_world_swap_respects_fee_adjusted_k
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
    feeAdjustedBalance after.balance0 amount0In *
        feeAdjustedBalance after.balance1 amount1In ≥
      requiredK before.reserve0 before.reserve1

/-- Canonical Uniswap's swap guard is fee-adjusted, but the surrounding
economic argument often cites raw reserve-product monotonicity. Once a swap's
cached reserves are the final balances, the fee-adjusted K check alone implies
raw cached K cannot decrease.
The raw-K fact is therefore derived, not an extra assumption about swaps. -/
def pair_closed_world_fee_adjusted_swap_implies_raw_k
    (amount0In amount1In : Nat)
    (before after : PairWorldState) : Prop :=
  after.reserve0 = after.balance0 →
    after.reserve1 = after.balance1 →
      feeAdjustedBalance after.balance0 amount0In *
          feeAdjustedBalance after.balance1 amount1In ≥
        requiredK before.reserve0 before.reserve1 →
        PairWorldK before ≤ PairWorldK after

def pair_closed_world_swap_preserves_good
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
      PairWorldGood after

def pair_closed_world_swap_never_decreases_k
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
    PairWorldK before ≤ PairWorldK after

def pair_closed_world_swap_has_input_and_output
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
    (0 < amount0Out ∨ 0 < amount1Out) ∧
    (0 < amount0In ∨ 0 < amount1In)

/-- The final balances used by swap safety are the balances after optimistic
output and inferred input. This is the closed-world flash-swap accounting rule:
callback-visible repayment, direct prepayment, and ordinary swaps all reduce to
the same equation before the fee-adjusted K check is applied. -/
def pair_closed_world_swap_final_balances_account_for_input_and_output
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
    after.balance0 + amount0Out = before.reserve0 + amount0In ∧
    after.balance1 + amount1Out = before.reserve1 + amount1In

/-- Flash-swap safety depends on the order of the economic check. The K
inequality is not charged against the balances immediately after optimistic
output; it is charged against the final balances after direct input or callback
repayment has arrived. This theorem packages that relationship: the same final
balances that account for output and inferred input are the balances used by
the fee-adjusted K check. -/
def pair_closed_world_swap_k_uses_final_balances
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
    after.balance0 + amount0Out = before.reserve0 + amount0In ∧
    after.balance1 + amount1Out = before.reserve1 + amount1In ∧
    feeAdjustedBalance after.balance0 amount0In *
        feeAdjustedBalance after.balance1 amount1In ≥
      requiredK before.reserve0 before.reserve1

def pair_closed_world_swap_outputs_below_reserves
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
    amount0Out < before.reserve0 ∧
    amount1Out < before.reserve1

def pair_closed_world_swap_preserves_liquidity_supply
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

/-- A valid swap cannot be a pool-value extraction at the starting spot price.
The pair may exchange token0 for token1 or token1 for token0, but from a good
live pool with a defined spot price the final reserves are worth at least the
starting reserves at that same price. This is the one-swap form of the
sequence-level no-profit theorem below. -/
def pair_closed_world_swap_no_spot_value_extraction
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      0 < before.reserve0 →
        0 < before.reserve1 →
          PairWorldStep
              (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
              before after →
            PairWorldSpotValueNum before before ≤
              PairWorldSpotValueNum before after

/-- Reachable one-swap no-extraction. This is the same economic claim in the
form a reader usually wants to cite: if the pool is reachable and nonempty, the
invariant layer already supplies the good-state and positive-reserve facts, so
a valid swap cannot reduce pool value at the starting spot price. -/
def pair_closed_world_reachable_positive_supply_swap_no_spot_value_extraction
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldStep
          (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
          before after →
        PairWorldSpotValueNum before before ≤
          PairWorldSpotValueNum before after

/--
Caller-facing one-swap no-profit.

The theorem above is stated from the pool's point of view: after a valid swap,
the pool's reserves are worth at least as much at the starting spot price. This
short consequence states the same fact from the caller's wallet perspective.
If the caller's spot-priced token value plus the pool's spot-priced reserve
value is only redistributed by the swap, then the caller cannot finish with
more spot-priced value than they started with.

The equality premise is deliberately explicit. The Pair model proves the pool
cannot be the source of profit; a separate caller ledger or token-world replay
must establish that the swap merely redistributes value between that caller and
the pair.
-/
def pair_closed_world_reachable_positive_supply_swap_no_caller_spot_profit
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldStep
          (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
          before after →
        callerValueBefore + PairWorldSpotValueNum before before =
          callerValueAfter + PairWorldSpotValueNum before after →
          callerValueAfter ≤ callerValueBefore

/--
Caller-facing one-swap no-profit over actual pair token balances.

The previous theorem measures cached reserve value. This version is the token
balance statement a user usually wants when the pool starts clean: if there is
no surplus above cached reserves before the swap, then the pair's actual token
balances are the value source that matters. A valid swap preserves LP supply,
so it is a same-supply history; the general same-supply no-profit theorem then
rules out caller profit under the explicit caller-plus-pair value conservation
premise.
-/
def pair_closed_world_reachable_zero_surplus_swap_no_caller_token_balance_profit
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          PairWorldStep
              (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
              before after →
            callerValueBefore + PairWorldBalanceSpotValueNum before before =
              callerValueAfter + PairWorldBalanceSpotValueNum before after →
              callerValueAfter ≤ callerValueBefore

/-!
### 5. Liquidity Creation And Redemption

Mint and burn are the only transitions that intentionally reshape LP supply.
The mint side updates reserves to the token balances and grants no more than the
minimum pro-rata LP share on subsequent mints. The burn side redeems no more
than the caller's pro-rata token balances, updates reserves to the post-transfer
balances, and keeps the permanently locked minimum liquidity out of circulation.
-/

def pair_closed_world_mint_updates_reserves_to_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    after.reserve0 = after.balance0 ∧
    after.reserve1 = after.balance1

/-- A valid mint adds token balances and then caches those balances as reserves,
so minting liquidity cannot make the raw reserve product smaller. -/
def pair_closed_world_mint_never_decreases_k
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    PairWorldK before ≤ PairWorldK after

def pair_closed_world_mint_preserves_good
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
      PairWorldGood after

def pair_closed_world_mint_liquidity_ratio
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    before.totalSupply = 0 ∨
      liquidity * before.reserve0 ≤ amount0 * before.totalSupply ∧
      liquidity * before.reserve1 ≤ amount1 * before.totalSupply

/-- Once a pool already has LP supply, a valid mint cannot dilute existing LPs:
measured as reserve product per squared LP supply, the pool is at least as
strong after the mint as before it. The first mint is excluded because there
are no preexisting LP shares to dilute. -/
def pair_closed_world_mint_does_not_dilute_existing_lp_share
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
        PairWorldKPerSupplyNondecreasing before after

def pair_closed_world_burn_updates_reserves_to_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    after.reserve0 = after.balance0 ∧
    after.reserve1 = after.balance1

def pair_closed_world_burn_preserves_good
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
      PairWorldGood after

def pair_closed_world_burn_liquidity_ratio
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    amount0 * before.totalSupply ≤ liquidity * before.balance0 ∧
    amount1 * before.totalSupply ≤ liquidity * before.balance1

/-- A burn may lower raw K because assets leave the pool, but it cannot extract
more than the burned LP share is entitled to. The remaining pool's reserve
product per squared LP supply is therefore at least as strong after the burn. -/
def pair_closed_world_burn_does_not_dilute_remaining_lp_share
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
        PairWorldKPerSupplyNondecreasing before after

/-!
### 6. LP Supply Discipline

Uniswap V2 LP shares are not allowed to become an implicit source or sink of
pool assets. Share-only actions leave the pool model exactly unchanged; mint and
burn are the only transitions that can change total LP supply; the first mint
permanently locks `MINIMUM_LIQUIDITY`; and burn cannot redeem that locked
liquidity.
-/

def pair_closed_world_nonzero_supply_locks_minimum_liquidity
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    w.totalSupply ≠ 0 →
      w.lockedLiquidity = minimumLiquidityNat ∧
      minimumLiquidityNat ≤ w.totalSupply

def pair_closed_world_zero_supply_has_no_locked_liquidity
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    w.totalSupply = 0 →
      w.lockedLiquidity = 0

def pair_closed_world_locked_liquidity_never_exceeds_supply
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    w.lockedLiquidity ≤ w.totalSupply

/-- The minimum-liquidity lock as a trace invariant. Starting from any reachable
pool and following any finite successful modeled history, the final state is
either still empty with no locked liquidity or has the canonical permanently
locked `MINIMUM_LIQUIDITY` amount covered by total LP supply. -/
def pair_closed_world_reachable_path_minimum_liquidity_lock
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      (after.totalSupply = 0 ∧ after.lockedLiquidity = 0) ∨
        (0 < after.totalSupply ∧
          after.lockedLiquidity = minimumLiquidityNat ∧
          minimumLiquidityNat ≤ after.totalSupply)

/-- "Permanent" liquidity is monotone. From a good modeled state, a successful
single action can establish the locked floor on first mint or preserve the
current lock, but it cannot reduce the locked amount. -/
def pair_closed_world_step_locked_liquidity_never_decreases
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      before.lockedLiquidity ≤ after.lockedLiquidity


/-- Reader-facing reachable form: in every reachable pool history, the locked
liquidity amount is monotone. Once the first mint installs
`MINIMUM_LIQUIDITY`, later mint, burn, swap, skim, sync, donation, and share
bookkeeping actions cannot reduce it. -/
def pair_closed_world_reachable_path_locked_liquidity_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      before.lockedLiquidity ≤ after.lockedLiquidity

def pair_closed_world_supply_changes_only_on_mint_or_burn
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    after.totalSupply ≠ before.totalSupply →
      (∃ amount0 amount1 liquidity,
        action = PairWorldAction.mint amount0 amount1 liquidity) ∨
      (∃ amount0 amount1 liquidity,
        action = PairWorldAction.burn amount0 amount1 liquidity)

/-- Cached reserve movement is isolated to reserve-update actions. Share
bookkeeping may move LP ownership, direct donations may raise token balances,
and `skim` may remove surplus, but none of those actions can rewrite the
router-visible reserves. If either cached reserve changes in one valid action,
the step must be mint, burn, swap, or sync. -/
def pair_closed_world_reserve_changes_only_on_reserve_update_actions
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (after.reserve0 ≠ before.reserve0 ∨
      after.reserve1 ≠ before.reserve1) →
      (∃ amount0 amount1 liquidity,
        action = PairWorldAction.mint amount0 amount1 liquidity) ∨
      (∃ amount0 amount1 liquidity,
        action = PairWorldAction.burn amount0 amount1 liquidity) ∨
      (∃ amount0In amount1In amount0Out amount1Out,
        action = PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
      action = PairWorldAction.sync


/-- Cached reserve movement requires a reserve-update action. If either cached
reserve differs at the endpoint, then the endpoint cannot be produced by a
successful history made only of LP bookkeeping, direct donations, and skim.
Some mint, burn, swap, or sync step must be present in the history. -/
def pair_closed_world_reachable_reserve_change_requires_reserve_update
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    (after.reserve0 ≠ before.reserve0 ∨
      after.reserve1 ≠ before.reserve1) →
      ¬ PairWorldPathNoReserveUpdate before after


/-- Reachable-state form of the same supply firewall. Starting from any
reachable pool, every finite successful history made only of share transfers,
approvals, donations, swaps, skim, and sync preserves LP supply exactly. -/
def pair_closed_world_reachable_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoMintBurn before after →
      after.totalSupply = before.totalSupply ∧
      after.lockedLiquidity = before.lockedLiquidity


/-- Reader-facing reachable form: from any reachable pool state, every finite
successful no-burn history preserves or increases LP supply. This pairs with
the no-burn K theorem below: without LP redemption, neither supply nor cached K
can move in the extraction direction. -/
def pair_closed_world_reachable_no_burn_path_never_decreases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoBurn before after →
      before.totalSupply ≤ after.totalSupply


/-- Reader-facing reachable form: from any reachable pool state, every finite
successful no-mint history preserves or decreases LP supply. Together with the
no-burn theorem, this pins LP supply movement to the two liquidity entrypoints:
mint creates shares and burn redeems them. -/
def pair_closed_world_reachable_no_mint_path_never_increases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoMint before after →
      after.totalSupply ≤ before.totalSupply

/-- LP issuance requires mint. This is the same supply invariant stated in the
direction an auditor usually wants: if an endpoint has more LP supply than the
reachable starting state, then no successful history without a mint can produce
that endpoint. -/
def pair_closed_world_reachable_supply_increase_requires_mint
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    before.totalSupply < after.totalSupply →
      ¬ PairWorldPathNoMint before after

/-- LP redemption requires burn. If an endpoint has less LP supply than the
reachable starting state, then no successful history without a burn can produce
that endpoint. -/
def pair_closed_world_reachable_supply_decrease_requires_burn
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    after.totalSupply < before.totalSupply →
      ¬ PairWorldPathNoBurn before after

/-- Any LP-supply change requires a liquidity operation. Histories made only of
approvals, LP transfers, donations, swaps, skim, and sync preserve total supply,
so an endpoint with different LP supply cannot be reached by a history that has
neither mint nor burn. -/
def pair_closed_world_reachable_supply_change_requires_mint_or_burn
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    after.totalSupply ≠ before.totalSupply →
      ¬ PairWorldPathNoMintBurn before after

def pair_closed_world_approve_preserves_pool
    (ownerAddr spender : Address) (amount : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.approve ownerAddr spender amount) before after →
    after = before

def pair_closed_world_transfer_preserves_pool
    (fromAddr toAddr : Address) (amount : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.transfer fromAddr toAddr amount) before after →
    after = before

def pair_closed_world_transferFrom_preserves_pool
    (spender fromAddr toAddr : Address) (amount : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.transferFrom spender fromAddr toAddr amount) before after →
    after = before


def pair_closed_world_first_mint_locks_minimum_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    before.totalSupply = 0 →
      after.lockedLiquidity = minimumLiquidityNat ∧
      after.totalSupply = minimumLiquidityNat + liquidity

/-- First-mint locking is also an ownership-security fact. A valid first mint
creates positive user liquidity, but total supply is strictly larger than that
user liquidity because `MINIMUM_LIQUIDITY` is already locked. The first LP can
therefore never own the entire pool supply in the closed-world model. -/
def pair_closed_world_first_mint_keeps_locked_share
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    before.totalSupply = 0 →
      after.lockedLiquidity < after.totalSupply ∧
      liquidity < after.totalSupply

def pair_closed_world_subsequent_mint_preserves_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    before.totalSupply ≠ 0 →
      after.lockedLiquidity = before.lockedLiquidity ∧
      after.totalSupply = before.totalSupply + liquidity

/-- Every valid mint creates positive user liquidity, and the first mint also
locks `MINIMUM_LIQUIDITY`; either way total LP supply strictly increases. -/
def pair_closed_world_mint_strictly_increases_supply
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    before.totalSupply < after.totalSupply

/--
Mint reserve accounting is exact in the closed-world model.

A valid mint observes token balances that exceed cached reserves by
`amount0` and `amount1`, then caches those balances. Equivalently, the new
cached reserves are the old cached reserves plus exactly the deposited amounts.
-/
def pair_closed_world_mint_adds_exact_deposits_to_reserves
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    after.reserve0 = before.reserve0 + amount0 ∧
    after.reserve1 = before.reserve1 + amount1

def pair_closed_world_burn_reduces_supply_by_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    after.totalSupply = before.totalSupply - liquidity

/--
Burn token accounting is exact in the closed-world model.

A valid burn pays `amount0` and `amount1` out of the pair's token balances, then
caches the remaining balances as reserves. No additional token amount can
disappear from the pool through the modeled burn step.
-/
def pair_closed_world_burn_removes_exact_redemptions_from_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    after.balance0 + amount0 = before.balance0 ∧
    after.balance1 + amount1 = before.balance1 ∧
    after.reserve0 = after.balance0 ∧
    after.reserve1 = after.balance1

/-- Burning destroys LP liquidity. The exact reduction is specified separately;
this consequence says no burn can increase total LP supply. -/
def pair_closed_world_burn_never_increases_supply
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    after.totalSupply ≤ before.totalSupply

def pair_closed_world_burn_cannot_redeem_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    before.lockedLiquidity ≤ after.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

/-- The minimum-liquidity lock is not just an LP-supply accounting fact. From a
good state with positive token balances, a valid burn cannot redeem every unit
of either token; some token backing must remain with the locked liquidity. -/
def pair_closed_world_burn_preserves_positive_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
      0 < before.balance0 →
        0 < before.balance1 →
          0 < after.balance0 ∧
          0 < after.balance1

/-- Reachable burn positive-balance theorem. In the form a maintainer should cite, a
valid burn from any reachable nonempty pool cannot empty either token side. The
reachable invariant supplies the pre-burn positive balances; the burn theorem
uses the locked minimum liquidity to show some token backing must remain. -/
def pair_closed_world_reachable_positive_supply_burn_preserves_positive_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
        0 < after.balance0 ∧
        0 < after.balance1

/-!
### 7. Token Inflow Without Accounting (Donations)

A direct token transfer into the pair must not silently change cached
reserves, LP supply, or cached K. Surplus = balance − reserve on each side;
donations may create surplus, no-donation histories cannot. `skim` may
remove an external gift, but the pair cannot create one internally.
-/

def pair_closed_world_donate_preserves_reserves_and_supply
    (amount0 amount1 : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.donate amount0 amount1) before after →
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1 ∧
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

def pair_closed_world_donate_preserves_k
    (amount0 amount1 : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.donate amount0 amount1) before after →
    PairWorldK after = PairWorldK before

/-- Donations are exactly the source of new unaccounted reserve surplus. From a
reserve-backed state, a direct token0/token1 inflow increases each token-side
surplus by exactly the donated amount while cached reserves remain unchanged. -/
def pair_closed_world_donation_increases_surplus_exactly
    (amount0 amount1 : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep (PairWorldAction.donate amount0 amount1) before after →
      PairWorldSurplus0 after = PairWorldSurplus0 before + amount0 ∧
      PairWorldSurplus1 after = PairWorldSurplus1 before + amount1


/-- Reader-facing reachable form of surplus isolation. Starting from an
actually reachable PairWorld state, any finite successful no-donation history
cannot create new unaccounted reserve surplus. Any later `skim` profit must
come from surplus that was already present, not from the pair's own mechanics. -/
def pair_closed_world_reachable_no_donation_path_never_increases_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoDonation before after →
      PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
      PairWorldSurplus1 after ≤ PairWorldSurplus1 before

/-- New skimmable surplus requires donation. If either token side ends with
more `balance - reserve` surplus than it started with, then a no-donation
history cannot explain that endpoint. This is the trace-level firewall behind
the no-profit theorems that allow `skim` to remove only pre-existing gifts. -/
def pair_closed_world_reachable_surplus_increase_requires_donation
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    (PairWorldSurplus0 before < PairWorldSurplus0 after ∨
      PairWorldSurplus1 before < PairWorldSurplus1 after) →
      ¬ PairWorldPathNoDonation before after

/-- Spot-valued form of the same surplus isolation. The previous theorem is
token-side; this one states the economic consequence at the starting pool's
spot price. Along a no-donation history, the token1-denominated value of
skimmable surplus cannot increase. Any later caller profit from `skim` must be
paid for by surplus that already existed at the start. -/
def pair_closed_world_reachable_no_donation_path_surplus_value_never_increases
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoDonation before after →
      PairWorldSurplusSpotValueNum before after ≤
        PairWorldSurplusSpotValueNum before before

/-- Clean-start surplus preservation. If a reachable pool starts with no
unaccounted reserve surplus, then a finite history with no direct donation step
still has no unaccounted reserve surplus at the end. This is the trace-wide
invariant behind the informal claim that `skim` cannot find internally-created
profit; without an external token transfer into the pair, there is no skimmable
gift to remove. -/
def pair_closed_world_reachable_zero_surplus_no_donation_path_preserves_zero_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathNoDonation before after →
          PairWorldSurplus0 after = 0 ∧
          PairWorldSurplus1 after = 0

/-- Clean-start endpoint balance. The previous theorem says no-donation
histories preserve zero `balance - reserve` surplus. Combined with the
reachable-state reserve-backing invariant, that means the endpoint is balanced
in the direct accounting sense: modeled ERC20 token balances equal cached
reserves on both sides. -/
def pair_closed_world_reachable_zero_surplus_no_donation_path_ends_balanced
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathNoDonation before after →
          after.balance0 = after.reserve0 ∧
          after.balance1 = after.reserve1

/-!
### 8. Surplus And Reserve Synchronization (Model)

`skim` removes only surplus above cached reserves. `sync` accepts the
currently observed token balances as reserves, subject to uint112 bounds.
Neither action mints or burns LP supply; neither decreases K from a
reserve-backed state.
-/

def pair_closed_world_skim_removes_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.skim before after →
    after.balance0 = before.reserve0 ∧
    after.balance1 = before.reserve1 ∧
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1

/-- After `skim`, there is no remaining modeled surplus above cached reserves.
The action is allowed to remove an external gift, but it cannot leave behind a
new skimmable balance created by the pair's own accounting. -/
def pair_closed_world_skim_eliminates_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.skim before after →
    PairWorldSurplus0 after = 0 ∧
    PairWorldSurplus1 after = 0

/-- At the initial spot price, `skim` removes exactly the token-balance value
that was already surplus above cached reserves. This separates legitimate
surplus cleanup from extraction of accounted reserve value. -/
def pair_closed_world_skim_removes_exact_surplus_value
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.skim before after →
      PairWorldBalanceSpotValueNum before before =
        PairWorldBalanceSpotValueNum before after +
        PairWorldSurplusSpotValueNum before before

/-- Since `skim` removes exactly pre-existing surplus, it cannot increase the
pair's actual token-balance value at the starting spot price. -/
def pair_closed_world_skim_token_balance_value_never_increases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.skim before after →
      PairWorldBalanceSpotValueNum before after ≤
        PairWorldBalanceSpotValueNum before before

/-- The same skim value bound holds for any external valuation spot. Skim moves
balances down to cached reserves, so in every nonnegative reserve-denominated
valuation it can only leave actual token-balance value unchanged or lower. -/
def pair_closed_world_skim_token_balance_value_never_increases_at_spot
    (spot before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.skim before after →
      PairWorldBalanceSpotValueNum spot after ≤
        PairWorldBalanceSpotValueNum spot before

/-- If the pool is already balanced, `skim` is a no-op on token balances as
well as cached accounting. This is the direct statement that skim cannot remove
accounted liquidity from a reserve-backed pool with no external surplus. -/
def pair_closed_world_skim_preserves_balanced_pool
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.skim before after →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity

def pair_closed_world_skim_preserves_good
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.skim before after →
      PairWorldGood after

def pair_closed_world_skim_preserves_liquidity_supply
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.skim before after →
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

def pair_closed_world_skim_preserves_k
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.skim before after →
    PairWorldK after = PairWorldK before

def pair_closed_world_sync_sets_reserves_to_balances
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.sync before after →
    after.reserve0 = before.balance0 ∧
    after.reserve1 = before.balance1 ∧
    after.balance0 = before.balance0 ∧
    after.balance1 = before.balance1

/-- `sync` is an accounting update, not a token transfer. It may move the
cached reserves up to the balances already sitting in the pair, but it cannot
create, remove, or send either underlying token. -/
def pair_closed_world_sync_preserves_token_balances
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.sync before after →
    after.balance0 = before.balance0 ∧
    after.balance1 = before.balance1

/-- Because `sync` does not move tokens, any spot-price valuation of the pair's
actual token balances is unchanged by sync. This keeps reserve accounting from
masquerading as economic extraction or profit. -/
def pair_closed_world_sync_preserves_token_balance_value
    (spot before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.sync before after →
    PairWorldBalanceSpotValueNum spot after =
      PairWorldBalanceSpotValueNum spot before

/-- Any action that rewrites the router-visible reserves writes them to the
actual token balances at the end of that action. This is the shared accounting
rule behind mint, burn, swap, and sync: cached reserves may change only by
catching up to the balances the pair actually holds. -/
def pair_closed_world_reserve_write_sets_reserves_to_balances
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  ((∃ amount0 amount1 liquidity,
      action = PairWorldAction.mint amount0 amount1 liquidity) ∨
    (∃ amount0 amount1 liquidity,
      action = PairWorldAction.burn amount0 amount1 liquidity) ∨
    (∃ amount0In amount1In amount0Out amount1Out,
      action = PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
    action = PairWorldAction.sync) →
    PairWorldStep action before after →
      after.reserve0 = after.balance0 ∧
      after.reserve1 = after.balance1

/-- Passive reconciliation cannot manufacture token-balance value. Skim may
remove donated surplus, while sync only changes cached reserves; neither action
can increase the pair's actual token-balance value at the starting spot price.
-/
def pair_closed_world_skim_or_sync_token_balance_value_never_increases
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  (action = PairWorldAction.skim ∨ action = PairWorldAction.sync) →
    PairWorldGood before →
      PairWorldStep action before after →
        PairWorldBalanceSpotValueNum before after ≤
          PairWorldBalanceSpotValueNum before before

/-- The one-step `skim`/`sync` value bound is independent of which spot price is
used to measure token balances. This lets finite-history proofs keep valuing
every later step at the original starting price. -/
def pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
    (spot : PairWorldState) (action : PairWorldAction)
    (before after : PairWorldState) : Prop :=
  (action = PairWorldAction.skim ∨ action = PairWorldAction.sync) →
    PairWorldGood before →
      PairWorldStep action before after →
        PairWorldBalanceSpotValueNum spot after ≤
          PairWorldBalanceSpotValueNum spot before

/-- After `sync`, cached reserves equal modeled token balances, so the pair has
no remaining unaccounted surplus in the closed-world state. This is why sync is
reserve reconciliation, not value creation. -/
def pair_closed_world_sync_eliminates_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.sync before after →
    PairWorldSurplus0 after = 0 ∧
    PairWorldSurplus1 after = 0

def pair_closed_world_sync_preserves_good
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.sync before after →
      PairWorldGood after

def pair_closed_world_sync_preserves_liquidity_supply
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.sync before after →
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

def pair_closed_world_sync_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.sync before after →
      PairWorldK before ≤ PairWorldK after

/-- If there is no surplus above cached reserves, `sync` is a no-op for cached
K. The only way sync can increase K is by accounting for token balances that
were already sitting in the pair above reserves. -/
def pair_closed_world_sync_preserves_k_without_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.sync before after →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          PairWorldK after = PairWorldK before

/-- If the pool is already balanced, `sync` is a no-op on both token balances
and cached accounting. This is the clean reserve-reconciliation case: with no
external surplus to account, sync cannot change reserves, LP supply, or the
permanent liquidity lock. -/
def pair_closed_world_sync_preserves_balanced_pool
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.sync before after →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity

/-- If there is no excess token balance to clean up, `skim` and `sync` cannot
change the pool. From a good state where token balances already equal cached
reserves, either action preserves token balances, cached reserves, LP supply,
and the permanent liquidity lock exactly. -/
def pair_closed_world_balanced_skim_or_sync_preserves_pool
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  (action = PairWorldAction.skim ∨ action = PairWorldAction.sync) →
    PairWorldGood before →
      PairWorldStep action before after →
        PairWorldSurplus0 before = 0 →
          PairWorldSurplus1 before = 0 →
            after.balance0 = before.balance0 ∧
            after.balance1 = before.balance1 ∧
            after.reserve0 = before.reserve0 ∧
            after.reserve1 = before.reserve1 ∧
            after.totalSupply = before.totalSupply ∧
            after.lockedLiquidity = before.lockedLiquidity



/-- Reader-facing version of the same finite-history value bound. Reachability
supplies the good-state invariant, so the theorem reads directly: any reachable
pool that only sees LP bookkeeping plus `skim`/`sync` cannot end with more
actual token-balance value at the starting spot price. -/
def pair_closed_world_reachable_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathLpBookkeepingSkimSync before after →
      PairWorldBalanceSpotValueNum before after ≤
        PairWorldBalanceSpotValueNum before before

/-- `sync` cannot manufacture cached liquidity value. In a good state, if
syncing balances into reserves increases cached K, then at least one token
balance was already above the cached reserve before the call. -/
def pair_closed_world_sync_k_increase_requires_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep PairWorldAction.sync before after →
      PairWorldK before < PairWorldK after →
        0 < PairWorldSurplus0 before ∨
        0 < PairWorldSurplus1 before
/-!
### 9. Concrete-State Projections

The closed-world invariant is expressed over a small mathematical model. These
specs say what the invariant means when projected back to a Verity
`ContractState`: cached reserves are covered by observed ERC20 balances and fit
inside the canonical uint112 reserve domain.
-/

def pair_concrete_state_reserves_backed
    (s : ContractState) : Prop :=
  PairWorldGood (pairWorldFromConcreteState s) →
    (s.storage reserve0Slot.slot).val ≤ (observedBalance0 s).val ∧
    (s.storage reserve1Slot.slot).val ≤ (observedBalance1 s).val

def pair_concrete_state_uint112_reserves
    (s : ContractState) : Prop :=
  PairWorldGood (pairWorldFromConcreteState s) →
    (s.storage reserve0Slot.slot).val ≤ maxUint112Nat ∧
    (s.storage reserve1Slot.slot).val ≤ maxUint112Nat

def pair_closed_world_reachable_reserves_backed
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    w.reserve0 ≤ w.balance0 ∧
    w.reserve1 ≤ w.balance1

def pair_closed_world_path_reserves_backed
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      after.reserve0 ≤ after.balance0 ∧
      after.reserve1 ≤ after.balance1

/-- The reserve-backing invariant in its most useful reader-facing form:
from any reachable pool state, after any finite sequence of successful modeled
calls, the cached reserves are still covered by the pair's token balances. -/
def pair_closed_world_reachable_path_reserves_backed
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      after.reserve0 ≤ after.balance0 ∧
      after.reserve1 ≤ after.balance1

/-- The reserve-domain invariant in the same finite-history form: a reachable
pool can never reach a successful modeled state whose cached reserves exceed
Uniswap V2's `uint112` reserve domain. -/
def pair_closed_world_reachable_path_reserves_fit_uint112
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      after.reserve0 ≤ maxUint112Nat ∧
      after.reserve1 ≤ maxUint112Nat

def pair_closed_world_reachable_reserves_fit_uint112
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    w.reserve0 ≤ maxUint112Nat ∧
    w.reserve1 ≤ maxUint112Nat

/-!
### 10. Reachability Invariants

The first layer is deliberately boring: define the states that can exist and
show that the definition is stable under both one step and arbitrary finite
paths. This is the base of the argument. Every later economic theorem is only
useful if it applies to all successful histories, not just to hand-picked
examples.
-/


def pair_closed_world_path_preserves_good
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      PairWorldGood after

def pair_closed_world_reachable_good
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    PairWorldGood w

/--
The core invariant over all finite modeled histories.

`PairWorldGood` is the compact name for the safety facts that must never be
lost: cached reserves are backed by actual token balances, cached reserves fit
the `uint112` domain, and LP supply obeys the permanent minimum-liquidity lock.
This theorem says those facts hold after any finite successful modeled history
starting from any reachable Pair state.
-/
def pair_closed_world_reachable_path_good
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      PairWorldGood after

/-- Reachability is stable under finite successful histories. This is the
trace-level closure fact that lets the rest of the section talk about "any
later reachable state" rather than only states built directly from the initial
pool. -/
def pair_closed_world_path_preserves_reachability
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      PairWorldReachable after

def pair_closed_world_reachable_supply_good
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    PairWorldSupplyGood w

def pair_closed_world_path_supply_good
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      PairWorldSupplyGood after

def pair_closed_world_path_reserves_fit_uint112
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      after.reserve0 ≤ maxUint112Nat ∧
      after.reserve1 ≤ maxUint112Nat

def pair_closed_world_path_locked_liquidity_never_exceeds_supply
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      after.lockedLiquidity ≤ after.totalSupply

/-- Once a good pool has positive LP supply, the permanent liquidity lock keeps
every finite successful path from returning total supply to zero. -/
def pair_closed_world_positive_supply_path_remains_positive
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        0 < after.totalSupply

/-- Reachability packages the good-state precondition above. In the form users
care about, any nonempty reachable pool remains nonempty after any finite
successful modeled history. -/
def pair_closed_world_reachable_positive_supply_path_remains_positive
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        0 < after.totalSupply

/-- A reachable pool with LP supply is not allowed to be a degenerate
one-sided or zero-reserve pool. In Uniswap V2 the first mint deposits both
tokens, later burns cannot redeem the permanently locked floor, and swaps keep
outputs below reserves; this invariant packages that story as the precondition
needed for a meaningful spot price. -/
def pair_closed_world_reachable_positive_supply_has_positive_reserves
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    0 < w.totalSupply →
      0 < w.reserve0 ∧
      0 < w.reserve1

/-- The finite-history version of the same nondegeneracy invariant. Starting
from any reachable nonempty pool, every finite sequence of successful modeled
actions leaves both reserves positive, so later economic theorems can rely on a
defined initial and final two-token pool rather than carrying that fact as an
unexplained side condition. -/
def pair_closed_world_reachable_positive_supply_path_has_positive_reserves
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        0 < after.reserve0 ∧
        0 < after.reserve1

/-- Token-side positive-balance invariant. The positive-reserve theorem says cached
reserves stay nonzero; reserve backing then says the actual ERC20 balances held
by the pair are also nonzero. Thus no finite successful modeled history from a
reachable nonempty pool can leave either token balance at zero. -/
def pair_closed_world_reachable_positive_supply_path_has_positive_token_balances
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        0 < after.balance0 ∧
        0 < after.balance1

/-!
## Oracle/TWAP

Cumulative prices are an accounting consequence of a reserve update. If
the 32-bit timestamp has not advanced, the cumulatives are unchanged. If
time has advanced and both old reserves are nonzero, each cumulative gains
the canonical UQ112x112 encoded price times elapsed time. If the timestamp
branch is entered but elapsed time or either old reserve is zero, the
cumulatives stay unchanged.
-/

/-- Reserve updates in the same 32-bit timestamp window do not move the TWAP
accumulators. This is a contract-level oracle rule shared by mint, burn, swap,
and sync; the new reserves may change, but no time has elapsed at the old
price. -/
def pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives
    (s : ContractState) : Prop :=
  timestamp32 s = s.storage blockTimestampLastSlot.slot →
    oraclePrice0CumulativeAfterSync s =
      s.storage price0CumulativeLastSlot.slot ∧
    oraclePrice1CumulativeAfterSync s =
      s.storage price1CumulativeLastSlot.slot

/-- When a reserve update crosses into a later 32-bit timestamp and both old
reserves are nonzero, the pair adds exactly the canonical UQ112x112 encoded
`reserve1 / reserve0` and `reserve0 / reserve1` prices multiplied by elapsed
time. -/
def pair_reserve_update_oracle_elapsed_updates_price_cumulatives
    (s : ContractState) : Prop :=
  (timestamp32 s != s.storage blockTimestampLastSlot.slot) = true →
    oracleElapsed s > 0 →
      s.storage reserve0Slot.slot > 0 →
        s.storage reserve1Slot.slot > 0 →
          oraclePrice0CumulativeAfterSync s =
            oraclePrice0CumulativeAfterElapsed s ∧
          oraclePrice1CumulativeAfterSync s =
            oraclePrice1CumulativeAfterElapsed s

/-- A timestamp change alone is not enough to update TWAP accumulators. If the
elapsed-price branch is inactive because elapsed time or either old reserve is
zero, both cumulative prices remain unchanged. -/
def pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives
    (s : ContractState) : Prop :=
  (timestamp32 s != s.storage blockTimestampLastSlot.slot) = true →
    ¬ (oracleElapsed s > 0 ∧
        s.storage reserve0Slot.slot > 0 ∧
        s.storage reserve1Slot.slot > 0) →
      oraclePrice0CumulativeAfterSync s =
        s.storage price0CumulativeLastSlot.slot ∧
      oraclePrice1CumulativeAfterSync s =
        s.storage price1CumulativeLastSlot.slot







/-!
## Mint, Burn, And Swap — Public Calls

When a real mint/burn/swap call succeeds and the relevant arithmetic
facts hold, the corresponding closed-world transition rule is available.
-/


/-- When the first `mint` succeeds, the lock gate was open and both observed
token balances fit the `uint112` reserve domain; the remaining premises identify
the call as the initial-liquidity path. -/
def pair_mint_first_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    PairWorldStep
                      (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                      (pairWorldBeforeMintRun s)
                      (pairWorldAfterFirstMintRun s)

/--
A successful first mint treats each token's balance increase as the deposit.

The pair does not receive deposit amounts as function arguments. It looks at
its ERC20 balances and subtracts cached reserves. This spec states that fact in
one place.
-/
def pair_first_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success (mintFirstLiquidity s) result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 = observedBalance0 s - s.storage reserve0Slot.slot ∧
              amount1 = observedBalance1 s - s.storage reserve1Slot.slot

/-- Successful initial `mint` preserves the core pair invariant: from a good
projected pre-state, the minted state still has backed reserves, uint112 reserve
bounds, and the minimum-liquidity lock shape. -/
def pair_mint_first_success_run_preserves_good_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let before := pairWorldBeforeMintRun s
  let after := pairWorldAfterFirstMintRun s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  PairWorldGood before →
    result = (mint toAddr).run s →
      result = ContractResult.success liquidity result.snd →
        s.storage totalSupplySlot.slot = 0 →
          s.storage reserve0Slot.slot ≤ observedBalance0 s →
            s.storage reserve1Slot.slot ≤ observedBalance1 s →
              amount0 > 0 →
                amount1 > 0 →
                  (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                    mintFirstRoot s > minimumLiquidity →
                      PairWorldGood after

/--
Initial-mint base case. In the initial-liquidity path, the concrete
empty-pool premises already imply the projected pre-state is good: cached
reserves are backed by observed balances, reserves fit the reserve domain, and
LP supply has not yet been created. Therefore a successful first `mint`
establishes the core pair invariant without asking the reader to assume it.
-/
def pair_mint_first_success_run_establishes_good_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let after := pairWorldAfterFirstMintRun s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    PairWorldGood after

/-- When the initial `mint` succeeds, LP total supply strictly increases. -/
def pair_mint_first_success_run_strictly_increases_supply_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let before := pairWorldBeforeMintRun s
  let after := pairWorldAfterFirstMintRun s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    before.totalSupply < after.totalSupply

/--
The initial successful `mint` does not give
the whole LP supply to the depositor: `MINIMUM_LIQUIDITY` is permanently locked,
and total supply is exactly the locked floor plus the returned user liquidity.
-/
def pair_mint_first_success_run_locks_minimum_liquidity_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let after := pairWorldAfterFirstMintRun s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    after.lockedLiquidity = minimumLiquidityNat ∧
                      after.totalSupply = minimumLiquidityNat + liquidity.val

/--
Because the first mint locks
`MINIMUM_LIQUIDITY`, the first liquidity provider's returned LP amount is
strictly smaller than total LP supply whenever the public first-mint path
succeeds.
-/
def pair_mint_first_success_run_keeps_locked_share_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let after := pairWorldAfterFirstMintRun s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    after.lockedLiquidity = minimumLiquidityNat ∧
                      after.lockedLiquidity < after.totalSupply ∧
                      liquidity.val < after.totalSupply

/--
When the first `mint` succeeds, total LP supply equals the square-root
liquidity measure and the caller receives exactly that amount minus
`MINIMUM_LIQUIDITY`.

This is the first-deposit fairness rule: the permanent lock is created once,
and the first LP cannot own the entire supply.
-/
def pair_first_mint_success_uses_canonical_liquidity_formula
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let after := pairWorldAfterFirstMintRun s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    liquidity.val + minimumLiquidityNat = (mintFirstRoot s).val ∧
                      after.totalSupply = (mintFirstRoot s).val ∧
                      after.totalSupply = minimumLiquidityNat + liquidity.val

/--
Initial liquidity deposits add token balances and
cache those balances as reserves; once the successful public run is connected
to that first-mint transition, raw cached K cannot decrease.
-/
def pair_mint_first_success_run_never_decreases_k_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let before := pairWorldBeforeMintRun s
  let after := pairWorldAfterFirstMintRun s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    PairWorldK before ≤ PairWorldK after

/--
In the initial-liquidity path, a
successful public `mint` caches exactly the observed token balances as the
router-visible reserves.
-/
def pair_mint_first_success_run_updates_reserves_to_balances_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let after := pairWorldAfterFirstMintRun s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 > 0 →
              amount1 > 0 →
                (amount0 == 0 || div (mintFirstProduct s) amount0 == amount1) = true →
                  mintFirstRoot s > minimumLiquidity →
                    after.reserve0 = after.balance0 ∧
                      after.reserve1 = after.balance1

/-!
### Subsequent mint, burn, and swap

The remaining mint, burn, and swap facts keep the same shape. Each says that a
successful public call, together with the arithmetic facts computed along that
path, matches the appropriate model action. The economic content remains in the
short invariants below, where those actions are composed over paths.
-/



/-- For later liquidity additions, a successful `mint` already establishes the
shared mint gates; the remaining premises say that supply/reserves are live and
that the returned LP amount is the canonical minimum of the two pro-rata sides.
-/
def pair_mint_subsequent_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot > 0 →
          s.storage reserve1Slot.slot > 0 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          PairWorldStep
                            (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                            (pairWorldBeforeMintRun s)
                            (pairWorldAfterSubsequentMintRun liquidity s)

/--
A successful later mint also treats each token's balance increase as the
deposit.
-/
def pair_later_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 = observedBalance0 s - s.storage reserve0Slot.slot ∧
              amount1 = observedBalance1 s - s.storage reserve1Slot.slot

/-- A successful later `mint` satisfying the canonical pro-rata facts preserves
the core pair invariant from any good projected pre-state. -/
def pair_mint_subsequent_success_run_preserves_good_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let before := pairWorldBeforeMintRun s
  let after := pairWorldAfterSubsequentMintRun liquidity s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  PairWorldGood before →
    result = (mint toAddr).run s →
      result = ContractResult.success liquidity result.snd →
        0 < (s.storage totalSupplySlot.slot).val →
          s.storage reserve0Slot.slot > 0 →
            s.storage reserve1Slot.slot > 0 →
              s.storage reserve0Slot.slot ≤ observedBalance0 s →
                s.storage reserve1Slot.slot ≤ observedBalance1 s →
                  amount0 > 0 →
                    amount1 > 0 →
                      liquidity > 0 →
                        liquidity.val * (s.storage reserve0Slot.slot).val ≤
                            amount0.val * (s.storage totalSupplySlot.slot).val →
                          liquidity.val * (s.storage reserve1Slot.slot).val ≤
                              amount1.val * (s.storage totalSupplySlot.slot).val →
                            PairWorldGood after

/--
In a nonempty pool, a successful public
`mint` that is connected to its pro-rata arithmetic facts strictly increases LP
total supply.
-/
def pair_mint_subsequent_success_run_strictly_increases_supply_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let before := pairWorldBeforeMintRun s
  let after := pairWorldAfterSubsequentMintRun liquidity s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot > 0 →
          s.storage reserve1Slot.slot > 0 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          before.totalSupply < after.totalSupply

/--
After the first mint has created the permanent
`MINIMUM_LIQUIDITY` floor, later successful mints may add user LP supply but
must preserve the locked-liquidity amount exactly.
-/
def pair_mint_subsequent_success_run_preserves_locked_liquidity_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let before := pairWorldBeforeMintRun s
  let after := pairWorldAfterSubsequentMintRun liquidity s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot > 0 →
          s.storage reserve1Slot.slot > 0 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          after.lockedLiquidity = before.lockedLiquidity ∧
                            after.totalSupply = before.totalSupply + liquidity.val

/--
Later-mint K fact. Later liquidity deposits add balances on both
token sides before reserves are updated, so connecting a successful public
`mint` to its pro-rata transition proves raw cached K cannot decrease.
-/
def pair_mint_subsequent_success_run_never_decreases_k_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let before := pairWorldBeforeMintRun s
  let after := pairWorldAfterSubsequentMintRun liquidity s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot > 0 →
          s.storage reserve1Slot.slot > 0 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          PairWorldK before ≤ PairWorldK after

/--
Later-mint reserve-write fact. In a live pool, a successful public
`mint` updates cached reserves to the observed token balances after the
liquidity addition.
-/
def pair_mint_subsequent_success_run_updates_reserves_to_balances_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let after := pairWorldAfterSubsequentMintRun liquidity s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot > 0 →
          s.storage reserve1Slot.slot > 0 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          after.reserve0 = after.balance0 ∧
                            after.reserve1 = after.balance1

/--
Successful later mints cannot dilute existing LPs. Once a real `mint` succeeds
in the nonempty-pool case and its pro-rata arithmetic facts are available, the
closed-world mint invariant proves that reserve product per squared LP supply
does not decrease.
-/
def pair_mint_subsequent_success_run_preserves_existing_lp_share
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let before := pairWorldBeforeMintRun s
  let after := pairWorldAfterSubsequentMintRun liquidity s
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      PairWorldGood before →
        0 < before.totalSupply →
          0 < (s.storage totalSupplySlot.slot).val →
            s.storage reserve0Slot.slot > 0 →
              s.storage reserve1Slot.slot > 0 →
                s.storage reserve0Slot.slot ≤ observedBalance0 s →
                  s.storage reserve1Slot.slot ≤ observedBalance1 s →
                    amount0 > 0 →
                      amount1 > 0 →
                        liquidity > 0 →
                          liquidity.val * (s.storage reserve0Slot.slot).val ≤
                              amount0.val * (s.storage totalSupplySlot.slot).val →
                            liquidity.val * (s.storage reserve1Slot.slot).val ≤
                                amount1.val * (s.storage totalSupplySlot.slot).val →
                              PairWorldKPerSupplyNondecreasing before after


def pair_burn_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          liquidity.val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
              amount0 > 0 →
                amount1 > 0 →
                  amount0 ≤ observedBalance0 s →
                    amount1 ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          amount0.val * (burnSupply s).val ≤
                              liquidity.val * (observedBalance0 s).val →
                            amount1.val * (burnSupply s).val ≤
                                liquidity.val * (observedBalance1 s).val →
                              PairWorldStep
                                (PairWorldAction.burn amount0.val amount1.val liquidity.val)
                                (pairWorldFromConcreteState s)
                                (pairWorldAfterBurnRun s)

/--
A successful burn destroys the LP tokens sitting on the pair itself and uses
current total supply as the denominator for redemption.
-/
def pair_burn_uses_pair_lp_balance_and_total_supply
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      burnLiquidity s = s.storageMap balancesSlot.slot (pairSelf s) ∧
        burnSupply s = s.storage totalSupplySlot.slot

/--
A successful burn leaves the pair with its previous token balances minus the
tokens paid to the recipient.
-/
def pair_burn_leaves_remaining_token_balances
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      burnAmount0 s ≤ observedBalance0 s →
        burnAmount1 s ≤ observedBalance1 s →
          (pairWorldAfterBurnRun s).balance0 + (burnAmount0 s).val =
            (observedBalance0 s).val ∧
            (pairWorldAfterBurnRun s).balance1 + (burnAmount1 s).val =
              (observedBalance1 s).val

/-- A successful burn satisfying the redemption arithmetic facts preserves the
core pair invariant: from a good projected pre-state, the post-burn model still
has backed reserves, uint112 reserve bounds, and coherent locked LP supply. -/
def pair_burn_success_run_preserves_good_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterBurnRun s
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  PairWorldGood before →
    result = (burn toAddr).run s →
      result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
        0 < liquidity.val →
          0 < (burnSupply s).val →
            liquidity.val ≤ (burnSupply s).val →
              minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
                amount0 > 0 →
                  amount1 > 0 →
                    amount0 ≤ observedBalance0 s →
                      amount1 ≤ observedBalance1 s →
                        burnBalance0After s ≤ maxUint112 →
                          burnBalance1After s ≤ maxUint112 →
                            amount0.val * (burnSupply s).val ≤
                                liquidity.val * (observedBalance0 s).val →
                              amount1.val * (burnSupply s).val ≤
                                  liquidity.val * (observedBalance1 s).val →
                                PairWorldGood after

/-- A successful public `burn` satisfying the redemption arithmetic facts
destroys exactly the LP liquidity held by the pair. -/
def pair_burn_success_run_reduces_supply_by_liquidity_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterBurnRun s
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          liquidity.val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
              amount0 > 0 →
                amount1 > 0 →
                  amount0 ≤ observedBalance0 s →
                    amount1 ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          amount0.val * (burnSupply s).val ≤
                              liquidity.val * (observedBalance0 s).val →
                            amount1.val * (burnSupply s).val ≤
                                liquidity.val * (observedBalance1 s).val →
                              after.totalSupply =
                                before.totalSupply - liquidity.val

/--
When `burn` succeeds, the paid token amounts are exactly the burned LP share
of the pair's token balances before the payout.

This is the LP redemption rule: a burner can receive only their pro-rata
share, and the remaining LPs are not diluted.
-/
def pair_burn_success_pays_exact_pro_rata_amounts
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (amount0, amount1) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          amount0 =
              div (mul liquidity (observedBalance0 s)) (burnSupply s) ∧
            amount1 =
              div (mul liquidity (observedBalance1 s)) (burnSupply s)

/--
A successful public `burn` may redeem ordinary LP
shares, but it cannot redeem below the permanently locked liquidity floor. The
locked amount remains the same before and after the burn, and the post-burn
total supply still covers it.
-/
def pair_burn_success_run_cannot_redeem_locked_liquidity_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterBurnRun s
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          liquidity.val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
              amount0 > 0 →
                amount1 > 0 →
                  amount0 ≤ observedBalance0 s →
                    amount1 ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          amount0.val * (burnSupply s).val ≤
                              liquidity.val * (observedBalance0 s).val →
                            amount1.val * (burnSupply s).val ≤
                                liquidity.val * (observedBalance1 s).val →
                              before.lockedLiquidity ≤ after.totalSupply ∧
                                after.lockedLiquidity = before.lockedLiquidity

/--
From a good pool with positive token
balances, a successful public `burn` cannot drain either token side to zero
once the run is connected to its redemption arithmetic.
-/
def pair_burn_success_run_preserves_positive_balances_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterBurnRun s
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      PairWorldGood before →
        0 < before.balance0 →
          0 < before.balance1 →
            0 < liquidity.val →
              0 < (burnSupply s).val →
                liquidity.val ≤ (burnSupply s).val →
                  minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
                    amount0 > 0 →
                      amount1 > 0 →
                        amount0 ≤ observedBalance0 s →
                          amount1 ≤ observedBalance1 s →
                            burnBalance0After s ≤ maxUint112 →
                              burnBalance1After s ≤ maxUint112 →
                                amount0.val * (burnSupply s).val ≤
                                    liquidity.val * (observedBalance0 s).val →
                                  amount1.val * (burnSupply s).val ≤
                                      liquidity.val * (observedBalance1 s).val →
                                    0 < after.balance0 ∧
                                      0 < after.balance1

/--
After a successful burn transfers redeemed
tokens out, the pair rereads both token balances and caches exactly those
post-transfer balances as reserves.
-/
def pair_burn_success_run_updates_reserves_to_balances_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let after := pairWorldAfterBurnRun s
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          liquidity.val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
              amount0 > 0 →
                amount1 > 0 →
                  amount0 ≤ observedBalance0 s →
                    amount1 ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          amount0.val * (burnSupply s).val ≤
                              liquidity.val * (observedBalance0 s).val →
                            amount1.val * (burnSupply s).val ≤
                                liquidity.val * (observedBalance1 s).val →
                              after.reserve0 = after.balance0 ∧
                                after.reserve1 = after.balance1

/--
When `burn` succeeds, cached reserves become the token balances left after the
redemption transfers.
-/
def pair_burn_success_caches_post_redemption_balances
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let after := pairWorldAfterBurnRun s
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (amount0, amount1) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          amount0 ≤ observedBalance0 s →
            amount1 ≤ observedBalance1 s →
              after.reserve0 = (burnBalance0After s).val ∧
                after.reserve1 = (burnBalance1After s).val

/--
A burn may reduce raw reserves because assets
leave the pair, but it must not over-extract from the LPs that remain. Once the
real public run satisfies its concrete redemption facts, the model proves that
reserve product per squared LP supply does not decrease.
-/
def pair_burn_success_run_preserves_remaining_lp_share
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterBurnRun s
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      PairWorldGood before →
        0 < before.totalSupply →
          0 < liquidity.val →
            0 < (burnSupply s).val →
              liquidity.val ≤ (burnSupply s).val →
                minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
                  amount0 > 0 →
                    amount1 > 0 →
                      amount0 ≤ observedBalance0 s →
                        amount1 ≤ observedBalance1 s →
                          burnBalance0After s ≤ maxUint112 →
                            burnBalance1After s ≤ maxUint112 →
                              amount0.val * (burnSupply s).val ≤
                                  liquidity.val * (observedBalance0 s).val →
                                amount1.val * (burnSupply s).val ≤
                                    liquidity.val * (observedBalance1 s).val →
                                  PairWorldKPerSupplyNondecreasing before after



/--
A successful swap infers token input from the final balances after optimistic
output and any callback repayment.

For each token, input is the positive excess above the balance expected after
output; if the final balance is not above that expected balance, inferred input
for that token is zero.
-/
def pair_swap_uses_final_balances_to_compute_input
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let expected0 := swapExpected0 amount0Out s
  let expected1 := swapExpected1 amount1Out s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0In =
          (if balance0Now > expected0 then
            Verity.EVM.Uint256.sub balance0Now expected0
          else
            0) ∧
        amount1In =
          (if balance1Now > expected1 then
            Verity.EVM.Uint256.sub balance1Now expected1
          else
            0)

/--
When a successful swap's final balance reads satisfy the fee-adjusted K check,
that check is about the same final balances the pair will cache as reserves.
-/
def pair_swap_checks_k_against_final_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      feeAdjustedBalance balance0Now.val amount0In.val *
          feeAdjustedBalance balance1Now.val amount1In.val ≥
        requiredK
          (s.storage reserve0Slot.slot).val
          (s.storage reserve1Slot.slot).val →
        feeAdjustedBalance after.balance0 amount0In.val *
            feeAdjustedBalance after.balance1 amount1In.val ≥
          requiredK before.reserve0 before.reserve1

/-- When `swap` succeeds, the zero-output guard has passed. The remaining
premises are the post-callback balance, input, reserve-bound, and K facts that
describe the state observed after any optimistic transfer and callback
repayment. -/
def pair_swap_success_run_matches_closed_world_step_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                            PairWorldStep
                            (PairWorldAction.swap
                              amount0In.val amount1In.val
                              amount0Out.val amount1Out.val)
                            (pairWorldFromConcreteState s)
                            (pairWorldAfterSwapRun balance0Now balance1Now s)

/-- A successful `swap` satisfying its final-balance and fee-adjusted-K facts
keeps the core invariant package in the resulting modeled state. -/
def pair_swap_success_run_preserves_good_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  PairWorldGood before →
    result = (swap amount0Out amount1Out toAddr data).run s →
      result = ContractResult.success () result.snd →
        amount0Out < s.storage reserve0Slot.slot →
          amount1Out < s.storage reserve1Slot.slot →
            (amount0In > 0 ∨ amount1In > 0) →
              balance0Now.val =
                  (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
                balance1Now.val =
                    (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                  balance0Now ≤ maxUint112 →
                    balance1Now ≤ maxUint112 →
                      amount0In.val * feeAdjustmentNat ≤
                          balance0Now.val * feeDenominatorNat →
                        amount1In.val * feeAdjustmentNat ≤
                            balance1Now.val * feeDenominatorNat →
                          feeAdjustedBalance balance0Now.val amount0In.val *
                              feeAdjustedBalance balance1Now.val amount1In.val ≥
                            requiredK
                              (s.storage reserve0Slot.slot).val
                              (s.storage reserve1Slot.slot).val →
                            PairWorldGood after

/--
A successful public `swap` may
change token balances and cached reserves, but it must not mint, burn, or unlock
any LP supply. Once the concrete final-balance and K facts identify the modeled
swap step, the closed-world supply theorem gives the public conclusion.
-/
def pair_swap_success_run_preserves_liquidity_supply_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                          after.totalSupply = before.totalSupply ∧
                            after.lockedLiquidity = before.lockedLiquidity

/--
The public `swap` reads final balances after optimistic
outputs and any callback repayment, then enforces the fee-adjusted K check. Once
those concrete facts identify the modeled swap step, raw cached reserve product
cannot decrease.
-/
def pair_swap_success_run_never_decreases_k_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                          PairWorldK before ≤ PairWorldK after

/--
The public `swap` may transfer
tokens optimistically and run a callback, but the safety check is about the
final balances after all input or repayment has arrived. Once a successful run
is connected to those final-balance facts, the same balances both account for
input/output and satisfy the fee-adjusted K inequality.
-/
def pair_swap_success_run_k_uses_final_balances_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                          after.balance0 + amount0Out.val =
                              before.reserve0 + amount0In.val ∧
                            after.balance1 + amount1Out.val =
                              before.reserve1 + amount1In.val ∧
                            feeAdjustedBalance after.balance0 amount0In.val *
                            feeAdjustedBalance after.balance1 amount1In.val ≥
                              requiredK before.reserve0 before.reserve1

/--
When `swap` succeeds, the final token balances account for the optimistic
output and any input paid back before the K check.
-/
def pair_swap_success_accounts_for_input_and_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                          after.balance0 + amount0Out.val =
                              before.reserve0 + amount0In.val ∧
                            after.balance1 + amount1Out.val =
                              before.reserve1 + amount1In.val

/--
When `swap` succeeds, the fee-adjusted constant-product check held on the
final balances, after optimistic output and after any callback repayment.
-/
def pair_swap_success_charges_k_against_final_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                          feeAdjustedBalance after.balance0 amount0In.val *
                              feeAdjustedBalance after.balance1 amount1In.val ≥
                            requiredK before.reserve0 before.reserve1

/--
The swap's K check is charged against final
post-output, post-callback balances, and the successful path then caches those
same final balances as reserves.
-/
def pair_swap_success_run_updates_reserves_to_balances_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                          after.reserve0 = after.balance0 ∧
                            after.reserve1 = after.balance1

/--
Successful swaps cannot make the caller richer when value is only redistributed.

Once a successful public `swap` satisfies the concrete balance and K facts, the
reachable one-swap no-profit theorem applies immediately. If caller-plus-pool
spot value is merely redistributed at the starting price, the caller cannot
finish richer.
-/
def pair_swap_success_run_no_caller_spot_profit_with_valid_swap
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      PairWorldReachable before →
        0 < before.totalSupply →
          PairWorldStep
              (PairWorldAction.swap
                amount0In.val amount1In.val amount0Out.val amount1Out.val)
              before
              after →
            callerValueBefore + PairWorldSpotValueNum before before =
              callerValueAfter + PairWorldSpotValueNum before after →
              callerValueAfter ≤ callerValueBefore

/--
Successful-swap no-profit once the swap accounting rule is established.

This is the reader-facing form: if a real `swap` succeeds, the final observed
balances satisfy the input/K facts, the starting pool is reachable and live, and
caller-plus-pool reserve value is merely redistributed at the starting price,
then the caller cannot finish richer. The statement deliberately leaves the
post-callback balance/K facts explicit because those are the concrete facts the
swap reads after optimistic transfer and callback repayment.
-/
def pair_swap_success_run_no_caller_spot_profit_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      PairWorldReachable before →
        0 < before.totalSupply →
          amount0Out < s.storage reserve0Slot.slot →
            amount1Out < s.storage reserve1Slot.slot →
              (amount0In > 0 ∨ amount1In > 0) →
                balance0Now.val =
                    (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
                  balance1Now.val =
                      (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                    balance0Now ≤ maxUint112 →
                      balance1Now ≤ maxUint112 →
                        amount0In.val * feeAdjustmentNat ≤
                            balance0Now.val * feeDenominatorNat →
                          amount1In.val * feeAdjustmentNat ≤
                              balance1Now.val * feeDenominatorNat →
                            feeAdjustedBalance balance0Now.val amount0In.val *
                                feeAdjustedBalance balance1Now.val amount1In.val ≥
                              requiredK
                                (s.storage reserve0Slot.slot).val
                                (s.storage reserve1Slot.slot).val →
                              callerValueBefore + PairWorldSpotValueNum before before =
                                callerValueAfter + PairWorldSpotValueNum before after →
                                callerValueAfter ≤ callerValueBefore

/--
Successful-swap actual-token-balance no-profit.

Reserve value is the core AMM invariant, but a caller sees ERC20 token balances.
When the starting pool has no surplus above cached reserves, the successful
public swap can use the closed-world actual-balance theorem directly:
if the final post-callback balances and fee-adjusted K facts identify the run as
a valid swap, and caller-plus-pair actual token-balance value is merely
redistributed at the starting spot price, then the caller cannot finish richer.
-/
def pair_swap_success_run_no_caller_token_balance_profit_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSwapRun balance0Now balance1Now s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      PairWorldReachable before →
        0 < before.totalSupply →
          PairWorldSurplus0 before = 0 →
            PairWorldSurplus1 before = 0 →
              amount0Out < s.storage reserve0Slot.slot →
                amount1Out < s.storage reserve1Slot.slot →
                  (amount0In > 0 ∨ amount1In > 0) →
                    balance0Now.val =
                        (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
                      balance1Now.val =
                          (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                        balance0Now ≤ maxUint112 →
                          balance1Now ≤ maxUint112 →
                            amount0In.val * feeAdjustmentNat ≤
                                balance0Now.val * feeDenominatorNat →
                              amount1In.val * feeAdjustmentNat ≤
                                  balance1Now.val * feeDenominatorNat →
                                feeAdjustedBalance balance0Now.val amount0In.val *
                                    feeAdjustedBalance balance1Now.val amount1In.val ≥
                                  requiredK
                                    (s.storage reserve0Slot.slot).val
                                    (s.storage reserve1Slot.slot).val →
                                  callerValueBefore + PairWorldBalanceSpotValueNum before before =
                                    callerValueAfter + PairWorldBalanceSpotValueNum before after →
                                    callerValueAfter ≤ callerValueBefore








/-!
## Skim And Sync — Public Calls

`skim` sends balances above cached reserves and leaves reserves unchanged.
`sync` writes the currently observed balances as new reserves, subject to
the uint112 reserve domain.
-/

def pair_skim_run_success_transfers_excess_and_restores_unlocked
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    s.storage reserve0Slot.slot ≤ observedBalance0 s →
      s.storage reserve1Slot.slot ≤ observedBalance1 s →
        (skim toAddr).run s =
          ContractResult.success () ((skim toAddr).run s).snd ∧
        ((skim toAddr).run s).snd.storage reserve0Slot.slot =
          s.storage reserve0Slot.slot ∧
        ((skim toAddr).run s).snd.storage reserve1Slot.slot =
          s.storage reserve1Slot.slot ∧
        ((skim toAddr).run s).snd.storage unlockedSlot.slot = 1 ∧
        hasPairSafeTransferTrace
          (s.storageAddr token0Slot.slot)
          s.thisAddress
          toAddr
          (skimExcess0 s)
          ((skim toAddr).run s).snd ∧
        hasPairSafeTransferTrace
          (s.storageAddr token1Slot.slot)
          s.thisAddress
          toAddr
          (skimExcess1 s)
          ((skim toAddr).run s).snd

/-- Successful `skim` has the exact token-world effect that its name promises:
when replayed through the pair-local ERC20 transfer trace, it transfers only the
token0 and token1 surplus above cached reserves from the pair to `toAddr`. -/
def pair_skim_run_success_moves_exact_surplus_in_token_world
    (toAddr : Address) (pre post : PairTokenBalances) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    s.storage reserve0Slot.slot ≤ observedBalance0 s →
      s.storage reserve1Slot.slot ≤ observedBalance1 s →
        post = pairTokenWorldAfterCall pre s ((skim toAddr).run s) →
          post =
            pairTokenWorldAfterTransfer
              (pairTokenWorldAfterTransfer pre
                (s.storageAddr token0Slot.slot)
                s.thisAddress
                toAddr
                (skimExcess0 s))
              (s.storageAddr token1Slot.slot)
              s.thisAddress
              toAddr
              (skimExcess1 s)


def pair_skim_success_run_implies_balances_back_reserves
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      s.storage reserve0Slot.slot ≤ observedBalance0 s ∧
      s.storage reserve1Slot.slot ≤ observedBalance1 s

/-- A successful public `skim` call restores the pair lock before returning.
The balance premises are not assumptions here; they are derived from the exact
under-reserve revert facts. -/
def pair_skim_success_run_restores_unlocked_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      result.snd.storage unlockedSlot.slot = 1

/-- When `skim` succeeds, the lock gate passed and the pair held at least its
cached reserves, so the call follows the skim rule used by the invariant
proofs. -/
def pair_skim_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      PairWorldStep PairWorldAction.skim
        (pairWorldFromConcreteState s)
        (pairWorldAfterSkimRun s)

/-- Successful `skim` is not a liquidity operation. Once success identifies the
closed-world skim transition, LP total supply and locked liquidity are unchanged.
-/
def pair_skim_success_run_preserves_liquidity_supply_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSkimRun s
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      after.totalSupply = before.totalSupply ∧
        after.lockedLiquidity = before.lockedLiquidity

/--
Successful `skim` preserves the core pair invariant.

The precondition is the projection of the concrete pre-state into the
closed-world invariant. Success of the real public call proves that the
call follows the skim rule; the invariant layer then proves that
reserve backing, uint112 bounds, and LP-supply lock coherence survive the call.
-/
def pair_skim_success_run_preserves_good_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSkimRun s
  PairWorldGood before →
    result = (skim toAddr).run s →
      result = ContractResult.success () result.snd →
        PairWorldGood after

/--
When `skim` succeeds from a clean reachable pool, it cannot transfer value to
the caller.

`skim` is allowed to remove surplus above cached reserves; that surplus is an
external gift, not AMM-created value. When the starting pool has no surplus, a
successful public `skim` is a no-op on pair token balances in the model.
Therefore, if caller-plus-pair actual token-balance value is merely redistributed
at the starting spot price, the caller cannot finish richer.
-/
def pair_skim_success_run_no_caller_token_balance_profit_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit)
    (callerValueBefore callerValueAfter : Nat) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSkimRun s
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      PairWorldReachable before →
        PairWorldSurplus0 before = 0 →
          PairWorldSurplus1 before = 0 →
            callerValueBefore + PairWorldBalanceSpotValueNum before before =
              callerValueAfter + PairWorldBalanceSpotValueNum before after →
              callerValueAfter ≤ callerValueBefore

def pair_sync_run_revert_locked
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    (sync).run s =
      ContractResult.revert "UniswapV2: LOCKED" s

/--
The Pair lock is a contract-level boundary, not a per-function curiosity. If a
callback or nested call reaches the pair while the lock is closed, every
state-changing AMM entrypoint rejects before it can transfer tokens, update
reserves, or touch LP accounting. This global statement packages the exact
locked-run facts above into the reentrancy invariant a reader should cite.
-/
def pair_reentrancy_guard_blocks_all_mutating_entrypoints
    (mintTo burnTo skimTo swapTo : Address)
    (amount0Out amount1Out : Uint256) (data : ByteArray)
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    (mint mintTo).run s = ContractResult.revert "UniswapV2: LOCKED" s ∧
    (burn burnTo).run s = ContractResult.revert "UniswapV2: LOCKED" s ∧
    (swap amount0Out amount1Out swapTo data).run s =
      ContractResult.revert "UniswapV2: LOCKED" s ∧
    (skim skimTo).run s = ContractResult.revert "UniswapV2: LOCKED" s ∧
    (sync).run s = ContractResult.revert "UniswapV2: LOCKED" s

/--
Flash callbacks run while the pair is locked.

The recipient callback may attempt arbitrary nested calls. Any nested call back
into the pair sees the lock value closed, because the swap closes the lock
before optimistic transfers and callback execution.
-/
def pair_flash_callback_runs_while_pair_is_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) : Prop :=
  data.size > 0 →
    (pairCallbackObservationForSwap amount0Out amount1Out toAddr s).lockValue = 0

/--
Any attempt to mutate the pair during a flash callback is blocked by the normal
reentrancy guard.

This is the callback-facing version of the global lock invariant above: mint,
burn, swap, skim, and sync all reject before durable side effects when the
callback reaches the pair while the lock is closed.
-/
def pair_flash_callback_reentry_attempts_revert_locked
    (mintTo burnTo skimTo swapTo : Address)
    (amount0Out amount1Out nested0Out nested1Out : Uint256)
    (data nestedData : ByteArray)
    (s : ContractState) : Prop :=
  data.size > 0 →
    let callbackState := pairLockedState s
    (mint mintTo).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState ∧
    (burn burnTo).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState ∧
    (swap nested0Out nested1Out swapTo nestedData).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState ∧
    (skim skimTo).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState ∧
    (sync).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState

/-- If `mint` succeeds, the initial lock value must have been open. -/
def pair_mint_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  result = (mint toAddr).run s →
    (∃ liquidity, result = ContractResult.success liquidity result.snd) →
      s.storage unlockedSlot.slot = 1

/-- If `burn` succeeds, the initial lock value must have been open. -/
def pair_burn_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  result = (burn toAddr).run s →
    (∃ amounts, result = ContractResult.success amounts result.snd) →
      s.storage unlockedSlot.slot = 1

/-- If `swap` succeeds, the initial lock value must have been open. -/
def pair_swap_success_run_implies_lock_open
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      s.storage unlockedSlot.slot = 1

/-- A successful `swap` must have passed the first economic guard: at least one
output amount is nonzero. A zero-output request fails before token transfers,
callback repayment, or the K check can matter. -/
def pair_swap_success_run_implies_nonzero_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out ≠ 0 ∨ amount1Out ≠ 0

/-- If `skim` succeeds, the initial lock value must have been open. -/
def pair_skim_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      s.storage unlockedSlot.slot = 1

def pair_sync_run_revert_balance0_overflow
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance0 s > maxUint112 →
      (sync).run s =
        ContractResult.revert "UniswapV2: OVERFLOW" s

def pair_sync_run_revert_balance1_overflow
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance1 s > maxUint112 →
      (sync).run s =
        ContractResult.revert "UniswapV2: OVERFLOW" s


/-- A successful `mint` call cannot have observed balances outside the reserve
domain. If either token balance were above `uint112`, the exact mint overflow
revert specs would force the run to revert instead. -/
def pair_mint_success_run_implies_balances_fit_uint112
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  result = (mint toAddr).run s →
    (∃ liquidity, result = ContractResult.success liquidity result.snd) →
      observedBalance0 s ≤ maxUint112 ∧
      observedBalance1 s ≤ maxUint112

/-- A successful `sync` call must have passed the reentrancy lock gate. If the
lock were closed, the exact locked-revert spec would force the run to return
`LOCKED` instead of success. -/
def pair_sync_success_run_implies_lock_open
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      s.storage unlockedSlot.slot = 1

/-- A successful `sync` call cannot have observed balances outside the reserve
domain. If either observed token balance were above `uint112`, the exact
overflow revert specs above would force the run to revert instead. -/
def pair_sync_success_run_implies_balances_fit_uint112
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      observedBalance0 s ≤ maxUint112 ∧
      observedBalance1 s ≤ maxUint112

/-- When `sync` succeeds, the lock gate and reserve-domain checks passed, so
the call follows the sync rule used by the invariant proofs. -/
def pair_sync_success_run_matches_closed_world_step_from_run
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      PairWorldStep PairWorldAction.sync
        (pairWorldFromConcreteState s)
        (pairWorldAfterSyncRun s)

/-- Successful `sync` is reserve accounting, not LP issuance or redemption. Once
the call follows the sync rule, LP total supply and locked liquidity are
unchanged.
-/
def pair_sync_success_run_preserves_liquidity_supply_from_run
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSyncRun s
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      after.totalSupply = before.totalSupply ∧
        after.lockedLiquidity = before.lockedLiquidity

/--
Successful `sync` preserves the core pair invariant.

The public call first proves its observed balances fit the reserve domain, then
follows the sync rule. From a good projected pre-state, that rule preserves the
same invariant package that the global trace
theorems use: reserves remain backed, reserves remain `uint112`, and LP supply
keeps the minimum-liquidity lock shape.
-/
def pair_sync_success_run_preserves_good_from_run
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  let before := pairWorldFromConcreteState s
  let after := pairWorldAfterSyncRun s
  PairWorldGood before →
    result = (sync).run s →
      result = ContractResult.success () result.snd →
        PairWorldGood after

/--
When `sync` succeeds from a clean reachable pool, it cannot transfer value to
the caller.

`sync` changes accounting, not custody: it records current token balances as
cached reserves. From a zero-surplus reachable pool, current balances already
equal cached reserves, so a successful public `sync` is a no-op on actual pair
token balances in the model. If caller-plus-pair token-balance value is only
redistributed at the starting spot price, the caller therefore cannot finish
richer.
-/
def pair_sync_success_run_no_caller_token_balance_profit_from_run
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

/-- A successful public `sync` caches the pair's currently observed token
balances as reserves. -/
def pair_sync_success_run_updates_reserves_to_balances_from_run
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  let after := pairWorldAfterSyncRun s
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      after.reserve0 = after.balance0 ∧
        after.reserve1 = after.balance1

/-!
## Flash-Swap Boundary

A swap optimistically sends output, optionally calls the recipient, then
reads final balances and enforces K against the post-callback balances.
The compiled callback ECM is gated by nonempty calldata.
-/

def pair_flash_callback_module_gates_nonempty_data : Prop :=
  ∀ (ctx : Compiler.ECM.CompilationContext)
    (target sender amount0Out amount1Out : Compiler.Yul.YulExpr)
    (stmts : List Compiler.Yul.YulStmt),
    TamaUniV2.uniswapV2CallbackModule.compile ctx
        [target, sender, amount0Out, amount1Out] = Except.ok stmts →
      ∃ body,
        stmts =
          [Compiler.Yul.YulStmt.if_
            (Compiler.Yul.YulExpr.call "gt"
              [Compiler.Yul.YulExpr.ident "data_length", Compiler.Yul.YulExpr.lit 0])
            body]

/--
The callback boundary must not merely be gated; the gated body must be the
canonical Uniswap V2 callback shape. It writes the `uniswapV2Call` selector,
forwards the original swap sender and output amounts as calldata words, and
uses the recipient as the call target. The dynamic bytes payload is handled by
the ECM helper, so this spec focuses on the fixed ABI prefix and target call
that are security-critical for flash-swap compatibility.
-/
def pair_flash_callback_module_encodes_canonical_call : Prop :=
  ∀ (ctx : Compiler.ECM.CompilationContext)
    (target sender amount0Out amount1Out : Compiler.Yul.YulExpr)
    (stmts : List Compiler.Yul.YulStmt),
    TamaUniV2.uniswapV2CallbackModule.compile ctx
        [target, sender, amount0Out, amount1Out] = Except.ok stmts →
      ∃ body totalSize,
        stmts =
          [Compiler.Yul.YulStmt.if_
            (Compiler.Yul.YulExpr.call "gt"
              [Compiler.Yul.YulExpr.ident "data_length", Compiler.Yul.YulExpr.lit 0])
            [Compiler.Yul.YulStmt.block body]] ∧
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "mstore"
            [Compiler.Yul.YulExpr.lit 0,
              Compiler.Yul.YulExpr.call "shl"
                [Compiler.Yul.YulExpr.lit 224, Compiler.Yul.YulExpr.hex 0x10d1e85c]]) ∈ body ∧
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 4, sender]) ∈ body ∧
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 36, amount0Out]) ∈ body ∧
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 68, amount1Out]) ∈ body ∧
        Compiler.Yul.YulStmt.let_ "__uv2_cb_success"
          (Compiler.Yul.YulExpr.call "call"
            [Compiler.Yul.YulExpr.call "gas" [],
              target,
              Compiler.Yul.YulExpr.lit 0,
              Compiler.Yul.YulExpr.lit 0,
              totalSize,
              Compiler.Yul.YulExpr.lit 0,
              Compiler.Yul.YulExpr.lit 0]) ∈ body

/--
Callback failure must be visible to the pair. The ECM-generated callback body
records the low-level call result and, when that result is zero, copies the
callee's returndata and reverts with it. The general EVM/Verity revert frame is
what makes the state rollback atomic; this spec proves the callback boundary
actually reaches that revert path instead of silently continuing.
-/
def pair_flash_callback_module_bubbles_callback_failure : Prop :=
  ∀ (ctx : Compiler.ECM.CompilationContext)
    (target sender amount0Out amount1Out : Compiler.Yul.YulExpr)
    (stmts : List Compiler.Yul.YulStmt),
    TamaUniV2.uniswapV2CallbackModule.compile ctx
        [target, sender, amount0Out, amount1Out] = Except.ok stmts →
      ∃ body,
        stmts =
          [Compiler.Yul.YulStmt.if_
            (Compiler.Yul.YulExpr.call "gt"
              [Compiler.Yul.YulExpr.ident "data_length", Compiler.Yul.YulExpr.lit 0])
            [Compiler.Yul.YulStmt.block body]] ∧
        Compiler.Yul.YulStmt.if_
          (Compiler.Yul.YulExpr.call "iszero"
            [Compiler.Yul.YulExpr.ident "__uv2_cb_success"])
          [ Compiler.Yul.YulStmt.let_ "__uv2_cb_rds"
              (Compiler.Yul.YulExpr.call "returndatasize" [])
          , Compiler.Yul.YulStmt.expr
              (Compiler.Yul.YulExpr.call "returndatacopy"
                [Compiler.Yul.YulExpr.lit 0,
                  Compiler.Yul.YulExpr.lit 0,
                  Compiler.Yul.YulExpr.ident "__uv2_cb_rds"])
          , Compiler.Yul.YulStmt.expr
              (Compiler.Yul.YulExpr.call "revert"
                [Compiler.Yul.YulExpr.lit 0,
                  Compiler.Yul.YulExpr.ident "__uv2_cb_rds"])
          ] ∈ body

/-!
## Exact Guard Runs

Each statement: once the hypotheses establish that earlier guards have
failed or passed in the intended order, the public entrypoint returns the
canonical revert string and the pre-call state. Guard order is
security-relevant — every guarded failure must happen before any ERC20
transfer, callback, reserve update, or LP accounting write becomes
durable.
-/

def pair_initialize_run_revert_non_factory
    (token0Value token1Value : Address) (s : ContractState) : Prop :=
  s.sender != s.storageAddr factorySlot.slot →
    («initialize» token0Value token1Value).run s =
      ContractResult.revert "UniswapV2: FORBIDDEN" s

def pair_initialize_run_revert_already_initialized
    (token0Value token1Value : Address) (s : ContractState) : Prop :=
  s.sender = s.storageAddr factorySlot.slot →
    (s.storageAddr token0Slot.slot != zeroAddress ∨
      s.storageAddr token1Slot.slot != zeroAddress) →
      («initialize» token0Value token1Value).run s =
        ContractResult.revert "UniswapV2: ALREADY_INITIALIZED" s

def pair_transfer_run_revert_balance_low
    (toAddr : Address) (amount : Uint256) (s : ContractState) : Prop :=
  amount.val > (s.storageMap balancesSlot.slot s.sender).val →
    (transfer toAddr amount).run s =
      ContractResult.revert "UniswapV2: INSUFFICIENT_BALANCE" s

def pair_transfer_run_revert_recipient_balance_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) : Prop :=
  amount.val ≤ (s.storageMap balancesSlot.slot s.sender).val →
    s.sender ≠ toAddr →
      (s.storageMap balancesSlot.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
        (transfer toAddr amount).run s =
          ContractResult.revert "UniswapV2: BALANCE_OVERFLOW" s

def pair_transferFrom_run_revert_allowance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) : Prop :=
  amount.val > (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    (transferFrom fromAddr toAddr amount).run s =
      ContractResult.revert "UniswapV2: INSUFFICIENT_ALLOWANCE" s

def pair_transferFrom_run_revert_balance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val > (s.storageMap balancesSlot.slot fromAddr).val →
      (transferFrom fromAddr toAddr amount).run s =
        ContractResult.revert "UniswapV2: INSUFFICIENT_BALANCE" s

def pair_transferFrom_run_revert_recipient_balance_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balancesSlot.slot fromAddr).val →
      fromAddr ≠ toAddr →
        (s.storageMap balancesSlot.slot toAddr).val + amount.val >
            Verity.Stdlib.Math.MAX_UINT256 →
          (transferFrom fromAddr toAddr amount).run s =
            ContractResult.revert "UniswapV2: BALANCE_OVERFLOW" s

def pair_mint_run_revert_locked
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    (mint toAddr).run s =
      ContractResult.revert "UniswapV2: LOCKED" s

/--
Mint is allowed to turn observed ERC20 balances into cached reserves only while
those balances fit in the canonical `uint112` reserve domain. This is the first
economic guard after the reentrancy gate and balance reads, so an out-of-range
token0 balance must revert before any liquidity formula can run.
-/
def pair_mint_run_revert_balance0_overflow
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance0 s > maxUint112 →
      (mint toAddr).run s =
        ContractResult.revert "UniswapV2: OVERFLOW" s

/--
The same reserve-domain guard applies symmetrically to token1. Together these
two obligations make the public `mint` boundary agree with the closed-world
invariant that every cached reserve always remains inside `uint112`.
-/
def pair_mint_run_revert_balance1_overflow
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance1 s > maxUint112 →
      (mint toAddr).run s =
        ContractResult.revert "UniswapV2: OVERFLOW" s

def pair_burn_run_revert_locked
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    (burn toAddr).run s =
      ContractResult.revert "UniswapV2: LOCKED" s

def pair_swap_run_revert_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    (swap amount0Out amount1Out toAddr data).run s =
      ContractResult.revert "UniswapV2: LOCKED" s

/--
Before the pair can send optimistic output or cross the flash-callback boundary,
the swap must request at least one nonzero output amount.
-/
def pair_swap_run_revert_zero_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    amount0Out = 0 →
      amount1Out = 0 →
        (swap amount0Out amount1Out toAddr data).run s =
          ContractResult.revert "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT" s

def pair_skim_run_revert_locked
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    (skim toAddr).run s =
      ContractResult.revert "UniswapV2: LOCKED" s

def pair_skim_run_revert_balance0_below_reserve
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance0 s < s.storage reserve0Slot.slot →
      (skim toAddr).run s =
        ContractResult.revert "UniswapV2: INSUFFICIENT_BALANCE" s

def pair_skim_run_revert_balance1_below_reserve
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance1 s < s.storage reserve1Slot.slot →
      (skim toAddr).run s =
        ContractResult.revert "UniswapV2: INSUFFICIENT_BALANCE" s

/-!
## Revert Frames

A reverted pair call leaves the replayed token-balance world unchanged and
preserves the pair's storage and event log.
-/

def pair_mint_revert_keeps_token_balances
    (toAddr : Address) (pre post : PairTokenBalances) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  post = pairTokenWorldAfterCall pre s result →
    pairRevertedWithOriginalState s result →
      pairTokenBalancesUnchanged pre post

def pair_burn_revert_keeps_token_balances
    (toAddr : Address) (pre post : PairTokenBalances) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  post = pairTokenWorldAfterCall pre s result →
    pairRevertedWithOriginalState s result →
      pairTokenBalancesUnchanged pre post

def pair_swap_revert_keeps_token_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (pre post : PairTokenBalances) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  post = pairTokenWorldAfterCall pre s result →
    pairRevertedWithOriginalState s result →
      pairTokenBalancesUnchanged pre post

def pair_skim_revert_keeps_token_balances
    (toAddr : Address) (pre post : PairTokenBalances) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  post = pairTokenWorldAfterCall pre s result →
    pairRevertedWithOriginalState s result →
      pairTokenBalancesUnchanged pre post

def pair_sync_revert_keeps_token_balances
    (pre post : PairTokenBalances) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  post = pairTokenWorldAfterCall pre s result →
    pairRevertedWithOriginalState s result →
      pairTokenBalancesUnchanged pre post

/-!
## LP Bookkeeping Frame

Approve, transfer, and transferFrom do not call the underlying token
contracts; replaying the pair-local ERC20 transfer trace across these
calls leaves the token-balance world unchanged.
-/

def pair_approve_run_keeps_token_balances
    (spender : Address) (amount : Uint256)
    (pre post : PairTokenBalances) (s : ContractState) : Prop :=
  post = pairTokenWorldAfterCall pre s ((approve spender amount).run s) →
    pairTokenBalancesUnchanged pre post

def pair_transfer_run_keeps_token_balances
    (toAddr : Address) (amount : Uint256)
    (pre post : PairTokenBalances) (s : ContractState) : Prop :=
  post = pairTokenWorldAfterCall pre s ((transfer toAddr amount).run s) →
    pairTokenBalancesUnchanged pre post

def pair_transferFrom_run_keeps_token_balances
    (fromAddr toAddr : Address) (amount : Uint256)
    (pre post : PairTokenBalances) (s : ContractState) : Prop :=
  post = pairTokenWorldAfterCall pre s ((transferFrom fromAddr toAddr amount).run s) →
    pairTokenBalancesUnchanged pre post

def pair_mint_revert_keeps_pair_state
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  result = (mint toAddr).run s →
    (∃ reason, result = ContractResult.revert reason s) →
      result.snd.storage = s.storage ∧
      result.snd.storageMap = s.storageMap ∧
      result.snd.storageMap2 = s.storageMap2 ∧
      result.snd.events = s.events

def pair_burn_revert_keeps_pair_state
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  result = (burn toAddr).run s →
    (∃ reason, result = ContractResult.revert reason s) →
      result.snd.storage = s.storage ∧
      result.snd.storageMap = s.storageMap ∧
      result.snd.storageMap2 = s.storageMap2 ∧
      result.snd.events = s.events

def pair_swap_revert_keeps_pair_state
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    (∃ reason, result = ContractResult.revert reason s) →
      result.snd.storage = s.storage ∧
      result.snd.storageMap = s.storageMap ∧
      result.snd.storageMap2 = s.storageMap2 ∧
      result.snd.events = s.events

def pair_skim_revert_keeps_pair_state
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    (∃ reason, result = ContractResult.revert reason s) →
      result.snd.storage = s.storage ∧
      result.snd.storageMap = s.storageMap ∧
      result.snd.storageMap2 = s.storageMap2 ∧
      result.snd.events = s.events

def pair_sync_revert_keeps_pair_state
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    (∃ reason, result = ContractResult.revert reason s) →
      result.snd.storage = s.storage ∧
      result.snd.storageMap = s.storageMap ∧
      result.snd.storageMap2 = s.storageMap2 ∧
      result.snd.events = s.events

/-!
## ERC20 Boundary Traces

The pair affects token balances only through ERC20 transfer ECMs. A
successful safe-transfer records a ghost event whose replay moves exactly
that token amount in the pair-local token-balance world.
-/

def pair_safeTransfer_traces_token_transfer
    (token toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  result = ContractResult.success 1 result.snd ∧
  hasPairSafeTransferTrace token s.thisAddress toAddr amount result.snd

/--
The token-transfer trace model has one job: when a pair-local ERC20 transfer
event is replayed, it moves exactly that token amount from the pair-side sender
to the recipient in the ghost token-balance world. Later public-call specs for
`skim`, `burn`, and `swap` can cite this fact instead of re-proving event
decoding each time.
-/
def pair_safeTransfer_event_replay_moves_token_balance
    (token fromAddr toAddr : Address) (amount : Uint256)
    (pre : PairTokenBalances) : Prop :=
  pairTokenWorldAfterEvent pre
      (TamaUniV2.pairTokenSafeTransferEvent token fromAddr toAddr amount) =
    pairTokenWorldAfterTransfer pre token fromAddr toAddr amount

/--
Burn and two-sided swaps use two pair-local ERC20 transfers. When the two
tokens are distinct and the transfer is not to the pair itself, replaying those
two trace events decreases the pair-side balance for each token by exactly its
amount and increases the recipient-side balance by exactly that amount. This is
a reusable fact for later burn and swap specs that need to account for both
underlying token transfers.
-/
def pair_two_safeTransfer_events_replay_move_distinct_token_balances
    (token0Value token1Value fromAddr toAddr : Address)
    (amount0 amount1 : Uint256) (pre : PairTokenBalances) : Prop :=
  token0Value ≠ token1Value →
    fromAddr ≠ toAddr →
      let post :=
        pairTokenWorldAfterEvents pre [
          TamaUniV2.pairTokenSafeTransferEvent
            token0Value fromAddr toAddr amount0,
          TamaUniV2.pairTokenSafeTransferEvent
            token1Value fromAddr toAddr amount1
        ]
      post token0Value fromAddr =
        Verity.EVM.Uint256.sub (pre token0Value fromAddr) amount0 ∧
      post token0Value toAddr =
        pre token0Value toAddr + amount0 ∧
      post token1Value fromAddr =
        Verity.EVM.Uint256.sub (pre token1Value fromAddr) amount1 ∧
      post token1Value toAddr =
        pre token1Value toAddr + amount1

/-!
## Local Entry Points

Initialization is factory-only and one-shot: token identities are fixed
after the first `initialize`. LP approve/transfer/transferFrom are
ordinary ERC20 share accounting; balances move only on transfer, total
supply is constant, finite allowances are consumed, and max allowance is
stable.
-/

/-- Initialization either rejects non-factory callers, rejects a second
initialization, or records the two token addresses exactly once. -/
def pair_initialize_reverts_for_non_factory
    (token0Value token1Value : Address) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  s.sender != s.storageAddr factorySlot.slot →
    result = ContractResult.revert "UniswapV2: FORBIDDEN" s

def pair_initialize_reverts_when_already_initialized
    (token0Value token1Value : Address) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  s.sender = s.storageAddr factorySlot.slot →
    (s.storageAddr token0Slot.slot != zeroAddress ∨
      s.storageAddr token1Slot.slot != zeroAddress) →
      result = ContractResult.revert "UniswapV2: ALREADY_INITIALIZED" s

def pair_initialize_sets_tokens
    (token0Value token1Value : Address) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  s.sender = s.storageAddr factorySlot.slot →
    s.storageAddr token0Slot.slot = zeroAddress →
      s.storageAddr token1Slot.slot = zeroAddress →
        result = ContractResult.success () result.snd ∧
        result.snd.storageAddr token0Slot.slot = token0Value ∧
        result.snd.storageAddr token1Slot.slot = token1Value

/-- Exact successful initialization boundary. When the factory calls a fresh
pair, the actual public `initialize` run succeeds and records the two token
addresses that define the market. Together with the two exact revert specs, this
states the complete token-identity lifecycle: the factory can set identity once,
and nobody can change it after that. -/
def pair_initialize_run_success_sets_tokens
    (token0Value token1Value : Address) (s : ContractState) : Prop :=
  s.sender = s.storageAddr factorySlot.slot →
    s.storageAddr token0Slot.slot = zeroAddress →
      s.storageAddr token1Slot.slot = zeroAddress →
        («initialize» token0Value token1Value).run s =
          ContractResult.success () ((«initialize» token0Value token1Value).run s).snd ∧
        ((«initialize» token0Value token1Value).run s).snd.storageAddr
          token0Slot.slot = token0Value ∧
        ((«initialize» token0Value token1Value).run s).snd.storageAddr
          token1Slot.slot = token1Value

/-- Initialization is identity-only. A successful fresh-pair initialization
must not mint LP shares, change reserves, mutate LP balances/allowances, or emit
events. This keeps factory deployment from becoming an implicit economic action;
the AMM starts changing only through mint, burn, swap, skim, and sync. -/
def pair_initialize_run_success_keeps_amm_accounting
    (token0Value token1Value : Address) (s : ContractState) : Prop :=
  s.sender = s.storageAddr factorySlot.slot →
    s.storageAddr token0Slot.slot = zeroAddress →
      s.storageAddr token1Slot.slot = zeroAddress →
        let post := ((«initialize» token0Value token1Value).run s).snd
        post.storage reserve0Slot.slot = s.storage reserve0Slot.slot ∧
        post.storage reserve1Slot.slot = s.storage reserve1Slot.slot ∧
        post.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot ∧
        post.storageMap = s.storageMap ∧
        post.storageMap2 = s.storageMap2 ∧
        post.events = s.events

/-- Approval is intentionally narrow: it returns true, writes exactly one
allowance cell, preserves all LP balances and total supply, and emits Approval. -/
def pair_approve_succeeds
    (spender : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result = ContractResult.success true result.snd

def pair_approve_sets_allowance
    (spender : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storageMap2 allowancesSlot.slot s.sender spender = amount

def pair_approve_keeps_balances
    (spender : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storageMap = s.storageMap

def pair_approve_keeps_total_supply
    (spender : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot

/-- Approval is LP-claim bookkeeping only. It may write an allowance map cell,
but it cannot change scalar AMM storage: reserves, TWAP accumulators, LP supply,
token identities, or the reentrancy lock. -/
def pair_approve_keeps_pool_storage
    (spender : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage = s.storage

def pair_approve_emits_approval
    (spender : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  pairTraceContains (pairLpApprovalEvent s.sender spender amount) result.snd.events

/-- Direct LP transfers are conservation statements. They either reject an
underfunded sender or overflowed recipient, leave self-transfers unchanged, or
move exactly `amount` between two distinct LP balances while preserving supply. -/
def pair_transfer_reverts_when_balance_low
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val > (s.storageMap balancesSlot.slot s.sender).val →
    result = ContractResult.revert "UniswapV2: INSUFFICIENT_BALANCE" s

def pair_transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balancesSlot.slot s.sender).val →
    s.sender = toAddr →
      result = ContractResult.success true result.snd ∧
      result.snd.storageMap = s.storageMap

def pair_transfer_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balancesSlot.slot s.sender).val →
    s.sender ≠ toAddr →
      (s.storageMap balancesSlot.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "UniswapV2: BALANCE_OVERFLOW" s

def pair_transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balancesSlot.slot s.sender).val →
    s.sender ≠ toAddr →
      (s.storageMap balancesSlot.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMap balancesSlot.slot s.sender =
          (s.storageMap balancesSlot.slot s.sender) - amount ∧
        result.snd.storageMap balancesSlot.slot toAddr =
          (s.storageMap balancesSlot.slot toAddr) + amount

def pair_transfer_keeps_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot

/-- Direct LP transfers may move LP balances, but they cannot change scalar AMM
storage. This is the public-call counterpart of the model-level fact that share
bookkeeping does not touch reserves, prices, supply, token identities, or the
lock. -/
def pair_transfer_keeps_pool_storage
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage = s.storage

def pair_transfer_emits_transfer
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balancesSlot.slot s.sender).val →
    (s.sender = toAddr ∨
      (s.sender ≠ toAddr ∧
        (s.storageMap balancesSlot.slot toAddr).val + amount.val ≤
          Verity.Stdlib.Math.MAX_UINT256)) →
      pairTraceContains (pairLpTransferEvent s.sender toAddr amount) result.snd.events

/-- Delegated LP transfers add the allowance dimension to the same conservation
story. The source balance still pays, the recipient still receives exactly the
amount, finite allowance is spent, and max allowance remains max. -/
def pair_transferFrom_reverts_when_allowance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val > (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    result = ContractResult.revert "UniswapV2: INSUFFICIENT_ALLOWANCE" s

def pair_transferFrom_reverts_when_balance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val > (s.storageMap balancesSlot.slot fromAddr).val →
      result = ContractResult.revert "UniswapV2: INSUFFICIENT_BALANCE" s

def pair_transferFrom_reverts_when_recipient_balance_would_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balancesSlot.slot fromAddr).val →
      fromAddr ≠ toAddr →
        (s.storageMap balancesSlot.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
          result = ContractResult.revert "UniswapV2: BALANCE_OVERFLOW" s

def pair_transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balancesSlot.slot fromAddr).val →
      fromAddr = toAddr →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMap = s.storageMap

def pair_transferFrom_moves_tokens_between_distinct_accounts
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balancesSlot.slot fromAddr).val →
      fromAddr ≠ toAddr →
        (s.storageMap balancesSlot.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
          result = ContractResult.success true result.snd ∧
          result.snd.storageMap balancesSlot.slot fromAddr =
            (s.storageMap balancesSlot.slot fromAddr) - amount ∧
          result.snd.storageMap balancesSlot.slot toAddr =
            (s.storageMap balancesSlot.slot toAddr) + amount

def pair_transferFrom_keeps_total_supply
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot

/-- Delegated LP transfers have the same AMM-storage frame as direct transfers.
They may update balances and finite allowance, but no scalar pool accounting
slot can move. -/
def pair_transferFrom_keeps_pool_storage
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage = s.storage

def pair_transferFrom_keeps_infinite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balancesSlot.slot fromAddr).val →
      (fromAddr = toAddr ∨
        (fromAddr ≠ toAddr ∧
          (s.storageMap balancesSlot.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256)) →
        s.storageMap2 allowancesSlot.slot fromAddr s.sender = maxUint256 →
          result.snd.storageMap2 allowancesSlot.slot fromAddr s.sender = maxUint256

def pair_transferFrom_spends_finite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balancesSlot.slot fromAddr).val →
      (fromAddr = toAddr ∨
        (fromAddr ≠ toAddr ∧
          (s.storageMap balancesSlot.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256)) →
        s.storageMap2 allowancesSlot.slot fromAddr s.sender != maxUint256 →
          result.snd.storageMap2 allowancesSlot.slot fromAddr s.sender =
            (s.storageMap2 allowancesSlot.slot fromAddr s.sender) - amount

def pair_transferFrom_emits_transfer
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowancesSlot.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balancesSlot.slot fromAddr).val →
      (fromAddr = toAddr ∨
        (fromAddr ≠ toAddr ∧
          (s.storageMap balancesSlot.slot toAddr).val + amount.val ≤
            Verity.Stdlib.Math.MAX_UINT256)) →
        pairTraceContains (pairLpTransferEvent fromAddr toAddr amount) result.snd.events

/-- The following adapter specs name common failure branches with an explicit
result parameter. Exact-run specs below reuse these small facts when the proof
needs to reduce a concrete entrypoint call. -/
def pair_mint_reverts_when_locked
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    result = ContractResult.revert "UniswapV2: LOCKED" s

def pair_burn_reverts_when_locked
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    result = ContractResult.revert "UniswapV2: LOCKED" s

def pair_swap_reverts_when_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    result = ContractResult.revert "UniswapV2: LOCKED" s

def pair_skim_reverts_when_locked
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    result = ContractResult.revert "UniswapV2: LOCKED" s

def pair_skim_reverts_when_balance0_below_reserve
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance0 s < s.storage reserve0Slot.slot →
      result = ContractResult.revert "UniswapV2: INSUFFICIENT_BALANCE" s

def pair_skim_reverts_when_balance1_below_reserve
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance1 s < s.storage reserve1Slot.slot →
      result = ContractResult.revert "UniswapV2: INSUFFICIENT_BALANCE" s

def pair_sync_reverts_when_locked
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    result = ContractResult.revert "UniswapV2: LOCKED" s

/-!
## Views

Each public read returns the expected storage cell (or constant) and frames
pair state on success. With the protocol fee mint off, `kLast()` is the
constant zero read.
-/

/-- `decimals` is a pure LP-token display constant and cannot mutate pair
state. -/
def pair_decimals_run_success_frames_state
    (s : ContractState) : Prop :=
  (decimals).run s = ContractResult.success 18 s

/-- `totalSupply` exposes exactly the LP supply cell. It is the public read that
anchors every LP-supply and no-profit theorem below. -/
def pair_totalSupply_run_success_frames_state
    (s : ContractState) : Prop :=
  (totalSupply).run s =
    ContractResult.success (s.storage totalSupplySlot.slot) s

/-- `balanceOf` exposes exactly one LP balance cell and has no side effects. -/
def pair_balanceOf_run_success_frames_state
    (account : Address) (s : ContractState) : Prop :=
  (balanceOf account).run s =
    ContractResult.success (s.storageMap balancesSlot.slot account) s

/-- `allowance` exposes exactly one delegated-LP-spend cell and has no side
effects. -/
def pair_allowance_run_success_frames_state
    (owner spender : Address) (s : ContractState) : Prop :=
  (allowance owner spender).run s =
    ContractResult.success (s.storageMap2 allowancesSlot.slot owner spender) s

/-- `factory` exposes the immutable creator/initializer authority stored for
the pair and has no side effects. -/
def pair_factory_run_success_frames_state
    (s : ContractState) : Prop :=
  (factory).run s =
    ContractResult.success (s.storageAddr factorySlot.slot) s

/-- `token0` exposes the first market token identity recorded at initialization
and has no side effects. -/
def pair_token0_run_success_frames_state
    (s : ContractState) : Prop :=
  (token0).run s =
    ContractResult.success (s.storageAddr token0Slot.slot) s

/-- `token1` exposes the second market token identity recorded at initialization
and has no side effects. -/
def pair_token1_run_success_frames_state
    (s : ContractState) : Prop :=
  (token1).run s =
    ContractResult.success (s.storageAddr token1Slot.slot) s

/-- `MINIMUM_LIQUIDITY` exposes the permanent lock constant used by the
finite-history liquidity-lock theorems. -/
def pair_minimumLiquidity_run_success_frames_state
    (s : ContractState) : Prop :=
  (MINIMUM_LIQUIDITY).run s =
    ContractResult.success minimumLiquidity s

/-- `getReserves` is the reserve oracle boundary exposed to routers and users.
It is an exact state-framing read of cached reserve0, cached reserve1, and the
last 32-bit update timestamp. -/
def pair_getReserves_run_success_frames_state
    (s : ContractState) : Prop :=
  (getReserves).run s =
    ContractResult.success
      (s.storage reserve0Slot.slot,
        s.storage reserve1Slot.slot,
        s.storage blockTimestampLastSlot.slot)
      s

/-- `price0CumulativeLast` exposes exactly the cached token0 TWAP accumulator
and has no side effects. -/
def pair_price0CumulativeLast_run_success_frames_state
    (s : ContractState) : Prop :=
  (price0CumulativeLast).run s =
    ContractResult.success (s.storage price0CumulativeLastSlot.slot) s

/-- `price1CumulativeLast` exposes exactly the cached token1 TWAP accumulator
and has no side effects. -/
def pair_price1CumulativeLast_run_success_frames_state
    (s : ContractState) : Prop :=
  (price1CumulativeLast).run s =
    ContractResult.success (s.storage price1CumulativeLastSlot.slot) s

/-- The fee-off Pair never uses protocol-fee accounting, so `kLast()` is the
constant zero read and cannot mutate state. -/
def pair_kLast_run_success_frames_state
    (s : ContractState) : Prop :=
  (kLast).run s = ContractResult.success 0 s

end TamaUniV2.Spec.UniswapV2PairSpec
