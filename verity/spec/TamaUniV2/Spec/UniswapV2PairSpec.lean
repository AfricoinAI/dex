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
callbacks, and CREATE2 deployment.

## Properties

### Tier 1 — Economic safety

1. From any reachable state, no finite sequence of valid actions can
   increase a single caller's initial-spot-price portfolio value (wallet
   tokens + LP-claimed reserves + skimmable surplus).

2. Across every finite reachable history from a positive-supply state,
   reserve product per squared LP supply is monotone non-decreasing.

### Tier 2 — Structural invariants

3. Cached reserves are covered by actual ERC20 balances along every finite
   reachable history.

4. Cached reserves never exceed the uint112 bound.

5. Once positive LP supply exists, the locked `MINIMUM_LIQUIDITY` floor is
   monotone non-decreasing and never redeemable.

6. LP supply changes only on mint or burn.

7. Once the reentrancy lock is closed, every mutating entrypoint reverts
   before durable side effects.

8. Donations are the only source of skimmable surplus.

### Tier 3 — Boundary mechanics

9. Every guarded failure has a canonical revert payload and leaves the
   pre-call state unchanged.

10. Token movement is modeled by pair-local ERC20 trace events.

11. LP approve/transfer/transferFrom move share claims only; AMM state,
    reserves, and token balances are unchanged.

12. Initialization is factory-only and one-shot; after the first
    `initialize`, token identities are fixed.

13. Views return exactly one storage cell (or a constant) without mutating
    state.

14. Each successful public mutating call matches its closed-world
    transition and the corresponding caller-wallet step, bridging the
    contract boundary into the models used by properties 1–13.
-/

/-!
## 1. Single-Caller Portfolio Safety

The headline economic property. From any reachable state, no finite
sequence of valid caller actions can increase the caller's portfolio
value at the initial spot price.
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
## 2. LP-Share Backing

Across every finite reachable history from a positive-supply state,
reserve product per squared LP supply is monotone non-decreasing.
This is the global mint/burn ratio guarantee — and the underlying
mathematical content of the no-profit theorem in § 1.
-/

/-- Starting from any reachable pool with positive LP supply, every finite
successful path leaves reserve product per squared LP supply at least as
strong as it was at the start. -/
def pair_closed_world_reachable_path_lp_share_backing_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        PairWorldKPerSupplyNondecreasing before after

/-!
## 3. Reserve Backing

Cached reserves are always covered by the pair's actual ERC20
balances along every finite reachable history.
-/

def pair_concrete_state_reserves_backed
    (s : ContractState) : Prop :=
  PairWorldGood (pairWorldFromConcreteState s) →
    (s.storage reserve0Slot.slot).val ≤ (observedBalance0 s).val ∧
    (s.storage reserve1Slot.slot).val ≤ (observedBalance1 s).val

/-- The reserve-backing invariant in its most useful reader-facing form:
from any reachable pool state, after any finite sequence of successful modeled
calls, the cached reserves are still covered by the pair's token balances. -/
def pair_closed_world_reachable_path_reserves_backed
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      after.reserve0 ≤ after.balance0 ∧
      after.reserve1 ≤ after.balance1

/-!
## 4. uint112 Reserve Domain

Cached reserves never exceed the canonical 2^112 bound.
-/

def pair_concrete_state_uint112_reserves
    (s : ContractState) : Prop :=
  PairWorldGood (pairWorldFromConcreteState s) →
    (s.storage reserve0Slot.slot).val ≤ maxUint112Nat ∧
    (s.storage reserve1Slot.slot).val ≤ maxUint112Nat

/-- The reserve-domain invariant in the same finite-history form: a reachable
pool can never reach a successful modeled state whose cached reserves exceed
Uniswap V2's `uint112` reserve domain. -/
def pair_closed_world_reachable_path_reserves_fit_uint112
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      after.reserve0 ≤ maxUint112Nat ∧
      after.reserve1 ≤ maxUint112Nat

/-!
## 5. Minimum-Liquidity Lock

Once positive LP supply exists, `MINIMUM_LIQUIDITY` is permanently
locked: the first LP cannot own the entire supply, the lock is
monotone non-decreasing across finite reachable histories, and burn
cannot redeem the locked floor.
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

/-- Reader-facing reachable form: in every reachable pool history, the locked
liquidity amount is monotone. Once the first mint installs
`MINIMUM_LIQUIDITY`, later mint, burn, swap, skim, sync, donation, and share
bookkeeping actions cannot reduce it. -/
def pair_closed_world_reachable_path_locked_liquidity_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPath before after →
      before.lockedLiquidity ≤ after.lockedLiquidity

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

def pair_closed_world_burn_cannot_redeem_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    before.lockedLiquidity ≤ after.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

/-!
## 6. LP Supply Discipline

Mint and burn are the only transitions that change total LP supply.
Share-only actions (approve, transfer, transferFrom) leave the pool
model exactly unchanged. Mint adds exact deposits to reserves; burn
removes exact pro-rata redemptions and preserves positive balances.
-/

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

/-!
## 7. Reentrancy Lock

Once the lock is closed, every mutating entrypoint reverts before
durable side effects. Flash callbacks run while the lock is closed;
the compiled callback ECM is gated by nonempty calldata, encodes
the canonical `uniswapV2Call` invocation, and bubbles callback
failure.
-/

/--
If a callback or nested call reaches the pair while the lock is closed,
every state-changing AMM entrypoint rejects before it can transfer tokens,
update reserves, or touch LP accounting. This packages the per-entrypoint
locked-run reverts into one reentrancy invariant.
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
Any attempt to mutate the pair during a flash callback is blocked by the
reentrancy guard. Mint, burn, swap, skim, and sync all reject before durable
side effects when the callback reaches the pair while the lock is closed.
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
## 8. Donations And Surplus

Donations are the only way new skimmable surplus can appear above
cached reserves. `skim` removes exactly that surplus; `sync` writes
the observed balances back into cached reserves. Neither action
mints or burns LP supply or weakens K from a reserve-backed state.
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

def pair_closed_world_skim_removes_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.skim before after →
    after.balance0 = before.reserve0 ∧
    after.balance1 = before.reserve1 ∧
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1

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

/-!
## 9. Exact-Revert Guards

Every guarded failure has a canonical revert payload and leaves the
pre-call state unchanged: pair storage, LP balances and allowances,
the event log, and the replayed token-balance world.
-/

def pair_sync_run_revert_locked
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    (sync).run s =
      ContractResult.revert "UniswapV2: LOCKED" s

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

/-!
## 10. ERC20 Trace Boundary

The pair affects token balances only through ERC20 transfer ECMs.
Each successful `safeTransfer` records a pair-local ghost event
whose replay moves exactly that token amount.
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
## 11. LP ERC20 Share Ledger

Approve, transfer, and transferFrom are conservative ERC20 share
accounting: balances move only on transfer, total supply is
constant, finite allowances are consumed, max allowance is stable.
These calls do not touch the underlying token contracts, do not
change AMM storage, and do not move token0/token1 balances.
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

def pair_transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balancesSlot.slot s.sender).val →
    s.sender = toAddr →
      result = ContractResult.success true result.snd ∧
      result.snd.storageMap = s.storageMap

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

/-!
## 12. Initialization

Initialization is factory-only and one-shot. After the first
successful `initialize`, the pair's token identities are fixed
forever; initialization itself does not mutate reserves, LP supply,
LP accounting maps, or events.
-/

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

/-!
## 13. Views

Each public read returns the expected storage cell (or a constant)
and frames pair state on success. With the protocol fee mint
disabled, `kLast()` is the constant zero read.
-/

/-- `decimals` is a pure LP-token display constant and cannot mutate pair
state. -/
def pair_decimals_run_success_frames_state
    (s : ContractState) : Prop :=
  (decimals).run s = ContractResult.success 18 s

/-- `totalSupply` exposes exactly the LP supply cell. -/
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

/-- With the protocol fee mint disabled, `kLast()` is the constant zero read
and cannot mutate state. -/
def pair_kLast_run_success_frames_state
    (s : ContractState) : Prop :=
  (kLast).run s = ContractResult.success 0 s

/-!
## 14. Public-Call Matching

Each successful public mutating call matches its closed-world transition
and the corresponding caller-wallet step. These specs connect the
contract boundary into the closed-world model used by properties 2–13
and the caller-wallet model used by property 1.
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

/-- A successful `swap` must have passed the first economic guard: at least one
output amount is nonzero. A zero-output request fails before token transfers,
callback repayment, or the K check can matter. -/
def pair_swap_success_run_implies_nonzero_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out ≠ 0 ∨ amount1Out ≠ 0

/-- When `sync` succeeds, the lock gate and reserve-domain checks passed, so
the call follows the sync rule used by the invariant proofs. -/
def pair_sync_success_run_matches_closed_world_step_from_run
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      PairWorldStep PairWorldAction.sync
        (pairWorldFromConcreteState s)
        (pairWorldAfterSyncRun s)

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

/-!
## Closed-World Foundations

`PairWorldGood` (reserve backing + uint112 bounds +
minimum-liquidity coherence) is preserved across any finite
successful path from a good state; reachability is closed under
appending finite paths; positive-supply reachable pools remain
positive-supply with positive reserves.
-/

def pair_closed_world_path_preserves_good
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      PairWorldGood after

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

/-- Reachability packages the good-state precondition above. In the form users
care about, any nonempty reachable pool remains nonempty after any finite
successful modeled history. -/
def pair_closed_world_reachable_positive_supply_path_remains_positive
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        0 < after.totalSupply

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

/-!
## Per-Action Closed-World Facts

What each `mint`, `burn`, `swap` step does in the closed-world
model: reserves catch up to balances, the fee-adjusted K check is
honored against final post-callback balances, mint and burn obey
their pro-rata ratio rules, swap reads input from the
post-output/post-callback balance gap, and `PairWorldGood`
survives.
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

def pair_closed_world_swap_preserves_good
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      before after →
      PairWorldGood after

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

/-!
## Oracle / TWAP Update Rules

Cumulative prices follow the canonical Uniswap V2 rule. Same-block
timestamps leave them unchanged; elapsed updates with nonzero
reserves add the UQ112x112 encoded price times elapsed time; the
elapsed branch with zero elapsed time or a zero old reserve leaves
them unchanged.
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

end TamaUniV2.Spec.UniswapV2PairSpec
