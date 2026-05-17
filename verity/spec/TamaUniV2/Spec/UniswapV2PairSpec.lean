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
Behavior specs for the production-style Uniswap v2 pair.

The executable contract uses external-call modules for token transfers, token
balances, pair creation, and flash callbacks. Specs follow Tamago's ERC4626
style: local storage/accounting obligations are proved directly, while
external-token movement is connected to concrete execution through pair-local
ghost transfer traces. The remaining assumptions stay at actual external
boundaries such as ERC20 calls, callbacks, and CREATE2 deployment.

The file is organized as an assurance argument rather than a checklist. The
reader should be able to answer three questions as the sections progress:

* Correctness: do public calls and views agree with the intended Uniswap V2
  fee-off accounting rules?
* Security: can any finite sequence of successful calls violate reserve backing,
  bypass the lock, weaken K except through proportional LP redemption, or create
  spot-price profit?
* Completeness: do the specs cover the behaviors users rely on at the Pair
  boundary without specifying proof-only helpers or unsupported APIs?

The argument proceeds in layers:

1. Identify the contract state that outside users can observe: reserves,
   cumulative prices, token addresses, LP balances, allowances, and the fee-off
   `kLast` constant.
2. Separate local Pair state from ERC20 state. Reverts must frame both, while
   successful token movement is represented by explicit trace facts at the ECM
   boundary.
3. Prove the LP token behaves like a conservative ERC20 share ledger before
   considering AMM economics.
4. Pin down security-relevant executable guards: the reentrancy lock, reserve
   bounds, under-backed `skim` failures, and early swap/factory
   failures all have exact revert payloads and original-state frames.
5. Bridge successful public entrypoints into small ghost transitions. These are
   intentionally not whole-function summaries; they are the doorway from
   executable code into the mathematical model.
6. Prove the model-level theorem stack over every finite successful history:
   reserve backing, uint112 bounds, minimum-liquidity locking, K behavior,
   LP-share discipline, and same-supply no-profit.

Read from top to bottom, the argument is: the executable boundary admits only
well-framed failures and well-shaped successful transitions; the transition
model preserves the invariants; therefore every finite closed-world history of
the fee-off pair preserves the safety and economic properties users rely on.
This is also the rule for future additions: add a short proposition when it
closes a visible correctness or security step in that argument, not merely
because a proof helper exists.

The public theorem names are intentionally redundant with this prose. A reader
should be able to skim the section comments, then read each `def` as the
one-line formal version of that paragraph's claim.
-/

/-!
## Views

These specs pin each public view to the storage value or constant it is supposed
to expose. The fee-off variant deliberately fixes `kLast()` at zero. The
run-level facts are not API-parity checks; they are the observable-state layer
of the assurance argument. Routers, LPs, and proofs below can trust these reads
only because the actual executable view returns the expected value and frames
pair state.
-/

def pair_decimals_spec (result : Uint256) : Prop :=
  result = 18

/-- `decimals` is a pure LP-token display constant and cannot mutate pair
state. -/
def pair_decimals_run_success_frames_state
    (s : ContractState) : Prop :=
  (decimals).run s = ContractResult.success 18 s

def pair_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage totalSupplySlot.slot

/-- `totalSupply` exposes exactly the LP supply cell. It is the public read that
anchors every LP-supply and no-profit theorem below. -/
def pair_totalSupply_run_success_frames_state
    (s : ContractState) : Prop :=
  (totalSupply).run s =
    ContractResult.success (s.storage totalSupplySlot.slot) s

def pair_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap balancesSlot.slot account

/-- `balanceOf` exposes exactly one LP balance cell and has no side effects. -/
def pair_balanceOf_run_success_frames_state
    (account : Address) (s : ContractState) : Prop :=
  (balanceOf account).run s =
    ContractResult.success (s.storageMap balancesSlot.slot account) s

def pair_allowance_spec (owner spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap2 allowancesSlot.slot owner spender

/-- `allowance` exposes exactly one delegated-LP-spend cell and has no side
effects. -/
def pair_allowance_run_success_frames_state
    (owner spender : Address) (s : ContractState) : Prop :=
  (allowance owner spender).run s =
    ContractResult.success (s.storageMap2 allowancesSlot.slot owner spender) s

def pair_factory_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr factorySlot.slot

/-- `factory` exposes the immutable creator/initializer authority stored for
the pair and has no side effects. -/
def pair_factory_run_success_frames_state
    (s : ContractState) : Prop :=
  (factory).run s =
    ContractResult.success (s.storageAddr factorySlot.slot) s

def pair_token0_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr token0Slot.slot

/-- `token0` exposes the first market token identity recorded at initialization
and has no side effects. -/
def pair_token0_run_success_frames_state
    (s : ContractState) : Prop :=
  (token0).run s =
    ContractResult.success (s.storageAddr token0Slot.slot) s

def pair_token1_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr token1Slot.slot

/-- `token1` exposes the second market token identity recorded at initialization
and has no side effects. -/
def pair_token1_run_success_frames_state
    (s : ContractState) : Prop :=
  (token1).run s =
    ContractResult.success (s.storageAddr token1Slot.slot) s

def pair_minimumLiquidity_spec (result : Uint256) : Prop :=
  result = minimumLiquidity

/-- `MINIMUM_LIQUIDITY` exposes the permanent lock constant used by the
finite-history liquidity-lock theorems. -/
def pair_minimumLiquidity_run_success_frames_state
    (s : ContractState) : Prop :=
  (MINIMUM_LIQUIDITY).run s =
    ContractResult.success minimumLiquidity s

def pair_getReserves_spec
    (result : Uint256 × Uint256 × Uint256) (s : ContractState) : Prop :=
  result =
    (s.storage reserve0Slot.slot,
      s.storage reserve1Slot.slot,
      s.storage blockTimestampLastSlot.slot)

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

def pair_price0CumulativeLast_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage price0CumulativeLastSlot.slot

/-- `price0CumulativeLast` exposes exactly the cached token0 TWAP accumulator
and has no side effects. -/
def pair_price0CumulativeLast_run_success_frames_state
    (s : ContractState) : Prop :=
  (price0CumulativeLast).run s =
    ContractResult.success (s.storage price0CumulativeLastSlot.slot) s

def pair_price1CumulativeLast_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage price1CumulativeLastSlot.slot

/-- `price1CumulativeLast` exposes exactly the cached token1 TWAP accumulator
and has no side effects. -/
def pair_price1CumulativeLast_run_success_frames_state
    (s : ContractState) : Prop :=
  (price1CumulativeLast).run s =
    ContractResult.success (s.storage price1CumulativeLastSlot.slot) s

def pair_kLast_spec (result : Uint256) : Prop :=
  result = 0

/-- The fee-off Pair never uses protocol-fee accounting, so `kLast()` is the
constant zero read and cannot mutate state. -/
def pair_kLast_run_success_frames_state
    (s : ContractState) : Prop :=
  (kLast).run s = ContractResult.success 0 s

/-!
## ERC20 Boundary Traces

The pair can only affect token balances through ERC20 transfer ECMs. The
`pair_safeTransfer_traces_token_transfer` spec records a ghost event for each
successful token transfer so later frame and transition specs can reason about
token movement without pretending the ERC20 contract is local storage.
-/

def pair_safeTransfer_traces_token_transfer
    (token toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  result = ContractResult.success 1 result.snd ∧
  hasPairSafeTransferTrace token s.thisAddress toAddr amount result.snd

/--
The token-transfer trace model has one job: when a pair-local ERC20 transfer
event is replayed, it moves exactly that token amount from the pair-side sender
to the recipient in the ghost token-balance world. Later executable specs for
`skim`, `burn`, and `swap` can cite this fact instead of re-proving event
decoding each time.
-/
def pair_safeTransfer_event_replay_moves_token_balance
    (token fromAddr toAddr : Address) (amount : Uint256)
    (pre : PairTokenBalances) : Prop :=
  pairTokenWorldAfterEvent pre
      (TamaUniV2.pairTokenSafeTransferEvent token fromAddr toAddr amount) =
    pairTokenWorldAfterTransfer pre token fromAddr toAddr amount

/-!
## Revert Frames

On revert, Verity restores the pair state and emits no successful transfer
trace. These specs keep ERC20 balance accounting separate from the pair's local
storage rules: a caller supplies the token-balance world obtained by replaying
the call's transfer events, and the spec says reverted pair calls leave that
world unchanged. The pair-local frame specs then state the matching storage and
event-log atomicity for each mutating Pair entrypoint.
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
LP-token bookkeeping never calls the underlying ERC20 tokens. The LP `Transfer`
and `Approval` events are local share-ledger events, not token0/token1
movements, so replaying the pair-local ERC20 transfer trace across these calls
must leave the token-balance world unchanged.
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
## Local Entry Points

This layer is about the pair's local authority and LP-token accounting before
we talk about AMM economics.

The reader should be able to check three things from this section. First,
initialization is factory-only and one-shot, so the pair's token identity cannot
be changed after creation. Second, LP-token approval and transfer behavior is
ordinary ERC20 accounting: balances move only on transfer, total supply does not
move, finite allowances are consumed, max allowance is stable, and events are
present. Third, the result-parameter guard specs give reusable branch facts for
the exact-run obligations that follow.
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
storage. This is the executable counterpart of the model-level fact that share
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
## Exact Guard Runs

This section pins the contract's failure boundaries to exact executable runs.
Each statement has the same shape: once the hypotheses establish that earlier
guards have either failed or passed in the intended order, the actual public
entrypoint returns the canonical revert string and the pre-call state.

These are intentionally branch facts rather than full function summaries. They
are useful because guard order is security-relevant: before any ERC20 transfer,
callback, reserve update, or LP accounting write can become durable, the
matching public entrypoint must fail with the expected reason and frame.

The section should stay narrow. If proving a later guard requires unfolding the
whole function tail, the right move is to factor a proof-local prefix adapter
first, then expose a short public guard fact here.
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
## Skim And Sync Bridges

`skim` and `sync` are the direct calls for reconciling token balances with
cached reserves. Skim sends only balances above cached reserves and leaves
reserves unchanged. Sync accepts the observed balances as the new reserves, but
only if they fit the uint112 reserve domain. These bridge specs connect those
executable calls to the closed-world transition model used by the invariant
section.
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

def pair_skim_run_success_refines_closed_world
    (toAddr : Address) (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    s.storage reserve0Slot.slot ≤ observedBalance0 s →
      s.storage reserve1Slot.slot ≤ observedBalance1 s →
        match (skim toAddr).run s with
        | ContractResult.success () _post =>
            PairWorldStep PairWorldAction.skim
              (pairWorldFromConcreteState s)
              (pairWorldAfterSkimRun s)
        | ContractResult.revert _ _ => False

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

def pair_sync_expected_refines_closed_world
    (s : ContractState) : Prop :=
  observedBalance0 s ≤ maxUint112 →
    observedBalance1 s ≤ maxUint112 →
      PairWorldStep PairWorldAction.sync
        (pairWorldFromConcreteState s)
        (pairWorldAfterSyncRun s)

def pair_sync_success_run_refines_closed_world
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      observedBalance0 s ≤ maxUint112 →
        observedBalance1 s ≤ maxUint112 →
          PairWorldStep PairWorldAction.sync
            (pairWorldFromConcreteState s)
            (pairWorldAfterSyncRun s)

/-!
Oracle/TWAP arithmetic for reserve updates.

The pair's cumulative prices are not a separate asset ledger; they are an
accounting consequence of a reserve update. These obligations pin that rule in
small pieces. If the 32-bit timestamp has not advanced, the cumulative prices
are unchanged. If time has advanced and both old reserves are nonzero, each
cumulative price increases by the canonical Uniswap V2 fixed-point price times
the elapsed time. If the timestamp branch is entered but elapsed time or either
old reserve is zero, cumulatives stay unchanged.

The arithmetic is contract-level reserve-update behavior, shared by mint, burn,
swap, and sync. The formulas are factored outside the contract source so the
spec can discuss the rule directly without adding public or internal Pair
functions for proof convenience. The first three specs state the generic rule;
the `sync`-named obligations keep the simplest public-entrypoint bridge visible
until the mint/burn/swap reserve-update paths are connected to the same facts.
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
reserves are nonzero, the pair adds exactly the canonical fixed-point
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

/-- `sync` is the direct public bridge to the generic same-timestamp reserve
update rule. -/
def pair_sync_oracle_same_timestamp_keeps_price_cumulatives
    (s : ContractState) : Prop :=
  pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives s

/-- `sync` is the direct public bridge to the generic active-elapsed reserve
update rule. -/
def pair_sync_oracle_elapsed_updates_price_cumulatives
    (s : ContractState) : Prop :=
  pair_reserve_update_oracle_elapsed_updates_price_cumulatives s

/-- `sync` is the direct public bridge to the generic inactive-elapsed reserve
update rule. -/
def pair_sync_oracle_inactive_elapsed_keeps_price_cumulatives
    (s : ContractState) : Prop :=
  pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives s

/-!
## Flash-Swap Boundary

Flash swaps are verify-after swaps: the pair may optimistically send output,
optionally call the recipient, then read final token balances and enforce the K
rule against the balances after any callback-visible repayment. The callback
itself is an external boundary, so the Lean source model does not pretend to
execute recipient code. The spec suite therefore separates two facts:

* The compiled callback ECM is gated by nonempty calldata, matching canonical
  Uniswap V2 flash-swap behavior.
* The closed-world swap transition below charges the K check against final
  balances, not against balances before the recipient has a chance to repay.
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
## Mint, Burn, And Swap Bridges

The closed-world model below is where the main invariant and economic theorems
live. These bridge specs are the narrow doorway from executable public calls to
that model: if a real call succeeds and exposes the expected arithmetic facts,
then the corresponding `PairWorldStep` is available. The public specs stay
short on purpose. They do not copy the whole function body; they connect one
entrypoint to one modeled economic transition.

These are simulation links, not substitutes for the invariant section. A bridge
only says "this successful run is one of the modeled actions." The reason that
action is safe comes later, where the model proves reserve backing, K behavior,
LP-share discipline, and no-profit consequences across arbitrary finite
histories.
-/

def pair_mint_first_expected_refines_closed_world
    (toAddr : Address) (s : ContractState) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  s.storage unlockedSlot.slot = 1 →
    s.storage totalSupplySlot.slot = 0 →
      observedBalance0 s ≤ maxUint112 →
        observedBalance1 s ≤ maxUint112 →
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

def pair_mint_first_success_run_refines_closed_world
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage unlockedSlot.slot = 1 →
        s.storage totalSupplySlot.slot = 0 →
          observedBalance0 s ≤ maxUint112 →
            observedBalance1 s ≤ maxUint112 →
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

/-!
The remaining bridge specs keep the same shape. Each one is a one-step
simulation fact: a successful public call, together with the arithmetic facts
that the executable path computes, corresponds to the appropriate ghost action.
The economic content remains in the short invariants below, where those actions
are composed over paths.
-/

def pair_mint_subsequent_expected_refines_closed_world
    (s : ContractState) (liquidity : Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  0 < (s.storage totalSupplySlot.slot).val →
    s.storage reserve0Slot.slot > 0 →
      s.storage reserve1Slot.slot > 0 →
        observedBalance0 s ≤ maxUint112 →
          observedBalance1 s ≤ maxUint112 →
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

def pair_mint_subsequent_success_run_refines_closed_world
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      pair_mint_subsequent_expected_refines_closed_world s liquidity

def pair_burn_expected_refines_closed_world
    (s : ContractState) : Prop :=
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
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

def pair_burn_success_run_refines_closed_world
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      pair_burn_expected_refines_closed_world s

def pair_swap_expected_refines_closed_world
    (amount0Out amount1Out balance0Now balance1Now : Uint256)
    (s : ContractState) : Prop :=
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  (amount0Out > 0 ∨ amount1Out > 0) →
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

def pair_swap_success_run_refines_closed_world
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      pair_swap_expected_refines_closed_world
        amount0Out amount1Out balance0Now balance1Now s

/-!
## Closed-World Economic Invariants

These specs mirror Tamago's ERC4626 trace-wide style. They quantify over every
finite successful transition sequence in `PairWorldReachable`; external ERC20
movement is represented by explicit mint/burn/swap/donate/skim/sync steps rather
than by new assumptions about Verity ECM internals.

The logical flow is intentionally compositional:

* `PairWorldGood` says reserves are backed by token balances, reserves fit in
  uint112, and the permanently locked minimum liquidity is coherent with supply.
* One-step preservation plus induction gives the same facts for every reachable
  finite trace.
* Per-action specs then expose the pieces of Uniswap V2 economics that matter:
  mint/burn pro-rata discipline, swap fee-adjusted K with derived raw-K
  nondecrease, surplus-only skim, sync-to-balance behavior, and LP-supply
  preservation by non-liquidity actions.
* LP-normalized K composes across arbitrary finite paths from positive-supply
  states. If such a path begins and ends with the same LP supply, the
  normalization cancels, raw K cannot fall, and the final pool has no
  spot-price profit at the initial price. The older no-burn theorem remains as
  a simpler corollary for traces without LP redemption.

Properties specified:

* Every successful modeled action preserves the core Pair invariant, and every
  finite modeled path from a good state preserves it too.
* Cached reserves remain backed by token balances and inside the uint112 range.
* LP supply is coherent with the permanently locked minimum liquidity; only
  mint and burn can change that supply.
* Swaps satisfy the fee-adjusted K check and cannot decrease raw cached K.
* Any one-step raw K decrease must be a burn. Across paths, LP-normalized K
  cannot decrease from a good positive-supply state, and reachable same-supply
  paths cannot create value at the initial spot price.

Security conclusions:

* The pair cannot report reserves that exceed modeled token backing in any
  closed-world finite trace.
* Reentrancy-free non-burn traces, including swaps, donations, skims, and syncs,
  cannot reduce pool K. More generally, same-LP-supply finite traces from
  reachable positive-supply states cannot manufacture spot-price profit without
  an external gift.
* Liquidity creation and redemption are isolated to mint/burn, where the
  separate ratio specs bound LP tokens against pro-rata token movement.

This section is the proof spine. Individual entrypoint facts tell us what one
call can do; these invariants tell us what no finite sequence of calls can do.
That is where the contract-level security claims live.
-/

/-!
### 1. Reachability Invariants

The first layer is deliberately boring: define the states that can exist and
show that the definition is stable under both one step and arbitrary finite
paths. This is the base of the argument. Every later economic theorem is only
useful if it applies to all successful histories, not just to hand-picked
examples.
-/

def pair_closed_world_step_preserves_good
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      PairWorldGood after

def pair_closed_world_path_preserves_good
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      PairWorldGood after

def pair_closed_world_reachable_good
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    PairWorldGood w

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

/-- Token-side no-drain invariant. The positive-reserve theorem says cached
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
### 2. Concrete-State Projections

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
### 3. LP Supply Discipline

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

/-- The finite-history version of permanent locked liquidity. Starting from a
good pool model, no successful sequence can unwind the locked floor. -/
def pair_closed_world_path_locked_liquidity_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
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
router-visible reserves. If either cached reserve changes in one modeled step,
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

/-- Finite-history reserve isolation. A history made only of LP bookkeeping,
direct donations, and skim may change LP ownership or token balances, but it
never changes the cached reserves. This is the path-level form of the
reserve-change classifier above, and it is the invariant a router-facing reader
can cite when reasoning that cached price state is stable unless a reserve
update action actually occurs. -/
def pair_closed_world_no_reserve_update_path_preserves_reserves
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoReserveUpdate before after →
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1

/-- Economic corollary of finite-history reserve isolation. If no mint, burn,
swap, or sync occurs, the cached reserve product and reserve-denominated spot
value are unchanged. This deliberately talks about cached reserves rather than
actual token balances: direct donations and `skim` may change surplus, but they
do not change the reserve price state. -/
def pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoReserveUpdate before after →
    PairWorldK after = PairWorldK before ∧
    PairWorldSpotValueNum before after =
      PairWorldSpotValueNum before before

/-- The one-step LP-supply firewall. A successful modeled action that is not
mint and not burn cannot change total LP supply or the permanently locked
liquidity amount. This is the local fact that the finite-history theorem below
iterates. -/
def pair_closed_world_non_liquidity_step_preserves_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      after.totalSupply = before.totalSupply ∧
      after.lockedLiquidity = before.lockedLiquidity

/-- The finite-history version of the LP supply firewall. If a successful
modeled path contains no mint and no burn, then it cannot change total LP supply
or the permanently locked liquidity amount. -/
def pair_closed_world_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoMintBurn before after →
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

/-- Reachable-state form of the same supply firewall. Starting from any
reachable pool, every finite successful history made only of share transfers,
approvals, donations, swaps, skim, and sync preserves LP supply exactly. -/
def pair_closed_world_reachable_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoMintBurn before after →
      after.totalSupply = before.totalSupply ∧
      after.lockedLiquidity = before.lockedLiquidity

/-- The directional LP-supply firewall. A single successful modeled action that
is not burn cannot destroy LP supply. Mint may create new shares and ordinary
pool operations may leave supply unchanged, but redemption is the only direction
that can move supply downward. -/
def pair_closed_world_non_burn_step_never_decreases_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      before.totalSupply ≤ after.totalSupply

/-- The finite-history version of the same supply direction fact. Along any
successful modeled history with no burn step, total LP supply cannot decrease.
This is the trace-level statement that "LP redemption requires burn." -/
def pair_closed_world_no_burn_path_never_decreases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoBurn before after →
    before.totalSupply ≤ after.totalSupply

/-- Reader-facing reachable form: from any reachable pool state, every finite
successful no-burn history preserves or increases LP supply. This pairs with
the no-burn K theorem below: without LP redemption, neither supply nor cached K
can move in the extraction direction. -/
def pair_closed_world_reachable_no_burn_path_never_decreases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoBurn before after →
      before.totalSupply ≤ after.totalSupply

/-- The other direction of LP-supply isolation. A single successful modeled
action that is not mint cannot create LP supply. Burn may redeem shares and
ordinary pool operations may leave supply unchanged, but issuance is isolated to
mint. -/
def pair_closed_world_non_mint_step_never_increases_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
      after.totalSupply ≤ before.totalSupply

/-- The finite-history version of LP issuance isolation. Along any successful
modeled history with no mint step, total LP supply cannot increase. This is the
trace-level statement that new LP claims require mint. -/
def pair_closed_world_no_mint_path_never_increases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoMint before after →
    after.totalSupply ≤ before.totalSupply

/-- Reader-facing reachable form: from any reachable pool state, every finite
successful no-mint history preserves or decreases LP supply. Together with the
no-burn theorem, this pins LP supply movement to the two liquidity entrypoints:
mint creates shares and burn redeems them. -/
def pair_closed_world_reachable_no_mint_path_never_increases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    PairWorldPathNoMint before after →
      after.totalSupply ≤ before.totalSupply

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

/-- LP token bookkeeping is only bookkeeping. Across any finite sequence made
solely of approvals, direct LP transfers, and delegated LP transfers, the AMM
state is unchanged: token balances, cached reserves, total LP supply, and the
permanently locked liquidity amount all end exactly where they started. This is
the trace-level version of the ERC20-share claim above, and it is what lets the
economic sections ignore pure share movements as price- or reserve-changing
actions. -/
def pair_closed_world_share_bookkeeping_path_preserves_pool_state
    (before after : PairWorldState) : Prop :=
  PairWorldPathShareBookkeeping before after →
    after.balance0 = before.balance0 ∧
    after.balance1 = before.balance1 ∧
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1 ∧
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

/-- Economic corollary of the share-bookkeeping invariant. If a history only
moves LP approvals or LP balances between accounts, then it cannot change the
pool's cached K, reserve-denominated spot value, or actual-token-balance spot
value. Pure ownership bookkeeping is therefore not an AMM profit path. -/
def pair_closed_world_share_bookkeeping_path_preserves_k_and_value
    (before after : PairWorldState) : Prop :=
  PairWorldPathShareBookkeeping before after →
    PairWorldK after = PairWorldK before ∧
    PairWorldSpotValueNum before after =
      PairWorldSpotValueNum before before ∧
    PairWorldBalanceSpotValueNum before after =
      PairWorldBalanceSpotValueNum before before

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

def pair_closed_world_burn_reduces_supply_by_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    after.totalSupply = before.totalSupply - liquidity

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

/-!
### 4. Token Inflow Without Accounting

Anyone may transfer tokens directly into a pair. That donation must not silently
alter cached reserves, LP supply, or cached K. The only way to account for the
extra token balance is through later mint/swap/sync behavior.

This is the Uniswap V2 analogue of Tamago's ERC4626 donation-surplus layer.
The model tracks reserve surplus as `balance - reserve` on each token side.
Direct donations are allowed to create that surplus, but histories with no
donation step cannot manufacture more of it. That is the missing premise behind
the actual-token-balance no-profit theorem: `skim` may remove an external gift,
but the pair cannot create that gift internally.
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

/-- No non-donation action can create new reserve surplus. Share bookkeeping
preserves any existing surplus; mint, burn, swap, skim, and sync either account
for balances as reserves or remove surplus; none of them can increase
`balance - reserve` without an explicit external token donation. -/
def pair_closed_world_non_donation_step_never_increases_surplus
    (action : PairWorldAction)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1, action ≠ PairWorldAction.donate amount0 amount1) →
        PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
        PairWorldSurplus1 after ≤ PairWorldSurplus1 before

/-- Trace-level surplus isolation. Across any finite successful history with no
direct donation step, reserve surplus on either token side cannot increase. -/
def pair_closed_world_no_donation_path_never_increases_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoDonation before after →
      PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
      PairWorldSurplus1 after ≤ PairWorldSurplus1 before

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
### 6. Swap Safety

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
economic argument often cites raw reserve-product monotonicity. This theorem is
the bridge between those statements: once a swap's cached reserves are the final
balances, the fee-adjusted K check alone implies raw cached K cannot decrease.
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

/-!
### 7. Sequence-Level Economic Consequences

The reserve-product facts above compose across finite traces. For no-burn
histories, K never decreases. If such a history also begins and ends with the
same LP supply, then the pool's final reserves are worth at least the initial
pool value at the initial spot price. In a closed world with no external gift to
the caller, that is exactly the condition needed to rule out spot-price profit.

The stronger LP-normalized theorem removes the no-burn restriction. Mint and
burn may change raw K, but valid pro-rata mint/burn transitions cannot decrease
`K / totalSupply^2` while LP supply is positive. Therefore any finite path that
starts and ends with the same positive LP supply cannot reduce K, even if it
contains mint/burn round trips.

The specs below are intentionally layered. First, one valid action cannot reduce
LP-normalized K. Second, the same fact composes across arbitrary finite paths.
Third, if the path starts and ends with the same positive LP supply, the
normalization cancels and raw K itself cannot fall. Finally, the usual
constant-product geometry converts that K fact into a spot-value no-profit
statement.

Properties specified:
* Every valid action preserves or improves reserve product per squared LP supply
  once the pool is nonempty.
* Every finite successful history from a reachable nonempty pool preserves that
  LP-normalized backing.
* If a finite history returns to the same LP supply, the final pool value at the
  initial spot price is at least the starting value.
* A raw K decrease is classified as liquidity redemption: without a burn step,
  K cannot decrease.

Security conclusions:
* Swap-only and no-burn histories cannot drain the pool by weakening K.
* Mint/burn round trips do not create a hidden extraction path, because the
  LP-normalized invariant survives the round trip and same supply cancels the
  normalization.
* The no-profit theorem is pool-side and closed-world: profit would have to
  appear as missing spot value from the pool unless it comes from an external
  gift outside the model.
-/

/- One valid closed-world transition cannot dilute existing LP shares: measured
as reserve product per squared LP supply, the pool is at least as strong after
the step as before it. -/
def pair_closed_world_step_k_per_supply_never_decreases
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep action before after →
        PairWorldKPerSupplyNondecreasing before after

/- The one-step dilution bound composes over every finite path. This is the
main sequence invariant: no combination of transfers, donations, mint, burn,
swap, skim, or sync can reduce LP-normalized K from a good positive-supply
state. -/
def pair_closed_world_path_k_per_supply_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        PairWorldKPerSupplyNondecreasing before after

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

/- If a finite path returns to the same LP supply, LP normalization cancels.
The pool's raw reserve product therefore cannot be lower than where it began. -/
def pair_closed_world_same_supply_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldK before ≤ PairWorldK after

/- Constant-product arithmetic: once raw K is known not to fall, the final
reserves cannot be worth less than the initial reserves at the initial spot
price. This lemma is kept parameterized by the K fact so other sequence
arguments can reuse the geometric conversion directly. -/
def pair_closed_world_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldPath before after →
    PairWorldGood before →
      before.totalSupply = after.totalSupply →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldK before ≤ PairWorldK after →
              PairWorldNoSpotProfit before after

/- The complete same-supply no-profit theorem for the closed-world pool model:
from any good positive-supply state with nonzero reserves, every finite path
that ends with the same LP supply has no spot-price profit. This version allows
mint/burn round trips because it relies on LP-normalized K rather than the older
no-burn K theorem. -/
def pair_closed_world_positive_supply_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
            0 < before.reserve1 →
              PairWorldNoSpotProfit before after

/- The reachable-state version of the same-supply K theorem is the one most
callers should cite: from any actually reachable nonempty pool, any finite
successful sequence that returns LP supply to its starting value cannot reduce
raw reserve product. -/
def pair_closed_world_reachable_same_supply_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldK before ≤ PairWorldK after

/- The reachable-state no-profit theorem states the economic conclusion in the
language of the contract user. Starting from any reachable nonempty pool with a
defined spot price, any finite successful sequence that leaves LP supply
unchanged leaves the pool worth at least as much at the initial spot price.
Without an external gift to the caller, that rules out spot-price profit. -/
def pair_closed_world_reachable_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
            0 < before.reserve1 →
              PairWorldNoSpotProfit before after

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

/-- Caller-facing form of the same theorem. `PairWorld` tracks pool-side token
balances and LP supply, not arbitrary external wallet balances, so the
closed-world no-profit claim is stated as absence of pool value extraction: if a
finite successful history returns LP supply to its starting value, the final pool
cannot be worth less at the initial spot price. Any positive closed-world caller
profit would have to appear as that missing pool value; external gifts are
outside this theorem's closed-world premise. -/
def pair_closed_world_reachable_same_supply_path_no_spot_value_extraction
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

/-- Common operational zero-surplus no-extraction theorem. Histories with no
mint and no burn preserve LP supply by the supply firewall, so the same
actual-balance no-extraction conclusion applies without restating a same-supply
premise. This is the most direct closed-world expression of "ordinary pair
operation cannot profitably drain actual token balances from a clean starting
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

/-- Non-liquidity histories are the common operational case: swaps, surplus
management, donations, and LP-token bookkeeping, but no mint and no burn. The
supply firewall above makes these histories same-supply histories, so the
same no-extraction conclusion applies directly. -/
def pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPathNoMintBurn before after →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldSpotValueNum before before ≤
              PairWorldSpotValueNum before after

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

def pair_closed_world_non_burn_step_never_decreases_k
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
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

def pair_closed_world_no_burn_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoBurn before after →
      PairWorldK before ≤ PairWorldK after

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

def pair_closed_world_no_burn_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoBurn before after →
      before.totalSupply = after.totalSupply →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldNoSpotProfit before after

/-!
### 8. Surplus And Reserve Synchronization

`skim` removes only surplus above cached reserves. `sync` accepts the currently
observed token balances as reserves, subject to uint112 bounds. Neither action
can mint or burn LP supply, and neither can decrease K when started from a
reserve-backed state.

Properties specified:
* Skim can remove excess balances, but it cannot change cached reserves.
* Sync can change cached reserves, but only to the observed balances and only
  inside the uint112 reserve domain.
* Both actions preserve LP supply and the permanently locked liquidity amount.

Security conclusions:
* Surplus removal cannot rewrite the pool's price state.
* Reserve synchronization cannot manufacture LP tokens or weaken K from a good
  state; it only makes cached reserves catch up to backed balances.
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
def pair_closed_world_balanced_reserve_management_preserves_pool
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

/-- The same no-change claim holds for any finite history made only of `skim`
and `sync`. Starting from a good pool with no excess balances above cached
reserves, repeated cleanup calls preserve token balances, cached reserves, LP
supply, and the permanent liquidity lock exactly. -/
def pair_closed_world_balanced_reserve_management_path_preserves_pool
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathReserveManagement before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity

/-- LP approvals/transfers only move LP-token claims, not pool assets. Combining
those bookkeeping actions with `skim`/`sync` on a pool that has no excess token
balances therefore preserves the pool exactly across any finite history made
only of `approve`, `transfer`, `transferFrom`, `skim`, and `sync`. -/
def pair_closed_world_balanced_maintenance_path_preserves_pool
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathMaintenance before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity

/-- The cached reserve product is unchanged by the same histories. Since token
balances and cached reserves are unchanged, the pool's `reserve0 * reserve1`
value is unchanged too; this lets economic arguments cite the K consequence
directly. -/
def pair_closed_world_balanced_maintenance_path_preserves_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathMaintenance before after →
          PairWorldK after = PairWorldK before

/-- Clean pools stay clean under LP bookkeeping plus `skim`/`sync`. Those
actions cannot create new excess token balances above cached reserves when none
existed at the start. -/
def pair_closed_world_balanced_maintenance_path_preserves_zero_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathMaintenance before after →
          PairWorldSurplus0 after = 0 ∧
          PairWorldSurplus1 after = 0

/-- Economic reading of the no-change theorem above. If a clean balanced pool
only goes through LP approval/transfer bookkeeping plus `skim`/`sync`, the
actual token balances held by the pool have exactly the same spot-priced value
at the end as they had at the start. This is the concise no-extraction
consequence of the stronger state-preservation theorem above. -/
def pair_closed_world_balanced_maintenance_path_preserves_token_balance_value
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathMaintenance before after →
          PairWorldBalanceSpotValueNum before after =
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

end TamaUniV2.Spec.UniswapV2PairSpec
