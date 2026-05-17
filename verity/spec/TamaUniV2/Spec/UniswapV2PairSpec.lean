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

The file is organized as an assurance argument:

1. Views expose the intended storage fields and fee-off constants.
2. Reverts frame both pair storage and external token movement.
3. LP-token operations satisfy ERC20-style balance, allowance, supply, and event
   properties.
4. Exact guard specs pin down important revert payloads for executable runs.
5. Bridge predicates connect successful public runs to small economic
   transitions.
6. Closed-world trace specs prove invariant and economic consequences for every
   finite sequence of successful modeled actions.

The public theorem names are intentionally redundant with this prose. A reader
should be able to skim the section comments, then read each `def` as the
one-line formal version of that paragraph's claim.
-/

/-!
## Views

These specs pin each public view to the storage value or constant it is supposed
to expose. The fee-off variant deliberately fixes `kLast()` at zero.
-/

def pair_decimals_spec (result : Uint256) : Prop :=
  result = 18

def pair_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage totalSupplySlot.slot

def pair_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap balancesSlot.slot account

def pair_allowance_spec (owner spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap2 allowancesSlot.slot owner spender

def pair_factory_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr factorySlot.slot

def pair_token0_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr token0Slot.slot

def pair_token1_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr token1Slot.slot

def pair_minimumLiquidity_spec (result : Uint256) : Prop :=
  result = minimumLiquidity

def pair_getReserves_spec
    (result : Uint256 × Uint256 × Uint256) (s : ContractState) : Prop :=
  result =
    (s.storage reserve0Slot.slot,
      s.storage reserve1Slot.slot,
      s.storage blockTimestampLastSlot.slot)

def pair_price0CumulativeLast_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage price0CumulativeLastSlot.slot

def pair_price1CumulativeLast_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage price1CumulativeLastSlot.slot

def pair_kLast_spec (result : Uint256) : Prop :=
  result = 0

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

`skim` and `sync` are the smallest reserve-management entrypoints. Skim sends
only balances above cached reserves and leaves reserves unchanged. Sync accepts
the observed balances as the new reserves, but only if they fit the uint112
reserve domain. These bridge specs connect those executable calls to the
closed-world transition model used by the invariant section.
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
the elapsed time. The `sync` transition bridge above ties the public entrypoint
to the closed-world reserve transition; these claims isolate the oracle
arithmetic that every reserve-update proof should reuse.
-/

def pair_sync_oracle_same_timestamp_keeps_price_cumulatives
    (s : ContractState) : Prop :=
  timestamp32 s = s.storage blockTimestampLastSlot.slot →
    oraclePrice0CumulativeAfterSync s =
      s.storage price0CumulativeLastSlot.slot ∧
    oraclePrice1CumulativeAfterSync s =
      s.storage price1CumulativeLastSlot.slot

def pair_sync_oracle_elapsed_updates_price_cumulatives
    (s : ContractState) : Prop :=
  (timestamp32 s != s.storage blockTimestampLastSlot.slot) = true →
    oracleElapsed s > 0 →
      s.storage reserve0Slot.slot > 0 →
        s.storage reserve1Slot.slot > 0 →
          oraclePrice0CumulativeAfterSync s =
            oraclePrice0CumulativeAfterElapsed s ∧
          oraclePrice1CumulativeAfterSync s =
            oraclePrice1CumulativeAfterElapsed s

/--
Entering the timestamp-change branch is not enough to move the oracle. If the
elapsed-price branch is inactive because elapsed time or either old reserve is
zero, both cumulative prices remain unchanged.
-/
def pair_sync_oracle_inactive_elapsed_keeps_price_cumulatives
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

/-!
## Mint, Burn, And Swap Bridges

The closed-world model below is where the main invariant and economic theorems
live. These bridge specs are the narrow doorway from executable public calls to
that model: if a real call succeeds and exposes the expected arithmetic facts,
then the corresponding `PairWorldStep` is available. The public specs stay
short on purpose. They do not copy the whole function body; they connect one
entrypoint to one modeled economic transition.
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
The remaining bridge specs are deliberately small. They do not restate the full
function bodies. They say that once the arithmetic facts exposed by a successful
public call are available, the concrete formulas refine the closed-world action
used by the invariant section below.
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
                        (s.storage reserve0Slot.slot).val *
                            (s.storage reserve1Slot.slot).val ≤
                          balance0Now.val * balance1Now.val →
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
  mint/burn pro-rata discipline, swap fee-adjusted K and raw-K nondecrease,
  surplus-only skim, sync-to-balance behavior, and LP-supply preservation by
  non-liquidity actions.
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

def pair_closed_world_supply_changes_only_on_mint_or_burn
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    after.totalSupply ≠ before.totalSupply →
      (∃ amount0 amount1 liquidity,
        action = PairWorldAction.mint amount0 amount1 liquidity) ∨
      (∃ amount0 amount1 liquidity,
        action = PairWorldAction.burn amount0 amount1 liquidity)

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

end TamaUniV2.Spec.UniswapV2PairSpec
