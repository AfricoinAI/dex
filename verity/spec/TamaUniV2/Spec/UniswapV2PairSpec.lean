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

These properties are executable Lean obligations over the source model.
Entrypoints that read token balances or make callbacks are proved by combining
pair-local storage facts, explicit external-boundary assumptions, and the
closed-world economic invariants below.

Initialization is one-shot and factory-only. LP-token approvals and transfers
then follow the usual ERC20-style rules: approve only writes allowance, transfer
and transferFrom conserve total supply, finite allowances are spent, infinite
allowances remain infinite, and successful movements emit Transfer/Approval.
-/

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

The public obligation mentions the actual entrypoint run result, not a
separately supplied result value. The older `result`-parameter specs above are
kept as small reusable adapters.

These are branch-specific: each spec states that, once earlier guards required
by its hypotheses have passed, the named guard produces the exact canonical
revert payload and original-state frame.
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
* The same-supply no-profit theorem is the sequence-level consequence: if a
  finite path begins and ends with the same LP supply and does not decrease K,
  then the pool state has no positive profit at the initial spot price.

Properties specified:

* Every successful modeled action preserves the core Pair invariant, and every
  finite modeled path from a good state preserves it too.
* Cached reserves remain backed by token balances and inside the uint112 range.
* LP supply is coherent with the permanently locked minimum liquidity; only
  mint and burn can change that supply.
* Swaps satisfy the fee-adjusted K check and cannot decrease raw cached K.
* Any finite path without a burn cannot decrease cached K. Combined with the
  spot-value lemma, a same-LP-supply no-burn path cannot create value at the
  initial spot price.

Security conclusions:

* The pair cannot report reserves that exceed modeled token backing in any
  closed-world finite trace.
* Reentrancy-free non-burn traces, including swaps, donations, skims, and syncs,
  cannot reduce pool K or manufacture spot-price profit for a caller without an
  external gift.
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

def pair_closed_world_supply_changes_only_on_mint_or_burn
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    after.totalSupply ≠ before.totalSupply →
      (∃ amount0 amount1 liquidity,
        action = PairWorldAction.mint amount0 amount1 liquidity) ∨
      (∃ amount0 amount1 liquidity,
        action = PairWorldAction.burn amount0 amount1 liquidity)

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

def pair_closed_world_burn_reduces_supply_by_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    after.totalSupply = before.totalSupply - liquidity

def pair_closed_world_burn_cannot_redeem_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    before.lockedLiquidity ≤ after.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

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
-/

def pair_closed_world_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldPath before after →
    PairWorldGood before →
      before.totalSupply = after.totalSupply →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldK before ≤ PairWorldK after →
              PairWorldNoSpotProfit before after

def pair_closed_world_non_burn_step_never_decreases_k
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
        PairWorldK before ≤ PairWorldK after

def pair_closed_world_no_burn_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
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
