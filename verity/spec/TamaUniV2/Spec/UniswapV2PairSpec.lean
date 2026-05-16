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

def pair_safeTransfer_traces_token_transfer
    (token toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  result = ContractResult.success 1 result.snd ∧
  hasPairSafeTransferTrace token s.thisAddress toAddr amount result.snd

/-
Local state-transition specs.

These properties avoid ERC20/callback ECM behavior and are therefore honest
Lean obligations over the executable source model. Liquidity and swap behavior
remain covered by Foundry tests until the external-token balance model is rich
enough to prove them directly.
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

def pair_swap_reverts_for_insufficient_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    amount0Out = 0 →
      amount1Out = 0 →
        result = ContractResult.revert "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT" s

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

def pair_sync_reverts_when_balance0_overflows
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance0 s > maxUint112 →
      result = ContractResult.revert "UniswapV2: OVERFLOW" s

def pair_sync_reverts_when_balance1_overflows
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance1 s > maxUint112 →
      result = ContractResult.revert "UniswapV2: OVERFLOW" s

/-!
Exact executable guard specs.

The public obligation mentions the actual entrypoint run result, not a
separately supplied result value. The older `result`-parameter specs above are
kept as small reusable adapters.
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

def pair_swap_run_revert_insufficient_output
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

def pair_sync_run_revert_locked
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    (sync).run s =
      ContractResult.revert "UniswapV2: LOCKED" s

def pair_sync_run_revert_balance0_overflows
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance0 s > maxUint112 →
      (sync).run s =
        ContractResult.revert "UniswapV2: OVERFLOW" s

def pair_sync_run_revert_balance1_overflows
    (s : ContractState) : Prop :=
  s.storage unlockedSlot.slot = 1 →
    observedBalance1 s > maxUint112 →
      (sync).run s =
        ContractResult.revert "UniswapV2: OVERFLOW" s

/-!
Closed-world economic invariants.

These specs mirror Tamago's ERC4626 trace-wide style. They quantify over every
finite successful transition sequence in `PairWorldReachable`; external ERC20
movement is represented by explicit mint/burn/swap/donate/skim/sync steps rather
than by new assumptions about Verity ECM internals.
-/

def pair_closed_world_reachable_reserves_backed
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    w.reserve0 ≤ w.balance0 ∧
    w.reserve1 ≤ w.balance1

def pair_closed_world_reachable_reserves_fit_uint112
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    w.reserve0 ≤ maxUint112Nat ∧
    w.reserve1 ≤ maxUint112Nat

def pair_closed_world_nonzero_supply_locks_minimum_liquidity
    (w : PairWorldState) : Prop :=
  PairWorldReachable w →
    w.totalSupply ≠ 0 →
      w.lockedLiquidity = minimumLiquidityNat ∧
      minimumLiquidityNat ≤ w.totalSupply

def pair_closed_world_mint_updates_reserves_to_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before after →
    after.reserve0 = after.balance0 ∧
    after.reserve1 = after.balance1

def pair_closed_world_burn_updates_reserves_to_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before after →
    after.reserve0 = after.balance0 ∧
    after.reserve1 = after.balance1

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

def pair_closed_world_skim_removes_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.skim before after →
    after.balance0 = before.reserve0 ∧
    after.balance1 = before.reserve1 ∧
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1

def pair_closed_world_sync_sets_reserves_to_balances
    (before after : PairWorldState) : Prop :=
  PairWorldStep PairWorldAction.sync before after →
    after.reserve0 = before.balance0 ∧
    after.reserve1 = before.balance1 ∧
    after.balance0 = before.balance0 ∧
    after.balance1 = before.balance1

end TamaUniV2.Spec.UniswapV2PairSpec
