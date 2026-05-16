import TamaUniV2.UniswapV2Pair
import TamaUniV2.Common.UniswapV2PairConcrete

namespace TamaUniV2.Spec.UniswapV2PairSpec

open Verity
open Verity.EVM.Uint256
open TamaUniV2.UniswapV2Pair
open TamaUniV2.Common.UniswapV2PairConcrete

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

def pair_sync_reverts_when_locked
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  s.storage unlockedSlot.slot != 1 →
    result = ContractResult.revert "UniswapV2: LOCKED" s

end TamaUniV2.Spec.UniswapV2PairSpec
