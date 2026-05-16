import TamaUniV2.UniswapV2Factory

namespace TamaUniV2.Spec.UniswapV2FactorySpec

open Verity
open Verity.EVM.Uint256
open TamaUniV2.UniswapV2Factory

/-! Specs for the Uniswap v2 factory storage-facing ABI. -/

def factory_getPair_spec (tokenA tokenB result : Address) (s : ContractState) : Prop :=
  result = wordToAddress (s.storageMap2 pairForSlot.slot tokenA tokenB)

def factory_allPairsLength_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage allPairsLengthSlot.slot

def factory_allPairs_success_spec (index : Uint256) (result : Address) (s : ContractState) : Prop :=
  index < s.storage allPairsLengthSlot.slot →
    result = wordToAddress (s.storageMapUint allPairsSlot.slot index)

/-!
Local factory state-transition obligations.

Successful pair creation crosses the CREATE2 and pair-initialize boundaries.
Factory-local storage and ordering behavior should still be specified directly;
only the external deployment/call effects belong at those boundaries.
-/

def factory_allPairs_reverts_out_of_bounds
    (index : Uint256) (s : ContractState) (result : ContractResult Address) : Prop :=
  ¬ index < s.storage allPairsLengthSlot.slot →
    result = ContractResult.revert "UniswapV2: INDEX_OUT_OF_BOUNDS" s

def factory_createPair_rejects_identical_addresses
    (tokenA tokenB : Address) (s : ContractState) (result : ContractResult Address) : Prop :=
  tokenA = tokenB →
    result = ContractResult.revert "UniswapV2: IDENTICAL_ADDRESSES" s

def factory_createPair_rejects_zero_address
    (tokenA tokenB : Address) (s : ContractState) (result : ContractResult Address) : Prop :=
  tokenA ≠ tokenB →
    (tokenA = zeroAddress ∨ tokenB = zeroAddress) →
      result = ContractResult.revert "UniswapV2: ZERO_ADDRESS" s

def factory_createPair_rejects_duplicates
    (tokenA tokenB : Address) (s : ContractState) (result : ContractResult Address) : Prop :=
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot
          (if (addressToWord tokenA) < (addressToWord tokenB) then tokenA else tokenB)
          (if (addressToWord tokenA) < (addressToWord tokenB) then tokenB else tokenA) ≠ 0 →
          result = ContractResult.revert "UniswapV2: PAIR_EXISTS" s

/-! Exact run-result revert specs for factory guards. -/

def factory_allPairs_run_revert_out_of_bounds
    (index : Uint256) (s : ContractState) : Prop :=
  ¬ index < s.storage allPairsLengthSlot.slot →
    (allPairs index).run s =
      ContractResult.revert "UniswapV2: INDEX_OUT_OF_BOUNDS" s

def factory_createPair_run_revert_identical_addresses
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  tokenA = tokenB →
    (createPair tokenA tokenB).run s =
      ContractResult.revert "UniswapV2: IDENTICAL_ADDRESSES" s

def factory_createPair_run_revert_zero_address
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  tokenA ≠ tokenB →
    (tokenA = zeroAddress ∨ tokenB = zeroAddress) →
      (createPair tokenA tokenB).run s =
        ContractResult.revert "UniswapV2: ZERO_ADDRESS" s

def factory_createPair_run_revert_duplicates
    (tokenA tokenB : Address) (s : ContractState) : Prop :=
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot
          (if (addressToWord tokenA) < (addressToWord tokenB) then tokenA else tokenB)
          (if (addressToWord tokenA) < (addressToWord tokenB) then tokenB else tokenA) ≠ 0 →
          (createPair tokenA tokenB).run s =
            ContractResult.revert "UniswapV2: PAIR_EXISTS" s

end TamaUniV2.Spec.UniswapV2FactorySpec
