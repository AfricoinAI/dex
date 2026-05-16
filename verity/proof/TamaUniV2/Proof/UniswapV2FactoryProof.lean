import TamaUniV2.Spec.UniswapV2FactorySpec
import Verity.Proofs.Stdlib.Automation

namespace TamaUniV2.Proof.UniswapV2FactoryProof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open TamaUniV2.Spec.UniswapV2FactorySpec
open TamaUniV2.UniswapV2Factory

attribute [local simp] getPair allPairs allPairsLength pairForSlot allPairsSlot allPairsLengthSlot
  createPair
  UniswapV2FactoryBase.getPair UniswapV2FactoryBase.allPairs
  UniswapV2FactoryBase.allPairsLength UniswapV2FactoryBase.createPair

-- tama: discharges=factory_getPair_spec
theorem getPair_meets_spec (tokenA tokenB : Address) (s : ContractState) :
  factory_getPair_spec tokenA tokenB ((getPair tokenA tokenB).run s).fst s := by
  rfl

-- tama: discharges=factory_allPairsLength_spec
theorem allPairsLength_meets_spec (s : ContractState) :
  factory_allPairsLength_spec ((allPairsLength).run s).fst s := by
  rfl

-- tama: discharges=factory_allPairs_success_spec
theorem allPairs_meets_spec (index : Uint256) (s : ContractState) :
  factory_allPairs_success_spec index ((allPairs index).run s).fst s := by
  intro h
  have hval : index.val < (s.storage allPairsLengthSlot.slot).val := h
  simp [allPairs, UniswapV2FactoryBase.allPairs,
    Verity.getStorage, Verity.getMappingUint, Verity.require, Contract.run,
    ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure, hval]

-- tama: discharges=factory_allPairs_reverts_out_of_bounds
theorem allPairs_reverts_out_of_bounds (index : Uint256) (s : ContractState) :
  factory_allPairs_reverts_out_of_bounds index s ((allPairs index).run s) := by
  intro h
  have hval : ¬ index.val < (s.storage allPairsLengthSlot.slot).val := by
    simpa using h
  simp [factory_allPairs_reverts_out_of_bounds, allPairs, UniswapV2FactoryBase.allPairs,
    Verity.getStorage, Verity.require, Contract.run, Verity.bind, Bind.bind, hval]

-- tama: discharges=factory_createPair_rejects_identical_addresses
theorem createPair_rejects_identical_addresses
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_rejects_identical_addresses tokenA tokenB s
    ((createPair tokenA tokenB).run s) := by
  intro h_same
  subst h_same
  simp [factory_createPair_rejects_identical_addresses, createPair,
    UniswapV2FactoryBase.createPair, Verity.require, Contract.run,
    Verity.bind, Bind.bind]

-- tama: discharges=factory_createPair_rejects_zero_address
theorem createPair_rejects_zero_address
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_rejects_zero_address tokenA tokenB s
    ((createPair tokenA tokenB).run s) := by
  intro h_distinct h_zero
  rcases h_zero with h_tokenA_zero | h_tokenB_zero
  · subst h_tokenA_zero
    have h_not_identical : ¬ (0 : Address) = tokenB := by
      simpa using h_distinct
    simp [factory_createPair_rejects_zero_address, createPair,
      UniswapV2FactoryBase.createPair, Verity.require, Contract.run,
      Verity.bind, Bind.bind, h_not_identical]
  · subst h_tokenB_zero
    have h_not_identical : ¬ tokenA = (0 : Address) := by
      simpa using h_distinct
    simp [factory_createPair_rejects_zero_address, createPair,
      UniswapV2FactoryBase.createPair, Verity.require, Contract.run,
      Verity.bind, Bind.bind, h_not_identical]

-- tama: discharges=factory_createPair_rejects_duplicates
theorem createPair_rejects_duplicates
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_rejects_duplicates tokenA tokenB s
    ((createPair tokenA tokenB).run s) := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_existing
  have h_tokenA_not_zero : ¬ tokenA = (0 : Address) := by
    simpa using h_tokenA_nonzero
  have h_tokenB_not_zero : ¬ tokenB = (0 : Address) := by
    simpa using h_tokenB_nonzero
  by_cases h_sort : addressToWord tokenA < addressToWord tokenB
  · have h_sort_raw :
        Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_existing_branch : s.storageMap2 pairForSlot.slot tokenA tokenB ≠ 0 := by
      simpa [addressToWord, h_sort_raw] using h_existing
    simp [factory_createPair_rejects_duplicates, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, Verity.require, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, h_distinct, h_tokenA_nonzero,
      h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero, h_sort, h_sort_raw,
      h_existing_branch]
  · have h_sort_raw :
        ¬ Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_existing_branch : s.storageMap2 pairForSlot.slot tokenB tokenA ≠ 0 := by
      simpa [addressToWord, h_sort_raw] using h_existing
    simp [factory_createPair_rejects_duplicates, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, Verity.require, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, h_distinct, h_tokenA_nonzero,
      h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero, h_sort, h_sort_raw,
      h_existing_branch]

end TamaUniV2.Proof.UniswapV2FactoryProof
