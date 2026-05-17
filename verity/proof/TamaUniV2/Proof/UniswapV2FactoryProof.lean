import TamaUniV2.Spec.UniswapV2FactorySpec
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.Math

namespace TamaUniV2.Proof.UniswapV2FactoryProof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open TamaUniV2.Spec.UniswapV2FactorySpec
open TamaUniV2.UniswapV2Factory
open TamaUniV2.Common.UniswapV2FactoryConcrete
open TamaUniV2.Common.UniswapV2FactoryGhost

attribute [local simp] getPair allPairs allPairsLength pairForSlot allPairsSlot allPairsLengthSlot
  createPair pairCreate2Word factoryToken0 factoryToken1 factoryCreate2Word factoryLengthAfter
  factoryTraceContains factoryPairCreatedEvent
  UniswapV2FactoryBase.getPair UniswapV2FactoryBase.allPairs
  UniswapV2FactoryBase.allPairsLength UniswapV2FactoryBase.createPair

private theorem addressToWord_injective {a b : Address} :
    addressToWord a = addressToWord b → a = b := by
  intro h
  apply Core.Address.toNat_injective
  have h_val := congrArg (fun w : Uint256 => w.val) h
  have h_a_lt_uint : a.val < Core.Uint256.modulus := by
    have h_a_lt_addr : a.val < Core.Address.modulus := Core.Address.val_lt_modulus a
    have h_addr_lt_uint : Core.Address.modulus < Core.Uint256.modulus := by
      decide
    exact Nat.lt_trans h_a_lt_addr h_addr_lt_uint
  have h_b_lt_uint : b.val < Core.Uint256.modulus := by
    have h_b_lt_addr : b.val < Core.Address.modulus := Core.Address.val_lt_modulus b
    have h_addr_lt_uint : Core.Address.modulus < Core.Uint256.modulus := by
      decide
    exact Nat.lt_trans h_b_lt_addr h_addr_lt_uint
  have h_a_mod : a.val % Core.Uint256.modulus = a.val :=
    Nat.mod_eq_of_lt h_a_lt_uint
  have h_b_mod : b.val % Core.Uint256.modulus = b.val :=
    Nat.mod_eq_of_lt h_b_lt_uint
  simpa [addressToWord, Core.Address.toNat, h_a_mod, h_b_mod] using h_val

private theorem addressToWord_reverse_lt_of_not_lt
    {a b : Address}
    (h_distinct : a ≠ b)
    (h_not_lt : ¬ addressToWord a < addressToWord b) :
    addressToWord b < addressToWord a := by
  have h_word_ne : addressToWord a ≠ addressToWord b := by
    intro h_eq
    exact h_distinct (addressToWord_injective h_eq)
  have h_val_ne : (addressToWord a).val ≠ (addressToWord b).val := by
    intro h_val
    exact h_word_ne (Core.Uint256.ext h_val)
  have h_not_lt_val :
      ¬ (addressToWord a).val < (addressToWord b).val := by
    simpa [Verity.Core.Uint256.lt_def] using h_not_lt
  have h_rev : (addressToWord b).val < (addressToWord a).val := by
    omega
  simpa [Verity.Core.Uint256.lt_def] using h_rev

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

-- tama: discharges=factory_createPair_success_updates_storage_and_emits
theorem createPair_success_updates_storage_and_emits
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_success_updates_storage_and_emits tokenA tokenB s := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent h_pair_nonzero h_len_ok
  have h_tokenA_not_zero : ¬ tokenA = (0 : Address) := by
    simpa using h_tokenA_nonzero
  have h_tokenB_not_zero : ¬ tokenB = (0 : Address) := by
    simpa using h_tokenB_nonzero
  have h_safe_len :
      Verity.Stdlib.Math.safeAdd (s.storage allPairsLengthSlot.slot) 1 =
        some (s.storage allPairsLengthSlot.slot + 1) :=
    Verity.Proofs.Stdlib.Automation.safeAdd_some_val
      (s.storage allPairsLengthSlot.slot) 1 h_len_ok
  by_cases h_sort : addressToWord tokenA < addressToWord tokenB
  · have h_sort_raw :
        Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_absent_branch : s.storageMap2 pairForSlot.slot tokenA tokenB = 0 := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw] using h_absent
    have h_pair_nonzero_branch :
        wordToAddress (externalCall "uniswapV2PairCreate2" [tokenA, tokenB]) ≠ zeroAddress := by
      simpa [factoryCreate2Word, factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_pair_nonzero
    have h_create2_guard :
        ¬ Core.Address.ofNat
            ((Contracts.externalCallWords "uniswapV2PairCreate2"
              [Contracts.ExternalArg.toWord tokenA, Contracts.ExternalArg.toWord tokenB]) : Uint256).val =
          (0 : Address) := by
      simpa [wordToAddress] using h_pair_nonzero_branch
    simp [factory_createPair_success_updates_storage_and_emits, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, setMapping2, getMappingUint,
      setMappingUint, getStorage, setStorage, Verity.require, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.emit, emitEvent,
      Verity.Stdlib.Math.requireSomeUint, h_distinct, h_tokenA_nonzero,
      h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero, h_sort, h_sort_raw,
      h_absent_branch, h_pair_nonzero_branch, h_create2_guard, h_safe_len]
  · have h_sort_raw :
        ¬ Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_absent_branch : s.storageMap2 pairForSlot.slot tokenB tokenA = 0 := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw] using h_absent
    have h_pair_nonzero_branch :
        wordToAddress (externalCall "uniswapV2PairCreate2" [tokenB, tokenA]) ≠ zeroAddress := by
      simpa [factoryCreate2Word, factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_pair_nonzero
    have h_create2_guard :
        ¬ Core.Address.ofNat
            ((Contracts.externalCallWords "uniswapV2PairCreate2"
              [Contracts.ExternalArg.toWord tokenB, Contracts.ExternalArg.toWord tokenA]) : Uint256).val =
          (0 : Address) := by
      simpa [wordToAddress] using h_pair_nonzero_branch
    simp [factory_createPair_success_updates_storage_and_emits, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, setMapping2, getMappingUint,
      setMappingUint, getStorage, setStorage, Verity.require, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.emit, emitEvent,
      Verity.Stdlib.Math.requireSomeUint, h_distinct, h_tokenA_nonzero,
      h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero, h_sort, h_sort_raw,
      h_absent_branch, h_pair_nonzero_branch, h_create2_guard, h_safe_len]

-- tama: discharges=factory_createPair_first_success_refines_closed_world
theorem createPair_first_success_refines_closed_world
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_first_success_refines_closed_world tokenA tokenB s := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero _h_empty
    _h_absent h_pair_nonzero _h_len_ok _h_run
  have h_tokenA_not_zero : ¬ tokenA = (0 : Address) := by
    simpa using h_tokenA_nonzero
  have h_tokenB_not_zero : ¬ tokenB = (0 : Address) := by
    simpa using h_tokenB_nonzero
  by_cases h_sort : addressToWord tokenA < addressToWord tokenB
  · have h_sort_raw :
        Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_pair_nonzero_branch :
        wordToAddress (externalCall "uniswapV2PairCreate2" [tokenA, tokenB]) ≠ zeroAddress := by
      simpa [factoryCreate2Word, factoryToken0, factoryToken1, addressToWord,
        h_sort, h_sort_raw] using h_pair_nonzero
    have h_create2_guard :
        ¬ Core.Address.ofNat
            ((Contracts.externalCallWords "uniswapV2PairCreate2"
              [Contracts.ExternalArg.toWord tokenA, Contracts.ExternalArg.toWord tokenB]) : Uint256).val =
          (0 : Address) := by
      simpa [wordToAddress] using h_pair_nonzero_branch
    simp [factory_createPair_first_success_refines_closed_world,
      FactoryWorldStep, FactoryWorldCreatePairStep, FactoryWorldInitial,
      FactoryWorldPairGood, factoryToken0, factoryToken1, addressToWord,
      h_sort, h_sort_raw, h_distinct, h_tokenA_nonzero, h_tokenB_nonzero,
      h_tokenA_not_zero, h_tokenB_not_zero, h_pair_nonzero,
      h_pair_nonzero_branch, h_create2_guard]
  · have h_sort_raw :
        ¬ Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_reverse_sort : addressToWord tokenB < addressToWord tokenA :=
      addressToWord_reverse_lt_of_not_lt h_distinct h_sort
    have h_reverse_sort_raw :
        Core.Address.toNat tokenB % Core.Uint256.modulus <
          Core.Address.toNat tokenA % Core.Uint256.modulus := by
      simpa [addressToWord] using h_reverse_sort
    have h_distinct_symm : tokenB ≠ tokenA := by
      exact fun h => h_distinct h.symm
    have h_pair_nonzero_branch :
        wordToAddress (externalCall "uniswapV2PairCreate2" [tokenB, tokenA]) ≠ zeroAddress := by
      simpa [factoryCreate2Word, factoryToken0, factoryToken1, addressToWord,
        h_sort, h_sort_raw] using h_pair_nonzero
    have h_create2_guard :
        ¬ Core.Address.ofNat
            ((Contracts.externalCallWords "uniswapV2PairCreate2"
              [Contracts.ExternalArg.toWord tokenB, Contracts.ExternalArg.toWord tokenA]) : Uint256).val =
          (0 : Address) := by
      simpa [wordToAddress] using h_pair_nonzero_branch
    simp [factory_createPair_first_success_refines_closed_world,
      FactoryWorldStep, FactoryWorldCreatePairStep, FactoryWorldInitial,
      FactoryWorldPairGood, factoryToken0, factoryToken1, addressToWord,
      h_sort, h_sort_raw, h_reverse_sort, h_reverse_sort_raw, h_distinct,
      h_tokenA_nonzero, h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero,
      h_distinct_symm, h_pair_nonzero, h_pair_nonzero_branch, h_create2_guard]

-- tama: discharges=factory_allPairs_run_revert_out_of_bounds
theorem allPairs_run_revert_out_of_bounds (index : Uint256) (s : ContractState) :
  factory_allPairs_run_revert_out_of_bounds index s := by
  simpa [factory_allPairs_run_revert_out_of_bounds,
    factory_allPairs_reverts_out_of_bounds]
    using allPairs_reverts_out_of_bounds index s

-- tama: discharges=factory_createPair_run_revert_identical_addresses
theorem createPair_run_revert_identical_addresses
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_run_revert_identical_addresses tokenA tokenB s := by
  simpa [factory_createPair_run_revert_identical_addresses,
    factory_createPair_rejects_identical_addresses]
    using createPair_rejects_identical_addresses tokenA tokenB s

-- tama: discharges=factory_createPair_run_revert_zero_address
theorem createPair_run_revert_zero_address
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_run_revert_zero_address tokenA tokenB s := by
  simpa [factory_createPair_run_revert_zero_address,
    factory_createPair_rejects_zero_address]
    using createPair_rejects_zero_address tokenA tokenB s

-- tama: discharges=factory_createPair_run_revert_duplicates
theorem createPair_run_revert_duplicates
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_run_revert_duplicates tokenA tokenB s := by
  simpa [factory_createPair_run_revert_duplicates,
    factory_createPair_rejects_duplicates]
    using createPair_rejects_duplicates tokenA tokenB s

-- tama: discharges=factory_createPair_run_revert_create2_failed
theorem createPair_run_revert_create2_failed
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_run_revert_create2_failed tokenA tokenB s := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent h_pair_zero
  have h_tokenA_not_zero : ¬ tokenA = (0 : Address) := by
    simpa using h_tokenA_nonzero
  have h_tokenB_not_zero : ¬ tokenB = (0 : Address) := by
    simpa using h_tokenB_nonzero
  by_cases h_sort : addressToWord tokenA < addressToWord tokenB
  · have h_sort_raw :
        Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_absent_branch : s.storageMap2 pairForSlot.slot tokenA tokenB = 0 := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw] using h_absent
    have h_pair_zero_branch :
        externalCall "uniswapV2PairCreate2" [tokenA, tokenB] = (0 : Uint256) := by
      simpa [factoryCreate2Word, factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_pair_zero
    simp [factory_createPair_run_revert_create2_failed, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, Verity.require, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, h_distinct,
      h_tokenA_nonzero, h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero,
      h_sort, h_sort_raw, h_absent_branch, h_pair_zero_branch]
  · have h_sort_raw :
        ¬ Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_absent_branch : s.storageMap2 pairForSlot.slot tokenB tokenA = 0 := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw] using h_absent
    have h_pair_zero_branch :
        externalCall "uniswapV2PairCreate2" [tokenB, tokenA] = (0 : Uint256) := by
      simpa [factoryCreate2Word, factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_pair_zero
    simp [factory_createPair_run_revert_create2_failed, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, Verity.require, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, h_distinct,
      h_tokenA_nonzero, h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero,
      h_sort, h_sort_raw, h_absent_branch, h_pair_zero_branch]

-- tama: discharges=factory_createPair_run_revert_pair_count_overflow
theorem createPair_run_revert_pair_count_overflow
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_run_revert_pair_count_overflow tokenA tokenB s := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent h_pair_nonzero h_len_overflow
  have h_tokenA_not_zero : ¬ tokenA = (0 : Address) := by
    simpa using h_tokenA_nonzero
  have h_tokenB_not_zero : ¬ tokenB = (0 : Address) := by
    simpa using h_tokenB_nonzero
  have h_safe_len :
      Verity.Stdlib.Math.safeAdd (s.storage allPairsLengthSlot.slot) 1 = none := by
    exact Verity.Proofs.Stdlib.Math.safeAdd_none
      (s.storage allPairsLengthSlot.slot) 1 h_len_overflow
  by_cases h_sort : addressToWord tokenA < addressToWord tokenB
  · have h_sort_raw :
        Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_absent_branch : s.storageMap2 pairForSlot.slot tokenA tokenB = 0 := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw] using h_absent
    have h_pair_nonzero_branch :
        wordToAddress (externalCall "uniswapV2PairCreate2" [tokenA, tokenB]) ≠ zeroAddress := by
      simpa [factoryCreate2Word, factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_pair_nonzero
    have h_create2_guard :
        ¬ Core.Address.ofNat
            ((Contracts.externalCallWords "uniswapV2PairCreate2"
              [Contracts.ExternalArg.toWord tokenA, Contracts.ExternalArg.toWord tokenB]) : Uint256).val =
          (0 : Address) := by
      simpa [wordToAddress] using h_pair_nonzero_branch
    simp [factory_createPair_run_revert_pair_count_overflow, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, setMapping2, getStorage, Verity.require,
      Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Verity.Stdlib.Math.requireSomeUint, h_distinct, h_tokenA_nonzero,
      h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero, h_sort, h_sort_raw,
      h_absent_branch, h_pair_nonzero_branch, h_create2_guard, h_safe_len]
  · have h_sort_raw :
        ¬ Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    have h_absent_branch : s.storageMap2 pairForSlot.slot tokenB tokenA = 0 := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw] using h_absent
    have h_pair_nonzero_branch :
        wordToAddress (externalCall "uniswapV2PairCreate2" [tokenB, tokenA]) ≠ zeroAddress := by
      simpa [factoryCreate2Word, factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_pair_nonzero
    have h_create2_guard :
        ¬ Core.Address.ofNat
            ((Contracts.externalCallWords "uniswapV2PairCreate2"
              [Contracts.ExternalArg.toWord tokenB, Contracts.ExternalArg.toWord tokenA]) : Uint256).val =
          (0 : Address) := by
      simpa [wordToAddress] using h_pair_nonzero_branch
    simp [factory_createPair_run_revert_pair_count_overflow, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, setMapping2, getStorage, Verity.require,
      Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Verity.Stdlib.Math.requireSomeUint, h_distinct, h_tokenA_nonzero,
      h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero, h_sort, h_sort_raw,
      h_absent_branch, h_pair_nonzero_branch, h_create2_guard, h_safe_len]

-- tama: discharges=factory_createPair_revert_keeps_factory_state
theorem createPair_revert_keeps_factory_state
    (tokenA tokenB : Address) (s : ContractState)
    (result : ContractResult Address) :
  factory_createPair_revert_keeps_factory_state tokenA tokenB s result := by
  intro _h_run h_revert
  rcases h_revert with ⟨reason, h_result⟩
  rw [h_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem factoryWorldStep_preserves_good
    (action : FactoryWorldAction)
    (before after : FactoryWorldState) :
  FactoryWorldGood before →
    FactoryWorldStep action before after →
      FactoryWorldGood after := by
  intro h_good h_step
  rcases h_good with ⟨h_entries_good, h_no_dup, h_count_before⟩
  cases action with
  | createPair tokenA tokenB pair =>
      simp [FactoryWorldStep, FactoryWorldCreatePairStep] at h_step
      rcases h_step with ⟨_h_distinct, _h_tokenA_nonzero, _h_tokenB_nonzero,
        _h_token_order, h_new_good, h_absent, h_pairs, h_count⟩
      refine ⟨?_, ?_, ?_⟩
      · intro entry h_entry
        rw [h_pairs] at h_entry
        rcases List.mem_append.mp h_entry with h_old | h_new
        · exact h_entries_good entry h_old
        · simp at h_new
          rcases h_new with h_new
          rw [h_new]
          exact h_new_good
      · intro a b h_a h_b h_token0 h_token1
        rw [h_pairs] at h_a h_b
        rcases List.mem_append.mp h_a with h_a_old | h_a_new
        · rcases List.mem_append.mp h_b with h_b_old | h_b_new
          · exact h_no_dup a b h_a_old h_b_old h_token0 h_token1
          · simp at h_b_new
            rw [h_b_new] at h_token0 h_token1
            rcases h_absent a h_a_old with h_absent0 | h_absent1
            · exact False.elim (h_absent0 h_token0)
            · exact False.elim (h_absent1 h_token1)
        · rcases List.mem_append.mp h_b with h_b_old | h_b_new
          · simp at h_a_new
            rw [h_a_new] at h_token0 h_token1
            rcases h_absent b h_b_old with h_absent0 | h_absent1
            · exact False.elim (h_absent0 h_token0.symm)
            · exact False.elim (h_absent1 h_token1.symm)
          · simp at h_a_new h_b_new
            rw [h_a_new, h_b_new]
      · rw [h_count, h_pairs, h_count_before]
        simp

private theorem factoryWorldReachable_good
    (w : FactoryWorldState) :
  FactoryWorldReachable w → FactoryWorldGood w := by
  intro h_reachable
  induction h_reachable with
  | init =>
      simp [FactoryWorldInitial, FactoryWorldGood,
        FactoryWorldNoDuplicateSortedPairs]
  | step action h_before h_step ih =>
      exact factoryWorldStep_preserves_good action _ _ ih h_step

private theorem factoryWorldPath_preserves_good
    {before after : FactoryWorldState} :
  FactoryWorldGood before →
    FactoryWorldPath before after →
      FactoryWorldGood after := by
  intro h_good h_path
  revert h_good
  induction h_path with
  | refl =>
      intro h_good
      exact h_good
  | step action h_prefix h_step ih =>
      intro h_good
      exact factoryWorldStep_preserves_good action _ _ (ih h_good) h_step

private theorem factoryWorldPath_preserves_existing_pair
    {before after : FactoryWorldState}
    {existing0 existing1 existingPair : Address} :
  FactoryWorldContainsPair before existing0 existing1 existingPair →
    FactoryWorldPath before after →
      FactoryWorldContainsPair after existing0 existing1 existingPair := by
  intro h_existing h_path
  induction h_path with
  | refl =>
      exact h_existing
  | step action h_prefix h_step ih =>
      cases action with
      | createPair tokenA tokenB pair =>
          rcases ih with ⟨entry, h_entry, h_tokens, h_pair⟩
          simp [FactoryWorldStep, FactoryWorldCreatePairStep] at h_step
          rcases h_step with ⟨_h_distinct, _h_tokenA_nonzero, _h_tokenB_nonzero,
            _h_token_order, _h_new_good, _h_absent, h_pairs, _h_count⟩
          refine ⟨entry, ?_, h_tokens, h_pair⟩
          rw [h_pairs]
          exact List.mem_append_left _ h_entry

-- tama: discharges=factory_closed_world_step_preserves_good
theorem closed_world_step_preserves_good
    (action : FactoryWorldAction)
    (before after : FactoryWorldState) :
  factory_closed_world_step_preserves_good action before after := by
  exact factoryWorldStep_preserves_good action before after

-- tama: discharges=factory_closed_world_reachable_good
theorem closed_world_reachable_good
    (w : FactoryWorldState) :
  factory_closed_world_reachable_good w := by
  exact factoryWorldReachable_good w

-- tama: discharges=factory_closed_world_path_preserves_good
theorem closed_world_path_preserves_good
    (before after : FactoryWorldState) :
  factory_closed_world_path_preserves_good before after := by
  exact factoryWorldPath_preserves_good

-- tama: discharges=factory_closed_world_created_pairs_are_sorted_and_nonzero
theorem closed_world_created_pairs_are_sorted_and_nonzero
    (w : FactoryWorldState) :
  factory_closed_world_created_pairs_are_sorted_and_nonzero w := by
  intro h_reachable
  exact (factoryWorldReachable_good w h_reachable).1

-- tama: discharges=factory_closed_world_sorted_pair_unique
theorem closed_world_sorted_pair_unique
    (w : FactoryWorldState) :
  factory_closed_world_sorted_pair_unique w := by
  intro h_reachable
  exact (factoryWorldReachable_good w h_reachable).2.1

-- tama: discharges=factory_closed_world_lookup_symmetric
theorem closed_world_lookup_symmetric
    (w : FactoryWorldState) (tokenA tokenB pair : Address) :
  factory_closed_world_lookup_symmetric w tokenA tokenB pair := by
  intro _h_reachable h_contains
  rcases h_contains with ⟨entry, h_entry, h_tokens, h_pair⟩
  refine ⟨entry, h_entry, ?_, h_pair⟩
  rcases h_tokens with h_forward | h_reverse
  · exact Or.inr h_forward
  · exact Or.inl h_reverse

-- tama: discharges=factory_closed_world_create_appends_one_pair
theorem closed_world_create_appends_one_pair
    (tokenA tokenB pair : Address)
    (before after : FactoryWorldState) :
  factory_closed_world_create_appends_one_pair tokenA tokenB pair before after := by
  intro h_step
  simp [FactoryWorldCreatePairStep] at h_step
  rcases h_step with ⟨_h_distinct, _h_tokenA_nonzero, _h_tokenB_nonzero,
    _h_token_order, _h_new_good, _h_absent, h_pairs, h_count⟩
  constructor
  · rw [h_pairs]
    simp
  · exact h_count

-- tama: discharges=factory_closed_world_create_adds_symmetric_lookup
theorem closed_world_create_adds_symmetric_lookup
    (tokenA tokenB pair : Address)
    (before after : FactoryWorldState) :
  factory_closed_world_create_adds_symmetric_lookup tokenA tokenB pair before after := by
  intro h_step
  dsimp [FactoryWorldCreatePairStep] at h_step
  rcases h_step with ⟨_h_distinct, _h_tokenA_nonzero, _h_tokenB_nonzero,
    h_token_order, _h_new_good, _h_absent, h_pairs, _h_count⟩
  constructor
  · refine ⟨{
        token0 := factoryToken0 tokenA tokenB
        token1 := factoryToken1 tokenA tokenB
        pair := pair
      }, ?_, ?_, rfl⟩
    · rw [h_pairs]
      simp
    · exact h_token_order
  · refine ⟨{
        token0 := factoryToken0 tokenA tokenB
        token1 := factoryToken1 tokenA tokenB
        pair := pair
      }, ?_, ?_, rfl⟩
    · rw [h_pairs]
      simp
    · rcases h_token_order with h_forward | h_reverse
      · exact Or.inr h_forward
      · exact Or.inl h_reverse

-- tama: discharges=factory_closed_world_create_preserves_existing_pairs
theorem closed_world_create_preserves_existing_pairs
    (tokenA tokenB pair existing0 existing1 existingPair : Address)
    (before after : FactoryWorldState) :
  factory_closed_world_create_preserves_existing_pairs
    tokenA tokenB pair existing0 existing1 existingPair before after := by
  intro h_existing h_step
  rcases h_existing with ⟨entry, h_entry, h_tokens, h_pair⟩
  simp [FactoryWorldCreatePairStep] at h_step
  rcases h_step with ⟨_h_distinct, _h_tokenA_nonzero, _h_tokenB_nonzero,
    _h_token_order, _h_new_good, _h_absent, h_pairs, _h_count⟩
  refine ⟨entry, ?_, h_tokens, h_pair⟩
  rw [h_pairs]
  exact List.mem_append_left _ h_entry

-- tama: discharges=factory_closed_world_path_preserves_existing_pairs
theorem closed_world_path_preserves_existing_pairs
    (existing0 existing1 existingPair : Address)
    (before after : FactoryWorldState) :
  factory_closed_world_path_preserves_existing_pairs
    existing0 existing1 existingPair before after := by
  exact factoryWorldPath_preserves_existing_pair

-- tama: discharges=factory_closed_world_length_matches_created_pairs
theorem closed_world_length_matches_created_pairs
    (w : FactoryWorldState) :
  factory_closed_world_length_matches_created_pairs w := by
  intro h_reachable
  exact (factoryWorldReachable_good w h_reachable).2.2

-- tama: discharges=factory_closed_world_path_length_matches_created_pairs
theorem closed_world_path_length_matches_created_pairs
    (before after : FactoryWorldState) :
  factory_closed_world_path_length_matches_created_pairs before after := by
  intro h_good h_path
  exact (factoryWorldPath_preserves_good h_good h_path).2.2

end TamaUniV2.Proof.UniswapV2FactoryProof
