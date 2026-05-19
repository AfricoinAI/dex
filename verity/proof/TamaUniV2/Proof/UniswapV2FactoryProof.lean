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
private theorem list_get?_some_lt
    {α : Type} {xs : List α} {index : Nat} {entry : α} :
  xs[index]? = some entry →
    index < xs.length := by
  revert index
  induction xs with
  | nil =>
      intro index h_get
      cases index <;> simp at h_get
  | cons head tail ih =>
      intro index h_get
      cases index with
      | zero =>
          simp
      | succ index =>
          simp at h_get
          have h_tail := ih h_get
          simp [h_tail]
private theorem list_get?_append_singleton_cases
    {α : Type} {xs : List α} {x y : α} {index : Nat} :
  (xs ++ [x])[index]? = some y →
    xs[index]? = some y ∨ (index = xs.length ∧ y = x) := by
  revert index
  induction xs with
  | nil =>
      intro index h_get
      cases index with
      | zero =>
          have h_xy : x = y := by
            simpa using h_get
          exact Or.inr ⟨rfl, h_xy.symm⟩
      | succ index =>
          simp at h_get
  | cons head tail ih =>
      intro index h_get
      cases index with
      | zero =>
          have h_head : head = y := by
            simpa using h_get
          exact Or.inl (by simp [h_head])
      | succ index =>
          simp at h_get
          rcases ih h_get with h_old | ⟨h_index, h_y⟩
          · exact Or.inl (by simp [h_old])
          · exact Or.inr ⟨by simp [h_index], h_y⟩
private theorem list_get?_append_left_of_some
    {α : Type} {xs ys : List α} {index : Nat} {entry : α} :
  xs[index]? = some entry →
    (xs ++ ys)[index]? = some entry := by
  revert index
  induction xs with
  | nil =>
      intro index h_get
      cases index <;> simp at h_get
  | cons head tail ih =>
      intro index h_get
      cases index with
      | zero =>
          simpa using h_get
      | succ index =>
          simp at h_get ⊢
          exact ih h_get
private theorem uint256_ofNat_ne_of_lt_val
    {index : Nat} {u : Uint256}
    (h_lt : index < u.val) :
  Core.Uint256.ofNat index ≠ u := by
  intro h_eq
  have h_val := congrArg (fun w : Uint256 => w.val) h_eq
  have h_index_lt_mod : index < Core.Uint256.modulus :=
    Nat.lt_trans h_lt u.isLt
  have h_mod : index % Core.Uint256.modulus = index :=
    Nat.mod_eq_of_lt h_index_lt_mod
  have h_eq_val : index = u.val := by
    simpa [h_mod] using h_val
  omega
private theorem uint256_ofNat_eq_of_eq_val
    {index : Nat} {u : Uint256}
    (h_eq_val : index = u.val) :
  Core.Uint256.ofNat index = u := by
  apply Core.Uint256.ext
  have h_index_lt_mod : index < Core.Uint256.modulus := by
    rw [h_eq_val]
    exact u.isLt
  have h_mod : index % Core.Uint256.modulus = index :=
    Nat.mod_eq_of_lt h_index_lt_mod
  have h_u_mod : u.val % Core.Uint256.modulus = u.val :=
    Nat.mod_eq_of_lt u.isLt
  simp [h_mod, h_eq_val, h_u_mod]
private theorem factoryWorldEntry_not_reverse_pair
    (entry newEntry : FactoryWorldPair)
    (h_entry_good : FactoryWorldPairGood entry)
    (h_new_good : FactoryWorldPairGood newEntry) :
  entry.token0 ≠ newEntry.token1 ∨
    entry.token1 ≠ newEntry.token0 := by
  by_cases h_token0 : entry.token0 = newEntry.token1
  · right
    intro h_token1
    rcases h_entry_good with
      ⟨_h_entry_distinct, _h_entry_nonzero0, _h_entry_nonzero1,
        h_entry_sorted, _h_entry_pair⟩
    rcases h_new_good with
      ⟨_h_new_distinct, _h_new_nonzero0, _h_new_nonzero1,
        h_new_sorted, _h_new_pair⟩
    rw [h_token0, h_token1] at h_entry_sorted
    have h_entry_sorted_val :
        (addressToWord newEntry.token1).val <
          (addressToWord newEntry.token0).val := by
      simpa [Verity.Core.Uint256.lt_def] using h_entry_sorted
    have h_new_sorted_val :
        (addressToWord newEntry.token0).val <
          (addressToWord newEntry.token1).val := by
      simpa [Verity.Core.Uint256.lt_def] using h_new_sorted
    exact False.elim ((Nat.lt_asymm h_new_sorted_val) h_entry_sorted_val)
  · exact Or.inl h_token0
-- tama: discharges=factory_getPair_run_success_frames_state
theorem getPair_run_success_frames_state
    (tokenA tokenB : Address) (s : ContractState) :
  factory_getPair_run_success_frames_state tokenA tokenB s := by
  rfl
-- tama: discharges=factory_allPairsLength_run_success_frames_state
theorem allPairsLength_run_success_frames_state (s : ContractState) :
  factory_allPairsLength_run_success_frames_state s := by
  rfl
-- tama: discharges=factory_allPairs_run_success_in_bounds
theorem allPairs_run_success_in_bounds (index : Uint256) (s : ContractState) :
  factory_allPairs_run_success_in_bounds index s := by
  intro h
  have hval : index.val < (s.storage allPairsLengthSlot.slot).val := h
  simp [factory_allPairs_run_success_in_bounds, allPairs,
    UniswapV2FactoryBase.allPairs, Verity.getStorage, Verity.getMappingUint,
    Verity.require, Contract.run, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, hval]
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
-- tama: discharges=factory_createPair_success_matches_closed_world_step
theorem createPair_success_matches_closed_world_step
    (tokenA tokenB : Address) (s : ContractState)
    (before : FactoryWorldState) :
  factory_createPair_success_matches_closed_world_step tokenA tokenB s before := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero _h_good _h_count
    _h_absent h_absent_world h_pair_nonzero _h_len_ok _h_run
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
    have h_absent_world_branch :
        ∀ entry, entry ∈ before.pairs →
          entry.token0 ≠ tokenA ∨ entry.token1 ≠ tokenB := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_absent_world
    simp [factory_createPair_success_matches_closed_world_step,
      FactoryWorldStep, FactoryWorldCreatePairStep, FactoryWorldInitial,
      FactoryWorldPairGood, factoryToken0, factoryToken1, addressToWord,
      h_sort, h_sort_raw, h_distinct, h_tokenA_nonzero, h_tokenB_nonzero,
      h_tokenA_not_zero, h_tokenB_not_zero, h_pair_nonzero,
      h_pair_nonzero_branch, h_create2_guard, h_absent_world,
      h_absent_world_branch]
    exact h_absent_world_branch
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
    have h_absent_world_branch :
        ∀ entry, entry ∈ before.pairs →
          entry.token0 ≠ tokenB ∨ entry.token1 ≠ tokenA := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_absent_world
    simp [factory_createPair_success_matches_closed_world_step,
      FactoryWorldStep, FactoryWorldCreatePairStep, FactoryWorldInitial,
      FactoryWorldPairGood, factoryToken0, factoryToken1, addressToWord,
      h_sort, h_sort_raw, h_reverse_sort, h_reverse_sort_raw, h_distinct,
      h_tokenA_nonzero, h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero,
      h_distinct_symm, h_pair_nonzero, h_pair_nonzero_branch, h_create2_guard,
      h_absent_world, h_absent_world_branch]
    exact h_absent_world_branch
-- tama: discharges=factory_allPairs_run_revert_out_of_bounds
theorem allPairs_run_revert_out_of_bounds (index : Uint256) (s : ContractState) :
  factory_allPairs_run_revert_out_of_bounds index s := by
  intro h
  have hval : ¬ index.val < (s.storage allPairsLengthSlot.slot).val := by
    simpa using h
  simp [factory_allPairs_run_revert_out_of_bounds, allPairs, UniswapV2FactoryBase.allPairs,
    Verity.getStorage, Verity.require, Contract.run, Verity.bind, Bind.bind, hval]
-- tama: discharges=factory_createPair_run_revert_identical_addresses
theorem createPair_run_revert_identical_addresses
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_run_revert_identical_addresses tokenA tokenB s := by
  intro h_same
  subst h_same
  simp [factory_createPair_run_revert_identical_addresses, createPair,
    UniswapV2FactoryBase.createPair, Verity.require, Contract.run,
    Verity.bind, Bind.bind]
-- tama: discharges=factory_createPair_run_revert_zero_address
theorem createPair_run_revert_zero_address
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_run_revert_zero_address tokenA tokenB s := by
  intro h_distinct h_zero
  rcases h_zero with h_tokenA_zero | h_tokenB_zero
  · subst h_tokenA_zero
    have h_not_identical : ¬ (0 : Address) = tokenB := by
      simpa using h_distinct
    simp [factory_createPair_run_revert_zero_address, createPair,
      UniswapV2FactoryBase.createPair, Verity.require, Contract.run,
      Verity.bind, Bind.bind, h_not_identical]
  · subst h_tokenB_zero
    have h_not_identical : ¬ tokenA = (0 : Address) := by
      simpa using h_distinct
    simp [factory_createPair_run_revert_zero_address, createPair,
      UniswapV2FactoryBase.createPair, Verity.require, Contract.run,
      Verity.bind, Bind.bind, h_not_identical]
-- tama: discharges=factory_createPair_run_revert_duplicates
theorem createPair_run_revert_duplicates
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_run_revert_duplicates tokenA tokenB s := by
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
    simp [factory_createPair_run_revert_duplicates, createPair,
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
    simp [factory_createPair_run_revert_duplicates, createPair,
      UniswapV2FactoryBase.createPair, getMapping2, Verity.require, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure, h_distinct, h_tokenA_nonzero,
      h_tokenB_nonzero, h_tokenA_not_zero, h_tokenB_not_zero, h_sort, h_sort_raw,
      h_existing_branch]
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
-- tama: discharges=factory_createPair_success_implies_pre_create_guards
theorem createPair_success_implies_pre_create_guards
    (tokenA tokenB : Address) (s : ContractState)
    (result : ContractResult Address) :
  factory_createPair_success_implies_pre_create_guards tokenA tokenB s result := by
  intro h_run h_success
  rcases h_success with ⟨pair, h_success⟩
  have h_distinct : tokenA ≠ tokenB := by
    intro h_same
    have h_revert := createPair_run_revert_identical_addresses tokenA tokenB s h_same
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success
  have h_tokenA_nonzero : tokenA ≠ zeroAddress := by
    intro h_zero
    have h_revert := createPair_run_revert_zero_address tokenA tokenB s h_distinct (Or.inl h_zero)
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success
  have h_tokenB_nonzero : tokenB ≠ zeroAddress := by
    intro h_zero
    have h_revert := createPair_run_revert_zero_address tokenA tokenB s h_distinct (Or.inr h_zero)
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success
  have h_absent :
      s.storageMap2 pairForSlot.slot
        (factoryToken0 tokenA tokenB) (factoryToken1 tokenA tokenB) = 0 := by
    by_contra h_existing_not
    have h_existing :
        s.storageMap2 pairForSlot.slot
          (if addressToWord tokenA < addressToWord tokenB then tokenA else tokenB)
          (if addressToWord tokenA < addressToWord tokenB then tokenB else tokenA) ≠ 0 := by
      simpa [factoryToken0, factoryToken1] using h_existing_not
    have h_revert :=
      createPair_run_revert_duplicates tokenA tokenB s
        h_distinct h_tokenA_nonzero h_tokenB_nonzero h_existing
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success
  exact ⟨h_distinct, h_tokenA_nonzero, h_tokenB_nonzero, h_absent⟩
-- tama: discharges=factory_concrete_world_length_matches_storage
theorem concrete_world_length_matches_storage
    (s : ContractState) (w : FactoryWorldState) :
  factory_concrete_world_length_matches_storage s w := by
  intro h_match
  exact h_match.1
private theorem concrete_world_lookup_matches_storage_aux
    (s : ContractState) (w : FactoryWorldState)
    (tokenA tokenB pair : Address) :
    FactoryWorldMatchesStorage s w →
      FactoryWorldContainsPair w tokenA tokenB pair →
        wordToAddress (s.storageMap2 pairForSlot.slot tokenA tokenB) = pair := by
  intro h_match h_contains
  rcases h_match with ⟨_h_count, h_entries, _h_array⟩
  rcases h_contains with ⟨entry, h_entry, h_tokens, h_pair⟩
  rcases h_entries entry h_entry with ⟨h_forward, h_reverse⟩
  subst pair
  rcases h_tokens with h_forward_tokens | h_reverse_tokens
  · rcases h_forward_tokens with ⟨h_token0, h_token1⟩
    subst tokenA
    subst tokenB
    exact h_forward
  · rcases h_reverse_tokens with ⟨h_token0, h_token1⟩
    subst tokenB
    subst tokenA
    exact h_reverse
-- tama: discharges=factory_concrete_world_allPairs_matches_storage
theorem concrete_world_allPairs_matches_storage
    (s : ContractState) (w : FactoryWorldState)
    (index : Nat) (entry : FactoryWorldPair) :
  factory_concrete_world_allPairs_matches_storage s w index entry := by
  intro h_match h_get
  exact h_match.2.2 index entry h_get
private theorem createPair_success_preserves_pair_lookup_decode_of_ne
    (tokenA tokenB x y : Address) (s : ContractState) :
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot
          (factoryToken0 tokenA tokenB) (factoryToken1 tokenA tokenB) = 0 →
          wordToAddress (factoryCreate2Word tokenA tokenB) ≠ zeroAddress →
            (s.storage allPairsLengthSlot.slot).val + 1 ≤
              Verity.Stdlib.Math.MAX_UINT256 →
              (x ≠ factoryToken0 tokenA tokenB ∨
                y ≠ factoryToken1 tokenA tokenB) →
                (x ≠ factoryToken1 tokenA tokenB ∨
                  y ≠ factoryToken0 tokenA tokenB) →
                  wordToAddress
                      (((createPair tokenA tokenB).run s).snd.storageMap2
                        pairForSlot.slot x y) =
                    wordToAddress (s.storageMap2 pairForSlot.slot x y) := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent h_pair_nonzero
    h_len_ok h_ne_forward h_ne_reverse
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
    have h_ne_forward_branch : x ≠ tokenA ∨ y ≠ tokenB := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_ne_forward
    have h_ne_reverse_branch : x ≠ tokenB ∨ y ≠ tokenA := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_ne_reverse
    have h_not_forward : ¬ (x = tokenA ∧ y = tokenB) := by
      intro hxy
      rcases h_ne_forward_branch with hx | hy
      · exact hx hxy.1
      · exact hy hxy.2
    have h_not_reverse : ¬ (x = tokenB ∧ y = tokenA) := by
      intro hxy
      rcases h_ne_reverse_branch with hx | hy
      · exact hx hxy.1
      · exact hy hxy.2
    simp [createPair, UniswapV2FactoryBase.createPair, getMapping2,
      setMapping2, getStorage, setStorage, getMappingUint, setMappingUint,
      Verity.require, Contract.run, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contracts.emit, emitEvent, Verity.Stdlib.Math.requireSomeUint,
      h_distinct, h_tokenA_nonzero, h_tokenB_nonzero, h_tokenA_not_zero,
      h_tokenB_not_zero, h_sort, h_sort_raw, h_absent_branch,
      h_pair_nonzero_branch, h_create2_guard, h_safe_len, h_not_forward,
      h_not_reverse]
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
    have h_ne_forward_branch : x ≠ tokenB ∨ y ≠ tokenA := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_ne_forward
    have h_ne_reverse_branch : x ≠ tokenA ∨ y ≠ tokenB := by
      simpa [factoryToken0, factoryToken1, addressToWord, h_sort, h_sort_raw]
        using h_ne_reverse
    have h_not_forward : ¬ (x = tokenB ∧ y = tokenA) := by
      intro hxy
      rcases h_ne_forward_branch with hx | hy
      · exact hx hxy.1
      · exact hy hxy.2
    have h_not_reverse : ¬ (x = tokenA ∧ y = tokenB) := by
      intro hxy
      rcases h_ne_reverse_branch with hx | hy
      · exact hx hxy.1
      · exact hy hxy.2
    simp [createPair, UniswapV2FactoryBase.createPair, getMapping2,
      setMapping2, getStorage, setStorage, getMappingUint, setMappingUint,
      Verity.require, Contract.run, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contracts.emit, emitEvent, Verity.Stdlib.Math.requireSomeUint,
      h_distinct, h_tokenA_nonzero, h_tokenB_nonzero, h_tokenA_not_zero,
      h_tokenB_not_zero, h_sort, h_sort_raw, h_absent_branch,
      h_pair_nonzero_branch, h_create2_guard, h_safe_len, h_not_forward,
      h_not_reverse]
private theorem createPair_success_preserves_allPairs_index_decode_of_ne
    (tokenA tokenB : Address) (s : ContractState) (index : Nat) :
  tokenA ≠ tokenB →
    tokenA ≠ zeroAddress →
      tokenB ≠ zeroAddress →
        s.storageMap2 pairForSlot.slot
          (factoryToken0 tokenA tokenB) (factoryToken1 tokenA tokenB) = 0 →
          wordToAddress (factoryCreate2Word tokenA tokenB) ≠ zeroAddress →
            (s.storage allPairsLengthSlot.slot).val + 1 ≤
              Verity.Stdlib.Math.MAX_UINT256 →
              Core.Uint256.ofNat index ≠ s.storage allPairsLengthSlot.slot →
                wordToAddress
                    (((createPair tokenA tokenB).run s).snd.storageMapUint
                      allPairsSlot.slot (Core.Uint256.ofNat index)) =
                  wordToAddress
                    (s.storageMapUint allPairsSlot.slot (Core.Uint256.ofNat index)) := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent h_pair_nonzero
    h_len_ok h_key_ne
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
    simp [createPair, UniswapV2FactoryBase.createPair, getMapping2,
      setMapping2, getStorage, setStorage, getMappingUint, setMappingUint,
      Verity.require, Contract.run, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contracts.emit, emitEvent, Verity.Stdlib.Math.requireSomeUint,
      h_distinct, h_tokenA_nonzero, h_tokenB_nonzero, h_tokenA_not_zero,
      h_tokenB_not_zero, h_sort, h_sort_raw, h_absent_branch,
      h_pair_nonzero_branch, h_create2_guard, h_safe_len, h_key_ne]
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
    simp [createPair, UniswapV2FactoryBase.createPair, getMapping2,
      setMapping2, getStorage, setStorage, getMappingUint, setMappingUint,
      Verity.require, Contract.run, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contracts.emit, emitEvent, Verity.Stdlib.Math.requireSomeUint,
      h_distinct, h_tokenA_nonzero, h_tokenB_nonzero, h_tokenA_not_zero,
      h_tokenB_not_zero, h_sort, h_sort_raw, h_absent_branch,
      h_pair_nonzero_branch, h_create2_guard, h_safe_len, h_key_ne]
-- tama: discharges=factory_createPair_success_preserves_concrete_world_match
theorem createPair_success_preserves_concrete_world_match
    (tokenA tokenB : Address) (s : ContractState)
    (before : FactoryWorldState) :
  factory_createPair_success_preserves_concrete_world_match tokenA tokenB s before := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_good h_match h_absent
    h_absent_world h_pair_nonzero h_len_ok _h_run
  rcases h_good with ⟨h_entries_good, _h_no_duplicates, h_count_length⟩
  rcases h_match with ⟨h_count_match, h_entries_match, h_array_match⟩
  have h_success :=
    createPair_success_updates_storage_and_emits tokenA tokenB s
      h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent
      h_pair_nonzero h_len_ok
  rcases h_success with
    ⟨_h_success_run, h_new_forward, h_new_reverse, h_new_array,
      h_length, _h_event⟩
  have h_add_lt :
      (s.storage allPairsLengthSlot.slot).val + 1 <
        Core.Uint256.modulus := by
    rw [← Core.Uint256.max_uint256_succ_eq_modulus]
    exact Nat.lt_succ_of_le h_len_ok
  have h_len_after_val :
      ((s.storage allPairsLengthSlot.slot + 1 : Uint256) : Nat) =
        (s.storage allPairsLengthSlot.slot).val + 1 := by
    simpa using
      (Core.Uint256.add_eq_of_lt
        (a := s.storage allPairsLengthSlot.slot) (b := (1 : Uint256)) h_add_lt)
  have h_len_after_val_left :
      ((1 : Uint256) + s.storage allPairsLengthSlot.slot : Uint256).val =
        1 + (s.storage allPairsLengthSlot.slot).val := by
    have h_add_lt_left :
        (1 : Uint256).val + (s.storage allPairsLengthSlot.slot).val <
          Core.Uint256.modulus := by
      simpa [Core.Uint256.val_one, Nat.add_comm] using h_add_lt
    simpa using
      (Core.Uint256.add_eq_of_lt
        (a := (1 : Uint256)) (b := s.storage allPairsLengthSlot.slot)
        h_add_lt_left)
  have h_new_good :
      FactoryWorldPairGood {
        token0 := factoryToken0 tokenA tokenB
        token1 := factoryToken1 tokenA tokenB
        pair := wordToAddress (factoryCreate2Word tokenA tokenB)
      } := by
    by_cases h_sort : addressToWord tokenA < addressToWord tokenB
    · have h_sort_raw :
          Core.Address.toNat tokenA % Core.Uint256.modulus <
            Core.Address.toNat tokenB % Core.Uint256.modulus := by
        simpa [addressToWord] using h_sort
      simpa [FactoryWorldPairGood, factoryToken0, factoryToken1,
        factoryCreate2Word, addressToWord, h_sort, h_sort_raw] using
        (show FactoryWorldPairGood {
          token0 := tokenA
          token1 := tokenB
          pair := wordToAddress
            (externalCall "uniswapV2PairCreate2" [tokenA, tokenB])
        } from
          ⟨h_distinct, h_tokenA_nonzero, h_tokenB_nonzero, h_sort,
            (by
              simpa [factoryCreate2Word, factoryToken0, factoryToken1,
                addressToWord, h_sort, h_sort_raw] using h_pair_nonzero)⟩)
    · have h_sort_raw :
          ¬ Core.Address.toNat tokenA % Core.Uint256.modulus <
            Core.Address.toNat tokenB % Core.Uint256.modulus := by
        simpa [addressToWord] using h_sort
      have h_reverse_sort : addressToWord tokenB < addressToWord tokenA :=
        addressToWord_reverse_lt_of_not_lt h_distinct h_sort
      have h_distinct_symm : tokenB ≠ tokenA := by
        exact fun h => h_distinct h.symm
      simpa [FactoryWorldPairGood, factoryToken0, factoryToken1,
        factoryCreate2Word, addressToWord, h_sort, h_sort_raw] using
        (show FactoryWorldPairGood {
          token0 := tokenB
          token1 := tokenA
          pair := wordToAddress
            (externalCall "uniswapV2PairCreate2" [tokenB, tokenA])
        } from
          ⟨h_distinct_symm, h_tokenB_nonzero, h_tokenA_nonzero,
            h_reverse_sort,
            (by
              simpa [factoryCreate2Word, factoryToken0, factoryToken1,
                addressToWord, h_sort, h_sort_raw] using h_pair_nonzero)⟩)
  refine ⟨?_, ?_, ?_⟩
  · rw [h_length]
    simp [factoryLengthAfter]
    rw [h_len_after_val_left, ← h_count_match]
    omega
  · intro entry h_entry_after
    rcases List.mem_append.mp h_entry_after with h_entry_old | h_entry_new
    · rcases h_entries_match entry h_entry_old with
        ⟨h_old_forward, h_old_reverse⟩
      have h_entry_good := h_entries_good entry h_entry_old
      have h_not_forward :
          entry.token0 ≠ factoryToken0 tokenA tokenB ∨
            entry.token1 ≠ factoryToken1 tokenA tokenB :=
        h_absent_world entry h_entry_old
      have h_not_reverse :
          entry.token0 ≠ factoryToken1 tokenA tokenB ∨
            entry.token1 ≠ factoryToken0 tokenA tokenB :=
        factoryWorldEntry_not_reverse_pair entry
          {
            token0 := factoryToken0 tokenA tokenB
            token1 := factoryToken1 tokenA tokenB
            pair := wordToAddress (factoryCreate2Word tokenA tokenB)
          }
          h_entry_good h_new_good
      constructor
      · calc
          wordToAddress
              (((createPair tokenA tokenB).run s).snd.storageMap2
                pairForSlot.slot entry.token0 entry.token1)
              =
            wordToAddress (s.storageMap2 pairForSlot.slot entry.token0 entry.token1) :=
              createPair_success_preserves_pair_lookup_decode_of_ne
                tokenA tokenB entry.token0 entry.token1 s
                h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent
                h_pair_nonzero h_len_ok h_not_forward h_not_reverse
          _ = entry.pair := h_old_forward
      · have h_rev_not_forward :
            entry.token1 ≠ factoryToken0 tokenA tokenB ∨
              entry.token0 ≠ factoryToken1 tokenA tokenB := by
          rcases h_not_reverse with h0 | h1
          · exact Or.inr h0
          · exact Or.inl h1
        have h_rev_not_reverse :
            entry.token1 ≠ factoryToken1 tokenA tokenB ∨
              entry.token0 ≠ factoryToken0 tokenA tokenB := by
          rcases h_not_forward with h0 | h1
          · exact Or.inr h0
          · exact Or.inl h1
        calc
          wordToAddress
              (((createPair tokenA tokenB).run s).snd.storageMap2
                pairForSlot.slot entry.token1 entry.token0)
              =
            wordToAddress (s.storageMap2 pairForSlot.slot entry.token1 entry.token0) :=
              createPair_success_preserves_pair_lookup_decode_of_ne
                tokenA tokenB entry.token1 entry.token0 s
                h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent
                h_pair_nonzero h_len_ok h_rev_not_forward h_rev_not_reverse
          _ = entry.pair := h_old_reverse
    · simp at h_entry_new
      rcases h_entry_new with h_entry_new
      rw [h_entry_new]
      constructor
      · simpa using congrArg wordToAddress h_new_forward
      · simpa using congrArg wordToAddress h_new_reverse
  · intro index entry h_get_after
    rcases list_get?_append_singleton_cases h_get_after with h_get_old | h_get_new
    · have h_old_array := h_array_match index entry h_get_old
      have h_index_lt := list_get?_some_lt h_get_old
      have h_index_lt_storage :
          index < (s.storage allPairsLengthSlot.slot).val := by
        rw [← h_count_match, h_count_length]
        exact h_index_lt
      have h_key_ne :
          Core.Uint256.ofNat index ≠ s.storage allPairsLengthSlot.slot :=
        uint256_ofNat_ne_of_lt_val h_index_lt_storage
      calc
        wordToAddress
            (((createPair tokenA tokenB).run s).snd.storageMapUint
              allPairsSlot.slot (Core.Uint256.ofNat index))
            =
          wordToAddress
            (s.storageMapUint allPairsSlot.slot (Core.Uint256.ofNat index)) :=
            createPair_success_preserves_allPairs_index_decode_of_ne
              tokenA tokenB s index h_distinct h_tokenA_nonzero
              h_tokenB_nonzero h_absent h_pair_nonzero h_len_ok h_key_ne
        _ = entry.pair := h_old_array
    · rcases h_get_new with ⟨h_index, h_entry⟩
      subst index
      subst entry
      have h_key_eq :
          Core.Uint256.ofNat before.pairs.length =
            s.storage allPairsLengthSlot.slot := by
        apply uint256_ofNat_eq_of_eq_val
        rw [← h_count_match, h_count_length]
      change
        wordToAddress
          (((createPair tokenA tokenB).run s).snd.storageMapUint
            allPairsSlot.slot (Core.Uint256.ofNat before.pairs.length)) =
          wordToAddress (factoryCreate2Word tokenA tokenB)
      rw [h_key_eq]
      simpa using congrArg wordToAddress h_new_array
private theorem createPair_success_adds_decoded_lookup_aux
    (tokenA tokenB : Address) (s : ContractState) :
    tokenA ≠ tokenB →
      tokenA ≠ zeroAddress →
        tokenB ≠ zeroAddress →
          s.storageMap2 pairForSlot.slot
              (factoryToken0 tokenA tokenB) (factoryToken1 tokenA tokenB) = 0 →
            wordToAddress (factoryCreate2Word tokenA tokenB) ≠ zeroAddress →
              (s.storage allPairsLengthSlot.slot).val + 1 ≤
                Verity.Stdlib.Math.MAX_UINT256 →
                (createPair tokenA tokenB).run s =
                  ContractResult.success
                    (wordToAddress (factoryCreate2Word tokenA tokenB))
                    ((createPair tokenA tokenB).run s).snd →
                  wordToAddress
                      (((createPair tokenA tokenB).run s).snd.storageMap2
                        pairForSlot.slot tokenA tokenB) =
                      wordToAddress (factoryCreate2Word tokenA tokenB) ∧
                  wordToAddress
                      (((createPair tokenA tokenB).run s).snd.storageMap2
                        pairForSlot.slot tokenB tokenA) =
                      wordToAddress (factoryCreate2Word tokenA tokenB) := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent
    h_pair_nonzero h_len_ok _h_run
  have h_success :=
    createPair_success_updates_storage_and_emits tokenA tokenB s
      h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent
      h_pair_nonzero h_len_ok
  rcases h_success with
    ⟨_h_success_run, h_new_forward, h_new_reverse, _h_new_array,
      _h_length, _h_event⟩
  by_cases h_sort : addressToWord tokenA < addressToWord tokenB
  · have h_sort_raw :
        Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    constructor
    · simpa [factoryToken0, factoryToken1, factoryCreate2Word,
        addressToWord, h_sort, h_sort_raw] using
        congrArg wordToAddress h_new_forward
    · simpa [factoryToken0, factoryToken1, factoryCreate2Word,
        addressToWord, h_sort, h_sort_raw] using
        congrArg wordToAddress h_new_reverse
  · have h_sort_raw :
        ¬ Core.Address.toNat tokenA % Core.Uint256.modulus <
          Core.Address.toNat tokenB % Core.Uint256.modulus := by
      simpa [addressToWord] using h_sort
    constructor
    · simpa [factoryToken0, factoryToken1, factoryCreate2Word,
        addressToWord, h_sort, h_sort_raw] using
        congrArg wordToAddress h_new_reverse
    · simpa [factoryToken0, factoryToken1, factoryCreate2Word,
        addressToWord, h_sort, h_sort_raw] using
        congrArg wordToAddress h_new_forward
-- tama: discharges=factory_createPair_success_getPair_views_return_new_pair
theorem createPair_success_getPair_views_return_new_pair
    (tokenA tokenB : Address) (s : ContractState) :
  factory_createPair_success_getPair_views_return_new_pair tokenA tokenB s := by
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent
    h_pair_nonzero h_len_ok h_run
  have h_lookup :=
    createPair_success_adds_decoded_lookup_aux tokenA tokenB s
      h_distinct h_tokenA_nonzero h_tokenB_nonzero h_absent
      h_pair_nonzero h_len_ok h_run
  rcases h_lookup with ⟨h_forward, h_reverse⟩
  constructor
  · simpa [factory_createPair_success_getPair_views_return_new_pair,
      getPair, UniswapV2FactoryBase.getPair, getMapping2, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure] using h_forward
  · simpa [factory_createPair_success_getPair_views_return_new_pair,
      getPair, UniswapV2FactoryBase.getPair, getMapping2, Contract.run,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure] using h_reverse
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
-- tama: discharges=factory_createPair_success_preserves_good
theorem createPair_success_preserves_good
    (tokenA tokenB : Address) (s : ContractState)
    (before : FactoryWorldState) :
  factory_createPair_success_preserves_good tokenA tokenB s before := by
  dsimp [factory_createPair_success_preserves_good]
  intro h_distinct h_tokenA_nonzero h_tokenB_nonzero h_good h_count
    h_absent h_absent_world h_pair_nonzero h_len_ok h_run
  have h_step :=
    createPair_success_matches_closed_world_step tokenA tokenB s before
      h_distinct h_tokenA_nonzero h_tokenB_nonzero h_good h_count
      h_absent h_absent_world h_pair_nonzero h_len_ok h_run
  exact factoryWorldStep_preserves_good
    (FactoryWorldAction.createPair tokenA tokenB
      (wordToAddress (factoryCreate2Word tokenA tokenB)))
    before
    { pairs := before.pairs ++ [{
        token0 := factoryToken0 tokenA tokenB
        token1 := factoryToken1 tokenA tokenB
        pair := wordToAddress (factoryCreate2Word tokenA tokenB)
      }]
      pairCount := before.pairCount + 1 }
    h_good h_step
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
private theorem factoryWorldPath_preserves_reachability
    {before after : FactoryWorldState} :
  FactoryWorldReachable before →
    FactoryWorldPath before after →
      FactoryWorldReachable after := by
  intro h_reachable h_path
  induction h_path with
  | refl =>
      exact h_reachable
  | step action h_prefix h_step ih =>
      exact FactoryWorldReachable.step action ih h_step
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
private theorem factoryWorldPath_append_only
    {before after : FactoryWorldState} :
  FactoryWorldPath before after →
    ∃ suffix,
      after.pairs = before.pairs ++ suffix ∧
      after.pairCount = before.pairCount + suffix.length := by
  intro h_path
  induction h_path with
  | refl =>
      refine ⟨[], ?_, ?_⟩
      · simp
      · simp
  | step action h_prefix h_step ih =>
      cases action with
      | createPair tokenA tokenB pair =>
          rcases ih with ⟨suffix, h_pairs_prefix, h_count_prefix⟩
          simp [FactoryWorldStep, FactoryWorldCreatePairStep] at h_step
          rcases h_step with ⟨_h_distinct, _h_tokenA_nonzero, _h_tokenB_nonzero,
            _h_token_order, _h_new_good, _h_absent, h_pairs_step, h_count_step⟩
          refine ⟨suffix ++ [{
              token0 := factoryToken0 tokenA tokenB
              token1 := factoryToken1 tokenA tokenB
              pair := pair
            }], ?_, ?_⟩
          · rw [h_pairs_step, h_pairs_prefix]
            simp [List.append_assoc]
          · rw [h_count_step, h_count_prefix]
            simp
            omega
private theorem factoryConcreteCreateStep_preserves_world_match
    (tokenA tokenB : Address)
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) :
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryConcreteCreateStep tokenA tokenB sBefore sAfter wBefore wAfter →
        FactoryWorldGood wAfter ∧
        FactoryWorldMatchesStorage sAfter wAfter := by
  intro h_good h_match h_concrete
  dsimp [FactoryConcreteCreateStep] at h_concrete
  rcases h_concrete with ⟨h_absent, h_len_ok, h_run, h_world_step⟩
  have h_good_after :
      FactoryWorldGood wAfter :=
    factoryWorldStep_preserves_good
      (FactoryWorldAction.createPair tokenA tokenB
        (wordToAddress (factoryCreate2Word tokenA tokenB)))
      wBefore wAfter h_good h_world_step
  dsimp [FactoryWorldStep, FactoryWorldCreatePairStep] at h_world_step
  rcases h_world_step with
    ⟨h_distinct, h_tokenA_nonzero, h_tokenB_nonzero, _h_token_order,
      h_new_good, h_absent_world, h_pairs, h_count⟩
  rcases h_new_good with
    ⟨_h_new_distinct, _h_new_token0_nonzero, _h_new_token1_nonzero,
      _h_new_sorted, h_pair_nonzero⟩
  have h_run_success :
      (createPair tokenA tokenB).run sBefore =
        ContractResult.success
          (wordToAddress (factoryCreate2Word tokenA tokenB))
          sAfter := by
    simpa [createPair, UniswapV2FactoryBase.createPair, factoryCreate2Word,
      factoryToken0, factoryToken1, wordToAddress] using h_run
  have h_run_expected :
      (createPair tokenA tokenB).run sBefore =
        ContractResult.success
          (wordToAddress (factoryCreate2Word tokenA tokenB))
          ((createPair tokenA tokenB).run sBefore).snd := by
    rw [h_run_success]
    simp
  have h_state_eq :
      ((createPair tokenA tokenB).run sBefore).snd = sAfter := by
    rw [h_run_success]
    simp
  have h_after_eq :
      wAfter =
        { pairs := wBefore.pairs ++ [{
            token0 := factoryToken0 tokenA tokenB
            token1 := factoryToken1 tokenA tokenB
            pair := wordToAddress (factoryCreate2Word tokenA tokenB)
          }]
          pairCount := wBefore.pairCount + 1 } := by
    cases wAfter with
    | mk pairs pairCount =>
        simp at h_pairs h_count ⊢
        exact ⟨h_pairs, h_count⟩
  have h_match_after :
      FactoryWorldMatchesStorage
        ((createPair tokenA tokenB).run sBefore).snd
        { pairs := wBefore.pairs ++ [{
            token0 := factoryToken0 tokenA tokenB
            token1 := factoryToken1 tokenA tokenB
            pair := wordToAddress (factoryCreate2Word tokenA tokenB)
          }]
          pairCount := wBefore.pairCount + 1 } :=
    createPair_success_preserves_concrete_world_match
      tokenA tokenB sBefore wBefore
      h_distinct h_tokenA_nonzero h_tokenB_nonzero h_good h_match
      h_absent h_absent_world h_pair_nonzero h_len_ok h_run_expected
  constructor
  · exact h_good_after
  · rw [← h_state_eq, h_after_eq]
    exact h_match_after
private theorem factoryConcreteCreatePath_preserves_match
    {sBefore sAfter : ContractState}
    {wBefore wAfter : FactoryWorldState} :
  FactoryWorldGood wBefore →
    FactoryWorldMatchesStorage sBefore wBefore →
      FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
        FactoryWorldGood wAfter ∧
        FactoryWorldMatchesStorage sAfter wAfter := by
  intro h_good h_match h_path
  induction h_path with
  | refl =>
      exact ⟨h_good, h_match⟩
  | step tokenA tokenB h_prefix h_step ih =>
      have h_prefix_result := ih h_good h_match
      exact factoryConcreteCreateStep_preserves_world_match
        tokenA tokenB _ _ _ _
        h_prefix_result.1 h_prefix_result.2 h_step
private theorem factoryConcreteCreatePath_matches_world_path
    {sBefore sAfter : ContractState}
    {wBefore wAfter : FactoryWorldState} :
  FactoryConcreteCreatePath sBefore wBefore sAfter wAfter →
    FactoryWorldPath wBefore wAfter := by
  intro h_path
  induction h_path with
  | refl =>
      exact FactoryWorldPath.refl _
  | step tokenA tokenB _h_prefix h_step ih =>
      dsimp [FactoryConcreteCreateStep] at h_step
      rcases h_step with ⟨_h_absent, _h_len_ok, _h_run, h_world_step⟩
      exact FactoryWorldPath.step
        (FactoryWorldAction.createPair tokenA tokenB
          (wordToAddress (factoryCreate2Word tokenA tokenB)))
        ih h_world_step
-- tama: discharges=factory_concrete_create_path_preserves_world_match
theorem concrete_create_path_preserves_world_match
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) :
  factory_concrete_create_path_preserves_world_match
    sBefore sAfter wBefore wAfter := by
  exact factoryConcreteCreatePath_preserves_match
-- tama: discharges=factory_concrete_create_path_preserves_existing_decoded_lookup
theorem concrete_create_path_preserves_existing_decoded_lookup
    (existing0 existing1 existingPair : Address)
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) :
  factory_concrete_create_path_preserves_existing_decoded_lookup
    existing0 existing1 existingPair sBefore sAfter wBefore wAfter := by
  intro h_good h_match h_existing h_path
  have h_final :=
    factoryConcreteCreatePath_preserves_match
      h_good h_match h_path
  have h_world_path :=
    factoryConcreteCreatePath_matches_world_path h_path
  have h_existing_after :=
    factoryWorldPath_preserves_existing_pair h_existing h_world_path
  exact concrete_world_lookup_matches_storage_aux
    sAfter wAfter existing0 existing1 existingPair
    h_final.2 h_existing_after
-- tama: discharges=factory_concrete_create_path_preserves_existing_allPairs_entry
theorem concrete_create_path_preserves_existing_allPairs_entry
    (index : Nat) (entry : FactoryWorldPair)
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) :
  factory_concrete_create_path_preserves_existing_allPairs_entry
    index entry sBefore sAfter wBefore wAfter := by
  intro h_good h_match h_get h_path
  have h_final :=
    factoryConcreteCreatePath_preserves_match
      h_good h_match h_path
  have h_world_path :=
    factoryConcreteCreatePath_matches_world_path h_path
  rcases factoryWorldPath_append_only h_world_path with
    ⟨suffix, h_pairs, _h_count⟩
  have h_get_after :
      wAfter.pairs[index]? = some entry := by
    rw [h_pairs]
    exact list_get?_append_left_of_some h_get
  exact concrete_world_allPairs_matches_storage
    sAfter wAfter index entry h_final.2 h_get_after
-- tama: discharges=factory_concrete_same_length_create_path_preserves_world
theorem concrete_same_length_create_path_preserves_world
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) :
  factory_concrete_same_length_create_path_preserves_world
    sBefore sAfter wBefore wAfter := by
  intro h_good h_match h_path h_same_length
  have h_final :=
    factoryConcreteCreatePath_preserves_match
      h_good h_match h_path
  have h_world_path :=
    factoryConcreteCreatePath_matches_world_path h_path
  have h_same_count :
      wBefore.pairCount = wAfter.pairCount := by
    rw [h_match.1, h_final.2.1]
    exact h_same_length
  rcases factoryWorldPath_append_only h_world_path with
    ⟨suffix, h_pairs, h_count⟩
  have h_suffix_length_zero : suffix.length = 0 := by
    rw [h_count] at h_same_count
    omega
  have h_suffix_nil : suffix = [] :=
    List.length_eq_zero_iff.mp h_suffix_length_zero
  have h_same_pairs : wAfter.pairs = wBefore.pairs := by
    rw [h_pairs, h_suffix_nil]
    simp
  cases wBefore with
  | mk pairsBefore countBefore =>
      cases wAfter with
      | mk pairsAfter countAfter =>
          dsimp at h_same_pairs h_same_count
          subst pairsAfter
          subst countAfter
          rfl
-- tama: discharges=factory_closed_world_path_preserves_reachability
theorem closed_world_path_preserves_reachability
    (before after : FactoryWorldState) :
  factory_closed_world_path_preserves_reachability before after := by
  exact factoryWorldPath_preserves_reachability
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
-- tama: discharges=factory_closed_world_reachable_lookup_is_valid
theorem closed_world_reachable_lookup_is_valid
    (w : FactoryWorldState) (tokenA tokenB pair : Address) :
  factory_closed_world_reachable_lookup_is_valid w tokenA tokenB pair := by
  intro h_reachable h_contains
  rcases h_contains with ⟨entry, h_entry, h_tokens, h_pair⟩
  rcases factoryWorldReachable_good w h_reachable with
    ⟨h_entries_good, _h_no_duplicates, _h_count⟩
  rcases h_entries_good entry h_entry with
    ⟨h_distinct, h_token0_nonzero, h_token1_nonzero, _h_sorted, h_pair_nonzero⟩
  subst pair
  rcases h_tokens with h_forward | h_reverse
  · rcases h_forward with ⟨h_token0, h_token1⟩
    subst tokenA
    subst tokenB
    exact ⟨h_pair_nonzero, h_distinct, h_token0_nonzero, h_token1_nonzero⟩
  · rcases h_reverse with ⟨h_token0, h_token1⟩
    subst tokenA
    subst tokenB
    exact ⟨h_pair_nonzero, (fun h => h_distinct h.symm),
      h_token1_nonzero, h_token0_nonzero⟩
-- tama: discharges=factory_concrete_reachable_lookup_is_valid
theorem concrete_reachable_lookup_is_valid
    (s : ContractState) (w : FactoryWorldState)
    (tokenA tokenB pair : Address) :
  factory_concrete_reachable_lookup_is_valid s w tokenA tokenB pair := by
  intro h_reachable h_match h_contains
  have h_lookup :=
    concrete_world_lookup_matches_storage_aux s w tokenA tokenB pair
      h_match h_contains
  have h_valid :=
    closed_world_reachable_lookup_is_valid w tokenA tokenB pair
      h_reachable h_contains
  exact ⟨h_lookup, h_valid⟩
-- tama: discharges=factory_concrete_create_path_reachable_lookup_is_valid
theorem concrete_create_path_reachable_lookup_is_valid
    (tokenA tokenB pair : Address)
    (sBefore sAfter : ContractState)
    (wBefore wAfter : FactoryWorldState) :
  factory_concrete_create_path_reachable_lookup_is_valid
    tokenA tokenB pair sBefore sAfter wBefore wAfter := by
  intro h_reachable h_match h_path h_contains
  have h_good_before := factoryWorldReachable_good wBefore h_reachable
  have h_final :=
    factoryConcreteCreatePath_preserves_match
      h_good_before h_match h_path
  have h_world_path :=
    factoryConcreteCreatePath_matches_world_path h_path
  have h_reachable_after :=
    factoryWorldPath_preserves_reachability h_reachable h_world_path
  exact concrete_reachable_lookup_is_valid sAfter wAfter tokenA tokenB pair
    h_reachable_after h_final.2 h_contains
-- tama: discharges=factory_closed_world_unordered_pair_address_unique
theorem closed_world_unordered_pair_address_unique
    (w : FactoryWorldState) (tokenA tokenB pairA pairB : Address) :
  factory_closed_world_unordered_pair_address_unique w tokenA tokenB pairA pairB := by
  intro h_reachable h_contains_a h_contains_b
  rcases h_contains_a with ⟨entryA, h_entry_a, h_tokens_a, h_pair_a⟩
  rcases h_contains_b with ⟨entryB, h_entry_b, h_tokens_b, h_pair_b⟩
  have h_good := factoryWorldReachable_good w h_reachable
  have h_no_duplicates := h_good.2.1
  have h_entry_a_good := h_good.1 entryA h_entry_a
  have h_entry_b_good := h_good.1 entryB h_entry_b
  have h_same_tokens :
      entryA.token0 = entryB.token0 ∧ entryA.token1 = entryB.token1 := by
    rcases h_tokens_a with h_a_forward | h_a_reverse
    · rcases h_tokens_b with h_b_forward | h_b_reverse
      · exact ⟨h_a_forward.1.trans h_b_forward.1.symm,
          h_a_forward.2.trans h_b_forward.2.symm⟩
      · rcases h_entry_a_good with
          ⟨_ha_distinct, _ha_nonzero0, _ha_nonzero1, h_a_order, _ha_pair⟩
        rcases h_entry_b_good with
          ⟨_hb_distinct, _hb_nonzero0, _hb_nonzero1, h_b_order, _hb_pair⟩
        rw [h_a_forward.1, h_a_forward.2] at h_a_order
        rw [h_b_reverse.1, h_b_reverse.2] at h_b_order
        have h_a_order_val :
            (addressToWord tokenA).val < (addressToWord tokenB).val := by
          simpa [Verity.Core.Uint256.lt_def] using h_a_order
        have h_b_order_val :
            (addressToWord tokenB).val < (addressToWord tokenA).val := by
          simpa [Verity.Core.Uint256.lt_def] using h_b_order
        exact False.elim ((Nat.lt_asymm h_a_order_val) h_b_order_val)
    · rcases h_tokens_b with h_b_forward | h_b_reverse
      · rcases h_entry_a_good with
          ⟨_ha_distinct, _ha_nonzero0, _ha_nonzero1, h_a_order, _ha_pair⟩
        rcases h_entry_b_good with
          ⟨_hb_distinct, _hb_nonzero0, _hb_nonzero1, h_b_order, _hb_pair⟩
        rw [h_a_reverse.1, h_a_reverse.2] at h_a_order
        rw [h_b_forward.1, h_b_forward.2] at h_b_order
        have h_a_order_val :
            (addressToWord tokenB).val < (addressToWord tokenA).val := by
          simpa [Verity.Core.Uint256.lt_def] using h_a_order
        have h_b_order_val :
            (addressToWord tokenA).val < (addressToWord tokenB).val := by
          simpa [Verity.Core.Uint256.lt_def] using h_b_order
        exact False.elim ((Nat.lt_asymm h_a_order_val) h_b_order_val)
      · exact ⟨h_a_reverse.1.trans h_b_reverse.1.symm,
          h_a_reverse.2.trans h_b_reverse.2.symm⟩
  have h_entry_eq :
      entryA = entryB :=
    h_no_duplicates entryA entryB h_entry_a h_entry_b
      h_same_tokens.1 h_same_tokens.2
  calc
    pairA = entryA.pair := h_pair_a.symm
    _ = entryB.pair := by rw [h_entry_eq]
    _ = pairB := h_pair_b
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
-- tama: discharges=factory_closed_world_path_preserves_existing_pairs
theorem closed_world_path_preserves_existing_pairs
    (existing0 existing1 existingPair : Address)
    (before after : FactoryWorldState) :
  factory_closed_world_path_preserves_existing_pairs
    existing0 existing1 existingPair before after := by
  exact factoryWorldPath_preserves_existing_pair
-- tama: discharges=factory_closed_world_path_is_append_only
theorem closed_world_path_is_append_only
    (before after : FactoryWorldState) :
  factory_closed_world_path_is_append_only before after := by
  exact factoryWorldPath_append_only
-- tama: discharges=factory_closed_world_same_count_path_preserves_pair_list
theorem closed_world_same_count_path_preserves_pair_list
    (before after : FactoryWorldState) :
  factory_closed_world_same_count_path_preserves_pair_list before after := by
  intro h_path h_same_count
  rcases factoryWorldPath_append_only h_path with
    ⟨suffix, h_pairs, h_count⟩
  have h_suffix_length_zero : suffix.length = 0 := by
    rw [h_count] at h_same_count
    omega
  have h_suffix_nil : suffix = [] := by
    exact List.length_eq_zero_iff.mp h_suffix_length_zero
  rw [h_pairs, h_suffix_nil]
  simp
-- tama: discharges=factory_closed_world_path_length_matches_created_pairs
theorem closed_world_path_length_matches_created_pairs
    (before after : FactoryWorldState) :
  factory_closed_world_path_length_matches_created_pairs before after := by
  intro h_good h_path
  exact (factoryWorldPath_preserves_good h_good h_path).2.2
end TamaUniV2.Proof.UniswapV2FactoryProof
