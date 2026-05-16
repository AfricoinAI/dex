import TamaUniV2.Spec.UniswapV2PairSpec
import Verity.Proofs.Stdlib.Automation

namespace TamaUniV2.Proof.UniswapV2PairProof

set_option linter.unusedSimpArgs false

open Verity
open Verity.EVM.Uint256
open TamaUniV2.Spec.UniswapV2PairSpec
open TamaUniV2.UniswapV2Pair
open TamaUniV2.Common.UniswapV2PairConcrete
open TamaUniV2.Common.UniswapV2PairGhost

attribute [local simp] decimals totalSupply balanceOf allowance factory token0 token1
  MINIMUM_LIQUIDITY getReserves price0CumulativeLast price1CumulativeLast kLast
  «initialize» approve transfer transferFrom mint burn swap skim sync
  factorySlot token0Slot token1Slot reserve0Slot reserve1Slot blockTimestampLastSlot
  totalSupplySlot balancesSlot allowancesSlot price0CumulativeLastSlot price1CumulativeLastSlot
  unlockedSlot maxUint256
  UniswapV2PairBase.decimals UniswapV2PairBase.totalSupply
  UniswapV2PairBase.balanceOf UniswapV2PairBase.allowance
  UniswapV2PairBase.factory UniswapV2PairBase.token0 UniswapV2PairBase.token1
  UniswapV2PairBase.MINIMUM_LIQUIDITY UniswapV2PairBase.getReserves
  UniswapV2PairBase.price0CumulativeLast
  UniswapV2PairBase.price1CumulativeLast UniswapV2PairBase.kLast
  UniswapV2PairBase.«initialize» UniswapV2PairBase.approve
  UniswapV2PairBase.transfer UniswapV2PairBase.transferFrom
  UniswapV2PairBase.mint UniswapV2PairBase.burn UniswapV2PairBase.swap
  UniswapV2PairBase.skim UniswapV2PairBase.sync
  UniswapV2PairBase.factorySlot UniswapV2PairBase.token0Slot
  UniswapV2PairBase.token1Slot UniswapV2PairBase.reserve0Slot
  UniswapV2PairBase.reserve1Slot UniswapV2PairBase.blockTimestampLastSlot
  UniswapV2PairBase.totalSupplySlot UniswapV2PairBase.balancesSlot
  UniswapV2PairBase.allowancesSlot UniswapV2PairBase.price0CumulativeLastSlot
  UniswapV2PairBase.price1CumulativeLastSlot UniswapV2PairBase.unlockedSlot
  UniswapV2PairBase.maxUint256
  TamaUniV2.erc20BalanceOf pairSelf pairToken0 pairToken1 observedBalance0 observedBalance1
  TamaUniV2.pairSafeTransfer TamaUniV2.tracePairTokenSafeTransfer
  TamaUniV2.pairTokenSafeTransferEvent pairTraceContains hasPairSafeTransferTrace
  pairLpApprovalEvent pairLpTransferEvent pairMintEvent pairBurnEvent pairSwapEvent pairSyncEvent
  mintAmount0 mintAmount1 timestamp32 skimExcess0 skimExcess1
  swapExpected0 swapExpected1 swapAmount0In swapAmount1In
  Contracts.emit emitEvent

-- tama: discharges=pair_decimals_spec
theorem decimals_meets_spec (s : ContractState) :
  pair_decimals_spec ((decimals).run s).fst := by
  rfl

-- tama: discharges=pair_totalSupply_spec
theorem totalSupply_meets_spec (s : ContractState) :
  pair_totalSupply_spec ((totalSupply).run s).fst s := by
  rfl

-- tama: discharges=pair_balanceOf_spec
theorem balanceOf_meets_spec (account : Address) (s : ContractState) :
  pair_balanceOf_spec account ((balanceOf account).run s).fst s := by
  rfl

-- tama: discharges=pair_allowance_spec
theorem allowance_meets_spec (owner spender : Address) (s : ContractState) :
  pair_allowance_spec owner spender ((allowance owner spender).run s).fst s := by
  rfl

-- tama: discharges=pair_factory_spec
theorem factory_meets_spec (s : ContractState) :
  pair_factory_spec ((factory).run s).fst s := by
  simp [pair_factory_spec, factory, Verity.getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_token0_spec
theorem token0_meets_spec (s : ContractState) :
  pair_token0_spec ((token0).run s).fst s := by
  simp [pair_token0_spec, token0, Verity.getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_token1_spec
theorem token1_meets_spec (s : ContractState) :
  pair_token1_spec ((token1).run s).fst s := by
  simp [pair_token1_spec, token1, Verity.getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_minimumLiquidity_spec
theorem minimumLiquidity_meets_spec (s : ContractState) :
  pair_minimumLiquidity_spec ((MINIMUM_LIQUIDITY).run s).fst := by
  rfl

-- tama: discharges=pair_getReserves_spec
theorem getReserves_meets_spec (s : ContractState) :
  pair_getReserves_spec ((getReserves).run s).fst s := by
  simp [pair_getReserves_spec, getReserves, reserve0Slot, reserve1Slot,
    blockTimestampLastSlot, getStorage, Contract.run, ContractResult.fst,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_price0CumulativeLast_spec
theorem price0CumulativeLast_meets_spec (s : ContractState) :
  pair_price0CumulativeLast_spec ((price0CumulativeLast).run s).fst s := by
  rfl

-- tama: discharges=pair_price1CumulativeLast_spec
theorem price1CumulativeLast_meets_spec (s : ContractState) :
  pair_price1CumulativeLast_spec ((price1CumulativeLast).run s).fst s := by
  rfl

-- tama: discharges=pair_kLast_spec
theorem kLast_meets_spec (s : ContractState) :
  pair_kLast_spec ((kLast).run s).fst := by
  rfl

-- tama: discharges=pair_safeTransfer_traces_token_transfer
theorem safeTransfer_traces_token_transfer
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_safeTransfer_traces_token_transfer token toAddr amount s
    ((TamaUniV2.pairSafeTransfer token toAddr amount).run s) := by
  simp [pair_safeTransfer_traces_token_transfer, TamaUniV2.pairSafeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, hasPairSafeTransferTrace,
    pairTraceContains, TamaUniV2.pairTokenSafeTransferEvent, Contracts.safeTransfer,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_initialize_reverts_for_non_factory
theorem initialize_reverts_for_non_factory
    (token0Value token1Value : Address) (s : ContractState) :
  pair_initialize_reverts_for_non_factory token0Value token1Value s
    ((«initialize» token0Value token1Value).run s) := by
  intro h_forbidden
  have h_forbidden_raw : ¬ s.sender = s.storageAddr 0 := by
    simpa [factorySlot] using h_forbidden
  simp [pair_initialize_reverts_for_non_factory, «initialize», msgSender,
    getStorageAddr, Verity.require, Contract.run, Verity.bind, Bind.bind,
    h_forbidden_raw]

-- tama: discharges=pair_initialize_reverts_when_already_initialized
theorem initialize_reverts_when_already_initialized
    (token0Value token1Value : Address) (s : ContractState) :
  pair_initialize_reverts_when_already_initialized token0Value token1Value s
    ((«initialize» token0Value token1Value).run s) := by
  intro h_sender h_initialized
  have h_sender_raw : s.sender = s.storageAddr 0 := by
    simpa [factorySlot] using h_sender
  rcases h_initialized with h_token0_initialized | h_token1_initialized
  · have h_token0_nonzero : ¬ s.storageAddr 1 = (0 : Address) := by
      simpa [token0Slot] using h_token0_initialized
    simp [pair_initialize_reverts_when_already_initialized, «initialize», msgSender,
      getStorageAddr, Verity.require, Contract.run, Verity.bind, Bind.bind,
      h_sender_raw, h_token0_nonzero]
  · have h_token1_nonzero : ¬ s.storageAddr 2 = (0 : Address) := by
      simpa [token1Slot] using h_token1_initialized
    by_cases h_token0_zero : s.storageAddr 1 = (0 : Address)
    · simp [pair_initialize_reverts_when_already_initialized, «initialize», msgSender,
        getStorageAddr, Verity.require, Contract.run, Verity.bind, Bind.bind,
        h_sender_raw, h_token0_zero, h_token1_nonzero]
    · simp [pair_initialize_reverts_when_already_initialized, «initialize», msgSender,
        getStorageAddr, Verity.require, Contract.run, Verity.bind, Bind.bind,
        h_sender_raw, h_token0_zero]

-- tama: discharges=pair_initialize_sets_tokens
theorem initialize_sets_tokens
    (token0Value token1Value : Address) (s : ContractState) :
  pair_initialize_sets_tokens token0Value token1Value s
    ((«initialize» token0Value token1Value).run s) := by
  intro h_sender h_token0_empty h_token1_empty
  have h_sender_raw : s.sender = s.storageAddr 0 := by
    simpa [factorySlot] using h_sender
  have h_token0_raw : s.storageAddr 1 = (0 : Address) := by
    simpa [token0Slot] using h_token0_empty
  have h_token1_raw : s.storageAddr 2 = (0 : Address) := by
    simpa [token1Slot] using h_token1_empty
  have h_token_slots_distinct : (1 : Nat) ≠ 2 := by
    omega
  simp [pair_initialize_sets_tokens, «initialize», msgSender, getStorageAddr,
    setStorageAddr, Verity.require, Contract.run, ContractResult.snd,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    h_sender_raw, h_token0_raw, h_token1_raw, h_token_slots_distinct]

private theorem approve_properties_after_run
    (spender : Address) (amount : Uint256) (s : ContractState) :
  pair_approve_succeeds spender amount s ((approve spender amount).run s) ∧
  pair_approve_sets_allowance spender amount s ((approve spender amount).run s) ∧
  pair_approve_keeps_balances spender amount s ((approve spender amount).run s) ∧
  pair_approve_keeps_total_supply spender amount s ((approve spender amount).run s) ∧
  pair_approve_emits_approval spender amount s ((approve spender amount).run s) := by
  unfold pair_approve_succeeds pair_approve_sets_allowance
    pair_approve_keeps_balances pair_approve_keeps_total_supply
    pair_approve_emits_approval
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · funext slotIdx addr
    simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      pairTraceContains]

-- tama: discharges=pair_approve_succeeds
theorem approve_succeeds (spender : Address) (amount : Uint256) (s : ContractState) :
  pair_approve_succeeds spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).1

-- tama: discharges=pair_approve_sets_allowance
theorem approve_sets_allowance (spender : Address) (amount : Uint256) (s : ContractState) :
  pair_approve_sets_allowance spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).2.1

-- tama: discharges=pair_approve_keeps_balances
theorem approve_keeps_balances (spender : Address) (amount : Uint256) (s : ContractState) :
  pair_approve_keeps_balances spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).2.2.1

-- tama: discharges=pair_approve_keeps_total_supply
theorem approve_keeps_total_supply (spender : Address) (amount : Uint256) (s : ContractState) :
  pair_approve_keeps_total_supply spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).2.2.2.1

-- tama: discharges=pair_approve_emits_approval
theorem approve_emits_approval (spender : Address) (amount : Uint256) (s : ContractState) :
  pair_approve_emits_approval spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).2.2.2.2

private theorem transfer_properties_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_reverts_when_balance_low toAddr amount s ((transfer toAddr amount).run s) ∧
  pair_transfer_to_self_keeps_balances toAddr amount s ((transfer toAddr amount).run s) ∧
  pair_transfer_reverts_when_recipient_balance_would_overflow toAddr amount s
    ((transfer toAddr amount).run s) ∧
  pair_transfer_moves_tokens_between_distinct_accounts toAddr amount s
    ((transfer toAddr amount).run s) ∧
  pair_transfer_keeps_total_supply toAddr amount s ((transfer toAddr amount).run s) ∧
  pair_transfer_emits_transfer toAddr amount s ((transfer toAddr amount).run s) := by
  unfold pair_transfer_reverts_when_balance_low
    pair_transfer_to_self_keeps_balances
    pair_transfer_reverts_when_recipient_balance_would_overflow
    pair_transfer_moves_tokens_between_distinct_accounts
    pair_transfer_keeps_total_supply
    pair_transfer_emits_transfer
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_insufficient
    have h_not_balance : ¬ amount.val ≤ (s.storageMap 9 s.sender).val := by
      have h_insufficient_raw : amount.val > (s.storageMap 9 s.sender).val := by
        simpa [balancesSlot] using h_insufficient
      omega
    simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_not_balance]
  · intro h_balance h_same
    have h_balance_raw : amount.val ≤ (s.storageMap 9 s.sender).val := by
      simpa [balancesSlot] using h_balance
    subst h_same
    simp [transfer, balancesSlot, totalSupplySlot, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Verity.require, h_balance_raw]
  · intro h_balance h_ne h_overflow
    have h_balance_raw : amount.val ≤ (s.storageMap 9 s.sender).val := by
      simpa [balancesSlot] using h_balance
    have h_overflow_strict :
        Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 9 toAddr).val + amount.val := by
      simpa [balancesSlot] using h_overflow
    simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne, h_overflow_strict]
  · intro h_balance h_ne h_no_overflow
    have h_balance_raw : amount.val ≤ (s.storageMap 9 s.sender).val := by
      simpa [balancesSlot] using h_balance
    have h_no_overflow_raw :
        (s.storageMap 9 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa [balancesSlot] using h_no_overflow
    have h_not_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 9 toAddr).val + amount.val := by
      omega
    refine ⟨?_, ?_, ?_⟩
    · simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint,
        Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne, h_not_overflow]
    · show ((transfer toAddr amount).run s).snd.storageMap 9 s.sender =
        sub (s.storageMap 9 s.sender) amount
      simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint,
        Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne, h_not_overflow]
    · simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint,
        Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne, h_not_overflow, HSub.hSub]
  · by_cases h_balance : amount.val ≤ (s.storageMap 9 s.sender).val
    · by_cases h_same : s.sender = toAddr
      · subst h_same
        simp [transfer, balancesSlot, totalSupplySlot, msgSender, getMapping, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Verity.require, h_balance]
      · by_cases h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + amount.val
        · simp [transfer, balancesSlot, totalSupplySlot, msgSender, getMapping, setMapping,
            Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
            Pure.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
            Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
        · simp [transfer, balancesSlot, totalSupplySlot, msgSender, getMapping, setMapping,
            Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
            Pure.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
            Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
    · simp [transfer, balancesSlot, totalSupplySlot, msgSender, getMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance]
  · intro h_balance h_path
    have h_balance_raw : amount.val ≤ (s.storageMap 9 s.sender).val := by
      simpa [balancesSlot] using h_balance
    rcases h_path with h_same | ⟨h_ne, h_no_overflow⟩
    · subst h_same
      simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, h_balance_raw, pairTraceContains]
    · have h_no_overflow_raw :
          (s.storageMap 9 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa [balancesSlot] using h_no_overflow
      have h_not_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 9 toAddr).val + amount.val := by
        omega
      simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, Verity.Stdlib.Math.requireSomeUint,
        Verity.Stdlib.Math.safeAdd, h_balance_raw, h_ne, h_not_overflow,
        pairTraceContains]

-- tama: discharges=pair_transfer_reverts_when_balance_low
theorem transfer_reverts_when_balance_low
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_reverts_when_balance_low toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).1

-- tama: discharges=pair_transfer_to_self_keeps_balances
theorem transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_to_self_keeps_balances toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.1

-- tama: discharges=pair_transfer_reverts_when_recipient_balance_would_overflow
theorem transfer_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_reverts_when_recipient_balance_would_overflow toAddr amount s
    ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.1

-- tama: discharges=pair_transfer_moves_tokens_between_distinct_accounts
theorem transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_moves_tokens_between_distinct_accounts toAddr amount s
    ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.2.1

-- tama: discharges=pair_transfer_keeps_total_supply
theorem transfer_keeps_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_keeps_total_supply toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.2.2.1

-- tama: discharges=pair_transfer_emits_transfer
theorem transfer_emits_transfer
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_emits_transfer toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.2.2.2

private theorem transferFrom_properties_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_reverts_when_allowance_low fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  pair_transferFrom_reverts_when_balance_low fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  pair_transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  pair_transferFrom_to_self_keeps_balances fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  pair_transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  pair_transferFrom_keeps_total_supply fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  pair_transferFrom_keeps_infinite_allowance fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  pair_transferFrom_spends_finite_allowance fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) ∧
  pair_transferFrom_emits_transfer fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) := by
  unfold pair_transferFrom_reverts_when_allowance_low
    pair_transferFrom_reverts_when_balance_low
    pair_transferFrom_reverts_when_recipient_balance_would_overflow
    pair_transferFrom_to_self_keeps_balances
    pair_transferFrom_moves_tokens_between_distinct_accounts
    pair_transferFrom_keeps_total_supply
    pair_transferFrom_keeps_infinite_allowance
    pair_transferFrom_spends_finite_allowance
    pair_transferFrom_emits_transfer
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_insufficient_allowance
    have h_insufficient_allowance_raw :
        amount.val > (s.storageMap2 10 fromAddr s.sender).val := by
      simpa [allowancesSlot] using h_insufficient_allowance
    have h_not_allowance :
        ¬ amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val := by
      omega
    simp [transferFrom, allowancesSlot, msgSender, getMapping2, Contract.run,
      Verity.bind, Bind.bind, Verity.require, h_not_allowance]
  · intro h_allowance h_insufficient_balance
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val := by
      simpa [allowancesSlot] using h_allowance
    have h_insufficient_balance_raw :
        amount.val > (s.storageMap 9 fromAddr).val := by
      simpa [balancesSlot] using h_insufficient_balance
    have h_not_balance : ¬ amount.val ≤ (s.storageMap 9 fromAddr).val := by
      omega
    simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2, getMapping,
      Contract.run, Verity.bind, Bind.bind, Verity.require, h_allowance_raw, h_not_balance]
  · intro h_allowance h_balance h_ne h_overflow
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val := by
      simpa [allowancesSlot] using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 9 fromAddr).val := by
      simpa [balancesSlot] using h_balance
    have h_overflow_strict :
        Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 9 toAddr).val + amount.val := by
      simpa [balancesSlot] using h_overflow
    simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2, getMapping,
      setMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Pure.pure, Verity.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
      Verity.Stdlib.Math.safeAdd, h_allowance_raw, h_balance_raw, h_ne, h_overflow_strict]
  · intro h_allowance h_balance h_eq
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val := by
      simpa [allowancesSlot] using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 9 fromAddr).val := by
      simpa [balancesSlot] using h_balance
    subst h_eq
    by_cases h_max :
        s.storageMap2 10 fromAddr s.sender =
          maxUint256
    · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
      have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
        simpa [h_max] using h_allowance_raw
      simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
        getMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Verity.require, h_allowance_raw,
        h_allowance_max, h_balance_raw, h_max]
    · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
      simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
        getMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Verity.require, h_allowance_raw,
        h_balance_raw, h_max]
  · intro h_allowance h_balance h_ne h_no_overflow
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val := by
      simpa [allowancesSlot] using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 9 fromAddr).val := by
      simpa [balancesSlot] using h_balance
    have h_no_overflow_raw :
        (s.storageMap 9 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      simpa [balancesSlot] using h_no_overflow
    have h_not_overflow :
        ¬ Verity.Stdlib.Math.MAX_UINT256 <
          (s.storageMap 9 toAddr).val + amount.val := by
      omega
    by_cases h_max :
        s.storageMap2 10 fromAddr s.sender =
          maxUint256
    · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
      have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
        simpa [h_max] using h_allowance_raw
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
          getMapping, setMapping, setMapping2, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Pure.pure, Verity.pure, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          h_allowance_raw, h_balance_raw, h_ne, h_not_overflow, h_allowance_max,
          h_max, HSub.hSub]
    · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
          getMapping, setMapping, setMapping2, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Pure.pure, Verity.pure, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          h_allowance_raw, h_balance_raw, h_ne, h_not_overflow, h_max, HSub.hSub]
  · by_cases h_allowance : amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val
    · by_cases h_balance : amount.val ≤ (s.storageMap 9 fromAddr).val
      · by_cases h_same : fromAddr = toAddr
        · subst h_same
          by_cases h_max :
              s.storageMap2 10 fromAddr s.sender =
                maxUint256
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
              simpa [h_max] using h_allowance
            simp [transferFrom, allowancesSlot, balancesSlot, totalSupplySlot,
              msgSender, getMapping2, getMapping, setMapping2, Contract.run,
              ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
              Verity.require, h_allowance, h_allowance_max, h_balance, h_max]
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            simp [transferFrom, allowancesSlot, balancesSlot, totalSupplySlot,
              msgSender, getMapping2, getMapping, setMapping2, Contract.run,
              ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
              Verity.require, h_allowance, h_balance, h_max]
        · by_cases h_overflow :
            Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + amount.val
          · simp [transferFrom, allowancesSlot, balancesSlot, totalSupplySlot,
              msgSender, getMapping2, getMapping, setMapping, Contract.run,
              ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
              Verity.require, Verity.Stdlib.Math.requireSomeUint,
              Verity.Stdlib.Math.safeAdd, h_allowance, h_balance, h_same,
              h_overflow]
          · by_cases h_max :
              s.storageMap2 10 fromAddr s.sender =
                maxUint256
            · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
              have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
                simpa [h_max] using h_allowance
              simp [transferFrom, allowancesSlot, balancesSlot, totalSupplySlot,
                msgSender, getMapping2, getMapping, setMapping, setMapping2,
                Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
                Pure.pure, Verity.pure, Verity.require,
                Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
                h_allowance, h_allowance_max, h_balance, h_same, h_overflow, h_max]
            · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
              simp [transferFrom, allowancesSlot, balancesSlot, totalSupplySlot,
                msgSender, getMapping2, getMapping, setMapping, setMapping2,
                Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
                Pure.pure, Verity.pure, Verity.require,
                Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
                h_allowance, h_balance, h_same, h_overflow, h_max]
      · simp [transferFrom, allowancesSlot, balancesSlot, totalSupplySlot, msgSender,
          getMapping2, getMapping, Contract.run, ContractResult.snd, Verity.bind,
          Bind.bind, Verity.require, h_allowance, h_balance]
    · simp [transferFrom, allowancesSlot, totalSupplySlot, msgSender, getMapping2,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.require,
        h_allowance]
  · intro h_allowance h_balance h_path h_max
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val := by
      simpa [allowancesSlot] using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 9 fromAddr).val := by
      simpa [balancesSlot] using h_balance
    have h_max_ofNat :
        s.storageMap2 10 fromAddr s.sender =
          maxUint256 := by
      change s.storageMap2 10 fromAddr s.sender =
        maxUint256
      simpa [allowancesSlot] using h_max
    simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max_ofNat
    have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
      simpa [h_max_ofNat] using h_allowance_raw
    rcases h_path with h_eq | ⟨h_ne, h_no_overflow⟩
    · subst h_eq
      simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
        getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.pure, Pure.pure, Verity.require, h_allowance_raw,
        h_allowance_max, h_balance_raw, h_max_ofNat, emitEvent]
    · have h_no_overflow_raw :
          (s.storageMap 9 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa [balancesSlot] using h_no_overflow
      have h_not_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 9 toAddr).val + amount.val := by
        omega
      simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
        getMapping, setMapping, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_allowance_raw, h_allowance_max, h_balance_raw, h_ne, h_not_overflow,
        h_max_ofNat]
  · intro h_allowance h_balance h_path h_not_max
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val := by
      simpa [allowancesSlot] using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 9 fromAddr).val := by
      simpa [balancesSlot] using h_balance
    have h_not_max_ofNat :
        s.storageMap2 10 fromAddr s.sender ≠
          maxUint256 := by
      change s.storageMap2 10 fromAddr s.sender ≠
        maxUint256
      simpa [allowancesSlot] using h_not_max
    simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_not_max_ofNat
    rcases h_path with h_eq | ⟨h_ne, h_no_overflow⟩
    · subst h_eq
      simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
        getMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Verity.require, h_allowance_raw,
        h_balance_raw, h_not_max_ofNat, HSub.hSub]
    · have h_no_overflow_raw :
          (s.storageMap 9 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa [balancesSlot] using h_no_overflow
      have h_not_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 9 toAddr).val + amount.val := by
        omega
      simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
        getMapping, setMapping, setMapping2, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
        Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
        h_allowance_raw, h_balance_raw, h_ne, h_not_overflow,
        h_not_max_ofNat, HSub.hSub]
  · intro h_allowance h_balance h_path
    have h_allowance_raw :
        amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val := by
      simpa [allowancesSlot] using h_allowance
    have h_balance_raw : amount.val ≤ (s.storageMap 9 fromAddr).val := by
      simpa [balancesSlot] using h_balance
    rcases h_path with h_eq | ⟨h_ne, h_no_overflow⟩
    · subst h_eq
      by_cases h_max :
          s.storageMap2 10 fromAddr s.sender =
            maxUint256
      · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
        have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
          simpa [h_max] using h_allowance_raw
        simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
          getMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind,
          Bind.bind, Verity.pure, Pure.pure, Verity.require, h_allowance_raw,
          h_allowance_max, h_balance_raw, h_max, pairTraceContains]
      · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
        simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
          getMapping, setMapping2, Contract.run, ContractResult.snd, Verity.bind,
          Bind.bind, Verity.pure, Pure.pure, Verity.require, h_allowance_raw,
          h_balance_raw, h_max, pairTraceContains]
    · have h_no_overflow_raw :
          (s.storageMap 9 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 := by
        simpa [balancesSlot] using h_no_overflow
      have h_not_overflow :
          ¬ Verity.Stdlib.Math.MAX_UINT256 <
            (s.storageMap 9 toAddr).val + amount.val := by
        omega
      by_cases h_max :
          s.storageMap2 10 fromAddr s.sender =
            maxUint256
      · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
        have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
          simpa [h_max] using h_allowance_raw
        simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
          getMapping, setMapping, setMapping2, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          h_allowance_raw, h_allowance_max, h_balance_raw, h_ne, h_not_overflow,
          h_max, pairTraceContains]
      · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
        simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
          getMapping, setMapping, setMapping2, Contract.run, ContractResult.snd,
          Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
          Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
          h_allowance_raw, h_balance_raw, h_ne, h_not_overflow,
          h_max, pairTraceContains]

-- tama: discharges=pair_transferFrom_reverts_when_allowance_low
theorem transferFrom_reverts_when_allowance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_reverts_when_allowance_low fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).1

-- tama: discharges=pair_transferFrom_reverts_when_balance_low
theorem transferFrom_reverts_when_balance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_reverts_when_balance_low fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.1

-- tama: discharges=pair_transferFrom_reverts_when_recipient_balance_would_overflow
theorem transferFrom_reverts_when_recipient_balance_would_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.1

-- tama: discharges=pair_transferFrom_to_self_keeps_balances
theorem transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_to_self_keeps_balances fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.1

-- tama: discharges=pair_transferFrom_moves_tokens_between_distinct_accounts
theorem transferFrom_moves_tokens_between_distinct_accounts
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.1

-- tama: discharges=pair_transferFrom_keeps_total_supply
theorem transferFrom_keeps_total_supply
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_keeps_total_supply fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.2.1

-- tama: discharges=pair_transferFrom_keeps_infinite_allowance
theorem transferFrom_keeps_infinite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_keeps_infinite_allowance fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.2.2.1

-- tama: discharges=pair_transferFrom_spends_finite_allowance
theorem transferFrom_spends_finite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_spends_finite_allowance fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.2.2.2.1

-- tama: discharges=pair_transferFrom_emits_transfer
theorem transferFrom_emits_transfer
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_emits_transfer fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) :=
  (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.2.2.2.2.2.2

-- tama: discharges=pair_mint_reverts_when_locked
theorem mint_reverts_when_locked (toAddr : Address) (s : ContractState) :
  pair_mint_reverts_when_locked toAddr s ((mint toAddr).run s) := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_mint_reverts_when_locked, mint, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_burn_reverts_when_locked
theorem burn_reverts_when_locked (toAddr : Address) (s : ContractState) :
  pair_burn_reverts_when_locked toAddr s ((burn toAddr).run s) := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_burn_reverts_when_locked, burn, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_swap_reverts_when_locked
theorem swap_reverts_when_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_swap_reverts_when_locked amount0Out amount1Out toAddr data s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_swap_reverts_when_locked, swap, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_swap_reverts_for_insufficient_output
theorem swap_reverts_for_insufficient_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_swap_reverts_for_insufficient_output amount0Out amount1Out toAddr data s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_unlocked h_amount0 h_amount1
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  subst h_amount0
  subst h_amount1
  simp [pair_swap_reverts_for_insufficient_output, swap, UniswapV2PairBase.swap,
    unlockedSlot, getStorage, setStorage, Verity.require, Contract.run,
    Verity.bind, Bind.bind, h_unlocked_raw]

-- tama: discharges=pair_skim_reverts_when_locked
theorem skim_reverts_when_locked (toAddr : Address) (s : ContractState) :
  pair_skim_reverts_when_locked toAddr s ((skim toAddr).run s) := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_skim_reverts_when_locked, skim, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_skim_reverts_when_balance0_below_reserve
theorem skim_reverts_when_balance0_below_reserve
    (toAddr : Address) (s : ContractState) :
  pair_skim_reverts_when_balance0_below_reserve toAddr s ((skim toAddr).run s) := by
  intro h_unlocked h_balance0
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_balance0_raw : (observedBalance0 s).val < (s.storage 3).val := by
    simpa [reserve0Slot] using h_balance0
  have h_require_false :
      ¬ ((s.storage 3).val ≤ (observedBalance0 s).val ∧
        (s.storage 4).val ≤ (observedBalance1 s).val) := by
    intro h
    omega
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_skim_reverts_when_balance0_below_reserve, skim, UniswapV2PairBase.skim,
    unlockedSlot, token0Slot, token1Slot, reserve0Slot, reserve1Slot,
    getStorage, getStorageAddr, setStorage, Verity.contractAddress,
    Contracts.balanceOf, Verity.require, Contract.run, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, observedBalance0, observedBalance1,
    TamaUniV2.erc20BalanceOf, h_unlocked_raw, h_require_false_raw]

-- tama: discharges=pair_skim_reverts_when_balance1_below_reserve
theorem skim_reverts_when_balance1_below_reserve
    (toAddr : Address) (s : ContractState) :
  pair_skim_reverts_when_balance1_below_reserve toAddr s ((skim toAddr).run s) := by
  intro h_unlocked h_balance1
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_balance1_raw : (observedBalance1 s).val < (s.storage 4).val := by
    simpa [reserve1Slot] using h_balance1
  have h_require_false :
      ¬ ((s.storage 3).val ≤ (observedBalance0 s).val ∧
        (s.storage 4).val ≤ (observedBalance1 s).val) := by
    intro h
    omega
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_skim_reverts_when_balance1_below_reserve, skim, UniswapV2PairBase.skim,
    unlockedSlot, token0Slot, token1Slot, reserve0Slot, reserve1Slot,
    getStorage, getStorageAddr, setStorage, Verity.contractAddress,
    Contracts.balanceOf, Verity.require, Contract.run, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, observedBalance0, observedBalance1,
    TamaUniV2.erc20BalanceOf, h_unlocked_raw, h_require_false_raw]

-- tama: discharges=pair_sync_reverts_when_locked
theorem sync_reverts_when_locked (s : ContractState) :
  pair_sync_reverts_when_locked s ((sync).run s) := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_sync_reverts_when_locked, sync, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_sync_reverts_when_balance0_overflows
theorem sync_reverts_when_balance0_overflows (s : ContractState) :
  pair_sync_reverts_when_balance0_overflows s ((sync).run s) := by
  intro h_unlocked h_balance0
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_balance0_raw : maxUint112.val < (observedBalance0 s).val := by
    simpa using h_balance0
  have h_require_false :
      ¬ ((observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val) := by
    intro h
    omega
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_sync_reverts_when_balance0_overflows, sync, UniswapV2PairBase.sync,
    unlockedSlot, token0Slot, token1Slot, maxUint112, getStorage, getStorageAddr,
    setStorage, Verity.contractAddress, Contracts.balanceOf, Verity.require,
    Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    observedBalance0, observedBalance1, TamaUniV2.erc20BalanceOf,
    h_unlocked_raw, h_require_false_raw]

-- tama: discharges=pair_sync_reverts_when_balance1_overflows
theorem sync_reverts_when_balance1_overflows (s : ContractState) :
  pair_sync_reverts_when_balance1_overflows s ((sync).run s) := by
  intro h_unlocked h_balance1
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_balance1_raw : maxUint112.val < (observedBalance1 s).val := by
    simpa using h_balance1
  have h_require_false :
      ¬ ((observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val) := by
    intro h
    omega
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_sync_reverts_when_balance1_overflows, sync, UniswapV2PairBase.sync,
    unlockedSlot, token0Slot, token1Slot, maxUint112, getStorage, getStorageAddr,
    setStorage, Verity.contractAddress, Contracts.balanceOf, Verity.require,
    Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    observedBalance0, observedBalance1, TamaUniV2.erc20BalanceOf,
    h_unlocked_raw, h_require_false_raw]

-- tama: discharges=pair_initialize_run_revert_non_factory
theorem initialize_run_revert_non_factory
    (token0Value token1Value : Address) (s : ContractState) :
  pair_initialize_run_revert_non_factory token0Value token1Value s := by
  simpa [pair_initialize_run_revert_non_factory,
    pair_initialize_reverts_for_non_factory]
    using initialize_reverts_for_non_factory token0Value token1Value s

-- tama: discharges=pair_initialize_run_revert_already_initialized
theorem initialize_run_revert_already_initialized
    (token0Value token1Value : Address) (s : ContractState) :
  pair_initialize_run_revert_already_initialized token0Value token1Value s := by
  simpa [pair_initialize_run_revert_already_initialized,
    pair_initialize_reverts_when_already_initialized]
    using initialize_reverts_when_already_initialized token0Value token1Value s

-- tama: discharges=pair_transfer_run_revert_balance_low
theorem transfer_run_revert_balance_low
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_run_revert_balance_low toAddr amount s := by
  simpa [pair_transfer_run_revert_balance_low,
    pair_transfer_reverts_when_balance_low]
    using transfer_reverts_when_balance_low toAddr amount s

-- tama: discharges=pair_transfer_run_revert_recipient_balance_overflow
theorem transfer_run_revert_recipient_balance_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_run_revert_recipient_balance_overflow toAddr amount s := by
  simpa [pair_transfer_run_revert_recipient_balance_overflow,
    pair_transfer_reverts_when_recipient_balance_would_overflow]
    using transfer_reverts_when_recipient_balance_would_overflow toAddr amount s

-- tama: discharges=pair_transferFrom_run_revert_allowance_low
theorem transferFrom_run_revert_allowance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_run_revert_allowance_low fromAddr toAddr amount s := by
  simpa [pair_transferFrom_run_revert_allowance_low,
    pair_transferFrom_reverts_when_allowance_low]
    using transferFrom_reverts_when_allowance_low fromAddr toAddr amount s

-- tama: discharges=pair_transferFrom_run_revert_balance_low
theorem transferFrom_run_revert_balance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_run_revert_balance_low fromAddr toAddr amount s := by
  simpa [pair_transferFrom_run_revert_balance_low,
    pair_transferFrom_reverts_when_balance_low]
    using transferFrom_reverts_when_balance_low fromAddr toAddr amount s

-- tama: discharges=pair_transferFrom_run_revert_recipient_balance_overflow
theorem transferFrom_run_revert_recipient_balance_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_run_revert_recipient_balance_overflow fromAddr toAddr amount s := by
  simpa [pair_transferFrom_run_revert_recipient_balance_overflow,
    pair_transferFrom_reverts_when_recipient_balance_would_overflow]
    using transferFrom_reverts_when_recipient_balance_would_overflow
      fromAddr toAddr amount s

-- tama: discharges=pair_mint_run_revert_locked
theorem mint_run_revert_locked (toAddr : Address) (s : ContractState) :
  pair_mint_run_revert_locked toAddr s := by
  simpa [pair_mint_run_revert_locked, pair_mint_reverts_when_locked]
    using mint_reverts_when_locked toAddr s

-- tama: discharges=pair_burn_run_revert_locked
theorem burn_run_revert_locked (toAddr : Address) (s : ContractState) :
  pair_burn_run_revert_locked toAddr s := by
  simpa [pair_burn_run_revert_locked, pair_burn_reverts_when_locked]
    using burn_reverts_when_locked toAddr s

-- tama: discharges=pair_swap_run_revert_locked
theorem swap_run_revert_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_swap_run_revert_locked amount0Out amount1Out toAddr data s := by
  simpa [pair_swap_run_revert_locked, pair_swap_reverts_when_locked]
    using swap_reverts_when_locked amount0Out amount1Out toAddr data s

-- tama: discharges=pair_swap_run_revert_insufficient_output
theorem swap_run_revert_insufficient_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_swap_run_revert_insufficient_output amount0Out amount1Out toAddr data s := by
  simpa [pair_swap_run_revert_insufficient_output,
    pair_swap_reverts_for_insufficient_output]
    using swap_reverts_for_insufficient_output amount0Out amount1Out toAddr data s

-- tama: discharges=pair_skim_run_revert_locked
theorem skim_run_revert_locked (toAddr : Address) (s : ContractState) :
  pair_skim_run_revert_locked toAddr s := by
  simpa [pair_skim_run_revert_locked, pair_skim_reverts_when_locked]
    using skim_reverts_when_locked toAddr s

-- tama: discharges=pair_skim_run_revert_balance0_below_reserve
theorem skim_run_revert_balance0_below_reserve
    (toAddr : Address) (s : ContractState) :
  pair_skim_run_revert_balance0_below_reserve toAddr s := by
  simpa [pair_skim_run_revert_balance0_below_reserve,
    pair_skim_reverts_when_balance0_below_reserve]
    using skim_reverts_when_balance0_below_reserve toAddr s

-- tama: discharges=pair_skim_run_revert_balance1_below_reserve
theorem skim_run_revert_balance1_below_reserve
    (toAddr : Address) (s : ContractState) :
  pair_skim_run_revert_balance1_below_reserve toAddr s := by
  simpa [pair_skim_run_revert_balance1_below_reserve,
    pair_skim_reverts_when_balance1_below_reserve]
    using skim_reverts_when_balance1_below_reserve toAddr s

-- tama: discharges=pair_skim_run_success_transfers_excess_and_restores_unlocked
theorem skim_run_success_transfers_excess_and_restores_unlocked
    (toAddr : Address) (s : ContractState) :
  pair_skim_run_success_transfers_excess_and_restores_unlocked toAddr s := by
  intro h_unlocked h_balance0 h_balance1
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_require_raw :
      (s.storage 3).val ≤ (observedBalance0 s).val ∧
      (s.storage 4).val ≤ (observedBalance1 s).val := by
    constructor
    · simpa [reserve0Slot] using h_balance0
    · simpa [reserve1Slot] using h_balance1
  have h_require_raw_unfold := h_require_raw
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_raw_unfold
  simp [pair_skim_run_success_transfers_excess_and_restores_unlocked,
    skim, UniswapV2PairBase.skim, unlockedSlot, token0Slot, token1Slot,
    reserve0Slot, reserve1Slot, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.pairSafeTransfer, TamaUniV2.tracePairTokenSafeTransfer,
    TamaUniV2.pairTokenSafeTransferEvent, Contracts.safeTransfer,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    skimExcess0, skimExcess1, h_unlocked_raw, h_require_raw_unfold,
    hasPairSafeTransferTrace, pairTraceContains]

-- tama: discharges=pair_sync_run_revert_locked
theorem sync_run_revert_locked (s : ContractState) :
  pair_sync_run_revert_locked s := by
  simpa [pair_sync_run_revert_locked, pair_sync_reverts_when_locked]
    using sync_reverts_when_locked s

-- tama: discharges=pair_sync_run_revert_balance0_overflows
theorem sync_run_revert_balance0_overflows (s : ContractState) :
  pair_sync_run_revert_balance0_overflows s := by
  simpa [pair_sync_run_revert_balance0_overflows,
    pair_sync_reverts_when_balance0_overflows]
    using sync_reverts_when_balance0_overflows s

-- tama: discharges=pair_sync_run_revert_balance1_overflows
theorem sync_run_revert_balance1_overflows (s : ContractState) :
  pair_sync_run_revert_balance1_overflows s := by
  simpa [pair_sync_run_revert_balance1_overflows,
    pair_sync_reverts_when_balance1_overflows]
    using sync_reverts_when_balance1_overflows s

-- tama: discharges=pair_mint_first_expected_refines_closed_world
theorem mint_first_expected_refines_closed_world (toAddr : Address) (s : ContractState) :
  pair_mint_first_expected_refines_closed_world toAddr s := by
  dsimp [pair_mint_first_expected_refines_closed_world]
  intro h_unlocked h_supply_zero h_bound0 h_bound1 h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_supply_zero_raw : s.storage 8 = (0 : Uint256) := by
    simpa [totalSupplySlot] using h_supply_zero
  have h_supply_zero_val : (s.storage 8).val = 0 := by
    rw [h_supply_zero_raw]
    rfl
  unfold PairWorldStep PairWorldMintStep pairWorldBeforeMintRun
    pairWorldAfterFirstMintRun pairWorldLockedLiquidity
  simp only [totalSupplySlot, h_supply_zero_raw, h_supply_zero_val, if_true]
  constructor
  · simpa [mintAmount0] using h_amount0
  constructor
  · simpa [mintAmount1] using h_amount1
  constructor
  · have h_root_le : minimumLiquidity.val ≤ (mintFirstRoot s).val :=
      Nat.le_of_lt h_root
    have h_liquidity_eq :
        (mintFirstLiquidity s).val =
          (mintFirstRoot s).val - minimumLiquidity.val := by
      simpa [mintFirstLiquidity] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := mintFirstRoot s) (b := minimumLiquidity) h_root_le)
    have h_liquidity_pos : 0 < (mintFirstLiquidity s).val := by
      rw [h_liquidity_eq]
      omega
    simpa [mintFirstLiquidity] using h_liquidity_pos
  constructor
  · have h_sub :
        (mintAmount0 s).val =
          (observedBalance0 s).val - (s.storage reserve0Slot.slot).val := by
      simpa [mintAmount0] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance0 s) (b := s.storage reserve0Slot.slot) h_reserve0)
    have h_sub_raw :
        (Verity.EVM.Uint256.sub
            ((Contracts.balanceOf (s.storageAddr 1) s.thisAddress).run s).fst
            (s.storage 3)).val =
          (observedBalance0 s).val - (s.storage reserve0Slot.slot).val := by
      simpa [mintAmount0, observedBalance0, pairToken0, pairSelf,
        TamaUniV2.erc20BalanceOf, Contracts.balanceOf, reserve0Slot, Contract.run,
        ContractResult.fst, Verity.pure, Pure.pure] using h_sub
    rw [h_sub_raw]
    omega
  constructor
  · have h_sub :
        (mintAmount1 s).val =
          (observedBalance1 s).val - (s.storage reserve1Slot.slot).val := by
      simpa [mintAmount1] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance1 s) (b := s.storage reserve1Slot.slot) h_reserve1)
    have h_sub_raw :
        (Verity.EVM.Uint256.sub
            ((Contracts.balanceOf (s.storageAddr 2) s.thisAddress).run s).fst
            (s.storage 4)).val =
          (observedBalance1 s).val - (s.storage reserve1Slot.slot).val := by
      simpa [mintAmount1, observedBalance1, pairToken1, pairSelf,
        TamaUniV2.erc20BalanceOf, Contracts.balanceOf, reserve1Slot, Contract.run,
        ContractResult.fst, Verity.pure, Pure.pure] using h_sub
    rw [h_sub_raw]
    omega
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound0
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound1
  constructor
  · have h_root_le : minimumLiquidity.val ≤ (mintFirstRoot s).val :=
      Nat.le_of_lt h_root
    have h_min_val : minimumLiquidity.val = minimumLiquidityNat := by
      change (Verity.Core.Uint256.ofNat 1000).val = (1000 : Nat)
      norm_num [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
        Verity.Core.UINT256_MODULUS]
    have h_liquidity_eq :
        (mintFirstLiquidity s).val =
          (mintFirstRoot s).val - minimumLiquidity.val := by
      simpa [mintFirstLiquidity] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := mintFirstRoot s) (b := minimumLiquidity) h_root_le)
    have h_root_le_nat : minimumLiquidityNat ≤ (mintFirstRoot s).val := by
      rw [← h_min_val]
      exact h_root_le
    have h_root_eq :
        (mintFirstRoot s).val =
          minimumLiquidityNat + ((mintFirstRoot s).val - minimumLiquidityNat) := by
      exact (Nat.add_sub_of_le h_root_le_nat).symm
    simpa [h_supply_zero_val, h_liquidity_eq, h_min_val] using h_root_eq
  · simp [h_supply_zero_val]

-- tama: discharges=pair_mint_first_success_run_refines_closed_world
theorem mint_first_success_run_refines_closed_world
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_refines_closed_world toAddr s
    ((mint toAddr).run s) := by
  dsimp [pair_mint_first_success_run_refines_closed_world]
  intro _h_actual _h_success h_unlocked h_supply_zero h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_product h_root
  exact mint_first_expected_refines_closed_world toAddr s
    h_unlocked h_supply_zero h_bound0 h_bound1 h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root

private theorem pairWorldStep_preserves_good
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldStep action before after →
      PairWorldGood after := by
  intro h_good h_step
  cases action <;>
    simp [PairWorldStep, PairWorldMintStep, PairWorldBurnStep, PairWorldSwapStep,
      PairWorldSkimStep, PairWorldSyncStep] at h_step
  · subst after
    exact h_good
  · subst after
    exact h_good
  · subst after
    exact h_good
  · rcases h_good with ⟨h_back0, h_back1, h_bound0, h_bound1, h_supply⟩
    rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
      h_supply_eq, h_locked_eq⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h_reserve0, h_balance0]
      omega
    · rw [h_reserve1, h_balance1]
      omega
    · rw [h_reserve0]
      exact h_bound0
    · rw [h_reserve1]
      exact h_bound1
    · simpa [PairWorldSupplyGood, h_supply_eq, h_locked_eq] using h_supply
  · rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
    rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity,
      _h_before_balance0, _h_before_balance1, h_after_balance0, h_after_balance1,
      h_after_reserve0, h_after_reserve1, h_bound0, h_bound1, h_supply_eq,
      h_locked_eq⟩
    refine ⟨?_, ?_, h_bound0, h_bound1, ?_⟩
    · rw [h_after_reserve0, h_after_balance0]
    · rw [h_after_reserve1, h_after_balance1]
    · by_cases h_zero : before.totalSupply = 0
      · right
        rw [h_supply_eq, h_locked_eq]
        simp [h_zero, minimumLiquidityNat]
      · rcases h_supply with h_empty | h_nonzero
        · exact False.elim (h_zero h_empty.1)
        · rcases h_nonzero with ⟨h_positive, h_locked, h_min⟩
          have h_min_raw : 1000 ≤ before.totalSupply := by
            simpa [minimumLiquidityNat] using h_min
          right
          rw [h_supply_eq, h_locked_eq]
          simp [h_zero, h_locked, minimumLiquidityNat]
          omega
  · rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
    rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity_le,
      h_locked_remaining, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
      h_bound0, h_bound1, h_supply_eq, h_locked_eq⟩
    refine ⟨?_, ?_, h_bound0, h_bound1, ?_⟩
    · rw [h_reserve0]
    · rw [h_reserve1]
    · rcases h_supply with h_empty | h_nonzero
      · left
        rw [h_supply_eq, h_locked_eq]
        omega
      · rcases h_nonzero with ⟨_h_positive, h_locked, _h_min⟩
        right
        rw [h_supply_eq, h_locked_eq]
        constructor
        · rw [h_locked] at h_locked_remaining
          simp [minimumLiquidityNat] at h_locked_remaining
          omega
        · constructor
          · exact h_locked
          · rw [h_locked] at h_locked_remaining
            exact h_locked_remaining
  · rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
    rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
      _h_input, _h_balance0, _h_balance1, h_reserve0, h_reserve1, h_bound0,
      h_bound1, h_supply_eq, h_locked_eq, _h_fee0, _h_fee1, _h_k⟩
    refine ⟨?_, ?_, h_bound0, h_bound1, ?_⟩
    · rw [h_reserve0]
    · rw [h_reserve1]
    · simpa [PairWorldSupplyGood, h_supply_eq, h_locked_eq] using h_supply
  · rcases h_good with ⟨_h_back0, _h_back1, h_bound0, h_bound1, h_supply⟩
    rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
      h_supply_eq, h_locked_eq⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h_reserve0, h_balance0]
    · rw [h_reserve1, h_balance1]
    · rw [h_reserve0]
      exact h_bound0
    · rw [h_reserve1]
      exact h_bound1
    · simpa [PairWorldSupplyGood, h_supply_eq, h_locked_eq] using h_supply
  · rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
    rcases h_step with ⟨h_bound0, h_bound1, h_balance0, h_balance1,
      h_reserve0, h_reserve1, h_supply_eq, h_locked_eq⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h_reserve0, h_balance0]
    · rw [h_reserve1, h_balance1]
    · rw [h_reserve0]
      exact h_bound0
    · rw [h_reserve1]
      exact h_bound1
    · simpa [PairWorldSupplyGood, h_supply_eq, h_locked_eq] using h_supply

private theorem pairWorldReachable_good
    (w : PairWorldState) :
  PairWorldReachable w → PairWorldGood w := by
  intro h_reachable
  induction h_reachable with
  | init =>
      simp [PairWorldInitial, PairWorldGood, PairWorldSupplyGood,
        minimumLiquidityNat, maxUint112Nat]
  | step action h_before h_step ih =>
      exact pairWorldStep_preserves_good ih h_step

-- tama: discharges=pair_closed_world_reachable_reserves_backed
theorem closed_world_reachable_reserves_backed
    (w : PairWorldState) :
  pair_closed_world_reachable_reserves_backed w := by
  intro h_reachable
  rcases pairWorldReachable_good w h_reachable with
    ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  exact ⟨h_back0, h_back1⟩

-- tama: discharges=pair_closed_world_reachable_reserves_fit_uint112
theorem closed_world_reachable_reserves_fit_uint112
    (w : PairWorldState) :
  pair_closed_world_reachable_reserves_fit_uint112 w := by
  intro h_reachable
  rcases pairWorldReachable_good w h_reachable with
    ⟨_h_back0, _h_back1, h_bound0, h_bound1, _h_supply⟩
  exact ⟨h_bound0, h_bound1⟩

-- tama: discharges=pair_closed_world_nonzero_supply_locks_minimum_liquidity
theorem closed_world_nonzero_supply_locks_minimum_liquidity
    (w : PairWorldState) :
  pair_closed_world_nonzero_supply_locks_minimum_liquidity w := by
  intro h_reachable h_nonzero
  rcases pairWorldReachable_good w h_reachable with
    ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
  rcases h_supply with h_empty | h_nonempty
  · exact False.elim (h_nonzero h_empty.1)
  · rcases h_nonempty with ⟨_h_positive, h_locked, h_min⟩
    exact ⟨h_locked, h_min⟩

-- tama: discharges=pair_closed_world_mint_updates_reserves_to_balances
theorem closed_world_mint_updates_reserves_to_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_updates_reserves_to_balances
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_before_balance0,
    _h_before_balance1, h_after_balance0, h_after_balance1, h_after_reserve0,
    h_after_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked⟩
  constructor
  · rw [h_after_reserve0, h_after_balance0]
  · rw [h_after_reserve1, h_after_balance1]

-- tama: discharges=pair_closed_world_burn_updates_reserves_to_balances
theorem closed_world_burn_updates_reserves_to_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_updates_reserves_to_balances
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, h_reserve0, h_reserve1, _h_bound0, _h_bound1,
    _h_supply, _h_locked⟩
  exact ⟨h_reserve0, h_reserve1⟩

-- tama: discharges=pair_closed_world_swap_updates_reserves_to_balances
theorem closed_world_swap_updates_reserves_to_balances
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_updates_reserves_to_balances
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
    _h_input, _h_balance0, _h_balance1, h_reserve0, h_reserve1, _h_bound0,
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_k⟩
  exact ⟨h_reserve0, h_reserve1⟩

-- tama: discharges=pair_closed_world_swap_respects_fee_adjusted_k
theorem closed_world_swap_respects_fee_adjusted_k
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_respects_fee_adjusted_k
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
    _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, h_k⟩
  exact h_k

-- tama: discharges=pair_closed_world_skim_removes_surplus
theorem closed_world_skim_removes_surplus
    (before after : PairWorldState) :
  pair_closed_world_skim_removes_surplus before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  exact ⟨h_balance0, h_balance1, h_reserve0, h_reserve1⟩

-- tama: discharges=pair_closed_world_sync_sets_reserves_to_balances
theorem closed_world_sync_sets_reserves_to_balances
    (before after : PairWorldState) :
  pair_closed_world_sync_sets_reserves_to_balances before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
    h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  exact ⟨h_reserve0, h_reserve1, h_balance0, h_balance1⟩

end TamaUniV2.Proof.UniswapV2PairProof
