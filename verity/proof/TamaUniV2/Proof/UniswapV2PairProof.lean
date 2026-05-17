import TamaUniV2.Spec.UniswapV2PairSpec
import Verity.Proofs.Stdlib.Automation

namespace TamaUniV2.Proof.UniswapV2PairProof

set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

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
  unlockedSlot feeDenominator feeAdjustment maxUint112 maxUint256
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
  UniswapV2PairBase.feeDenominator UniswapV2PairBase.feeAdjustment
  UniswapV2PairBase.maxUint112 UniswapV2PairBase.maxUint256
  TamaUniV2.erc20BalanceOf pairSelf pairToken0 pairToken1 observedBalance0 observedBalance1
  TamaUniV2.pairSafeTransfer TamaUniV2.tracePairTokenSafeTransfer
  TamaUniV2.pairTokenSafeTransferEvent pairTraceContains hasPairSafeTransferTrace
  pairLpApprovalEvent pairLpTransferEvent pairMintEvent pairBurnEvent pairSwapEvent pairSyncEvent
  mintAmount0 mintAmount1 timestamp32 skimExcess0 skimExcess1
  swapExpected0 swapExpected1 swapAmountIn swapAmount0In swapAmount1In
  swapBalance0Scaled swapBalance1Scaled swapAmount0Fee swapAmount1Fee
  swapBalance0Adjusted swapBalance1Adjusted swapAdjustedProduct swapReserveProductOf
  swapReserveProduct swapScaleProduct swapRequiredProductOf swapRequiredProduct
  Contracts.emit emitEvent

private def pairLockedState (s : ContractState) : ContractState :=
  { s with «storage» := fun slotIdx => if slotIdx = 11 then 0 else s.storage slotIdx }

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

private theorem pair_revert_keeps_token_balances {α : Type}
    (pre post : PairTokenBalances) (s : ContractState) (result : ContractResult α) :
  post = pairTokenWorldAfterCall pre s result →
    pairRevertedWithOriginalState s result →
      pairTokenBalancesUnchanged pre post := by
  intro h_post h_revert token account
  rcases h_revert with ⟨reason, h_result⟩
  rw [h_result] at h_post
  rw [h_post]
  simp [pairTokenWorldAfterCall, emittedPairEventsAfterCall,
    pairTokenWorldAfterEvents]

-- tama: discharges=pair_mint_revert_keeps_token_balances
theorem mint_revert_keeps_token_balances
    (toAddr : Address) (pre post : PairTokenBalances) (s : ContractState) :
  pair_mint_revert_keeps_token_balances toAddr pre post s ((mint toAddr).run s) :=
  pair_revert_keeps_token_balances pre post s ((mint toAddr).run s)

-- tama: discharges=pair_burn_revert_keeps_token_balances
theorem burn_revert_keeps_token_balances
    (toAddr : Address) (pre post : PairTokenBalances) (s : ContractState) :
  pair_burn_revert_keeps_token_balances toAddr pre post s ((burn toAddr).run s) :=
  pair_revert_keeps_token_balances pre post s ((burn toAddr).run s)

-- tama: discharges=pair_swap_revert_keeps_token_balances
theorem swap_revert_keeps_token_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (pre post : PairTokenBalances) (s : ContractState) :
  pair_swap_revert_keeps_token_balances amount0Out amount1Out toAddr data pre post s
    ((swap amount0Out amount1Out toAddr data).run s) :=
  pair_revert_keeps_token_balances pre post s
    ((swap amount0Out amount1Out toAddr data).run s)

-- tama: discharges=pair_skim_revert_keeps_token_balances
theorem skim_revert_keeps_token_balances
    (toAddr : Address) (pre post : PairTokenBalances) (s : ContractState) :
  pair_skim_revert_keeps_token_balances toAddr pre post s ((skim toAddr).run s) :=
  pair_revert_keeps_token_balances pre post s ((skim toAddr).run s)

-- tama: discharges=pair_sync_revert_keeps_token_balances
theorem sync_revert_keeps_token_balances
    (pre post : PairTokenBalances) (s : ContractState) :
  pair_sync_revert_keeps_token_balances pre post s ((sync).run s) :=
  pair_revert_keeps_token_balances pre post s ((sync).run s)

private theorem pair_revert_keeps_pair_state {α : Type}
    (s : ContractState) (result : ContractResult α) :
  (∃ reason, result = ContractResult.revert reason s) →
    result.snd.storage = s.storage ∧
    result.snd.storageMap = s.storageMap ∧
    result.snd.storageMap2 = s.storageMap2 ∧
    result.snd.events = s.events := by
  intro h_revert
  rcases h_revert with ⟨reason, h_result⟩
  rw [h_result]
  exact ⟨rfl, rfl, rfl, rfl⟩

-- tama: discharges=pair_mint_revert_keeps_pair_state
theorem mint_revert_keeps_pair_state
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) :
  pair_mint_revert_keeps_pair_state toAddr s result := by
  intro _h_run h_revert
  exact pair_revert_keeps_pair_state s result h_revert

-- tama: discharges=pair_burn_revert_keeps_pair_state
theorem burn_revert_keeps_pair_state
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) :
  pair_burn_revert_keeps_pair_state toAddr s result := by
  intro _h_run h_revert
  exact pair_revert_keeps_pair_state s result h_revert

-- tama: discharges=pair_swap_revert_keeps_pair_state
theorem swap_revert_keeps_pair_state
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) :
  pair_swap_revert_keeps_pair_state amount0Out amount1Out toAddr data s result := by
  intro _h_run h_revert
  exact pair_revert_keeps_pair_state s result h_revert

-- tama: discharges=pair_skim_revert_keeps_pair_state
theorem skim_revert_keeps_pair_state
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Unit) :
  pair_skim_revert_keeps_pair_state toAddr s result := by
  intro _h_run h_revert
  exact pair_revert_keeps_pair_state s result h_revert

-- tama: discharges=pair_sync_revert_keeps_pair_state
theorem sync_revert_keeps_pair_state
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_revert_keeps_pair_state s result := by
  intro _h_run h_revert
  exact pair_revert_keeps_pair_state s result h_revert

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

-- tama: discharges=pair_skim_run_success_refines_closed_world
theorem skim_run_success_refines_closed_world
    (toAddr : Address) (s : ContractState) :
  pair_skim_run_success_refines_closed_world toAddr s := by
  intro h_unlocked h_balance0 h_balance1
  have h_success :=
    skim_run_success_transfers_excess_and_restores_unlocked
      toAddr s h_unlocked h_balance0 h_balance1
  rcases h_success with ⟨h_run, _h_reserve0, _h_reserve1, _h_unlocked,
    _h_transfer0, _h_transfer1⟩
  rw [h_run]
  simp [pair_skim_run_success_refines_closed_world, PairWorldStep,
    PairWorldSkimStep, pairWorldFromConcreteState, pairWorldAfterSkimRun,
    pairWorldLockedLiquidity]

-- tama: discharges=pair_sync_run_revert_locked
theorem sync_run_revert_locked (s : ContractState) :
  pair_sync_run_revert_locked s := by
  simpa [pair_sync_run_revert_locked, pair_sync_reverts_when_locked]
    using sync_reverts_when_locked s

-- tama: discharges=pair_sync_expected_refines_closed_world
theorem sync_expected_refines_closed_world (s : ContractState) :
  pair_sync_expected_refines_closed_world s := by
  intro h_bound0 h_bound1
  simp [pair_sync_expected_refines_closed_world, PairWorldStep,
    PairWorldSyncStep, pairWorldFromConcreteState, pairWorldAfterSyncRun,
    pairWorldLockedLiquidity, maxUint112Nat, maxUint112,
    UniswapV2PairBase.maxUint112]
  exact ⟨by simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using h_bound0,
    by simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using h_bound1⟩

-- tama: discharges=pair_sync_success_run_refines_closed_world
theorem sync_success_run_refines_closed_world
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_refines_closed_world s result := by
  intro _h_run _h_success h_bound0 h_bound1
  exact sync_expected_refines_closed_world s h_bound0 h_bound1

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
      h_locked_eq, _h_ratio⟩
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
      h_bound0, h_bound1, h_supply_eq, h_locked_eq, _h_ratio0, _h_ratio1⟩
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
      h_bound1, h_supply_eq, h_locked_eq, _h_fee0, _h_fee1, _h_k, _h_raw_k⟩
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

private theorem pairWorldPath_preserves_good
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPath before after →
      PairWorldGood after := by
  intro h_good h_path
  revert h_good
  induction h_path with
  | refl =>
      intro h_good
      exact h_good
  | step action h_prefix h_step ih =>
      intro h_good
      exact pairWorldStep_preserves_good (ih h_good) h_step

private theorem pairWorldPath_of_noBurn
    {before after : PairWorldState} :
  PairWorldPathNoBurn before after →
    PairWorldPath before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWorldPath.refl before
  | step action h_prefix h_step _h_not_burn ih =>
      exact PairWorldPath.step action ih h_step

private theorem pairWorldNonBurnStep_never_decreases_k
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
        PairWorldK before ≤ PairWorldK after := by
  intro h_good h_step h_not_burn
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rfl
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      unfold PairWorldK
      rw [h_reserve0, h_reserve1]
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        h_before_balance0, h_before_balance1, h_after_balance0, h_after_balance1,
        h_after_reserve0, h_after_reserve1, _h_bound0, _h_bound1, _h_supply,
        _h_locked, _h_ratio⟩
      unfold PairWorldK
      rw [h_after_reserve0, h_after_reserve1]
      have h0 : before.reserve0 ≤ before.balance0 := by
        rw [h_before_balance0]
        omega
      have h1 : before.reserve1 ≤ before.balance1 := by
        rw [h_before_balance1]
        omega
      exact Nat.mul_le_mul h0 h1
  | burn amount0 amount1 liquidity =>
      exact False.elim (h_not_burn amount0 amount1 liquidity rfl)
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
        _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1,
        _h_adjusted_k, h_raw_k⟩
      exact h_raw_k
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      unfold PairWorldK
      rw [h_reserve0, h_reserve1]
  | sync =>
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1,
        _h_supply_good⟩
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        h_reserve0, h_reserve1, _h_supply, _h_locked⟩
      unfold PairWorldK
      rw [h_reserve0, h_reserve1]
      exact Nat.mul_le_mul h_back0 h_back1

private theorem pairWorldNoBurnPath_never_decreases_k
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPathNoBurn before after →
      PairWorldK before ≤ PairWorldK after := by
  intro h_good h_path
  revert h_good
  induction h_path with
  | refl =>
      intro _h_good
      rfl
  | step action h_prefix h_step h_not_burn ih =>
      intro h_good
      have h_good_before :=
        pairWorldPath_preserves_good h_good
          (pairWorldPath_of_noBurn h_prefix)
      exact Nat.le_trans
        (ih h_good)
        (pairWorldNonBurnStep_never_decreases_k
          h_good_before h_step h_not_burn)

-- tama: discharges=pair_closed_world_step_preserves_good
theorem closed_world_step_preserves_good
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_step_preserves_good action before after := by
  exact pairWorldStep_preserves_good

-- tama: discharges=pair_closed_world_path_preserves_good
theorem closed_world_path_preserves_good
    (before after : PairWorldState) :
  pair_closed_world_path_preserves_good before after := by
  exact pairWorldPath_preserves_good

-- tama: discharges=pair_closed_world_reachable_good
theorem closed_world_reachable_good
    (w : PairWorldState) :
  pair_closed_world_reachable_good w := by
  exact pairWorldReachable_good w

-- tama: discharges=pair_closed_world_reachable_supply_good
theorem closed_world_reachable_supply_good
    (w : PairWorldState) :
  pair_closed_world_reachable_supply_good w := by
  intro h_reachable
  exact (pairWorldReachable_good w h_reachable).2.2.2.2

-- tama: discharges=pair_closed_world_path_supply_good
theorem closed_world_path_supply_good
    (before after : PairWorldState) :
  pair_closed_world_path_supply_good before after := by
  intro h_good h_path
  exact (pairWorldPath_preserves_good h_good h_path).2.2.2.2

-- tama: discharges=pair_closed_world_path_reserves_fit_uint112
theorem closed_world_path_reserves_fit_uint112
    (before after : PairWorldState) :
  pair_closed_world_path_reserves_fit_uint112 before after := by
  intro h_good h_path
  rcases pairWorldPath_preserves_good h_good h_path with
    ⟨_h_back0, _h_back1, h_bound0, h_bound1, _h_supply⟩
  exact ⟨h_bound0, h_bound1⟩

-- tama: discharges=pair_closed_world_path_locked_liquidity_never_exceeds_supply
theorem closed_world_path_locked_liquidity_never_exceeds_supply
    (before after : PairWorldState) :
  pair_closed_world_path_locked_liquidity_never_exceeds_supply before after := by
  intro h_good h_path
  have h_supply := (pairWorldPath_preserves_good h_good h_path).2.2.2.2
  rcases h_supply with h_empty | h_nonempty
  · rcases h_empty with ⟨h_supply_zero, h_locked_zero⟩
    rw [h_supply_zero, h_locked_zero]
  · rcases h_nonempty with ⟨_h_positive, h_locked, h_min⟩
    rw [h_locked]
    exact h_min

-- tama: discharges=pair_concrete_state_reserves_backed
theorem concrete_state_reserves_backed (s : ContractState) :
  pair_concrete_state_reserves_backed s := by
  intro h_good
  rcases h_good with ⟨h0, h1, _h1120, _h1121, _hsupply⟩
  exact ⟨h0, h1⟩

-- tama: discharges=pair_concrete_state_uint112_reserves
theorem concrete_state_uint112_reserves (s : ContractState) :
  pair_concrete_state_uint112_reserves s := by
  intro h_good
  rcases h_good with ⟨_h0, _h1, h1120, h1121, _hsupply⟩
  exact ⟨h1120, h1121⟩

-- tama: discharges=pair_closed_world_reachable_reserves_backed
theorem closed_world_reachable_reserves_backed
    (w : PairWorldState) :
  pair_closed_world_reachable_reserves_backed w := by
  intro h_reachable
  rcases pairWorldReachable_good w h_reachable with
    ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  exact ⟨h_back0, h_back1⟩

-- tama: discharges=pair_closed_world_path_reserves_backed
theorem closed_world_path_reserves_backed
    (before after : PairWorldState) :
  pair_closed_world_path_reserves_backed before after := by
  intro h_good h_path
  rcases pairWorldPath_preserves_good h_good h_path with
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

-- tama: discharges=pair_closed_world_zero_supply_has_no_locked_liquidity
theorem closed_world_zero_supply_has_no_locked_liquidity
    (w : PairWorldState) :
  pair_closed_world_zero_supply_has_no_locked_liquidity w := by
  intro h_reachable h_zero_supply
  rcases pairWorldReachable_good w h_reachable with
    ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
  rcases h_supply with h_empty | h_nonempty
  · exact h_empty.2
  · rcases h_nonempty with ⟨h_positive, _h_locked, _h_min⟩
    have h_positive_zero : 0 < 0 := by
      simp [h_zero_supply] at h_positive
    exact False.elim ((Nat.lt_irrefl 0) h_positive_zero)

-- tama: discharges=pair_closed_world_locked_liquidity_never_exceeds_supply
theorem closed_world_locked_liquidity_never_exceeds_supply
    (w : PairWorldState) :
  pair_closed_world_locked_liquidity_never_exceeds_supply w := by
  intro h_reachable
  rcases pairWorldReachable_good w h_reachable with
    ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply⟩
  rcases h_supply with h_empty | h_nonempty
  · rcases h_empty with ⟨h_supply_zero, h_locked_zero⟩
    rw [h_supply_zero, h_locked_zero]
  · rcases h_nonempty with ⟨_h_positive, h_locked, h_min⟩
    rw [h_locked]
    exact h_min

-- tama: discharges=pair_closed_world_supply_changes_only_on_mint_or_burn
theorem closed_world_supply_changes_only_on_mint_or_burn
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_supply_changes_only_on_mint_or_burn action before after := by
  intro h_step h_change
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact False.elim (h_change rfl)
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact False.elim (h_change rfl)
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact False.elim (h_change rfl)
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      exact False.elim (h_change h_supply)
  | mint amount0 amount1 liquidity =>
      exact Or.inl ⟨amount0, amount1, liquidity, rfl⟩
  | burn amount0 amount1 liquidity =>
      exact Or.inr ⟨amount0, amount1, liquidity, rfl⟩
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
        _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0, _h_fee1,
        _h_adjusted_k, _h_raw_k⟩
      exact False.elim (h_change h_supply)
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      exact False.elim (h_change h_supply)
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
      exact False.elim (h_change h_supply)

-- tama: discharges=pair_closed_world_approve_preserves_pool
theorem closed_world_approve_preserves_pool
    (ownerAddr spender : Address) (amount : Nat)
    (before after : PairWorldState) :
  pair_closed_world_approve_preserves_pool ownerAddr spender amount before after := by
  intro h_step
  simpa [PairWorldStep] using h_step

-- tama: discharges=pair_closed_world_transfer_preserves_pool
theorem closed_world_transfer_preserves_pool
    (fromAddr toAddr : Address) (amount : Nat)
    (before after : PairWorldState) :
  pair_closed_world_transfer_preserves_pool fromAddr toAddr amount before after := by
  intro h_step
  simpa [PairWorldStep] using h_step

-- tama: discharges=pair_closed_world_transferFrom_preserves_pool
theorem closed_world_transferFrom_preserves_pool
    (spender fromAddr toAddr : Address) (amount : Nat)
    (before after : PairWorldState) :
  pair_closed_world_transferFrom_preserves_pool
    spender fromAddr toAddr amount before after := by
  intro h_step
  simpa [PairWorldStep] using h_step

-- tama: discharges=pair_closed_world_first_mint_locks_minimum_liquidity
theorem closed_world_first_mint_locks_minimum_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_first_mint_locks_minimum_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step h_first
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, h_supply, h_locked, _h_ratio⟩
  simp [h_first] at h_supply h_locked
  exact ⟨h_locked, h_supply⟩

-- tama: discharges=pair_closed_world_subsequent_mint_preserves_locked_liquidity
theorem closed_world_subsequent_mint_preserves_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_subsequent_mint_preserves_locked_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step h_subsequent
  have h_totalSupply_ne : ¬ before.totalSupply = 0 := h_subsequent
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, h_supply, h_locked, _h_ratio⟩
  simp [h_totalSupply_ne] at h_supply h_locked
  exact ⟨h_locked, h_supply⟩

-- tama: discharges=pair_closed_world_burn_reduces_supply_by_liquidity
theorem closed_world_burn_reduces_supply_by_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_reduces_supply_by_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  exact h_supply

-- tama: discharges=pair_closed_world_burn_cannot_redeem_locked_liquidity
theorem closed_world_burn_cannot_redeem_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_cannot_redeem_locked_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    h_supply, h_locked, _h_ratio0, _h_ratio1⟩
  rw [h_supply]
  exact ⟨h_locked_remaining, h_locked⟩

-- tama: discharges=pair_closed_world_donate_preserves_reserves_and_supply
theorem closed_world_donate_preserves_reserves_and_supply
    (amount0 amount1 : Nat)
    (before after : PairWorldState) :
  pair_closed_world_donate_preserves_reserves_and_supply
    amount0 amount1 before after := by
  intro h_step
  simp [PairWorldStep] at h_step
  rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
    h_supply, h_locked⟩
  exact ⟨h_reserve0, h_reserve1, h_supply, h_locked⟩

-- tama: discharges=pair_closed_world_donate_preserves_k
theorem closed_world_donate_preserves_k
    (amount0 amount1 : Nat)
    (before after : PairWorldState) :
  pair_closed_world_donate_preserves_k amount0 amount1 before after := by
  intro h_step
  simp [PairWorldStep] at h_step
  rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  unfold PairWorldK
  rw [h_reserve0, h_reserve1]

-- tama: discharges=pair_closed_world_mint_preserves_good
theorem closed_world_mint_preserves_good
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_preserves_good amount0 amount1 liquidity before after := by
  exact pairWorldStep_preserves_good

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
    h_after_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
  constructor
  · rw [h_after_reserve0, h_after_balance0]
  · rw [h_after_reserve1, h_after_balance1]

-- tama: discharges=pair_closed_world_mint_liquidity_ratio
theorem closed_world_mint_liquidity_ratio
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_liquidity_ratio
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked, h_ratio⟩
  exact h_ratio

-- tama: discharges=pair_closed_world_burn_preserves_good
theorem closed_world_burn_preserves_good
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_preserves_good amount0 amount1 liquidity before after := by
  exact pairWorldStep_preserves_good

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
    _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  exact ⟨h_reserve0, h_reserve1⟩

-- tama: discharges=pair_closed_world_burn_liquidity_ratio
theorem closed_world_burn_liquidity_ratio
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_liquidity_ratio
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    _h_supply, _h_locked, h_ratio0, h_ratio1⟩
  exact ⟨h_ratio0, h_ratio1⟩

-- tama: discharges=pair_closed_world_swap_preserves_good
theorem closed_world_swap_preserves_good
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_preserves_good
    amount0In amount1In amount0Out amount1Out before after := by
  exact pairWorldStep_preserves_good

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
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_k, _h_raw_k⟩
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
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, h_k, _h_raw_k⟩
  exact h_k

-- tama: discharges=pair_closed_world_swap_never_decreases_k
theorem closed_world_swap_never_decreases_k
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_never_decreases_k
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
    _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_adjusted_k, h_raw_k⟩
  exact h_raw_k

-- tama: discharges=pair_closed_world_swap_has_input_and_output
theorem closed_world_swap_has_input_and_output
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_has_input_and_output
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
    h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_adjusted_k, _h_raw_k⟩
  exact ⟨h_output, h_input⟩

-- tama: discharges=pair_closed_world_swap_outputs_below_reserves
theorem closed_world_swap_outputs_below_reserves
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_outputs_below_reserves
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨_h_output, h_liq0, h_liq1, _h_enough0, _h_enough1,
    _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_adjusted_k, _h_raw_k⟩
  exact ⟨h_liq0, h_liq1⟩

-- tama: discharges=pair_closed_world_swap_preserves_liquidity_supply
theorem closed_world_swap_preserves_liquidity_supply
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_preserves_liquidity_supply
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
    _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
    _h_bound1, h_supply, h_locked, _h_fee0, _h_fee1, _h_adjusted_k, _h_raw_k⟩
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_closed_world_same_supply_path_no_spot_profit
theorem closed_world_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_same_supply_path_no_spot_profit before after := by
  intro _h_path _h_good _h_supply h_reserve0 h_reserve1 h_k
  unfold PairWorldNoSpotProfit PairWorldSpotValueNum PairWorldK at *
  by_contra h_not
  have h_lt :
      after.reserve0 * before.reserve1 + after.reserve1 * before.reserve0 <
        2 * (before.reserve0 * before.reserve1) :=
    Nat.lt_of_not_ge h_not
  have h_reserve0_int : (0 : Int) < before.reserve0 := by
    exact_mod_cast h_reserve0
  have h_reserve1_int : (0 : Int) < before.reserve1 := by
    exact_mod_cast h_reserve1
  let a : Int := before.reserve0
  let b : Int := before.reserve1
  let c : Int := after.reserve0
  let d : Int := after.reserve1
  have ha : 0 < a := by simpa [a] using h_reserve0_int
  have hb : 0 < b := by simpa [b] using h_reserve1_int
  have hc : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast Nat.zero_le after.reserve0
  have hd : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast Nat.zero_le after.reserve1
  have hk : a * b ≤ c * d := by
    dsimp [a, b, c, d]
    exact_mod_cast h_k
  have hlt : c * b + d * a < 2 * (a * b) := by
    dsimp [a, b, c, d]
    exact_mod_cast h_lt
  have hsq : 0 ≤ (c * b - d * a) ^ 2 := sq_nonneg _
  have hamgm : 4 * c * d * a * b ≤ (c * b + d * a) ^ 2 := by
    nlinarith [hsq]
  have hab_pos : 0 < a * b := by
    nlinarith [ha, hb]
  have hkscaled : 4 * a * b * a * b ≤ 4 * c * d * a * b := by
    nlinarith [hk, hab_pos]
  have hsum_nonneg : 0 ≤ c * b + d * a := by
    nlinarith [ha, hb, hc, hd]
  have htarget_pos : 0 < 2 * (a * b) := by
    nlinarith [ha, hb]
  have hlt_sq : (c * b + d * a) ^ 2 < (2 * (a * b)) ^ 2 := by
    nlinarith [hlt, hsum_nonneg, htarget_pos]
  nlinarith [hamgm, hkscaled, hlt_sq]

-- tama: discharges=pair_closed_world_non_burn_step_never_decreases_k
theorem closed_world_non_burn_step_never_decreases_k
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_burn_step_never_decreases_k action before after := by
  exact pairWorldNonBurnStep_never_decreases_k

-- tama: discharges=pair_closed_world_no_burn_path_never_decreases_k
theorem closed_world_no_burn_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_no_burn_path_never_decreases_k before after := by
  exact pairWorldNoBurnPath_never_decreases_k

-- tama: discharges=pair_closed_world_no_burn_same_supply_path_no_spot_profit
theorem closed_world_no_burn_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_no_burn_same_supply_path_no_spot_profit before after := by
  intro h_good h_path h_supply h_reserve0 h_reserve1
  have h_k :
      PairWorldK before ≤ PairWorldK after :=
    pairWorldNoBurnPath_never_decreases_k h_good h_path
  exact closed_world_same_supply_path_no_spot_profit before after
    (pairWorldPath_of_noBurn h_path) h_good h_supply h_reserve0 h_reserve1 h_k

-- tama: discharges=pair_closed_world_skim_preserves_good
theorem closed_world_skim_preserves_good
    (before after : PairWorldState) :
  pair_closed_world_skim_preserves_good before after := by
  exact pairWorldStep_preserves_good

-- tama: discharges=pair_closed_world_skim_removes_surplus
theorem closed_world_skim_removes_surplus
    (before after : PairWorldState) :
  pair_closed_world_skim_removes_surplus before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  exact ⟨h_balance0, h_balance1, h_reserve0, h_reserve1⟩

-- tama: discharges=pair_closed_world_skim_preserves_liquidity_supply
theorem closed_world_skim_preserves_liquidity_supply
    (before after : PairWorldState) :
  pair_closed_world_skim_preserves_liquidity_supply before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
    h_supply, h_locked⟩
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_closed_world_skim_preserves_k
theorem closed_world_skim_preserves_k
    (before after : PairWorldState) :
  pair_closed_world_skim_preserves_k before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  unfold PairWorldK
  rw [h_reserve0, h_reserve1]

-- tama: discharges=pair_closed_world_sync_preserves_good
theorem closed_world_sync_preserves_good
    (before after : PairWorldState) :
  pair_closed_world_sync_preserves_good before after := by
  exact pairWorldStep_preserves_good

-- tama: discharges=pair_closed_world_sync_sets_reserves_to_balances
theorem closed_world_sync_sets_reserves_to_balances
    (before after : PairWorldState) :
  pair_closed_world_sync_sets_reserves_to_balances before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
    h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  exact ⟨h_reserve0, h_reserve1, h_balance0, h_balance1⟩

-- tama: discharges=pair_closed_world_sync_preserves_liquidity_supply
theorem closed_world_sync_preserves_liquidity_supply
    (before after : PairWorldState) :
  pair_closed_world_sync_preserves_liquidity_supply before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
    _h_reserve0, _h_reserve1, h_supply, h_locked⟩
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_closed_world_sync_never_decreases_k
theorem closed_world_sync_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_sync_never_decreases_k before after := by
  intro h_good h_step
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
    h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  unfold PairWorldK
  rw [h_reserve0, h_reserve1]
  exact Nat.mul_le_mul h_back0 h_back1

end TamaUniV2.Proof.UniswapV2PairProof
