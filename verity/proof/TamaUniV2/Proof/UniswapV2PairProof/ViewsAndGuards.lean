-- SPDX-License-Identifier: AGPL-3.0-only
import TamaUniV2.Proof.UniswapV2PairProof.Setup

namespace TamaUniV2.Proof.UniswapV2PairProof

set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

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
  unlockedSlot feeDenominator feeAdjustment maxUint112 maxUint256 q112 uint32Modulus
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
  UniswapV2PairBase.q112 UniswapV2PairBase.uint32Modulus
  TamaUniV2.erc20BalanceOf pairSelf pairToken0 pairToken1 observedBalance0 observedBalance1
  TamaUniV2.pairSafeTransfer TamaUniV2.tracePairTokenSafeTransfer
  TamaUniV2.pairTokenSafeTransferEvent pairTraceContains hasPairSafeTransferTrace
  pairLpApprovalEvent pairLpTransferEvent pairMintEvent pairBurnEvent pairSwapEvent pairSyncEvent
  mintAmount0 mintAmount1 timestamp32 oracleElapsed oraclePrice0 oraclePrice1
  oraclePrice0Increment oraclePrice1Increment
  oraclePrice0CumulativeAfterElapsed oraclePrice1CumulativeAfterElapsed
  oraclePrice0CumulativeAfterSync oraclePrice1CumulativeAfterSync
  skimExcess0 skimExcess1
  swapExpected0 swapExpected1 swapAmountIn swapAmount0In swapAmount1In
  swapBalance0Scaled swapBalance1Scaled swapAmount0Fee swapAmount1Fee
  swapBalance0Adjusted swapBalance1Adjusted swapAdjustedProduct swapReserveProductOf
  swapReserveProduct swapScaleProduct swapRequiredProductOf swapRequiredProduct
  Contracts.emit emitEvent

attribute [local simp] sqrt_run_success_frames_state

-- tama: discharges=pair_decimals_run_success_frames_state
theorem decimals_run_success_frames_state (s : ContractState) :
  pair_decimals_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_totalSupply_run_success_frames_state
theorem totalSupply_run_success_frames_state (s : ContractState) :
  pair_totalSupply_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_balanceOf_run_success_frames_state
theorem balanceOf_run_success_frames_state (account : Address) (s : ContractState) :
  pair_balanceOf_run_success_frames_state account s := by
  rfl

-- tama: discharges=pair_allowance_run_success_frames_state
theorem allowance_run_success_frames_state
    (owner spender : Address) (s : ContractState) :
  pair_allowance_run_success_frames_state owner spender s := by
  rfl

-- tama: discharges=pair_factory_run_success_frames_state
theorem factory_run_success_frames_state (s : ContractState) :
  pair_factory_run_success_frames_state s := by
  simp [pair_factory_run_success_frames_state, factory, Verity.getStorageAddr,
    Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_token0_run_success_frames_state
theorem token0_run_success_frames_state (s : ContractState) :
  pair_token0_run_success_frames_state s := by
  simp [pair_token0_run_success_frames_state, token0, Verity.getStorageAddr,
    Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_token1_run_success_frames_state
theorem token1_run_success_frames_state (s : ContractState) :
  pair_token1_run_success_frames_state s := by
  simp [pair_token1_run_success_frames_state, token1, Verity.getStorageAddr,
    Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_minimumLiquidity_run_success_frames_state
theorem minimumLiquidity_run_success_frames_state (s : ContractState) :
  pair_minimumLiquidity_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_getReserves_run_success_frames_state
theorem getReserves_run_success_frames_state (s : ContractState) :
  pair_getReserves_run_success_frames_state s := by
  simp [pair_getReserves_run_success_frames_state, getReserves, reserve0Slot,
    reserve1Slot, blockTimestampLastSlot, getStorage, Contract.run,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_price0CumulativeLast_run_success_frames_state
theorem price0CumulativeLast_run_success_frames_state (s : ContractState) :
  pair_price0CumulativeLast_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_price1CumulativeLast_run_success_frames_state
theorem price1CumulativeLast_run_success_frames_state (s : ContractState) :
  pair_price1CumulativeLast_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_kLast_run_success_frames_state
theorem kLast_run_success_frames_state (s : ContractState) :
  pair_kLast_run_success_frames_state s := by
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

-- tama: discharges=pair_safeTransfer_event_replay_moves_token_balance
theorem safeTransfer_event_replay_moves_token_balance
    (token fromAddr toAddr : Address) (amount : Uint256)
    (pre : PairTokenBalances) :
  pair_safeTransfer_event_replay_moves_token_balance
    token fromAddr toAddr amount pre := by
  simp [pair_safeTransfer_event_replay_moves_token_balance,
    pairTokenWorldAfterEvent, TamaUniV2.pairTokenSafeTransferEvent,
    pairTokenWorldAfterTransfer, addressOfNat_toNat_mod_uint256]

-- tama: discharges=pair_two_safeTransfer_events_replay_move_distinct_token_balances
theorem two_safeTransfer_events_replay_move_distinct_token_balances
    (token0Value token1Value fromAddr toAddr : Address)
    (amount0 amount1 : Uint256) (pre : PairTokenBalances) :
  pair_two_safeTransfer_events_replay_move_distinct_token_balances
    token0Value token1Value fromAddr toAddr amount0 amount1 pre := by
  intro h_tokens h_accounts
  have h_tokens_symm : token1Value ≠ token0Value := by
    intro h_eq
    exact h_tokens h_eq.symm
  have h_accounts_symm : toAddr ≠ fromAddr := by
    intro h_eq
    exact h_accounts h_eq.symm
  simp [pair_two_safeTransfer_events_replay_move_distinct_token_balances,
    pairTokenWorldAfterEvents, pairTokenWorldAfterEvent,
    TamaUniV2.pairTokenSafeTransferEvent, pairTokenWorldAfterTransfer,
    addressOfNat_toNat_mod_uint256, h_tokens, h_tokens_symm, h_accounts,
    h_accounts_symm]

theorem pair_revert_keeps_token_balances {α : Type}
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

-- tama: discharges=pair_approve_run_keeps_token_balances
theorem approve_run_keeps_token_balances
    (spender : Address) (amount : Uint256)
    (pre post : PairTokenBalances) (s : ContractState) :
  pair_approve_run_keeps_token_balances spender amount pre post s := by
  intro h_post token account
  rw [h_post]
  simp [pair_approve_run_keeps_token_balances, pairTokenWorldAfterCall,
    emittedPairEventsAfterCall, pairTokenWorldAfterEvents,
    pairTokenWorldAfterEvent, pairTokenBalancesUnchanged, approve,
    allowancesSlot, msgSender, setMapping2, Contract.run, ContractResult.snd,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_transfer_run_keeps_token_balances
theorem transfer_run_keeps_token_balances
    (toAddr : Address) (amount : Uint256)
    (pre post : PairTokenBalances) (s : ContractState) :
  pair_transfer_run_keeps_token_balances toAddr amount pre post s := by
  intro h_post token account
  rw [h_post]
  by_cases h_balance : amount.val ≤ (s.storageMap 9 s.sender).val
  · by_cases h_same : s.sender = toAddr
    · subst h_same
      simp [pair_transfer_run_keeps_token_balances, pairTokenWorldAfterCall,
        emittedPairEventsAfterCall, pairTokenWorldAfterEvents,
        pairTokenWorldAfterEvent, pairTokenBalancesUnchanged, transfer,
        balancesSlot, msgSender, getMapping, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require,
        h_balance]
    · by_cases h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + amount.val
      · simp [pair_transfer_run_keeps_token_balances, pairTokenWorldAfterCall,
          emittedPairEventsAfterCall, pairTokenWorldAfterEvents,
          pairTokenWorldAfterEvent, pairTokenBalancesUnchanged, transfer,
          balancesSlot, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
      · simp [pair_transfer_run_keeps_token_balances, pairTokenWorldAfterCall,
          emittedPairEventsAfterCall, pairTokenWorldAfterEvents,
          pairTokenWorldAfterEvent, pairTokenBalancesUnchanged, transfer,
          balancesSlot, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
  · simp [pair_transfer_run_keeps_token_balances, pairTokenWorldAfterCall,
      emittedPairEventsAfterCall, pairTokenWorldAfterEvents,
      pairTokenWorldAfterEvent, pairTokenBalancesUnchanged, transfer,
      balancesSlot, msgSender, getMapping, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_balance]

-- tama: discharges=pair_transferFrom_run_keeps_token_balances
theorem transferFrom_run_keeps_token_balances
    (fromAddr toAddr : Address) (amount : Uint256)
    (pre post : PairTokenBalances) (s : ContractState) :
  pair_transferFrom_run_keeps_token_balances fromAddr toAddr amount pre post s := by
  intro h_post token account
  rw [h_post]
  by_cases h_allowance : amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val
  · by_cases h_balance : amount.val ≤ (s.storageMap 9 fromAddr).val
    · by_cases h_same : fromAddr = toAddr
      · subst h_same
        by_cases h_max :
            s.storageMap2 10 fromAddr s.sender =
              maxUint256
        · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
          have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
            simpa [h_max] using h_allowance
          simp [pair_transferFrom_run_keeps_token_balances,
            pairTokenWorldAfterCall, emittedPairEventsAfterCall,
            pairTokenWorldAfterEvents, pairTokenWorldAfterEvent,
            pairTokenBalancesUnchanged, transferFrom, allowancesSlot,
            balancesSlot, msgSender, getMapping2, getMapping, setMapping2,
            Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Verity.pure, Pure.pure, Verity.require, h_allowance,
            h_allowance_max, h_balance, h_max]
        · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
          simp [pair_transferFrom_run_keeps_token_balances,
            pairTokenWorldAfterCall, emittedPairEventsAfterCall,
            pairTokenWorldAfterEvents, pairTokenWorldAfterEvent,
            pairTokenBalancesUnchanged, transferFrom, allowancesSlot,
            balancesSlot, msgSender, getMapping2, getMapping, setMapping2,
            Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Verity.pure, Pure.pure, Verity.require, h_allowance, h_balance,
            h_max]
      · by_cases h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + amount.val
        · simp [pair_transferFrom_run_keeps_token_balances,
            pairTokenWorldAfterCall, emittedPairEventsAfterCall,
            pairTokenWorldAfterEvents, pairTokenWorldAfterEvent,
            pairTokenBalancesUnchanged, transferFrom, allowancesSlot,
            balancesSlot, msgSender, getMapping2, getMapping, setMapping,
            Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
            Pure.pure, Verity.pure, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            h_allowance, h_balance, h_same, h_overflow]
        · by_cases h_max :
            s.storageMap2 10 fromAddr s.sender =
              maxUint256
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
              simpa [h_max] using h_allowance
            simp [pair_transferFrom_run_keeps_token_balances,
              pairTokenWorldAfterCall, emittedPairEventsAfterCall,
              pairTokenWorldAfterEvents, pairTokenWorldAfterEvent,
              pairTokenBalancesUnchanged, transferFrom, allowancesSlot,
              balancesSlot, msgSender, getMapping2, getMapping, setMapping,
              setMapping2, Contract.run, ContractResult.snd, Verity.bind,
              Bind.bind, Pure.pure, Verity.pure, Verity.require,
              Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
              h_allowance, h_allowance_max, h_balance, h_same, h_overflow,
              h_max]
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            simp [pair_transferFrom_run_keeps_token_balances,
              pairTokenWorldAfterCall, emittedPairEventsAfterCall,
              pairTokenWorldAfterEvents, pairTokenWorldAfterEvent,
              pairTokenBalancesUnchanged, transferFrom, allowancesSlot,
              balancesSlot, msgSender, getMapping2, getMapping, setMapping,
              setMapping2, Contract.run, ContractResult.snd, Verity.bind,
              Bind.bind, Pure.pure, Verity.pure, Verity.require,
              Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
              h_allowance, h_balance, h_same, h_overflow, h_max]
    · simp [pair_transferFrom_run_keeps_token_balances,
        pairTokenWorldAfterCall, emittedPairEventsAfterCall,
        pairTokenWorldAfterEvents, pairTokenWorldAfterEvent,
        pairTokenBalancesUnchanged, transferFrom, allowancesSlot, balancesSlot,
        msgSender, getMapping2, getMapping, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.require, h_allowance, h_balance]
  · simp [pair_transferFrom_run_keeps_token_balances, pairTokenWorldAfterCall,
      emittedPairEventsAfterCall, pairTokenWorldAfterEvents,
      pairTokenWorldAfterEvent, pairTokenBalancesUnchanged, transferFrom,
      allowancesSlot, msgSender, getMapping2, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.require, h_allowance]

theorem pair_revert_keeps_pair_state {α : Type}
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


-- tama: discharges=pair_initialize_run_success_sets_tokens
theorem initialize_run_success_sets_tokens
    (token0Value token1Value : Address) (s : ContractState) :
  pair_initialize_run_success_sets_tokens token0Value token1Value s := by
  intro h_sender h_token0_empty h_token1_empty
  have h_sender_raw : s.sender = s.storageAddr 0 := by
    simpa [factorySlot] using h_sender
  have h_token0_raw : s.storageAddr 1 = (0 : Address) := by
    simpa [token0Slot] using h_token0_empty
  have h_token1_raw : s.storageAddr 2 = (0 : Address) := by
    simpa [token1Slot] using h_token1_empty
  have h_token_slots_distinct : (1 : Nat) ≠ 2 := by
    omega
  simp [pair_initialize_run_success_sets_tokens, «initialize», msgSender,
    getStorageAddr, setStorageAddr, Verity.require, Contract.run,
    ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    h_sender_raw, h_token0_raw, h_token1_raw, h_token_slots_distinct]

-- tama: discharges=pair_initialize_run_success_keeps_amm_accounting
theorem initialize_run_success_keeps_amm_accounting
    (token0Value token1Value : Address) (s : ContractState) :
  pair_initialize_run_success_keeps_amm_accounting token0Value token1Value s := by
  intro h_sender h_token0_empty h_token1_empty
  have h_sender_raw : s.sender = s.storageAddr 0 := by
    simpa [factorySlot] using h_sender
  have h_token0_raw : s.storageAddr 1 = (0 : Address) := by
    simpa [token0Slot] using h_token0_empty
  have h_token1_raw : s.storageAddr 2 = (0 : Address) := by
    simpa [token1Slot] using h_token1_empty
  simp [pair_initialize_run_success_keeps_amm_accounting, «initialize»,
    msgSender, getStorageAddr, setStorageAddr, Verity.require, Contract.run,
    ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    h_sender_raw, h_token0_raw, h_token1_raw, reserve0Slot, reserve1Slot,
    totalSupplySlot]

theorem approve_properties_after_run
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

-- tama: discharges=pair_approve_keeps_pool_storage
theorem approve_keeps_pool_storage
    (spender : Address) (amount : Uint256) (s : ContractState) :
  pair_approve_keeps_pool_storage spender amount s ((approve spender amount).run s) := by
  unfold pair_approve_keeps_pool_storage
  funext slotIdx
  simp [approve, allowancesSlot, msgSender, setMapping2, Contract.run,
    ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_approve_emits_approval
theorem approve_emits_approval (spender : Address) (amount : Uint256) (s : ContractState) :
  pair_approve_emits_approval spender amount s ((approve spender amount).run s) :=
  (approve_properties_after_run spender amount s).2.2.2.2

theorem transfer_properties_after_run
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_run_revert_balance_low toAddr amount s ∧
  pair_transfer_to_self_keeps_balances toAddr amount s ((transfer toAddr amount).run s) ∧
  pair_transfer_run_revert_recipient_balance_overflow toAddr amount s ∧
  pair_transfer_moves_tokens_between_distinct_accounts toAddr amount s
    ((transfer toAddr amount).run s) ∧
  pair_transfer_keeps_total_supply toAddr amount s ((transfer toAddr amount).run s) ∧
  pair_transfer_emits_transfer toAddr amount s ((transfer toAddr amount).run s) := by
  unfold pair_transfer_run_revert_balance_low
    pair_transfer_to_self_keeps_balances
    pair_transfer_run_revert_recipient_balance_overflow
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


-- tama: discharges=pair_transfer_to_self_keeps_balances
theorem transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_to_self_keeps_balances toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.1


-- tama: discharges=pair_transfer_moves_tokens_between_distinct_accounts
theorem transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_moves_tokens_between_distinct_accounts toAddr amount s
    ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.2.1

theorem transfer_run_storageAddr_frame
    (toAddr : Address) (amount : Uint256) (s : ContractState) (i : Nat) :
  ((transfer toAddr amount).run s).snd.storageAddr i = s.storageAddr i := by
  by_cases h_balance : amount.val ≤ (s.storageMap 9 s.sender).val
  · by_cases h_same : s.sender = toAddr
    · subst h_same
      simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, h_balance]
    · by_cases h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + amount.val
      · simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
      · simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
  · simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance]

theorem transfer_run_thisAddress_frame
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  ((transfer toAddr amount).run s).snd.thisAddress = s.thisAddress := by
  by_cases h_balance : amount.val ≤ (s.storageMap 9 s.sender).val
  · by_cases h_same : s.sender = toAddr
    · subst h_same
      simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, h_balance]
    · by_cases h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + amount.val
      · simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
      · simp [transfer, balancesSlot, msgSender, getMapping, setMapping, Contract.run,
          ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
          Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
  · simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance]

theorem transfer_caller_lp_sub
    (caller : Address) (amount : Uint256) (s : ContractState)
    (hSender : s.sender = caller)
    (hCallerNeSelf : caller ≠ pairSelf s)
    (hBalance : amount.val ≤ (s.storageMap balancesSlot.slot caller).val)
    (hNoOverflow :
      (s.storageMap balancesSlot.slot (pairSelf s)).val + amount.val ≤
        Verity.Stdlib.Math.MAX_UINT256) :
  ((transfer (pairSelf s) amount).run s).snd.storageMap balancesSlot.slot caller =
    s.storageMap balancesSlot.slot caller - amount := by
  have hBalanceRaw : amount.val ≤ (s.storageMap balancesSlot.slot s.sender).val := by
    simpa [hSender] using hBalance
  have hSenderNeSelf : s.sender ≠ pairSelf s := by
    simpa [hSender] using hCallerNeSelf
  rcases transfer_moves_tokens_between_distinct_accounts (pairSelf s) amount s
      hBalanceRaw hSenderNeSelf hNoOverflow with
    ⟨_hSuccess, hSenderSub, _hPairAdd⟩
  simpa [hSender] using hSenderSub

theorem transfer_pairSelf_lp_add
    (caller : Address) (amount : Uint256) (s : ContractState)
    (hSender : s.sender = caller)
    (hCallerNeSelf : caller ≠ pairSelf s)
    (hBalance : amount.val ≤ (s.storageMap balancesSlot.slot caller).val)
    (hNoOverflow :
      (s.storageMap balancesSlot.slot (pairSelf s)).val + amount.val ≤
        Verity.Stdlib.Math.MAX_UINT256) :
  ((transfer (pairSelf s) amount).run s).snd.storageMap balancesSlot.slot (pairSelf s) =
    s.storageMap balancesSlot.slot (pairSelf s) + amount := by
  have hBalanceRaw : amount.val ≤ (s.storageMap balancesSlot.slot s.sender).val := by
    simpa [hSender] using hBalance
  have hSenderNeSelf : s.sender ≠ pairSelf s := by
    simpa [hSender] using hCallerNeSelf
  rcases transfer_moves_tokens_between_distinct_accounts (pairSelf s) amount s
      hBalanceRaw hSenderNeSelf hNoOverflow with
    ⟨_hSuccess, _hSenderSub, hPairAdd⟩
  exact hPairAdd

-- tama: discharges=pair_transfer_keeps_total_supply
theorem transfer_keeps_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_keeps_total_supply toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.2.2.1

-- tama: discharges=pair_transfer_keeps_pool_storage
theorem transfer_keeps_pool_storage
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_keeps_pool_storage toAddr amount s ((transfer toAddr amount).run s) := by
  unfold pair_transfer_keeps_pool_storage
  funext slotIdx
  by_cases h_balance : amount.val ≤ (s.storageMap 9 s.sender).val
  · by_cases h_same : s.sender = toAddr
    · subst h_same
      simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
        ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
        Verity.require, h_balance]
    · by_cases h_overflow :
        Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + amount.val
      · simp [transfer, balancesSlot, msgSender, getMapping, setMapping,
          Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
      · simp [transfer, balancesSlot, msgSender, getMapping, setMapping,
          Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
          Pure.pure, Verity.require, Verity.Stdlib.Math.requireSomeUint,
          Verity.Stdlib.Math.safeAdd, h_balance, h_same, h_overflow]
  · simp [transfer, balancesSlot, msgSender, getMapping, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_balance]

-- tama: discharges=pair_transfer_emits_transfer
theorem transfer_emits_transfer
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_emits_transfer toAddr amount s ((transfer toAddr amount).run s) :=
  (transfer_properties_after_run toAddr amount s).2.2.2.2.2

theorem transferFrom_properties_after_run
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_run_revert_allowance_low fromAddr toAddr amount s ∧
  pair_transferFrom_run_revert_balance_low fromAddr toAddr amount s ∧
  pair_transferFrom_run_revert_recipient_balance_overflow fromAddr toAddr amount s ∧
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
  unfold pair_transferFrom_run_revert_allowance_low
    pair_transferFrom_run_revert_balance_low
    pair_transferFrom_run_revert_recipient_balance_overflow
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

-- tama: discharges=pair_transferFrom_keeps_pool_storage
theorem transferFrom_keeps_pool_storage
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_keeps_pool_storage fromAddr toAddr amount s
    ((transferFrom fromAddr toAddr amount).run s) := by
  unfold pair_transferFrom_keeps_pool_storage
  funext slotIdx
  by_cases h_allowance : amount.val ≤ (s.storageMap2 10 fromAddr s.sender).val
  · by_cases h_balance : amount.val ≤ (s.storageMap 9 fromAddr).val
    · by_cases h_same : fromAddr = toAddr
      · subst h_same
        by_cases h_max :
            s.storageMap2 10 fromAddr s.sender =
              maxUint256
        · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
          have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
            simpa [h_max] using h_allowance
          simp [transferFrom, allowancesSlot, balancesSlot, msgSender,
            getMapping2, getMapping, setMapping2, Contract.run,
            ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
            Verity.require, h_allowance, h_allowance_max, h_balance, h_max]
        · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
          simp [transferFrom, allowancesSlot, balancesSlot, msgSender,
            getMapping2, getMapping, setMapping2, Contract.run,
            ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
            Verity.require, h_allowance, h_balance, h_max]
      · by_cases h_overflow :
          Verity.Stdlib.Math.MAX_UINT256 < (s.storageMap 9 toAddr).val + amount.val
        · simp [transferFrom, allowancesSlot, balancesSlot, msgSender,
            getMapping2, getMapping, setMapping, Contract.run, ContractResult.snd,
            Verity.bind, Bind.bind, Pure.pure, Verity.pure, Verity.require,
            Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
            h_allowance, h_balance, h_same, h_overflow]
        · by_cases h_max :
            s.storageMap2 10 fromAddr s.sender =
              maxUint256
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            have h_allowance_max : amount.val ≤ (sub 0 1 : Uint256).val := by
              simpa [h_max] using h_allowance
            simp [transferFrom, allowancesSlot, balancesSlot, msgSender,
              getMapping2, getMapping, setMapping, setMapping2, Contract.run,
              ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
              Verity.require, Verity.Stdlib.Math.requireSomeUint,
              Verity.Stdlib.Math.safeAdd, h_allowance, h_allowance_max,
              h_balance, h_same, h_overflow, h_max]
          · simp [Verity.Stdlib.Math.MAX_UINT256, Verity.Core.MAX_UINT256] at h_max
            simp [transferFrom, allowancesSlot, balancesSlot, msgSender,
              getMapping2, getMapping, setMapping, setMapping2, Contract.run,
              ContractResult.snd, Verity.bind, Bind.bind, Pure.pure, Verity.pure,
              Verity.require, Verity.Stdlib.Math.requireSomeUint,
              Verity.Stdlib.Math.safeAdd, h_allowance, h_balance, h_same,
              h_overflow, h_max]
    · simp [transferFrom, allowancesSlot, balancesSlot, msgSender, getMapping2,
        getMapping, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
        Verity.require, h_allowance, h_balance]
  · simp [transferFrom, allowancesSlot, msgSender, getMapping2, Contract.run,
      ContractResult.snd, Verity.bind, Bind.bind, Verity.require, h_allowance]

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
  exact (transfer_properties_after_run toAddr amount s).1

-- tama: discharges=pair_transfer_run_revert_recipient_balance_overflow
theorem transfer_run_revert_recipient_balance_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transfer_run_revert_recipient_balance_overflow toAddr amount s := by
  exact (transfer_properties_after_run toAddr amount s).2.2.1

-- tama: discharges=pair_transferFrom_run_revert_allowance_low
theorem transferFrom_run_revert_allowance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_run_revert_allowance_low fromAddr toAddr amount s := by
  exact (transferFrom_properties_after_run fromAddr toAddr amount s).1

-- tama: discharges=pair_transferFrom_run_revert_balance_low
theorem transferFrom_run_revert_balance_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_run_revert_balance_low fromAddr toAddr amount s := by
  exact (transferFrom_properties_after_run fromAddr toAddr amount s).2.1

-- tama: discharges=pair_transferFrom_run_revert_recipient_balance_overflow
theorem transferFrom_run_revert_recipient_balance_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState) :
  pair_transferFrom_run_revert_recipient_balance_overflow fromAddr toAddr amount s := by
  exact (transferFrom_properties_after_run fromAddr toAddr amount s).2.2.1

-- tama: discharges=pair_mint_run_revert_locked
theorem mint_run_revert_locked (toAddr : Address) (s : ContractState) :
  pair_mint_run_revert_locked toAddr s := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_mint_run_revert_locked, mint, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_mint_run_revert_balance0_overflow
theorem mint_run_revert_balance0_overflow
    (toAddr : Address) (s : ContractState) :
  pair_mint_run_revert_balance0_overflow toAddr s := by
  intro h_unlocked h_overflow
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_require_false :
      ¬ ((observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val) := by
    intro h
    exact (Nat.not_le_of_gt (by simpa [Verity.Core.Uint256.lt_def] using h_overflow)) h.1
  have h_guard_false :
      (decide (observedBalance0 s ≤ maxUint112) &&
        decide (observedBalance1 s ≤ maxUint112)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_guard_true
    have h_guard_parts :
        decide (observedBalance0 s ≤ maxUint112) = true ∧
          decide (observedBalance1 s ≤ maxUint112) = true := by
      simpa [Bool.and_eq_true] using h_guard_true
    apply h_require_false
    constructor
    · have h0 : observedBalance0 s ≤ maxUint112 := by
        simpa using h_guard_parts.1
      simpa [Verity.Core.Uint256.le_def] using h0
    · have h1 : observedBalance1 s ≤ maxUint112 := by
        simpa using h_guard_parts.2
      simpa [Verity.Core.Uint256.le_def] using h1
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  have h_guard_false_raw := h_guard_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_guard_false_raw
  simp only [pair_mint_run_revert_balance0_overflow, mint, UniswapV2PairBase.mint,
    unlockedSlot, token0Slot, token1Slot, maxUint112, UniswapV2PairBase.maxUint112,
    UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    Verity.Core.Uint256.le_def,
    getStorage, getStorageAddr, setStorage, msgSender, Verity.contractAddress,
    Contracts.balanceOf, Verity.require, Contract.run, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, observedBalance0, observedBalance1, pairToken0,
    pairToken1, pairSelf, TamaUniV2.erc20BalanceOf, h_unlocked_raw,
    h_lock_guard, h_require_false_raw, h_guard_false_raw, if_true, if_false,
    reduceCtorEq]

-- tama: discharges=pair_mint_run_revert_balance1_overflow
theorem mint_run_revert_balance1_overflow
    (toAddr : Address) (s : ContractState) :
  pair_mint_run_revert_balance1_overflow toAddr s := by
  intro h_unlocked h_overflow
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_require_false :
      ¬ ((observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val) := by
    intro h
    exact (Nat.not_le_of_gt (by simpa [Verity.Core.Uint256.lt_def] using h_overflow)) h.2
  have h_guard_false :
      (decide (observedBalance0 s ≤ maxUint112) &&
        decide (observedBalance1 s ≤ maxUint112)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_guard_true
    have h_guard_parts :
        decide (observedBalance0 s ≤ maxUint112) = true ∧
          decide (observedBalance1 s ≤ maxUint112) = true := by
      simpa [Bool.and_eq_true] using h_guard_true
    apply h_require_false
    constructor
    · have h0 : observedBalance0 s ≤ maxUint112 := by
        simpa using h_guard_parts.1
      simpa [Verity.Core.Uint256.le_def] using h0
    · have h1 : observedBalance1 s ≤ maxUint112 := by
        simpa using h_guard_parts.2
      simpa [Verity.Core.Uint256.le_def] using h1
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  have h_guard_false_raw := h_guard_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_guard_false_raw
  simp only [pair_mint_run_revert_balance1_overflow, mint, UniswapV2PairBase.mint,
    unlockedSlot, token0Slot, token1Slot, maxUint112, UniswapV2PairBase.maxUint112,
    UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    Verity.Core.Uint256.le_def,
    getStorage, getStorageAddr, setStorage, msgSender, Verity.contractAddress,
    Contracts.balanceOf, Verity.require, Contract.run, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, observedBalance0, observedBalance1, pairToken0,
    pairToken1, pairSelf, TamaUniV2.erc20BalanceOf, h_unlocked_raw,
    h_lock_guard, h_require_false_raw, h_guard_false_raw, if_true, if_false,
    reduceCtorEq]

-- tama: discharges=pair_burn_run_revert_locked
theorem burn_run_revert_locked (toAddr : Address) (s : ContractState) :
  pair_burn_run_revert_locked toAddr s := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_burn_run_revert_locked, burn, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_swap_run_revert_locked
theorem swap_run_revert_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_swap_run_revert_locked amount0Out amount1Out toAddr data s := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_swap_run_revert_locked, swap, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_swap_run_revert_zero_output
theorem swap_run_revert_zero_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_swap_run_revert_zero_output amount0Out amount1Out toAddr data s := by
  intro h_unlocked h_amount0 h_amount1
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  subst amount0Out
  subst amount1Out
  simp [pair_swap_run_revert_zero_output, swap, unlockedSlot, getStorage,
    Verity.blockTimestamp, Verity.require, Contract.run, Verity.bind, Bind.bind,
    h_unlocked_raw]

-- tama: discharges=pair_skim_run_revert_locked
theorem skim_run_revert_locked (toAddr : Address) (s : ContractState) :
  pair_skim_run_revert_locked toAddr s := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_skim_run_revert_locked, skim, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_skim_run_revert_balance0_below_reserve
theorem skim_run_revert_balance0_below_reserve
    (toAddr : Address) (s : ContractState) :
  pair_skim_run_revert_balance0_below_reserve toAddr s := by
  intro h_unlocked h_under
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_require_false :
      ¬ ((s.storage reserve0Slot.slot).val ≤ (observedBalance0 s).val ∧
        (s.storage reserve1Slot.slot).val ≤ (observedBalance1 s).val) := by
    intro h
    exact (Nat.not_le_of_gt (by simpa [Verity.Core.Uint256.lt_def] using h_under)) h.1
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_skim_run_revert_balance0_below_reserve, skim, UniswapV2PairBase.skim,
    unlockedSlot, token0Slot, token1Slot, reserve0Slot, reserve1Slot,
    getStorage, getStorageAddr, setStorage, Verity.contractAddress,
    Contracts.balanceOf, Verity.require, Contract.run, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, observedBalance0, observedBalance1, pairToken0,
    pairToken1, pairSelf, TamaUniV2.erc20BalanceOf, h_unlocked_raw,
    h_lock_guard, h_require_false_raw]

-- tama: discharges=pair_skim_run_revert_balance1_below_reserve
theorem skim_run_revert_balance1_below_reserve
    (toAddr : Address) (s : ContractState) :
  pair_skim_run_revert_balance1_below_reserve toAddr s := by
  intro h_unlocked h_under
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_require_false :
      ¬ ((s.storage reserve0Slot.slot).val ≤ (observedBalance0 s).val ∧
        (s.storage reserve1Slot.slot).val ≤ (observedBalance1 s).val) := by
    intro h
    exact (Nat.not_le_of_gt (by simpa [Verity.Core.Uint256.lt_def] using h_under)) h.2
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_skim_run_revert_balance1_below_reserve, skim, UniswapV2PairBase.skim,
    unlockedSlot, token0Slot, token1Slot, reserve0Slot, reserve1Slot,
    getStorage, getStorageAddr, setStorage, Verity.contractAddress,
    Contracts.balanceOf, Verity.require, Contract.run, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, observedBalance0, observedBalance1, pairToken0,
    pairToken1, pairSelf, TamaUniV2.erc20BalanceOf, h_unlocked_raw,
    h_lock_guard, h_require_false_raw]

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

-- tama: discharges=pair_skim_run_success_moves_exact_surplus_in_token_world
theorem skim_run_success_moves_exact_surplus_in_token_world
    (toAddr : Address) (pre post : PairTokenBalances) (s : ContractState) :
  pair_skim_run_success_moves_exact_surplus_in_token_world toAddr pre post s := by
  intro h_unlocked h_balance0 h_balance1 h_post
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
  rw [h_post]
  funext token account
  simp [pair_skim_run_success_moves_exact_surplus_in_token_world,
    skim, UniswapV2PairBase.skim, unlockedSlot, token0Slot, token1Slot,
    reserve0Slot, reserve1Slot, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.pairSafeTransfer, TamaUniV2.tracePairTokenSafeTransfer,
    TamaUniV2.pairTokenSafeTransferEvent, Contracts.safeTransfer,
    pairTokenWorldAfterCall, emittedPairEventsAfterCall,
    pairTokenWorldAfterEvents, pairTokenWorldAfterEvent,
    pairTokenWorldAfterTransfer, observedBalance0, observedBalance1,
    pairToken0, pairToken1, pairSelf, skimExcess0, skimExcess1,
    h_unlocked_raw, h_require_raw_unfold, addressOfNat_toNat_mod_uint256]

def pair_skim_run_success_matches_closed_world_step
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

theorem skim_run_success_matches_closed_world_step
    (toAddr : Address) (s : ContractState) :
  pair_skim_run_success_matches_closed_world_step toAddr s := by
  intro h_unlocked h_balance0 h_balance1
  have h_success :=
    skim_run_success_transfers_excess_and_restores_unlocked
      toAddr s h_unlocked h_balance0 h_balance1
  rcases h_success with ⟨h_run, _h_reserve0, _h_reserve1, _h_unlocked,
    _h_transfer0, _h_transfer1⟩
  rw [h_run]
  simp [pair_skim_run_success_matches_closed_world_step, PairWorldStep,
    PairWorldSkimStep, pairWorldFromConcreteState, pairWorldAfterSkimRun,
    pairWorldLockedLiquidity]

-- tama: discharges=pair_sync_run_revert_locked
theorem sync_run_revert_locked (s : ContractState) :
  pair_sync_run_revert_locked s := by
  intro h_locked
  have h_locked_raw : ¬ s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_locked
  simp [pair_sync_run_revert_locked, sync, unlockedSlot, getStorage,
    Verity.require, Contract.run, Verity.bind, Bind.bind, h_locked_raw]

-- tama: discharges=pair_reentrancy_guard_blocks_all_mutating_entrypoints
theorem reentrancy_guard_blocks_all_mutating_entrypoints
    (mintTo burnTo skimTo swapTo : Address)
    (amount0Out amount1Out : Uint256) (data : ByteArray)
    (s : ContractState) :
  pair_reentrancy_guard_blocks_all_mutating_entrypoints
    mintTo burnTo skimTo swapTo amount0Out amount1Out data s := by
  intro h_locked
  exact ⟨
    mint_run_revert_locked mintTo s h_locked,
    burn_run_revert_locked burnTo s h_locked,
    swap_run_revert_locked amount0Out amount1Out swapTo data s h_locked,
    skim_run_revert_locked skimTo s h_locked,
    sync_run_revert_locked s h_locked
  ⟩

-- tama: discharges=pair_flash_callback_runs_while_pair_is_locked
theorem flash_callback_runs_while_pair_is_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_flash_callback_runs_while_pair_is_locked amount0Out amount1Out toAddr data s := by
  intro _h_data h_success
  have h_unlocked : s.storage unlockedSlot.slot = (1 : Uint256) := by
    by_contra h_not
    have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
      simpa using h_not
    have h_revert := swap_run_revert_locked amount0Out amount1Out toAddr data s h_locked
    rw [h_revert] at h_success
    simp at h_success
  have h_callback_locked :
      (pairSwapCallbackState s).storage unlockedSlot.slot != (1 : Uint256) := by
    simpa [pairSwapCallbackState, setStorage, unlockedSlot] using
      (uint256_bne_true_of_ne (a := (0 : Uint256)) (b := (1 : Uint256)) (by decide))
  rcases reentrancy_guard_blocks_all_mutating_entrypoints
      toAddr toAddr toAddr toAddr amount0Out amount1Out data
      (pairSwapCallbackState s) h_callback_locked with
    ⟨h_mint, h_burn, h_swap, h_skim, h_sync⟩
  dsimp [pair_flash_callback_runs_while_pair_is_locked]
  constructor
  · rfl
  constructor
  · simp [pairSwapCallbackState, setStorage, unlockedSlot]
  constructor
  · exact h_unlocked
  constructor
  · exact h_mint
  constructor
  · exact h_burn
  constructor
  · exact h_swap
  constructor
  · exact h_skim
  · exact h_sync

-- tama: discharges=pair_flash_callback_reentry_attempts_revert_locked
theorem flash_callback_reentry_attempts_revert_locked
    (mintTo burnTo skimTo swapTo : Address)
    (amount0Out amount1Out nested0Out nested1Out : Uint256)
    (data nestedData : ByteArray)
    (s : ContractState) :
  pair_flash_callback_reentry_attempts_revert_locked
    mintTo burnTo skimTo swapTo amount0Out amount1Out nested0Out nested1Out
    data nestedData s := by
  intro _h_data
  exact reentrancy_guard_blocks_all_mutating_entrypoints
    mintTo burnTo skimTo swapTo nested0Out nested1Out nestedData
    (pairLockedState s) (by
      simp [pairLockedState, unlockedSlot]
      decide)


end TamaUniV2.Proof.UniswapV2PairProof
