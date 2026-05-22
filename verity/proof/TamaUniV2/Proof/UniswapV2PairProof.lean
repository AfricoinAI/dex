import TamaUniV2.Spec.UniswapV2PairSpec
import Verity.Proofs.Stdlib.Automation

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

private theorem uint256_bne_true_of_ne {a b : Uint256} (h : a ≠ b) :
    (a != b) = true := by
  simpa [bne_iff_ne] using h

private theorem uint256_pos_of_ne_zero {a : Uint256} (h : a ≠ 0) :
    a > 0 := by
  change 0 < a.val
  by_contra h_not_pos
  have h_val_zero : a.val = 0 := by
    omega
  apply h
  cases a with
  | mk val isLt =>
      simp at h_val_zero
      subst val
      rfl

private theorem addressOfNat_toNat_mod_uint256 (a : Address) :
    Core.Address.ofNat (Core.Address.toNat a % Core.Uint256.modulus) = a := by
  apply Core.Address.toNat_injective
  have h_lt_uint : Core.Address.toNat a < Core.Uint256.modulus := by
    have h_lt_addr : Core.Address.toNat a < Core.Address.modulus :=
      Core.Address.val_lt_modulus a
    have h_addr_lt_uint : Core.Address.modulus < Core.Uint256.modulus := by
      decide
    exact Nat.lt_trans h_lt_addr h_addr_lt_uint
  have h_uint_mod : Core.Address.toNat a % Core.Uint256.modulus = Core.Address.toNat a :=
    Nat.mod_eq_of_lt h_lt_uint
  have h_addr_mod : Core.Address.toNat a % Core.Address.modulus = Core.Address.toNat a := by
    simp [Core.Address.toNat, Core.Address.val_mod_modulus]
  simp [h_uint_mod, h_addr_mod]

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

private theorem transfer_properties_after_run
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

private theorem transferFrom_properties_after_run
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

private def pair_skim_run_success_matches_closed_world_step
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

private theorem skim_run_success_matches_closed_world_step
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
  intro _h_data
  rfl

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

private theorem swap_success_run_implies_lock_open
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) :
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      s.storage unlockedSlot.slot = 1 := by
  intro h_run h_success
  by_contra h_not_open
  have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
    simpa using h_not_open
  have h_revert :=
    swap_run_revert_locked amount0Out amount1Out toAddr data s h_locked
  rw [← h_run, h_success] at h_revert
  cases h_revert

private theorem skim_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      s.storage unlockedSlot.slot = 1 := by
  intro h_run h_success
  by_contra h_not_open
  have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
    simpa using h_not_open
  have h_revert := skim_run_revert_locked toAddr s h_locked
  rw [← h_run, h_success] at h_revert
  cases h_revert




-- tama: discharges=pair_swap_success_run_implies_nonzero_output
theorem swap_success_run_implies_nonzero_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) :
  pair_swap_success_run_implies_nonzero_output
    amount0Out amount1Out toAddr data s result := by
  intro h_run h_success
  by_cases h_amount0 : amount0Out = 0
  · by_cases h_amount1 : amount1Out = 0
    · have h_unlocked :=
        swap_success_run_implies_lock_open
          amount0Out amount1Out toAddr data s result h_run h_success
      have h_revert :=
        swap_run_revert_zero_output
          amount0Out amount1Out toAddr data s h_unlocked h_amount0 h_amount1
      rw [h_run] at h_success
      rw [h_revert] at h_success
      cases h_success
    · exact Or.inr h_amount1
  · exact Or.inl h_amount0


-- tama: discharges=pair_skim_success_run_implies_balances_back_reserves
theorem skim_success_run_implies_balances_back_reserves
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_implies_balances_back_reserves toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  constructor
  · by_contra h_not_bound
    have h_not_bound_val :
        ¬ (s.storage reserve0Slot.slot).val ≤ (observedBalance0 s).val := by
      simpa [Verity.Core.Uint256.le_def] using h_not_bound
    have h_under : observedBalance0 s < s.storage reserve0Slot.slot := by
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_not_bound_val
    have h_revert := skim_run_revert_balance0_below_reserve toAddr s h_unlocked h_under
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success
  · by_contra h_not_bound
    have h_not_bound_val :
        ¬ (s.storage reserve1Slot.slot).val ≤ (observedBalance1 s).val := by
      simpa [Verity.Core.Uint256.le_def] using h_not_bound
    have h_under : observedBalance1 s < s.storage reserve1Slot.slot := by
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_not_bound_val
    have h_revert := skim_run_revert_balance1_below_reserve toAddr s h_unlocked h_under
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success

-- tama: discharges=pair_skim_success_run_restores_unlocked_from_run
theorem skim_success_run_restores_unlocked_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_restores_unlocked_from_run toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  rcases skim_success_run_implies_balances_back_reserves
      toAddr s result h_run h_success with
    ⟨h_balance0, h_balance1⟩
  have h_skim :=
    skim_run_success_transfers_excess_and_restores_unlocked
      toAddr s h_unlocked h_balance0 h_balance1
  rcases h_skim with ⟨_h_actual, _h_reserve0, _h_reserve1, h_restored,
    _h_transfer0, _h_transfer1⟩
  rw [h_run]
  exact h_restored

private def pair_skim_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      PairWorldStep PairWorldAction.skim
        (pairWorldFromConcreteState s)
        (pairWorldAfterSkimRun s)

private theorem skim_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_matches_closed_world_step_from_run toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  rcases skim_success_run_implies_balances_back_reserves
      toAddr s result h_run h_success with
    ⟨h_balance0, h_balance1⟩
  have h_step := skim_run_success_matches_closed_world_step toAddr s
    h_unlocked h_balance0 h_balance1
  rw [← h_run, h_success] at h_step
  exact h_step

private def pair_skim_success_run_preserves_world
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (skim toAddr).run s →
    result = ContractResult.success () result.snd →
      pairWorldFromConcreteState result.snd = pairWorldFromConcreteState s

private theorem skim_success_run_preserves_world
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_preserves_world toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  rcases skim_success_run_implies_balances_back_reserves toAddr s result h_run h_success with
    ⟨h_b0, h_b1⟩
  subst h_run
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by simpa [unlockedSlot] using h_unlocked
  have h_require_raw :
      (s.storage 3).val ≤ (observedBalance0 s).val ∧
      (s.storage 4).val ≤ (observedBalance1 s).val := by
    refine ⟨?_, ?_⟩
    · simpa [reserve0Slot] using h_b0
    · simpa [reserve1Slot] using h_b1
  have h_require_raw_unfold := h_require_raw
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_require_raw_unfold
  simp [skim, UniswapV2PairBase.skim, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.pairSafeTransfer, TamaUniV2.tracePairTokenSafeTransfer,
    TamaUniV2.pairTokenSafeTransferEvent, Contracts.safeTransfer,
    pairWorldFromConcreteState, pairWorldLockedLiquidity,
    h_unlocked_raw, h_require_raw_unfold]

-- tama: discharges=pair_skim_success_reaches_expected_pair_state
theorem skim_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances)
    (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_reaches_expected_pair_state toAddr preTokens s result := by
  intro h_run h_success h_boundary
  rcases h_boundary with ⟨⟨h_before, h_post⟩, h_expected⟩
  have h_step :=
    skim_success_run_matches_closed_world_step_from_run
      toAddr s result h_run h_success
  constructor
  · rw [h_before, h_expected]
    exact h_step
  · exact h_post

-- tama: discharges=pair_sync_run_revert_balance0_overflow
theorem sync_run_revert_balance0_overflow (s : ContractState) :
  pair_sync_run_revert_balance0_overflow s := by
  intro h_unlocked h_overflow
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_require_false :
      ¬ ((observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val) := by
    intro h
    exact (Nat.not_le_of_gt (by simpa [Verity.Core.Uint256.lt_def] using h_overflow)) h.1
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_sync_run_revert_balance0_overflow, sync, UniswapV2PairBase.sync,
    unlockedSlot, token0Slot, token1Slot, maxUint112, UniswapV2PairBase.maxUint112,
    getStorage, getStorageAddr, setStorage, Verity.blockTimestamp,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, observedBalance0,
    observedBalance1, pairToken0, pairToken1, pairSelf, TamaUniV2.erc20BalanceOf,
    h_unlocked_raw, h_require_false_raw]

-- tama: discharges=pair_sync_run_revert_balance1_overflow
theorem sync_run_revert_balance1_overflow (s : ContractState) :
  pair_sync_run_revert_balance1_overflow s := by
  intro h_unlocked h_overflow
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_require_false :
      ¬ ((observedBalance0 s).val ≤ maxUint112.val ∧
        (observedBalance1 s).val ≤ maxUint112.val) := by
    intro h
    exact (Nat.not_le_of_gt (by simpa [Verity.Core.Uint256.lt_def] using h_overflow)) h.2
  have h_require_false_raw := h_require_false
  dsimp [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure] at h_require_false_raw
  simp [pair_sync_run_revert_balance1_overflow, sync, UniswapV2PairBase.sync,
    unlockedSlot, token0Slot, token1Slot, maxUint112, UniswapV2PairBase.maxUint112,
    getStorage, getStorageAddr, setStorage, Verity.blockTimestamp,
    Verity.contractAddress, Contracts.balanceOf, Verity.require, Contract.run,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, observedBalance0,
    observedBalance1, pairToken0, pairToken1, pairSelf, TamaUniV2.erc20BalanceOf,
    h_unlocked_raw, h_require_false_raw]

private theorem sync_success_run_implies_balances_fit_uint112
    (s : ContractState) (result : ContractResult Unit) :
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      observedBalance0 s ≤ maxUint112 ∧ observedBalance1 s ≤ maxUint112 := by
  intro h_run h_success
  have h_unlocked : s.storage unlockedSlot.slot = 1 := by
    by_contra h_not_open
    have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
      simpa using h_not_open
    have h_revert := sync_run_revert_locked s h_locked
    rw [← h_run, h_success] at h_revert
    cases h_revert
  constructor
  · by_contra h_not_le
    have h_gt : observedBalance0 s > maxUint112 := by
      have h_nat : ¬ (observedBalance0 s).val ≤ maxUint112.val := by
        simpa [Verity.Core.Uint256.le_def] using h_not_le
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_nat
    have h_revert := sync_run_revert_balance0_overflow s h_unlocked h_gt
    rw [← h_run, h_success] at h_revert
    cases h_revert
  · by_contra h_not_le
    have h_gt : observedBalance1 s > maxUint112 := by
      have h_nat : ¬ (observedBalance1 s).val ≤ maxUint112.val := by
        simpa [Verity.Core.Uint256.le_def] using h_not_le
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_nat
    have h_revert := sync_run_revert_balance1_overflow s h_unlocked h_gt
    rw [← h_run, h_success] at h_revert
    cases h_revert

private theorem mint_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) :
  result = (mint toAddr).run s →
    (∃ liquidity, result = ContractResult.success liquidity result.snd) →
      s.storage unlockedSlot.slot = 1 := by
  intro h_run h_success_exists
  rcases h_success_exists with ⟨liquidity, h_success⟩
  by_contra h_not_open
  have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
    simpa using h_not_open
  have h_revert := mint_run_revert_locked toAddr s h_locked
  rw [← h_run, h_success] at h_revert
  cases h_revert

private theorem mint_success_run_implies_balances_fit_uint112
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) :
  result = (mint toAddr).run s →
    (∃ liquidity, result = ContractResult.success liquidity result.snd) →
      observedBalance0 s ≤ maxUint112 ∧ observedBalance1 s ≤ maxUint112 := by
  intro h_run h_success_exists
  have h_unlocked :=
    mint_success_run_implies_lock_open toAddr s result h_run h_success_exists
  rcases h_success_exists with ⟨liquidity, h_success⟩
  constructor
  · by_contra h_not_le
    have h_gt : observedBalance0 s > maxUint112 := by
      have h_nat : ¬ (observedBalance0 s).val ≤ maxUint112.val := by
        simpa [Verity.Core.Uint256.le_def] using h_not_le
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_nat
    have h_revert := mint_run_revert_balance0_overflow toAddr s h_unlocked h_gt
    rw [← h_run, h_success] at h_revert
    cases h_revert
  · by_contra h_not_le
    have h_gt : observedBalance1 s > maxUint112 := by
      have h_nat : ¬ (observedBalance1 s).val ≤ maxUint112.val := by
        simpa [Verity.Core.Uint256.le_def] using h_not_le
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_nat
    have h_revert := mint_run_revert_balance1_overflow toAddr s h_unlocked h_gt
    rw [← h_run, h_success] at h_revert
    cases h_revert

private def pair_sync_expected_matches_closed_world_step
    (s : ContractState) : Prop :=
  observedBalance0 s ≤ maxUint112 →
    observedBalance1 s ≤ maxUint112 →
      PairWorldStep PairWorldAction.sync
        (pairWorldFromConcreteState s)
        (pairWorldAfterSyncRun s)

private theorem sync_expected_matches_closed_world_step (s : ContractState) :
  pair_sync_expected_matches_closed_world_step s := by
  intro h_bound0 h_bound1
  simp [pair_sync_expected_matches_closed_world_step, PairWorldStep,
    PairWorldSyncStep, pairWorldFromConcreteState, pairWorldAfterSyncRun,
    pairWorldLockedLiquidity, maxUint112Nat, maxUint112,
    UniswapV2PairBase.maxUint112]
  exact ⟨by simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using h_bound0,
    by simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using h_bound1⟩

private def pair_sync_success_run_matches_closed_world_step
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      observedBalance0 s ≤ maxUint112 →
        observedBalance1 s ≤ maxUint112 →
          PairWorldStep PairWorldAction.sync
            (pairWorldFromConcreteState s)
            (pairWorldAfterSyncRun s)

private theorem sync_success_run_matches_closed_world_step
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_matches_closed_world_step s result := by
  intro _h_run _h_success h_bound0 h_bound1
  exact sync_expected_matches_closed_world_step s h_bound0 h_bound1



private def pair_sync_success_run_matches_closed_world_step_from_run
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      PairWorldStep PairWorldAction.sync
        (pairWorldFromConcreteState s)
        (pairWorldAfterSyncRun s)

private theorem sync_success_run_matches_closed_world_step_from_run
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_matches_closed_world_step_from_run s result := by
  intro h_run h_success
  rcases sync_success_run_implies_balances_fit_uint112
      s result h_run h_success with
    ⟨h_bound0, h_bound1⟩
  exact sync_expected_matches_closed_world_step s h_bound0 h_bound1

private theorem sync_unlocked_raw
    (s : ContractState) (h_unlocked : s.storage unlockedSlot.slot = 1) :
    s.storage 11 = (1 : Uint256) := by simpa [unlockedSlot] using h_unlocked

private theorem sync_bound_val
    (s : ContractState)
    (h0 : observedBalance0 s ≤ maxUint112) (h1 : observedBalance1 s ≤ maxUint112) :
    (observedBalance0 s).val ≤ maxUint112.val ∧ (observedBalance1 s).val ≤ maxUint112.val := by
  rw [Verity.Core.Uint256.le_def] at h0 h1
  exact ⟨h0, h1⟩

private theorem sync_post_reserve0_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    (sync.run s).snd.storage reserve0Slot.slot = observedBalance0 s := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit := h_bfold
  simp only [maxUint112, UniswapV2PairBase.maxUint112] at h_blit
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

private theorem sync_post_reserve1_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    (sync.run s).snd.storage reserve1Slot.slot = observedBalance1 s := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit := h_bfold
  simp only [maxUint112, UniswapV2PairBase.maxUint112] at h_blit
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

private theorem sync_post_supply_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    (sync.run s).snd.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit := h_bfold
  simp only [maxUint112, UniswapV2PairBase.maxUint112] at h_blit
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

private theorem sync_post_obs0_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    observedBalance0 (sync.run s).snd = observedBalance0 s := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit := h_bfold
  simp only [maxUint112, UniswapV2PairBase.maxUint112] at h_blit
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore, ContractResult.fst, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore, ContractResult.fst, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

private theorem sync_post_obs1_run
    (s : ContractState)
    (h_unlocked : s.storage unlockedSlot.slot = 1)
    (h_bound0 : observedBalance0 s ≤ maxUint112)
    (h_bound1 : observedBalance1 s ≤ maxUint112) :
    observedBalance1 (sync.run s).snd = observedBalance1 s := by
  have h_unlocked_raw := sync_unlocked_raw s h_unlocked
  have h_bfold := sync_bound_val s h_bound0 h_bound1
  dsimp only [observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    token0Slot, token1Slot, UniswapV2PairBase.token0Slot, UniswapV2PairBase.token1Slot,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run, ContractResult.fst,
    Verity.pure, Pure.pure] at h_bfold
  have h_blit := h_bfold
  simp only [maxUint112, UniswapV2PairBase.maxUint112] at h_blit
  simp [sync, UniswapV2PairBase.sync, getStorage, getStorageAddr, setStorage,
    Verity.contractAddress, Verity.blockTimestamp, Contracts.balanceOf, Verity.require,
    Contract.run, ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    TamaUniV2.erc20BalanceOf, Contracts.rawLog, Contracts.mstore,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    h_unlocked_raw, h_blit,
    -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore, ContractResult.fst, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))
  all_goals (try (split_ifs <;>
    simp [getStorage, getStorageAddr, setStorage, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, ContractResult.fst, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore, ContractResult.fst, TamaUniV2.erc20BalanceOf, Contracts.balanceOf,
      observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
      h_bfold,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]))

private def pair_sync_success_run_reaches_world
    (s : ContractState) (result : ContractResult Unit) : Prop :=
  result = (sync).run s →
    result = ContractResult.success () result.snd →
      pairWorldFromConcreteState result.snd = pairWorldAfterSyncRun s

private theorem sync_success_run_reaches_world
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_reaches_world s result := by
  intro h_run h_success
  have h_unlocked : s.storage unlockedSlot.slot = 1 := by
    by_contra h_not_open
    have h_locked : s.storage unlockedSlot.slot != (1 : Uint256) := by
      simpa using h_not_open
    have h_revert := sync_run_revert_locked s h_locked
    rw [← h_run, h_success] at h_revert
    cases h_revert
  rcases sync_success_run_implies_balances_fit_uint112 s result h_run h_success with
    ⟨h_bound0, h_bound1⟩
  subst h_run
  simp only [pairWorldFromConcreteState, pairWorldAfterSyncRun, pairWorldLockedLiquidity,
    sync_post_obs0_run s h_unlocked h_bound0 h_bound1,
    sync_post_obs1_run s h_unlocked h_bound0 h_bound1,
    sync_post_reserve0_run s h_unlocked h_bound0 h_bound1,
    sync_post_reserve1_run s h_unlocked h_bound0 h_bound1,
    sync_post_supply_run s h_unlocked h_bound0 h_bound1]

-- tama: discharges=pair_sync_success_reaches_expected_pair_state
theorem sync_success_reaches_expected_pair_state
    (preTokens : PairTokenBalances)
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_reaches_expected_pair_state preTokens s result := by
  intro h_run h_success h_boundary
  rcases h_boundary with ⟨⟨h_before, h_post⟩, h_expected⟩
  have h_step :=
    sync_success_run_matches_closed_world_step_from_run s result h_run h_success
  constructor
  · rw [h_before, h_expected]
    exact h_step
  · exact h_post

-- tama: discharges=pair_flash_callback_module_gates_nonempty_data
theorem flash_callback_module_gates_nonempty_data :
  pair_flash_callback_module_gates_nonempty_data := by
  intro ctx target sender amount0Out amount1Out stmts h_compile
  dsimp [TamaUniV2.uniswapV2CallbackModule] at h_compile
  injection h_compile with h_stmts
  exact ⟨_, h_stmts.symm⟩

-- tama: discharges=pair_flash_callback_module_encodes_canonical_call
theorem flash_callback_module_encodes_canonical_call :
  pair_flash_callback_module_encodes_canonical_call := by
  intro ctx target sender amount0Out amount1Out stmts h_compile
  dsimp [TamaUniV2.uniswapV2CallbackModule] at h_compile
  injection h_compile with h_stmts
  let bytesLenExpr := Compiler.Yul.YulExpr.ident "data_length"
  let bytesDataOffset := Compiler.Yul.YulExpr.ident "data_data_offset"
  let bytesDataSlot : Nat := 4 + (3 + 2) * 32
  let paddedBytesLen := Compiler.Yul.YulExpr.call "and" [
    Compiler.Yul.YulExpr.call "add" [bytesLenExpr, Compiler.Yul.YulExpr.lit 31],
    Compiler.Yul.YulExpr.call "not" [Compiler.Yul.YulExpr.lit 31]
  ]
  let totalSize := Compiler.Yul.YulExpr.call "add"
    [Compiler.Yul.YulExpr.lit bytesDataSlot, paddedBytesLen]
  let body :=
    [ Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "mstore" [
        Compiler.Yul.YulExpr.lit 0,
        Compiler.Yul.YulExpr.call "shl"
          [Compiler.Yul.YulExpr.lit 224, Compiler.Yul.YulExpr.hex 0x10d1e85c]])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 4, sender])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 36, amount0Out])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore" [Compiler.Yul.YulExpr.lit 68, amount1Out])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore"
          [Compiler.Yul.YulExpr.lit 100, Compiler.Yul.YulExpr.lit 128])
    , Compiler.Yul.YulStmt.expr
        (Compiler.Yul.YulExpr.call "mstore"
          [Compiler.Yul.YulExpr.lit 132, bytesLenExpr])
    ] ++
    Compiler.ECM.dynamicCopyData ctx
      (Compiler.Yul.YulExpr.lit bytesDataSlot) bytesDataOffset bytesLenExpr ++
    [ Compiler.Yul.YulStmt.let_ "__uv2_cb_success"
        (Compiler.Yul.YulExpr.call "call" [
          Compiler.Yul.YulExpr.call "gas" [],
          target,
          Compiler.Yul.YulExpr.lit 0,
          Compiler.Yul.YulExpr.lit 0,
          totalSize,
          Compiler.Yul.YulExpr.lit 0,
          Compiler.Yul.YulExpr.lit 0
        ])
    , Compiler.Yul.YulStmt.if_
        (Compiler.Yul.YulExpr.call "iszero"
          [Compiler.Yul.YulExpr.ident "__uv2_cb_success"])
        [ Compiler.Yul.YulStmt.let_ "__uv2_cb_rds"
            (Compiler.Yul.YulExpr.call "returndatasize" [])
        , Compiler.Yul.YulStmt.expr
            (Compiler.Yul.YulExpr.call "returndatacopy"
              [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.lit 0,
                Compiler.Yul.YulExpr.ident "__uv2_cb_rds"])
        , Compiler.Yul.YulStmt.expr
            (Compiler.Yul.YulExpr.call "revert"
              [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.ident "__uv2_cb_rds"])
        ]
    ]
  refine ⟨body, totalSize, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [body, totalSize, paddedBytesLen, bytesDataSlot, bytesDataOffset,
      bytesLenExpr] using h_stmts.symm
  · simp [body]
  · simp [body]
  · simp [body]
  · simp [body]
  · simp [body, totalSize]

-- tama: discharges=pair_flash_callback_module_bubbles_callback_failure
theorem flash_callback_module_bubbles_callback_failure :
  pair_flash_callback_module_bubbles_callback_failure := by
  intro ctx target sender amount0Out amount1Out stmts h_compile
  dsimp [TamaUniV2.uniswapV2CallbackModule] at h_compile
  injection h_compile with h_stmts
  refine ⟨_, h_stmts.symm, ?_⟩
  simp

private def pair_mint_first_expected_matches_closed_world_step
    (_toAddr : Address) (s : ContractState) : Prop :=
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

private theorem mint_first_expected_matches_closed_world_step (toAddr : Address) (s : ContractState) :
  pair_mint_first_expected_matches_closed_world_step toAddr s := by
  dsimp [pair_mint_first_expected_matches_closed_world_step]
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
    change (observedBalance0 s).val =
      (s.storage reserve0Slot.slot).val +
        (Verity.EVM.Uint256.sub
          ((Contracts.balanceOf (s.storageAddr 1) s.thisAddress).run s).fst
          (s.storage 3)).val
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
    change (observedBalance1 s).val =
      (s.storage reserve1Slot.slot).val +
        (Verity.EVM.Uint256.sub
          ((Contracts.balanceOf (s.storageAddr 2) s.thisAddress).run s).fst
          (s.storage 4)).val
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

private def pair_mint_first_success_run_matches_closed_world_step
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

private theorem mint_first_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_matches_closed_world_step toAddr s
    ((mint toAddr).run s) := by
  dsimp [pair_mint_first_success_run_matches_closed_world_step]
  intro _h_actual _h_success h_unlocked h_supply_zero h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_product h_root
  exact mint_first_expected_matches_closed_world_step toAddr s
    h_unlocked h_supply_zero h_bound0 h_bound1 h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root

private def pair_mint_first_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  let liquidity := mintFirstLiquidity s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      s.storage totalSupplySlot.slot = 0 →
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

private theorem mint_first_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_matches_closed_world_step_from_run toAddr s
    ((mint toAddr).run s) := by
  dsimp [pair_mint_first_success_run_matches_closed_world_step_from_run]
  intro _h_actual h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_success_exists :
      ∃ liquidity,
        (mint toAddr).run s =
          ContractResult.success liquidity ((mint toAddr).run s).snd := by
    exact ⟨mintFirstLiquidity s, h_success⟩
  have h_unlocked :=
    mint_success_run_implies_lock_open toAddr s
      ((mint toAddr).run s) rfl h_success_exists
  rcases mint_success_run_implies_balances_fit_uint112 toAddr s
      ((mint toAddr).run s) rfl h_success_exists with
    ⟨h_bound0, h_bound1⟩
  exact mint_first_expected_matches_closed_world_step toAddr s
    h_unlocked h_supply_zero h_bound0 h_bound1 h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root

-- tama: discharges=pair_first_mint_success_reaches_expected_pair_state
theorem first_mint_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances) (s : ContractState) :
  pair_first_mint_success_reaches_expected_pair_state
    toAddr preTokens s ((mint toAddr).run s) := by
  intro h_run h_success h_boundary h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  rcases h_boundary with ⟨⟨h_before, h_post⟩, h_expected⟩
  have h_step :=
    mint_first_success_run_matches_closed_world_step_from_run
      toAddr s h_run h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  constructor
  · rw [h_before, h_expected]
    exact h_step
  · exact h_post

-- tama: discharges=pair_first_mint_uses_balance_increase_as_deposit
theorem first_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState) :
  pair_first_mint_uses_balance_increase_as_deposit
    toAddr s ((mint toAddr).run s) := by
  intro _h_run _h_success _h_supply_zero _h_reserve0 _h_reserve1
  constructor <;> rfl

private def pair_mint_subsequent_expected_matches_closed_world_step
    (s : ContractState) (liquidity : Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  0 < (s.storage totalSupplySlot.slot).val →
    s.storage reserve0Slot.slot > 0 →
      s.storage reserve1Slot.slot > 0 →
        observedBalance0 s ≤ maxUint112 →
          observedBalance1 s ≤ maxUint112 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          PairWorldStep
                            (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                            (pairWorldBeforeMintRun s)
                            (pairWorldAfterSubsequentMintRun liquidity s)

private theorem mint_subsequent_expected_matches_closed_world_step
    (s : ContractState) (liquidity : Uint256) :
  pair_mint_subsequent_expected_matches_closed_world_step s liquidity := by
  dsimp [pair_mint_subsequent_expected_matches_closed_world_step]
  intro h_supply_pos h_reserve0_pos h_reserve1_pos h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_supply_ne :
      ¬ (s.storage totalSupplySlot.slot).val = 0 :=
    Nat.ne_of_gt h_supply_pos
  have h_supply_ne_raw : ¬ (s.storage 8).val = 0 := by
    simpa [totalSupplySlot] using h_supply_ne
  unfold PairWorldStep PairWorldMintStep pairWorldBeforeMintRun
    pairWorldAfterSubsequentMintRun
  constructor
  · simpa [mintAmount0] using h_amount0
  constructor
  · simpa [mintAmount1] using h_amount1
  constructor
  · simpa using h_liquidity
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
    change (observedBalance0 s).val =
      (s.storage reserve0Slot.slot).val +
        (Verity.EVM.Uint256.sub
          ((Contracts.balanceOf (s.storageAddr 1) s.thisAddress).run s).fst
          (s.storage 3)).val
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
    change (observedBalance1 s).val =
      (s.storage reserve1Slot.slot).val +
        (Verity.EVM.Uint256.sub
          ((Contracts.balanceOf (s.storageAddr 2) s.thisAddress).run s).fst
          (s.storage 4)).val
    rw [h_sub_raw]
    omega
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound0
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound1
  constructor
  · simp [pairWorldLockedLiquidity, totalSupplySlot, h_supply_ne_raw]
  constructor
  · simp [pairWorldLockedLiquidity, totalSupplySlot, h_supply_ne_raw]
  · exact Or.inr ⟨h_ratio0, h_ratio1⟩

private def pair_mint_subsequent_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      pair_mint_subsequent_expected_matches_closed_world_step s liquidity

private theorem mint_subsequent_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_matches_closed_world_step
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run _h_success
  exact mint_subsequent_expected_matches_closed_world_step s liquidity

private def pair_mint_subsequent_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) (liquidity : Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot > 0 →
          s.storage reserve1Slot.slot > 0 →
            s.storage reserve0Slot.slot ≤ observedBalance0 s →
              s.storage reserve1Slot.slot ≤ observedBalance1 s →
                amount0 > 0 →
                  amount1 > 0 →
                    liquidity > 0 →
                      liquidity.val * (s.storage reserve0Slot.slot).val ≤
                          amount0.val * (s.storage totalSupplySlot.slot).val →
                        liquidity.val * (s.storage reserve1Slot.slot).val ≤
                            amount1.val * (s.storage totalSupplySlot.slot).val →
                          PairWorldStep
                            (PairWorldAction.mint amount0.val amount1.val liquidity.val)
                            (pairWorldBeforeMintRun s)
                            (pairWorldAfterSubsequentMintRun liquidity s)

private theorem mint_subsequent_success_run_matches_closed_world_step_from_run
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_matches_closed_world_step_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  dsimp [pair_mint_subsequent_success_run_matches_closed_world_step_from_run]
  intro _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_success_exists :
      ∃ liquidity',
        (mint toAddr).run s =
          ContractResult.success liquidity' ((mint toAddr).run s).snd := by
    exact ⟨liquidity, h_success⟩
  rcases mint_success_run_implies_balances_fit_uint112 toAddr s
      ((mint toAddr).run s) rfl h_success_exists with
    ⟨h_bound0, h_bound1⟩
  exact mint_subsequent_expected_matches_closed_world_step s liquidity
    h_supply_pos h_reserve0_pos h_reserve1_pos h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1

-- tama: discharges=pair_later_mint_success_reaches_expected_pair_state
theorem later_mint_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances) (s : ContractState)
    (liquidity : Uint256) :
  pair_later_mint_success_reaches_expected_pair_state
    toAddr preTokens s ((mint toAddr).run s) liquidity := by
  intro h_run h_success h_boundary h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  rcases h_boundary with ⟨⟨h_before, h_post⟩, h_expected⟩
  have h_step :=
    mint_subsequent_success_run_matches_closed_world_step_from_run
      toAddr s liquidity h_run h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1
      h_liquidity h_ratio0 h_ratio1
  constructor
  · rw [h_before, h_expected]
    exact h_step
  · exact h_post

-- tama: discharges=pair_later_mint_uses_balance_increase_as_deposit
theorem later_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  pair_later_mint_uses_balance_increase_as_deposit
    toAddr s liquidity ((mint toAddr).run s) := by
  intro _h_run _h_success _h_supply_pos _h_reserve0 _h_reserve1
  constructor <;> rfl

private def pair_burn_expected_matches_closed_world_step
    (s : ContractState) : Prop :=
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  0 < liquidity.val →
    0 < (burnSupply s).val →
      liquidity.val ≤ (burnSupply s).val →
        minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
          amount0 > 0 →
            amount1 > 0 →
              amount0 ≤ observedBalance0 s →
                amount1 ≤ observedBalance1 s →
                  burnBalance0After s ≤ maxUint112 →
                    burnBalance1After s ≤ maxUint112 →
                      amount0.val * (burnSupply s).val ≤
                          liquidity.val * (observedBalance0 s).val →
                        amount1.val * (burnSupply s).val ≤
                            liquidity.val * (observedBalance1 s).val →
                          PairWorldStep
                            (PairWorldAction.burn amount0.val amount1.val liquidity.val)
                            (pairWorldFromConcreteState s)
                            (pairWorldAfterBurnRun s)

private theorem burn_expected_matches_closed_world_step
    (s : ContractState) :
  pair_burn_expected_matches_closed_world_step s := by
  dsimp [pair_burn_expected_matches_closed_world_step]
  intro h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
    h_amount0 h_amount1 h_amount0_le h_amount1_le h_bound0 h_bound1
    h_ratio0 h_ratio1
  have h_supply_ne : ¬ (burnSupply s).val = 0 :=
    Nat.ne_of_gt h_supply_pos
  have h_supply_ne_raw : ¬ (s.storage 8).val = 0 := by
    simpa [burnSupply, totalSupplySlot] using h_supply_ne
  have h_balance0_after :
      (burnBalance0After s).val =
        (observedBalance0 s).val - (burnAmount0 s).val := by
    simpa [burnBalance0After] using
      (Verity.Core.Uint256.sub_eq_of_le
        (a := observedBalance0 s) (b := burnAmount0 s) h_amount0_le)
  have h_balance1_after :
      (burnBalance1After s).val =
        (observedBalance1 s).val - (burnAmount1 s).val := by
    simpa [burnBalance1After] using
      (Verity.Core.Uint256.sub_eq_of_le
        (a := observedBalance1 s) (b := burnAmount1 s) h_amount1_le)
  have h_supply_after :
      (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s)).val =
        (burnSupply s).val - (burnLiquidity s).val := by
    simpa using
      (Verity.Core.Uint256.sub_eq_of_le
        (a := burnSupply s) (b := burnLiquidity s) h_liquidity_le)
  unfold PairWorldStep PairWorldBurnStep pairWorldFromConcreteState
    pairWorldAfterBurnRun pairWorldLockedLiquidity
  constructor
  · simpa using h_amount0
  constructor
  · simpa using h_amount1
  constructor
  · exact h_liquidity_pos
  constructor
  · exact h_supply_pos
  constructor
  · simpa using h_amount0_le
  constructor
  · simpa using h_amount1_le
  constructor
  · exact h_liquidity_le
  constructor
  · simp [h_supply_ne]
    simpa [burnSupply, pairWorldLockedLiquidity, totalSupplySlot, h_supply_ne_raw]
      using h_locked_remaining
  constructor
  · exact h_balance0_after
  constructor
  · exact h_balance1_after
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound0
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound1
  constructor
  · exact h_supply_after
  constructor
  · rfl
  constructor
  · exact h_ratio0
  · exact h_ratio1

private def pair_burn_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  let liquidity := burnLiquidity s
  let amount0 := burnAmount0 s
  let amount1 := burnAmount1 s
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      0 < liquidity.val →
        0 < (burnSupply s).val →
          liquidity.val ≤ (burnSupply s).val →
            minimumLiquidityNat ≤ (burnSupply s).val - liquidity.val →
              amount0 > 0 →
                amount1 > 0 →
                  amount0 ≤ observedBalance0 s →
                    amount1 ≤ observedBalance1 s →
                      burnBalance0After s ≤ maxUint112 →
                        burnBalance1After s ≤ maxUint112 →
                          amount0.val * (burnSupply s).val ≤
                              liquidity.val * (observedBalance0 s).val →
                            amount1.val * (burnSupply s).val ≤
                                liquidity.val * (observedBalance1 s).val →
                              PairWorldStep
                                (PairWorldAction.burn amount0.val amount1.val liquidity.val)
                                (pairWorldFromConcreteState s)
                                (pairWorldAfterBurnRun s)

private theorem burn_success_run_matches_closed_world_step
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_matches_closed_world_step toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success
  exact burn_expected_matches_closed_world_step s

-- tama: discharges=pair_burn_success_reaches_expected_pair_state
theorem burn_success_reaches_expected_pair_state
    (toAddr : Address) (preTokens : PairTokenBalances) (s : ContractState) :
  pair_burn_success_reaches_expected_pair_state
    toAddr preTokens s ((burn toAddr).run s) := by
  intro h_run h_success h_boundary h_liquidity_pos h_supply_pos h_liquidity_le
    h_locked_remaining h_amount0_pos h_amount1_pos h_amount0_le h_amount1_le
    h_bound0 h_bound1 h_ratio0 h_ratio1
  rcases h_boundary with ⟨⟨h_before, h_post⟩, h_expected⟩
  have h_step :=
    burn_success_run_matches_closed_world_step toAddr s h_run h_success
      h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
      h_amount0_pos h_amount1_pos h_amount0_le h_amount1_le h_bound0
      h_bound1 h_ratio0 h_ratio1
  constructor
  · rw [h_before, h_expected]
    exact h_step
  · exact h_post

-- tama: discharges=pair_burn_uses_pair_lp_balance_and_total_supply
theorem burn_uses_pair_lp_balance_and_total_supply
    (toAddr : Address) (s : ContractState) :
  pair_burn_uses_pair_lp_balance_and_total_supply
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success
  constructor <;> rfl

-- tama: discharges=pair_burn_leaves_remaining_token_balances
theorem burn_leaves_remaining_token_balances
    (toAddr : Address) (s : ContractState) :
  pair_burn_leaves_remaining_token_balances
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success h_amount0 h_amount1
  constructor
  · have h_sub :
        (burnBalance0After s).val =
          (observedBalance0 s).val - (burnAmount0 s).val := by
      simpa [burnBalance0After] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance0 s) (b := burnAmount0 s) h_amount0)
    have h_le : (burnAmount0 s).val ≤ (observedBalance0 s).val := by
      simpa using h_amount0
    change (burnBalance0After s).val + (burnAmount0 s).val =
      (observedBalance0 s).val
    rw [h_sub]
    omega
  · have h_sub :
        (burnBalance1After s).val =
          (observedBalance1 s).val - (burnAmount1 s).val := by
      simpa [burnBalance1After] using
        (Verity.Core.Uint256.sub_eq_of_le
          (a := observedBalance1 s) (b := burnAmount1 s) h_amount1)
    have h_le : (burnAmount1 s).val ≤ (observedBalance1 s).val := by
      simpa using h_amount1
    change (burnBalance1After s).val + (burnAmount1 s).val =
      (observedBalance1 s).val
    rw [h_sub]
    omega

private theorem feeAdjustedSwap_implies_raw_k
    (amount0In amount1In : Nat)
    (before after : PairWorldState) :
  after.reserve0 = after.balance0 →
    after.reserve1 = after.balance1 →
      feeAdjustedBalance after.balance0 amount0In *
          feeAdjustedBalance after.balance1 amount1In ≥
        requiredK before.reserve0 before.reserve1 →
        PairWorldK before ≤ PairWorldK after := by
  intro h_reserve0 h_reserve1 h_adjusted_k
  have h_adjusted0_le :
      feeAdjustedBalance after.balance0 amount0In ≤
        after.balance0 * feeDenominatorNat := by
    unfold feeAdjustedBalance
    exact Nat.sub_le _ _
  have h_adjusted1_le :
      feeAdjustedBalance after.balance1 amount1In ≤
        after.balance1 * feeDenominatorNat := by
    unfold feeAdjustedBalance
    exact Nat.sub_le _ _
  have h_adjusted_product_le :
      feeAdjustedBalance after.balance0 amount0In *
          feeAdjustedBalance after.balance1 amount1In ≤
        (after.balance0 * feeDenominatorNat) *
          (after.balance1 * feeDenominatorNat) :=
    Nat.mul_le_mul h_adjusted0_le h_adjusted1_le
  have h_required_le_scaled :=
    Nat.le_trans h_adjusted_k h_adjusted_product_le
  have h_scale_pos : 0 < feeDenominatorNat * feeDenominatorNat := by
    norm_num [feeDenominatorNat]
  have h_scaled :
      PairWorldK before * (feeDenominatorNat * feeDenominatorNat) ≤
        PairWorldK after * (feeDenominatorNat * feeDenominatorNat) := by
    unfold requiredK at h_required_le_scaled
    unfold PairWorldK
    rw [h_reserve0, h_reserve1]
    nlinarith [h_required_le_scaled]
  exact Nat.le_of_mul_le_mul_right h_scaled h_scale_pos

private def pair_swap_expected_matches_closed_world_step
    (amount0Out amount1Out balance0Now balance1Now : Uint256)
    (s : ContractState) : Prop :=
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  (amount0Out > 0 ∨ amount1Out > 0) →
    amount0Out < s.storage reserve0Slot.slot →
      amount1Out < s.storage reserve1Slot.slot →
        (amount0In > 0 ∨ amount1In > 0) →
          balance0Now.val =
              (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
            balance1Now.val =
                (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
              balance0Now ≤ maxUint112 →
                balance1Now ≤ maxUint112 →
                  amount0In.val * feeAdjustmentNat ≤
                      balance0Now.val * feeDenominatorNat →
                    amount1In.val * feeAdjustmentNat ≤
                        balance1Now.val * feeDenominatorNat →
                      feeAdjustedBalance balance0Now.val amount0In.val *
                          feeAdjustedBalance balance1Now.val amount1In.val ≥
                        requiredK
                          (s.storage reserve0Slot.slot).val
                          (s.storage reserve1Slot.slot).val →
                          PairWorldStep
                            (PairWorldAction.swap
                              amount0In.val amount1In.val
                              amount0Out.val amount1Out.val)
                            (pairWorldFromConcreteState s)
                            (pairWorldAfterSwapRun balance0Now balance1Now s)

private theorem swap_expected_matches_closed_world_step
    (amount0Out amount1Out balance0Now balance1Now : Uint256)
    (s : ContractState) :
  pair_swap_expected_matches_closed_world_step
    amount0Out amount1Out balance0Now balance1Now s := by
  dsimp [pair_swap_expected_matches_closed_world_step]
  intro h_output h_liq0 h_liq1 h_input h_balance0 h_balance1 h_bound0 h_bound1
    h_fee0 h_fee1 h_adjusted_k
  unfold PairWorldStep PairWorldSwapStep pairWorldFromConcreteState
    pairWorldAfterSwapRun
  constructor
  · exact h_output
  constructor
  · simpa using h_liq0
  constructor
  · simpa using h_liq1
  constructor
  · have h_liq0_nat : amount0Out.val < (s.storage reserve0Slot.slot).val := by
      simpa using h_liq0
    exact Nat.le_trans (Nat.le_of_lt h_liq0_nat)
      (Nat.le_add_right
        (s.storage reserve0Slot.slot).val
        (swapAmount0In amount0Out balance0Now s).val)
  constructor
  · have h_liq1_nat : amount1Out.val < (s.storage reserve1Slot.slot).val := by
      simpa using h_liq1
    exact Nat.le_trans (Nat.le_of_lt h_liq1_nat)
      (Nat.le_add_right
        (s.storage reserve1Slot.slot).val
        (swapAmount1In amount1Out balance1Now s).val)
  constructor
  · exact h_input
  constructor
  · exact h_balance0
  constructor
  · exact h_balance1
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound0
  constructor
  · simpa [maxUint112Nat, maxUint112, UniswapV2PairBase.maxUint112] using
      h_bound1
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact h_fee0
  constructor
  · exact h_fee1
  · exact h_adjusted_k

private def pair_swap_success_run_matches_closed_world_step
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      pair_swap_expected_matches_closed_world_step
        amount0Out amount1Out balance0Now balance1Now s

private theorem swap_success_run_matches_closed_world_step
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_matches_closed_world_step
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run _h_success
  exact swap_expected_matches_closed_world_step
    amount0Out amount1Out balance0Now balance1Now s

-- tama: discharges=pair_swap_uses_final_balances_to_compute_input
theorem swap_uses_final_balances_to_compute_input
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_uses_final_balances_to_compute_input
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run _h_success
  simp [pair_swap_uses_final_balances_to_compute_input, swapAmount0In,
    swapAmount1In, swapAmountIn]

-- tama: discharges=pair_swap_checks_k_against_final_balances
theorem swap_checks_k_against_final_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_checks_k_against_final_balances
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run _h_success h_k
  simpa [pair_swap_checks_k_against_final_balances,
    pairWorldAfterSwapRun, pairWorldFromConcreteState] using h_k

private def pair_swap_success_run_matches_closed_world_step_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          (amount0In > 0 ∨ amount1In > 0) →
            balance0Now.val =
                (s.storage reserve0Slot.slot).val + amount0In.val - amount0Out.val →
              balance1Now.val =
                  (s.storage reserve1Slot.slot).val + amount1In.val - amount1Out.val →
                balance0Now ≤ maxUint112 →
                  balance1Now ≤ maxUint112 →
                    amount0In.val * feeAdjustmentNat ≤
                        balance0Now.val * feeDenominatorNat →
                      amount1In.val * feeAdjustmentNat ≤
                          balance1Now.val * feeDenominatorNat →
                        feeAdjustedBalance balance0Now.val amount0In.val *
                            feeAdjustedBalance balance1Now.val amount1In.val ≥
                          requiredK
                            (s.storage reserve0Slot.slot).val
                            (s.storage reserve1Slot.slot).val →
                            PairWorldStep
                            (PairWorldAction.swap
                              amount0In.val amount1In.val
                              amount0Out.val amount1Out.val)
                            (pairWorldFromConcreteState s)
                            (pairWorldAfterSwapRun balance0Now balance1Now s)

private theorem swap_success_run_matches_closed_world_step_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_matches_closed_world_step_from_run
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  have h_nonzero :=
    swap_success_run_implies_nonzero_output
      amount0Out amount1Out toAddr data s
      ((swap amount0Out amount1Out toAddr data).run s) rfl h_success
  have h_output : amount0Out > 0 ∨ amount1Out > 0 := by
    rcases h_nonzero with h_amount0 | h_amount1
    · exact Or.inl (uint256_pos_of_ne_zero h_amount0)
    · exact Or.inr (uint256_pos_of_ne_zero h_amount1)
  exact swap_expected_matches_closed_world_step
    amount0Out amount1Out balance0Now balance1Now s h_output
    h_liq0 h_liq1 h_input h_balance0 h_balance1 h_bound0 h_bound1
    h_fee0 h_fee1 h_adjusted_k

-- tama: discharges=pair_swap_success_reaches_expected_pair_state
theorem swap_success_reaches_expected_pair_state
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (preTokens : PairTokenBalances)
    (s : ContractState) :
  pair_swap_success_reaches_expected_pair_state
    amount0Out amount1Out toAddr data balance0Now balance1Now preTokens s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_run h_success h_boundary h_liq0 h_liq1 h_input h_balance0
    h_balance1 h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  rcases h_boundary with ⟨⟨h_before, h_post⟩, h_expected⟩
  have h_step :=
    swap_success_run_matches_closed_world_step_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  constructor
  · rw [h_before, h_expected]
    exact h_step
  · exact h_post

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
    rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      h_supply_pos, _h_amount0_le, _h_amount1_le, h_liquidity_le,
      h_locked_remaining, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
      h_bound0, h_bound1, h_supply_eq, h_locked_eq, _h_ratio0, _h_ratio1⟩
    refine ⟨?_, ?_, h_bound0, h_bound1, ?_⟩
    · rw [h_reserve0]
    · rw [h_reserve1]
    · rcases h_supply with h_empty | h_nonzero
      · exact False.elim (Nat.ne_of_gt h_supply_pos h_empty.1)
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

private theorem pairWorldPath_preserves_reachability
    {before after : PairWorldState} :
  PairWorldReachable before →
    PairWorldPath before after →
      PairWorldReachable after := by
  intro h_reachable h_path
  induction h_path with
  | refl =>
      exact h_reachable
  | step action h_prefix h_step ih =>
      exact PairWorldReachable.step action ih h_step

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

private theorem pairWorldPath_of_noMintBurn
    {before after : PairWorldState} :
  PairWorldPathNoMintBurn before after →
    PairWorldPath before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWorldPath.refl before
  | step action h_prefix h_step _h_not_mint _h_not_burn ih =>
      exact PairWorldPath.step action ih h_step

private theorem pairWorldPath_of_noDonation
    {before after : PairWorldState} :
  PairWorldPathNoDonation before after →
    PairWorldPath before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWorldPath.refl before
  | step action h_prefix h_step _h_not_donation ih =>
      exact PairWorldPath.step action ih h_step

private theorem pairWorldNoBurnPath_of_noMintBurn
    {before after : PairWorldState} :
  PairWorldPathNoMintBurn before after →
    PairWorldPathNoBurn before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWorldPathNoBurn.refl before
  | step action h_prefix h_step _h_not_mint h_not_burn ih =>
      exact PairWorldPathNoBurn.step action ih h_step h_not_burn

private theorem pairWorldNoMintBurnPath_preserves_supply
    {before after : PairWorldState} :
  PairWorldPathNoMintBurn before after →
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity := by
  intro h_path
  induction h_path with
  | refl =>
      exact ⟨rfl, rfl⟩
  | step action h_prefix h_step h_not_mint h_not_burn ih =>
      cases action with
      | approve ownerAddr spender amount =>
          simp [PairWorldStep] at h_step
          rw [h_step]
          exact ih
      | transfer fromAddr toAddr amount =>
          simp [PairWorldStep] at h_step
          rw [h_step]
          exact ih
      | transferFrom spender fromAddr toAddr amount =>
          simp [PairWorldStep] at h_step
          rw [h_step]
          exact ih
      | donate amount0 amount1 =>
          simp [PairWorldStep] at h_step
          rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, h_supply, h_locked⟩
          exact ⟨h_supply.trans ih.1, h_locked.trans ih.2⟩
      | mint amount0 amount1 liquidity =>
          exact False.elim (h_not_mint amount0 amount1 liquidity rfl)
      | burn amount0 amount1 liquidity =>
          exact False.elim (h_not_burn amount0 amount1 liquidity rfl)
      | swap amount0In amount1In amount0Out amount1Out =>
          simp [PairWorldStep, PairWorldSwapStep] at h_step
          rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
            _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, _h_bound0, _h_bound1, h_supply, h_locked, _h_fee0,
            _h_fee1, _h_adjusted_k⟩
          exact ⟨h_supply.trans ih.1, h_locked.trans ih.2⟩
      | skim =>
          simp [PairWorldStep, PairWorldSkimStep] at h_step
          rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, h_supply, h_locked⟩
          exact ⟨h_supply.trans ih.1, h_locked.trans ih.2⟩
      | sync =>
          simp [PairWorldStep, PairWorldSyncStep] at h_step
          rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
            _h_reserve0, _h_reserve1, h_supply, h_locked⟩
          exact ⟨h_supply.trans ih.1, h_locked.trans ih.2⟩

private theorem pairWorldNonBurnStep_never_decreases_supply
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      before.totalSupply ≤ after.totalSupply := by
  intro h_step h_not_burn
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
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_before_balance0, _h_before_balance1, _h_after_balance0,
        _h_after_balance1, _h_after_reserve0, _h_after_reserve1, _h_bound0,
        _h_bound1, h_supply, _h_locked, _h_ratio⟩
      by_cases h_zero : before.totalSupply = 0
      · rw [h_supply, if_pos h_zero, h_zero]
        exact Nat.zero_le _
      · rw [h_supply, if_neg h_zero]
        exact Nat.le_add_right before.totalSupply liquidity
  | burn amount0 amount1 liquidity =>
      exact False.elim (h_not_burn amount0 amount1 liquidity rfl)
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
        _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0,
        _h_fee1, _h_adjusted_k⟩
      rw [h_supply]
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
      rw [h_supply]

private theorem pairWorldNoBurnPath_never_decreases_supply
    {before after : PairWorldState} :
  PairWorldPathNoBurn before after →
    before.totalSupply ≤ after.totalSupply := by
  intro h_path
  induction h_path with
  | refl =>
      rfl
  | step action h_prefix h_step h_not_burn ih =>
      exact Nat.le_trans ih
        (pairWorldNonBurnStep_never_decreases_supply h_step h_not_burn)

private theorem pairWorldNonMintStep_never_increases_supply
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
      after.totalSupply ≤ before.totalSupply := by
  intro h_step h_not_mint
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
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
  | mint amount0 amount1 liquidity =>
      exact False.elim (h_not_mint amount0 amount1 liquidity rfl)
  | burn amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liquidity_le,
        _h_locked_remaining, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_ratio0,
        _h_ratio1⟩
      rw [h_supply]
      exact Nat.sub_le before.totalSupply liquidity
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
        _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0,
        _h_fee1, _h_adjusted_k⟩
      rw [h_supply]
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
      rw [h_supply]

private theorem pairWorldNoMintPath_never_increases_supply
    {before after : PairWorldState} :
  PairWorldPathNoMint before after →
    after.totalSupply ≤ before.totalSupply := by
  intro h_path
  induction h_path with
  | refl =>
      rfl
  | step action h_prefix h_step h_not_mint ih =>
      exact Nat.le_trans
        (pairWorldNonMintStep_never_increases_supply h_step h_not_mint)
        ih

private theorem pairWorldStep_locked_liquidity_never_decreases
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldStep action before after →
      before.lockedLiquidity ≤ after.lockedLiquidity := by
  intro h_good h_step
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
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        _h_supply, h_locked⟩
      rw [h_locked]
  | mint amount0 amount1 liquidity =>
      rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1,
        h_supply_good⟩
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_before_balance0, _h_before_balance1, _h_after_balance0,
        _h_after_balance1, _h_after_reserve0, _h_after_reserve1, _h_bound0,
        _h_bound1, _h_supply, h_locked, _h_ratio⟩
      by_cases h_zero : before.totalSupply = 0
      · have h_locked_before : before.lockedLiquidity = 0 := by
          rcases h_supply_good with h_empty | h_nonempty
          · exact h_empty.2
          · exact False.elim ((Nat.ne_of_gt h_nonempty.1) h_zero)
        rw [h_locked_before, h_locked, if_pos h_zero]
        exact Nat.zero_le _
      · rw [h_locked, if_neg h_zero]
  | burn amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liquidity_le,
        _h_locked_remaining, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, _h_supply, h_locked, _h_ratio0,
        _h_ratio1⟩
      rw [h_locked]
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
        _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
        _h_reserve1, _h_bound0, _h_bound1, _h_supply, h_locked, _h_fee0,
        _h_fee1, _h_adjusted_k⟩
      rw [h_locked]
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        _h_supply, h_locked⟩
      rw [h_locked]
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, _h_supply, h_locked⟩
      rw [h_locked]

private theorem pairWorldPath_locked_liquidity_never_decreases
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPath before after →
      before.lockedLiquidity ≤ after.lockedLiquidity := by
  intro h_good h_path
  revert h_good
  induction h_path with
  | refl =>
      intro _h_good
      rfl
  | step action h_prefix h_step ih =>
      intro h_good
      have h_good_before := pairWorldPath_preserves_good h_good h_prefix
      exact Nat.le_trans
        (ih h_good)
        (pairWorldStep_locked_liquidity_never_decreases h_good_before h_step)

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
        _h_input, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1,
        h_adjusted_k⟩
      exact feeAdjustedSwap_implies_raw_k
        amount0In amount1In before after h_reserve0 h_reserve1 h_adjusted_k
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

private theorem pairWorldStep_positive_supply_preserved
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep action before after →
        0 < after.totalSupply := by
  intro h_good h_positive h_step
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact h_positive
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact h_positive
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact h_positive
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
      exact h_positive
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity, _h_before_balance0,
        _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
        _h_after_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_ratio⟩
      by_cases h_zero : before.totalSupply = 0
      · exact False.elim (Nat.ne_of_gt h_positive h_zero)
      · rw [h_supply]
        simp [h_zero]
        omega
  | burn amount0 amount1 liquidity =>
      rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply_good⟩
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
        _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, h_locked_remaining,
        _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
        h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
      rcases h_supply_good with h_empty | h_nonempty
      · exact False.elim (Nat.ne_of_gt h_positive h_empty.1)
      · rcases h_nonempty with ⟨_h_supply_pos, h_locked, _h_min⟩
        rw [h_supply]
        rw [h_locked] at h_locked_remaining
        simp [minimumLiquidityNat] at h_locked_remaining
        omega
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
        _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0, _h_fee1,
        _h_adjusted_k⟩
      rw [h_supply]
      exact h_positive
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
        h_supply, _h_locked⟩
      rw [h_supply]
      exact h_positive
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
      rw [h_supply]
      exact h_positive

private theorem pairWorldPath_positive_supply_preserved
    {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        0 < after.totalSupply := by
  intro h_good h_positive h_path
  induction h_path with
  | refl =>
      exact h_positive
  | step action h_prefix h_step ih =>
      have h_good_before := pairWorldPath_preserves_good h_good h_prefix
      exact pairWorldStep_positive_supply_preserved h_good_before ih h_step

private theorem pairWorldStep_k_per_supply_never_decreases
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep action before after →
        PairWorldKPerSupplyNondecreasing before after := by
  intro h_good h_positive h_step
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      unfold PairWorldKPerSupplyNondecreasing
      rfl
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      unfold PairWorldKPerSupplyNondecreasing
      rfl
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      unfold PairWorldKPerSupplyNondecreasing
      rfl
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        h_supply, _h_locked⟩
      unfold PairWorldKPerSupplyNondecreasing PairWorldK
      rw [h_reserve0, h_reserve1, h_supply]
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, h_before_balance0,
        h_before_balance1, h_after_balance0, h_after_balance1, h_after_reserve0,
        h_after_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, h_ratio⟩
      by_cases h_zero : before.totalSupply = 0
      · exact False.elim (Nat.ne_of_gt h_positive h_zero)
      · rcases h_ratio with h_first | h_ratio
        · exact False.elim (h_zero h_first)
        · have h_supply' :
              after.totalSupply = before.totalSupply + liquidity := by
            simpa [h_zero] using h_supply
          have h_reserve0' :
              after.reserve0 = before.reserve0 + amount0 := by
            rw [h_after_reserve0, h_before_balance0]
          have h_reserve1' :
              after.reserve1 = before.reserve1 + amount1 := by
            rw [h_after_reserve1, h_before_balance1]
          have h0 :
              before.reserve0 * after.totalSupply ≤
                after.reserve0 * before.totalSupply := by
            rw [h_supply', h_reserve0']
            nlinarith [h_ratio.1]
          have h1 :
              before.reserve1 * after.totalSupply ≤
                after.reserve1 * before.totalSupply := by
            rw [h_supply', h_reserve1']
            nlinarith [h_ratio.2]
          have h_mul := Nat.mul_le_mul h0 h1
          unfold PairWorldKPerSupplyNondecreasing PairWorldK
          nlinarith [h_mul]
  | burn amount0 amount1 liquidity =>
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
        _h_supply_pos, h_amount0, h_amount1, h_liquidity, _h_locked_remaining,
        h_balance0, h_balance1, h_reserve0, h_reserve1, _h_bound0, _h_bound1,
        h_supply, _h_locked, h_ratio0, h_ratio1⟩
      have h_after0 :
          after.reserve0 = before.balance0 - amount0 := by
        rw [h_reserve0, h_balance0]
      have h_after1 :
          after.reserve1 = before.balance1 - amount1 := by
        rw [h_reserve1, h_balance1]
      have h0_balance :
          before.balance0 * (before.totalSupply - liquidity) ≤
            (before.balance0 - amount0) * before.totalSupply := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.sub_le_sub_left h_ratio0 (before.balance0 * before.totalSupply)
      have h1_balance :
          before.balance1 * (before.totalSupply - liquidity) ≤
            (before.balance1 - amount1) * before.totalSupply := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.sub_le_sub_left h_ratio1 (before.balance1 * before.totalSupply)
      have h0 :
          before.reserve0 * after.totalSupply ≤
            after.reserve0 * before.totalSupply := by
        rw [h_supply, h_after0]
        exact Nat.le_trans (Nat.mul_le_mul_right _ h_back0) h0_balance
      have h1 :
          before.reserve1 * after.totalSupply ≤
            after.reserve1 * before.totalSupply := by
        rw [h_supply, h_after1]
        exact Nat.le_trans (Nat.mul_le_mul_right _ h_back1) h1_balance
      have h_mul := Nat.mul_le_mul h0 h1
      unfold PairWorldKPerSupplyNondecreasing PairWorldK
      nlinarith [h_mul]
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
        _h_input, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, h_supply, _h_locked, _h_fee0, _h_fee1,
        h_adjusted_k⟩
      have h_raw_k :
          PairWorldK before ≤ PairWorldK after :=
        feeAdjustedSwap_implies_raw_k
          amount0In amount1In before after h_reserve0 h_reserve1 h_adjusted_k
      unfold PairWorldKPerSupplyNondecreasing
      rw [h_supply]
      exact Nat.mul_le_mul_right before.totalSupply
        (Nat.mul_le_mul_right before.totalSupply h_raw_k)
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        h_supply, _h_locked⟩
      unfold PairWorldKPerSupplyNondecreasing PairWorldK
      rw [h_reserve0, h_reserve1, h_supply]
  | sync =>
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1,
        _h_supply_good⟩
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        h_reserve0, h_reserve1, h_supply, _h_locked⟩
      have h_k : PairWorldK before ≤ PairWorldK after := by
        unfold PairWorldK
        rw [h_reserve0, h_reserve1]
        exact Nat.mul_le_mul h_back0 h_back1
      unfold PairWorldKPerSupplyNondecreasing
      rw [h_supply]
      exact Nat.mul_le_mul_right before.totalSupply
        (Nat.mul_le_mul_right before.totalSupply h_k)

private theorem pairWorldPath_k_per_supply_never_decreases
    {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        PairWorldKPerSupplyNondecreasing before after := by
  intro h_good h_positive h_path
  revert h_good h_positive
  induction h_path with
  | refl =>
      intro h_good h_positive
      unfold PairWorldKPerSupplyNondecreasing
      rfl
  | step action h_prefix h_step ih =>
      rename_i mid last
      intro h_good h_positive
      have h_good_mid := pairWorldPath_preserves_good h_good h_prefix
      have h_positive_mid :=
        pairWorldPath_positive_supply_preserved h_good h_positive h_prefix
      have h_prefix_scaled := ih h_good h_positive
      have h_step_scaled :=
        pairWorldStep_k_per_supply_never_decreases
          h_good_mid h_positive_mid h_step
      have h_mid_sq_pos := Nat.mul_pos h_positive_mid h_positive_mid
      have h_prefix_mul :=
        Nat.mul_le_mul_right (last.totalSupply * last.totalSupply) h_prefix_scaled
      have h_step_mul :=
        Nat.mul_le_mul_right (before.totalSupply * before.totalSupply) h_step_scaled
      unfold PairWorldKPerSupplyNondecreasing at *
      nlinarith [h_prefix_mul, h_step_mul, h_mid_sq_pos]

private theorem pairWorldSameSupplyPath_never_decreases_k
    {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldK before ≤ PairWorldK after := by
  intro h_good h_positive h_path h_supply
  have h_scaled :=
    pairWorldPath_k_per_supply_never_decreases h_good h_positive h_path
  unfold PairWorldKPerSupplyNondecreasing at h_scaled
  rw [← h_supply] at h_scaled
  have h_scaled' :
      PairWorldK before * (before.totalSupply * before.totalSupply) ≤
        PairWorldK after * (before.totalSupply * before.totalSupply) := by
    simpa [Nat.mul_assoc] using h_scaled
  exact Nat.le_of_mul_le_mul_right h_scaled'
    (Nat.mul_pos h_positive h_positive)

private def pair_closed_world_step_preserves_good
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      PairWorldGood after

private theorem closed_world_step_preserves_good
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_step_preserves_good action before after := by
  exact pairWorldStep_preserves_good

-- tama: discharges=pair_closed_world_path_preserves_good
theorem closed_world_path_preserves_good
    (before after : PairWorldState) :
  pair_closed_world_path_preserves_good before after := by
  exact pairWorldPath_preserves_good


-- tama: discharges=pair_closed_world_reachable_path_good
theorem closed_world_reachable_path_good
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_good before after := by
  intro h_reachable h_path
  exact pairWorldPath_preserves_good
    (pairWorldReachable_good before h_reachable)
    h_path

-- tama: discharges=pair_closed_world_path_preserves_reachability
theorem closed_world_path_preserves_reachability
    (before after : PairWorldState) :
  pair_closed_world_path_preserves_reachability before after := by
  exact pairWorldPath_preserves_reachability







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



-- tama: discharges=pair_closed_world_reachable_path_reserves_backed
theorem closed_world_reachable_path_reserves_backed
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_reserves_backed before after := by
  intro h_reachable h_path
  rcases pairWorldPath_preserves_good
      (pairWorldReachable_good before h_reachable) h_path with
    ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  exact ⟨h_back0, h_back1⟩

-- tama: discharges=pair_closed_world_reachable_path_reserves_fit_uint112
theorem closed_world_reachable_path_reserves_fit_uint112
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_reserves_fit_uint112 before after := by
  intro h_reachable h_path
  rcases pairWorldPath_preserves_good
      (pairWorldReachable_good before h_reachable) h_path with
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

-- tama: discharges=pair_closed_world_reachable_path_minimum_liquidity_lock
theorem closed_world_reachable_path_minimum_liquidity_lock
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_minimum_liquidity_lock before after := by
  intro h_reachable h_path
  exact (pairWorldPath_preserves_good
    (pairWorldReachable_good before h_reachable) h_path).2.2.2.2


/-- The finite-history version of permanent locked liquidity. Starting from a
good pool model, no successful sequence can unwind the locked floor. -/
private def pair_closed_world_path_locked_liquidity_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPath before after →
      before.lockedLiquidity ≤ after.lockedLiquidity

private theorem closed_world_path_locked_liquidity_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_path_locked_liquidity_never_decreases before after := by
  exact pairWorldPath_locked_liquidity_never_decreases

-- tama: discharges=pair_closed_world_reachable_path_locked_liquidity_never_decreases
theorem closed_world_reachable_path_locked_liquidity_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_locked_liquidity_never_decreases before after := by
  intro h_reachable h_path
  exact pairWorldPath_locked_liquidity_never_decreases
    (pairWorldReachable_good before h_reachable) h_path



/-- Finite-history reserve isolation. A history made only of LP bookkeeping,
direct donations, and skim may change LP ownership or token balances, but it
never changes the cached reserves. This is the path-level form of the
reserve-change classifier above, and it is the invariant a router-facing reader
can cite when reasoning that cached price state is stable unless a reserve
update action actually occurs. -/
private def pair_closed_world_no_reserve_update_path_preserves_reserves
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoReserveUpdate before after →
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1

private theorem closed_world_no_reserve_update_path_preserves_reserves
    (start finish : PairWorldState) :
  pair_closed_world_no_reserve_update_path_preserves_reserves start finish := by
  intro h_path
  induction h_path with
  | refl =>
      exact ⟨rfl, rfl⟩
  | @step mid next action h_prefix h_step
      h_not_mint h_not_burn h_not_swap h_not_sync ih =>
      have h_step_reserves :
          next.reserve0 = mid.reserve0 ∧
          next.reserve1 = mid.reserve1 := by
        cases action with
        | approve ownerAddr spender amount =>
            simp [PairWorldStep] at h_step
            subst next
            exact ⟨rfl, rfl⟩
        | transfer fromAddr toAddr amount =>
            simp [PairWorldStep] at h_step
            subst next
            exact ⟨rfl, rfl⟩
        | transferFrom spender fromAddr toAddr amount =>
            simp [PairWorldStep] at h_step
            subst next
            exact ⟨rfl, rfl⟩
        | donate amount0 amount1 =>
            simp [PairWorldStep] at h_step
            rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0,
              h_reserve1, _h_supply, _h_locked⟩
            exact ⟨h_reserve0, h_reserve1⟩
        | mint amount0 amount1 liquidity =>
            exact False.elim (h_not_mint amount0 amount1 liquidity rfl)
        | burn amount0 amount1 liquidity =>
            exact False.elim (h_not_burn amount0 amount1 liquidity rfl)
        | swap amount0In amount1In amount0Out amount1Out =>
            exact False.elim
              (h_not_swap amount0In amount1In amount0Out amount1Out rfl)
        | skim =>
            simp [PairWorldStep, PairWorldSkimStep] at h_step
            rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0,
              h_reserve1, _h_supply, _h_locked⟩
            exact ⟨h_reserve0, h_reserve1⟩
        | sync =>
            exact False.elim (h_not_sync rfl)
      exact ⟨by rw [h_step_reserves.1, ih.1],
        by rw [h_step_reserves.2, ih.2]⟩

/-- Economic corollary of finite-history reserve isolation. If no mint, burn,
swap, or sync occurs, the cached reserve product and reserve-denominated spot
value are unchanged. This deliberately talks about cached reserves rather than
actual token balances: direct donations and `skim` may change surplus, but they
do not change the reserve price state. -/
private def pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoReserveUpdate before after →
    PairWorldK after = PairWorldK before ∧
    PairWorldSpotValueNum before after =
      PairWorldSpotValueNum before before

private theorem closed_world_no_reserve_update_path_preserves_k_and_spot_value
    (before after : PairWorldState) :
  pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value
    before after := by
  intro h_path
  have h_reserves :=
    closed_world_no_reserve_update_path_preserves_reserves before after h_path
  constructor
  · unfold PairWorldK
    rw [h_reserves.1, h_reserves.2]
  · unfold PairWorldSpotValueNum
    rw [h_reserves.1, h_reserves.2]

-- tama: discharges=pair_closed_world_reachable_reserve_change_requires_reserve_update
theorem closed_world_reachable_reserve_change_requires_reserve_update
    (before after : PairWorldState) :
  pair_closed_world_reachable_reserve_change_requires_reserve_update
    before after := by
  intro _h_reachable h_changed h_no_reserve_update
  have h_preserve :=
    closed_world_no_reserve_update_path_preserves_reserves
      before after h_no_reserve_update
  rcases h_changed with h_reserve0_changed | h_reserve1_changed
  · exact h_reserve0_changed h_preserve.1
  · exact h_reserve1_changed h_preserve.2

/-- The one-step LP-supply firewall. A successful modeled action that is not
mint and not burn cannot change total LP supply or the permanently locked
liquidity amount. This is the local fact that the finite-history theorem below
iterates. -/
private def pair_closed_world_non_liquidity_step_preserves_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      after.totalSupply = before.totalSupply ∧
      after.lockedLiquidity = before.lockedLiquidity

private theorem closed_world_non_liquidity_step_preserves_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_liquidity_step_preserves_supply action before after := by
  intro h_step h_not_mint h_not_burn
  exact pairWorldNoMintBurnPath_preserves_supply
    (PairWorldPathNoMintBurn.step action
      (PairWorldPathNoMintBurn.refl before)
      h_step h_not_mint h_not_burn)

/-- The finite-history version of the LP supply firewall. If a successful
modeled path contains no mint and no burn, then it cannot change total LP supply
or the permanently locked liquidity amount. -/
private def pair_closed_world_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoMintBurn before after →
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

private theorem closed_world_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) :
  pair_closed_world_no_mint_burn_path_preserves_supply before after := by
  exact pairWorldNoMintBurnPath_preserves_supply


/-- The directional LP-supply firewall. A single successful modeled action that
is not burn cannot destroy LP supply. Mint may create new shares and ordinary
pool operations may leave supply unchanged, but redemption is the only direction
that can move supply downward. -/
private def pair_closed_world_non_burn_step_never_decreases_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      before.totalSupply ≤ after.totalSupply

private theorem closed_world_non_burn_step_never_decreases_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_burn_step_never_decreases_supply action before after := by
  exact pairWorldNonBurnStep_never_decreases_supply

/-- The finite-history version of the same supply direction fact. Along any
successful modeled history with no burn step, total LP supply cannot decrease.
This is the trace-level statement that "LP redemption requires burn." -/
private def pair_closed_world_no_burn_path_never_decreases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoBurn before after →
    before.totalSupply ≤ after.totalSupply

private theorem closed_world_no_burn_path_never_decreases_supply
    (before after : PairWorldState) :
  pair_closed_world_no_burn_path_never_decreases_supply before after := by
  exact pairWorldNoBurnPath_never_decreases_supply


/-- The other direction of LP-supply isolation. A single successful modeled
action that is not mint cannot create LP supply. Burn may redeem shares and
ordinary pool operations may leave supply unchanged, but issuance is isolated to
mint. -/
private def pair_closed_world_non_mint_step_never_increases_supply
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldStep action before after →
    (∀ amount0 amount1 liquidity,
      action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
      after.totalSupply ≤ before.totalSupply

private theorem closed_world_non_mint_step_never_increases_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_mint_step_never_increases_supply action before after := by
  exact pairWorldNonMintStep_never_increases_supply

/-- The finite-history version of LP issuance isolation. Along any successful
modeled history with no mint step, total LP supply cannot increase. This is the
trace-level statement that new LP claims require mint. -/
private def pair_closed_world_no_mint_path_never_increases_supply
    (before after : PairWorldState) : Prop :=
  PairWorldPathNoMint before after →
    after.totalSupply ≤ before.totalSupply

private theorem closed_world_no_mint_path_never_increases_supply
    (before after : PairWorldState) :
  pair_closed_world_no_mint_path_never_increases_supply before after := by
  exact pairWorldNoMintPath_never_increases_supply




-- tama: discharges=pair_closed_world_reachable_supply_change_requires_mint_or_burn
theorem closed_world_reachable_supply_change_requires_mint_or_burn
    (before after : PairWorldState) :
  pair_closed_world_reachable_supply_change_requires_mint_or_burn before after := by
  intro h_reachable h_changed h_no_mint_burn
  have h_preserve :=
    closed_world_no_mint_burn_path_preserves_supply
      before after h_no_mint_burn
  exact h_changed h_preserve.1

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

private theorem pairWorldShareBookkeepingPath_preserves_pool_state
    {before after : PairWorldState} :
  PairWorldPathShareBookkeeping before after →
    after.balance0 = before.balance0 ∧
    after.balance1 = before.balance1 ∧
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1 ∧
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity := by
  intro h_path
  induction h_path with
  | refl =>
      simp
  | approve ownerAddr spender amount h_prefix h_step ih =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ih
  | transfer fromAddr toAddr amount h_prefix h_step ih =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ih
  | transferFrom spender fromAddr toAddr amount h_prefix h_step ih =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ih

/-- LP token bookkeeping is only bookkeeping. Across any finite sequence made
solely of approvals, direct LP transfers, and delegated LP transfers, the AMM
state is unchanged: token balances, cached reserves, total LP supply, and the
permanently locked liquidity amount all end exactly where they started. This is
the trace-level version of the ERC20-share claim above, and it is what lets the
economic sections ignore pure share movements as price- or reserve-changing
actions. -/
private def pair_closed_world_share_bookkeeping_path_preserves_pool_state
    (before after : PairWorldState) : Prop :=
  PairWorldPathShareBookkeeping before after →
    after.balance0 = before.balance0 ∧
    after.balance1 = before.balance1 ∧
    after.reserve0 = before.reserve0 ∧
    after.reserve1 = before.reserve1 ∧
    after.totalSupply = before.totalSupply ∧
    after.lockedLiquidity = before.lockedLiquidity

private theorem closed_world_share_bookkeeping_path_preserves_pool_state
    (before after : PairWorldState) :
  pair_closed_world_share_bookkeeping_path_preserves_pool_state before after := by
  exact pairWorldShareBookkeepingPath_preserves_pool_state

/-- Economic corollary of the share-bookkeeping invariant. If a history only
moves LP approvals or LP balances between accounts, then it cannot change the
pool's cached K, reserve-denominated spot value, or actual-token-balance spot
value. Pure ownership bookkeeping is therefore not an AMM profit path. -/
private def pair_closed_world_share_bookkeeping_path_preserves_k_and_value
    (before after : PairWorldState) : Prop :=
  PairWorldPathShareBookkeeping before after →
    PairWorldK after = PairWorldK before ∧
    PairWorldSpotValueNum before after =
      PairWorldSpotValueNum before before ∧
    PairWorldBalanceSpotValueNum before after =
      PairWorldBalanceSpotValueNum before before

private theorem closed_world_share_bookkeeping_path_preserves_k_and_value
    (before after : PairWorldState) :
  pair_closed_world_share_bookkeeping_path_preserves_k_and_value before after := by
  intro h_path
  rcases pairWorldShareBookkeepingPath_preserves_pool_state h_path with
    ⟨h_balance0, h_balance1, h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  simp [pair_closed_world_share_bookkeeping_path_preserves_k_and_value,
    PairWorldK, PairWorldSpotValueNum, PairWorldBalanceSpotValueNum,
    h_balance0, h_balance1, h_reserve0, h_reserve1]

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

-- tama: discharges=pair_closed_world_first_mint_keeps_locked_share
theorem closed_world_first_mint_keeps_locked_share
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_first_mint_keeps_locked_share
    amount0 amount1 liquidity before after := by
  intro h_step h_first
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, h_supply, h_locked, _h_ratio⟩
  simp [h_first] at h_supply h_locked
  constructor
  · rw [h_locked, h_supply]
    unfold minimumLiquidityNat
    omega
  · rw [h_supply]
    unfold minimumLiquidityNat
    omega

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

-- tama: discharges=pair_closed_world_mint_strictly_increases_supply
theorem closed_world_mint_strictly_increases_supply
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_strictly_increases_supply
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, h_liquidity, _h_before_balance0,
    _h_before_balance1, _h_after_balance0, _h_after_balance1, _h_after_reserve0,
    _h_after_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked, _h_ratio⟩
  by_cases h_first : before.totalSupply = 0
  · simp [h_first] at h_supply
    rw [h_supply, h_first]
    omega
  · simp [h_first] at h_supply
    rw [h_supply]
    omega

-- tama: discharges=pair_closed_world_mint_adds_exact_deposits_to_reserves
theorem closed_world_mint_adds_exact_deposits_to_reserves
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_adds_exact_deposits_to_reserves
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, h_before_balance0,
    h_before_balance1, _h_after_balance0, _h_after_balance1, h_after_reserve0,
    h_after_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
  constructor
  · rw [h_after_reserve0, h_before_balance0]
  · rw [h_after_reserve1, h_before_balance1]




-- tama: discharges=pair_first_mint_success_uses_canonical_liquidity_formula
theorem first_mint_success_uses_canonical_liquidity_formula
    (toAddr : Address) (s : ContractState) :
  pair_first_mint_success_uses_canonical_liquidity_formula
    toAddr s ((mint toAddr).run s) := by
  intro _h_run _h_success _h_supply_zero _h_reserve0 _h_reserve1
    _h_amount0 _h_amount1 _h_product h_root
  have h_root_le : minimumLiquidity.val ≤ (mintFirstRoot s).val :=
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
  constructor
  · rw [h_liquidity_eq, h_min_val]
    have h_root_le_nat : minimumLiquidityNat ≤ (mintFirstRoot s).val := by
      rw [← h_min_val]
      exact h_root_le
    omega
  constructor
  · simp [pairWorldAfterFirstMintRun]
  · rw [h_liquidity_eq, h_min_val]
    simp [pairWorldAfterFirstMintRun]
    have h_root_le_nat : minimumLiquidityNat ≤ (mintFirstRoot s).val := by
      rw [← h_min_val]
      exact h_root_le
    omega



-- tama: discharges=pair_closed_world_burn_reduces_supply_by_liquidity
theorem closed_world_burn_reduces_supply_by_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_reduces_supply_by_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  exact h_supply

-- tama: discharges=pair_closed_world_burn_removes_exact_redemptions_from_balances
theorem closed_world_burn_removes_exact_redemptions_from_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_removes_exact_redemptions_from_balances
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, h_amount0_le, h_amount1_le, _h_liquidity_le,
    _h_locked_remaining, h_balance0, h_balance1, h_reserve0, h_reserve1,
    _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · exact h_reserve0
  · exact h_reserve1


-- tama: discharges=pair_closed_world_burn_never_increases_supply
theorem closed_world_burn_never_increases_supply
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_never_increases_supply
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  rw [h_supply]
  exact Nat.sub_le before.totalSupply liquidity

-- tama: discharges=pair_closed_world_burn_cannot_redeem_locked_liquidity
theorem closed_world_burn_cannot_redeem_locked_liquidity
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_cannot_redeem_locked_liquidity
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    h_supply, h_locked, _h_ratio0, _h_ratio1⟩
  rw [h_supply]
  exact ⟨h_locked_remaining, h_locked⟩


-- tama: discharges=pair_closed_world_burn_preserves_positive_balances
theorem closed_world_burn_preserves_positive_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_preserves_positive_balances
    amount0 amount1 liquidity before after := by
  intro h_good h_step h_before_balance0 h_before_balance1
  rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply_good⟩
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    h_supply_pos, h_amount0_le, h_amount1_le, _h_liquidity_le,
    h_locked_remaining, h_balance0, h_balance1, _h_reserve0, _h_reserve1,
    _h_bound0, _h_bound1, _h_supply, _h_locked, h_ratio0, h_ratio1⟩
  have h_locked : before.lockedLiquidity = minimumLiquidityNat := by
    rcases h_supply_good with h_empty | h_nonempty
    · exact False.elim (Nat.ne_of_gt h_supply_pos h_empty.1)
    · exact h_nonempty.2.1
  have h_locked_remaining_min :
      minimumLiquidityNat ≤ before.totalSupply - liquidity := by
    simpa [h_locked] using h_locked_remaining
  have h_liquidity_lt_supply : liquidity < before.totalSupply := by
    have h_sub_pos : 0 < before.totalSupply - liquidity := by
      exact Nat.lt_of_lt_of_le (by norm_num [minimumLiquidityNat])
        h_locked_remaining_min
    exact Nat.sub_pos_iff_lt.mp h_sub_pos
  have h_amount0_lt : amount0 < before.balance0 := by
    by_contra h_not_lt
    have h_ge : before.balance0 ≤ amount0 := Nat.le_of_not_gt h_not_lt
    have h_eq : amount0 = before.balance0 := le_antisymm h_amount0_le h_ge
    have h_ratio0' :
        before.balance0 * before.totalSupply ≤ liquidity * before.balance0 := by
      simpa [h_eq] using h_ratio0
    have h_balance_pos_int : (0 : Int) < before.balance0 := by
      exact_mod_cast h_before_balance0
    have h_liquidity_lt_int : (liquidity : Int) < before.totalSupply := by
      exact_mod_cast h_liquidity_lt_supply
    have h_ratio0_int :
        (before.balance0 : Int) * before.totalSupply ≤
          (liquidity : Int) * before.balance0 := by
      exact_mod_cast h_ratio0'
    nlinarith
  have h_amount1_lt : amount1 < before.balance1 := by
    by_contra h_not_lt
    have h_ge : before.balance1 ≤ amount1 := Nat.le_of_not_gt h_not_lt
    have h_eq : amount1 = before.balance1 := le_antisymm h_amount1_le h_ge
    have h_ratio1' :
        before.balance1 * before.totalSupply ≤ liquidity * before.balance1 := by
      simpa [h_eq] using h_ratio1
    have h_balance_pos_int : (0 : Int) < before.balance1 := by
      exact_mod_cast h_before_balance1
    have h_liquidity_lt_int : (liquidity : Int) < before.totalSupply := by
      exact_mod_cast h_liquidity_lt_supply
    have h_ratio1_int :
        (before.balance1 : Int) * before.totalSupply ≤
          (liquidity : Int) * before.balance1 := by
      exact_mod_cast h_ratio1'
    nlinarith
  constructor
  · rw [h_balance0]
    omega
  · rw [h_balance1]
    omega


private theorem pairWorldStep_positive_reserves_preserved
    {action : PairWorldAction} {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      0 < before.reserve0 →
        0 < before.reserve1 →
          PairWorldStep action before after →
            0 < after.reserve0 ∧
            0 < after.reserve1 := by
  intro h_good h_supply_pos h_reserve0_pos h_reserve1_pos h_step
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      rw [h_reserve0, h_reserve1]
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨h_amount0_pos, h_amount1_pos, _h_liquidity_pos,
        h_before_balance0, h_before_balance1, _h_after_balance0,
        _h_after_balance1, h_after_reserve0, h_after_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
      constructor
      · rw [h_after_reserve0, h_before_balance0]
        omega
      · rw [h_after_reserve1, h_before_balance1]
        omega
  | burn amount0 amount1 liquidity =>
      have h_good_copy := h_good
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1,
        _h_supply_good⟩
      have h_balance0_pos : 0 < before.balance0 :=
        Nat.lt_of_lt_of_le h_reserve0_pos h_back0
      have h_balance1_pos : 0 < before.balance1 :=
        Nat.lt_of_lt_of_le h_reserve1_pos h_back1
      have h_balances :=
        closed_world_burn_preserves_positive_balances
          amount0 amount1 liquidity before after
          h_good_copy h_step h_balance0_pos h_balance1_pos
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
        _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity,
        _h_locked_remaining, h_balance0, h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
      constructor
      · rw [h_reserve0]
        exact h_balances.1
      · rw [h_reserve1]
        exact h_balances.2
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, h_liq0, h_liq1, _h_enough0, _h_enough1,
        _h_input, h_balance0, h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1,
        _h_adjusted_k⟩
      constructor
      · rw [h_reserve0, h_balance0]
        exact Nat.sub_pos_of_lt (by omega)
      · rw [h_reserve1, h_balance1]
        exact Nat.sub_pos_of_lt (by omega)
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      rw [h_reserve0, h_reserve1]
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | sync =>
      rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1,
        _h_supply_good⟩
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
        h_reserve0, h_reserve1, _h_supply, _h_locked⟩
      constructor
      · rw [h_reserve0]
        exact Nat.lt_of_lt_of_le h_reserve0_pos h_back0
      · rw [h_reserve1]
        exact Nat.lt_of_lt_of_le h_reserve1_pos h_back1

private theorem pairWorldReachable_positive_supply_positive_reserves
    {w : PairWorldState} :
  PairWorldReachable w →
    0 < w.totalSupply →
      0 < w.reserve0 ∧
      0 < w.reserve1 := by
  intro h_reachable
  induction h_reachable with
  | init =>
      intro h_positive
      simp [PairWorldInitial] at h_positive
  | step action h_before h_step ih =>
      intro h_positive_after
      rename_i before after
      have h_step_original := h_step
      cases action with
      | approve ownerAddr spender amount =>
          simp [PairWorldStep] at h_step
          subst after
          exact ih h_positive_after
      | transfer fromAddr toAddr amount =>
          simp [PairWorldStep] at h_step
          subst after
          exact ih h_positive_after
      | transferFrom spender fromAddr toAddr amount =>
          simp [PairWorldStep] at h_step
          subst after
          exact ih h_positive_after
      | donate amount0 amount1 =>
          simp [PairWorldStep] at h_step
          rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, h_supply, _h_locked⟩
          have h_positive_before : 0 < before.totalSupply := by
            rwa [h_supply] at h_positive_after
          have h_before_reserves := ih h_positive_before
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_positive_before h_before_reserves.1 h_before_reserves.2
            h_step_original
      | mint amount0 amount1 liquidity =>
          simp [PairWorldStep, PairWorldMintStep] at h_step
          rcases h_step with ⟨h_amount0_pos, h_amount1_pos, _h_liquidity_pos,
            h_before_balance0, h_before_balance1, _h_after_balance0,
            _h_after_balance1, h_after_reserve0, h_after_reserve1,
            _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
          constructor
          · rw [h_after_reserve0, h_before_balance0]
            omega
          · rw [h_after_reserve1, h_before_balance1]
            omega
      | burn amount0 amount1 liquidity =>
          simp [PairWorldStep, PairWorldBurnStep] at h_step
          rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
            h_supply_before_pos, _h_amount0, _h_amount1, _h_liquidity,
            _h_locked_remaining, _h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
            _h_ratio0, _h_ratio1⟩
          have h_before_reserves := ih h_supply_before_pos
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_supply_before_pos h_before_reserves.1 h_before_reserves.2
            h_step_original
      | swap amount0In amount1In amount0Out amount1Out =>
          simp [PairWorldStep, PairWorldSwapStep] at h_step
          rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
            _h_enough1, _h_input, _h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked,
            _h_fee0, _h_fee1, _h_adjusted_k⟩
          have h_positive_before : 0 < before.totalSupply := by
            rwa [h_supply] at h_positive_after
          have h_before_reserves := ih h_positive_before
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_positive_before h_before_reserves.1 h_before_reserves.2
            h_step_original
      | skim =>
          simp [PairWorldStep, PairWorldSkimStep] at h_step
          rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0,
            _h_reserve1, h_supply, _h_locked⟩
          have h_positive_before : 0 < before.totalSupply := by
            rwa [h_supply] at h_positive_after
          have h_before_reserves := ih h_positive_before
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_positive_before h_before_reserves.1 h_before_reserves.2
            h_step_original
      | sync =>
          simp [PairWorldStep, PairWorldSyncStep] at h_step
          rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
            _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
          have h_positive_before : 0 < before.totalSupply := by
            rwa [h_supply] at h_positive_after
          have h_before_reserves := ih h_positive_before
          exact pairWorldStep_positive_reserves_preserved
            (pairWorldReachable_good before h_before)
            h_positive_before h_before_reserves.1 h_before_reserves.2
            h_step_original

private theorem pairWorldPath_positive_reserves_preserved
    {before after : PairWorldState} :
  PairWorldGood before →
    0 < before.totalSupply →
      0 < before.reserve0 →
        0 < before.reserve1 →
          PairWorldPath before after →
            0 < after.reserve0 ∧
            0 < after.reserve1 := by
  intro h_good h_supply_pos h_reserve0_pos h_reserve1_pos h_path
  induction h_path with
  | refl =>
      exact ⟨h_reserve0_pos, h_reserve1_pos⟩
  | step action h_prefix h_step ih =>
      have h_good_before := pairWorldPath_preserves_good h_good h_prefix
      have h_supply_before :=
        pairWorldPath_positive_supply_preserved h_good h_supply_pos h_prefix
      have h_reserves_before := ih
      exact pairWorldStep_positive_reserves_preserved
        h_good_before h_supply_before
        h_reserves_before.1 h_reserves_before.2 h_step



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

-- tama: discharges=pair_closed_world_donation_increases_surplus_exactly
theorem closed_world_donation_increases_surplus_exactly
    (amount0 amount1 : Nat)
    (before after : PairWorldState) :
  pair_closed_world_donation_increases_surplus_exactly
    amount0 amount1 before after := by
  intro h_good h_step
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  simp [PairWorldStep] at h_step
  rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  unfold PairWorldSurplus0 PairWorldSurplus1
  constructor <;> omega

/-- No non-donation action can create new reserve surplus. Share bookkeeping
preserves any existing surplus; mint, burn, swap, skim, and sync either account
for balances as reserves or remove surplus; none of them can increase
`balance - reserve` without an explicit external token donation. -/
private def pair_closed_world_non_donation_step_never_increases_surplus
    (action : PairWorldAction)
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1, action ≠ PairWorldAction.donate amount0 amount1) →
        PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
        PairWorldSurplus1 after ≤ PairWorldSurplus1 before

private theorem closed_world_non_donation_step_never_increases_surplus
    (action : PairWorldAction)
    (before after : PairWorldState) :
  pair_closed_world_non_donation_step_never_increases_surplus
    action before after := by
  intro h_good h_step h_not_donation
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ⟨le_rfl, le_rfl⟩
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ⟨le_rfl, le_rfl⟩
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      rw [h_step]
      exact ⟨le_rfl, le_rfl⟩
  | donate amount0 amount1 =>
      exact False.elim (h_not_donation amount0 amount1 rfl)
  | mint amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldMintStep] at h_step
      rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
        _h_before_balance0, _h_before_balance1, h_after_balance0,
        h_after_balance1, h_after_reserve0, h_after_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_after_reserve0, h_after_reserve1, h_after_balance0, h_after_balance1]
      omega
  | burn amount0 amount1 liquidity =>
      simp [PairWorldStep, PairWorldBurnStep] at h_step
      rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
        _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity,
        _h_locked_remaining, h_balance0, h_balance1, h_reserve0, h_reserve1,
        _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_reserve0, h_reserve1]
      omega
  | swap amount0In amount1In amount0Out amount1Out =>
      simp [PairWorldStep, PairWorldSwapStep] at h_step
      rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0,
        _h_enough1, _h_input, h_balance0, h_balance1, h_reserve0,
        h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
        _h_fee0, _h_fee1, _h_adjusted_k⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_reserve0, h_reserve1]
      omega
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_balance0, h_balance1, h_reserve0, h_reserve1]
      omega
  | sync =>
      simp [PairWorldStep, PairWorldSyncStep] at h_step
      rcases h_step with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
        h_reserve0, h_reserve1, _h_supply, _h_locked⟩
      unfold PairWorldSurplus0 PairWorldSurplus1
      rw [h_balance0, h_balance1, h_reserve0, h_reserve1]
      omega

private theorem pairWorldNoDonationPath_never_increases_surplus
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPathNoDonation before after →
      PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
      PairWorldSurplus1 after ≤ PairWorldSurplus1 before := by
  intro h_good h_path
  induction h_path with
  | refl =>
      exact ⟨le_rfl, le_rfl⟩
  | step action h_prefix h_step h_not_donation ih =>
      have h_good_mid :=
        pairWorldPath_preserves_good h_good
          (pairWorldPath_of_noDonation h_prefix)
      have h_step_surplus :=
        closed_world_non_donation_step_never_increases_surplus
          action _ _ h_good_mid h_step h_not_donation
      exact ⟨Nat.le_trans h_step_surplus.1 ih.1,
        Nat.le_trans h_step_surplus.2 ih.2⟩

/-- Trace-level surplus isolation. Across any finite successful history with no
direct donation step, reserve surplus on either token side cannot increase. -/
private def pair_closed_world_no_donation_path_never_increases_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoDonation before after →
      PairWorldSurplus0 after ≤ PairWorldSurplus0 before ∧
      PairWorldSurplus1 after ≤ PairWorldSurplus1 before

private theorem closed_world_no_donation_path_never_increases_surplus
    (before after : PairWorldState) :
  pair_closed_world_no_donation_path_never_increases_surplus before after := by
  exact pairWorldNoDonationPath_never_increases_surplus

-- tama: discharges=pair_closed_world_reachable_no_donation_path_never_increases_surplus
theorem closed_world_reachable_no_donation_path_never_increases_surplus
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_donation_path_never_increases_surplus
    before after := by
  intro h_reachable h_path
  exact pairWorldNoDonationPath_never_increases_surplus
    (pairWorldReachable_good before h_reachable) h_path






-- tama: discharges=pair_burn_success_pays_exact_pro_rata_amounts
theorem burn_success_pays_exact_pro_rata_amounts
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_pays_exact_pro_rata_amounts
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success _h_liquidity_pos _h_supply_pos
  simp [burnAmount0, burnAmount1, burnAmount0Product, burnAmount1Product,
    observedBalance0, observedBalance1, pairToken0, pairToken1, pairSelf,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.fst, Verity.pure, Pure.pure]

-- tama: discharges=pair_burn_success_caches_post_redemption_balances
theorem burn_success_caches_post_redemption_balances
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_caches_post_redemption_balances
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success _h_liquidity_pos _h_supply_pos
    _h_amount0_le _h_amount1_le
  simp [pairWorldAfterBurnRun]


-- tama: discharges=pair_swap_success_accounts_for_input_and_output
theorem swap_success_accounts_for_input_and_output
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_accounts_for_input_and_output
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_k
  dsimp [pair_swap_success_accounts_for_input_and_output,
    pairWorldFromConcreteState, pairWorldAfterSwapRun]
  constructor
  · have h_cover0 :
        amount0Out.val ≤
          (s.storage reserve0Slot.slot).val +
            (swapAmount0In amount0Out balance0Now s).val := by
      have h_liq0_val :
          amount0Out.val < (s.storage reserve0Slot.slot).val := by
        simpa [Verity.Core.Uint256.lt_def] using h_liq0
      omega
    calc
      balance0Now.val + amount0Out.val
          = ((s.storage reserve0Slot.slot).val +
                (swapAmount0In amount0Out balance0Now s).val -
              amount0Out.val) + amount0Out.val := by rw [h_balance0]
      _ = (s.storage reserve0Slot.slot).val +
            (swapAmount0In amount0Out balance0Now s).val := by
          exact Nat.sub_add_cancel h_cover0
  · have h_cover1 :
        amount1Out.val ≤
          (s.storage reserve1Slot.slot).val +
            (swapAmount1In amount1Out balance1Now s).val := by
      have h_liq1_val :
          amount1Out.val < (s.storage reserve1Slot.slot).val := by
        simpa [Verity.Core.Uint256.lt_def] using h_liq1
      omega
    calc
      balance1Now.val + amount1Out.val
          = ((s.storage reserve1Slot.slot).val +
                (swapAmount1In amount1Out balance1Now s).val -
              amount1Out.val) + amount1Out.val := by rw [h_balance1]
      _ = (s.storage reserve1Slot.slot).val +
            (swapAmount1In amount1Out balance1Now s).val := by
          exact Nat.sub_add_cancel h_cover1

-- tama: discharges=pair_swap_success_charges_k_against_final_balances
theorem swap_success_charges_k_against_final_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_charges_k_against_final_balances
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_k
  simpa [pair_swap_success_charges_k_against_final_balances,
    pairWorldFromConcreteState, pairWorldAfterSwapRun] using h_k

/- One valid action cannot dilute existing LP shares: measured
as reserve product per squared LP supply, the pool is at least as strong after
the step as before it. -/
private def pair_closed_world_step_k_per_supply_never_decreases
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldStep action before after →
        PairWorldKPerSupplyNondecreasing before after

private theorem closed_world_step_k_per_supply_never_decreases
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_step_k_per_supply_never_decreases action before after := by
  exact pairWorldStep_k_per_supply_never_decreases

/- The one-step dilution bound composes over every finite path. This is the
main sequence invariant: no combination of transfers, donations, mint, burn,
swap, skim, or sync can reduce LP-normalized K from a good positive-supply
state. -/
private def pair_closed_world_path_k_per_supply_never_decreases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        PairWorldKPerSupplyNondecreasing before after

private theorem closed_world_path_k_per_supply_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_path_k_per_supply_never_decreases before after := by
  exact pairWorldPath_k_per_supply_never_decreases

-- tama: discharges=pair_closed_world_reachable_path_lp_share_backing_never_decreases
theorem closed_world_reachable_path_lp_share_backing_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_lp_share_backing_never_decreases before after := by
  intro h_reachable h_positive h_path
  exact pairWorldPath_k_per_supply_never_decreases
    (pairWorldReachable_good before h_reachable) h_positive h_path

private theorem pairWalletStep_pairPath
    {action : PairWalletAction} {before after : PairWalletWorldState} :
  PairWalletStep action before after →
    PairWorldPath before.pair after.pair := by
  intro h_step
  cases action <;>
    simp [PairWalletStep] at h_step
  · subst after
    exact PairWorldPath.refl before.pair
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.2.2.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.2.1
  · exact PairWorldPath.step _ (PairWorldPath.refl before.pair) h_step.1

private theorem pairWalletHistory_pairPath
    {before after : PairWalletWorldState} :
  PairWalletHistory before after →
    PairWorldPath before.pair after.pair := by
  intro h_history
  induction h_history with
  | refl => exact PairWorldPath.refl before.pair
  | step action h_prefix h_step ih =>
      cases action <;>
        simp [PairWalletStep] at h_step
      · simpa [h_step] using ih
      · exact PairWorldPath.step (PairWorldAction.donate _ _) ih h_step.2.2.1
      · exact PairWorldPath.step PairWorldAction.skim ih h_step.1
      · exact PairWorldPath.step
          (PairWorldAction.swap _ _ _ _) ih h_step.1
      · exact PairWorldPath.step
          (PairWorldAction.mint _ _ _) ih h_step.1
      · exact PairWorldPath.step
          (PairWorldAction.burn _ _ _) ih h_step.2.1
      · exact PairWorldPath.step PairWorldAction.sync ih h_step.1

private theorem pairWalletStep_total_value_conserved
    (spot : PairWorldState) {action : PairWalletAction}
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    PairWalletStep action before after →
      PairWalletTotalTokenValueAtSpot spot before =
        PairWalletTotalTokenValueAtSpot spot after := by
  intro h_good h_step
  rcases h_good with ⟨h_pair_good, _h_wallet⟩
  rcases h_pair_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  cases action <;>
    simp [PairWalletStep, PairWorldStep, PairWorldMintStep, PairWorldBurnStep,
      PairWorldSwapStep, PairWorldSkimStep, PairWorldSyncStep] at h_step
  · subst after
    rfl
  · rcases h_step with ⟨h_token0, h_token1, h_pair, h_caller0, h_caller1, _h_lp⟩
    rename_i amount0 amount1
    rcases h_pair with ⟨h_balance0, h_balance1, _h_reserve0, _h_reserve1,
      _h_supply, _h_locked⟩
    have h_caller0_add : after.callerToken0 + amount0 = before.callerToken0 := by
      rw [h_caller0]
      omega
    have h_caller1_add : after.callerToken1 + amount1 = before.callerToken1 := by
      rw [h_caller1]
      omega
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_balance0, h_balance1]
    nlinarith
  · rcases h_step with ⟨h_pair, h_amount0, h_amount1, h_caller0, h_caller1, _h_lp⟩
    rcases h_pair with ⟨h_balance0, h_balance1, _h_reserve0, _h_reserve1,
      _h_supply, _h_locked⟩
    have h_surplus0 :
        before.pair.balance0 =
          before.pair.reserve0 + PairWorldSurplus0 before.pair := by
      unfold PairWorldSurplus0
      omega
    have h_surplus1 :
        before.pair.balance1 =
          before.pair.reserve1 + PairWorldSurplus1 before.pair := by
      unfold PairWorldSurplus1
      omega
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1, h_balance0, h_balance1, h_amount0, h_amount1,
      h_surplus0, h_surplus1]
    nlinarith
  · rcases h_step with ⟨h_pair, h_amount0In, h_amount1In, h_caller0,
      h_caller1, _h_lp⟩
    rename_i amount0In amount1In amount0Out amount1Out
    rcases h_pair with ⟨_h_output, _h_liq0, _h_liq1, h_enough0, h_enough1,
      _h_input, h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
      _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_k⟩
    have h_before_balance0 :
        before.pair.balance0 = before.pair.reserve0 + amount0In := by
      rw [h_amount0In]
      unfold PairWorldSurplus0
      omega
    have h_before_balance1 :
        before.pair.balance1 = before.pair.reserve1 + amount1In := by
      rw [h_amount1In]
      unfold PairWorldSurplus1
      omega
    have h_after_plus0 :
        after.pair.balance0 + amount0Out = before.pair.reserve0 + amount0In := by
      rw [h_balance0, Nat.sub_add_cancel h_enough0]
    have h_after_plus1 :
        after.pair.balance1 + amount1Out = before.pair.reserve1 + amount1In := by
      rw [h_balance1, Nat.sub_add_cancel h_enough1]
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1, h_before_balance0, h_before_balance1]
    nlinarith
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, h_caller0,
      h_caller1, _h_lp⟩
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_balance0_before, _h_balance1_before, h_balance0, h_balance1,
      _h_reserve0, _h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
      _h_ratio⟩
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1, h_balance0, h_balance1]
  · rcases h_step with ⟨_h_lp_enough, h_pair, h_caller0, h_caller1, _h_lp⟩
    rename_i amount0 amount1 liquidity
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_supply_pos, h_amount0_le, h_amount1_le, _h_liq_le, _h_locked_le,
      h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
      _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
    have h_balance0_add : after.pair.balance0 + amount0 = before.pair.balance0 := by
      rw [h_balance0]
      omega
    have h_balance1_add : after.pair.balance1 + amount1 = before.pair.balance1 := by
      rw [h_balance1]
      omega
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1]
    nlinarith
  · rcases h_step with ⟨h_pair, h_caller0, h_caller1, _h_lp⟩
    rcases h_pair with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
      _h_reserve0, _h_reserve1, _h_supply, _h_locked⟩
    unfold PairWalletTotalTokenValueAtSpot PairWalletCallerTokenValueAtSpot
      PairWorldBalanceSpotValueNum
    rw [h_caller0, h_caller1, h_balance0, h_balance1]

private theorem pairWorldGood_positive_supply_locked_pos
    {w : PairWorldState} :
  PairWorldGood w →
    0 < w.totalSupply →
      0 < w.lockedLiquidity := by
  intro h_good h_positive
  rcases h_good with ⟨_h_back0, _h_back1, _h_bound0, _h_bound1, h_supply_good⟩
  rcases h_supply_good with h_empty | h_nonempty
  · omega
  · rcases h_nonempty with ⟨_h_supply, h_locked, _h_min⟩
    rw [h_locked]
    norm_num [minimumLiquidityNat]

private theorem pairWalletStep_preserves_good_and_positive
    {action : PairWalletAction} {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletStep action before after →
        PairWalletGood after ∧
          0 < after.pair.totalSupply ∧
          after.pair.lockedLiquidity = before.pair.lockedLiquidity := by
  intro h_good h_positive h_step
  rcases h_good with ⟨h_pair_good, h_wallet⟩
  cases action <;>
    simp [PairWalletStep, PairWorldStep, PairWorldMintStep, PairWorldBurnStep,
      PairWorldSwapStep, PairWorldSkimStep, PairWorldSyncStep] at h_step
  · subst after
    exact ⟨⟨h_pair_good, h_wallet⟩, h_positive, rfl⟩
  · rcases h_step with ⟨_h_token0, _h_token1, h_pair, _h_caller0, _h_caller1,
      h_lp⟩
    rename_i amount0 amount1
    have h_pair_step :
        PairWorldStep (PairWorldAction.donate amount0 amount1) before.pair after.pair := by
      simpa [PairWorldStep] using h_pair
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, h_locked⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0, _h_caller1,
      h_lp⟩
    have h_pair_step : PairWorldStep PairWorldAction.skim before.pair after.pair := by
      simpa [PairWorldStep, PairWorldSkimStep] using h_pair
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, h_locked⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega
  · rcases h_step with ⟨h_pair, _h_amount0In, _h_amount1In, _h_caller0,
      _h_caller1, h_lp⟩
    rename_i amount0In amount1In amount0Out amount1Out
    have h_pair_step :
        PairWorldStep
          (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
          before.pair after.pair := by
      simpa [PairWorldStep, PairWorldSwapStep] using h_pair
    rcases h_pair with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
      _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
      _h_bound1, h_supply, h_locked, _h_fee0, _h_fee1, _h_k⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0,
      _h_caller1, h_lp⟩
    rename_i amount0 amount1 liquidity
    have h_pair_step :
        PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity)
          before.pair after.pair := by
      simpa [PairWorldStep, PairWorldMintStep] using h_pair
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_balance0_before, _h_balance1_before, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, _h_bound0, _h_bound1, h_supply, h_locked,
      _h_ratio⟩
    rw [if_neg (Nat.ne_of_gt h_positive)] at h_supply
    rw [if_neg (Nat.ne_of_gt h_positive)] at h_locked
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega
  · rcases h_step with ⟨h_lp_enough, h_pair, _h_caller0, _h_caller1, h_lp⟩
    rename_i amount0 amount1 liquidity
    have h_pair_step :
        PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity)
          before.pair after.pair := by
      simpa [PairWorldStep, PairWorldBurnStep] using h_pair
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liq_le, h_locked_le,
      _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
      h_supply, h_locked, _h_ratio0, _h_ratio1⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    have h_locked_pos := pairWorldGood_positive_supply_locked_pos h_pair_good h_positive
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · constructor
      · omega
      · exact h_locked
  · rcases h_step with ⟨h_pair, _h_caller0, _h_caller1, h_lp⟩
    have h_pair_step : PairWorldStep PairWorldAction.sync before.pair after.pair := by
      simpa [PairWorldStep, PairWorldSyncStep] using h_pair
    rcases h_pair with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, h_supply, h_locked⟩
    have h_pair_good_after := pairWorldStep_preserves_good h_pair_good h_pair_step
    constructor
    · constructor
      · exact h_pair_good_after
      · omega
    · omega

/- If a finite path returns to the same LP supply, LP normalization cancels.
The pool's raw reserve product therefore cannot be lower than where it began. -/
private def pair_closed_world_same_supply_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldK before ≤ PairWorldK after

private theorem closed_world_same_supply_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_same_supply_path_never_decreases_k before after := by
  exact pairWorldSameSupplyPath_never_decreases_k

/- Constant-product arithmetic: once raw K is known not to fall, the final
reserves cannot be worth less than the initial reserves at the initial spot
price. This lemma is kept parameterized by the K fact so other sequence
arguments can reuse the geometric conversion directly. -/
private def pair_closed_world_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldPath before after →
    PairWorldGood before →
      before.totalSupply = after.totalSupply →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldK before ≤ PairWorldK after →
              PairWorldNoSpotProfit before after

private theorem closed_world_same_supply_path_no_spot_profit
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

/- The complete same-supply no-profit theorem for the closed-world pool model:
from any good positive-supply state with nonzero reserves, every finite path
that ends with the same LP supply has no spot-price profit. This version allows
mint/burn round trips because it relies on LP-normalized K rather than the older
no-burn K theorem. -/
private def pair_closed_world_positive_supply_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
            0 < before.reserve1 →
              PairWorldNoSpotProfit before after

private theorem closed_world_positive_supply_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_positive_supply_same_supply_path_no_spot_profit before after := by
  intro h_good h_positive h_path h_supply h_reserve0 h_reserve1
  have h_k :
      PairWorldK before ≤ PairWorldK after :=
    pairWorldSameSupplyPath_never_decreases_k h_good h_positive h_path h_supply
  exact closed_world_same_supply_path_no_spot_profit before after
    h_path h_good h_supply h_reserve0 h_reserve1 h_k






/- The reachable-state version of the same-supply K theorem is the one most
callers should cite: from any actually reachable nonempty pool, any finite
successful sequence that returns LP supply to its starting value cannot reduce
raw reserve product. -/
private def pair_closed_world_reachable_same_supply_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          PairWorldK before ≤ PairWorldK after

private theorem closed_world_reachable_same_supply_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_never_decreases_k before after := by
  intro h_reachable h_positive h_path h_supply
  exact pairWorldSameSupplyPath_never_decreases_k
    (pairWorldReachable_good before h_reachable) h_positive h_path h_supply

/- The reachable-state no-profit theorem states the economic conclusion in the
language of the contract user. Starting from any reachable nonempty pool with a
defined spot price, any finite successful sequence that leaves LP supply
unchanged leaves the pool worth at least as much at the initial spot price.
Without an external gift to the caller, that rules out spot-price profit. -/
private def pair_closed_world_reachable_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
            0 < before.reserve1 →
              PairWorldNoSpotProfit before after

private theorem closed_world_reachable_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_no_spot_profit before after := by
  intro h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  exact closed_world_positive_supply_same_supply_path_no_spot_profit before after
    (pairWorldReachable_good before h_reachable)
    h_positive h_path h_supply h_reserve0 h_reserve1


/-- Caller-facing form of the same theorem. `PairWorld` tracks pool-side token
balances and LP supply, not arbitrary external wallet balances, so the
closed-world no-profit claim is stated as absence of pool value extraction: if a
finite successful history returns LP supply to its starting value, the final pool
cannot be worth less at the initial spot price. Any positive closed-world caller
profit would have to appear as that missing pool value; external gifts are
outside this theorem's closed-world premise. -/
private def pair_closed_world_reachable_same_supply_path_no_spot_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPath before after →
        before.totalSupply = after.totalSupply →
          0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldSpotValueNum before before ≤
              PairWorldSpotValueNum before after

private theorem closed_world_reachable_same_supply_path_no_spot_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_no_spot_value_extraction before after := by
  intro h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  have h_no_profit :=
    closed_world_reachable_same_supply_path_no_spot_profit
      before after h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  unfold PairWorldNoSpotProfit PairWorldSpotValueNum PairWorldK at h_no_profit
  unfold PairWorldSpotValueNum
  nlinarith



private theorem pairWorldSpotValue_le_balanceSpotValue
    {spot pool : PairWorldState} :
  PairWorldGood pool →
    PairWorldSpotValueNum spot pool ≤
      PairWorldBalanceSpotValueNum spot pool := by
  intro h_good
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  unfold PairWorldSpotValueNum PairWorldBalanceSpotValueNum
  exact Nat.add_le_add
    (Nat.mul_le_mul_right spot.reserve1 h_back0)
    (Nat.mul_le_mul_right spot.reserve0 h_back1)

private theorem pairWorldBalanceSpotValue_eq_spot_plus_surplus
    {spot pool : PairWorldState} :
  PairWorldGood pool →
    PairWorldBalanceSpotValueNum spot pool =
      PairWorldSpotValueNum spot pool +
        PairWorldSurplusSpotValueNum spot pool := by
  intro h_good
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  have h_balance0 :
      pool.balance0 = pool.reserve0 + PairWorldSurplus0 pool := by
    unfold PairWorldSurplus0
    omega
  have h_balance1 :
      pool.balance1 = pool.reserve1 + PairWorldSurplus1 pool := by
    unfold PairWorldSurplus1
    omega
  unfold PairWorldBalanceSpotValueNum PairWorldSpotValueNum
    PairWorldSurplusSpotValueNum
  rw [h_balance0, h_balance1]
  nlinarith

private theorem pairWalletHistory_preserves_good_and_positive
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletHistory before after →
        PairWalletGood after ∧
          0 < after.pair.totalSupply ∧
          after.pair.lockedLiquidity = before.pair.lockedLiquidity := by
  intro h_good h_positive h_history
  revert h_good h_positive
  induction h_history with
  | refl =>
      intro h_good h_positive
      exact ⟨h_good, h_positive, rfl⟩
  | step action h_prefix h_step ih =>
      intro h_good h_positive
      rcases ih h_good h_positive with
        ⟨h_mid_good, h_mid_positive, h_mid_locked⟩
      rcases pairWalletStep_preserves_good_and_positive
          h_mid_good h_mid_positive h_step with
        ⟨h_after_good, h_after_positive, h_after_locked⟩
      exact ⟨h_after_good, h_after_positive, by rw [h_after_locked, h_mid_locked]⟩

private theorem pairWalletHistory_total_value_conserved
    (spot : PairWorldState) {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletHistory before after →
        PairWalletTotalTokenValueAtSpot spot before =
          PairWalletTotalTokenValueAtSpot spot after := by
  intro h_good h_positive h_history
  revert h_good h_positive
  induction h_history with
  | refl =>
      intro _h_good _h_positive
      rfl
  | step action h_prefix h_step ih =>
      intro h_good h_positive
      have h_prefix_value := ih h_good h_positive
      rcases pairWalletHistory_preserves_good_and_positive
          h_good h_positive h_prefix with
        ⟨h_mid_good, _h_mid_positive, _h_mid_locked⟩
      have h_step_value :=
        pairWalletStep_total_value_conserved spot h_mid_good h_step
      exact h_prefix_value.trans h_step_value

private theorem pairWalletPortfolio_plus_unowned_eq_total
    (spot : PairWorldState) (w : PairWalletWorldState) :
  PairWalletGood w →
    PairWalletPortfolioValueNumeratorAtSpot spot w +
        (w.pair.totalSupply - w.callerLp) * PairWorldSpotValueNum spot w.pair =
      PairWalletTotalTokenValueAtSpot spot w * w.pair.totalSupply := by
  intro h_good
  rcases h_good with ⟨h_pair_good, h_wallet⟩
  have h_balance_eq :=
    pairWorldBalanceSpotValue_eq_spot_plus_surplus
      (spot := spot) (pool := w.pair) h_pair_good
  have h_le : w.callerLp ≤ w.pair.totalSupply := by omega
  unfold PairWalletPortfolioValueNumeratorAtSpot PairWalletTotalTokenValueAtSpot
    PairWalletCallerTokenValueAtSpot PairWalletSkimmableValueAtSpot
  rw [h_balance_eq]
  have h_split :
      (w.pair.totalSupply - w.callerLp) * PairWorldSpotValueNum spot w.pair +
          w.callerLp * PairWorldSpotValueNum spot w.pair =
        w.pair.totalSupply * PairWorldSpotValueNum spot w.pair := by
    rw [← Nat.add_mul]
    congr 1
    omega
  nlinarith [h_split]

private theorem pairWorldKPerSupply_spot_value_per_supply
    {spot after : PairWorldState} :
  0 < spot.totalSupply →
    0 < after.totalSupply →
      0 < spot.reserve0 →
        0 < spot.reserve1 →
          PairWorldKPerSupplyNondecreasing spot after →
            PairWorldSpotValueNum spot spot * after.totalSupply ≤
              PairWorldSpotValueNum spot after * spot.totalSupply := by
  intro h_spot_supply h_after_supply h_reserve0 h_reserve1 h_k_scaled
  unfold PairWorldKPerSupplyNondecreasing PairWorldSpotValueNum PairWorldK at *
  by_contra h_not
  have h_lt :
      (after.reserve0 * spot.reserve1 + after.reserve1 * spot.reserve0) *
          spot.totalSupply <
        (spot.reserve0 * spot.reserve1 + spot.reserve1 * spot.reserve0) *
          after.totalSupply :=
    Nat.lt_of_not_ge h_not
  have h_reserve0_int : (0 : Int) < spot.reserve0 := by
    exact_mod_cast h_reserve0
  have h_reserve1_int : (0 : Int) < spot.reserve1 := by
    exact_mod_cast h_reserve1
  have h_spot_supply_int : (0 : Int) < spot.totalSupply := by
    exact_mod_cast h_spot_supply
  have h_after_supply_int : (0 : Int) < after.totalSupply := by
    exact_mod_cast h_after_supply
  let a : Int := spot.reserve0
  let b : Int := spot.reserve1
  let c : Int := after.reserve0
  let d : Int := after.reserve1
  let s0 : Int := spot.totalSupply
  let s1 : Int := after.totalSupply
  have ha : 0 < a := by simpa [a] using h_reserve0_int
  have hb : 0 < b := by simpa [b] using h_reserve1_int
  have hc : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast Nat.zero_le after.reserve0
  have hd : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast Nat.zero_le after.reserve1
  have hs0 : 0 < s0 := by simpa [s0] using h_spot_supply_int
  have hs1 : 0 < s1 := by simpa [s1] using h_after_supply_int
  have hk :
      a * b * s1 * s1 ≤ c * d * s0 * s0 := by
    dsimp [a, b, c, d, s0, s1]
    exact_mod_cast h_k_scaled
  have hlt :
      (c * b + d * a) * s0 < (a * b + b * a) * s1 := by
    dsimp [a, b, c, d, s0, s1]
    exact_mod_cast h_lt
  have hsq : 0 ≤ (c * b * s0 - d * a * s0) ^ 2 := sq_nonneg _
  have hamgm :
      4 * c * d * a * b * s0 * s0 ≤
        ((c * b + d * a) * s0) ^ 2 := by
    nlinarith [hsq]
  have hab_pos : 0 < a * b := by
    nlinarith [ha, hb]
  have hkscaled :
      4 * a * b * a * b * s1 * s1 ≤
        4 * c * d * a * b * s0 * s0 := by
    nlinarith [hk, hab_pos]
  have hsum_nonneg : 0 ≤ (c * b + d * a) * s0 := by
    have hcb_nonneg : 0 ≤ c * b := mul_nonneg hc (le_of_lt hb)
    have hda_nonneg : 0 ≤ d * a := mul_nonneg hd (le_of_lt ha)
    exact mul_nonneg (add_nonneg hcb_nonneg hda_nonneg) (le_of_lt hs0)
  have htarget_pos : 0 < (a * b + b * a) * s1 := by
    have hab_pos' : 0 < a * b := mul_pos ha hb
    have hba_pos : 0 < b * a := mul_pos hb ha
    exact mul_pos (add_pos hab_pos' hba_pos) hs1
  have hlt_sq :
      ((c * b + d * a) * s0) ^ 2 <
        ((a * b + b * a) * s1) ^ 2 := by
    nlinarith [hlt, hsum_nonneg, htarget_pos]
  nlinarith [hamgm, hkscaled, hlt_sq]

private theorem pairWalletStep_preserves_unowned
    {action : PairWalletAction} {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletStep action before after →
        after.pair.totalSupply - after.callerLp =
          before.pair.totalSupply - before.callerLp := by
  intro h_good h_positive h_step
  rcases h_good with ⟨_h_pair_good, h_wallet⟩
  cases action <;>
    simp [PairWalletStep, PairWorldStep, PairWorldMintStep, PairWorldBurnStep,
      PairWorldSwapStep, PairWorldSkimStep, PairWorldSyncStep] at h_step
  · subst after; rfl
  · rcases h_step with ⟨_h_token0, _h_token1, h_pair, _h_caller0, _h_caller1,
      h_lp⟩
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, _h_locked⟩
    omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0, _h_caller1,
      h_lp⟩
    rcases h_pair with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
      h_supply, _h_locked⟩
    omega
  · rcases h_step with ⟨h_pair, _h_amount0In, _h_amount1In, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
      _h_input, _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
      _h_bound1, h_supply, _h_locked, _h_fee0, _h_fee1, _h_k⟩
    omega
  · rcases h_step with ⟨h_pair, _h_amount0, _h_amount1, _h_caller0,
      _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_balance0_before, _h_balance1_before, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, _h_bound0, _h_bound1, h_supply, _h_locked,
      _h_ratio⟩
    rw [if_neg (Nat.ne_of_gt h_positive)] at h_supply
    omega
  · rcases h_step with ⟨h_lp_enough, h_pair, _h_caller0, _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
      _h_supply_pos, _h_amount0_le, _h_amount1_le, h_liq_le, _h_locked_le,
      _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
      h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
    omega
  · rcases h_step with ⟨h_pair, _h_caller0, _h_caller1, h_lp⟩
    rcases h_pair with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
      _h_reserve0, _h_reserve1, h_supply, _h_locked⟩
    omega

private theorem pairWalletHistory_preserves_unowned
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      PairWalletHistory before after →
        after.pair.totalSupply - after.callerLp =
          before.pair.totalSupply - before.callerLp := by
  intro h_good h_positive h_history
  revert h_good h_positive
  induction h_history with
  | refl =>
      intro _h_good _h_positive
      rfl
  | step action h_prefix h_step ih =>
      intro h_good h_positive
      have h_mid := ih h_good h_positive
      rcases pairWalletHistory_preserves_good_and_positive
          h_good h_positive h_prefix with
        ⟨h_mid_good, h_mid_positive, _h_mid_locked⟩
      have h_step_eq :=
        pairWalletStep_preserves_unowned h_mid_good h_mid_positive h_step
      rw [h_step_eq]; exact h_mid

private theorem pairWalletHistory_no_portfolio_profit
    {before after : PairWalletWorldState} :
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletHistory before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply := by
  intro h_good h_supply h_reserve0 h_reserve1 h_history
  have h_path := pairWalletHistory_pairPath h_history
  rcases pairWalletHistory_preserves_good_and_positive
      h_good h_supply h_history with
    ⟨h_good_after, h_supply_after, _h_locked_after⟩
  have h_total :=
    pairWalletHistory_total_value_conserved before.pair
      h_good h_supply h_history
  have h_unowned :=
    pairWalletHistory_preserves_unowned h_good h_supply h_history
  have h_k_scaled :=
    pairWorldPath_k_per_supply_never_decreases
      h_good.1 h_supply h_path
  have h_spot_per_supply :=
    pairWorldKPerSupply_spot_value_per_supply
      h_supply h_supply_after h_reserve0 h_reserve1 h_k_scaled
  have h_before_identity :=
    pairWalletPortfolio_plus_unowned_eq_total before.pair before h_good
  have h_after_identity :=
    pairWalletPortfolio_plus_unowned_eq_total before.pair after h_good_after
  rw [← h_total] at h_after_identity
  rw [h_unowned] at h_after_identity
  have h_unowned_spot :=
    Nat.mul_le_mul_left (before.pair.totalSupply - before.callerLp)
      h_spot_per_supply
  nlinarith [h_before_identity, h_after_identity, h_unowned_spot]

private theorem pairWalletPortfolio_in_token1_eq_numerator
    (spot : PairWorldState) (w : PairWalletWorldState) :
    0 < spot.reserve0 → 0 < w.pair.totalSupply →
      PairWalletPortfolioValueInToken1 spot w =
        (PairWalletPortfolioValueNumeratorAtSpot spot w : ℚ) /
          ((w.pair.totalSupply : ℚ) * (spot.reserve0 : ℚ)) := by
  intro h_reserve0 h_supply
  have h_reserve0_rat : (spot.reserve0 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp h_reserve0
  have h_supply_rat : (w.pair.totalSupply : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp h_supply
  unfold PairWalletPortfolioValueInToken1 PairWorldTokenValueRat
    PairWorldSpotPriceRat PairWalletPortfolioValueNumeratorAtSpot
    PairWalletCallerTokenValueAtSpot PairWalletSkimmableValueAtSpot
    PairWorldSurplusSpotValueNum PairWorldSpotValueNum
  field_simp
  ring

private def pair_wallet_single_caller_history_no_portfolio_profit
    (before after : PairWalletWorldState) : Prop :=
  PairWalletGood before →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletHistory before after →
            PairWalletPortfolioValueInToken1 before.pair after ≤
              PairWalletPortfolioValueInToken1 before.pair before

private theorem wallet_single_caller_history_no_portfolio_profit
    (before after : PairWalletWorldState) :
  pair_wallet_single_caller_history_no_portfolio_profit before after := by
  intro h_good h_supply h_reserve0 h_reserve1 h_history
  have h_nat := pairWalletHistory_no_portfolio_profit
    h_good h_supply h_reserve0 h_reserve1 h_history
  rcases pairWalletHistory_preserves_good_and_positive h_good h_supply h_history
    with ⟨_h_after_good, h_after_supply, _h_after_locked⟩
  have h_before := pairWalletPortfolio_in_token1_eq_numerator
    before.pair before h_reserve0 h_supply
  have h_after := pairWalletPortfolio_in_token1_eq_numerator
    before.pair after h_reserve0 h_after_supply
  rw [h_before, h_after]
  have h_reserve0_rat : (0 : ℚ) < (before.pair.reserve0 : ℚ) := by
    exact_mod_cast h_reserve0
  have h_before_supply_rat : (0 : ℚ) < (before.pair.totalSupply : ℚ) := by
    exact_mod_cast h_supply
  have h_after_supply_rat : (0 : ℚ) < (after.pair.totalSupply : ℚ) := by
    exact_mod_cast h_after_supply
  have h_nat_rat :
      (PairWalletPortfolioValueNumeratorAtSpot before.pair after : ℚ) *
          (before.pair.totalSupply : ℚ) ≤
        (PairWalletPortfolioValueNumeratorAtSpot before.pair before : ℚ) *
          (after.pair.totalSupply : ℚ) := by
    exact_mod_cast h_nat
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h_nat_rat, h_reserve0_rat]

private theorem pairEconomicActionConcreteStep_wallet
    {caller : Address} {before after : PairWalletWorldState} :
  PairEconomicActionConcreteStep caller before after →
    ∃ action, PairWalletStep action before after := by
  intro h_step
  cases h_step with
  | mint toAddr preTokens s result liquidity expected hRun hSuccess hBefore
      hAfter hExpected hWallet =>
      exact ⟨PairWalletAction.callerMint
        (mintAmount0 s).val (mintAmount1 s).val liquidity.val, hWallet⟩
  | burn toAddr preTokens s result expected hRun hSuccess hBefore
      hAfter hExpected hWallet =>
      exact ⟨PairWalletAction.callerBurn
        (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val, hWallet⟩
  | swap amount0Out amount1Out toAddr data balance0Now balance1Now preTokens
      s result expected hRun hSuccess hBefore hAfter hExpected hWallet =>
      exact ⟨PairWalletAction.callerSwap
        (swapAmount0In amount0Out balance0Now s).val
        (swapAmount1In amount1Out balance1Now s).val
        amount0Out.val amount1Out.val, hWallet⟩
  | skim toAddr preTokens s result expected hRun hSuccess hBefore hAfter
      hExpected hWallet =>
      exact ⟨PairWalletAction.callerSkimReceive
        (PairWorldSurplus0 before.pair) (PairWorldSurplus1 before.pair), hWallet⟩
  | sync preTokens s result expected hRun hSuccess hBefore hAfter hExpected
      hWallet =>
      exact ⟨PairWalletAction.callerSync, hWallet⟩

private theorem pairEconomicActionConcretePath_walletHistory
    {caller : Address} {before after : PairWalletWorldState} :
  PairEconomicActionConcretePath caller before after →
    PairWalletHistory before after := by
  intro h_path
  induction h_path with
  | refl =>
      exact PairWalletHistory.refl before
  | step h_prefix h_step ih =>
      rcases pairEconomicActionConcreteStep_wallet h_step with
        ⟨action, h_wallet⟩
      exact PairWalletHistory.step action ih h_wallet

-- tama: discharges=pair_actual_execution_no_free_lunch
theorem actual_execution_no_free_lunch
    (caller : Address) (initialTokens : PairTokenBalances)
    (initialState : ContractState) (after : PairWalletWorldState) :
  pair_actual_execution_no_free_lunch caller initialTokens initialState after := by
  intro h_good h_supply h_reserve0 h_reserve1 h_path
  exact wallet_single_caller_history_no_portfolio_profit
    (pairWalletFromConcreteAndTokens caller initialTokens initialState)
    after h_good h_supply h_reserve0 h_reserve1
    (pairEconomicActionConcretePath_walletHistory h_path)

-- tama: discharges=pair_wallet_history_preserves_good
theorem wallet_history_preserves_good
    (before after : PairWalletWorldState) :
  pair_wallet_history_preserves_good before after := by
  intro h_good h_supply h_hist
  rcases pairWalletHistory_preserves_good_and_positive h_good h_supply h_hist
    with ⟨h_after_good, _h_after_supply, _h_after_locked⟩
  exact h_after_good

-- tama: discharges=pair_wallet_history_total_value_conserved
theorem wallet_history_total_value_conserved
    (spot : PairWorldState) (before after : PairWalletWorldState) :
  pair_wallet_history_total_value_conserved spot before after := by
  intro h_good h_supply h_hist
  exact pairWalletHistory_total_value_conserved spot h_good h_supply h_hist

-- tama: discharges=pair_wallet_history_preserves_unowned
theorem wallet_history_preserves_unowned
    (before after : PairWalletWorldState) :
  pair_wallet_history_preserves_unowned before after := by
  intro h_good h_supply h_hist
  exact pairWalletHistory_preserves_unowned h_good h_supply h_hist

/-- Non-liquidity histories are the common operational case: swaps, surplus
management, donations, and LP-token bookkeeping, but no mint and no burn. The
supply firewall above makes these histories same-supply histories, so the
same no-extraction conclusion applies directly. -/
private def pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    (before after : PairWorldState) : Prop :=
  PairWorldReachable before →
    0 < before.totalSupply →
      PairWorldPathNoMintBurn before after →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldSpotValueNum before before ≤
              PairWorldSpotValueNum before after

private theorem closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    before after := by
  intro h_reachable h_positive h_path h_reserve0 h_reserve1
  have h_supply :=
    (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_same_supply_path_no_spot_value_extraction
    before after h_reachable h_positive
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm h_reserve0 h_reserve1



private def pair_closed_world_non_burn_step_never_decreases_k
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
        PairWorldK before ≤ PairWorldK after

private theorem closed_world_non_burn_step_never_decreases_k
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_burn_step_never_decreases_k action before after := by
  exact pairWorldNonBurnStep_never_decreases_k


private def pair_closed_world_no_burn_path_never_decreases_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoBurn before after →
      PairWorldK before ≤ PairWorldK after

private theorem closed_world_no_burn_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_no_burn_path_never_decreases_k before after := by
  exact pairWorldNoBurnPath_never_decreases_k



private def pair_closed_world_no_burn_same_supply_path_no_spot_profit
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathNoBurn before after →
      before.totalSupply = after.totalSupply →
        0 < before.reserve0 →
          0 < before.reserve1 →
            PairWorldNoSpotProfit before after

private theorem closed_world_no_burn_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_no_burn_same_supply_path_no_spot_profit before after := by
  intro h_good h_path h_supply h_reserve0 h_reserve1
  have h_k :
      PairWorldK before ≤ PairWorldK after :=
    pairWorldNoBurnPath_never_decreases_k h_good h_path
  exact closed_world_same_supply_path_no_spot_profit before after
    (pairWorldPath_of_noBurn h_path) h_good h_supply h_reserve0 h_reserve1 h_k


-- tama: discharges=pair_closed_world_skim_removes_surplus
theorem closed_world_skim_removes_surplus
    (before after : PairWorldState) :
  pair_closed_world_skim_removes_surplus before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
    _h_supply, _h_locked⟩
  exact ⟨h_balance0, h_balance1, h_reserve0, h_reserve1⟩


-- tama: discharges=pair_closed_world_skim_removes_exact_surplus_value
theorem closed_world_skim_removes_exact_surplus_value
    (before after : PairWorldState) :
  pair_closed_world_skim_removes_exact_surplus_value before after := by
  intro h_good h_step
  have h_remove := closed_world_skim_removes_surplus before after h_step
  have h_after_value :
      PairWorldBalanceSpotValueNum before after =
        PairWorldSpotValueNum before before := by
    unfold PairWorldBalanceSpotValueNum PairWorldSpotValueNum
    rw [h_remove.1, h_remove.2.1]
  have h_before_decomp :=
    pairWorldBalanceSpotValue_eq_spot_plus_surplus
      (spot := before) (pool := before) h_good
  rw [h_before_decomp, h_after_value]


-- tama: discharges=pair_closed_world_skim_token_balance_value_never_increases_at_spot
theorem closed_world_skim_token_balance_value_never_increases_at_spot
    (spot before after : PairWorldState) :
  pair_closed_world_skim_token_balance_value_never_increases_at_spot
    spot before after := by
  intro h_good h_step
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  have h_remove := closed_world_skim_removes_surplus before after h_step
  unfold PairWorldBalanceSpotValueNum
  rw [h_remove.1, h_remove.2.1]
  exact Nat.add_le_add
    (Nat.mul_le_mul_right spot.reserve1 h_back0)
    (Nat.mul_le_mul_right spot.reserve0 h_back1)

-- tama: discharges=pair_closed_world_skim_preserves_balanced_pool
theorem closed_world_skim_preserves_balanced_pool
    (before after : PairWorldState) :
  pair_closed_world_skim_preserves_balanced_pool before after := by
  intro h_good h_step h_surplus0 h_surplus1
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
  have h_balance0_before : before.balance0 = before.reserve0 := by
    unfold PairWorldSurplus0 at h_surplus0
    omega
  have h_balance1_before : before.balance1 = before.reserve1 := by
    unfold PairWorldSurplus1 at h_surplus1
    omega
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨h_balance0, h_balance1, h_reserve0, h_reserve1,
    h_supply, h_locked⟩
  constructor
  · rw [h_balance0, h_balance0_before]
  constructor
  · rw [h_balance1, h_balance1_before]
  exact ⟨h_reserve0, h_reserve1, h_supply, h_locked⟩



-- tama: discharges=pair_closed_world_sync_sets_reserves_to_balances
theorem closed_world_sync_sets_reserves_to_balances
    (before after : PairWorldState) :
  pair_closed_world_sync_sets_reserves_to_balances before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
    h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  exact ⟨h_reserve0, h_reserve1, h_balance0, h_balance1⟩

-- tama: discharges=pair_closed_world_sync_preserves_token_balances
theorem closed_world_sync_preserves_token_balances
    (before after : PairWorldState) :
  pair_closed_world_sync_preserves_token_balances before after := by
  intro h_step
  have h_sync := closed_world_sync_sets_reserves_to_balances before after h_step
  exact ⟨h_sync.2.2.1, h_sync.2.2.2⟩


-- tama: discharges=pair_closed_world_reserve_write_sets_reserves_to_balances
theorem closed_world_reserve_write_sets_reserves_to_balances
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_reserve_write_sets_reserves_to_balances action before after := by
  intro h_action h_step
  rcases h_action with h_mint | h_burn | h_swap | h_sync
  · rcases h_mint with ⟨amount0, amount1, liquidity, h_action⟩
    subst action
    simp [PairWorldStep, PairWorldMintStep] at h_step
    rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
      _h_before0, _h_before1, h_balance0, h_balance1, h_reserve0,
      h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
    exact ⟨by rw [h_reserve0, h_balance0], by rw [h_reserve1, h_balance1]⟩
  · rcases h_burn with ⟨amount0, amount1, liquidity, h_action⟩
    subst action
    simp [PairWorldStep, PairWorldBurnStep] at h_step
    rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity,
      _h_supply_pos, _h_amount0_le, _h_amount1_le, _h_liq_le,
      _h_locked_le, _h_balance0, _h_balance1, h_reserve0, h_reserve1,
      _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
    exact ⟨h_reserve0, h_reserve1⟩
  · rcases h_swap with ⟨amount0In, amount1In, amount0Out, amount1Out, h_action⟩
    subst action
    simp [PairWorldStep, PairWorldSwapStep] at h_step
    rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_cover0,
      _h_cover1, _h_input, _h_balance0, _h_balance1, h_reserve0,
      h_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked,
      _h_fee0, _h_fee1, _h_k⟩
    exact ⟨h_reserve0, h_reserve1⟩
  · subst action
    have h_sync_step := closed_world_sync_sets_reserves_to_balances before after h_step
    constructor
    · rw [h_sync_step.1, h_sync_step.2.2.1]
    · rw [h_sync_step.2.1, h_sync_step.2.2.2]


private theorem closed_world_sync_preserves_token_balance_value
    (spot before after : PairWorldState) :
  PairWorldStep PairWorldAction.sync before after →
    PairWorldBalanceSpotValueNum spot after =
      PairWorldBalanceSpotValueNum spot before := by
  intro h_step
  have h_sync := closed_world_sync_preserves_token_balances before after h_step
  unfold PairWorldBalanceSpotValueNum
  rw [h_sync.1, h_sync.2]

private theorem closed_world_sync_preserves_balanced_pool
    (before after : PairWorldState) :
  PairWorldGood before →
    PairWorldStep PairWorldAction.sync before after →
      PairWorldSurplus0 before = 0 →
        PairWorldSurplus1 before = 0 →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity := by
  intro h_good h_step h_surplus0 h_surplus1
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  have h_balance0_before : before.balance0 = before.reserve0 := by
    unfold PairWorldSurplus0 at h_surplus0
    omega
  have h_balance1_before : before.balance1 = before.reserve1 := by
    unfold PairWorldSurplus1 at h_surplus1
    omega
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, h_balance0, h_balance1,
    h_reserve0, h_reserve1, h_supply, h_locked⟩
  constructor
  · exact h_balance0
  constructor
  · exact h_balance1
  constructor
  · rw [h_reserve0, h_balance0_before]
  constructor
  · rw [h_reserve1, h_balance1_before]
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
theorem closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
    (spot : PairWorldState) (action : PairWorldAction)
    (before after : PairWorldState) :
  pair_closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
    spot action before after := by
  intro h_action h_good h_step
  rcases h_action with h_skim | h_sync
  · subst action
    exact closed_world_skim_token_balance_value_never_increases_at_spot
      spot before after h_good h_step
  · subst action
    have h_value :=
      closed_world_sync_preserves_token_balance_value spot before after h_step
    rw [h_value]





private theorem pairWorldSkimSyncPath_preserves_balanced_pool
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathSkimSync before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity := by
  intro h_good h_surplus0 h_surplus1 h_path
  induction h_path with
  | refl =>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | skim h_prefix h_step ih =>
      rename_i mid final
      rcases ih with
        ⟨h_balance0_prefix, h_balance1_prefix, h_reserve0_prefix,
          h_reserve1_prefix, h_supply_prefix, h_locked_prefix⟩
      have h_good_prefix : PairWorldGood mid := by
        simpa [PairWorldGood, PairWorldSupplyGood, h_balance0_prefix,
          h_balance1_prefix, h_reserve0_prefix, h_reserve1_prefix,
          h_supply_prefix, h_locked_prefix] using h_good
      have h_surplus0_prefix : PairWorldSurplus0 mid = 0 := by
        simpa [PairWorldSurplus0, h_balance0_prefix, h_reserve0_prefix]
          using h_surplus0
      have h_surplus1_prefix : PairWorldSurplus1 mid = 0 := by
        simpa [PairWorldSurplus1, h_balance1_prefix, h_reserve1_prefix]
          using h_surplus1
      rcases closed_world_skim_preserves_balanced_pool
          mid final h_good_prefix h_step h_surplus0_prefix h_surplus1_prefix with
        ⟨h_balance0_step, h_balance1_step, h_reserve0_step,
          h_reserve1_step, h_supply_step, h_locked_step⟩
      constructor
      · rw [h_balance0_step, h_balance0_prefix]
      constructor
      · rw [h_balance1_step, h_balance1_prefix]
      constructor
      · rw [h_reserve0_step, h_reserve0_prefix]
      constructor
      · rw [h_reserve1_step, h_reserve1_prefix]
      constructor
      · rw [h_supply_step, h_supply_prefix]
      · rw [h_locked_step, h_locked_prefix]
  | sync h_prefix h_step ih =>
      rename_i mid final
      rcases ih with
        ⟨h_balance0_prefix, h_balance1_prefix, h_reserve0_prefix,
          h_reserve1_prefix, h_supply_prefix, h_locked_prefix⟩
      have h_good_prefix : PairWorldGood mid := by
        simpa [PairWorldGood, PairWorldSupplyGood, h_balance0_prefix,
          h_balance1_prefix, h_reserve0_prefix, h_reserve1_prefix,
          h_supply_prefix, h_locked_prefix] using h_good
      have h_surplus0_prefix : PairWorldSurplus0 mid = 0 := by
        simpa [PairWorldSurplus0, h_balance0_prefix, h_reserve0_prefix]
          using h_surplus0
      have h_surplus1_prefix : PairWorldSurplus1 mid = 0 := by
        simpa [PairWorldSurplus1, h_balance1_prefix, h_reserve1_prefix]
          using h_surplus1
      rcases closed_world_sync_preserves_balanced_pool
          mid final h_good_prefix h_step h_surplus0_prefix h_surplus1_prefix with
        ⟨h_balance0_step, h_balance1_step, h_reserve0_step,
          h_reserve1_step, h_supply_step, h_locked_step⟩
      constructor
      · rw [h_balance0_step, h_balance0_prefix]
      constructor
      · rw [h_balance1_step, h_balance1_prefix]
      constructor
      · rw [h_reserve0_step, h_reserve0_prefix]
      constructor
      · rw [h_reserve1_step, h_reserve1_prefix]
      constructor
      · rw [h_supply_step, h_supply_prefix]
      · rw [h_locked_step, h_locked_prefix]

/-- The same no-change claim holds for any finite history made only of `skim`
and `sync`. Starting from a good pool with no excess balances above cached
reserves, repeated cleanup calls preserve token balances, cached reserves, LP
supply, and the permanent liquidity lock exactly. -/
private def pair_closed_world_balanced_skim_sync_path_preserves_pool
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathSkimSync before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity

private theorem closed_world_balanced_skim_sync_path_preserves_pool
    (before after : PairWorldState) :
  pair_closed_world_balanced_skim_sync_path_preserves_pool before after := by
  exact pairWorldSkimSyncPath_preserves_balanced_pool

private theorem pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
    {before after : PairWorldState} :
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity := by
  intro h_good h_surplus0 h_surplus1 h_path
  induction h_path with
  | refl =>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | approve ownerAddr spender amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | transfer fromAddr toAddr amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | transferFrom spender fromAddr toAddr amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | skim h_prefix h_step ih =>
      rename_i mid final
      rcases ih with
        ⟨h_balance0_prefix, h_balance1_prefix, h_reserve0_prefix,
          h_reserve1_prefix, h_supply_prefix, h_locked_prefix⟩
      have h_good_prefix : PairWorldGood mid := by
        simpa [PairWorldGood, PairWorldSupplyGood, h_balance0_prefix,
          h_balance1_prefix, h_reserve0_prefix, h_reserve1_prefix,
          h_supply_prefix, h_locked_prefix] using h_good
      have h_surplus0_prefix : PairWorldSurplus0 mid = 0 := by
        simpa [PairWorldSurplus0, h_balance0_prefix, h_reserve0_prefix]
          using h_surplus0
      have h_surplus1_prefix : PairWorldSurplus1 mid = 0 := by
        simpa [PairWorldSurplus1, h_balance1_prefix, h_reserve1_prefix]
          using h_surplus1
      rcases closed_world_skim_preserves_balanced_pool
          mid final h_good_prefix h_step h_surplus0_prefix h_surplus1_prefix with
        ⟨h_balance0_step, h_balance1_step, h_reserve0_step,
          h_reserve1_step, h_supply_step, h_locked_step⟩
      constructor
      · rw [h_balance0_step, h_balance0_prefix]
      constructor
      · rw [h_balance1_step, h_balance1_prefix]
      constructor
      · rw [h_reserve0_step, h_reserve0_prefix]
      constructor
      · rw [h_reserve1_step, h_reserve1_prefix]
      constructor
      · rw [h_supply_step, h_supply_prefix]
      · rw [h_locked_step, h_locked_prefix]
  | sync h_prefix h_step ih =>
      rename_i mid final
      rcases ih with
        ⟨h_balance0_prefix, h_balance1_prefix, h_reserve0_prefix,
          h_reserve1_prefix, h_supply_prefix, h_locked_prefix⟩
      have h_good_prefix : PairWorldGood mid := by
        simpa [PairWorldGood, PairWorldSupplyGood, h_balance0_prefix,
          h_balance1_prefix, h_reserve0_prefix, h_reserve1_prefix,
          h_supply_prefix, h_locked_prefix] using h_good
      have h_surplus0_prefix : PairWorldSurplus0 mid = 0 := by
        simpa [PairWorldSurplus0, h_balance0_prefix, h_reserve0_prefix]
          using h_surplus0
      have h_surplus1_prefix : PairWorldSurplus1 mid = 0 := by
        simpa [PairWorldSurplus1, h_balance1_prefix, h_reserve1_prefix]
          using h_surplus1
      rcases closed_world_sync_preserves_balanced_pool
          mid final h_good_prefix h_step h_surplus0_prefix h_surplus1_prefix with
        ⟨h_balance0_step, h_balance1_step, h_reserve0_step,
          h_reserve1_step, h_supply_step, h_locked_step⟩
      constructor
      · rw [h_balance0_step, h_balance0_prefix]
      constructor
      · rw [h_balance1_step, h_balance1_prefix]
      constructor
      · rw [h_reserve0_step, h_reserve0_prefix]
      constructor
      · rw [h_reserve1_step, h_reserve1_prefix]
      constructor
      · rw [h_supply_step, h_supply_prefix]
      · rw [h_locked_step, h_locked_prefix]

/-- LP approvals/transfers only move LP-token claims, not pool assets. Combining
those bookkeeping actions with `skim`/`sync` on a pool that has no excess token
balances therefore preserves the pool exactly across any finite history made
only of `approve`, `transfer`, `transferFrom`, `skim`, and `sync`. -/
private def pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          after.balance0 = before.balance0 ∧
          after.balance1 = before.balance1 ∧
          after.reserve0 = before.reserve0 ∧
          after.reserve1 = before.reserve1 ∧
          after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity

private theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool before after := by
  exact pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool

/-- The cached reserve product is unchanged by the same histories. Since token
balances and cached reserves are unchanged, the pool's `reserve0 * reserve1`
value is unchanged too; this lets economic arguments cite the K consequence
directly. -/
private def pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          PairWorldK after = PairWorldK before

private theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k before after := by
  intro h_good h_surplus0 h_surplus1 h_path
  rcases pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
      h_good h_surplus0 h_surplus1 h_path with
    ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  simp [PairWorldK, h_reserve0, h_reserve1]

/-- Clean pools stay clean under LP bookkeeping plus `skim`/`sync`. Those
actions cannot create new excess token balances above cached reserves when none
existed at the start. -/
private def pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          PairWorldSurplus0 after = 0 ∧
          PairWorldSurplus1 after = 0

private theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus
    before after := by
  intro h_good h_surplus0 h_surplus1 h_path
  rcases pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
      h_good h_surplus0 h_surplus1 h_path with
    ⟨h_balance0, h_balance1, h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  constructor
  · simpa [PairWorldSurplus0, h_balance0, h_reserve0] using h_surplus0
  · simpa [PairWorldSurplus1, h_balance1, h_reserve1] using h_surplus1

/-- Economic reading of the no-change theorem above. If a clean balanced pool
only goes through LP approval/transfer bookkeeping plus `skim`/`sync`, the
actual token balances held by the pool have exactly the same spot-priced value
at the end as they had at the start. This is the concise no-extraction
consequence of the stronger state-preservation theorem above. -/
private def pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldSurplus0 before = 0 →
      PairWorldSurplus1 before = 0 →
        PairWorldPathLpBookkeepingSkimSync before after →
          PairWorldBalanceSpotValueNum before after =
            PairWorldBalanceSpotValueNum before before

private theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value
    before after := by
  intro h_good h_surplus0 h_surplus1 h_path
  rcases pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
      h_good h_surplus0 h_surplus1 h_path with
    ⟨h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_supply, _h_locked⟩
  simp [PairWorldBalanceSpotValueNum, h_balance0, h_balance1]

private theorem pairWorldLpBookkeepingSkimSyncPath_token_balance_value_never_increases_at_spot
    {spot before after : PairWorldState} :
  PairWorldGood before →
    PairWorldPathLpBookkeepingSkimSync before after →
      PairWorldGood after ∧
      PairWorldBalanceSpotValueNum spot after ≤
        PairWorldBalanceSpotValueNum spot before := by
  intro h_good h_path
  induction h_path with
  | refl =>
      exact ⟨h_good, le_rfl⟩
  | approve ownerAddr spender amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | transfer fromAddr toAddr amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | transferFrom spender fromAddr toAddr amount h_prefix h_step ih =>
      rename_i mid final
      have h_eq : final = mid := by
        simpa [PairWorldStep] using h_step
      subst final
      exact ih
  | skim h_prefix h_step ih =>
      rename_i mid final
      rcases ih with ⟨h_good_mid, h_value_prefix⟩
      have h_step_value :=
        closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
          spot PairWorldAction.skim mid final (Or.inl rfl) h_good_mid h_step
      exact ⟨pairWorldStep_preserves_good h_good_mid h_step,
        Nat.le_trans h_step_value h_value_prefix⟩
  | sync h_prefix h_step ih =>
      rename_i mid final
      rcases ih with ⟨h_good_mid, h_value_prefix⟩
      have h_step_value :=
        closed_world_skim_or_sync_token_balance_value_never_increases_at_spot
          spot PairWorldAction.sync mid final (Or.inr rfl) h_good_mid h_step
      exact ⟨pairWorldStep_preserves_good h_good_mid h_step,
        Nat.le_trans h_step_value h_value_prefix⟩

/-- Without the zero-surplus assumption, LP bookkeeping plus `skim`/`sync` may
remove donated excess via skim, but it still cannot increase the pair's actual
token-balance value at the starting spot price. -/
private def pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    (before after : PairWorldState) : Prop :=
  PairWorldGood before →
    PairWorldPathLpBookkeepingSkimSync before after →
      PairWorldBalanceSpotValueNum before after ≤
        PairWorldBalanceSpotValueNum before before

private theorem closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    (before after : PairWorldState) :
  pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    before after := by
  intro h_good h_path
  exact
    (pairWorldLpBookkeepingSkimSyncPath_token_balance_value_never_increases_at_spot
      (spot := before) h_good h_path).2


end TamaUniV2.Proof.UniswapV2PairProof
