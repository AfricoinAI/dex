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

private def pairLockedState (s : ContractState) : ContractState :=
  { s with «storage» := fun slotIdx => if slotIdx = 11 then 0 else s.storage slotIdx }

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

-- tama: discharges=pair_decimals_spec
theorem decimals_meets_spec (s : ContractState) :
  pair_decimals_spec ((decimals).run s).fst := by
  rfl

-- tama: discharges=pair_decimals_run_success_frames_state
theorem decimals_run_success_frames_state (s : ContractState) :
  pair_decimals_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_totalSupply_spec
theorem totalSupply_meets_spec (s : ContractState) :
  pair_totalSupply_spec ((totalSupply).run s).fst s := by
  rfl

-- tama: discharges=pair_totalSupply_run_success_frames_state
theorem totalSupply_run_success_frames_state (s : ContractState) :
  pair_totalSupply_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_balanceOf_spec
theorem balanceOf_meets_spec (account : Address) (s : ContractState) :
  pair_balanceOf_spec account ((balanceOf account).run s).fst s := by
  rfl

-- tama: discharges=pair_balanceOf_run_success_frames_state
theorem balanceOf_run_success_frames_state (account : Address) (s : ContractState) :
  pair_balanceOf_run_success_frames_state account s := by
  rfl

-- tama: discharges=pair_allowance_spec
theorem allowance_meets_spec (owner spender : Address) (s : ContractState) :
  pair_allowance_spec owner spender ((allowance owner spender).run s).fst s := by
  rfl

-- tama: discharges=pair_allowance_run_success_frames_state
theorem allowance_run_success_frames_state
    (owner spender : Address) (s : ContractState) :
  pair_allowance_run_success_frames_state owner spender s := by
  rfl

-- tama: discharges=pair_factory_spec
theorem factory_meets_spec (s : ContractState) :
  pair_factory_spec ((factory).run s).fst s := by
  simp [pair_factory_spec, factory, Verity.getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_factory_run_success_frames_state
theorem factory_run_success_frames_state (s : ContractState) :
  pair_factory_run_success_frames_state s := by
  simp [pair_factory_run_success_frames_state, factory, Verity.getStorageAddr,
    Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_token0_spec
theorem token0_meets_spec (s : ContractState) :
  pair_token0_spec ((token0).run s).fst s := by
  simp [pair_token0_spec, token0, Verity.getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_token0_run_success_frames_state
theorem token0_run_success_frames_state (s : ContractState) :
  pair_token0_run_success_frames_state s := by
  simp [pair_token0_run_success_frames_state, token0, Verity.getStorageAddr,
    Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_token1_spec
theorem token1_meets_spec (s : ContractState) :
  pair_token1_spec ((token1).run s).fst s := by
  simp [pair_token1_spec, token1, Verity.getStorageAddr, Contract.run,
    ContractResult.fst, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_token1_run_success_frames_state
theorem token1_run_success_frames_state (s : ContractState) :
  pair_token1_run_success_frames_state s := by
  simp [pair_token1_run_success_frames_state, token1, Verity.getStorageAddr,
    Contract.run, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_minimumLiquidity_spec
theorem minimumLiquidity_meets_spec (s : ContractState) :
  pair_minimumLiquidity_spec ((MINIMUM_LIQUIDITY).run s).fst := by
  rfl

-- tama: discharges=pair_minimumLiquidity_run_success_frames_state
theorem minimumLiquidity_run_success_frames_state (s : ContractState) :
  pair_minimumLiquidity_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_getReserves_spec
theorem getReserves_meets_spec (s : ContractState) :
  pair_getReserves_spec ((getReserves).run s).fst s := by
  simp [pair_getReserves_spec, getReserves, reserve0Slot, reserve1Slot,
    blockTimestampLastSlot, getStorage, Contract.run, ContractResult.fst,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_getReserves_run_success_frames_state
theorem getReserves_run_success_frames_state (s : ContractState) :
  pair_getReserves_run_success_frames_state s := by
  simp [pair_getReserves_run_success_frames_state, getReserves, reserve0Slot,
    reserve1Slot, blockTimestampLastSlot, getStorage, Contract.run,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

-- tama: discharges=pair_price0CumulativeLast_spec
theorem price0CumulativeLast_meets_spec (s : ContractState) :
  pair_price0CumulativeLast_spec ((price0CumulativeLast).run s).fst s := by
  rfl

-- tama: discharges=pair_price0CumulativeLast_run_success_frames_state
theorem price0CumulativeLast_run_success_frames_state (s : ContractState) :
  pair_price0CumulativeLast_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_price1CumulativeLast_spec
theorem price1CumulativeLast_meets_spec (s : ContractState) :
  pair_price1CumulativeLast_spec ((price1CumulativeLast).run s).fst s := by
  rfl

-- tama: discharges=pair_price1CumulativeLast_run_success_frames_state
theorem price1CumulativeLast_run_success_frames_state (s : ContractState) :
  pair_price1CumulativeLast_run_success_frames_state s := by
  rfl

-- tama: discharges=pair_kLast_spec
theorem kLast_meets_spec (s : ContractState) :
  pair_kLast_spec ((kLast).run s).fst := by
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

-- tama: discharges=pair_initialize_run_success_sets_tokens
theorem initialize_run_success_sets_tokens
    (token0Value token1Value : Address) (s : ContractState) :
  pair_initialize_run_success_sets_tokens token0Value token1Value s := by
  simpa [pair_initialize_run_success_sets_tokens, pair_initialize_sets_tokens]
    using initialize_sets_tokens token0Value token1Value s

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
  simpa [pair_burn_run_revert_locked, pair_burn_reverts_when_locked]
    using burn_reverts_when_locked toAddr s

-- tama: discharges=pair_swap_run_revert_locked
theorem swap_run_revert_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_swap_run_revert_locked amount0Out amount1Out toAddr data s := by
  simpa [pair_swap_run_revert_locked, pair_swap_reverts_when_locked]
    using swap_reverts_when_locked amount0Out amount1Out toAddr data s

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

-- tama: discharges=pair_mint_success_run_implies_lock_open
theorem mint_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) :
  pair_mint_success_run_implies_lock_open toAddr s result := by
  intro h_run h_success
  rcases h_success with ⟨liquidity, h_success⟩
  by_contra h_locked
  have h_revert := mint_run_revert_locked toAddr s (uint256_bne_true_of_ne h_locked)
  rw [h_run] at h_success
  rw [h_revert] at h_success
  cases h_success

-- tama: discharges=pair_burn_success_run_implies_lock_open
theorem burn_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) :
  pair_burn_success_run_implies_lock_open toAddr s result := by
  intro h_run h_success
  rcases h_success with ⟨amounts, h_success⟩
  by_contra h_locked
  have h_revert := burn_run_revert_locked toAddr s (uint256_bne_true_of_ne h_locked)
  rw [h_run] at h_success
  rw [h_revert] at h_success
  cases h_success

-- tama: discharges=pair_swap_success_run_implies_lock_open
theorem swap_success_run_implies_lock_open
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (result : ContractResult Unit) :
  pair_swap_success_run_implies_lock_open
    amount0Out amount1Out toAddr data s result := by
  intro h_run h_success
  by_contra h_locked
  have h_revert :=
    swap_run_revert_locked amount0Out amount1Out toAddr data s
      (uint256_bne_true_of_ne h_locked)
  rw [h_run] at h_success
  rw [h_revert] at h_success
  cases h_success

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

-- tama: discharges=pair_skim_success_run_implies_lock_open
theorem skim_success_run_implies_lock_open
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_implies_lock_open toAddr s result := by
  intro h_run h_success
  by_contra h_locked
  have h_revert := skim_run_revert_locked toAddr s (uint256_bne_true_of_ne h_locked)
  rw [h_run] at h_success
  rw [h_revert] at h_success
  cases h_success

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

-- tama: discharges=pair_skim_success_run_refines_closed_world_from_run
theorem skim_success_run_refines_closed_world_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_refines_closed_world_from_run toAddr s result := by
  intro h_run h_success
  have h_unlocked := skim_success_run_implies_lock_open toAddr s result h_run h_success
  rcases skim_success_run_implies_balances_back_reserves
      toAddr s result h_run h_success with
    ⟨h_balance0, h_balance1⟩
  have h_step := skim_run_success_refines_closed_world toAddr s
    h_unlocked h_balance0 h_balance1
  rw [← h_run, h_success] at h_step
  exact h_step

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

-- tama: discharges=pair_mint_success_run_implies_balances_fit_uint112
theorem mint_success_run_implies_balances_fit_uint112
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) :
  pair_mint_success_run_implies_balances_fit_uint112 toAddr s result := by
  intro h_run h_success
  have h_unlocked :=
    mint_success_run_implies_lock_open toAddr s result h_run h_success
  constructor
  · by_contra h_not_bound
    have h_not_bound_val :
        ¬ (observedBalance0 s).val ≤ maxUint112.val := by
      simpa [Verity.Core.Uint256.le_def] using h_not_bound
    have h_overflow : observedBalance0 s > maxUint112 := by
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_not_bound_val
    have h_revert := mint_run_revert_balance0_overflow toAddr s h_unlocked h_overflow
    rcases h_success with ⟨liquidity, h_success⟩
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success
  · by_contra h_not_bound
    have h_not_bound_val :
        ¬ (observedBalance1 s).val ≤ maxUint112.val := by
      simpa [Verity.Core.Uint256.le_def] using h_not_bound
    have h_overflow : observedBalance1 s > maxUint112 := by
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_not_bound_val
    have h_revert := mint_run_revert_balance1_overflow toAddr s h_unlocked h_overflow
    rcases h_success with ⟨liquidity, h_success⟩
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success

-- tama: discharges=pair_sync_success_run_implies_lock_open
theorem sync_success_run_implies_lock_open
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_implies_lock_open s result := by
  intro h_run h_success
  by_contra h_locked
  have h_locked_bool :
      (s.storage unlockedSlot.slot != (1 : Uint256)) = true := by
    exact uint256_bne_true_of_ne h_locked
  have h_revert := sync_run_revert_locked s h_locked_bool
  rw [h_run] at h_success
  rw [h_revert] at h_success
  cases h_success

-- tama: discharges=pair_sync_success_run_implies_balances_fit_uint112
theorem sync_success_run_implies_balances_fit_uint112
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_implies_balances_fit_uint112 s result := by
  intro h_run h_success
  have h_unlocked := sync_success_run_implies_lock_open s result h_run h_success
  constructor
  · by_contra h_not_bound
    have h_not_bound_val :
        ¬ (observedBalance0 s).val ≤ maxUint112.val := by
      simpa [Verity.Core.Uint256.le_def] using h_not_bound
    have h_overflow : observedBalance0 s > maxUint112 := by
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_not_bound_val
    have h_revert := sync_run_revert_balance0_overflow s h_unlocked h_overflow
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success
  · by_contra h_not_bound
    have h_not_bound_val :
        ¬ (observedBalance1 s).val ≤ maxUint112.val := by
      simpa [Verity.Core.Uint256.le_def] using h_not_bound
    have h_overflow : observedBalance1 s > maxUint112 := by
      simpa [Verity.Core.Uint256.lt_def] using Nat.lt_of_not_ge h_not_bound_val
    have h_revert := sync_run_revert_balance1_overflow s h_unlocked h_overflow
    rw [h_run] at h_success
    rw [h_revert] at h_success
    cases h_success

-- tama: discharges=pair_sync_success_run_refines_closed_world_from_run
theorem sync_success_run_refines_closed_world_from_run
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_refines_closed_world_from_run s result := by
  intro h_run h_success
  rcases sync_success_run_implies_balances_fit_uint112
      s result h_run h_success with
    ⟨h_bound0, h_bound1⟩
  exact sync_expected_refines_closed_world s h_bound0 h_bound1

-- tama: discharges=pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives
theorem reserve_update_oracle_same_timestamp_keeps_price_cumulatives
    (s : ContractState) :
  pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives s := by
  intro h_same_timestamp
  have h_same_raw :
      Verity.EVM.Uint256.mod s.blockTimestamp uint32Modulus =
        s.storage 5 := by
    simpa [timestamp32, blockTimestampLastSlot] using h_same_timestamp
  have h_same_num :
      Verity.EVM.Uint256.mod s.blockTimestamp 4294967296 =
        s.storage 5 := by
    simpa [uint32Modulus] using h_same_raw
  have h_same_bne_false :
      (timestamp32 s != s.storage blockTimestampLastSlot.slot) = false := by
    simp [timestamp32, blockTimestampLastSlot, uint32Modulus, h_same_num, BEq.beq]
  simp [pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives,
    oraclePrice0CumulativeAfterSync, oraclePrice1CumulativeAfterSync,
    oraclePrice0CumulativeAfterElapsed, oraclePrice1CumulativeAfterElapsed,
    oraclePrice0Increment, oraclePrice1Increment, oraclePrice0, oraclePrice1,
    oracleElapsed, timestamp32, blockTimestampLastSlot,
    reserve0Slot, reserve1Slot, price0CumulativeLastSlot,
    price1CumulativeLastSlot, uint32Modulus, q112,
    h_same_raw, h_same_num, h_same_bne_false]

-- tama: discharges=pair_sync_oracle_same_timestamp_keeps_price_cumulatives
theorem sync_oracle_same_timestamp_keeps_price_cumulatives
    (s : ContractState) :
  pair_sync_oracle_same_timestamp_keeps_price_cumulatives s := by
  exact reserve_update_oracle_same_timestamp_keeps_price_cumulatives s

-- tama: discharges=pair_reserve_update_oracle_elapsed_updates_price_cumulatives
theorem reserve_update_oracle_elapsed_updates_price_cumulatives
    (s : ContractState) :
  pair_reserve_update_oracle_elapsed_updates_price_cumulatives s := by
  intro h_time_changed h_elapsed h_reserve0 h_reserve1
  have h_elapsed_branch :
      oracleElapsed s > 0 ∧
        s.storage reserve0Slot.slot > 0 ∧
        s.storage reserve1Slot.slot > 0 :=
    ⟨h_elapsed, h_reserve0, h_reserve1⟩
  have h_time_changed_raw :
      (Verity.EVM.Uint256.mod s.blockTimestamp uint32Modulus !=
        s.storage 5) = true := by
    simpa [timestamp32, blockTimestampLastSlot] using h_time_changed
  have h_time_changed_num :
      (Verity.EVM.Uint256.mod s.blockTimestamp 4294967296 !=
        s.storage 5) = true := by
    simpa [uint32Modulus] using h_time_changed_raw
  have h_time_neq_num :
      ¬ Verity.EVM.Uint256.mod s.blockTimestamp 4294967296 =
        s.storage 5 := by
    intro h_eq
    simp [h_eq] at h_time_changed_num
  have h_elapsed_branch_raw :
      Verity.EVM.Uint256.mod
          (Verity.EVM.Uint256.sub
            (Verity.EVM.Uint256.add
              (Verity.EVM.Uint256.mod s.blockTimestamp uint32Modulus)
              uint32Modulus)
            (s.storage 5))
          uint32Modulus > 0 ∧
        s.storage 3 > 0 ∧
        s.storage 4 > 0 := by
    exact ⟨by simpa [oracleElapsed, timestamp32, blockTimestampLastSlot] using h_elapsed,
      by simpa [reserve0Slot] using h_reserve0,
      by simpa [reserve1Slot] using h_reserve1⟩
  have h_elapsed_num :
      0 <
        (Verity.EVM.Uint256.mod
          (Verity.EVM.Uint256.sub
            (Verity.EVM.Uint256.add
              (Verity.EVM.Uint256.mod s.blockTimestamp 4294967296)
              4294967296)
            (s.storage 5))
          4294967296).val := by
    simpa [oracleElapsed, timestamp32, blockTimestampLastSlot,
      uint32Modulus, Verity.Core.Uint256.lt_def] using h_elapsed
  simp [pair_reserve_update_oracle_elapsed_updates_price_cumulatives,
    oraclePrice0CumulativeAfterSync, oraclePrice1CumulativeAfterSync,
    oraclePrice0CumulativeAfterElapsed, oraclePrice1CumulativeAfterElapsed,
    oraclePrice0Increment, oraclePrice1Increment, oraclePrice0, oraclePrice1,
    oracleElapsed, timestamp32, blockTimestampLastSlot,
    reserve0Slot, reserve1Slot, price0CumulativeLastSlot,
    price1CumulativeLastSlot, uint32Modulus, q112,
    h_time_changed, h_time_changed_raw, h_time_changed_num, h_time_neq_num,
    h_elapsed_branch, h_elapsed_branch_raw, h_elapsed_num]

-- tama: discharges=pair_sync_oracle_elapsed_updates_price_cumulatives
theorem sync_oracle_elapsed_updates_price_cumulatives
    (s : ContractState) :
  pair_sync_oracle_elapsed_updates_price_cumulatives s := by
  exact reserve_update_oracle_elapsed_updates_price_cumulatives s

-- tama: discharges=pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives
theorem reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives
    (s : ContractState) :
  pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives s := by
  intro h_time_changed h_inactive
  simp [pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives,
    oraclePrice0CumulativeAfterSync, oraclePrice1CumulativeAfterSync,
    oraclePrice0CumulativeAfterElapsed, oraclePrice1CumulativeAfterElapsed,
    oraclePrice0Increment, oraclePrice1Increment, oraclePrice0, oraclePrice1,
    oracleElapsed, timestamp32, blockTimestampLastSlot,
    reserve0Slot, reserve1Slot, price0CumulativeLastSlot,
    price1CumulativeLastSlot, uint32Modulus, q112,
    h_time_changed]
  constructor
  · intro _ h_elapsed_raw h_reserve0_raw h_reserve1_raw
    exfalso
    apply h_inactive
    exact ⟨by
        simpa [oracleElapsed, timestamp32, blockTimestampLastSlot,
          uint32Modulus, Verity.Core.Uint256.lt_def] using h_elapsed_raw,
      by
        simpa [reserve0Slot, Verity.Core.Uint256.lt_def] using h_reserve0_raw,
      by
        simpa [reserve1Slot, Verity.Core.Uint256.lt_def] using h_reserve1_raw⟩
  · intro _ h_elapsed_raw h_reserve0_raw h_reserve1_raw
    exfalso
    apply h_inactive
    exact ⟨by
        simpa [oracleElapsed, timestamp32, blockTimestampLastSlot,
          uint32Modulus, Verity.Core.Uint256.lt_def] using h_elapsed_raw,
      by
        simpa [reserve0Slot, Verity.Core.Uint256.lt_def] using h_reserve0_raw,
      by
        simpa [reserve1Slot, Verity.Core.Uint256.lt_def] using h_reserve1_raw⟩

-- tama: discharges=pair_sync_oracle_inactive_elapsed_keeps_price_cumulatives
theorem sync_oracle_inactive_elapsed_keeps_price_cumulatives
    (s : ContractState) :
  pair_sync_oracle_inactive_elapsed_keeps_price_cumulatives s := by
  exact reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives s

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

-- tama: discharges=pair_mint_first_success_run_refines_closed_world_from_run
theorem mint_first_success_run_refines_closed_world_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_refines_closed_world_from_run toAddr s
    ((mint toAddr).run s) := by
  dsimp [pair_mint_first_success_run_refines_closed_world_from_run]
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
  exact mint_first_expected_refines_closed_world toAddr s
    h_unlocked h_supply_zero h_bound0 h_bound1 h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root

-- tama: discharges=pair_mint_subsequent_expected_refines_closed_world
theorem mint_subsequent_expected_refines_closed_world
    (s : ContractState) (liquidity : Uint256) :
  pair_mint_subsequent_expected_refines_closed_world s liquidity := by
  dsimp [pair_mint_subsequent_expected_refines_closed_world]
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

-- tama: discharges=pair_mint_subsequent_success_run_refines_closed_world
theorem mint_subsequent_success_run_refines_closed_world
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_refines_closed_world
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run _h_success
  exact mint_subsequent_expected_refines_closed_world s liquidity

-- tama: discharges=pair_mint_subsequent_success_run_refines_closed_world_from_run
theorem mint_subsequent_success_run_refines_closed_world_from_run
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_refines_closed_world_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  dsimp [pair_mint_subsequent_success_run_refines_closed_world_from_run]
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
  exact mint_subsequent_expected_refines_closed_world s liquidity
    h_supply_pos h_reserve0_pos h_reserve1_pos h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1

-- tama: discharges=pair_burn_expected_refines_closed_world
theorem burn_expected_refines_closed_world
    (s : ContractState) :
  pair_burn_expected_refines_closed_world s := by
  dsimp [pair_burn_expected_refines_closed_world]
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

-- tama: discharges=pair_burn_success_run_refines_closed_world
theorem burn_success_run_refines_closed_world
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_refines_closed_world toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success
  exact burn_expected_refines_closed_world s

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

-- tama: discharges=pair_swap_expected_refines_closed_world
theorem swap_expected_refines_closed_world
    (amount0Out amount1Out balance0Now balance1Now : Uint256)
    (s : ContractState) :
  pair_swap_expected_refines_closed_world
    amount0Out amount1Out balance0Now balance1Now s := by
  dsimp [pair_swap_expected_refines_closed_world]
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

-- tama: discharges=pair_swap_success_run_refines_closed_world
theorem swap_success_run_refines_closed_world
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_refines_closed_world
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run _h_success
  exact swap_expected_refines_closed_world
    amount0Out amount1Out balance0Now balance1Now s

-- tama: discharges=pair_swap_success_run_refines_closed_world_from_run
theorem swap_success_run_refines_closed_world_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_refines_closed_world_from_run
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
  exact swap_expected_refines_closed_world
    amount0Out amount1Out balance0Now balance1Now s h_output
    h_liq0 h_liq1 h_input h_balance0 h_balance1 h_bound0 h_bound1
    h_fee0 h_fee1 h_adjusted_k

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

-- tama: discharges=pair_closed_world_positive_supply_path_remains_positive
theorem closed_world_positive_supply_path_remains_positive
    (before after : PairWorldState) :
  pair_closed_world_positive_supply_path_remains_positive before after := by
  intro h_good h_positive h_path
  exact pairWorldPath_positive_supply_preserved h_good h_positive h_path

-- tama: discharges=pair_closed_world_reachable_positive_supply_path_remains_positive
theorem closed_world_reachable_positive_supply_path_remains_positive
    (before after : PairWorldState) :
  pair_closed_world_reachable_positive_supply_path_remains_positive before after := by
  intro h_reachable h_positive h_path
  exact pairWorldPath_positive_supply_preserved
    (pairWorldReachable_good before h_reachable) h_positive h_path

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

-- tama: discharges=pair_closed_world_reachable_path_minimum_liquidity_lock
theorem closed_world_reachable_path_minimum_liquidity_lock
    (before after : PairWorldState) :
  pair_closed_world_reachable_path_minimum_liquidity_lock before after := by
  intro h_reachable h_path
  exact (pairWorldPath_preserves_good
    (pairWorldReachable_good before h_reachable) h_path).2.2.2.2

-- tama: discharges=pair_closed_world_step_locked_liquidity_never_decreases
theorem closed_world_step_locked_liquidity_never_decreases
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_step_locked_liquidity_never_decreases action before after := by
  exact pairWorldStep_locked_liquidity_never_decreases

-- tama: discharges=pair_closed_world_path_locked_liquidity_never_decreases
theorem closed_world_path_locked_liquidity_never_decreases
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
        _h_adjusted_k⟩
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

-- tama: discharges=pair_closed_world_reserve_changes_only_on_reserve_update_actions
theorem closed_world_reserve_changes_only_on_reserve_update_actions
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_reserve_changes_only_on_reserve_update_actions
    action before after := by
  intro h_step h_change
  cases action with
  | approve ownerAddr spender amount =>
      simp [PairWorldStep] at h_step
      subst after
      rcases h_change with h_change | h_change
      · exact False.elim (h_change rfl)
      · exact False.elim (h_change rfl)
  | transfer fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rcases h_change with h_change | h_change
      · exact False.elim (h_change rfl)
      · exact False.elim (h_change rfl)
  | transferFrom spender fromAddr toAddr amount =>
      simp [PairWorldStep] at h_step
      subst after
      rcases h_change with h_change | h_change
      · exact False.elim (h_change rfl)
      · exact False.elim (h_change rfl)
  | donate amount0 amount1 =>
      simp [PairWorldStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      rcases h_change with h_change | h_change
      · exact False.elim (h_change h_reserve0)
      · exact False.elim (h_change h_reserve1)
  | mint amount0 amount1 liquidity =>
      exact Or.inl ⟨amount0, amount1, liquidity, rfl⟩
  | burn amount0 amount1 liquidity =>
      exact Or.inr (Or.inl ⟨amount0, amount1, liquidity, rfl⟩)
  | swap amount0In amount1In amount0Out amount1Out =>
      exact Or.inr (Or.inr (Or.inl
        ⟨amount0In, amount1In, amount0Out, amount1Out, rfl⟩))
  | skim =>
      simp [PairWorldStep, PairWorldSkimStep] at h_step
      rcases h_step with ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1,
        _h_supply, _h_locked⟩
      rcases h_change with h_change | h_change
      · exact False.elim (h_change h_reserve0)
      · exact False.elim (h_change h_reserve1)
  | sync =>
      exact Or.inr (Or.inr (Or.inr rfl))

-- tama: discharges=pair_closed_world_no_reserve_update_path_preserves_reserves
theorem closed_world_no_reserve_update_path_preserves_reserves
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

-- tama: discharges=pair_closed_world_no_reserve_update_path_preserves_k_and_spot_value
theorem closed_world_no_reserve_update_path_preserves_k_and_spot_value
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

-- tama: discharges=pair_closed_world_non_liquidity_step_preserves_supply
theorem closed_world_non_liquidity_step_preserves_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_liquidity_step_preserves_supply action before after := by
  intro h_step h_not_mint h_not_burn
  exact pairWorldNoMintBurnPath_preserves_supply
    (PairWorldPathNoMintBurn.step action
      (PairWorldPathNoMintBurn.refl before)
      h_step h_not_mint h_not_burn)

-- tama: discharges=pair_closed_world_no_mint_burn_path_preserves_supply
theorem closed_world_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) :
  pair_closed_world_no_mint_burn_path_preserves_supply before after := by
  exact pairWorldNoMintBurnPath_preserves_supply

-- tama: discharges=pair_closed_world_reachable_no_mint_burn_path_preserves_supply
theorem closed_world_reachable_no_mint_burn_path_preserves_supply
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_mint_burn_path_preserves_supply before after := by
  intro _h_reachable h_path
  exact pairWorldNoMintBurnPath_preserves_supply h_path

-- tama: discharges=pair_closed_world_non_burn_step_never_decreases_supply
theorem closed_world_non_burn_step_never_decreases_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_burn_step_never_decreases_supply action before after := by
  exact pairWorldNonBurnStep_never_decreases_supply

-- tama: discharges=pair_closed_world_no_burn_path_never_decreases_supply
theorem closed_world_no_burn_path_never_decreases_supply
    (before after : PairWorldState) :
  pair_closed_world_no_burn_path_never_decreases_supply before after := by
  exact pairWorldNoBurnPath_never_decreases_supply

-- tama: discharges=pair_closed_world_reachable_no_burn_path_never_decreases_supply
theorem closed_world_reachable_no_burn_path_never_decreases_supply
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_burn_path_never_decreases_supply before after := by
  intro _h_reachable h_path
  exact pairWorldNoBurnPath_never_decreases_supply h_path

-- tama: discharges=pair_closed_world_non_mint_step_never_increases_supply
theorem closed_world_non_mint_step_never_increases_supply
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_mint_step_never_increases_supply action before after := by
  exact pairWorldNonMintStep_never_increases_supply

-- tama: discharges=pair_closed_world_no_mint_path_never_increases_supply
theorem closed_world_no_mint_path_never_increases_supply
    (before after : PairWorldState) :
  pair_closed_world_no_mint_path_never_increases_supply before after := by
  exact pairWorldNoMintPath_never_increases_supply

-- tama: discharges=pair_closed_world_reachable_no_mint_path_never_increases_supply
theorem closed_world_reachable_no_mint_path_never_increases_supply
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_mint_path_never_increases_supply before after := by
  intro _h_reachable h_path
  exact pairWorldNoMintPath_never_increases_supply h_path

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

-- tama: discharges=pair_closed_world_share_bookkeeping_path_preserves_pool_state
theorem closed_world_share_bookkeeping_path_preserves_pool_state
    (before after : PairWorldState) :
  pair_closed_world_share_bookkeeping_path_preserves_pool_state before after := by
  exact pairWorldShareBookkeepingPath_preserves_pool_state

-- tama: discharges=pair_closed_world_share_bookkeeping_path_preserves_k_and_value
theorem closed_world_share_bookkeeping_path_preserves_k_and_value
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

-- tama: discharges=pair_mint_first_success_run_strictly_increases_supply_from_run
theorem mint_first_success_run_strictly_increases_supply_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_strictly_increases_supply_from_run
    toAddr s ((mint toAddr).run s) := by
  intro _h_run h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_step :=
    mint_first_success_run_refines_closed_world_from_run toAddr s
      rfl h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  exact closed_world_mint_strictly_increases_supply
    (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val
    (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s)
    h_step

-- tama: discharges=pair_mint_first_success_run_locks_minimum_liquidity_from_run
theorem mint_first_success_run_locks_minimum_liquidity_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_locks_minimum_liquidity_from_run
    toAddr s ((mint toAddr).run s) := by
  intro _h_run h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_step :=
    mint_first_success_run_refines_closed_world_from_run toAddr s
      rfl h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  have h_first : (pairWorldBeforeMintRun s).totalSupply = 0 := by
    have h_supply_zero_val : (s.storage totalSupplySlot.slot).val = 0 := by
      simpa using congrArg (fun x : Uint256 => x.val) h_supply_zero
    simpa [pairWorldBeforeMintRun] using h_supply_zero_val
  exact closed_world_first_mint_locks_minimum_liquidity
    (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val
    (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s)
    h_step h_first

-- tama: discharges=pair_mint_first_success_run_keeps_locked_share_from_run
theorem mint_first_success_run_keeps_locked_share_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_keeps_locked_share_from_run
    toAddr s ((mint toAddr).run s) := by
  intro _h_run h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_step :=
    mint_first_success_run_refines_closed_world_from_run toAddr s
      rfl h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  have h_first : (pairWorldBeforeMintRun s).totalSupply = 0 := by
    have h_supply_zero_val : (s.storage totalSupplySlot.slot).val = 0 := by
      simpa using congrArg (fun x : Uint256 => x.val) h_supply_zero
    simpa [pairWorldBeforeMintRun] using h_supply_zero_val
  have h_locked_share :=
    closed_world_first_mint_keeps_locked_share
      (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val
      (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s)
      h_step h_first
  have h_locked :=
    closed_world_first_mint_locks_minimum_liquidity
      (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val
      (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s)
      h_step h_first
  exact ⟨h_locked.1, h_locked_share⟩

-- tama: discharges=pair_mint_subsequent_success_run_strictly_increases_supply_from_run
theorem mint_subsequent_success_run_strictly_increases_supply_from_run
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_strictly_increases_supply_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_step :=
    mint_subsequent_success_run_refines_closed_world_from_run
      toAddr s liquidity rfl h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity
      h_ratio0 h_ratio1
  exact closed_world_mint_strictly_increases_supply
    (mintAmount0 s).val (mintAmount1 s).val liquidity.val
    (pairWorldBeforeMintRun s) (pairWorldAfterSubsequentMintRun liquidity s)
    h_step

-- tama: discharges=pair_mint_subsequent_success_run_preserves_locked_liquidity_from_run
theorem mint_subsequent_success_run_preserves_locked_liquidity_from_run
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_preserves_locked_liquidity_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_step :=
    mint_subsequent_success_run_refines_closed_world_from_run
      toAddr s liquidity rfl h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity
      h_ratio0 h_ratio1
  have h_before_supply_pos : 0 < (pairWorldBeforeMintRun s).totalSupply := by
    simpa [pairWorldBeforeMintRun] using h_supply_pos
  have h_subsequent : (pairWorldBeforeMintRun s).totalSupply ≠ 0 := by
    omega
  exact closed_world_subsequent_mint_preserves_locked_liquidity
    (mintAmount0 s).val (mintAmount1 s).val liquidity.val
    (pairWorldBeforeMintRun s) (pairWorldAfterSubsequentMintRun liquidity s)
    h_step h_subsequent

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

-- tama: discharges=pair_burn_success_run_reduces_supply_by_liquidity_from_run
theorem burn_success_run_reduces_supply_by_liquidity_from_run
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_reduces_supply_by_liquidity_from_run
    toAddr s ((burn toAddr).run s) := by
  intro _h_run h_success h_liquidity_pos h_supply_pos h_liquidity_le
    h_locked_remaining h_amount0 h_amount1 h_amount0_le h_amount1_le
    h_bound0 h_bound1 h_ratio0 h_ratio1
  have h_step :=
    burn_success_run_refines_closed_world toAddr s
      rfl h_success h_liquidity_pos h_supply_pos h_liquidity_le
      h_locked_remaining h_amount0 h_amount1 h_amount0_le h_amount1_le
      h_bound0 h_bound1 h_ratio0 h_ratio1
  exact closed_world_burn_reduces_supply_by_liquidity
    (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val
    (pairWorldFromConcreteState s) (pairWorldAfterBurnRun s)
    h_step

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

-- tama: discharges=pair_burn_success_run_cannot_redeem_locked_liquidity_from_run
theorem burn_success_run_cannot_redeem_locked_liquidity_from_run
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_cannot_redeem_locked_liquidity_from_run
    toAddr s ((burn toAddr).run s) := by
  intro _h_run h_success h_liquidity_pos h_supply_pos h_liquidity_le
    h_locked_remaining h_amount0 h_amount1 h_amount0_le h_amount1_le
    h_bound0 h_bound1 h_ratio0 h_ratio1
  have h_step :=
    burn_success_run_refines_closed_world toAddr s
      rfl h_success h_liquidity_pos h_supply_pos h_liquidity_le
      h_locked_remaining h_amount0 h_amount1 h_amount0_le h_amount1_le
      h_bound0 h_bound1 h_ratio0 h_ratio1
  exact closed_world_burn_cannot_redeem_locked_liquidity
    (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val
    (pairWorldFromConcreteState s) (pairWorldAfterBurnRun s)
    h_step

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

-- tama: discharges=pair_burn_success_run_preserves_positive_balances_from_run
theorem burn_success_run_preserves_positive_balances_from_run
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_preserves_positive_balances_from_run
    toAddr s ((burn toAddr).run s) := by
  intro _h_run h_success h_good h_before_balance0 h_before_balance1
    h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
    h_amount0 h_amount1 h_amount0_le h_amount1_le
    h_bound0 h_bound1 h_ratio0 h_ratio1
  have h_step :=
    burn_success_run_refines_closed_world toAddr s
      rfl h_success h_liquidity_pos h_supply_pos h_liquidity_le
      h_locked_remaining h_amount0 h_amount1 h_amount0_le h_amount1_le
      h_bound0 h_bound1 h_ratio0 h_ratio1
  exact closed_world_burn_preserves_positive_balances
    (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val
    (pairWorldFromConcreteState s) (pairWorldAfterBurnRun s)
    h_good h_step h_before_balance0 h_before_balance1

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

-- tama: discharges=pair_closed_world_reachable_positive_supply_has_positive_reserves
theorem closed_world_reachable_positive_supply_has_positive_reserves
    (w : PairWorldState) :
  pair_closed_world_reachable_positive_supply_has_positive_reserves w := by
  exact pairWorldReachable_positive_supply_positive_reserves

-- tama: discharges=pair_closed_world_reachable_positive_supply_path_has_positive_reserves
theorem closed_world_reachable_positive_supply_path_has_positive_reserves
    (before after : PairWorldState) :
  pair_closed_world_reachable_positive_supply_path_has_positive_reserves
    before after := by
  intro h_reachable h_positive h_path
  have h_before_reserves :=
    pairWorldReachable_positive_supply_positive_reserves h_reachable h_positive
  exact pairWorldPath_positive_reserves_preserved
    (pairWorldReachable_good before h_reachable)
    h_positive h_before_reserves.1 h_before_reserves.2 h_path

-- tama: discharges=pair_closed_world_reachable_positive_supply_path_has_positive_token_balances
theorem closed_world_reachable_positive_supply_path_has_positive_token_balances
    (before after : PairWorldState) :
  pair_closed_world_reachable_positive_supply_path_has_positive_token_balances
    before after := by
  intro h_reachable h_positive h_path
  have h_reserves :=
    closed_world_reachable_positive_supply_path_has_positive_reserves
      before after h_reachable h_positive h_path
  have h_after_good :=
    pairWorldPath_preserves_good
      (pairWorldReachable_good before h_reachable)
      h_path
  rcases h_after_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  exact ⟨Nat.lt_of_lt_of_le h_reserves.1 h_back0,
    Nat.lt_of_lt_of_le h_reserves.2 h_back1⟩

-- tama: discharges=pair_closed_world_reachable_positive_supply_burn_preserves_positive_balances
theorem closed_world_reachable_positive_supply_burn_preserves_positive_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_reachable_positive_supply_burn_preserves_positive_balances
    amount0 amount1 liquidity before after := by
  intro h_reachable h_positive h_step
  have h_good : PairWorldGood before :=
    pairWorldReachable_good before h_reachable
  have h_before_balances :
      0 < before.balance0 ∧ 0 < before.balance1 :=
    closed_world_reachable_positive_supply_path_has_positive_token_balances
      before before h_reachable h_positive (PairWorldPath.refl before)
  exact closed_world_burn_preserves_positive_balances
    amount0 amount1 liquidity before after
    h_good h_step h_before_balances.1 h_before_balances.2

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

-- tama: discharges=pair_closed_world_non_donation_step_never_increases_surplus
theorem closed_world_non_donation_step_never_increases_surplus
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

-- tama: discharges=pair_closed_world_no_donation_path_never_increases_surplus
theorem closed_world_no_donation_path_never_increases_surplus
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

-- tama: discharges=pair_closed_world_reachable_no_donation_path_surplus_value_never_increases
theorem closed_world_reachable_no_donation_path_surplus_value_never_increases
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_donation_path_surplus_value_never_increases
    before after := by
  intro h_reachable h_path
  have h_surplus :=
    closed_world_reachable_no_donation_path_never_increases_surplus
      before after h_reachable h_path
  unfold PairWorldSurplusSpotValueNum
  exact Nat.add_le_add
    (Nat.mul_le_mul_right before.reserve1 h_surplus.1)
    (Nat.mul_le_mul_right before.reserve0 h_surplus.2)

-- tama: discharges=pair_closed_world_reachable_zero_surplus_no_donation_path_preserves_zero_surplus
theorem closed_world_reachable_zero_surplus_no_donation_path_preserves_zero_surplus
    (before after : PairWorldState) :
  pair_closed_world_reachable_zero_surplus_no_donation_path_preserves_zero_surplus
    before after := by
  intro h_reachable h_surplus0 h_surplus1 h_path
  have h_le :=
    closed_world_reachable_no_donation_path_never_increases_surplus
      before after h_reachable h_path
  omega

-- tama: discharges=pair_closed_world_reachable_zero_surplus_no_donation_path_ends_balanced
theorem closed_world_reachable_zero_surplus_no_donation_path_ends_balanced
    (before after : PairWorldState) :
  pair_closed_world_reachable_zero_surplus_no_donation_path_ends_balanced
    before after := by
  intro h_reachable h_surplus0 h_surplus1 h_path
  have h_zero :=
    closed_world_reachable_zero_surplus_no_donation_path_preserves_zero_surplus
      before after h_reachable h_surplus0 h_surplus1 h_path
  have h_after_good :=
    pairWorldPath_preserves_good
      (pairWorldReachable_good before h_reachable)
      (pairWorldPath_of_noDonation h_path)
  rcases h_after_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply⟩
  unfold PairWorldSurplus0 PairWorldSurplus1 at h_zero
  omega

-- tama: discharges=pair_closed_world_mint_preserves_good
theorem closed_world_mint_preserves_good
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_preserves_good amount0 amount1 liquidity before after := by
  exact pairWorldStep_preserves_good

-- tama: discharges=pair_mint_first_success_run_preserves_good_from_run
theorem mint_first_success_run_preserves_good_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_preserves_good_from_run
    toAddr s ((mint toAddr).run s) := by
  intro h_good _h_run h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_step :=
    mint_first_success_run_refines_closed_world_from_run toAddr s
      rfl h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  exact closed_world_mint_preserves_good
    (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val
    (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s)
    h_good h_step

-- tama: discharges=pair_mint_first_success_run_establishes_good_from_run
theorem mint_first_success_run_establishes_good_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_establishes_good_from_run
    toAddr s ((mint toAddr).run s) := by
  intro _h_run h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_success_exists :
      ∃ liquidity,
        (mint toAddr).run s =
          ContractResult.success liquidity ((mint toAddr).run s).snd := by
    exact ⟨mintFirstLiquidity s, h_success⟩
  rcases mint_success_run_implies_balances_fit_uint112 toAddr s
      ((mint toAddr).run s) rfl h_success_exists with
    ⟨h_bound0, h_bound1⟩
  have h_supply_zero_val : (s.storage totalSupplySlot.slot).val = 0 := by
    simpa using congrArg (fun x : Uint256 => x.val) h_supply_zero
  have h_slot8_zero : (s.storage 8).val = 0 := by
    simpa [totalSupplySlot] using h_supply_zero_val
  have h_reserve0_bound :
      (s.storage reserve0Slot.slot).val ≤ maxUint112Nat := by
    exact Nat.le_trans
      (by simpa [Verity.Core.Uint256.le_def] using h_reserve0)
      (by simpa [Verity.Core.Uint256.le_def, maxUint112, maxUint112Nat,
        UniswapV2PairBase.maxUint112] using h_bound0)
  have h_reserve1_bound :
      (s.storage reserve1Slot.slot).val ≤ maxUint112Nat := by
    exact Nat.le_trans
      (by simpa [Verity.Core.Uint256.le_def] using h_reserve1)
      (by simpa [Verity.Core.Uint256.le_def, maxUint112, maxUint112Nat,
        UniswapV2PairBase.maxUint112] using h_bound1)
  have h_good_before : PairWorldGood (pairWorldBeforeMintRun s) := by
    constructor
    · simpa [pairWorldBeforeMintRun, Verity.Core.Uint256.le_def] using h_reserve0
    constructor
    · simpa [pairWorldBeforeMintRun, Verity.Core.Uint256.le_def] using h_reserve1
    constructor
    · simpa [pairWorldBeforeMintRun] using h_reserve0_bound
    constructor
    · simpa [pairWorldBeforeMintRun] using h_reserve1_bound
    · left
      constructor
      · simpa [pairWorldBeforeMintRun] using h_supply_zero_val
      · unfold pairWorldBeforeMintRun pairWorldLockedLiquidity
        simp [h_slot8_zero]
  exact mint_first_success_run_preserves_good_from_run toAddr s
    h_good_before rfl h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root

-- tama: discharges=pair_mint_subsequent_success_run_preserves_good_from_run
theorem mint_subsequent_success_run_preserves_good_from_run
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_preserves_good_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  intro h_good _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_step :=
    mint_subsequent_success_run_refines_closed_world_from_run
      toAddr s liquidity rfl h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1
      h_liquidity h_ratio0 h_ratio1
  exact closed_world_mint_preserves_good
    (mintAmount0 s).val (mintAmount1 s).val liquidity.val
    (pairWorldBeforeMintRun s) (pairWorldAfterSubsequentMintRun liquidity s)
    h_good h_step

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

-- tama: discharges=pair_mint_first_success_run_updates_reserves_to_balances_from_run
theorem mint_first_success_run_updates_reserves_to_balances_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_updates_reserves_to_balances_from_run
    toAddr s ((mint toAddr).run s) := by
  intro _h_run h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_step :=
    mint_first_success_run_refines_closed_world_from_run toAddr s
      rfl h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  exact closed_world_mint_updates_reserves_to_balances
    (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val
    (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s)
    h_step

-- tama: discharges=pair_mint_subsequent_success_run_updates_reserves_to_balances_from_run
theorem mint_subsequent_success_run_updates_reserves_to_balances_from_run
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_updates_reserves_to_balances_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_step :=
    mint_subsequent_success_run_refines_closed_world_from_run
      toAddr s liquidity rfl h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity
      h_ratio0 h_ratio1
  exact closed_world_mint_updates_reserves_to_balances
    (mintAmount0 s).val (mintAmount1 s).val liquidity.val
    (pairWorldBeforeMintRun s) (pairWorldAfterSubsequentMintRun liquidity s)
    h_step

-- tama: discharges=pair_closed_world_mint_never_decreases_k
theorem closed_world_mint_never_decreases_k
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_never_decreases_k
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldMintStep] at h_step
  rcases h_step with ⟨_h_amount0, _h_amount1, _h_liquidity, h_before_balance0,
    h_before_balance1, _h_after_balance0, _h_after_balance1, h_after_reserve0,
    h_after_reserve1, _h_bound0, _h_bound1, _h_supply, _h_locked, _h_ratio⟩
  unfold PairWorldK
  rw [h_after_reserve0, h_after_reserve1, h_before_balance0, h_before_balance1]
  exact Nat.mul_le_mul
    (Nat.le_add_right before.reserve0 amount0)
    (Nat.le_add_right before.reserve1 amount1)

-- tama: discharges=pair_mint_first_success_run_never_decreases_k_from_run
theorem mint_first_success_run_never_decreases_k_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_never_decreases_k_from_run
    toAddr s ((mint toAddr).run s) := by
  intro _h_run h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_step :=
    mint_first_success_run_refines_closed_world_from_run toAddr s
      rfl h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  exact closed_world_mint_never_decreases_k
    (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val
    (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s)
    h_step

-- tama: discharges=pair_mint_subsequent_success_run_never_decreases_k_from_run
theorem mint_subsequent_success_run_never_decreases_k_from_run
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_never_decreases_k_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_step :=
    mint_subsequent_success_run_refines_closed_world_from_run
      toAddr s liquidity rfl h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity
      h_ratio0 h_ratio1
  exact closed_world_mint_never_decreases_k
    (mintAmount0 s).val (mintAmount1 s).val liquidity.val
    (pairWorldBeforeMintRun s) (pairWorldAfterSubsequentMintRun liquidity s)
    h_step

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

-- tama: discharges=pair_closed_world_mint_does_not_dilute_existing_lp_share
theorem closed_world_mint_does_not_dilute_existing_lp_share
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_mint_does_not_dilute_existing_lp_share
    amount0 amount1 liquidity before after := by
  intro h_good h_positive h_step
  exact pairWorldStep_k_per_supply_never_decreases h_good h_positive h_step

-- tama: discharges=pair_mint_subsequent_success_run_preserves_existing_lp_share
theorem mint_subsequent_success_run_preserves_existing_lp_share
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) :
  pair_mint_subsequent_success_run_preserves_existing_lp_share
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run h_success h_good h_positive h_supply_pos h_reserve0_pos
    h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity
    h_ratio0 h_ratio1
  have h_step :=
    mint_subsequent_success_run_refines_closed_world_from_run
      toAddr s liquidity rfl h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity
      h_ratio0 h_ratio1
  exact closed_world_mint_does_not_dilute_existing_lp_share
    (mintAmount0 s).val (mintAmount1 s).val liquidity.val
    (pairWorldBeforeMintRun s) (pairWorldAfterSubsequentMintRun liquidity s)
    h_good h_positive h_step

-- tama: discharges=pair_closed_world_burn_preserves_good
theorem closed_world_burn_preserves_good
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_preserves_good amount0 amount1 liquidity before after := by
  exact pairWorldStep_preserves_good

-- tama: discharges=pair_burn_success_run_preserves_good_from_run
theorem burn_success_run_preserves_good_from_run
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_preserves_good_from_run
    toAddr s ((burn toAddr).run s) := by
  intro h_good _h_run h_success h_liquidity_pos h_supply_pos
    h_liquidity_le h_locked_remaining h_amount0 h_amount1 h_amount0_le
    h_amount1_le h_bound0 h_bound1 h_ratio0 h_ratio1
  have h_step :=
    burn_success_run_refines_closed_world toAddr s rfl h_success
      h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
      h_amount0 h_amount1 h_amount0_le h_amount1_le h_bound0 h_bound1
      h_ratio0 h_ratio1
  exact closed_world_burn_preserves_good
    (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val
    (pairWorldFromConcreteState s) (pairWorldAfterBurnRun s)
    h_good h_step

-- tama: discharges=pair_closed_world_burn_updates_reserves_to_balances
theorem closed_world_burn_updates_reserves_to_balances
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_updates_reserves_to_balances
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, h_reserve0, h_reserve1, _h_bound0, _h_bound1,
    _h_supply, _h_locked, _h_ratio0, _h_ratio1⟩
  exact ⟨h_reserve0, h_reserve1⟩

-- tama: discharges=pair_burn_success_run_updates_reserves_to_balances_from_run
theorem burn_success_run_updates_reserves_to_balances_from_run
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_updates_reserves_to_balances_from_run
    toAddr s ((burn toAddr).run s) := by
  intro _h_run h_success h_liquidity_pos h_supply_pos h_liquidity_le
    h_locked_remaining h_amount0 h_amount1 h_amount0_le h_amount1_le
    h_bound0 h_bound1 h_ratio0 h_ratio1
  have h_step :=
    burn_success_run_refines_closed_world toAddr s
      rfl h_success h_liquidity_pos h_supply_pos h_liquidity_le
      h_locked_remaining h_amount0 h_amount1 h_amount0_le h_amount1_le
      h_bound0 h_bound1 h_ratio0 h_ratio1
  exact closed_world_burn_updates_reserves_to_balances
    (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val
    (pairWorldFromConcreteState s) (pairWorldAfterBurnRun s)
    h_step

-- tama: discharges=pair_closed_world_burn_liquidity_ratio
theorem closed_world_burn_liquidity_ratio
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_liquidity_ratio
    amount0 amount1 liquidity before after := by
  intro h_step
  simp [PairWorldStep, PairWorldBurnStep] at h_step
  rcases h_step with ⟨_h_amount0_pos, _h_amount1_pos, _h_liquidity_pos,
    _h_supply_pos, _h_amount0, _h_amount1, _h_liquidity, _h_locked_remaining,
    _h_balance0, _h_balance1, _h_reserve0, _h_reserve1, _h_bound0, _h_bound1,
    _h_supply, _h_locked, h_ratio0, h_ratio1⟩
  exact ⟨h_ratio0, h_ratio1⟩

-- tama: discharges=pair_closed_world_burn_does_not_dilute_remaining_lp_share
theorem closed_world_burn_does_not_dilute_remaining_lp_share
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) :
  pair_closed_world_burn_does_not_dilute_remaining_lp_share
    amount0 amount1 liquidity before after := by
  intro h_good h_positive h_step
  exact pairWorldStep_k_per_supply_never_decreases h_good h_positive h_step

-- tama: discharges=pair_burn_success_run_preserves_remaining_lp_share
theorem burn_success_run_preserves_remaining_lp_share
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_preserves_remaining_lp_share
    toAddr s ((burn toAddr).run s) := by
  intro _h_run h_success h_good h_positive h_liquidity_pos h_supply_pos
    h_liquidity_le h_locked_remaining h_amount0 h_amount1 h_amount0_le
    h_amount1_le h_bound0 h_bound1 h_ratio0 h_ratio1
  have h_step :=
    burn_success_run_refines_closed_world toAddr s rfl h_success
      h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
      h_amount0 h_amount1 h_amount0_le h_amount1_le h_bound0 h_bound1
      h_ratio0 h_ratio1
  exact closed_world_burn_does_not_dilute_remaining_lp_share
    (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val
    (pairWorldFromConcreteState s) (pairWorldAfterBurnRun s)
    h_good h_positive h_step

-- tama: discharges=pair_closed_world_swap_preserves_good
theorem closed_world_swap_preserves_good
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_preserves_good
    amount0In amount1In amount0Out amount1Out before after := by
  exact pairWorldStep_preserves_good

-- tama: discharges=pair_swap_success_run_preserves_good_from_run
theorem swap_success_run_preserves_good_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_preserves_good_from_run
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro h_good _h_run h_success h_liq0 h_liq1 h_input h_balance0
    h_balance1 h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  have h_step :=
    swap_success_run_refines_closed_world_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      rfl h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  exact closed_world_swap_preserves_good
    (swapAmount0In amount0Out balance0Now s).val
    (swapAmount1In amount1Out balance1Now s).val
    amount0Out.val amount1Out.val
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s)
    h_good h_step

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

-- tama: discharges=pair_swap_success_run_updates_reserves_to_balances_from_run
theorem swap_success_run_updates_reserves_to_balances_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_updates_reserves_to_balances_from_run
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_k
  have h_step :=
    swap_success_run_refines_closed_world_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s rfl
      h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_k
  exact closed_world_swap_updates_reserves_to_balances
    (swapAmount0In amount0Out balance0Now s).val
    (swapAmount1In amount1Out balance1Now s).val
    amount0Out.val amount1Out.val
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s)
    h_step

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

-- tama: discharges=pair_closed_world_fee_adjusted_swap_implies_raw_k
theorem closed_world_fee_adjusted_swap_implies_raw_k
    (amount0In amount1In : Nat)
    (before after : PairWorldState) :
  pair_closed_world_fee_adjusted_swap_implies_raw_k
    amount0In amount1In before after := by
  exact feeAdjustedSwap_implies_raw_k amount0In amount1In before after

-- tama: discharges=pair_closed_world_swap_never_decreases_k
theorem closed_world_swap_never_decreases_k
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_never_decreases_k
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, _h_enough0, _h_enough1,
    _h_input, _h_balance0, _h_balance1, h_reserve0, h_reserve1, _h_bound0,
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, h_adjusted_k⟩
  exact feeAdjustedSwap_implies_raw_k
    amount0In amount1In before after h_reserve0 h_reserve1 h_adjusted_k

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
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_adjusted_k⟩
  exact ⟨h_output, h_input⟩

-- tama: discharges=pair_closed_world_swap_final_balances_account_for_input_and_output
theorem closed_world_swap_final_balances_account_for_input_and_output
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_final_balances_account_for_input_and_output
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, h_enough0, h_enough1,
    _h_input, h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_adjusted_k⟩
  constructor
  · rw [h_balance0, Nat.sub_add_cancel h_enough0]
  · rw [h_balance1, Nat.sub_add_cancel h_enough1]

-- tama: discharges=pair_closed_world_swap_k_uses_final_balances
theorem closed_world_swap_k_uses_final_balances
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_k_uses_final_balances
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSwapStep] at h_step
  rcases h_step with ⟨_h_output, _h_liq0, _h_liq1, h_enough0, h_enough1,
    _h_input, h_balance0, h_balance1, _h_reserve0, _h_reserve1, _h_bound0,
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, h_adjusted_k⟩
  exact ⟨by rw [h_balance0, Nat.sub_add_cancel h_enough0],
    by rw [h_balance1, Nat.sub_add_cancel h_enough1],
    h_adjusted_k⟩

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
    _h_bound1, _h_supply, _h_locked, _h_fee0, _h_fee1, _h_adjusted_k⟩
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
    _h_bound1, h_supply, h_locked, _h_fee0, _h_fee1, _h_adjusted_k⟩
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_swap_success_run_preserves_liquidity_supply_from_run
theorem swap_success_run_preserves_liquidity_supply_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_preserves_liquidity_supply_from_run
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_k
  have h_step :=
    swap_success_run_refines_closed_world_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s rfl
      h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_k
  exact closed_world_swap_preserves_liquidity_supply
    (swapAmount0In amount0Out balance0Now s).val
    (swapAmount1In amount1Out balance1Now s).val
    amount0Out.val amount1Out.val
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s)
    h_step

-- tama: discharges=pair_swap_success_run_never_decreases_k_from_run
theorem swap_success_run_never_decreases_k_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_never_decreases_k_from_run
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_k
  have h_step :=
    swap_success_run_refines_closed_world_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s rfl
      h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_k
  exact closed_world_swap_never_decreases_k
    (swapAmount0In amount0Out balance0Now s).val
    (swapAmount1In amount1Out balance1Now s).val
    amount0Out.val amount1Out.val
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s)
    h_step

-- tama: discharges=pair_closed_world_step_k_per_supply_never_decreases
theorem closed_world_step_k_per_supply_never_decreases
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_step_k_per_supply_never_decreases action before after := by
  exact pairWorldStep_k_per_supply_never_decreases

-- tama: discharges=pair_closed_world_path_k_per_supply_never_decreases
theorem closed_world_path_k_per_supply_never_decreases
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

-- tama: discharges=pair_closed_world_same_supply_path_never_decreases_k
theorem closed_world_same_supply_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_same_supply_path_never_decreases_k before after := by
  exact pairWorldSameSupplyPath_never_decreases_k

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

-- tama: discharges=pair_closed_world_positive_supply_same_supply_path_no_spot_profit
theorem closed_world_positive_supply_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_positive_supply_same_supply_path_no_spot_profit before after := by
  intro h_good h_positive h_path h_supply h_reserve0 h_reserve1
  have h_k :
      PairWorldK before ≤ PairWorldK after :=
    pairWorldSameSupplyPath_never_decreases_k h_good h_positive h_path h_supply
  exact closed_world_same_supply_path_no_spot_profit before after
    h_path h_good h_supply h_reserve0 h_reserve1 h_k

-- tama: discharges=pair_closed_world_swap_no_spot_value_extraction
theorem closed_world_swap_no_spot_value_extraction
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_swap_no_spot_value_extraction
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_good h_positive h_reserve0 h_reserve1 h_step
  have h_path : PairWorldPath before after :=
    PairWorldPath.step
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      (PairWorldPath.refl before) h_step
  have h_supply : before.totalSupply = after.totalSupply := by
    have h_swap :
        after.totalSupply = before.totalSupply ∧
          after.lockedLiquidity = before.lockedLiquidity :=
      closed_world_swap_preserves_liquidity_supply
        amount0In amount1In amount0Out amount1Out before after h_step
    exact h_swap.1.symm
  have h_no_profit :
      PairWorldNoSpotProfit before after :=
    closed_world_positive_supply_same_supply_path_no_spot_profit before after
      h_good h_positive h_path h_supply h_reserve0 h_reserve1
  have h_start :
      PairWorldSpotValueNum before before = 2 * PairWorldK before := by
    unfold PairWorldSpotValueNum PairWorldK
    ring
  simpa [pair_closed_world_swap_no_spot_value_extraction, h_start,
    PairWorldNoSpotProfit] using h_no_profit

-- tama: discharges=pair_closed_world_reachable_positive_supply_swap_no_spot_value_extraction
theorem closed_world_reachable_positive_supply_swap_no_spot_value_extraction
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) :
  pair_closed_world_reachable_positive_supply_swap_no_spot_value_extraction
    amount0In amount1In amount0Out amount1Out before after := by
  intro h_reachable h_positive h_step
  have h_good : PairWorldGood before :=
    pairWorldReachable_good before h_reachable
  have h_reserves :
      0 < before.reserve0 ∧ 0 < before.reserve1 :=
    pairWorldReachable_positive_supply_positive_reserves
      h_reachable h_positive
  exact closed_world_swap_no_spot_value_extraction
    amount0In amount1In amount0Out amount1Out before after
    h_good h_positive h_reserves.1 h_reserves.2 h_step

-- tama: discharges=pair_closed_world_reachable_positive_supply_swap_no_caller_spot_profit
theorem closed_world_reachable_positive_supply_swap_no_caller_spot_profit
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_positive_supply_swap_no_caller_spot_profit
    amount0In amount1In amount0Out amount1Out before after
    callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_step h_total_value
  have h_pool_value :
      PairWorldSpotValueNum before before ≤
        PairWorldSpotValueNum before after :=
    closed_world_reachable_positive_supply_swap_no_spot_value_extraction
      amount0In amount1In amount0Out amount1Out before after
      h_reachable h_positive h_step
  omega

-- tama: discharges=pair_swap_success_run_bridge_no_caller_spot_profit
theorem swap_success_run_bridge_no_caller_spot_profit
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_swap_success_run_bridge_no_caller_spot_profit
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s)
    callerValueBefore callerValueAfter := by
  intro _h_run _h_success h_reachable h_positive h_step h_total_value
  exact closed_world_reachable_positive_supply_swap_no_caller_spot_profit
    (swapAmount0In amount0Out balance0Now s).val
    (swapAmount1In amount1Out balance1Now s).val
    amount0Out.val amount1Out.val
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s)
    callerValueBefore callerValueAfter
    h_reachable h_positive h_step h_total_value

-- tama: discharges=pair_swap_success_run_no_caller_spot_profit_from_run
theorem swap_success_run_no_caller_spot_profit_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_swap_success_run_no_caller_spot_profit_from_run
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s)
    callerValueBefore callerValueAfter := by
  intro _h_run h_success h_reachable h_positive h_liq0 h_liq1 h_input
    h_balance0 h_balance1 h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
    h_total_value
  have h_step :=
    swap_success_run_refines_closed_world_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      rfl h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  exact closed_world_reachable_positive_supply_swap_no_caller_spot_profit
    (swapAmount0In amount0Out balance0Now s).val
    (swapAmount1In amount1Out balance1Now s).val
    amount0Out.val amount1Out.val
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s)
    callerValueBefore callerValueAfter
    h_reachable h_positive h_step h_total_value

-- tama: discharges=pair_closed_world_reachable_same_supply_path_never_decreases_k
theorem closed_world_reachable_same_supply_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_never_decreases_k before after := by
  intro h_reachable h_positive h_path h_supply
  exact pairWorldSameSupplyPath_never_decreases_k
    (pairWorldReachable_good before h_reachable) h_positive h_path h_supply

-- tama: discharges=pair_closed_world_reachable_same_supply_path_no_spot_profit
theorem closed_world_reachable_same_supply_path_no_spot_profit
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_no_spot_profit before after := by
  intro h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  exact closed_world_positive_supply_same_supply_path_no_spot_profit before after
    (pairWorldReachable_good before h_reachable)
    h_positive h_path h_supply h_reserve0 h_reserve1

-- tama: discharges=pair_closed_world_reachable_same_supply_path_pool_value_never_decreases
theorem closed_world_reachable_same_supply_path_pool_value_never_decreases
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_pool_value_never_decreases before after := by
  intro h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  have h_no_profit :
      PairWorldNoSpotProfit before after :=
    closed_world_reachable_same_supply_path_no_spot_profit before after
      h_reachable h_positive h_path h_supply h_reserve0 h_reserve1
  have h_initial_value :
      PairWorldSpotValueNum before before = 2 * PairWorldK before := by
    unfold PairWorldSpotValueNum PairWorldK
    nlinarith
  simpa [pair_closed_world_reachable_same_supply_path_pool_value_never_decreases,
    PairWorldNoSpotProfit, h_initial_value] using h_no_profit

-- tama: discharges=pair_closed_world_reachable_same_supply_path_no_spot_value_extraction
theorem closed_world_reachable_same_supply_path_no_spot_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_no_spot_value_extraction before after := by
  simpa [pair_closed_world_reachable_same_supply_path_no_spot_value_extraction]
    using closed_world_reachable_same_supply_path_pool_value_never_decreases
      before after

-- tama: discharges=pair_closed_world_reachable_same_supply_path_no_token1_denominated_profit
theorem closed_world_reachable_same_supply_path_no_token1_denominated_profit
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_no_token1_denominated_profit
    before after := by
  simpa [pair_closed_world_reachable_same_supply_path_no_token1_denominated_profit]
    using closed_world_reachable_same_supply_path_pool_value_never_decreases
      before after

-- tama: discharges=pair_closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction
theorem closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction
    before after := by
  intro h_reachable h_positive h_path h_supply
  have h_reserves :=
    pairWorldReachable_positive_supply_positive_reserves h_reachable h_positive
  exact closed_world_reachable_same_supply_path_no_spot_value_extraction
    before after h_reachable h_positive h_path h_supply
    h_reserves.1 h_reserves.2

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

-- tama: discharges=pair_closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus
theorem closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus
    (before after : PairWorldState) :
  pair_closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus
    before after := by
  intro h_reachable h_positive h_path h_supply
  have h_reserve_value :
      PairWorldSpotValueNum before before ≤
        PairWorldSpotValueNum before after :=
    closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction
      before after h_reachable h_positive h_path h_supply
  have h_after_good :=
    pairWorldPath_preserves_good
      (pairWorldReachable_good before h_reachable)
      h_path
  have h_spot_to_balance :
      PairWorldSpotValueNum before before ≤
        PairWorldBalanceSpotValueNum before after :=
    Nat.le_trans h_reserve_value
      (pairWorldSpotValue_le_balanceSpotValue
        (spot := before) (pool := after) h_after_good)
  have h_before_eq :=
    pairWorldBalanceSpotValue_eq_spot_plus_surplus
      (spot := before) (pool := before)
      (pairWorldReachable_good before h_reachable)
  rw [h_before_eq]
  exact Nat.add_le_add_right h_spot_to_balance
    (PairWorldSurplusSpotValueNum before before)

-- tama: discharges=pair_closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus
theorem closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus
    before after callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_path h_supply h_total_value
  have h_pair_bound :
      PairWorldBalanceSpotValueNum before before ≤
        PairWorldBalanceSpotValueNum before after +
          PairWorldSurplusSpotValueNum before before :=
    closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus
      before after h_reachable h_positive h_path h_supply
  omega

-- tama: discharges=pair_closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction
theorem closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction
    before after := by
  intro h_reachable h_positive h_surplus0 h_surplus1 h_path h_supply
  have h_bound :=
    closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus
      before after h_reachable h_positive h_path h_supply
  have h_start_surplus_value :
      PairWorldSurplusSpotValueNum before before = 0 := by
    simp [PairWorldSurplusSpotValueNum, h_surplus0, h_surplus1]
  simpa [h_start_surplus_value] using h_bound

-- tama: discharges=pair_closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit
theorem closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit
    before after callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_surplus0 h_surplus1 h_path h_supply h_total_value
  have h_pair_value :
      PairWorldBalanceSpotValueNum before before ≤
        PairWorldBalanceSpotValueNum before after :=
    closed_world_reachable_zero_surplus_same_supply_path_no_token_balance_value_extraction
      before after h_reachable h_positive h_surplus0 h_surplus1 h_path h_supply
  omega

-- tama: discharges=pair_closed_world_reachable_same_supply_path_no_caller_spot_profit
theorem closed_world_reachable_same_supply_path_no_caller_spot_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_same_supply_path_no_caller_spot_profit
    before after callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_path h_supply h_total_value
  have h_pool_value :
      PairWorldSpotValueNum before before ≤
        PairWorldSpotValueNum before after :=
    closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction
      before after h_reachable h_positive h_path h_supply
  omega

-- tama: discharges=pair_closed_world_reachable_zero_surplus_swap_no_caller_token_balance_profit
theorem closed_world_reachable_zero_surplus_swap_no_caller_token_balance_profit
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_zero_surplus_swap_no_caller_token_balance_profit
    amount0In amount1In amount0Out amount1Out before after
    callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_surplus0 h_surplus1 h_step h_total_value
  have h_supply :=
    (closed_world_swap_preserves_liquidity_supply
      amount0In amount1In amount0Out amount1Out before after h_step).1
  have h_path : PairWorldPath before after :=
    PairWorldPath.step
      (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
      (PairWorldPath.refl before) h_step
  exact closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit
    before after callerValueBefore callerValueAfter h_reachable h_positive
    h_surplus0 h_surplus1 h_path h_supply.symm h_total_value

-- tama: discharges=pair_closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction
theorem closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction
    before after := by
  intro h_reachable h_positive h_balance0 h_balance1 h_path h_supply
  have h_reserve_value :=
    closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction
      before after h_reachable h_positive h_path h_supply
  have h_after_good :=
    pairWorldPath_preserves_good
      (pairWorldReachable_good before h_reachable)
      h_path
  have h_final_reserve_to_balance :=
    pairWorldSpotValue_le_balanceSpotValue
      (spot := before) (pool := after) h_after_good
  have h_initial_value :
      PairWorldBalanceSpotValueNum before before =
        PairWorldSpotValueNum before before := by
    unfold PairWorldBalanceSpotValueNum PairWorldSpotValueNum
    rw [h_balance0, h_balance1]
  rw [h_initial_value]
  exact Nat.le_trans h_reserve_value h_final_reserve_to_balance

-- tama: discharges=pair_closed_world_reachable_balanced_no_mint_burn_path_no_token_balance_value_extraction
theorem closed_world_reachable_balanced_no_mint_burn_path_no_token_balance_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_balanced_no_mint_burn_path_no_token_balance_value_extraction
    before after := by
  intro h_reachable h_positive h_balance0 h_balance1 h_path
  have h_supply :=
    (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_balanced_same_supply_path_no_token_balance_value_extraction
    before after h_reachable h_positive h_balance0 h_balance1
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm

-- tama: discharges=pair_closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus
theorem closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus
    before after := by
  intro h_reachable h_positive h_path
  have h_supply :=
    (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_same_supply_path_token_balance_loss_bounded_by_initial_surplus
    before after h_reachable h_positive
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm

-- tama: discharges=pair_closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus
theorem closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_no_mint_burn_path_caller_token_balance_profit_bounded_by_initial_surplus
    before after callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_path h_total_value
  have h_supply := (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_same_supply_path_caller_token_balance_profit_bounded_by_initial_surplus
    before after callerValueBefore callerValueAfter h_reachable h_positive
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm h_total_value

-- tama: discharges=pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction
theorem closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction
    before after := by
  intro h_reachable h_positive h_surplus0 h_surplus1 h_path
  have h_bound :=
    closed_world_reachable_no_mint_burn_path_token_balance_loss_bounded_by_initial_surplus
      before after h_reachable h_positive h_path
  have h_start_surplus_value :
      PairWorldSurplusSpotValueNum before before = 0 := by
    simp [PairWorldSurplusSpotValueNum, h_surplus0, h_surplus1]
  simpa [h_start_surplus_value] using h_bound

-- tama: discharges=pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit
theorem closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit
    before after callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_surplus0 h_surplus1 h_path h_total_value
  have h_supply := (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_zero_surplus_same_supply_path_no_caller_token_balance_profit
    before after callerValueBefore callerValueAfter
    h_reachable h_positive h_surplus0 h_surplus1
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm h_total_value

-- tama: discharges=pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction
theorem closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_token_balance_value_extraction
    before after := by
  intro h_reachable h_positive h_surplus0 h_surplus1 h_no_donation h_no_mint_burn
  have h_balanced :=
    closed_world_reachable_zero_surplus_no_donation_path_ends_balanced
      before after h_reachable h_surplus0 h_surplus1 h_no_donation
  have h_value :=
    closed_world_reachable_zero_surplus_no_mint_burn_path_no_token_balance_value_extraction
      before after h_reachable h_positive h_surplus0 h_surplus1 h_no_mint_burn
  exact ⟨h_balanced.1, h_balanced.2, h_value⟩

-- tama: discharges=pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit
theorem closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_zero_surplus_no_donation_no_mint_burn_path_balanced_and_no_caller_token_balance_profit
    before after callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_surplus0 h_surplus1 h_no_donation
    h_no_mint_burn h_total_value
  have h_balanced :=
    closed_world_reachable_zero_surplus_no_donation_path_ends_balanced
      before after h_reachable h_surplus0 h_surplus1 h_no_donation
  have h_caller :=
    closed_world_reachable_zero_surplus_no_mint_burn_path_no_caller_token_balance_profit
      before after callerValueBefore callerValueAfter
      h_reachable h_positive h_surplus0 h_surplus1 h_no_mint_burn
      h_total_value
  exact ⟨h_balanced.1, h_balanced.2, h_caller⟩

-- tama: discharges=pair_closed_world_reachable_no_mint_burn_path_no_caller_spot_profit
theorem closed_world_reachable_no_mint_burn_path_no_caller_spot_profit
    (before after : PairWorldState)
    (callerValueBefore callerValueAfter : Nat) :
  pair_closed_world_reachable_no_mint_burn_path_no_caller_spot_profit
    before after callerValueBefore callerValueAfter := by
  intro h_reachable h_positive h_path h_total_value
  have h_supply := (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_same_supply_path_no_caller_spot_profit
    before after callerValueBefore callerValueAfter h_reachable h_positive
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm h_total_value

-- tama: discharges=pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
theorem closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_mint_burn_path_no_spot_value_extraction
    before after := by
  intro h_reachable h_positive h_path h_reserve0 h_reserve1
  have h_supply :=
    (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_same_supply_path_no_spot_value_extraction
    before after h_reachable h_positive
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm h_reserve0 h_reserve1

-- tama: discharges=pair_closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction
theorem closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction
    (before after : PairWorldState) :
  pair_closed_world_reachable_positive_supply_no_mint_burn_path_no_spot_value_extraction
    before after := by
  intro h_reachable h_positive h_path
  have h_supply :=
    (pairWorldNoMintBurnPath_preserves_supply h_path).1
  exact closed_world_reachable_positive_supply_same_supply_path_no_spot_value_extraction
    before after h_reachable h_positive
    (pairWorldPath_of_noMintBurn h_path) h_supply.symm

-- tama: discharges=pair_closed_world_reachable_no_mint_burn_path_never_decreases_k
theorem closed_world_reachable_no_mint_burn_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_mint_burn_path_never_decreases_k before after := by
  intro h_reachable h_path
  exact pairWorldNoBurnPath_never_decreases_k
    (pairWorldReachable_good before h_reachable)
    (pairWorldNoBurnPath_of_noMintBurn h_path)

-- tama: discharges=pair_closed_world_non_burn_step_never_decreases_k
theorem closed_world_non_burn_step_never_decreases_k
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_non_burn_step_never_decreases_k action before after := by
  exact pairWorldNonBurnStep_never_decreases_k

-- tama: discharges=pair_closed_world_k_decrease_requires_burn
theorem closed_world_k_decrease_requires_burn
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_k_decrease_requires_burn action before after := by
  intro h_good h_step h_decrease
  by_cases h_burn :
      ∃ amount0 amount1 liquidity,
        action = PairWorldAction.burn amount0 amount1 liquidity
  · exact h_burn
  · have h_not_burn :
        ∀ amount0 amount1 liquidity,
          action ≠ PairWorldAction.burn amount0 amount1 liquidity := by
      intro amount0 amount1 liquidity h_eq
      exact h_burn ⟨amount0, amount1, liquidity, h_eq⟩
    have h_nondec :=
      pairWorldNonBurnStep_never_decreases_k h_good h_step h_not_burn
    exact False.elim ((Nat.not_lt_of_ge h_nondec) h_decrease)

-- tama: discharges=pair_closed_world_no_burn_path_never_decreases_k
theorem closed_world_no_burn_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_no_burn_path_never_decreases_k before after := by
  exact pairWorldNoBurnPath_never_decreases_k

-- tama: discharges=pair_closed_world_reachable_no_burn_path_never_decreases_k
theorem closed_world_reachable_no_burn_path_never_decreases_k
    (before after : PairWorldState) :
  pair_closed_world_reachable_no_burn_path_never_decreases_k before after := by
  intro h_reachable h_path
  exact pairWorldNoBurnPath_never_decreases_k
    (pairWorldReachable_good before h_reachable) h_path

-- tama: discharges=pair_closed_world_reachable_k_decrease_excludes_burn_free_path
theorem closed_world_reachable_k_decrease_excludes_burn_free_path
    (before after : PairWorldState) :
  pair_closed_world_reachable_k_decrease_excludes_burn_free_path before after := by
  intro h_reachable _h_path h_decrease h_no_burn_path
  have h_nondec :
      PairWorldK before ≤ PairWorldK after :=
    pairWorldNoBurnPath_never_decreases_k
      (pairWorldReachable_good before h_reachable) h_no_burn_path
  exact (Nat.not_lt_of_ge h_nondec) h_decrease

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

-- tama: discharges=pair_closed_world_skim_eliminates_surplus
theorem closed_world_skim_eliminates_surplus
    (before after : PairWorldState) :
  pair_closed_world_skim_eliminates_surplus before after := by
  intro h_step
  have h_remove := closed_world_skim_removes_surplus before after h_step
  unfold PairWorldSurplus0 PairWorldSurplus1
  rw [h_remove.1, h_remove.2.1, h_remove.2.2.1, h_remove.2.2.2]
  exact ⟨Nat.sub_self before.reserve0, Nat.sub_self before.reserve1⟩

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

-- tama: discharges=pair_closed_world_skim_token_balance_value_never_increases
theorem closed_world_skim_token_balance_value_never_increases
    (before after : PairWorldState) :
  pair_closed_world_skim_token_balance_value_never_increases before after := by
  intro h_good h_step
  have h_exact :=
    closed_world_skim_removes_exact_surplus_value before after h_good h_step
  omega

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

-- tama: discharges=pair_closed_world_skim_preserves_liquidity_supply
theorem closed_world_skim_preserves_liquidity_supply
    (before after : PairWorldState) :
  pair_closed_world_skim_preserves_liquidity_supply before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSkimStep] at h_step
  rcases h_step with ⟨_h_balance0, _h_balance1, _h_reserve0, _h_reserve1,
    h_supply, h_locked⟩
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_skim_success_run_preserves_liquidity_supply_from_run
theorem skim_success_run_preserves_liquidity_supply_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_preserves_liquidity_supply_from_run
    toAddr s result := by
  intro h_run h_success
  have h_step :=
    skim_success_run_refines_closed_world_from_run
      toAddr s result h_run h_success
  exact closed_world_skim_preserves_liquidity_supply
    (pairWorldFromConcreteState s) (pairWorldAfterSkimRun s) h_step

-- tama: discharges=pair_skim_success_run_preserves_good_from_run
theorem skim_success_run_preserves_good_from_run
    (toAddr : Address) (s : ContractState) (result : ContractResult Unit) :
  pair_skim_success_run_preserves_good_from_run toAddr s result := by
  intro h_good h_run h_success
  have h_step :=
    skim_success_run_refines_closed_world_from_run
      toAddr s result h_run h_success
  exact closed_world_skim_preserves_good
    (pairWorldFromConcreteState s) (pairWorldAfterSkimRun s)
    h_good h_step

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

-- tama: discharges=pair_sync_success_run_preserves_good_from_run
theorem sync_success_run_preserves_good_from_run
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_preserves_good_from_run s result := by
  intro h_good h_run h_success
  have h_step :=
    sync_success_run_refines_closed_world_from_run s result h_run h_success
  exact closed_world_sync_preserves_good
    (pairWorldFromConcreteState s) (pairWorldAfterSyncRun s)
    h_good h_step

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

-- tama: discharges=pair_closed_world_sync_preserves_token_balance_value
theorem closed_world_sync_preserves_token_balance_value
    (spot before after : PairWorldState) :
  pair_closed_world_sync_preserves_token_balance_value spot before after := by
  intro h_step
  rcases closed_world_sync_preserves_token_balances before after h_step with
    ⟨h_balance0, h_balance1⟩
  simp [pair_closed_world_sync_preserves_token_balance_value,
    PairWorldBalanceSpotValueNum, h_balance0, h_balance1]

-- tama: discharges=pair_closed_world_reserve_write_sets_reserves_to_balances
theorem closed_world_reserve_write_sets_reserves_to_balances
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_reserve_write_sets_reserves_to_balances action before after := by
  intro h_action h_step
  rcases h_action with h_mint | h_burn | h_swap | h_sync
  · rcases h_mint with ⟨amount0, amount1, liquidity, h_action⟩
    subst action
    exact closed_world_mint_updates_reserves_to_balances
      amount0 amount1 liquidity before after h_step
  · rcases h_burn with ⟨amount0, amount1, liquidity, h_action⟩
    subst action
    exact closed_world_burn_updates_reserves_to_balances
      amount0 amount1 liquidity before after h_step
  · rcases h_swap with ⟨amount0In, amount1In, amount0Out, amount1Out, h_action⟩
    subst action
    exact closed_world_swap_updates_reserves_to_balances
      amount0In amount1In amount0Out amount1Out before after h_step
  · subst action
    have h_sync_step := closed_world_sync_sets_reserves_to_balances before after h_step
    constructor
    · rw [h_sync_step.1, h_sync_step.2.2.1]
    · rw [h_sync_step.2.1, h_sync_step.2.2.2]

-- tama: discharges=pair_closed_world_concrete_reserve_write_uses_oracle_rule
theorem closed_world_concrete_reserve_write_uses_oracle_rule
    (action : PairWorldAction) (after : PairWorldState)
    (s : ContractState) :
  pair_closed_world_concrete_reserve_write_uses_oracle_rule action after s := by
  intro h_action h_step
  have h_write :=
    closed_world_reserve_write_sets_reserves_to_balances
      action (pairWorldFromConcreteState s) after h_action h_step
  exact ⟨h_write.1, h_write.2,
    reserve_update_oracle_same_timestamp_keeps_price_cumulatives s,
    reserve_update_oracle_elapsed_updates_price_cumulatives s,
    reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives s⟩

-- tama: discharges=pair_sync_success_run_uses_oracle_rule
theorem sync_success_run_uses_oracle_rule
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_uses_oracle_rule s result := by
  intro h_run h_success h_bound0 h_bound1
  have h_step :=
    sync_success_run_refines_closed_world
      s result h_run h_success h_bound0 h_bound1
  have h_action :
      ((∃ amount0 amount1 liquidity,
          PairWorldAction.sync = PairWorldAction.mint amount0 amount1 liquidity) ∨
        (∃ amount0 amount1 liquidity,
          PairWorldAction.sync = PairWorldAction.burn amount0 amount1 liquidity) ∨
        (∃ amount0In amount1In amount0Out amount1Out,
          PairWorldAction.sync =
            PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
        PairWorldAction.sync = PairWorldAction.sync) := by
    right
    right
    right
    rfl
  exact closed_world_concrete_reserve_write_uses_oracle_rule
    PairWorldAction.sync (pairWorldAfterSyncRun s) s h_action h_step

-- tama: discharges=pair_sync_success_run_uses_oracle_rule_from_run
theorem sync_success_run_uses_oracle_rule_from_run
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_uses_oracle_rule_from_run s result := by
  intro h_run h_success
  have h_step :=
    sync_success_run_refines_closed_world_from_run s result h_run h_success
  have h_action :
      ((∃ amount0 amount1 liquidity,
          PairWorldAction.sync = PairWorldAction.mint amount0 amount1 liquidity) ∨
        (∃ amount0 amount1 liquidity,
          PairWorldAction.sync = PairWorldAction.burn amount0 amount1 liquidity) ∨
        (∃ amount0In amount1In amount0Out amount1Out,
          PairWorldAction.sync =
            PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
        PairWorldAction.sync = PairWorldAction.sync) := by
    right
    right
    right
    rfl
  exact closed_world_concrete_reserve_write_uses_oracle_rule
    PairWorldAction.sync (pairWorldAfterSyncRun s) s h_action h_step

private theorem reserve_write_step_uses_oracle_rule
    (action : PairWorldAction) (before after : PairWorldState)
    (s : ContractState) :
  ((∃ amount0 amount1 liquidity,
      action = PairWorldAction.mint amount0 amount1 liquidity) ∨
    (∃ amount0 amount1 liquidity,
      action = PairWorldAction.burn amount0 amount1 liquidity) ∨
    (∃ amount0In amount1In amount0Out amount1Out,
      action = PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
    action = PairWorldAction.sync) →
    PairWorldStep action before after →
      after.reserve0 = after.balance0 ∧
      after.reserve1 = after.balance1 ∧
      pair_reserve_update_oracle_same_timestamp_keeps_price_cumulatives s ∧
      pair_reserve_update_oracle_elapsed_updates_price_cumulatives s ∧
      pair_reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives s := by
  intro h_action h_step
  have h_write :=
    closed_world_reserve_write_sets_reserves_to_balances
      action before after h_action h_step
  exact ⟨h_write.1, h_write.2,
    reserve_update_oracle_same_timestamp_keeps_price_cumulatives s,
    reserve_update_oracle_elapsed_updates_price_cumulatives s,
    reserve_update_oracle_inactive_elapsed_keeps_price_cumulatives s⟩

-- tama: discharges=pair_mint_first_success_run_uses_oracle_rule
theorem mint_first_success_run_uses_oracle_rule
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_uses_oracle_rule toAddr s
    ((mint toAddr).run s) := by
  dsimp [pair_mint_first_success_run_uses_oracle_rule]
  intro _h_run h_success h_unlocked h_supply_zero h_bound0 h_bound1
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_product h_root
  have h_step :=
    mint_first_success_run_refines_closed_world toAddr s
      rfl h_success h_unlocked h_supply_zero h_bound0 h_bound1
      h_reserve0 h_reserve1 h_amount0 h_amount1 h_product h_root
  have h_action :
      ((∃ amount0 amount1 liquidity,
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val =
            PairWorldAction.mint amount0 amount1 liquidity) ∨
        (∃ amount0 amount1 liquidity,
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val =
            PairWorldAction.burn amount0 amount1 liquidity) ∨
        (∃ amount0In amount1In amount0Out amount1Out,
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val =
            PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
        PairWorldAction.mint
            (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val =
          PairWorldAction.sync) := by
    left
    exact ⟨(mintAmount0 s).val, (mintAmount1 s).val,
      (mintFirstLiquidity s).val, rfl⟩
  exact reserve_write_step_uses_oracle_rule
    (PairWorldAction.mint
      (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val)
    (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s) s h_action h_step

-- tama: discharges=pair_mint_first_success_run_uses_oracle_rule_from_run
theorem mint_first_success_run_uses_oracle_rule_from_run
    (toAddr : Address) (s : ContractState) :
  pair_mint_first_success_run_uses_oracle_rule_from_run toAddr s
    ((mint toAddr).run s) := by
  dsimp [pair_mint_first_success_run_uses_oracle_rule_from_run]
  intro _h_run h_success h_supply_zero h_reserve0 h_reserve1
    h_amount0 h_amount1 h_product h_root
  have h_step :=
    mint_first_success_run_refines_closed_world_from_run toAddr s
      rfl h_success h_supply_zero h_reserve0 h_reserve1
      h_amount0 h_amount1 h_product h_root
  have h_action :
      ((∃ amount0 amount1 liquidity,
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val =
            PairWorldAction.mint amount0 amount1 liquidity) ∨
        (∃ amount0 amount1 liquidity,
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val =
            PairWorldAction.burn amount0 amount1 liquidity) ∨
        (∃ amount0In amount1In amount0Out amount1Out,
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val =
            PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
        PairWorldAction.mint
            (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val =
          PairWorldAction.sync) := by
    left
    exact ⟨(mintAmount0 s).val, (mintAmount1 s).val,
      (mintFirstLiquidity s).val, rfl⟩
  exact reserve_write_step_uses_oracle_rule
    (PairWorldAction.mint
      (mintAmount0 s).val (mintAmount1 s).val (mintFirstLiquidity s).val)
    (pairWorldBeforeMintRun s) (pairWorldAfterFirstMintRun s) s h_action h_step

-- tama: discharges=pair_mint_subsequent_success_run_uses_oracle_rule
theorem mint_subsequent_success_run_uses_oracle_rule
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  pair_mint_subsequent_success_run_uses_oracle_rule
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_bound0 h_bound1 h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity
    h_ratio0 h_ratio1
  have h_step :=
    mint_subsequent_success_run_refines_closed_world
      toAddr s liquidity rfl h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_bound0 h_bound1 h_reserve0 h_reserve1 h_amount0
      h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_action :
      ((∃ amount0 amount1 liquidity',
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val liquidity.val =
            PairWorldAction.mint amount0 amount1 liquidity') ∨
        (∃ amount0 amount1 liquidity',
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val liquidity.val =
            PairWorldAction.burn amount0 amount1 liquidity') ∨
        (∃ amount0In amount1In amount0Out amount1Out,
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val liquidity.val =
            PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
        PairWorldAction.mint
            (mintAmount0 s).val (mintAmount1 s).val liquidity.val =
          PairWorldAction.sync) := by
    left
    exact ⟨(mintAmount0 s).val, (mintAmount1 s).val, liquidity.val, rfl⟩
  exact reserve_write_step_uses_oracle_rule
    (PairWorldAction.mint
      (mintAmount0 s).val (mintAmount1 s).val liquidity.val)
    (pairWorldBeforeMintRun s) (pairWorldAfterSubsequentMintRun liquidity s)
    s h_action h_step

-- tama: discharges=pair_mint_subsequent_success_run_uses_oracle_rule_from_run
theorem mint_subsequent_success_run_uses_oracle_rule_from_run
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  pair_mint_subsequent_success_run_uses_oracle_rule_from_run
    toAddr s ((mint toAddr).run s) liquidity := by
  intro _h_run h_success h_supply_pos h_reserve0_pos h_reserve1_pos
    h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity h_ratio0 h_ratio1
  have h_step :=
    mint_subsequent_success_run_refines_closed_world_from_run
      toAddr s liquidity rfl h_success h_supply_pos h_reserve0_pos
      h_reserve1_pos h_reserve0 h_reserve1 h_amount0 h_amount1 h_liquidity
      h_ratio0 h_ratio1
  have h_action :
      ((∃ amount0 amount1 liquidity',
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val liquidity.val =
            PairWorldAction.mint amount0 amount1 liquidity') ∨
        (∃ amount0 amount1 liquidity',
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val liquidity.val =
            PairWorldAction.burn amount0 amount1 liquidity') ∨
        (∃ amount0In amount1In amount0Out amount1Out,
          PairWorldAction.mint
              (mintAmount0 s).val (mintAmount1 s).val liquidity.val =
            PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
        PairWorldAction.mint
            (mintAmount0 s).val (mintAmount1 s).val liquidity.val =
          PairWorldAction.sync) := by
    left
    exact ⟨(mintAmount0 s).val, (mintAmount1 s).val, liquidity.val, rfl⟩
  exact reserve_write_step_uses_oracle_rule
    (PairWorldAction.mint
      (mintAmount0 s).val (mintAmount1 s).val liquidity.val)
    (pairWorldBeforeMintRun s) (pairWorldAfterSubsequentMintRun liquidity s)
    s h_action h_step

-- tama: discharges=pair_burn_success_run_uses_oracle_rule
theorem burn_success_run_uses_oracle_rule
    (toAddr : Address) (s : ContractState) :
  pair_burn_success_run_uses_oracle_rule toAddr s ((burn toAddr).run s) := by
  intro _h_run h_success h_liquidity_pos h_supply_pos h_liquidity_le
    h_locked_remaining h_amount0 h_amount1 h_amount0_le h_amount1_le h_bound0
    h_bound1 h_ratio0 h_ratio1
  have h_step :=
    burn_success_run_refines_closed_world toAddr s rfl h_success
      h_liquidity_pos h_supply_pos h_liquidity_le h_locked_remaining
      h_amount0 h_amount1 h_amount0_le h_amount1_le h_bound0 h_bound1
      h_ratio0 h_ratio1
  have h_action :
      ((∃ amount0 amount1 liquidity,
          PairWorldAction.burn
              (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val =
            PairWorldAction.mint amount0 amount1 liquidity) ∨
        (∃ amount0 amount1 liquidity,
          PairWorldAction.burn
              (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val =
            PairWorldAction.burn amount0 amount1 liquidity) ∨
        (∃ amount0In amount1In amount0Out amount1Out,
          PairWorldAction.burn
              (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val =
            PairWorldAction.swap amount0In amount1In amount0Out amount1Out) ∨
        PairWorldAction.burn
            (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val =
          PairWorldAction.sync) := by
    right
    left
    exact ⟨(burnAmount0 s).val, (burnAmount1 s).val, (burnLiquidity s).val, rfl⟩
  exact reserve_write_step_uses_oracle_rule
    (PairWorldAction.burn
      (burnAmount0 s).val (burnAmount1 s).val (burnLiquidity s).val)
    (pairWorldFromConcreteState s) (pairWorldAfterBurnRun s) s h_action h_step

-- tama: discharges=pair_swap_success_run_uses_oracle_rule
theorem swap_success_run_uses_oracle_rule
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_uses_oracle_rule
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run h_success h_output h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  have h_step :=
    swap_success_run_refines_closed_world
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      rfl h_success h_output h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  have h_action :
      ((∃ amount0 amount1 liquidity,
          PairWorldAction.swap
              (swapAmount0In amount0Out balance0Now s).val
              (swapAmount1In amount1Out balance1Now s).val
              amount0Out.val amount1Out.val =
            PairWorldAction.mint amount0 amount1 liquidity) ∨
        (∃ amount0 amount1 liquidity,
          PairWorldAction.swap
              (swapAmount0In amount0Out balance0Now s).val
              (swapAmount1In amount1Out balance1Now s).val
              amount0Out.val amount1Out.val =
            PairWorldAction.burn amount0 amount1 liquidity) ∨
        (∃ amount0In amount1In amount0Out' amount1Out',
          PairWorldAction.swap
              (swapAmount0In amount0Out balance0Now s).val
              (swapAmount1In amount1Out balance1Now s).val
              amount0Out.val amount1Out.val =
            PairWorldAction.swap amount0In amount1In amount0Out' amount1Out') ∨
        PairWorldAction.swap
            (swapAmount0In amount0Out balance0Now s).val
            (swapAmount1In amount1Out balance1Now s).val
            amount0Out.val amount1Out.val =
          PairWorldAction.sync) := by
    right
    right
    left
    exact ⟨(swapAmount0In amount0Out balance0Now s).val,
      (swapAmount1In amount1Out balance1Now s).val,
      amount0Out.val, amount1Out.val, rfl⟩
  exact reserve_write_step_uses_oracle_rule
    (PairWorldAction.swap
      (swapAmount0In amount0Out balance0Now s).val
      (swapAmount1In amount1Out balance1Now s).val amount0Out.val amount1Out.val)
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s) s h_action h_step

-- tama: discharges=pair_swap_success_run_uses_oracle_rule_from_run
theorem swap_success_run_uses_oracle_rule_from_run
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  pair_swap_success_run_uses_oracle_rule_from_run
    amount0Out amount1Out toAddr data balance0Now balance1Now s
    ((swap amount0Out amount1Out toAddr data).run s) := by
  intro _h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
    h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  have h_step :=
    swap_success_run_refines_closed_world_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      rfl h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  have h_action :
      ((∃ amount0 amount1 liquidity,
          PairWorldAction.swap
              (swapAmount0In amount0Out balance0Now s).val
              (swapAmount1In amount1Out balance1Now s).val
              amount0Out.val amount1Out.val =
            PairWorldAction.mint amount0 amount1 liquidity) ∨
        (∃ amount0 amount1 liquidity,
          PairWorldAction.swap
              (swapAmount0In amount0Out balance0Now s).val
              (swapAmount1In amount1Out balance1Now s).val
              amount0Out.val amount1Out.val =
            PairWorldAction.burn amount0 amount1 liquidity) ∨
        (∃ amount0In amount1In amount0Out' amount1Out',
          PairWorldAction.swap
              (swapAmount0In amount0Out balance0Now s).val
              (swapAmount1In amount1Out balance1Now s).val
              amount0Out.val amount1Out.val =
            PairWorldAction.swap amount0In amount1In amount0Out' amount1Out') ∨
        PairWorldAction.swap
            (swapAmount0In amount0Out balance0Now s).val
            (swapAmount1In amount1Out balance1Now s).val
            amount0Out.val amount1Out.val =
          PairWorldAction.sync) := by
    right
    right
    left
    exact ⟨(swapAmount0In amount0Out balance0Now s).val,
      (swapAmount1In amount1Out balance1Now s).val,
      amount0Out.val, amount1Out.val, rfl⟩
  exact reserve_write_step_uses_oracle_rule
    (PairWorldAction.swap
      (swapAmount0In amount0Out balance0Now s).val
      (swapAmount1In amount1Out balance1Now s).val amount0Out.val amount1Out.val)
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s) s h_action h_step

-- tama: discharges=pair_closed_world_skim_or_sync_token_balance_value_never_increases
theorem closed_world_skim_or_sync_token_balance_value_never_increases
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_skim_or_sync_token_balance_value_never_increases
    action before after := by
  intro h_action h_good h_step
  rcases h_action with h_skim | h_sync
  · subst action
    exact closed_world_skim_token_balance_value_never_increases
      before after h_good h_step
  · subst action
    have h_value :=
      closed_world_sync_preserves_token_balance_value before before after h_step
    rw [h_value]

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

-- tama: discharges=pair_closed_world_sync_eliminates_surplus
theorem closed_world_sync_eliminates_surplus
    (before after : PairWorldState) :
  pair_closed_world_sync_eliminates_surplus before after := by
  intro h_step
  have h_sync := closed_world_sync_sets_reserves_to_balances before after h_step
  unfold PairWorldSurplus0 PairWorldSurplus1
  rw [h_sync.2.2.1, h_sync.1, h_sync.2.2.2, h_sync.2.1]
  exact ⟨Nat.sub_self before.balance0, Nat.sub_self before.balance1⟩

-- tama: discharges=pair_closed_world_sync_preserves_liquidity_supply
theorem closed_world_sync_preserves_liquidity_supply
    (before after : PairWorldState) :
  pair_closed_world_sync_preserves_liquidity_supply before after := by
  intro h_step
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
    _h_reserve0, _h_reserve1, h_supply, h_locked⟩
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_sync_success_run_preserves_liquidity_supply_from_run
theorem sync_success_run_preserves_liquidity_supply_from_run
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_preserves_liquidity_supply_from_run s result := by
  intro h_run h_success
  have h_step :=
    sync_success_run_refines_closed_world_from_run s result h_run h_success
  exact closed_world_sync_preserves_liquidity_supply
    (pairWorldFromConcreteState s) (pairWorldAfterSyncRun s) h_step

-- tama: discharges=pair_sync_success_run_updates_reserves_to_balances_from_run
theorem sync_success_run_updates_reserves_to_balances_from_run
    (s : ContractState) (result : ContractResult Unit) :
  pair_sync_success_run_updates_reserves_to_balances_from_run s result := by
  intro h_run h_success
  have h_step :=
    sync_success_run_refines_closed_world_from_run s result h_run h_success
  have h_sync :=
    closed_world_sync_sets_reserves_to_balances
      (pairWorldFromConcreteState s) (pairWorldAfterSyncRun s) h_step
  constructor
  · rw [h_sync.1, h_sync.2.2.1]
  · rw [h_sync.2.1, h_sync.2.2.2]

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

-- tama: discharges=pair_closed_world_sync_preserves_k_without_surplus
theorem closed_world_sync_preserves_k_without_surplus
    (before after : PairWorldState) :
  pair_closed_world_sync_preserves_k_without_surplus before after := by
  intro h_good h_step h_surplus0 h_surplus1
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
  have h_sync := closed_world_sync_sets_reserves_to_balances before after h_step
  have h_balance0 : before.balance0 = before.reserve0 := by
    unfold PairWorldSurplus0 at h_surplus0
    omega
  have h_balance1 : before.balance1 = before.reserve1 := by
    unfold PairWorldSurplus1 at h_surplus1
    omega
  unfold PairWorldK
  rw [h_sync.1, h_sync.2.1, h_balance0, h_balance1]

-- tama: discharges=pair_closed_world_sync_preserves_balanced_pool
theorem closed_world_sync_preserves_balanced_pool
    (before after : PairWorldState) :
  pair_closed_world_sync_preserves_balanced_pool before after := by
  intro h_good h_step h_surplus0 h_surplus1
  rcases h_good with ⟨h_back0, h_back1, _h_bound0, _h_bound1, _h_supply_good⟩
  have h_balance0_before : before.balance0 = before.reserve0 := by
    unfold PairWorldSurplus0 at h_surplus0
    omega
  have h_balance1_before : before.balance1 = before.reserve1 := by
    unfold PairWorldSurplus1 at h_surplus1
    omega
  have h_sync := closed_world_sync_sets_reserves_to_balances before after h_step
  simp [PairWorldStep, PairWorldSyncStep] at h_step
  rcases h_step with ⟨_h_bound0, _h_bound1, _h_balance0, _h_balance1,
    _h_reserve0, _h_reserve1, h_supply, h_locked⟩
  constructor
  · exact h_sync.2.2.1
  constructor
  · exact h_sync.2.2.2
  constructor
  · rw [h_sync.1, h_balance0_before]
  constructor
  · rw [h_sync.2.1, h_balance1_before]
  exact ⟨h_supply, h_locked⟩

-- tama: discharges=pair_closed_world_balanced_skim_or_sync_preserves_pool
theorem closed_world_balanced_skim_or_sync_preserves_pool
    (action : PairWorldAction) (before after : PairWorldState) :
  pair_closed_world_balanced_skim_or_sync_preserves_pool action before after := by
  intro h_action h_good h_step h_surplus0 h_surplus1
  rcases h_action with h_skim | h_sync
  · subst action
    exact closed_world_skim_preserves_balanced_pool
      before after h_good h_step h_surplus0 h_surplus1
  · subst action
    exact closed_world_sync_preserves_balanced_pool
      before after h_good h_step h_surplus0 h_surplus1

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

-- tama: discharges=pair_closed_world_balanced_skim_sync_path_preserves_pool
theorem closed_world_balanced_skim_sync_path_preserves_pool
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

-- tama: discharges=pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool
theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_pool before after := by
  exact pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool

-- tama: discharges=pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k
theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k
    (before after : PairWorldState) :
  pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_k before after := by
  intro h_good h_surplus0 h_surplus1 h_path
  rcases pairWorldLpBookkeepingSkimSyncPath_preserves_balanced_pool
      h_good h_surplus0 h_surplus1 h_path with
    ⟨_h_balance0, _h_balance1, h_reserve0, h_reserve1, _h_supply, _h_locked⟩
  simp [PairWorldK, h_reserve0, h_reserve1]

-- tama: discharges=pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus
theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_zero_surplus
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

-- tama: discharges=pair_closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value
theorem closed_world_balanced_lp_bookkeeping_skim_sync_path_preserves_token_balance_value
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

-- tama: discharges=pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
theorem closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    (before after : PairWorldState) :
  pair_closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    before after := by
  intro h_good h_path
  exact
    (pairWorldLpBookkeepingSkimSyncPath_token_balance_value_never_increases_at_spot
      (spot := before) h_good h_path).2

-- tama: discharges=pair_closed_world_reachable_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
theorem closed_world_reachable_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    (before after : PairWorldState) :
  pair_closed_world_reachable_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    before after := by
  intro h_reachable h_path
  exact closed_world_lp_bookkeeping_skim_sync_path_token_balance_value_never_increases
    before after (pairWorldReachable_good before h_reachable) h_path

-- tama: discharges=pair_closed_world_sync_k_increase_requires_surplus
theorem closed_world_sync_k_increase_requires_surplus
    (before after : PairWorldState) :
  pair_closed_world_sync_k_increase_requires_surplus before after := by
  intro h_good h_step h_increase
  by_cases h_surplus0 : PairWorldSurplus0 before = 0
  · by_cases h_surplus1 : PairWorldSurplus1 before = 0
    · have h_k :=
        closed_world_sync_preserves_k_without_surplus
          before after h_good h_step h_surplus0 h_surplus1
      rw [h_k] at h_increase
      omega
    · exact Or.inr (Nat.pos_of_ne_zero h_surplus1)
  · exact Or.inl (Nat.pos_of_ne_zero h_surplus0)

end TamaUniV2.Proof.UniswapV2PairProof
