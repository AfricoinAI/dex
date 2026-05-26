import TamaUniV2.Proof.UniswapV2PairProof.Bridges.Common
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
theorem swap_success_run_implies_lock_open
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

private theorem finishSwapChecked_preserves_state_raw
    (sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out : Uint256) :
    contractPreservesState
      (UniswapV2PairBase.finishSwapChecked sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out) := by
  unfold UniswapV2PairBase.finishSwapChecked
  by_cases h_balance0 :
      balance0Now > sub reserve0Value amount0Out
  · rw [if_pos h_balance0]
    apply contractPreservesState_bind
    · exact contractPreservesState_pure PUnit.unit
    · intro _
      dsimp only
      by_cases h_balance1 :
          balance1Now > sub reserve1Value amount1Out
      · rw [if_pos h_balance1]
        apply contractPreservesState_bind
        · exact contractPreservesState_pure PUnit.unit
        · intro _
          repeat
            first
            | apply contractPreservesState_bind
            | intro _
            | exact contractPreservesState_require _ _ _
            | exact contractPreservesState_pure _ _
            | exact contractPreservesState_require _ _
            | exact contractPreservesState_pure _
      · rw [if_neg h_balance1]
        apply contractPreservesState_bind
        · exact contractPreservesState_pure ()
        · intro _
          repeat
            first
            | apply contractPreservesState_bind
            | intro _
            | exact contractPreservesState_require _ _ _
            | exact contractPreservesState_pure _ _
            | exact contractPreservesState_require _ _
            | exact contractPreservesState_pure _
  · rw [if_neg h_balance0]
    apply contractPreservesState_bind
    · exact contractPreservesState_pure ()
    · intro _
      dsimp only
      by_cases h_balance1 :
          balance1Now > sub reserve1Value amount1Out
      · rw [if_pos h_balance1]
        apply contractPreservesState_bind
        · exact contractPreservesState_pure PUnit.unit
        · intro _
          repeat
            first
            | apply contractPreservesState_bind
            | intro _
            | exact contractPreservesState_require _ _ _
            | exact contractPreservesState_pure _ _
            | exact contractPreservesState_require _ _
            | exact contractPreservesState_pure _
      · rw [if_neg h_balance1]
        apply contractPreservesState_bind
        · exact contractPreservesState_pure ()
        · intro _
          repeat
            first
            | apply contractPreservesState_bind
            | intro _
            | exact contractPreservesState_require _ _ _
            | exact contractPreservesState_pure _ _
            | exact contractPreservesState_require _ _
            | exact contractPreservesState_pure _

theorem finishSwapChecked_preserves_storage
    (sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out : Uint256)
    (s : ContractState) (slotIdx : Nat) :
    ((UniswapV2PairBase.finishSwapChecked sender
      balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out).run s).snd.storage slotIdx = s.storage slotIdx := by
  rw [contractPreservesState_run_snd]
  exact finishSwapChecked_preserves_state_raw sender
    balance0Now balance1Now reserve0Value reserve1Value amount0Out amount1Out

theorem finishSwapUpdate_run_storage_matches_world
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (original s : ContractState) (result : ContractResult Unit) :
  result =
      (UniswapV2PairBase.finishSwapUpdate sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out toAddr
        timestamp32 previousTimestamp).run s →
    result = ContractResult.success () result.snd →
      s.storage totalSupplySlot.slot = original.storage totalSupplySlot.slot →
    pairConcreteStorageMatchesWorld
      result.snd
      (pairWorldAfterSwapRun balance0Now balance1Now original) := by
  intro h_run h_success h_supply
  have h_success_run :
      (UniswapV2PairBase.finishSwapUpdate sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out toAddr
        timestamp32 previousTimestamp).run s =
        ContractResult.success () result.snd := by
    rw [← h_run]
    exact h_success
  let preUpdateState := (Contracts.mstore (64 : Uint256) (128 : Uint256) s).snd
  have h_mstore :
      Contracts.mstore (64 : Uint256) (128 : Uint256) s =
        ContractResult.success () preUpdateState := by
    rfl
  have h_pre_supply :
      preUpdateState.storage totalSupplySlot.slot = original.storage totalSupplySlot.slot := by
    dsimp only [preUpdateState]
    rw [← h_supply]
    rfl
  have h_update_storage :
      pairConcreteStorageMatchesWorld
        ((UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
          reserve0Value reserve1Value timestamp32 previousTimestamp).run preUpdateState).snd
        (pairWorldAfterSwapRun balance0Now balance1Now original) := by
    apply updateReservesAndEmitSync_run_storage_matches_world
    · simp only [pairWorldAfterSwapRun]
    · simp only [pairWorldAfterSwapRun]
    · change (original.storage totalSupplySlot.slot).val =
        (preUpdateState.storage totalSupplySlot.slot).val
      rw [h_pre_supply]
    · change pairWorldLockedLiquidity (original.storage totalSupplySlot.slot) =
        pairWorldLockedLiquidity (preUpdateState.storage totalSupplySlot.slot)
      rw [h_pre_supply]
  cases h_update_case :
      (UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
        reserve0Value reserve1Value timestamp32 previousTimestamp) preUpdateState with
  | success _ postUpdate =>
      unfold Contract.run at h_update_storage
      rw [h_update_case] at h_update_storage
      simp only [ContractResult.snd] at h_update_storage
      rw [h_run]
      unfold UniswapV2PairBase.finishSwapUpdate Contract.run at h_success_run ⊢
      dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure] at h_success_run ⊢
      simpa only [h_mstore, h_update_case, pairConcreteStorageMatchesWorld,
        ContractResult.snd, Contracts.emit, emitEvent, setStorage,
        reserve0Slot, reserve1Slot, totalSupplySlot, unlockedSlot,
        UniswapV2PairBase.unlockedSlot, pairWorldAfterSwapRun] using
        h_update_storage
  | «revert» reason postUpdate =>
      have h_impossible : False := by
        unfold UniswapV2PairBase.finishSwapUpdate Contract.run at h_success_run
        dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure] at h_success_run
        simp only [h_mstore, h_update_case, ContractResult.snd] at h_success_run
        cases h_success_run
      cases h_impossible

theorem finishSwap_run_storage_matches_world
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (original s : ContractState) (result : ContractResult Unit) :
  result =
      (UniswapV2PairBase.finishSwap sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out toAddr timestamp32 previousTimestamp).run s →
    result = ContractResult.success () result.snd →
      s.storage totalSupplySlot.slot = original.storage totalSupplySlot.slot →
  pairConcreteStorageMatchesWorld
      result.snd
      (pairWorldAfterSwapRun balance0Now balance1Now original) := by
  intro h_run h_success h_supply
  have h_success_run :
      (UniswapV2PairBase.finishSwap sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out toAddr timestamp32 previousTimestamp).run s =
        ContractResult.success () result.snd := by
    rw [← h_run]
    exact h_success
  cases h_checked_case :
      (UniswapV2PairBase.finishSwapChecked sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out) s with
  | success amounts checkedState =>
      have h_checked_state : checkedState = s := by
        have h_preserved :=
          finishSwapChecked_preserves_state_raw sender
            balance0Now balance1Now reserve0Value reserve1Value
            amount0Out amount1Out s
        rw [h_checked_case] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst checkedState
      rcases amounts with ⟨amount0In, amount1In⟩
      have h_update_run :
          result =
            (UniswapV2PairBase.finishSwapUpdate sender
              balance0Now balance1Now reserve0Value reserve1Value
              amount0In amount1In amount0Out amount1Out toAddr
              timestamp32 previousTimestamp).run s := by
        rw [h_run]
        unfold UniswapV2PairBase.finishSwap Contract.run
        dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure]
        rw [h_checked_case]
      exact finishSwapUpdate_run_storage_matches_world sender toAddr
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp
        original s result h_update_run h_success h_supply
  | «revert» reason checkedState =>
      have h_impossible : False := by
        unfold UniswapV2PairBase.finishSwap Contract.run at h_success_run
        dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure] at h_success_run
        rw [h_checked_case] at h_success_run
        cases h_success_run
      cases h_impossible

private theorem pairSafeTransfer_snd_storage
    (token toAddr : Address) (amount : Uint256) (s : ContractState) (idx : Nat) :
  (((TamaUniV2.pairSafeTransfer token toAddr amount) s).snd).storage idx =
    s.storage idx := by
  simp [TamaUniV2.pairSafeTransfer, Contracts.safeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, Bind.bind, Verity.bind,
    Pure.pure, Verity.pure]

private theorem pairSafeTransfer_snd_storageAddr
    (token toAddr : Address) (amount : Uint256) (s : ContractState) (idx : Nat) :
  (((TamaUniV2.pairSafeTransfer token toAddr amount) s).snd).storageAddr idx =
    s.storageAddr idx := by
  simp [TamaUniV2.pairSafeTransfer, Contracts.safeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, Bind.bind, Verity.bind,
    Pure.pure, Verity.pure]

private theorem pairSafeTransfer_snd_thisAddress
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
  (((TamaUniV2.pairSafeTransfer token toAddr amount) s).snd).thisAddress =
    s.thisAddress := by
  simp [TamaUniV2.pairSafeTransfer, Contracts.safeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, Bind.bind, Verity.bind,
    Pure.pure, Verity.pure]

private theorem uniswapV2Callback_snd_storage
    (toAddr sender : Address) (amount0Out amount1Out : Uint256)
    (s : ContractState) (idx : Nat) :
  (((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out] :
        Contract Unit) s).snd).storage idx =
    s.storage idx := by
  rfl

private theorem uniswapV2Callback_snd_storageAddr
    (toAddr sender : Address) (amount0Out amount1Out : Uint256)
    (s : ContractState) (idx : Nat) :
  (((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out] :
        Contract Unit) s).snd).storageAddr idx =
    s.storageAddr idx := by
  rfl

private theorem uniswapV2Callback_snd_thisAddress
    (toAddr sender : Address) (amount0Out amount1Out : Uint256)
    (s : ContractState) :
  (((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out] :
        Contract Unit) s).snd).thisAddress =
    s.thisAddress := by
  rfl

private theorem pairTransfersAfterCall_eq_nil_of_snd_eq {α : Type}
    (s : ContractState) (result : ContractResult α)
    (h_snd : result.snd = s) :
  pairTransfersAfterCall s result = [] := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    h_snd]

theorem finishSwapChecked_pairTransfers
    (sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.finishSwapChecked sender
      balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out).run s) = [] := by
  apply pairTransfersAfterCall_eq_nil_of_snd_eq
  exact contractPreservesState_run_snd
    (UniswapV2PairBase.finishSwapChecked sender
      balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out)
    (finishSwapChecked_preserves_state_raw sender
      balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out) s

theorem finishSwapUpdate_pairTransfers
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.finishSwapUpdate sender
      balance0Now balance1Now reserve0Value reserve1Value
      amount0In amount1In amount0Out amount1Out toAddr timestamp32
      previousTimestamp).run s) = [] := by
  have h_update_transfers :=
    updateReservesAndEmitSync_pairTransfers balance0Now balance1Now
      reserve0Value reserve1Value timestamp32 previousTimestamp s
  unfold UniswapV2PairBase.finishSwapUpdate Contract.run
  dsimp only [Contracts.mstore, Pure.pure, Verity.pure, Bind.bind, Verity.bind]
  cases h_update :
      UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
        reserve0Value reserve1Value timestamp32 previousTimestamp s with
  | success value postUpdate =>
      have h_update_transfers' :
          pairTransfersAfterEvents (List.drop s.events.length postUpdate.events) = [] := by
        simpa [pairTransfersAfterCall, emittedPairEventsAfterCall, Contract.run,
          h_update] using h_update_transfers
      unfold pairTransfersAfterEvents at h_update_transfers'
      unfold pairTransfersAfterCall emittedPairEventsAfterCall pairTransfersAfterEvents
      simp [h_update, Contracts.emit, emitEvent, setStorage]
      rw [List.drop_append]
      rw [List.filterMap_eq_nil_iff] at h_update_transfers'
      intro event h_event
      rw [List.mem_append] at h_event
      rcases h_event with h_event | h_event
      · exact h_update_transfers' event h_event
      · have h_event_eq :
            event =
              { name := "Swap",
                args :=
                  [addressToWord sender, amount0In, amount1In, amount0Out,
                    amount1Out, addressToWord toAddr],
                indexedArgs := [] } := by
          simpa using (List.mem_of_mem_drop h_event)
        rw [h_event_eq]
        simp [pairTransferOfEvent]
  | «revert» reason postUpdate =>
      simpa [pairTransfersAfterCall, emittedPairEventsAfterCall,
        pairTransfersAfterEvents, Contract.run, h_update] using h_update_transfers

theorem finishSwap_pairTransfers
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.finishSwap sender
      balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out toAddr timestamp32 previousTimestamp).run s) = [] := by
  unfold UniswapV2PairBase.finishSwap Contract.run
  dsimp only [Bind.bind, Verity.bind]
  cases h_checked :
      UniswapV2PairBase.finishSwapChecked sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out s with
  | success amounts checkedState =>
      have h_checked_state : checkedState = s := by
        have h_preserved :=
          finishSwapChecked_preserves_state_raw sender
            balance0Now balance1Now reserve0Value reserve1Value
            amount0Out amount1Out s
        rw [h_checked] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst checkedState
      rcases amounts with ⟨amount0In, amount1In⟩
      simpa [h_checked] using
        finishSwapUpdate_pairTransfers sender toAddr
          balance0Now balance1Now reserve0Value reserve1Value
          amount0In amount1In amount0Out amount1Out timestamp32
          previousTimestamp s
  | «revert» reason checkedState =>
      have h_checked_state : checkedState = s := by
        have h_preserved :=
          finishSwapChecked_preserves_state_raw sender
            balance0Now balance1Now reserve0Value reserve1Value
            amount0Out amount1Out s
        rw [h_checked] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst checkedState
      simp [h_checked, pairTransfersAfterCall, emittedPairEventsAfterCall,
        pairTransfersAfterEvents]

theorem uniswapV2Callback_pairTransfers
    (toAddr sender : Address) (amount0Out amount1Out : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    (((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out] :
        Contract Unit).run s)) = [] := by
  apply pairTransfersAfterCall_eq_nil_of_snd_eq
  rfl

theorem swapInteractionTail_pairTransfers
    (token0Value token1Value : Address)
    (reserve0Value reserve1Value amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (toAddr : Address) (s : ContractState) :
  pairTransfersAfterCall s
    (((do
      let sender ← msgSender
      ecmDo uniswapV2CallbackModule
        [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out]
      let selfAddr ← Verity.contractAddress
      let balance0Now ← TamaUniV2.erc20BalanceOf token0Value selfAddr
      let balance1Now ← TamaUniV2.erc20BalanceOf token1Value selfAddr
      UniswapV2PairBase.finishSwap sender balance0Now balance1Now
        reserve0Value reserve1Value amount0Out amount1Out toAddr timestamp32
        previousTimestamp) : Contract Unit).run s) = [] := by
  let balance0Now :=
    ((TamaUniV2.erc20BalanceOf token0Value s.thisAddress).run s).fst
  let balance1Now :=
    ((TamaUniV2.erc20BalanceOf token1Value s.thisAddress).run s).fst
  simpa [balance0Now, balance1Now, msgSender, Verity.contractAddress,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure] using
      finishSwap_pairTransfers s.sender toAddr balance0Now balance1Now
        reserve0Value reserve1Value amount0Out amount1Out timestamp32
        previousTimestamp s

private theorem contractAppendsEvents_finishSwapUpdate
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp : Uint256) :
    contractAppendsEvents
      (UniswapV2PairBase.finishSwapUpdate sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out toAddr timestamp32
        previousTimestamp) := by
  unfold UniswapV2PairBase.finishSwapUpdate
  repeat
    first
    | exact contractAppendsEvents_mstore _ _
    | exact contractAppendsEvents_updateReservesAndEmitSync _ _ _ _ _ _
    | exact contractAppendsEvents_emit _ _
    | exact contractAppendsEvents_setStorage _ _
    | apply contractAppendsEvents_bind
    | intro _

theorem finishSwapUpdate_run_events_append
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
    ∃ ev,
      ((UniswapV2PairBase.finishSwapUpdate sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out toAddr timestamp32
        previousTimestamp).run s).snd.events = s.events ++ ev :=
  contractAppendsEvents_finishSwapUpdate sender toAddr
    balance0Now balance1Now reserve0Value reserve1Value amount0In amount1In
    amount0Out amount1Out timestamp32 previousTimestamp s

theorem finishSwap_run_events_append
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
    ∃ ev,
      ((UniswapV2PairBase.finishSwap sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out toAddr timestamp32 previousTimestamp).run s).snd.events =
        s.events ++ ev := by
  unfold UniswapV2PairBase.finishSwap Contract.run
  dsimp only [Bind.bind, Verity.bind]
  cases h_checked :
      UniswapV2PairBase.finishSwapChecked sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out s with
  | success amounts checkedState =>
      have h_checked_state : checkedState = s := by
        have h_preserved :=
          finishSwapChecked_preserves_state_raw sender
            balance0Now balance1Now reserve0Value reserve1Value
            amount0Out amount1Out s
        rw [h_checked] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst checkedState
      rcases amounts with ⟨amount0In, amount1In⟩
      simpa [h_checked] using
        finishSwapUpdate_run_events_append sender toAddr
          balance0Now balance1Now reserve0Value reserve1Value
          amount0In amount1In amount0Out amount1Out timestamp32
          previousTimestamp s
  | «revert» reason checkedState =>
      have h_checked_state : checkedState = s := by
        have h_preserved :=
          finishSwapChecked_preserves_state_raw sender
            balance0Now balance1Now reserve0Value reserve1Value
            amount0Out amount1Out s
        rw [h_checked] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst checkedState
      exact ⟨[], by simp [h_checked]⟩

theorem swapInteractionTail_run_events_append
    (token0Value token1Value : Address)
    (reserve0Value reserve1Value amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (toAddr : Address) (s : ContractState) :
    ∃ ev,
      (((do
        let sender ← msgSender
        ecmDo uniswapV2CallbackModule
          [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out]
        let selfAddr ← Verity.contractAddress
        let balance0Now ← TamaUniV2.erc20BalanceOf token0Value selfAddr
        let balance1Now ← TamaUniV2.erc20BalanceOf token1Value selfAddr
        UniswapV2PairBase.finishSwap sender balance0Now balance1Now
          reserve0Value reserve1Value amount0Out amount1Out toAddr timestamp32
          previousTimestamp) : Contract Unit).run s).snd.events = s.events ++ ev := by
  let balance0Now :=
    ((TamaUniV2.erc20BalanceOf token0Value s.thisAddress).run s).fst
  let balance1Now :=
    ((TamaUniV2.erc20BalanceOf token1Value s.thisAddress).run s).fst
  simpa [balance0Now, balance1Now, msgSender, Verity.contractAddress,
    TamaUniV2.erc20BalanceOf, Contracts.balanceOf, Contract.run,
    ContractResult.snd, ContractResult.fst, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure] using
      finishSwap_run_events_append s.sender toAddr balance0Now balance1Now
        reserve0Value reserve1Value amount0Out amount1Out timestamp32
        previousTimestamp s

private theorem pure_run_events_append {α : Type} (a : α) (s : ContractState) :
    ∃ ev, ((Verity.pure a : Contract α).run s).snd.events = s.events ++ ev :=
  contractAppendsEvents_pure a s

private def swapInteractionTailContract
    (token0Value token1Value : Address)
    (reserve0Value reserve1Value amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (toAddr : Address) : Contract Unit := do
  let sender ← msgSender
  ecmDo uniswapV2CallbackModule
    [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out]
  let selfAddr ← Verity.contractAddress
  let balance0Now ← TamaUniV2.erc20BalanceOf token0Value selfAddr
  let balance1Now ← TamaUniV2.erc20BalanceOf token1Value selfAddr
  UniswapV2PairBase.finishSwap sender balance0Now balance1Now
    reserve0Value reserve1Value amount0Out amount1Out toAddr timestamp32
    previousTimestamp

private theorem swapInteractionTailContract_pairTransfers
    (token0Value token1Value : Address)
    (reserve0Value reserve1Value amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (toAddr : Address) (s : ContractState) :
  pairTransfersAfterCall s
    ((swapInteractionTailContract token0Value token1Value reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp toAddr).run s) = [] := by
  unfold swapInteractionTailContract
  exact swapInteractionTail_pairTransfers token0Value token1Value reserve0Value
    reserve1Value amount0Out amount1Out timestamp32 previousTimestamp toAddr s

private theorem contractAppendsEvents_swapInteractionTailContract
    (token0Value token1Value : Address)
    (reserve0Value reserve1Value amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (toAddr : Address) :
  contractAppendsEvents
    (swapInteractionTailContract token0Value token1Value reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp toAddr) := by
  intro s
  unfold swapInteractionTailContract
  exact swapInteractionTail_run_events_append token0Value token1Value reserve0Value
    reserve1Value amount0Out amount1Out timestamp32 previousTimestamp toAddr s

private theorem pairSafeTransfer_run_success
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
  (TamaUniV2.pairSafeTransfer token toAddr amount).run s =
    ContractResult.success 1
      ((TamaUniV2.pairSafeTransfer token toAddr amount).run s).snd := by
  unfold TamaUniV2.pairSafeTransfer
  simp [Contract.run, Contracts.safeTransfer, TamaUniV2.tracePairTokenSafeTransfer,
    TamaUniV2.pairTokenSafeTransferEvent, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, ContractResult.snd]

private theorem contractAppendsEvents_pure_then {β : Type} (tail : Contract β)
    (h_tail : contractAppendsEvents tail) :
  contractAppendsEvents
    ((do
      (Verity.pure () : Contract Unit)
      tail) : Contract β) := by
  apply contractAppendsEvents_bind
  · exact contractAppendsEvents_pure ()
  · intro _
    exact h_tail

private theorem contractAppendsEvents_safeTransfer_pure_then {β : Type}
    (token toAddr : Address) (amount : Uint256) (tail : Contract β)
    (h_tail : contractAppendsEvents tail) :
  contractAppendsEvents
    ((do
      let _ ← TamaUniV2.pairSafeTransfer token toAddr amount
      (Verity.pure () : Contract Unit)
      tail) : Contract β) := by
  apply contractAppendsEvents_bind
  · exact contractAppendsEvents_pairSafeTransfer token toAddr amount
  · intro _
    exact contractAppendsEvents_pure_then tail h_tail

private theorem pairTransfersAfterCall_safeTransfer_pure_then
    (token toAddr : Address) (amount : Uint256) (tail : Contract Unit)
    (s : ContractState)
    (h_success :
      ((do
        let _ ← TamaUniV2.pairSafeTransfer token toAddr amount
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit).run s =
        ContractResult.success ()
          (((do
            let _ ← TamaUniV2.pairSafeTransfer token toAddr amount
            (Verity.pure () : Contract Unit)
            tail) : Contract Unit).run s).snd)
    (h_tail : contractAppendsEvents tail) :
  pairTransfersAfterCall s
      (((do
        let _ ← TamaUniV2.pairSafeTransfer token toAddr amount
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit).run s) =
    { token := token, fromAddr := pairSelf s, toAddr := toAddr, amount := amount } ::
      pairTransfersAfterCall
        ((TamaUniV2.pairSafeTransfer token toAddr amount).run s).snd
        (tail.run ((TamaUniV2.pairSafeTransfer token toAddr amount).run s).snd) := by
  let mid := ((TamaUniV2.pairSafeTransfer token toAddr amount).run s).snd
  have hx :
      (TamaUniV2.pairSafeTransfer token toAddr amount).run s =
        ContractResult.success 1 mid := by
    dsimp only [mid]
    exact pairSafeTransfer_run_success token toAddr amount s
  have h_cont_success :
      (((do
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit).run mid) =
        ContractResult.success ()
          (((do
            let _ ← TamaUniV2.pairSafeTransfer token toAddr amount
            (Verity.pure () : Contract Unit)
            tail) : Contract Unit).run s).snd := by
    exact run_success_bind_peel
      (TamaUniV2.pairSafeTransfer token toAddr amount)
      (fun _ => ((do
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit))
      s mid
      (((do
        let _ ← TamaUniV2.pairSafeTransfer token toAddr amount
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit).run s).snd
      1 () hx h_success
  have h_cont_appends :
      contractAppendsEvents
        ((do
          (Verity.pure () : Contract Unit)
          tail) : Contract Unit) :=
    contractAppendsEvents_pure_then tail h_tail
  rcases h_cont_appends mid with ⟨evCont, hevCont⟩
  have h_cont_success_self :
      (((do
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit).run mid) =
        ContractResult.success ()
          (((do
            (Verity.pure () : Contract Unit)
            tail) : Contract Unit).run mid).snd := by
    rw [h_cont_success]
    rfl
  have h_post_ev :
      ((((do
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit).run mid)).snd.events =
        mid.events ++ emittedPairEventsAfterCall mid
          (((do
            (Verity.pure () : Contract Unit)
            tail) : Contract Unit).run mid) :=
    run_success_events_extend_of_append
      ((do
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit)
      mid _
      () h_cont_success_self evCont hevCont
  rcases pairSafeTransfer_run_events_append token toAddr amount s with
    ⟨evXfer, hevXfer⟩
  rw [pairTransfersAfterCall_bind_safeTransfer token toAddr amount
    (fun _ => ((do
      (Verity.pure () : Contract Unit)
      tail) : Contract Unit))
    s mid hx
    ⟨(), _, h_cont_success⟩
    (run_success_events_extend_of_append
      (TamaUniV2.pairSafeTransfer token toAddr amount)
      s mid 1 hx evXfer hevXfer)
    h_post_ev]
  rw [pairTransfersAfterCall_bind_no_event
    (Verity.pure () : Contract Unit) (fun _ => tail)
    mid mid () rfl rfl]

private def swapConditionalTransfersAndTail
    (token0Value token1Value : Address)
    (reserve0Value reserve1Value amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (toAddr : Address) : Contract Unit := do
  if amount0Out > 0 then
    let _ ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out
    (Verity.pure () : Contract Unit)
  else
    (Verity.pure () : Contract Unit)
  if amount1Out > 0 then
    let _ ← TamaUniV2.pairSafeTransfer token1Value toAddr amount1Out
    (Verity.pure () : Contract Unit)
  else
    (Verity.pure () : Contract Unit)
  swapInteractionTailContract token0Value token1Value reserve0Value reserve1Value
    amount0Out amount1Out timestamp32 previousTimestamp toAddr

private theorem swapConditionalTransfersAndTail_pairTransfers
    (token0Value token1Value : Address)
    (reserve0Value reserve1Value amount0Out amount1Out timestamp32 previousTimestamp : Uint256)
    (toAddr : Address) (s : ContractState)
    (h_success :
      (swapConditionalTransfersAndTail token0Value token1Value reserve0Value reserve1Value
        amount0Out amount1Out timestamp32 previousTimestamp toAddr).run s =
        ContractResult.success ()
          ((swapConditionalTransfersAndTail token0Value token1Value reserve0Value reserve1Value
            amount0Out amount1Out timestamp32 previousTimestamp toAddr).run s).snd) :
  pairTransfersAfterCall s
      ((swapConditionalTransfersAndTail token0Value token1Value reserve0Value reserve1Value
        amount0Out amount1Out timestamp32 previousTimestamp toAddr).run s) =
    (if amount0Out > 0 then
      [{ token := token0Value, fromAddr := pairSelf s, toAddr := toAddr,
         amount := amount0Out }]
    else []) ++
    (if amount1Out > 0 then
      [{ token := token1Value, fromAddr := pairSelf s, toAddr := toAddr,
         amount := amount1Out }]
    else []) := by
  let tail :=
    swapInteractionTailContract token0Value token1Value reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp toAddr
  have h_tail_appends : contractAppendsEvents tail := by
    dsimp only [tail]
    exact contractAppendsEvents_swapInteractionTailContract token0Value token1Value
      reserve0Value reserve1Value amount0Out amount1Out timestamp32 previousTimestamp toAddr
  by_cases h0 : amount0Out > 0 <;> by_cases h1 : amount1Out > 0
  · let rest1 : Contract Unit := do
      let _ ← TamaUniV2.pairSafeTransfer token1Value toAddr amount1Out
      (Verity.pure () : Contract Unit)
      tail
    have h_rest1_appends : contractAppendsEvents rest1 := by
      dsimp only [rest1]
      exact contractAppendsEvents_safeTransfer_pure_then token1Value toAddr amount1Out
        tail h_tail_appends
    simp only [swapConditionalTransfersAndTail, if_pos h0, if_pos h1, tail] at h_success ⊢
    let mid0 := ((TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out).run s).snd
    have hx0 :
        (TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out).run s =
          ContractResult.success 1 mid0 := by
      dsimp only [mid0]
      exact pairSafeTransfer_run_success token0Value toAddr amount0Out s
    have h_mid0_this : mid0.thisAddress = s.thisAddress := by
      simp [mid0, Contract.run, TamaUniV2.pairSafeTransfer,
        Contracts.safeTransfer, TamaUniV2.tracePairTokenSafeTransfer,
        Bind.bind, Verity.bind, Pure.pure, Verity.pure]
    have h_cont0_success :
        (((do
          (Verity.pure () : Contract Unit)
          rest1) : Contract Unit).run mid0) =
          ContractResult.success ()
            (((do
              let _ ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out
              (Verity.pure () : Contract Unit)
              rest1) : Contract Unit).run s).snd := by
      exact run_success_bind_peel
        (TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out)
        (fun _ => ((do
          (Verity.pure () : Contract Unit)
          rest1) : Contract Unit))
        s mid0
        (((do
          let _ ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out
          (Verity.pure () : Contract Unit)
          rest1) : Contract Unit).run s).snd
        1 () hx0 h_success
    have h_rest1_success_raw :
        rest1.run mid0 =
          ContractResult.success ()
            (((do
              let _ ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out
              (Verity.pure () : Contract Unit)
              rest1) : Contract Unit).run s).snd := by
      exact run_success_bind_peel
        (Verity.pure () : Contract Unit) (fun _ => rest1)
        mid0 mid0
        (((do
          let _ ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out
          (Verity.pure () : Contract Unit)
          rest1) : Contract Unit).run s).snd
        () () rfl h_cont0_success
    have h_rest1_success :
        rest1.run mid0 = ContractResult.success () (rest1.run mid0).snd := by
      rw [h_rest1_success_raw]
      rfl
    rw [pairTransfersAfterCall_safeTransfer_pure_then token0Value toAddr amount0Out
      rest1 s h_success h_rest1_appends]
    rw [pairTransfersAfterCall_safeTransfer_pure_then token1Value toAddr amount1Out
      tail mid0 h_rest1_success h_tail_appends]
    simp [swapInteractionTailContract_pairTransfers, tail, List.singleton_append,
      pairSelf, h_mid0_this]
  · simp only [swapConditionalTransfersAndTail, if_pos h0, if_neg h1, tail] at h_success ⊢
    let tailWithPure : Contract Unit := do
      (Verity.pure () : Contract Unit)
      tail
    have h_tailWithPure_appends : contractAppendsEvents tailWithPure := by
      dsimp only [tailWithPure]
      exact contractAppendsEvents_pure_then tail h_tail_appends
    have h_success' :
        ((do
          let _ ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out
          (Verity.pure () : Contract Unit)
          tailWithPure) : Contract Unit).run s =
          ContractResult.success ()
            (((do
              let _ ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out
              (Verity.pure () : Contract Unit)
              tailWithPure) : Contract Unit).run s).snd := by
      simpa [tailWithPure] using h_success
    rw [pairTransfersAfterCall_safeTransfer_pure_then token0Value toAddr amount0Out
      tailWithPure s h_success' h_tailWithPure_appends]
    rw [pairTransfersAfterCall_bind_no_event
      (Verity.pure () : Contract Unit) (fun _ => tail)
      ((TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out).run s).snd
      ((TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out).run s).snd
      () rfl rfl]
    simp [swapInteractionTailContract_pairTransfers, tail, tailWithPure]
  · let rest1 : Contract Unit := do
      let _ ← TamaUniV2.pairSafeTransfer token1Value toAddr amount1Out
      (Verity.pure () : Contract Unit)
      tail
    have h_rest1_appends : contractAppendsEvents rest1 := by
      dsimp only [rest1]
      exact contractAppendsEvents_safeTransfer_pure_then token1Value toAddr amount1Out
        tail h_tail_appends
    simp only [swapConditionalTransfersAndTail, if_neg h0, if_pos h1, tail] at h_success ⊢
    have h_rest1_success_raw :
        rest1.run s =
          ContractResult.success ()
            (((do
              (Verity.pure () : Contract Unit)
              rest1) : Contract Unit).run s).snd := by
      exact run_success_bind_peel
        (Verity.pure () : Contract Unit) (fun _ => rest1)
        s s
        (((do
          (Verity.pure () : Contract Unit)
          rest1) : Contract Unit).run s).snd
        () () rfl h_success
    have h_rest1_success :
        rest1.run s = ContractResult.success () (rest1.run s).snd := by
      rw [h_rest1_success_raw]
      rfl
    rw [pairTransfersAfterCall_bind_no_event
      (Verity.pure () : Contract Unit) (fun _ => rest1)
      s s () rfl rfl]
    rw [pairTransfersAfterCall_safeTransfer_pure_then token1Value toAddr amount1Out
      tail s h_rest1_success h_tail_appends]
    simp [swapInteractionTailContract_pairTransfers, tail]
  · simp only [swapConditionalTransfersAndTail, if_neg h0, if_neg h1, tail] at h_success ⊢
    rw [pairTransfersAfterCall_bind_no_event
      (Verity.pure () : Contract Unit)
      (fun _ => ((do
        (Verity.pure () : Contract Unit)
        tail) : Contract Unit))
      s s () rfl rfl]
    rw [pairTransfersAfterCall_bind_no_event
      (Verity.pure () : Contract Unit) (fun _ => tail)
      s s () rfl rfl]
    simp [swapInteractionTailContract_pairTransfers, tail]

theorem swap_success_pairTransfers
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState)
    (h_success :
      (swap amount0Out amount1Out toAddr data).run s =
        ContractResult.success () ((swap amount0Out amount1Out toAddr data).run s).snd) :
  pairTransfersAfterCall s ((swap amount0Out amount1Out toAddr data).run s) =
    (if amount0Out > 0 then
      [{ token := pairToken0 s, fromAddr := pairSelf s, toAddr := toAddr,
         amount := amount0Out }]
    else []) ++
    (if amount1Out > 0 then
      [{ token := pairToken1 s, fromAddr := pairSelf s, toAddr := toAddr,
         amount := amount1Out }]
    else []) := by
  have h_unlocked := swap_success_run_implies_lock_open amount0Out amount1Out
    toAddr data s ((swap amount0Out amount1Out toAddr data).run s) rfl h_success
  have h_nonzero := swap_success_run_implies_nonzero_output amount0Out amount1Out
    toAddr data s ((swap amount0Out amount1Out toAddr data).run s) rfl h_success
  have h_output : amount0Out > 0 ∨ amount1Out > 0 := by
    rcases h_nonzero with h_amount0 | h_amount1
    · exact Or.inl (uint256_pos_of_ne_zero h_amount0)
    · exact Or.inr (uint256_pos_of_ne_zero h_amount1)
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_output_guard : (amount0Out > 0 || amount1Out > 0) = true := by
    simpa [Bool.or_eq_true] using h_output
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_timestamp :
      Verity.blockTimestamp s = ContractResult.success s.blockTimestamp s := rfl
  have h_previous :
      getStorage UniswapV2PairBase.blockTimestampLastSlot s =
        ContractResult.success (s.storage blockTimestampLastSlot.slot) s := by
    simp only [getStorage, blockTimestampLastSlot, UniswapV2PairBase.blockTimestampLastSlot]
  have h_req_output :
      Verity.require (amount0Out > 0 || amount1Out > 0)
        "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT" s =
          ContractResult.success () s := by
    simp only [Verity.require, h_output_guard, if_true]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  have h_liq_guard :
      (amount0Out < s.storage reserve0Slot.slot &&
        amount1Out < s.storage reserve1Slot.slot) = true := by
    by_cases h_guard :
        (amount0Out < s.storage reserve0Slot.slot &&
          amount1Out < s.storage reserve1Slot.slot) = true
    · exact h_guard
    · exfalso
      have h_req_liq_false :
          Verity.require
              (amount0Out < s.storage reserve0Slot.slot &&
                amount1Out < s.storage reserve1Slot.slot)
              "UniswapV2: INSUFFICIENT_LIQUIDITY" (mintLockedState s) =
            ContractResult.revert "UniswapV2: INSUFFICIENT_LIQUIDITY"
              (mintLockedState s) := by
        simp only [Verity.require]
        rw [if_neg h_guard]
      have h_swap_liq :
          (swap amount0Out amount1Out toAddr data).run s =
            ContractResult.revert "UniswapV2: INSUFFICIENT_LIQUIDITY" s := by
        unfold swap UniswapV2PairBase.swap Contract.run
        rw [contract_bind_success _ _ _ _ _ h_get_lock]
        rw [contract_bind_success _ _ _ _ _ h_req_lock]
        rw [contract_bind_success _ _ _ _ _ h_timestamp]
        rw [contract_bind_success _ _ _ _ _ h_previous]
        rw [contract_bind_success _ _ _ _ _ h_req_output]
        rw [contract_bind_success _ _ _ _ _ h_set_lock]
        rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
        rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_req_liq_false]
      rw [h_swap_liq] at h_success
      cases h_success
  have h_req_liq :
      Verity.require
          (amount0Out < s.storage reserve0Slot.slot &&
            amount1Out < s.storage reserve1Slot.slot)
          "UniswapV2: INSUFFICIENT_LIQUIDITY" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_liq_guard, if_true]
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_to_guard :
      (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
        toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot) = true := by
    by_cases h_guard :
        (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
          toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot) = true
    · exact h_guard
    · exfalso
      have h_req_to_false :
          Verity.require
              (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
                toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
              "UniswapV2: INVALID_TO" (mintLockedState s) =
            ContractResult.revert "UniswapV2: INVALID_TO" (mintLockedState s) := by
        simp only [Verity.require]
        rw [if_neg h_guard]
      have h_swap_invalid :
          (swap amount0Out amount1Out toAddr data).run s =
            ContractResult.revert "UniswapV2: INVALID_TO" s := by
        unfold swap UniswapV2PairBase.swap Contract.run
        rw [contract_bind_success _ _ _ _ _ h_get_lock]
        rw [contract_bind_success _ _ _ _ _ h_req_lock]
        rw [contract_bind_success _ _ _ _ _ h_timestamp]
        rw [contract_bind_success _ _ _ _ _ h_previous]
        rw [contract_bind_success _ _ _ _ _ h_req_output]
        rw [contract_bind_success _ _ _ _ _ h_set_lock]
        rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
        rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
        rw [contract_bind_success _ _ _ _ _ h_req_liq]
        rw [contract_bind_success _ _ _ _ _ h_token0]
        rw [contract_bind_success _ _ _ _ _ h_token1]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_req_to_false]
      rw [h_swap_invalid] at h_success
      cases h_success
  have h_req_to :
      Verity.require
          (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
            toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          "UniswapV2: INVALID_TO" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_to_guard, if_true]
  let mLS := mintLockedState s
  let tok0 := mLS.storageAddr token0Slot.slot
  let tok1 := mLS.storageAddr token1Slot.slot
  let body :=
    swapConditionalTransfersAndTail tok0 tok1
      (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
      amount0Out amount1Out (mod s.blockTimestamp uint32Modulus)
      (s.storage blockTimestampLastSlot.slot) toAddr
  have h_swap_body_wrapped :
      (swap amount0Out amount1Out toAddr data).run s =
        Contract.run (fun _ => body mLS) s := by
    unfold swap UniswapV2PairBase.swap Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_timestamp]
    rw [contract_bind_success _ _ _ _ _ h_previous]
    rw [contract_bind_success _ _ _ _ _ h_req_output]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_req_liq]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_req_to]
    dsimp [body, mLS, tok0, tok1, swapConditionalTransfersAndTail,
      swapInteractionTailContract]
    simp [Verity.pure, Pure.pure]
  have h_wrapped_success :
      Contract.run (fun _ => body mLS) s =
        ContractResult.success () (Contract.run (fun _ => body mLS) s).snd := by
    rw [← h_swap_body_wrapped]
    exact h_success
  have h_body_success :
      body.run mLS = ContractResult.success () (body.run mLS).snd := by
    unfold Contract.run at h_wrapped_success ⊢
    cases h_body_run : body mLS with
    | success value post =>
        cases value
        rfl
    | «revert» msg post =>
        rw [h_body_run] at h_wrapped_success
        simp [ContractResult.snd] at h_wrapped_success
  have h_wrapped_eq_body :
      Contract.run (fun _ => body mLS) s = body.run mLS := by
    have h_body_raw := Contract.eq_of_run_success h_body_success
    unfold Contract.run
    rw [h_body_raw]
  have h_tok0_eq : tok0 = pairToken0 s := by
    dsimp [tok0, mLS, pairToken0]
    rw [mintLockedState_storageAddr]
  have h_tok1_eq : tok1 = pairToken1 s := by
    dsimp [tok1, mLS, pairToken1]
    rw [mintLockedState_storageAddr]
  have h_self_eq : pairSelf mLS = pairSelf s := by
    dsimp [mLS, pairSelf]
    rw [mintLockedState_thisAddress]
  rw [h_swap_body_wrapped, h_wrapped_eq_body]
  rw [pairTransfersAfterCall_of_events_eq s mLS _
    (by dsimp [mLS]; exact mintLockedState_events_eq s)]
  rw [← h_tok0_eq, ← h_tok1_eq, ← h_self_eq]
  exact swapConditionalTransfersAndTail_pairTransfers tok0 tok1
    (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
    amount0Out amount1Out (mod s.blockTimestamp uint32Modulus)
    (s.storage blockTimestampLastSlot.slot) toAddr mLS (by
      dsimp only [body] at h_body_success
      exact h_body_success)

private theorem require_if_success_state
    {cond : Bool} {msg : String} {s s' : ContractState} {a : Unit} :
  (if cond = true then ContractResult.success () s
    else ContractResult.revert msg s) = ContractResult.success a s' →
    s' = s := by
  intro h
  cases cond <;> simp at h
  cases h
  rfl

theorem swap_success_run_storage_matches_world
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState) :
  (swap amount0Out amount1Out toAddr data).run s =
      ContractResult.success () ((swap amount0Out amount1Out toAddr data).run s).snd →
    pairPostCallSelfBalancesMatch s
      ((swap amount0Out amount1Out toAddr data).run s).snd balance0Now balance1Now →
      amount0Out < s.storage reserve0Slot.slot →
        amount1Out < s.storage reserve1Slot.slot →
          pairConcreteStorageMatchesWorld
            ((swap amount0Out amount1Out toAddr data).run s).snd
            (pairWorldAfterSwapRun balance0Now balance1Now s) := by
  intro h_success h_post h_liq0 h_liq1
  have h_success_exists :
      (swap amount0Out amount1Out toAddr data).run s =
        ContractResult.success () ((swap amount0Out amount1Out toAddr data).run s).snd :=
    h_success
  have h_unlocked :=
    swap_success_run_implies_lock_open amount0Out amount1Out toAddr data s
      ((swap amount0Out amount1Out toAddr data).run s) rfl h_success_exists
  have h_nonzero :=
    swap_success_run_implies_nonzero_output amount0Out amount1Out toAddr data s
      ((swap amount0Out amount1Out toAddr data).run s) rfl h_success_exists
  have h_output : amount0Out > 0 ∨ amount1Out > 0 := by
    rcases h_nonzero with h_amount0 | h_amount1
    · exact Or.inl (uint256_pos_of_ne_zero h_amount0)
    · exact Or.inr (uint256_pos_of_ne_zero h_amount1)
  have h_unlocked_raw : s.storage 11 = (1 : Uint256) := by
    simpa [unlockedSlot] using h_unlocked
  have h_lock_guard :
      (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256)) = true := by
    simp [UniswapV2PairBase.unlockedSlot, h_unlocked_raw]
  have h_output_guard : (amount0Out > 0 || amount1Out > 0) = true := by
    simpa [Bool.or_eq_true] using h_output
  have h_liq_guard :
      (amount0Out < s.storage reserve0Slot.slot &&
        amount1Out < s.storage reserve1Slot.slot) = true := by
    simpa [Bool.and_eq_true] using And.intro h_liq0 h_liq1
  have h_get_lock :
      getStorage UniswapV2PairBase.unlockedSlot s =
        ContractResult.success (s.storage UniswapV2PairBase.unlockedSlot.slot) s := rfl
  have h_req_lock :
      Verity.require (s.storage UniswapV2PairBase.unlockedSlot.slot == (1 : Uint256))
        "UniswapV2: LOCKED" s = ContractResult.success () s := by
    simp only [Verity.require, h_lock_guard, if_true]
  have h_timestamp :
      Verity.blockTimestamp s = ContractResult.success s.blockTimestamp s := rfl
  have h_previous :
      getStorage UniswapV2PairBase.blockTimestampLastSlot s =
        ContractResult.success (s.storage blockTimestampLastSlot.slot) s := by
    simp only [getStorage, blockTimestampLastSlot, UniswapV2PairBase.blockTimestampLastSlot]
  have h_req_output :
      Verity.require (amount0Out > 0 || amount1Out > 0)
        "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT" s =
          ContractResult.success () s := by
    simp only [Verity.require, h_output_guard, if_true]
  have h_set_lock :
      setStorage UniswapV2PairBase.unlockedSlot (0 : Uint256) s =
        ContractResult.success () (mintLockedState s) := by
    simpa only [UniswapV2PairBase.unlockedSlot] using
      setStorage_unlockedSlot_app_mintLockedState s
  have h_get_reserve0 :
      getStorage UniswapV2PairBase.reserve0Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve0Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve0]
  have h_get_reserve1 :
      getStorage UniswapV2PairBase.reserve1Slot (mintLockedState s) =
        ContractResult.success (s.storage reserve1Slot.slot) (mintLockedState s) := by
    simp only [getStorage]
    rw [mintLockedState_storage_reserve1]
  have h_req_liq :
      Verity.require
          (amount0Out < s.storage reserve0Slot.slot &&
            amount1Out < s.storage reserve1Slot.slot)
          "UniswapV2: INSUFFICIENT_LIQUIDITY" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_liq_guard, if_true]
  have h_token0 :
      getStorageAddr UniswapV2PairBase.token0Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
          (mintLockedState s) := rfl
  have h_token1 :
      getStorageAddr UniswapV2PairBase.token1Slot (mintLockedState s) =
        ContractResult.success ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          (mintLockedState s) := rfl
  have h_to_guard :
      (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
        toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot) = true := by
    by_cases h_guard :
        (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
          toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot) = true
    · exact h_guard
    · exfalso
      have h_req_to_false :
          Verity.require
              (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
                toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
              "UniswapV2: INVALID_TO" (mintLockedState s) =
            ContractResult.revert "UniswapV2: INVALID_TO" (mintLockedState s) := by
        simp only [Verity.require]
        rw [if_neg h_guard]
      have h_swap_invalid :
          (swap amount0Out amount1Out toAddr data).run s =
            ContractResult.revert "UniswapV2: INVALID_TO" s := by
        unfold swap UniswapV2PairBase.swap Contract.run
        rw [contract_bind_success _ _ _ _ _ h_get_lock]
        rw [contract_bind_success _ _ _ _ _ h_req_lock]
        rw [contract_bind_success _ _ _ _ _ h_timestamp]
        rw [contract_bind_success _ _ _ _ _ h_previous]
        rw [contract_bind_success _ _ _ _ _ h_req_output]
        rw [contract_bind_success _ _ _ _ _ h_set_lock]
        rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
        rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
        rw [contract_bind_success _ _ _ _ _ h_req_liq]
        rw [contract_bind_success _ _ _ _ _ h_token0]
        rw [contract_bind_success _ _ _ _ _ h_token1]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_req_to_false]
      rw [h_swap_invalid] at h_success
      cases h_success
  have h_req_to :
      Verity.require
          (toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot &&
            toAddr != (mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
          "UniswapV2: INVALID_TO" (mintLockedState s) =
        ContractResult.success () (mintLockedState s) := by
    simp only [Verity.require, h_to_guard, if_true]
  let token0Value := (mintLockedState s).storageAddr token0Slot.slot
  let token1Value := (mintLockedState s).storageAddr token1Slot.slot
  let swapTransfer0State :=
    if amount0Out > 0 then
      (TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out (mintLockedState s)).snd
    else
      mintLockedState s
  let swapTransfer1State :=
    if amount1Out > 0 then
      (TamaUniV2.pairSafeTransfer token1Value toAddr amount1Out swapTransfer0State).snd
    else
      swapTransfer0State
  let swapSender := swapTransfer1State.sender
  let swapCallbackState :=
    ((ecmDo uniswapV2CallbackModule
      [addressToWord toAddr, addressToWord swapSender, amount0Out, amount1Out] :
        Contract Unit) swapTransfer1State).snd
  have h_sender :
      msgSender swapTransfer1State =
        ContractResult.success swapSender swapTransfer1State := by
    rfl
  have h_callback :
      ((ecmDo uniswapV2CallbackModule
          [addressToWord toAddr, addressToWord swapSender, amount0Out, amount1Out] :
            Contract Unit) swapTransfer1State) =
        ContractResult.success () swapCallbackState := by
    dsimp [swapCallbackState, swapSender]
    rfl
  have h_self :
      contractAddress swapCallbackState =
        ContractResult.success swapCallbackState.thisAddress swapCallbackState := by
    rfl
  have h_transfer0_thisAddress :
      swapTransfer0State.thisAddress = s.thisAddress := by
    dsimp only [swapTransfer0State]
    by_cases h_amount0 : amount0Out > 0
    · rw [if_pos h_amount0]
      rw [pairSafeTransfer_snd_thisAddress]
      exact mintLockedState_thisAddress s
    · rw [if_neg h_amount0]
      exact mintLockedState_thisAddress s
  have h_transfer1_thisAddress :
      swapTransfer1State.thisAddress = s.thisAddress := by
    dsimp only [swapTransfer1State]
    by_cases h_amount1 : amount1Out > 0
    · rw [if_pos h_amount1]
      rw [pairSafeTransfer_snd_thisAddress]
      exact h_transfer0_thisAddress
    · rw [if_neg h_amount1]
      exact h_transfer0_thisAddress
  have h_callback_thisAddress :
      swapCallbackState.thisAddress = s.thisAddress := by
    calc
      swapCallbackState.thisAddress = swapTransfer1State.thisAddress := by
        simpa [swapCallbackState] using
          (uniswapV2Callback_snd_thisAddress
            toAddr swapSender amount0Out amount1Out swapTransfer1State)
      _ = s.thisAddress := h_transfer1_thisAddress
  have h_balance0_after :
      TamaUniV2.erc20BalanceOf token0Value swapCallbackState.thisAddress
          swapCallbackState =
        ContractResult.success balance0Now swapCallbackState := by
    dsimp only [token0Value]
    simpa [pairToken0, pairSelf, mintLockedState_storageAddr,
      mintLockedState_thisAddress, h_callback_thisAddress] using
      (pairPostCallSelfBalancesMatch_balance0_app_nf
        (s := s) (post := ((swap amount0Out amount1Out toAddr data).run s).snd)
        (readState := swapCallbackState) (b0 := balance0Now)
        (b1 := balance1Now) h_post)
  have h_balance1_after :
      TamaUniV2.erc20BalanceOf token1Value swapCallbackState.thisAddress
          swapCallbackState =
        ContractResult.success balance1Now swapCallbackState := by
    dsimp only [token1Value]
    simpa [pairToken1, pairSelf, mintLockedState_storageAddr,
      mintLockedState_thisAddress, h_callback_thisAddress] using
      (pairPostCallSelfBalancesMatch_balance1_app_nf
        (s := s) (post := ((swap amount0Out amount1Out toAddr data).run s).snd)
        (readState := swapCallbackState) (b0 := balance0Now)
        (b1 := balance1Now) h_post)
  have h_callback_supply :
      swapCallbackState.storage totalSupplySlot.slot = s.storage totalSupplySlot.slot := by
    have h_transfer0_supply :
        swapTransfer0State.storage totalSupplySlot.slot =
          s.storage totalSupplySlot.slot := by
      dsimp only [swapTransfer0State]
      by_cases h_amount0 : amount0Out > 0
      · rw [if_pos h_amount0]
        rw [pairSafeTransfer_snd_storage]
        exact mintLockedState_storage_totalSupply s
      · rw [if_neg h_amount0]
        exact mintLockedState_storage_totalSupply s
    have h_transfer1_supply :
        swapTransfer1State.storage totalSupplySlot.slot =
          s.storage totalSupplySlot.slot := by
      dsimp only [swapTransfer1State]
      by_cases h_amount1 : amount1Out > 0
      · rw [if_pos h_amount1]
        rw [pairSafeTransfer_snd_storage]
        exact h_transfer0_supply
      · rw [if_neg h_amount1]
        exact h_transfer0_supply
    calc
      swapCallbackState.storage totalSupplySlot.slot =
          swapTransfer1State.storage totalSupplySlot.slot := by
        simpa [swapCallbackState] using
          (uniswapV2Callback_snd_storage
            toAddr swapSender amount0Out amount1Out swapTransfer1State
            totalSupplySlot.slot)
      _ = s.storage totalSupplySlot.slot := h_transfer1_supply
  have h_swap_prefix :
      (swap amount0Out amount1Out toAddr data).run s =
        Contract.run
          (fun _ =>
            ((UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
              (s.storage blockTimestampLastSlot.slot)) : Contract Unit)
              swapCallbackState) s := by
    unfold swap UniswapV2PairBase.swap Contract.run
    rw [contract_bind_success _ _ _ _ _ h_get_lock]
    rw [contract_bind_success _ _ _ _ _ h_req_lock]
    rw [contract_bind_success _ _ _ _ _ h_timestamp]
    rw [contract_bind_success _ _ _ _ _ h_previous]
    rw [contract_bind_success _ _ _ _ _ h_req_output]
    rw [contract_bind_success _ _ _ _ _ h_set_lock]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve0]
    rw [contract_bind_success _ _ _ _ _ h_get_reserve1]
    rw [contract_bind_success _ _ _ _ _ h_req_liq]
    rw [contract_bind_success _ _ _ _ _ h_token0]
    rw [contract_bind_success _ _ _ _ _ h_token1]
    rw [contract_bind_success _ _ _ _ _ h_req_to]
    by_cases h_amount0 : amount0Out > 0
    · rw [if_pos h_amount0]
      have h_transfer0_success :
          TamaUniV2.pairSafeTransfer
              ((mintLockedState s).storageAddr UniswapV2PairBase.token0Slot.slot)
              toAddr amount0Out (mintLockedState s) =
            ContractResult.success 1 swapTransfer0State := by
        dsimp only [swapTransfer0State, token0Value]
        rw [if_pos h_amount0]
        rfl
      dsimp only [Bind.bind, Verity.bind]
      rw [h_transfer0_success]
      dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure]
      by_cases h_amount1 : amount1Out > 0
      · rw [if_pos h_amount1]
        have h_transfer1_success :
            TamaUniV2.pairSafeTransfer
                ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
                toAddr amount1Out swapTransfer0State =
              ContractResult.success 1 swapTransfer1State := by
          dsimp only [swapTransfer1State, token1Value]
          rw [if_pos h_amount1]
          rfl
        dsimp only [Bind.bind, Verity.bind]
        rw [h_transfer1_success]
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer1State =
          ContractResult.success () swapTransfer1State by rfl]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_sender]
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer1State =
          ContractResult.success () swapCallbackState by simpa using h_callback]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_self]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance0_after]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance1_after]
      · rw [if_neg h_amount1]
        have h_transfer1_state : swapTransfer1State = swapTransfer0State := by
          dsimp only [swapTransfer1State]
          rw [if_neg h_amount1]
        have h_sender' :
            msgSender swapTransfer0State =
              ContractResult.success swapSender swapTransfer0State := by
          simpa [h_transfer1_state] using h_sender
        have h_callback' :
            ((ecmDo uniswapV2CallbackModule
                [addressToWord toAddr, addressToWord swapSender, amount0Out, amount1Out] :
                  Contract Unit) swapTransfer0State) =
              ContractResult.success () swapCallbackState := by
          simpa [h_transfer1_state] using h_callback
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer0State =
          ContractResult.success () swapTransfer0State by rfl]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_sender']
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer0State =
          ContractResult.success () swapCallbackState by simpa using h_callback']
        dsimp only [Bind.bind, Verity.bind]
        rw [h_self]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance0_after]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance1_after]
    · rw [if_neg h_amount0]
      have h_transfer0_state : swapTransfer0State = mintLockedState s := by
        dsimp only [swapTransfer0State]
        rw [if_neg h_amount0]
      dsimp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure]
      by_cases h_amount1 : amount1Out > 0
      · rw [if_pos h_amount1]
        have h_transfer1_success :
            TamaUniV2.pairSafeTransfer
                ((mintLockedState s).storageAddr UniswapV2PairBase.token1Slot.slot)
                toAddr amount1Out (mintLockedState s) =
              ContractResult.success 1 swapTransfer1State := by
          dsimp only [swapTransfer1State, token1Value]
          rw [h_transfer0_state]
          rw [if_pos h_amount1]
          rfl
        dsimp only [Bind.bind, Verity.bind]
        rw [h_transfer1_success]
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer1State =
          ContractResult.success () swapTransfer1State by rfl]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_sender]
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) swapTransfer1State =
          ContractResult.success () swapCallbackState by simpa using h_callback]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_self]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance0_after]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance1_after]
      · rw [if_neg h_amount1]
        have h_transfer1_state : swapTransfer1State = mintLockedState s := by
          dsimp only [swapTransfer1State]
          rw [h_transfer0_state]
          rw [if_neg h_amount1]
        have h_sender' :
            msgSender (mintLockedState s) =
              ContractResult.success swapSender (mintLockedState s) := by
          simpa [h_transfer1_state] using h_sender
        have h_callback' :
            ((ecmDo uniswapV2CallbackModule
                [addressToWord toAddr, addressToWord swapSender, amount0Out, amount1Out] :
                  Contract Unit) (mintLockedState s)) =
              ContractResult.success () swapCallbackState := by
          simpa [h_transfer1_state] using h_callback
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) (mintLockedState s) =
          ContractResult.success () (mintLockedState s) by rfl]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_sender']
        dsimp only [Bind.bind, Verity.bind]
        rw [show (Verity.pure () : Contract Unit) (mintLockedState s) =
          ContractResult.success () swapCallbackState by simpa using h_callback']
        dsimp only [Bind.bind, Verity.bind]
        rw [h_self]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance0_after]
        dsimp only [Bind.bind, Verity.bind]
        rw [h_balance1_after]
  have h_finish_success_raw :
      UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
        (s.storage blockTimestampLastSlot.slot) swapCallbackState =
          ContractResult.success ()
            (UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
              (s.storage blockTimestampLastSlot.slot) swapCallbackState).snd := by
    cases h_finish :
        UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
          (s.storage blockTimestampLastSlot.slot) swapCallbackState with
    | success value postFinish =>
        cases value
        rfl
    | «revert» reason postFinish =>
        rw [h_swap_prefix] at h_success
        unfold Contract.run at h_success
        dsimp only at h_success
        rw [h_finish] at h_success
        simp only [ContractResult.snd] at h_success
        cases h_success
  have h_finish_success :
      (UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
        (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
        amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
        (s.storage blockTimestampLastSlot.slot)).run swapCallbackState =
          ContractResult.success ()
            ((UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
              (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
              amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
              (s.storage blockTimestampLastSlot.slot)).run swapCallbackState).snd := by
    unfold Contract.run
    rw [h_finish_success_raw]
    rfl
  have h_finish_storage :
      pairConcreteStorageMatchesWorld
        ((UniswapV2PairBase.finishSwap swapSender balance0Now balance1Now
          (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)
          amount0Out amount1Out toAddr (mod s.blockTimestamp uint32Modulus)
          (s.storage blockTimestampLastSlot.slot)).run swapCallbackState).snd
        (pairWorldAfterSwapRun balance0Now balance1Now s) := by
    apply finishSwap_run_storage_matches_world
    · rfl
    · exact h_finish_success
    · exact h_callback_supply
  rw [h_swap_prefix]
  unfold Contract.run
  dsimp only
  rw [h_finish_success_raw]
  have h_finish_storage' := h_finish_storage
  unfold Contract.run at h_finish_storage'
  rw [h_finish_success_raw] at h_finish_storage'
  simpa only [ContractResult.snd] using h_finish_storage'

theorem feeAdjustedSwap_implies_raw_k
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

def pair_swap_expected_matches_closed_world_step
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

theorem swap_expected_matches_closed_world_step
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

def pair_swap_success_run_matches_closed_world_step
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      pair_swap_expected_matches_closed_world_step
        amount0Out amount1Out balance0Now balance1Now s

theorem swap_success_run_matches_closed_world_step
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

def pair_swap_success_run_matches_closed_world_step_from_run
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

theorem swap_success_run_matches_closed_world_step_from_run
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
  intro h_run h_success h_boundary h_post_balances h_liq0 h_liq1 h_input
    h_balance0 h_balance1 h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  rcases h_boundary with ⟨h_before_tokens, h_after_tokens⟩
  have h_before :
      pairWorldFromConcreteAndTokens preTokens s =
        pairWorldFromConcreteState s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts preTokens s
      (pairWorldFromConcreteState s) h_before_tokens
      (by simp [pairConcreteStorageMatchesWorld, pairWorldFromConcreteState])
  have h_after :
      pairWorldFromConcreteAndTokens
        (pairTokenWorldAfterSwapCall preTokens s balance0Now balance1Now
          ((swap amount0Out amount1Out toAddr data).run s))
        ((swap amount0Out amount1Out toAddr data).run s).snd =
        pairWorldAfterSwapRun balance0Now balance1Now s := by
    exact pairWorldFromConcreteAndTokens_eq_of_parts
      (pairTokenWorldAfterSwapCall preTokens s balance0Now balance1Now
        ((swap amount0Out amount1Out toAddr data).run s))
      ((swap amount0Out amount1Out toAddr data).run s).snd
      (pairWorldAfterSwapRun balance0Now balance1Now s) h_after_tokens
      (swap_success_run_storage_matches_world
        amount0Out amount1Out toAddr data balance0Now balance1Now s
        h_success h_post_balances h_liq0 h_liq1)
  have h_step :=
    swap_success_run_matches_closed_world_step_from_run
      amount0Out amount1Out toAddr data balance0Now balance1Now s
      h_run h_success h_liq0 h_liq1 h_input h_balance0 h_balance1
      h_bound0 h_bound1 h_fee0 h_fee1 h_adjusted_k
  rw [h_before, h_after]
  exact h_step

private theorem contractPreservesStorageAddr_finishSwapChecked
    (sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.finishSwapChecked sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out) :=
  contractPreservesStorageAddr_of_preservesState _
    (finishSwapChecked_preserves_state_raw sender balance0Now balance1Now
      reserve0Value reserve1Value amount0Out amount1Out)

private theorem contractPreservesStorageMap_finishSwapChecked
    (key sender : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out : Uint256) :
    contractPreservesStorageMap key
      (UniswapV2PairBase.finishSwapChecked sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out) :=
  contractPreservesStorageMap_of_preservesState key _
    (finishSwapChecked_preserves_state_raw sender balance0Now balance1Now
      reserve0Value reserve1Value amount0Out amount1Out)

private theorem contractPreservesStorageAddr_finishSwapUpdate
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.finishSwapUpdate sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out toAddr timestamp32
        previousTimestamp) := by
  unfold UniswapV2PairBase.finishSwapUpdate
  repeat
    first
    | exact contractPreservesStorageAddr_mstore _ _
    | exact contractPreservesStorageAddr_updateReservesAndEmitSync _ _ _ _ _ _
    | exact contractPreservesStorageAddr_emit _ _
    | exact contractPreservesStorageAddr_setStorage _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _

private theorem contractPreservesStorageMap_finishSwapUpdate
    (key sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0In amount1In amount0Out amount1Out timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageMap key
      (UniswapV2PairBase.finishSwapUpdate sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0In amount1In amount0Out amount1Out toAddr timestamp32
        previousTimestamp) := by
  unfold UniswapV2PairBase.finishSwapUpdate
  repeat
    first
    | exact contractPreservesStorageMap_mstore key _ _
    | exact contractPreservesStorageMap_updateReservesAndEmitSync key _ _ _ _ _ _
    | exact contractPreservesStorageMap_emit key _ _
    | exact contractPreservesStorageMap_setStorage key _ _
    | exact contractPreservesStorageMap_pure key _
    | apply contractPreservesStorageMap_bind
    | intro _

private theorem contractPreservesStorageAddr_finishSwap
    (sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.finishSwap sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out toAddr timestamp32 previousTimestamp) := by
  unfold UniswapV2PairBase.finishSwap
  apply contractPreservesStorageAddr_bind
  · exact contractPreservesStorageAddr_finishSwapChecked sender
      balance0Now balance1Now reserve0Value reserve1Value amount0Out amount1Out
  · intro amounts
    rcases amounts with ⟨amount0In, amount1In⟩
    exact contractPreservesStorageAddr_finishSwapUpdate sender toAddr
      balance0Now balance1Now reserve0Value reserve1Value amount0In amount1In
      amount0Out amount1Out timestamp32 previousTimestamp

private theorem contractPreservesStorageMap_finishSwap
    (key sender toAddr : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      amount0Out amount1Out timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageMap key
      (UniswapV2PairBase.finishSwap sender
        balance0Now balance1Now reserve0Value reserve1Value
        amount0Out amount1Out toAddr timestamp32 previousTimestamp) := by
  unfold UniswapV2PairBase.finishSwap
  apply contractPreservesStorageMap_bind
  · exact contractPreservesStorageMap_finishSwapChecked key sender
      balance0Now balance1Now reserve0Value reserve1Value amount0Out amount1Out
  · intro amounts
    rcases amounts with ⟨amount0In, amount1In⟩
    exact contractPreservesStorageMap_finishSwapUpdate key sender toAddr
      balance0Now balance1Now reserve0Value reserve1Value amount0In amount1In
      amount0Out amount1Out timestamp32 previousTimestamp

private theorem contractPreservesStorageAddr_swap
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray) :
    contractPreservesStorageAddr (swap amount0Out amount1Out toAddr data) := by
  unfold swap UniswapV2PairBase.swap
  repeat
    first
    | exact contractPreservesStorageAddr_getStorage _
    | exact contractPreservesStorageAddr_getStorageAddr _
    | exact contractPreservesStorageAddr_require _ _
    | exact contractPreservesStorageAddr_setStorage _ _
    | exact contractPreservesStorageAddr_blockTimestamp
    | exact contractPreservesStorageAddr_pairSafeTransfer _ _ _
    | exact contractPreservesStorageAddr_msgSender
    | exact contractPreservesStorageAddr_ecmDo _ _
    | exact contractPreservesStorageAddr_contractAddress
    | exact contractPreservesStorageAddr_erc20BalanceOf _ _
    | exact contractPreservesStorageAddr_finishSwap _ _ _ _ _ _ _ _ _ _
    | exact contractPreservesStorageAddr_pure _
    | apply contractPreservesStorageAddr_bind
    | intro _
    | split_ifs

private theorem contractPreservesStorageMap_swap
    (key : Address)
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray) :
    contractPreservesStorageMap key (swap amount0Out amount1Out toAddr data) := by
  unfold swap UniswapV2PairBase.swap
  repeat
    first
    | exact contractPreservesStorageMap_getStorage key _
    | exact contractPreservesStorageMap_getStorageAddr key _
    | exact contractPreservesStorageMap_require key _ _
    | exact contractPreservesStorageMap_setStorage key _ _
    | exact contractPreservesStorageMap_blockTimestamp key
    | exact contractPreservesStorageMap_pairSafeTransfer key _ _ _
    | exact contractPreservesStorageMap_msgSender key
    | exact contractPreservesStorageMap_ecmDo key _ _
    | exact contractPreservesStorageMap_contractAddress key
    | exact contractPreservesStorageMap_erc20BalanceOf key _ _
    | exact contractPreservesStorageMap_finishSwap key _ _ _ _ _ _ _ _ _ _
    | exact contractPreservesStorageMap_pure key _
    | apply contractPreservesStorageMap_bind
    | intro _
    | split_ifs

theorem swap_run_storageAddr_frame
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) (i : Nat) :
  ((swap amount0Out amount1Out toAddr data).run s).snd.storageAddr i =
    s.storageAddr i :=
  contractPreservesStorageAddr_run_snd (swap amount0Out amount1Out toAddr data)
    (contractPreservesStorageAddr_swap amount0Out amount1Out toAddr data) s i

theorem swap_caller_lp_frame
    (amount0Out amount1Out : Uint256) (toAddr caller : Address) (data : ByteArray)
    (s : ContractState) :
  ((swap amount0Out amount1Out toAddr data).run s).snd.storageMap balancesSlot.slot caller =
    s.storageMap balancesSlot.slot caller := by
  exact contractPreservesStorageMap_run_snd caller
    (swap amount0Out amount1Out toAddr data)
    (contractPreservesStorageMap_swap caller amount0Out amount1Out toAddr data) s




end TamaUniV2.Proof.UniswapV2PairProof
