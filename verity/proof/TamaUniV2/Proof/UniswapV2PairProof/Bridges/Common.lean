import TamaUniV2.Proof.UniswapV2PairProof.ViewsAndGuards
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
theorem mintLockedState_storageMap (s : ContractState) :
    (mintLockedState s).storageMap = s.storageMap := rfl

theorem pairTokenWorldAfterEvent_eq_pairTransferOfEvent
    (pre : PairTokenBalances) (event : Event) :
  pairTokenWorldAfterEvent pre event =
    match pairTransferOfEvent event with
    | some tr => pairTokenWorldAfterPairTransfer pre tr
    | none => pre := by
  rcases event with ⟨name, args, indexedArgs⟩
  by_cases h_name : name = "UniswapV2PairTokenSafeTransfer"
  · subst name
    cases args with
    | nil =>
        simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
    | cons tokenWord args =>
        cases args with
        | nil =>
            simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
        | cons fromWord args =>
            cases args with
            | nil =>
                simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
            | cons toWord args =>
                cases args with
                | nil =>
                    simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
                | cons amount args =>
                    cases args with
                    | nil =>
                        cases indexedArgs with
                        | nil =>
                            simp [pairTokenWorldAfterEvent, pairTransferOfEvent,
                              pairTokenWorldAfterPairTransfer]
                        | cons indexed indexedArgs =>
                            simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
                    | cons extra args =>
                        simp [pairTokenWorldAfterEvent, pairTransferOfEvent]
  · simp [pairTokenWorldAfterEvent, pairTransferOfEvent, h_name]

theorem pairTokenWorldAfterEvents_eq_pairTransfers
    (pre : PairTokenBalances) (events : List Event) :
  pairTokenWorldAfterEvents pre events =
    pairTokenWorldAfterPairTransfers pre (pairTransfersAfterEvents events) := by
  induction events generalizing pre with
  | nil =>
      rfl
  | cons event events ih =>
      rw [pairTokenWorldAfterEvents]
      rw [ih]
      rw [pairTokenWorldAfterEvent_eq_pairTransferOfEvent]
      cases h_transfer : pairTransferOfEvent event <;>
        simp [pairTransfersAfterEvents, pairTokenWorldAfterPairTransfers, h_transfer]

theorem pairTokenWorldAfterCall_eq_pairTransfers {α : Type}
    (pre : PairTokenBalances) (s : ContractState) (result : ContractResult α) :
  pairTokenWorldAfterCall pre s result =
    pairTokenWorldAfterPairTransfers pre (pairTransfersAfterCall s result) := by
  simp [pairTokenWorldAfterCall, pairTransfersAfterCall,
    pairTokenWorldAfterEvents_eq_pairTransfers]

theorem pairTransfersAfterEvents_append (l1 l2 : List Event) :
  pairTransfersAfterEvents (l1 ++ l2) =
    pairTransfersAfterEvents l1 ++ pairTransfersAfterEvents l2 := by
  simp [pairTransfersAfterEvents]

theorem pairTransfersAfterCall_bind_success {α β : Type}
    (c : Contract α) (k : α → Contract β)
    (s mid : ContractState) (a : α)
    (h : c.run s = ContractResult.success a mid)
    (h_k_success : ∃ b post, (k a).run mid = ContractResult.success b post)
    (h_mid_events :
      mid.events = s.events ++ emittedPairEventsAfterCall s (c.run s))
    (h_post_events :
      ((k a).run mid).snd.events =
        mid.events ++ emittedPairEventsAfterCall mid ((k a).run mid)) :
  pairTransfersAfterCall s ((do let x ← c; k x).run s) =
    pairTransfersAfterCall s (c.run s) ++
    pairTransfersAfterCall mid ((k a).run mid) := by
  rcases h_k_success with ⟨b, post, h_k_success⟩
  have h_bind_raw : (Bind.bind c k) s = k a mid :=
    contract_bind_success c k s mid a (Contract.eq_of_run_success h)
  have h_bind : (Bind.bind c k).run s = (k a).run mid := by
    unfold Contract.run
    rw [h_bind_raw]
    rw [Contract.eq_of_run_success h_k_success]
  have h_post_events' :
      post.events =
        mid.events ++ emittedPairEventsAfterCall mid ((k a).run mid) := by
    simpa [h_k_success] using h_post_events
  have h_bind_events :
      emittedPairEventsAfterCall s ((Bind.bind c k).run s) =
        emittedPairEventsAfterCall s (c.run s) ++
          emittedPairEventsAfterCall mid ((k a).run mid) := by
    unfold emittedPairEventsAfterCall
    rw [h_bind, h, h_k_success]
    simp only [ContractResult.snd_success]
    rw [h_post_events', h_mid_events]
    simp [List.append_assoc, List.drop_left]
  unfold pairTransfersAfterCall
  rw [h_bind_events, pairTransfersAfterEvents_append]

theorem pairSafeTransfer_pairTransfers
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
  pairTransfersAfterCall s
    ((TamaUniV2.pairSafeTransfer token toAddr amount).run s) =
    [{ token := token, fromAddr := pairSelf s, toAddr := toAddr, amount := amount }] := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, TamaUniV2.pairSafeTransfer,
    TamaUniV2.tracePairTokenSafeTransfer, TamaUniV2.pairTokenSafeTransferEvent,
    Contracts.safeTransfer, Contract.run, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, pairSelf, addressOfNat_toNat_mod_uint256]

theorem run_success_events_extend_of_append {α : Type}
    (c : Contract α) (s s' : ContractState) (a : α)
    (h_run : c.run s = ContractResult.success a s')
    (emitted : List Event) (h_events : s'.events = s.events ++ emitted) :
  s'.events = s.events ++ emittedPairEventsAfterCall s (c.run s) := by
  unfold emittedPairEventsAfterCall
  rw [h_run]
  simp only [ContractResult.snd_success]
  rw [h_events]
  congr 1
  rw [List.drop_left]

theorem pairTransfersAfterCall_of_events_eq {α : Type}
    (s t : ContractState) (result : ContractResult α)
    (h_events : t.events = s.events) :
  pairTransfersAfterCall s result = pairTransfersAfterCall t result := by
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, h_events]

/-- Peel one event-free prefix step at the TRACE level: if `c s` succeeds landing
in `s'` with no new events, the pair-transfer trace of `(c >>= k).run s` equals
that of the continuation `(k a).run s'`. No continuation term is written, so this
is robust to the exact residual shape. -/
theorem pairTransfersAfterCall_bind_no_event {α β : Type}
    (c : Contract α) (k : α → Contract β) (s s' : ContractState) (a : α)
    (h : c s = ContractResult.success a s')
    (h_events : s'.events = s.events) :
  pairTransfersAfterCall s ((Bind.bind c k).run s) =
    pairTransfersAfterCall s' ((k a).run s') := by
  have hbind : (Bind.bind c k) s = k a s' := contract_bind_success c k s s' a h
  have hev :
      ((Bind.bind c k).run s).snd.events = ((k a).run s').snd.events := by
    unfold Contract.run
    rw [hbind]
    cases hka : k a s' with
    | success b p => simp [ContractResult.snd]
    | «revert» msg p => simp [ContractResult.snd, h_events]
  unfold pairTransfersAfterCall emittedPairEventsAfterCall
  rw [hev, h_events]

/-- Transport a success result one bind step inward without writing the
continuation: if `(c >>= k).run s` succeeds and `c s` succeeds in `s'`, then
`(k a).run s'` is that same success. -/
theorem run_success_bind_peel {α β : Type}
    (c : Contract α) (k : α → Contract β) (s s' final : ContractState) (a : α) (b : β)
    (h : c s = ContractResult.success a s')
    (h_succ : (Bind.bind c k).run s = ContractResult.success b final) :
  (k a).run s' = ContractResult.success b final := by
  have hbind : (Bind.bind c k) s = k a s' := contract_bind_success c k s s' a h
  unfold Contract.run at h_succ ⊢
  rw [hbind] at h_succ
  cases hka : k a s' with
  | success b' p' => rw [hka] at h_succ; simpa using h_succ
  | «revert» msg p' => rw [hka] at h_succ; simp at h_succ

/-- Peel a `pairSafeTransfer` step at the trace level: it prepends one
PairTransfer (from the pair to `toAddr`), then the continuation's trace follows. -/
theorem pairTransfersAfterCall_bind_safeTransfer {β : Type}
    (token toAddr : Address) (amt : Uint256) (k : Uint256 → Contract β)
    (s mid : ContractState)
    (h_xfer : (TamaUniV2.pairSafeTransfer token toAddr amt).run s =
      ContractResult.success 1 mid)
    (h_k_succ : ∃ b post, (k 1).run mid = ContractResult.success b post)
    (h_mid_ev : mid.events =
      s.events ++ emittedPairEventsAfterCall s
        ((TamaUniV2.pairSafeTransfer token toAddr amt).run s))
    (h_post_ev : ((k 1).run mid).snd.events =
      mid.events ++ emittedPairEventsAfterCall mid ((k 1).run mid)) :
  pairTransfersAfterCall s
      ((Bind.bind (TamaUniV2.pairSafeTransfer token toAddr amt) k).run s) =
    { token := token, fromAddr := pairSelf s, toAddr := toAddr, amount := amt } ::
      pairTransfersAfterCall mid ((k 1).run mid) := by
  rw [pairTransfersAfterCall_bind_success
    (TamaUniV2.pairSafeTransfer token toAddr amt) k s mid 1 h_xfer h_k_succ h_mid_ev h_post_ev]
  rw [pairSafeTransfer_pairTransfers]
  rfl

theorem updateReservesAndEmitSync_pairTransfers
    (balance0Now balance1Now reserve0Value reserve1Value
      timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
  pairTransfersAfterCall s
    ((UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
      reserve0Value reserve1Value timestamp32 previousTimestamp).run s) = [] := by
  unfold UniswapV2PairBase.updateReservesAndEmitSync
  simp [pairTransfersAfterCall, emittedPairEventsAfterCall, pairTransfersAfterEvents,
    pairTransferOfEvent, getStorage, setStorage, Contract.run, ContractResult.snd,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [pairTransfersAfterEvents, pairTransferOfEvent, getStorage, setStorage,
        Contract.run, ContractResult.snd, Verity.bind, Bind.bind, Verity.pure,
        Pure.pure, Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem updateReservesAndEmitSync_run_storage_matches_world
    (balance0Now balance1Now reserve0Value reserve1Value timestamp32 previousTimestamp : Uint256)
    (s : ContractState) (expected : PairWorldState)
    (h_reserve0 : expected.reserve0 = balance0Now.val)
    (h_reserve1 : expected.reserve1 = balance1Now.val)
    (h_supply : expected.totalSupply = (s.storage totalSupplySlot.slot).val)
    (h_locked : expected.lockedLiquidity = pairWorldLockedLiquidity (s.storage totalSupplySlot.slot)) :
  pairConcreteStorageMatchesWorld
    ((UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
      reserve0Value reserve1Value timestamp32 previousTimestamp).run s).snd
    expected := by
  unfold pairConcreteStorageMatchesWorld
  constructor
  · simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_reserve0,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
    all_goals (split_ifs <;>
      simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore])
  constructor
  · simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_reserve1,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
    all_goals (split_ifs <;>
      simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore])
  constructor
  · simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_supply,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
    all_goals (split_ifs <;>
      simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore])
  · simp [UniswapV2PairBase.updateReservesAndEmitSync,
      getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
      h_locked,
      -maxUint112, -UniswapV2PairBase.maxUint112,
      -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
      -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
      -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
      -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
      -timestamp32, -oracleElapsed]
    all_goals (split_ifs <;>
      simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore])

theorem mintLockedState_events_eq (s : ContractState) :
    (mintLockedState s).events = s.events := by
  rfl

def contractPreservesState {α : Type} (c : Contract α) : Prop :=
  ∀ s, (c s).snd = s

theorem contractPreservesState_pure {α : Type} (a : α) :
    contractPreservesState (Verity.pure a) := by
  intro s
  rfl

theorem contractPreservesState_require (condition : Bool) (message : String) :
    contractPreservesState (Verity.require condition message) := by
  intro s
  unfold Verity.require
  cases condition <;> rfl

theorem contractPreservesState_bind {α β : Type}
    (ma : Contract α) (f : α → Contract β)
    (h_ma : contractPreservesState ma)
    (h_f : ∀ a, contractPreservesState (f a)) :
    contractPreservesState (ma >>= f) := by
  intro s
  change ((Verity.bind ma f) s).snd = s
  unfold Verity.bind
  cases h_run : ma s with
  | success a s' =>
      have h_state : s' = s := by
        have h_preserved := h_ma s
        rw [h_run] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst s'
      exact h_f a s
  | «revert» reason s' =>
      have h_state : s' = s := by
        have h_preserved := h_ma s
        rw [h_run] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst s'
      rfl

theorem contractPreservesState_run_snd {α : Type}
    (c : Contract α) (h_c : contractPreservesState c) (s : ContractState) :
    (c.run s).snd = s := by
  unfold Contract.run
  cases h_run : c s with
  | success a s' =>
      have h_state : s' = s := by
        have h_preserved := h_c s
        rw [h_run] at h_preserved
        simpa only [ContractResult.snd] using h_preserved
      subst s'
      rfl
  | «revert» reason s' =>
      rfl

def contractPreservesStorageAddr {α : Type} (c : Contract α) : Prop :=
  ∀ s, ∀ i, (c s).snd.storageAddr i = s.storageAddr i

theorem contractPreservesStorageAddr_of_preservesState {α : Type}
    (c : Contract α) (h_c : contractPreservesState c) :
    contractPreservesStorageAddr c := by
  intro s i
  rw [h_c s]

theorem contractPreservesStorageAddr_pure {α : Type} (a : α) :
    contractPreservesStorageAddr (Verity.pure a : Contract α) := by
  intro s i
  rfl

theorem contractPreservesStorageAddr_require (condition : Bool) (message : String) :
    contractPreservesStorageAddr (Verity.require condition message) := by
  exact contractPreservesStorageAddr_of_preservesState _
    (contractPreservesState_require condition message)

theorem contractPreservesStorageAddr_bind {α β : Type}
    (ma : Contract α) (f : α → Contract β)
    (h_ma : contractPreservesStorageAddr ma)
    (h_f : ∀ a, contractPreservesStorageAddr (f a)) :
    contractPreservesStorageAddr (ma >>= f) := by
  intro s i
  change ((Verity.bind ma f) s).snd.storageAddr i = s.storageAddr i
  unfold Verity.bind
  cases h_run : ma s with
  | success a mid =>
      calc
        ((f a mid).snd).storageAddr i = mid.storageAddr i := h_f a mid i
        _ = s.storageAddr i := by
          have h_preserved := h_ma s i
          rw [h_run] at h_preserved
          simpa only [ContractResult.snd] using h_preserved
  | «revert» reason mid =>
      have h_preserved := h_ma s i
      rw [h_run] at h_preserved
      simpa only [ContractResult.snd] using h_preserved

theorem contractPreservesStorageAddr_run_snd {α : Type}
    (c : Contract α) (h_c : contractPreservesStorageAddr c)
    (s : ContractState) (i : Nat) :
    (c.run s).snd.storageAddr i = s.storageAddr i := by
  unfold Contract.run
  cases h_run : c s with
  | success a post =>
      have h_preserved := h_c s i
      rw [h_run] at h_preserved
      simpa only [ContractResult.snd] using h_preserved
  | «revert» reason post =>
      rfl

def contractPreservesStorageMap {α : Type} (key : Address) (c : Contract α) : Prop :=
  ∀ s, (c s).snd.storageMap balancesSlot.slot key = s.storageMap balancesSlot.slot key

theorem contractPreservesStorageMap_of_preservesState {α : Type}
    (key : Address) (c : Contract α) (h_c : contractPreservesState c) :
    contractPreservesStorageMap key c := by
  intro s
  rw [h_c s]

theorem contractPreservesStorageMap_pure {α : Type} (key : Address) (a : α) :
    contractPreservesStorageMap key (Verity.pure a : Contract α) := by
  intro s
  rfl

theorem contractPreservesStorageMap_require (key : Address)
    (condition : Bool) (message : String) :
    contractPreservesStorageMap key (Verity.require condition message) := by
  exact contractPreservesStorageMap_of_preservesState key _
    (contractPreservesState_require condition message)

theorem contractPreservesStorageMap_bind {α β : Type}
    (key : Address) (ma : Contract α) (f : α → Contract β)
    (h_ma : contractPreservesStorageMap key ma)
    (h_f : ∀ a, contractPreservesStorageMap key (f a)) :
    contractPreservesStorageMap key (ma >>= f) := by
  intro s
  change ((Verity.bind ma f) s).snd.storageMap balancesSlot.slot key =
    s.storageMap balancesSlot.slot key
  unfold Verity.bind
  cases h_run : ma s with
  | success a mid =>
      calc
        ((f a mid).snd).storageMap balancesSlot.slot key =
            mid.storageMap balancesSlot.slot key := h_f a mid
        _ = s.storageMap balancesSlot.slot key := by
          have h_preserved := h_ma s
          rw [h_run] at h_preserved
          simpa only [ContractResult.snd] using h_preserved
  | «revert» reason mid =>
      have h_preserved := h_ma s
      rw [h_run] at h_preserved
      simpa only [ContractResult.snd] using h_preserved

theorem contractPreservesStorageMap_run_snd {α : Type}
    (key : Address) (c : Contract α) (h_c : contractPreservesStorageMap key c)
    (s : ContractState) :
    (c.run s).snd.storageMap balancesSlot.slot key = s.storageMap balancesSlot.slot key := by
  unfold Contract.run
  cases h_run : c s with
  | success a post =>
      have h_preserved := h_c s
      rw [h_run] at h_preserved
      simpa only [ContractResult.snd] using h_preserved
  | «revert» reason post =>
      rfl

theorem contractPreservesStorageAddr_getStorage (sl : StorageSlot Uint256) :
    contractPreservesStorageAddr (getStorage sl) := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_getStorage (key : Address) (sl : StorageSlot Uint256) :
    contractPreservesStorageMap key (getStorage sl) := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_getStorageAddr (sl : StorageSlot Address) :
    contractPreservesStorageAddr (getStorageAddr sl) := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_getStorageAddr
    (key : Address) (sl : StorageSlot Address) :
    contractPreservesStorageMap key (getStorageAddr sl) := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_getMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) :
    contractPreservesStorageAddr (getMapping sl key) := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_getMapping
    (key : Address) (sl : StorageSlot (Address → Uint256)) (mapKey : Address) :
    contractPreservesStorageMap key (getMapping sl mapKey) := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_setStorage (sl : StorageSlot Uint256)
    (value : Uint256) :
    contractPreservesStorageAddr (setStorage sl value) := by
  intro s i
  rfl

theorem contractPreservesStorageMap_setStorage
    (key : Address) (sl : StorageSlot Uint256) (value : Uint256) :
    contractPreservesStorageMap key (setStorage sl value) := by
  intro s
  rfl

theorem contractPreservesStorageAddr_setMapping
    (sl : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) :
    contractPreservesStorageAddr (setMapping sl key value) := by
  intro s i
  rfl

theorem contractPreservesStorageMap_setMapping_of_ne
    (key : Address) (sl : StorageSlot (Address → Uint256))
    (mapKey : Address) (value : Uint256)
    (h_ne : sl.slot ≠ balancesSlot.slot ∨ mapKey ≠ key) :
    contractPreservesStorageMap key (setMapping sl mapKey value) := by
  intro s
  unfold setMapping
  change
    (if balancesSlot.slot == sl.slot && key == mapKey then value
      else s.storageMap balancesSlot.slot key) =
      s.storageMap balancesSlot.slot key
  by_cases h_cond : (balancesSlot.slot == sl.slot && key == mapKey) = true
  · have h_parts :
        (balancesSlot.slot == sl.slot) = true ∧ (key == mapKey) = true := by
      simpa [Bool.and_eq_true] using h_cond
    have h_slot_eq : balancesSlot.slot = sl.slot := by
      exact beq_iff_eq.mp h_parts.1
    have h_key_eq : key = mapKey := by
      exact beq_iff_eq.mp h_parts.2
    rcases h_ne with h_slot | h_key
    · exact False.elim (h_slot h_slot_eq.symm)
    · exact False.elim (h_key h_key_eq.symm)
  · have h_false : (balancesSlot.slot == sl.slot && key == mapKey) = false :=
      Bool.eq_false_of_not_eq_true h_cond
    rw [h_false]
    simp

theorem contractPreservesStorageAddr_setMapping2
    (sl : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) :
    contractPreservesStorageAddr (setMapping2 sl key1 key2 value) := by
  intro s i
  rfl

theorem contractPreservesStorageMap_setMapping2
    (key : Address) (sl : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) :
    contractPreservesStorageMap key (setMapping2 sl key1 key2 value) := by
  intro s
  rfl

theorem contractPreservesStorageAddr_requireSomeUint
    (opt : Option Uint256) (message : String) :
    contractPreservesStorageAddr (Verity.Stdlib.Math.requireSomeUint opt message) := by
  cases opt <;> exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_requireSomeUint
    (key : Address) (opt : Option Uint256) (message : String) :
    contractPreservesStorageMap key (Verity.Stdlib.Math.requireSomeUint opt message) := by
  cases opt <;> exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_sqrt (x : Uint256) :
    contractPreservesStorageAddr (Tamago.Utils.FixedPointMathLibBase.sqrt x) := by
  intro s i
  rw [sqrt_run_success_frames_state]
  rfl

theorem contractPreservesStorageMap_sqrt (key : Address) (x : Uint256) :
    contractPreservesStorageMap key (Tamago.Utils.FixedPointMathLibBase.sqrt x) := by
  intro s
  rw [sqrt_run_success_frames_state]
  rfl

theorem contractPreservesStorageAddr_blockTimestamp :
    contractPreservesStorageAddr Verity.blockTimestamp := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_blockTimestamp (key : Address) :
    contractPreservesStorageMap key Verity.blockTimestamp := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_msgSender :
    contractPreservesStorageAddr msgSender := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_msgSender (key : Address) :
    contractPreservesStorageMap key msgSender := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_contractAddress :
    contractPreservesStorageAddr Verity.contractAddress := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_contractAddress (key : Address) :
    contractPreservesStorageMap key Verity.contractAddress := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_mstore (offset value : Uint256) :
    contractPreservesStorageAddr (Contracts.mstore offset value) := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_mstore (key : Address) (offset value : Uint256) :
    contractPreservesStorageMap key (Contracts.mstore offset value) := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_rawLog
    (topics : List Uint256) (dataOffset dataSize : Uint256) :
    contractPreservesStorageAddr (Contracts.rawLog topics dataOffset dataSize) := by
  intro s i
  unfold Contracts.rawLog
  by_cases h_topics : topics.length > 4 <;> simp [h_topics]

theorem contractPreservesStorageMap_rawLog
    (key : Address) (topics : List Uint256) (dataOffset dataSize : Uint256) :
    contractPreservesStorageMap key (Contracts.rawLog topics dataOffset dataSize) := by
  intro s
  unfold Contracts.rawLog
  by_cases h_topics : topics.length > 4 <;> simp [h_topics]

theorem contractPreservesStorageAddr_emitEvent
    (name : String) (args indexedArgs : List Uint256) :
    contractPreservesStorageAddr (emitEvent name args indexedArgs) := by
  intro s i
  rfl

theorem contractPreservesStorageMap_emitEvent
    (key : Address) (name : String) (args indexedArgs : List Uint256) :
    contractPreservesStorageMap key (emitEvent name args indexedArgs) := by
  intro s
  rfl

theorem contractPreservesStorageAddr_emit (name : String) (args : List Uint256) :
    contractPreservesStorageAddr (Contracts.emit name args) := by
  intro s i
  rfl

theorem contractPreservesStorageMap_emit
    (key : Address) (name : String) (args : List Uint256) :
    contractPreservesStorageMap key (Contracts.emit name args) := by
  intro s
  rfl

theorem contractPreservesStorageAddr_balanceOf (token owner : Address) :
    contractPreservesStorageAddr (Contracts.balanceOf token owner) := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_balanceOf
    (key : Address) (token owner : Address) :
    contractPreservesStorageMap key (Contracts.balanceOf token owner) := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_erc20BalanceOf (token owner : Address) :
    contractPreservesStorageAddr (TamaUniV2.erc20BalanceOf token owner) := by
  exact contractPreservesStorageAddr_balanceOf token owner

theorem contractPreservesStorageMap_erc20BalanceOf
    (key : Address) (token owner : Address) :
    contractPreservesStorageMap key (TamaUniV2.erc20BalanceOf token owner) := by
  exact contractPreservesStorageMap_balanceOf key token owner

theorem contractPreservesStorageAddr_ecmDo {γ : Type}
    (module : γ) (args : List Uint256) :
    contractPreservesStorageAddr (ecmDo module args : Contract Unit) := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_ecmDo {γ : Type}
    (key : Address) (module : γ) (args : List Uint256) :
    contractPreservesStorageMap key (ecmDo module args : Contract Unit) := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_safeTransfer
    (token toAddr : Address) (amount : Uint256) :
    contractPreservesStorageAddr (Contracts.safeTransfer token toAddr amount) := by
  exact contractPreservesStorageAddr_of_preservesState _ (by intro s; rfl)

theorem contractPreservesStorageMap_safeTransfer
    (key : Address) (token toAddr : Address) (amount : Uint256) :
    contractPreservesStorageMap key (Contracts.safeTransfer token toAddr amount) := by
  exact contractPreservesStorageMap_of_preservesState key _ (by intro s; rfl)

theorem contractPreservesStorageAddr_tracePairTokenSafeTransfer
    (token toAddr : Address) (amount : Uint256) :
    contractPreservesStorageAddr
      (TamaUniV2.tracePairTokenSafeTransfer token toAddr amount) := by
  intro s i
  rfl

theorem contractPreservesStorageMap_tracePairTokenSafeTransfer
    (key : Address) (token toAddr : Address) (amount : Uint256) :
    contractPreservesStorageMap key
      (TamaUniV2.tracePairTokenSafeTransfer token toAddr amount) := by
  intro s
  rfl

theorem contractPreservesStorageAddr_pairSafeTransfer
    (token toAddr : Address) (amount : Uint256) :
    contractPreservesStorageAddr (TamaUniV2.pairSafeTransfer token toAddr amount) := by
  unfold TamaUniV2.pairSafeTransfer
  apply contractPreservesStorageAddr_bind
  · exact contractPreservesStorageAddr_safeTransfer token toAddr amount
  · intro _
    apply contractPreservesStorageAddr_bind
    · exact contractPreservesStorageAddr_tracePairTokenSafeTransfer token toAddr amount
    · intro _
      exact contractPreservesStorageAddr_pure (1 : Uint256)

theorem contractPreservesStorageMap_pairSafeTransfer
    (key : Address) (token toAddr : Address) (amount : Uint256) :
    contractPreservesStorageMap key (TamaUniV2.pairSafeTransfer token toAddr amount) := by
  unfold TamaUniV2.pairSafeTransfer
  apply contractPreservesStorageMap_bind
  · exact contractPreservesStorageMap_safeTransfer key token toAddr amount
  · intro _
    apply contractPreservesStorageMap_bind
    · exact contractPreservesStorageMap_tracePairTokenSafeTransfer key token toAddr amount
    · intro _
      exact contractPreservesStorageMap_pure key (1 : Uint256)

def contractAppendsEvents {α : Type} (c : Contract α) : Prop :=
  ∀ s, ∃ ev, (c.run s).snd.events = s.events ++ ev

theorem contractAppendsEvents_pure {α : Type} (a : α) :
    contractAppendsEvents (Verity.pure a : Contract α) := by
  intro s
  exact ⟨[], by simp [Contract.run, Verity.pure, Pure.pure]⟩

theorem contractAppendsEvents_bind {α β : Type}
    (ma : Contract α) (f : α → Contract β)
    (h_ma : contractAppendsEvents ma)
    (h_f : ∀ a, contractAppendsEvents (f a)) :
    contractAppendsEvents (ma >>= f) := by
  intro s
  rcases h_ma s with ⟨ev1, h_ma_events⟩
  unfold Contract.run at h_ma_events
  cases h_run : ma s with
  | success a mid =>
      have h_mid_events : mid.events = s.events ++ ev1 := by
        simpa [h_run, ContractResult.snd] using h_ma_events
      unfold Contract.run
      simp [Bind.bind, Verity.bind, h_run]
      cases h_f_run : f a mid with
      | success b post =>
          rcases h_f a mid with ⟨ev2, h_f_events⟩
          have h_post_events : post.events = mid.events ++ ev2 := by
            simpa [Contract.run, h_f_run, ContractResult.snd] using h_f_events
          exact ⟨ev1 ++ ev2, by simpa [h_mid_events, h_post_events, List.append_assoc]⟩
      | «revert» reason post =>
          exact ⟨[], by simp [ContractResult.snd]⟩
  | «revert» reason mid =>
      refine ⟨[], ?_⟩
      unfold Contract.run
      simp [Bind.bind, Verity.bind, h_run, ContractResult.snd]

theorem contractAppendsEvents_getStorage (sl : StorageSlot Uint256) :
    contractAppendsEvents (getStorage sl) := by
  intro s
  exact ⟨[], by simp [Contract.run, getStorage]⟩

theorem contractAppendsEvents_getStorageAddr (sl : StorageSlot Address) :
    contractAppendsEvents (getStorageAddr sl) := by
  intro s
  exact ⟨[], by simp [Contract.run, getStorageAddr]⟩

theorem contractAppendsEvents_setStorage (sl : StorageSlot Uint256)
    (value : Uint256) :
    contractAppendsEvents (setStorage sl value) := by
  intro s
  exact ⟨[], by simp [Contract.run, setStorage]⟩

theorem contractAppendsEvents_require (condition : Bool) (message : String) :
    contractAppendsEvents (Verity.require condition message) := by
  intro s
  unfold Verity.require
  cases condition <;> exact ⟨[], by simp [Contract.run]⟩

theorem contractAppendsEvents_blockTimestamp :
    contractAppendsEvents Verity.blockTimestamp := by
  intro s
  exact ⟨[], by simp [Contract.run, Verity.blockTimestamp]⟩

theorem contractAppendsEvents_msgSender :
    contractAppendsEvents msgSender := by
  intro s
  exact ⟨[], by simp [Contract.run, msgSender]⟩

theorem contractAppendsEvents_contractAddress :
    contractAppendsEvents Verity.contractAddress := by
  intro s
  exact ⟨[], by simp [Contract.run, Verity.contractAddress]⟩

theorem contractAppendsEvents_mstore (offset value : Uint256) :
    contractAppendsEvents (Contracts.mstore offset value) := by
  intro s
  exact ⟨[], by simp [Contracts.mstore, Contract.run, Verity.pure, Pure.pure]⟩

theorem contractAppendsEvents_rawLog
    (topics : List Uint256) (dataOffset dataSize : Uint256) :
    contractAppendsEvents (Contracts.rawLog topics dataOffset dataSize) := by
  intro s
  unfold Contracts.rawLog Contract.run
  by_cases h_topics : topics.length > 4
  · exact ⟨[], by simp [h_topics]⟩
  · exact ⟨[{ name := s!"log{topics.length}", args := [dataOffset, dataSize],
              indexedArgs := topics }], by simp [h_topics]⟩

theorem contractAppendsEvents_emit (name : String) (args : List Uint256) :
    contractAppendsEvents (Contracts.emit name args) := by
  intro s
  exact ⟨[{ name := name, args := args, indexedArgs := [] }], by rfl⟩

theorem contractAppendsEvents_balanceOf (token owner : Address) :
    contractAppendsEvents (Contracts.balanceOf token owner) := by
  intro s
  exact ⟨[], by simp [Contracts.balanceOf, Contract.run, Verity.pure, Pure.pure]⟩

theorem contractAppendsEvents_ecmDo {γ : Type}
    (module : γ) (args : List Uint256) :
    contractAppendsEvents (ecmDo module args : Contract Unit) := by
  intro s
  exact ⟨[], by simp [Contract.run, Verity.pure, Pure.pure]⟩

theorem contractAppendsEvents_safeTransfer
    (token toAddr : Address) (amount : Uint256) :
    contractAppendsEvents (Contracts.safeTransfer token toAddr amount) := by
  intro s
  exact ⟨[], by simp [Contracts.safeTransfer, Contract.run, Verity.pure, Pure.pure]⟩

theorem contractAppendsEvents_tracePairTokenSafeTransfer
    (token toAddr : Address) (amount : Uint256) :
    contractAppendsEvents (TamaUniV2.tracePairTokenSafeTransfer token toAddr amount) := by
  intro s
  exact ⟨[TamaUniV2.pairTokenSafeTransferEvent token s.thisAddress toAddr amount], by rfl⟩

theorem contractAppendsEvents_pairSafeTransfer
    (token toAddr : Address) (amount : Uint256) :
    contractAppendsEvents (TamaUniV2.pairSafeTransfer token toAddr amount) := by
  unfold TamaUniV2.pairSafeTransfer
  apply contractAppendsEvents_bind
  · exact contractAppendsEvents_safeTransfer token toAddr amount
  · intro _
    apply contractAppendsEvents_bind
    · exact contractAppendsEvents_tracePairTokenSafeTransfer token toAddr amount
    · intro _
      exact contractAppendsEvents_pure (1 : Uint256)

theorem contractAppendsEvents_updateReservesAndEmitSync
    (balance0Now balance1Now reserve0Value reserve1Value
      timestamp32 previousTimestamp : Uint256) :
    contractAppendsEvents
      (UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
        reserve0Value reserve1Value timestamp32 previousTimestamp) := by
  intro s
  refine ⟨List.drop s.events.length
    ((UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
      reserve0Value reserve1Value timestamp32 previousTimestamp).run s).snd.events, ?_⟩
  unfold UniswapV2PairBase.updateReservesAndEmitSync
  simp [getStorage, setStorage, Contract.run, ContractResult.snd, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [getStorage, setStorage, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog,
        Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem pairSafeTransfer_run_events_append
    (token toAddr : Address) (amount : Uint256) (s : ContractState) :
    ∃ ev, ((TamaUniV2.pairSafeTransfer token toAddr amount).run s).snd.events =
      s.events ++ ev :=
  contractAppendsEvents_pairSafeTransfer token toAddr amount s

theorem contractPreservesStorageAddr_updateReservesAndEmitSync
    (balance0Now balance1Now reserve0Value reserve1Value
      timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageAddr
      (UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
        reserve0Value reserve1Value timestamp32 previousTimestamp) := by
  intro s i
  unfold UniswapV2PairBase.updateReservesAndEmitSync
  simp [getStorage, setStorage, ContractResult.snd, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [getStorage, setStorage, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem contractPreservesStorageMap_updateReservesAndEmitSync
    (key : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      timestamp32 previousTimestamp : Uint256) :
    contractPreservesStorageMap key
      (UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
        reserve0Value reserve1Value timestamp32 previousTimestamp) := by
  intro s
  unfold UniswapV2PairBase.updateReservesAndEmitSync
  simp [getStorage, setStorage, ContractResult.snd, Verity.bind,
    Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
    -maxUint112, -UniswapV2PairBase.maxUint112,
    -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
    -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
    -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
    -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
    -timestamp32, -oracleElapsed]
  repeat' (first
    | split_ifs
    | simp [getStorage, setStorage, ContractResult.snd, Verity.bind,
        Bind.bind, Verity.pure, Pure.pure, Contracts.rawLog, Contracts.mstore,
        -maxUint112, -UniswapV2PairBase.maxUint112,
        -q112, -UniswapV2PairBase.q112, -uint32Modulus, -UniswapV2PairBase.uint32Modulus,
        -oraclePrice0, -oraclePrice1, -oraclePrice0Increment, -oraclePrice1Increment,
        -oraclePrice0CumulativeAfterElapsed, -oraclePrice1CumulativeAfterElapsed,
        -oraclePrice0CumulativeAfterSync, -oraclePrice1CumulativeAfterSync,
        -timestamp32, -oracleElapsed])

theorem updateReservesAndEmitSync_run_storageMap_balances
    (key : Address)
    (balance0Now balance1Now reserve0Value reserve1Value
      timestamp32 previousTimestamp : Uint256)
    (s : ContractState) :
    ((UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
      reserve0Value reserve1Value timestamp32 previousTimestamp).run s).snd.storageMap
        balancesSlot.slot key =
      s.storageMap balancesSlot.slot key :=
  contractPreservesStorageMap_run_snd key
    (UniswapV2PairBase.updateReservesAndEmitSync balance0Now balance1Now
      reserve0Value reserve1Value timestamp32 previousTimestamp)
    (contractPreservesStorageMap_updateReservesAndEmitSync key
      balance0Now balance1Now reserve0Value reserve1Value timestamp32 previousTimestamp)
    s


end TamaUniV2.Proof.UniswapV2PairProof
