import TamaUniV2.UniswapV2Pair
import TamaUniV2.Common.UniswapV2PairGhost

/-!
Concrete helper formulas for Uniswap V2 pair specs.

This module intentionally lives outside `verity/spec`: Tama treats public
top-level definitions in spec modules as candidate obligations. The definitions
here mirror Tamago's ERC4626 helper modules and keep balance-read formulas
available to public specs without turning helper names into obligations.
-/

namespace TamaUniV2.Common.UniswapV2PairConcrete

open Verity
open TamaUniV2.UniswapV2Pair
open TamaUniV2.Common.UniswapV2PairGhost
open Tamago.Utils

def pairSelf (s : ContractState) : Address :=
  s.thisAddress

def pairToken0 (s : ContractState) : Address :=
  s.storageAddr token0Slot.slot

def pairToken1 (s : ContractState) : Address :=
  s.storageAddr token1Slot.slot

def observedBalance0 (s : ContractState) : Uint256 :=
  ((TamaUniV2.erc20BalanceOf (pairToken0 s) (pairSelf s)).run s).fst

def observedBalance1 (s : ContractState) : Uint256 :=
  ((TamaUniV2.erc20BalanceOf (pairToken1 s) (pairSelf s)).run s).fst

def pairLockedState (s : ContractState) : ContractState :=
  { s with «storage» := fun slotIdx => if slotIdx = unlockedSlot.slot then 0 else s.storage slotIdx }

structure PairCallbackObservation where
  target : Address
  sender : Address
  amount0Out : Uint256
  amount1Out : Uint256
  lockValue : Uint256
  deriving Repr, BEq

def pairCallbackObservationForSwap
    (amount0Out amount1Out : Uint256) (toAddr : Address)
    (s : ContractState) : PairCallbackObservation :=
  { target := toAddr
    sender := s.sender
    amount0Out := amount0Out
    amount1Out := amount1Out
    lockValue := 0 }

def pairObservedTokenBalance (token owner : Address) (s : ContractState) : Uint256 :=
  ((TamaUniV2.erc20BalanceOf token owner).run s).fst

def pairTraceContains (event : Event) (events : List Event) : Prop :=
  event ∈ events

def pairLpApprovalEvent
    (owner spender : Address) (amount : Uint256) : Event :=
  { name := "Approval"
    args := [addressToWord owner, addressToWord spender, amount]
    indexedArgs := [] }

def pairLpTransferEvent
    (fromAddr toAddr : Address) (amount : Uint256) : Event :=
  { name := "Transfer"
    args := [addressToWord fromAddr, addressToWord toAddr, amount]
    indexedArgs := [] }

def pairMintEvent
    (sender : Address) (amount0 amount1 : Uint256) : Event :=
  { name := "Mint"
    args := [addressToWord sender, amount0, amount1]
    indexedArgs := [] }

def pairBurnEvent
    (sender : Address) (amount0 amount1 : Uint256) (toAddr : Address) : Event :=
  { name := "Burn"
    args := [addressToWord sender, amount0, amount1, addressToWord toAddr]
    indexedArgs := [] }

def pairSwapEvent
    (sender : Address)
    (amount0In amount1In amount0Out amount1Out : Uint256)
    (toAddr : Address) : Event :=
  { name := "Swap"
    args := [
      addressToWord sender,
      amount0In,
      amount1In,
      amount0Out,
      amount1Out,
      addressToWord toAddr
    ]
    indexedArgs := [] }

def pairSyncEvent (reserve0 reserve1 : Uint256) : Event :=
  { name := "Sync"
    args := [reserve0, reserve1]
    indexedArgs := [] }

def hasPairSafeTransferTrace
    (token fromAddr toAddr : Address) (amount : Uint256)
    (s : ContractState) : Prop :=
  pairTraceContains
    (TamaUniV2.pairTokenSafeTransferEvent token fromAddr toAddr amount)
    s.events

abbrev PairTokenBalances := Address → Address → Uint256

def pairTokenBalancesUnchanged (pre post : PairTokenBalances) : Prop :=
  ∀ token account, post token account = pre token account

def pairTokenWorldAfterTransfer
    (pre : PairTokenBalances) (token fromAddr toAddr : Address) (amount : Uint256) :
    PairTokenBalances :=
  fun tokenValue account =>
    if tokenValue = token then
      if fromAddr = toAddr then
        pre tokenValue account
      else if account = fromAddr then
        Verity.EVM.Uint256.sub (pre tokenValue account) amount
      else if account = toAddr then
        pre tokenValue account + amount
      else
        pre tokenValue account
    else
      pre tokenValue account

def pairTokenWorldAfterEvent (pre : PairTokenBalances) (event : Event) :
    PairTokenBalances :=
  match event.name, event.args, event.indexedArgs with
  | "UniswapV2PairTokenSafeTransfer", [tokenWord, fromWord, toWord, amount], [] =>
      pairTokenWorldAfterTransfer pre
        (wordToAddress tokenWord) (wordToAddress fromWord) (wordToAddress toWord) amount
  | _, _, _ => pre

def pairTokenWorldAfterEvents : PairTokenBalances → List Event → PairTokenBalances
  | pre, [] => pre
  | pre, event :: events =>
      pairTokenWorldAfterEvents (pairTokenWorldAfterEvent pre event) events

def emittedPairEventsAfterCall {α : Type}
    (s : ContractState) (result : ContractResult α) : List Event :=
  result.snd.events.drop s.events.length

def pairTokenWorldAfterCall {α : Type}
    (pre : PairTokenBalances) (s : ContractState) (result : ContractResult α) :
    PairTokenBalances :=
  pairTokenWorldAfterEvents pre (emittedPairEventsAfterCall s result)

structure PairTransfer where
  token : Address
  fromAddr : Address
  toAddr : Address
  amount : Uint256

def pairTransferOfEvent : Event → Option PairTransfer
  | { name := "UniswapV2PairTokenSafeTransfer",
      args := [tokenWord, fromWord, toWord, amount],
      indexedArgs := [] } =>
      some {
        token := wordToAddress tokenWord
        fromAddr := wordToAddress fromWord
        toAddr := wordToAddress toWord
        amount := amount
      }
  | _ => none

def pairTransfersAfterEvents (events : List Event) : List PairTransfer :=
  events.filterMap pairTransferOfEvent

def pairTransfersAfterCall {α : Type}
    (s : ContractState) (result : ContractResult α) : List PairTransfer :=
  pairTransfersAfterEvents (emittedPairEventsAfterCall s result)

def pairTokenWorldAfterPairTransfer
    (pre : PairTokenBalances) (tr : PairTransfer) : PairTokenBalances :=
  pairTokenWorldAfterTransfer pre tr.token tr.fromAddr tr.toAddr tr.amount

def pairTokenWorldAfterPairTransfers :
    PairTokenBalances → List PairTransfer → PairTokenBalances :=
  List.foldl pairTokenWorldAfterPairTransfer

def pairRevertedWithOriginalState {α : Type}
    (s : ContractState) (result : ContractResult α) : Prop :=
  ∃ reason, result = ContractResult.revert reason s

def mintAmount0 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance0 s) (s.storage reserve0Slot.slot)

def mintAmount1 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance1 s) (s.storage reserve1Slot.slot)

def mintFirstProduct (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mul (mintAmount0 s) (mintAmount1 s)

def mintLockedState (s : ContractState) : ContractState :=
  { s with «storage» := fun slotIdx =>
      if slotIdx == unlockedSlot.slot then 0 else s.storage slotIdx }

def sqrtValue (x : Uint256) (s : ContractState) : Uint256 :=
  ((FixedPointMathLibBase.sqrt x).run s).fst

def mintFirstRoot (s : ContractState) : Uint256 :=
  sqrtValue (mintFirstProduct s) (mintLockedState s)

def mintFirstLiquidity (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (mintFirstRoot s) minimumLiquidity

def mintFirstPathProduct (amount0 amount1 : Uint256) : Uint256 :=
  Verity.EVM.Uint256.mul amount0 amount1

def mintFirstPathRoot (amount0 amount1 : Uint256) (s : ContractState) : Uint256 :=
  sqrtValue (mintFirstPathProduct amount0 amount1) s

def mintFirstPathLiquidity (amount0 amount1 : Uint256) (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (mintFirstPathRoot amount0 amount1 s) minimumLiquidity

def mintFirstRecipientBase (toAddr : Address) (s : ContractState) : Uint256 :=
  if toAddr == zeroAddress then
    minimumLiquidity
  else
    s.storageMap balancesSlot.slot toAddr

def mintFirstRecipientAfter (toAddr : Address) (amount0 amount1 : Uint256)
    (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.add
    (mintFirstRecipientBase toAddr s)
    (mintFirstPathLiquidity amount0 amount1 s)

def mintFirstZeroBalanceAfter (toAddr : Address) (amount0 amount1 : Uint256)
    (s : ContractState) : Uint256 :=
  if toAddr == zeroAddress then
    mintFirstRecipientAfter toAddr amount0 amount1 s
  else
    minimumLiquidity

def pairWorldAfterSubsequentMintRun
    (liquidity : Uint256) (s : ContractState) : PairWorldState :=
  { balance0 := (observedBalance0 s).val
    balance1 := (observedBalance1 s).val
    reserve0 := (observedBalance0 s).val
    reserve1 := (observedBalance1 s).val
    totalSupply := (s.storage totalSupplySlot.slot).val + liquidity.val
    lockedLiquidity :=
      if (s.storage totalSupplySlot.slot).val = 0 then 0 else minimumLiquidityNat }

def burnLiquidity (s : ContractState) : Uint256 :=
  s.storageMap balancesSlot.slot (pairSelf s)

def burnSupply (s : ContractState) : Uint256 :=
  s.storage totalSupplySlot.slot

def burnAmount0Product (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mul (burnLiquidity s) (observedBalance0 s)

def burnAmount1Product (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mul (burnLiquidity s) (observedBalance1 s)

def burnAmount0 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.div (burnAmount0Product s) (burnSupply s)

def burnAmount1 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.div (burnAmount1Product s) (burnSupply s)

def burnBalance0After (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance0 s) (burnAmount0 s)

def burnBalance1After (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance1 s) (burnAmount1 s)

def pairWorldLockedLiquidity (supply : Uint256) : Nat :=
  if supply.val = 0 then 0 else minimumLiquidityNat

def pairWorldFromConcreteState (s : ContractState) : PairWorldState :=
  { balance0 := (observedBalance0 s).val
    balance1 := (observedBalance1 s).val
    reserve0 := (s.storage reserve0Slot.slot).val
    reserve1 := (s.storage reserve1Slot.slot).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairTokenBalance0 (tokens : PairTokenBalances) (s : ContractState) : Uint256 :=
  tokens (pairToken0 s) (pairSelf s)

def pairTokenBalance1 (tokens : PairTokenBalances) (s : ContractState) : Uint256 :=
  tokens (pairToken1 s) (pairSelf s)

def callerTokenBalance0
    (caller : Address) (tokens : PairTokenBalances) (s : ContractState) : Uint256 :=
  tokens (pairToken0 s) caller

def callerTokenBalance1
    (caller : Address) (tokens : PairTokenBalances) (s : ContractState) : Uint256 :=
  tokens (pairToken1 s) caller

def pairWorldFromConcreteAndTokens
    (tokens : PairTokenBalances) (s : ContractState) : PairWorldState :=
  { balance0 := (pairTokenBalance0 tokens s).val
    balance1 := (pairTokenBalance1 tokens s).val
    reserve0 := (s.storage reserve0Slot.slot).val
    reserve1 := (s.storage reserve1Slot.slot).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairConcreteStorageMatchesWorld
    (s : ContractState) (w : PairWorldState) : Prop :=
  (s.storage reserve0Slot.slot).val = w.reserve0 ∧
  (s.storage reserve1Slot.slot).val = w.reserve1 ∧
  (s.storage totalSupplySlot.slot).val = w.totalSupply ∧
  pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) = w.lockedLiquidity

def pairTokenBalancesMatchWorld
    (tokens : PairTokenBalances) (s : ContractState)
    (w : PairWorldState) : Prop :=
  (pairTokenBalance0 tokens s).val = w.balance0 ∧
  (pairTokenBalance1 tokens s).val = w.balance1

def pairWalletFromConcreteAndTokens
    (caller : Address) (tokens : PairTokenBalances)
    (s : ContractState) : PairWalletWorldState :=
  { pair := pairWorldFromConcreteAndTokens tokens s
    callerToken0 := (callerTokenBalance0 caller tokens s).val
    callerToken1 := (callerTokenBalance1 caller tokens s).val
    callerLp := (s.storageMap balancesSlot.slot caller).val
    pairLp := (s.storageMap balancesSlot.slot (pairSelf s)).val
    recv0 := 0
    recv1 := 0
    recvLp := 0
    give0 := 0
    give1 := 0
    giveLp := 0 }

def pairWalletWithStepFlows
    (snapshot before : PairWalletWorldState)
    (recv0 recv1 recvLp give0 give1 giveLp : Nat) : PairWalletWorldState :=
  { snapshot with
    pairLp := before.pairLp
    recv0 := before.recv0 + recv0
    recv1 := before.recv1 + recv1
    recvLp := before.recvLp + recvLp
    give0 := before.give0 + give0
    give1 := before.give1 + give1
    giveLp := before.giveLp + giveLp }

def pairWorldBeforeMintRunAndTokens
    (tokens : PairTokenBalances) (s : ContractState) : PairWorldState :=
  pairWorldFromConcreteAndTokens tokens s

def pairWorldBeforeMintRun (s : ContractState) : PairWorldState :=
  { balance0 := (observedBalance0 s).val
    balance1 := (observedBalance1 s).val
    reserve0 := (s.storage reserve0Slot.slot).val
    reserve1 := (s.storage reserve1Slot.slot).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairWorldAfterFirstMintRun (s : ContractState) : PairWorldState :=
  { balance0 := (observedBalance0 s).val
    balance1 := (observedBalance1 s).val
    reserve0 := (observedBalance0 s).val
    reserve1 := (observedBalance1 s).val
    totalSupply := (mintFirstRoot s).val
    lockedLiquidity := minimumLiquidityNat }

def pairWorldAfterFirstMintRunAndTokens
    (tokens : PairTokenBalances) (s : ContractState) : PairWorldState :=
  { balance0 := (pairTokenBalance0 tokens s).val
    balance1 := (pairTokenBalance1 tokens s).val
    reserve0 := (pairTokenBalance0 tokens s).val
    reserve1 := (pairTokenBalance1 tokens s).val
    totalSupply := (mintFirstRoot s).val
    lockedLiquidity := minimumLiquidityNat }

def pairWorldAfterSubsequentMintRunAndTokens
    (tokens : PairTokenBalances) (liquidity : Uint256)
    (s : ContractState) : PairWorldState :=
  { balance0 := (pairTokenBalance0 tokens s).val
    balance1 := (pairTokenBalance1 tokens s).val
    reserve0 := (pairTokenBalance0 tokens s).val
    reserve1 := (pairTokenBalance1 tokens s).val
    totalSupply := (s.storage totalSupplySlot.slot).val + liquidity.val
    lockedLiquidity :=
      if (s.storage totalSupplySlot.slot).val = 0 then 0 else minimumLiquidityNat }

def pairWorldAfterSkimRun (s : ContractState) : PairWorldState :=
  { balance0 := (s.storage reserve0Slot.slot).val
    balance1 := (s.storage reserve1Slot.slot).val
    reserve0 := (s.storage reserve0Slot.slot).val
    reserve1 := (s.storage reserve1Slot.slot).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairWorldAfterSyncRun (s : ContractState) : PairWorldState :=
  { balance0 := (observedBalance0 s).val
    balance1 := (observedBalance1 s).val
    reserve0 := (observedBalance0 s).val
    reserve1 := (observedBalance1 s).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairWorldAfterSkimRunAndTokens
    (tokens : PairTokenBalances) (s : ContractState) : PairWorldState :=
  { balance0 := (pairTokenBalance0 tokens s).val
    balance1 := (pairTokenBalance1 tokens s).val
    reserve0 := (s.storage reserve0Slot.slot).val
    reserve1 := (s.storage reserve1Slot.slot).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairWorldAfterSyncRunAndTokens
    (tokens : PairTokenBalances) (s : ContractState) : PairWorldState :=
  { balance0 := (pairTokenBalance0 tokens s).val
    balance1 := (pairTokenBalance1 tokens s).val
    reserve0 := (pairTokenBalance0 tokens s).val
    reserve1 := (pairTokenBalance1 tokens s).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairWorldAfterBurnRun (s : ContractState) : PairWorldState :=
  { balance0 := (burnBalance0After s).val
    balance1 := (burnBalance1After s).val
    reserve0 := (burnBalance0After s).val
    reserve1 := (burnBalance1After s).val
    totalSupply := (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s)).val
    lockedLiquidity := pairWorldLockedLiquidity (burnSupply s) }

def pairWorldAfterBurnRunAndTokens
    (tokens : PairTokenBalances) (s : ContractState) : PairWorldState :=
  { balance0 := (pairTokenBalance0 tokens s).val
    balance1 := (pairTokenBalance1 tokens s).val
    reserve0 := (pairTokenBalance0 tokens s).val
    reserve1 := (pairTokenBalance1 tokens s).val
    totalSupply := (Verity.EVM.Uint256.sub (burnSupply s) (burnLiquidity s)).val
    lockedLiquidity := pairWorldLockedLiquidity (burnSupply s) }

def timestamp32 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mod s.blockTimestamp uint32Modulus

def oracleElapsed (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mod
    (Verity.EVM.Uint256.sub
      (Verity.EVM.Uint256.add (timestamp32 s) uint32Modulus)
      (s.storage blockTimestampLastSlot.slot))
    uint32Modulus

def oraclePrice0 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.div
    (Verity.EVM.Uint256.mul (s.storage reserve1Slot.slot) q112)
    (s.storage reserve0Slot.slot)

def oraclePrice1 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.div
    (Verity.EVM.Uint256.mul (s.storage reserve0Slot.slot) q112)
    (s.storage reserve1Slot.slot)

def oraclePrice0Increment (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mul (oraclePrice0 s) (oracleElapsed s)

def oraclePrice1Increment (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.mul (oraclePrice1 s) (oracleElapsed s)

def oraclePrice0CumulativeAfterElapsed (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.add
    (s.storage price0CumulativeLastSlot.slot)
    (oraclePrice0Increment s)

def oraclePrice1CumulativeAfterElapsed (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.add
    (s.storage price1CumulativeLastSlot.slot)
    (oraclePrice1Increment s)

def oraclePrice0CumulativeAfterSync (s : ContractState) : Uint256 :=
  if (timestamp32 s != s.storage blockTimestampLastSlot.slot) = true then
    if oracleElapsed s > 0 ∧
        s.storage reserve0Slot.slot > 0 ∧
        s.storage reserve1Slot.slot > 0 then
      oraclePrice0CumulativeAfterElapsed s
    else
      s.storage price0CumulativeLastSlot.slot
  else
    s.storage price0CumulativeLastSlot.slot

def oraclePrice1CumulativeAfterSync (s : ContractState) : Uint256 :=
  if (timestamp32 s != s.storage blockTimestampLastSlot.slot) = true then
    if oracleElapsed s > 0 ∧
        s.storage reserve0Slot.slot > 0 ∧
        s.storage reserve1Slot.slot > 0 then
      oraclePrice1CumulativeAfterElapsed s
    else
      s.storage price1CumulativeLastSlot.slot
  else
    s.storage price1CumulativeLastSlot.slot

def skimExcess0 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance0 s) (s.storage reserve0Slot.slot)

def skimExcess1 (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (observedBalance1 s) (s.storage reserve1Slot.slot)

def swapExpected0 (amount0Out : Uint256) (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (s.storage reserve0Slot.slot) amount0Out

def swapExpected1 (amount1Out : Uint256) (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.sub (s.storage reserve1Slot.slot) amount1Out

def swapAmountIn (balanceNow expected : Uint256) : Uint256 :=
  if balanceNow > expected then
    Verity.EVM.Uint256.sub balanceNow expected
  else
    0

def swapAmount0In (amount0Out : Uint256) (balance0Now : Uint256) (s : ContractState) :
    Uint256 :=
  swapAmountIn balance0Now (swapExpected0 amount0Out s)

def swapAmount1In (amount1Out : Uint256) (balance1Now : Uint256) (s : ContractState) :
    Uint256 :=
  swapAmountIn balance1Now (swapExpected1 amount1Out s)

def pairWorldAfterSwapRun
    (balance0Now balance1Now : Uint256) (s : ContractState) : PairWorldState :=
  { balance0 := balance0Now.val
    balance1 := balance1Now.val
    reserve0 := balance0Now.val
    reserve1 := balance1Now.val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairWorldAfterSwapRunAndTokens
    (tokens : PairTokenBalances) (s : ContractState) : PairWorldState :=
  { balance0 := (pairTokenBalance0 tokens s).val
    balance1 := (pairTokenBalance1 tokens s).val
    reserve0 := (pairTokenBalance0 tokens s).val
    reserve1 := (pairTokenBalance1 tokens s).val
    totalSupply := (s.storage totalSupplySlot.slot).val
    lockedLiquidity := pairWorldLockedLiquidity (s.storage totalSupplySlot.slot) }

def pairExternalTokenBalancesMatchCall {α : Type}
    (preTokens : PairTokenBalances) (s : ContractState)
    (result : ContractResult α)
    (before after : PairWorldState) : Prop :=
  let postTokens := pairTokenWorldAfterCall preTokens s result
  pairTokenBalancesMatchWorld preTokens s before ∧
    pairTokenBalancesMatchWorld postTokens result.snd after

def pairPostCallSelfBalancesMatch
    (s : ContractState) (post : ContractState) (b0 b1 : Uint256) : Prop :=
  ((TamaUniV2.erc20BalanceOf (pairToken0 s) (pairSelf s)).run post).fst = b0 ∧
    ((TamaUniV2.erc20BalanceOf (pairToken1 s) (pairSelf s)).run post).fst = b1

def pairFirstMintExternalTokenBalancesMatchCall
    (preTokens : PairTokenBalances) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  pairExternalTokenBalancesMatchCall preTokens s result
    (pairWorldBeforeMintRun s)
    (pairWorldAfterFirstMintRun s)

def pairLaterMintExternalTokenBalancesMatchCall
    (preTokens : PairTokenBalances) (s : ContractState)
    (liquidity : Uint256) (result : ContractResult Uint256) : Prop :=
  pairExternalTokenBalancesMatchCall preTokens s result
    (pairWorldBeforeMintRun s)
    (pairWorldAfterSubsequentMintRun liquidity s)

def pairBurnExternalTokenBalancesMatchCall
    (preTokens : PairTokenBalances) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  pairExternalTokenBalancesMatchCall preTokens s result
    (pairWorldFromConcreteState s)
    (pairWorldAfterBurnRun s)

def pairSwapExternalTokenBalancesMatchCall
    (preTokens : PairTokenBalances) (s : ContractState)
    (balance0Now balance1Now : Uint256)
    (result : ContractResult Unit) : Prop :=
  pairExternalTokenBalancesMatchCall preTokens s result
    (pairWorldFromConcreteState s)
    (pairWorldAfterSwapRun balance0Now balance1Now s)

def pairSkimExternalTokenBalancesMatchCall
    (preTokens : PairTokenBalances) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  pairExternalTokenBalancesMatchCall preTokens s result
    (pairWorldFromConcreteState s)
    (pairWorldAfterSkimRun s)

def pairSyncExternalTokenBalancesMatchCall
    (preTokens : PairTokenBalances) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  pairExternalTokenBalancesMatchCall preTokens s result
    (pairWorldFromConcreteState s)
    (pairWorldAfterSyncRun s)

inductive PairEconomicActionConcreteStep
    (caller : Address) : PairWalletWorldState → PairWalletWorldState → Prop where
  /-- A concrete economic step records a successful pair call and the
  corresponding caller-wallet transition used by the economic history. LP
  balances are pair storage; the normal-behavior assumption only concerns the
  external token0/token1 balances used by the action bridges. -/
  | mint
      {before after : PairWalletWorldState}
      (toAddr : Address) (preTokens : PairTokenBalances)
      (s : ContractState) (result : ContractResult Uint256)
      (liquidity : Uint256)
      (hRun : result = (TamaUniV2.UniswapV2Pair.mint toAddr).run s)
      (hSuccess : result = ContractResult.success liquidity result.snd)
      (hBefore : before = pairWalletFromConcreteAndTokens caller preTokens s)
      (hAfter :
        after =
          pairWalletWithStepFlows
            (pairWalletFromConcreteAndTokens caller
              (pairTokenWorldAfterCall preTokens s result) result.snd)
            before
            0 0 liquidity.val 0 0 0)
      (hToAddr : toAddr = caller)
      (hReserve0 : s.storage reserve0Slot.slot ≤ observedBalance0 s)
      (hReserve1 : s.storage reserve1Slot.slot ≤ observedBalance1 s)
      (hAmount0 : mintAmount0 s > 0)
      (hAmount1 : mintAmount1 s > 0)
      (hFirstExternal :
        s.storage totalSupplySlot.slot = 0 →
          pairFirstMintExternalTokenBalancesMatchCall preTokens s result)
      (hLaterExternal :
        s.storage totalSupplySlot.slot ≠ 0 →
          pairLaterMintExternalTokenBalancesMatchCall preTokens s liquidity result)
      (hFirstGuards :
        s.storage totalSupplySlot.slot = 0 →
          liquidity = mintFirstLiquidity s ∧
            (mintAmount0 s == 0 ||
              Verity.EVM.Uint256.div (mintFirstProduct s) (mintAmount0 s) ==
                mintAmount1 s) = true ∧
            mintFirstRoot s > minimumLiquidity)
      (hLaterGuards :
        s.storage totalSupplySlot.slot ≠ 0 →
          0 < (s.storage totalSupplySlot.slot).val ∧
            s.storage reserve0Slot.slot > 0 ∧
            s.storage reserve1Slot.slot > 0 ∧
            liquidity > 0 ∧
            liquidity.val * (s.storage reserve0Slot.slot).val ≤
              (mintAmount0 s).val * (s.storage totalSupplySlot.slot).val ∧
            liquidity.val * (s.storage reserve1Slot.slot).val ≤
              (mintAmount1 s).val * (s.storage totalSupplySlot.slot).val) :
      PairEconomicActionConcreteStep caller before after
  | burn
      {before after : PairWalletWorldState}
      (toAddr : Address) (preTokens : PairTokenBalances)
      (s : ContractState)
      (transferLiquidity : Uint256)
      (transferResult : ContractResult Bool)
      (burnResult : ContractResult (Uint256 × Uint256))
      (hTransferRun :
        transferResult =
          (TamaUniV2.UniswapV2Pair.transfer (pairSelf s) transferLiquidity).run s)
      (hTransferSuccess :
        transferResult = ContractResult.success true transferResult.snd)
      (hBurnRun : burnResult = (TamaUniV2.UniswapV2Pair.burn toAddr).run transferResult.snd)
      (hSuccess :
        burnResult =
          ContractResult.success
            (burnAmount0 transferResult.snd, burnAmount1 transferResult.snd)
            burnResult.snd)
      (hBefore : before = pairWalletFromConcreteAndTokens caller preTokens s)
      (hAfter :
        after =
          { pairWalletWithStepFlows
              (pairWalletFromConcreteAndTokens caller
                (pairTokenWorldAfterCall preTokens transferResult.snd burnResult)
                burnResult.snd)
              before
              (burnAmount0 transferResult.snd).val
              (burnAmount1 transferResult.snd).val
              0
              0
              0
              transferLiquidity.val with
            pairLp := (burnResult.snd.storageMap balancesSlot.slot
              (pairSelf transferResult.snd)).val })
      (hToAddr : toAddr = caller)
      (hSender : s.sender = caller)
      (hCallerNeSelf : caller ≠ pairSelf s)
      (hTransferBalance :
        transferLiquidity.val ≤ (s.storageMap balancesSlot.slot caller).val)
      (hTransferNoOverflow :
        (s.storageMap balancesSlot.slot (pairSelf s)).val + transferLiquidity.val ≤
          Verity.Stdlib.Math.MAX_UINT256)
      (hExternal :
        pairBurnExternalTokenBalancesMatchCall
          preTokens transferResult.snd burnResult)
      (hPostBalances :
        pairPostCallSelfBalancesMatch transferResult.snd burnResult.snd
          (burnBalance0After transferResult.snd)
          (burnBalance1After transferResult.snd))
      (hLiquidityPos : 0 < (burnLiquidity transferResult.snd).val)
      (hSupplyPos : 0 < (burnSupply transferResult.snd).val)
      (hLiquidityLe :
        (burnLiquidity transferResult.snd).val ≤ (burnSupply transferResult.snd).val)
      (hLockedRemaining :
        minimumLiquidityNat ≤
          (burnSupply transferResult.snd).val -
            (burnLiquidity transferResult.snd).val)
      (hAmount0Pos : burnAmount0 transferResult.snd > 0)
      (hAmount1Pos : burnAmount1 transferResult.snd > 0)
      (hAmount0Le :
        burnAmount0 transferResult.snd ≤ observedBalance0 transferResult.snd)
      (hAmount1Le :
        burnAmount1 transferResult.snd ≤ observedBalance1 transferResult.snd)
      (hBound0 : burnBalance0After transferResult.snd ≤ maxUint112)
      (hBound1 : burnBalance1After transferResult.snd ≤ maxUint112)
      (hRatio0 :
        (burnAmount0 transferResult.snd).val * (burnSupply transferResult.snd).val ≤
          (burnLiquidity transferResult.snd).val *
            (observedBalance0 transferResult.snd).val)
      (hRatio1 :
        (burnAmount1 transferResult.snd).val * (burnSupply transferResult.snd).val ≤
          (burnLiquidity transferResult.snd).val *
            (observedBalance1 transferResult.snd).val)
      (hTokenDistinct : pairToken0 transferResult.snd ≠ pairToken1 transferResult.snd)
      (hCallerToken0Add :
        (callerTokenBalance0 caller preTokens transferResult.snd).val +
            (burnAmount0 transferResult.snd).val <
          Core.Uint256.modulus)
      (hCallerToken1Add :
        (callerTokenBalance1 caller preTokens transferResult.snd).val +
            (burnAmount1 transferResult.snd).val <
          Core.Uint256.modulus) :
      PairEconomicActionConcreteStep caller before after
  | swap
      {before after : PairWalletWorldState}
      (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
      (balance0Now balance1Now : Uint256) (preTokens : PairTokenBalances)
      (s : ContractState) (result : ContractResult Unit)
      (hRun :
        result =
          (TamaUniV2.UniswapV2Pair.swap amount0Out amount1Out toAddr data).run s)
      (hSuccess : result = ContractResult.success () result.snd)
      (hBefore : before = pairWalletFromConcreteAndTokens caller preTokens s)
      (hAfter :
        after =
          pairWalletWithStepFlows
            (pairWalletFromConcreteAndTokens caller
              (pairTokenWorldAfterCall preTokens s result) result.snd)
            before
            amount0Out.val amount1Out.val 0
            ((swapAmount0In amount0Out balance0Now s).val -
              PairWorldSurplus0 (pairWorldFromConcreteState s))
            ((swapAmount1In amount1Out balance1Now s).val -
              PairWorldSurplus1 (pairWorldFromConcreteState s))
            0)
      (hExternal :
        pairSwapExternalTokenBalancesMatchCall
          preTokens s balance0Now balance1Now result)
      (hBalance0Le :
        (observedBalance0 s).val ≤ balance0Now.val + amount0Out.val)
      (hBalance1Le :
        (observedBalance1 s).val ≤ balance1Now.val + amount1Out.val)
      (hToAddr : toAddr = caller)
      (hCallerNeSelf : caller ≠ pairSelf s)
      (hTokenDistinct : pairToken0 s ≠ pairToken1 s)
      (hCallerToken0Add :
        (callerTokenBalance0 caller preTokens s).val + amount0Out.val <
          Core.Uint256.modulus)
      (hCallerToken1Add :
        (callerTokenBalance1 caller preTokens s).val + amount1Out.val <
          Core.Uint256.modulus)
      (hPostBalances :
        pairPostCallSelfBalancesMatch s result.snd balance0Now balance1Now)
      (hAmount0OutLt : amount0Out < s.storage reserve0Slot.slot)
      (hAmount1OutLt : amount1Out < s.storage reserve1Slot.slot)
      (hInput :
        swapAmount0In amount0Out balance0Now s > 0 ∨
          swapAmount1In amount1Out balance1Now s > 0)
      (hBalance0 :
        balance0Now.val =
          (s.storage reserve0Slot.slot).val +
            (swapAmount0In amount0Out balance0Now s).val - amount0Out.val)
      (hBalance1 :
        balance1Now.val =
          (s.storage reserve1Slot.slot).val +
            (swapAmount1In amount1Out balance1Now s).val - amount1Out.val)
      (hBound0 : balance0Now ≤ maxUint112)
      (hBound1 : balance1Now ≤ maxUint112)
      (hFee0 :
        (swapAmount0In amount0Out balance0Now s).val * feeAdjustmentNat ≤
          balance0Now.val * feeDenominatorNat)
      (hFee1 :
        (swapAmount1In amount1Out balance1Now s).val * feeAdjustmentNat ≤
          balance1Now.val * feeDenominatorNat)
      (hAdjustedK :
        feeAdjustedBalance balance0Now.val
            (swapAmount0In amount0Out balance0Now s).val *
          feeAdjustedBalance balance1Now.val
            (swapAmount1In amount1Out balance1Now s).val ≥
            requiredK
              (s.storage reserve0Slot.slot).val
              (s.storage reserve1Slot.slot).val) :
      PairEconomicActionConcreteStep caller before after
  | skim
      {before after : PairWalletWorldState}
      (toAddr : Address) (preTokens : PairTokenBalances)
      (s : ContractState) (result : ContractResult Unit)
      (hRun : result = (TamaUniV2.UniswapV2Pair.skim toAddr).run s)
      (hSuccess : result = ContractResult.success () result.snd)
      (hBefore : before = pairWalletFromConcreteAndTokens caller preTokens s)
      (hAfter :
        after =
          pairWalletWithStepFlows
            (pairWalletFromConcreteAndTokens caller
              (pairTokenWorldAfterCall preTokens s result) result.snd)
            before
            (skimExcess0 s).val (skimExcess1 s).val 0 0 0 0)
      (hExternal : pairSkimExternalTokenBalancesMatchCall preTokens s result)
      (hToAddr : toAddr = caller)
      (hCallerNeSelf : caller ≠ pairSelf s)
      (hTokenDistinct : pairToken0 s ≠ pairToken1 s)
      (hCallerToken0Add :
        (callerTokenBalance0 caller preTokens s).val + (skimExcess0 s).val <
          Core.Uint256.modulus)
      (hCallerToken1Add :
        (callerTokenBalance1 caller preTokens s).val + (skimExcess1 s).val <
          Core.Uint256.modulus) :
      PairEconomicActionConcreteStep caller before after
  | sync
      {before after : PairWalletWorldState}
      (preTokens : PairTokenBalances)
      (s : ContractState) (result : ContractResult Unit)
      (hRun : result = (TamaUniV2.UniswapV2Pair.sync).run s)
      (hSuccess : result = ContractResult.success () result.snd)
      (hBefore : before = pairWalletFromConcreteAndTokens caller preTokens s)
      (hAfter :
        after =
          pairWalletWithStepFlows
            (pairWalletFromConcreteAndTokens caller
              (pairTokenWorldAfterCall preTokens s result) result.snd)
            before
            0 0 0 0 0 0)
      (hExternal : pairSyncExternalTokenBalancesMatchCall preTokens s result) :
      PairEconomicActionConcreteStep caller before after

inductive PairEconomicActionConcretePath
    (caller : Address) : PairWalletWorldState → PairWalletWorldState → Prop where
  | refl (w : PairWalletWorldState) :
      PairEconomicActionConcretePath caller w w
  | step {start before after : PairWalletWorldState} :
      PairEconomicActionConcretePath caller start before →
      PairEconomicActionConcreteStep caller before after →
      PairEconomicActionConcretePath caller start after

def swapBalance0Scaled (balance0Now : Uint256) : Uint256 :=
  Verity.EVM.Uint256.mul balance0Now feeDenominator

def swapBalance1Scaled (balance1Now : Uint256) : Uint256 :=
  Verity.EVM.Uint256.mul balance1Now feeDenominator

def swapAmount0Fee (amount0In : Uint256) : Uint256 :=
  Verity.EVM.Uint256.mul amount0In feeAdjustment

def swapAmount1Fee (amount1In : Uint256) : Uint256 :=
  Verity.EVM.Uint256.mul amount1In feeAdjustment

def swapBalance0Adjusted (balance0Now amount0In : Uint256) : Uint256 :=
  Verity.EVM.Uint256.sub (swapBalance0Scaled balance0Now) (swapAmount0Fee amount0In)

def swapBalance1Adjusted (balance1Now amount1In : Uint256) : Uint256 :=
  Verity.EVM.Uint256.sub (swapBalance1Scaled balance1Now) (swapAmount1Fee amount1In)

def swapAdjustedProduct
    (balance0Now balance1Now amount0In amount1In : Uint256) : Uint256 :=
  Verity.EVM.Uint256.mul
    (swapBalance0Adjusted balance0Now amount0In)
    (swapBalance1Adjusted balance1Now amount1In)

def swapReserveProductOf (reserve0Value reserve1Value : Uint256) : Uint256 :=
  Verity.EVM.Uint256.mul reserve0Value reserve1Value

def swapReserveProduct (s : ContractState) : Uint256 :=
  swapReserveProductOf (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)

def swapScaleProduct : Uint256 :=
  Verity.EVM.Uint256.mul feeDenominator feeDenominator

def swapRequiredProductOf (reserve0Value reserve1Value : Uint256) : Uint256 :=
  Verity.EVM.Uint256.mul (swapReserveProductOf reserve0Value reserve1Value) swapScaleProduct

def swapRequiredProduct (s : ContractState) : Uint256 :=
  swapRequiredProductOf (s.storage reserve0Slot.slot) (s.storage reserve1Slot.slot)

end TamaUniV2.Common.UniswapV2PairConcrete
