import TamaUniV2.UniswapV2Pair

/-!
Closed-world ghost model for Uniswap V2 pair economic invariants.

The executable pair reads ERC20 balances through ECMs. This module follows the
same pattern as Tamago's ERC4626 closed-world specs: model finite successful
action traces explicitly, prove economic invariants over that model, and keep
the model outside `verity/spec` so only public obligations are audited.
-/

namespace TamaUniV2.Common.UniswapV2PairGhost

open Verity

def minimumLiquidityNat : Nat := 1000
def maxUint112Nat : Nat := 5192296858534827628530496329220095
def feeDenominatorNat : Nat := 1000
def feeAdjustmentNat : Nat := 3

structure PairWorldState where
  balance0 : Nat
  balance1 : Nat
  reserve0 : Nat
  reserve1 : Nat
  totalSupply : Nat
  lockedLiquidity : Nat
  deriving Repr, BEq

def PairWorldSupplyGood (w : PairWorldState) : Prop :=
  (w.totalSupply = 0 ∧ w.lockedLiquidity = 0) ∨
    (0 < w.totalSupply ∧
      w.lockedLiquidity = minimumLiquidityNat ∧
      minimumLiquidityNat ≤ w.totalSupply)

def PairWorldGood (w : PairWorldState) : Prop :=
  w.reserve0 ≤ w.balance0 ∧
  w.reserve1 ≤ w.balance1 ∧
  w.reserve0 ≤ maxUint112Nat ∧
  w.reserve1 ≤ maxUint112Nat ∧
  PairWorldSupplyGood w

def feeAdjustedBalance (balance amountIn : Nat) : Nat :=
  balance * feeDenominatorNat - amountIn * feeAdjustmentNat

def requiredK (reserve0 reserve1 : Nat) : Nat :=
  reserve0 * reserve1 * feeDenominatorNat * feeDenominatorNat

def PairWorldK (w : PairWorldState) : Nat :=
  w.reserve0 * w.reserve1

def PairWorldSpotValueNum (spot pool : PairWorldState) : Nat :=
  pool.reserve0 * spot.reserve1 + pool.reserve1 * spot.reserve0

def PairWorldNoSpotProfit (before after : PairWorldState) : Prop :=
  2 * PairWorldK before ≤ PairWorldSpotValueNum before after

def PairWorldMintStep
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  0 < amount0 ∧
  0 < amount1 ∧
  0 < liquidity ∧
  before.balance0 = before.reserve0 + amount0 ∧
  before.balance1 = before.reserve1 + amount1 ∧
  after.balance0 = before.balance0 ∧
  after.balance1 = before.balance1 ∧
  after.reserve0 = before.balance0 ∧
  after.reserve1 = before.balance1 ∧
  after.reserve0 ≤ maxUint112Nat ∧
  after.reserve1 ≤ maxUint112Nat ∧
  after.totalSupply =
    (if before.totalSupply = 0 then
      minimumLiquidityNat + liquidity
    else
      before.totalSupply + liquidity) ∧
  after.lockedLiquidity =
    (if before.totalSupply = 0 then
      minimumLiquidityNat
    else
      before.lockedLiquidity) ∧
  (before.totalSupply = 0 ∨
    liquidity * before.reserve0 ≤ amount0 * before.totalSupply ∧
    liquidity * before.reserve1 ≤ amount1 * before.totalSupply)

def PairWorldBurnStep
    (amount0 amount1 liquidity : Nat)
    (before after : PairWorldState) : Prop :=
  amount0 ≤ before.balance0 ∧
  amount1 ≤ before.balance1 ∧
  liquidity ≤ before.totalSupply ∧
  before.lockedLiquidity ≤ before.totalSupply - liquidity ∧
  after.balance0 = before.balance0 - amount0 ∧
  after.balance1 = before.balance1 - amount1 ∧
  after.reserve0 = after.balance0 ∧
  after.reserve1 = after.balance1 ∧
  after.reserve0 ≤ maxUint112Nat ∧
  after.reserve1 ≤ maxUint112Nat ∧
  after.totalSupply = before.totalSupply - liquidity ∧
  after.lockedLiquidity = before.lockedLiquidity ∧
  amount0 * before.totalSupply ≤ liquidity * before.balance0 ∧
  amount1 * before.totalSupply ≤ liquidity * before.balance1

def PairWorldSwapStep
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWorldState) : Prop :=
  (0 < amount0Out ∨ 0 < amount1Out) ∧
  amount0Out < before.reserve0 ∧
  amount1Out < before.reserve1 ∧
  before.reserve0 + amount0In ≥ amount0Out ∧
  before.reserve1 + amount1In ≥ amount1Out ∧
  (0 < amount0In ∨ 0 < amount1In) ∧
  after.balance0 = before.reserve0 + amount0In - amount0Out ∧
  after.balance1 = before.reserve1 + amount1In - amount1Out ∧
  after.reserve0 = after.balance0 ∧
  after.reserve1 = after.balance1 ∧
  after.reserve0 ≤ maxUint112Nat ∧
  after.reserve1 ≤ maxUint112Nat ∧
  after.totalSupply = before.totalSupply ∧
  after.lockedLiquidity = before.lockedLiquidity ∧
  amount0In * feeAdjustmentNat ≤ after.balance0 * feeDenominatorNat ∧
  amount1In * feeAdjustmentNat ≤ after.balance1 * feeDenominatorNat ∧
  feeAdjustedBalance after.balance0 amount0In *
      feeAdjustedBalance after.balance1 amount1In ≥
    requiredK before.reserve0 before.reserve1 ∧
  PairWorldK before ≤ PairWorldK after

def PairWorldSkimStep (before after : PairWorldState) : Prop :=
  after.balance0 = before.reserve0 ∧
  after.balance1 = before.reserve1 ∧
  after.reserve0 = before.reserve0 ∧
  after.reserve1 = before.reserve1 ∧
  after.totalSupply = before.totalSupply ∧
  after.lockedLiquidity = before.lockedLiquidity

def PairWorldSyncStep (before after : PairWorldState) : Prop :=
  before.balance0 ≤ maxUint112Nat ∧
  before.balance1 ≤ maxUint112Nat ∧
  after.balance0 = before.balance0 ∧
  after.balance1 = before.balance1 ∧
  after.reserve0 = before.balance0 ∧
  after.reserve1 = before.balance1 ∧
  after.totalSupply = before.totalSupply ∧
  after.lockedLiquidity = before.lockedLiquidity

inductive PairWorldAction where
  | approve (ownerAddr spender : Address) (amount : Nat)
  | transfer (fromAddr toAddr : Address) (amount : Nat)
  | transferFrom (spender fromAddr toAddr : Address) (amount : Nat)
  | donate (amount0 amount1 : Nat)
  | mint (amount0 amount1 liquidity : Nat)
  | burn (amount0 amount1 liquidity : Nat)
  | swap (amount0In amount1In amount0Out amount1Out : Nat)
  | skim
  | sync

def PairWorldStep
    (action : PairWorldAction) (before after : PairWorldState) : Prop :=
  match action with
  | PairWorldAction.approve _ _ _ => after = before
  | PairWorldAction.transfer _ _ _ => after = before
  | PairWorldAction.transferFrom _ _ _ _ => after = before
  | PairWorldAction.donate amount0 amount1 =>
      after.balance0 = before.balance0 + amount0 ∧
      after.balance1 = before.balance1 + amount1 ∧
      after.reserve0 = before.reserve0 ∧
      after.reserve1 = before.reserve1 ∧
      after.totalSupply = before.totalSupply ∧
      after.lockedLiquidity = before.lockedLiquidity
  | PairWorldAction.mint amount0 amount1 liquidity =>
      PairWorldMintStep amount0 amount1 liquidity before after
  | PairWorldAction.burn amount0 amount1 liquidity =>
      PairWorldBurnStep amount0 amount1 liquidity before after
  | PairWorldAction.swap amount0In amount1In amount0Out amount1Out =>
      PairWorldSwapStep amount0In amount1In amount0Out amount1Out before after
  | PairWorldAction.skim =>
      PairWorldSkimStep before after
  | PairWorldAction.sync =>
      PairWorldSyncStep before after

def PairWorldInitial : PairWorldState :=
  { balance0 := 0
    balance1 := 0
    reserve0 := 0
    reserve1 := 0
    totalSupply := 0
    lockedLiquidity := 0 }

inductive PairWorldReachable : PairWorldState → Prop where
  | init : PairWorldReachable PairWorldInitial
  | step {before after : PairWorldState} (action : PairWorldAction) :
      PairWorldReachable before →
      PairWorldStep action before after →
      PairWorldReachable after

inductive PairWorldPath : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPath w w
  | step {start before after : PairWorldState} (action : PairWorldAction) :
      PairWorldPath start before →
      PairWorldStep action before after →
      PairWorldPath start after

inductive PairWorldPathNoBurn : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathNoBurn w w
  | step {start before after : PairWorldState} (action : PairWorldAction) :
      PairWorldPathNoBurn start before →
      PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      PairWorldPathNoBurn start after

end TamaUniV2.Common.UniswapV2PairGhost
