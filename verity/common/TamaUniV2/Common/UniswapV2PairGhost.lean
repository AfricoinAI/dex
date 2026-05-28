-- SPDX-License-Identifier: AGPL-3.0-only
import TamaUniV2.UniswapV2Pair

/-!
Closed-world ghost model for Uniswap V2 pair economic invariants.

The executable pair reads ERC20 balances through ECMs. This module follows the
same pattern as Tamago's ERC4626 closed-world specs: model finite successful
action traces explicitly, prove economic invariants over that model, and keep
the model outside `verity/spec` so only public obligations are audited.

The alphabet is intentionally economic rather than bytecode-shaped. LP
approvals and transfers are modeled because they must not change pool assets.
`donate` represents direct ERC20 inflow that the pair did not initiate.
`mint`, `burn`, `swap`, `skim`, and `sync` represent the successful public AMM
entrypoints after executable bridge facts have established their arithmetic
preconditions.

Within this model, "all possible histories" means every finite sequence whose
steps satisfy `PairWorldStep`. The public specs prove one-step facts, then
finite-path facts, then reachable-state corollaries. This mirrors the Tamago
ERC4626 style: proof over traces first, executable calls bridged into those
traces second, and no extra trust surface for internal accounting.
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

def PairWorldSurplus0 (w : PairWorldState) : Nat :=
  w.balance0 - w.reserve0

def PairWorldSurplus1 (w : PairWorldState) : Nat :=
  w.balance1 - w.reserve1

def PairWorldKPerSupplyNondecreasing (before after : PairWorldState) : Prop :=
  PairWorldK before * after.totalSupply * after.totalSupply ≤
    PairWorldK after * before.totalSupply * before.totalSupply

def PairWorldSpotValueNum (spot pool : PairWorldState) : Nat :=
  pool.reserve0 * spot.reserve1 + pool.reserve1 * spot.reserve0

def PairWorldBalanceSpotValueNum (spot pool : PairWorldState) : Nat :=
  pool.balance0 * spot.reserve1 + pool.balance1 * spot.reserve0

def PairWorldSurplusSpotValueNum (spot pool : PairWorldState) : Nat :=
  PairWorldSurplus0 pool * spot.reserve1 +
    PairWorldSurplus1 pool * spot.reserve0

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
  0 < amount0 ∧
  0 < amount1 ∧
  0 < liquidity ∧
  0 < before.totalSupply ∧
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
    requiredK before.reserve0 before.reserve1

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

structure PairWalletWorldState where
  pair : PairWorldState
  callerToken0 : Nat
  callerToken1 : Nat
  callerLp : Nat
  pairLp : Nat
  recv0 : Nat
  recv1 : Nat
  recvLp : Nat
  give0 : Nat
  give1 : Nat
  giveLp : Nat
  deriving Repr, BEq

def PairWalletGood (w : PairWalletWorldState) : Prop :=
  PairWorldGood w.pair ∧
    w.callerLp + w.pairLp + w.pair.lockedLiquidity ≤ w.pair.totalSupply

def PairWalletFlowEmpty (w : PairWalletWorldState) : Prop :=
  w.recv0 = 0 ∧
  w.recv1 = 0 ∧
  w.recvLp = 0 ∧
  w.give0 = 0 ∧
  w.give1 = 0 ∧
  w.giveLp = 0

def PairWalletCallerTokenValueAtSpot
    (spot : PairWorldState) (w : PairWalletWorldState) : Nat :=
  w.callerToken0 * spot.reserve1 +
    w.callerToken1 * spot.reserve0

def PairWalletSkimmableValueAtSpot
    (spot : PairWorldState) (w : PairWalletWorldState) : Nat :=
  PairWorldSurplusSpotValueNum spot w.pair

def PairWalletPortfolioValueNumeratorAtSpot
    (spot : PairWorldState) (w : PairWalletWorldState) : Nat :=
  PairWalletCallerTokenValueAtSpot spot w * w.pair.totalSupply +
    w.callerLp * PairWorldSpotValueNum spot w.pair +
    PairWalletSkimmableValueAtSpot spot w * w.pair.totalSupply

def PairWalletTotalTokenValueAtSpot
    (spot : PairWorldState) (w : PairWalletWorldState) : Nat :=
  PairWalletCallerTokenValueAtSpot spot w +
    PairWorldBalanceSpotValueNum spot w.pair

/-- Price of token0 in token1 at the spot's reserves. Undefined (returns 0 by
Lean's `/` convention) when `spot.reserve0 = 0`; callers guard against that. -/
def PairWorldSpotPriceRat (spot : PairWorldState) : ℚ :=
  (spot.reserve1 : ℚ) / spot.reserve0

/-- Value of `(token0, token1)` denominated in token1, at the spot's price. -/
def PairWorldTokenValueRat
    (spot : PairWorldState) (token0 token1 : Nat) : ℚ :=
  (token0 : ℚ) * PairWorldSpotPriceRat spot + token1

def PairWorldLpValueRat
    (spot pool : PairWorldState) (liquidity : Nat) : ℚ :=
  (liquidity : ℚ) * ((PairWorldSpotValueNum spot pool : ℚ) /
    ((pool.totalSupply : ℚ) * (spot.reserve0 : ℚ)))

def PairWorldSurplusValueRat (spot pool : PairWorldState) : ℚ :=
  PairWorldTokenValueRat spot (PairWorldSurplus0 pool) (PairWorldSurplus1 pool)

def PairWalletFlowReceivedValueAtSpot
    (spot : PairWorldState) (w : PairWalletWorldState) : ℚ :=
  PairWorldTokenValueRat spot w.recv0 w.recv1 +
    PairWorldLpValueRat spot w.pair w.recvLp + PairWorldSurplusValueRat spot w.pair

def PairWalletFlowGivenValueAtSpot
    (spot : PairWorldState) (w : PairWalletWorldState) : ℚ :=
  PairWorldTokenValueRat spot w.give0 w.give1 +
    PairWorldLpValueRat spot w.pair w.giveLp

def PairWalletInitialClaimValueAtSpot
    (spot : PairWorldState) (w : PairWalletWorldState) : ℚ :=
  PairWorldLpValueRat spot w.pair (w.callerLp + w.pairLp) +
    PairWorldSurplusValueRat spot w.pair

/-- The caller's portfolio value in token1, at the spot's prices.

Sums four sources of value: the caller's directly-held tokens, their fractional
claim on the pool's reserves through their LP shares, and any donations sitting
in the pair as skimmable surplus. -/
def PairWalletPortfolioValueInToken1
    (spot : PairWorldState) (w : PairWalletWorldState) : ℚ :=
  let pool := w.pair
  let poolValueInToken1 :=
    PairWorldTokenValueRat spot pool.reserve0 pool.reserve1
  PairWorldTokenValueRat spot w.callerToken0 w.callerToken1
    + (w.callerLp : ℚ) * poolValueInToken1 / pool.totalSupply
    + PairWorldTokenValueRat spot
        (PairWorldSurplus0 pool) (PairWorldSurplus1 pool)

inductive PairWalletAction where
  | callerApprove
  | callerDonate (amount0 amount1 : Nat)
  | callerSkimReceive (amount0 amount1 : Nat)
  | callerSwap (give0 give1 amount0Out amount1Out : Nat)
  | callerMint (amount0 amount1 liquidity : Nat)
  | callerBurn (amount0 amount1 transferredLiquidity burnedLiquidity : Nat)
  | callerSync
  deriving Repr, BEq

def PairWalletStep
    (action : PairWalletAction)
    (before after : PairWalletWorldState) : Prop :=
  match action with
  | PairWalletAction.callerApprove =>
      after.pair = before.pair ∧
      after.callerToken0 = before.callerToken0 ∧
      after.callerToken1 = before.callerToken1 ∧
      after.callerLp = before.callerLp ∧
      after.pairLp = before.pairLp ∧
      after.recv0 = before.recv0 ∧
      after.recv1 = before.recv1 ∧
      after.recvLp = before.recvLp ∧
      after.give0 = before.give0 ∧
      after.give1 = before.give1 ∧
      after.giveLp = before.giveLp
  | PairWalletAction.callerDonate amount0 amount1 =>
      before.callerToken0 ≥ amount0 ∧
      before.callerToken1 ≥ amount1 ∧
      PairWorldStep (PairWorldAction.donate amount0 amount1) before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 - amount0 ∧
      after.callerToken1 = before.callerToken1 - amount1 ∧
      after.callerLp = before.callerLp ∧
      after.pairLp = before.pairLp ∧
      after.recv0 = before.recv0 ∧
      after.recv1 = before.recv1 ∧
      after.recvLp = before.recvLp ∧
      after.give0 = before.give0 + amount0 ∧
      after.give1 = before.give1 + amount1 ∧
      after.giveLp = before.giveLp
  | PairWalletAction.callerSkimReceive amount0 amount1 =>
      PairWorldStep PairWorldAction.skim before.pair after.pair ∧
      amount0 = PairWorldSurplus0 before.pair ∧
      amount1 = PairWorldSurplus1 before.pair ∧
      after.callerToken0 = before.callerToken0 + amount0 ∧
      after.callerToken1 = before.callerToken1 + amount1 ∧
      after.callerLp = before.callerLp ∧
      after.pairLp = before.pairLp ∧
      after.recv0 = before.recv0 + amount0 ∧
      after.recv1 = before.recv1 + amount1 ∧
      after.recvLp = before.recvLp ∧
      after.give0 = before.give0 ∧
      after.give1 = before.give1 ∧
      after.giveLp = before.giveLp
  | PairWalletAction.callerSwap give0 give1 amount0Out amount1Out =>
      PairWorldStep
        (PairWorldAction.swap
          (give0 + PairWorldSurplus0 before.pair)
          (give1 + PairWorldSurplus1 before.pair)
          amount0Out amount1Out)
        before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 + amount0Out ∧
      after.callerToken1 = before.callerToken1 + amount1Out ∧
      after.callerLp = before.callerLp ∧
      after.pairLp = before.pairLp ∧
      after.recv0 = before.recv0 + amount0Out ∧
      after.recv1 = before.recv1 + amount1Out ∧
      after.recvLp = before.recvLp ∧
      after.give0 = before.give0 + give0 ∧
      after.give1 = before.give1 + give1 ∧
      after.giveLp = before.giveLp
  | PairWalletAction.callerMint amount0 amount1 liquidity =>
      PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before.pair after.pair ∧
      amount0 = PairWorldSurplus0 before.pair ∧
      amount1 = PairWorldSurplus1 before.pair ∧
      after.callerToken0 = before.callerToken0 ∧
      after.callerToken1 = before.callerToken1 ∧
      after.callerLp = before.callerLp + liquidity ∧
      after.pairLp = before.pairLp ∧
      after.recv0 = before.recv0 ∧
      after.recv1 = before.recv1 ∧
      after.recvLp = before.recvLp + liquidity ∧
      after.give0 = before.give0 ∧
      after.give1 = before.give1 ∧
      after.giveLp = before.giveLp
  | PairWalletAction.callerBurn amount0 amount1 transferredLiquidity burnedLiquidity =>
      before.callerLp ≥ transferredLiquidity ∧
      PairWorldStep (PairWorldAction.burn amount0 amount1 burnedLiquidity) before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 + amount0 ∧
      after.callerToken1 = before.callerToken1 + amount1 ∧
      after.callerLp = before.callerLp - transferredLiquidity ∧
      after.pairLp + burnedLiquidity = before.pairLp + transferredLiquidity ∧
      after.recv0 = before.recv0 + amount0 ∧
      after.recv1 = before.recv1 + amount1 ∧
      after.recvLp = before.recvLp ∧
      after.give0 = before.give0 ∧
      after.give1 = before.give1 ∧
      after.giveLp = before.giveLp + transferredLiquidity
  | PairWalletAction.callerSync =>
      PairWorldStep PairWorldAction.sync before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 ∧
      after.callerToken1 = before.callerToken1 ∧
      after.callerLp = before.callerLp ∧
      after.pairLp = before.pairLp ∧
      after.recv0 = before.recv0 ∧
      after.recv1 = before.recv1 ∧
      after.recvLp = before.recvLp ∧
      after.give0 = before.give0 ∧
      after.give1 = before.give1 ∧
      after.giveLp = before.giveLp

inductive PairWalletHistory : PairWalletWorldState → PairWalletWorldState → Prop where
  | refl (w : PairWalletWorldState) : PairWalletHistory w w
  | step {start before after : PairWalletWorldState} (action : PairWalletAction) :
      PairWalletHistory start before →
      PairWalletStep action before after →
      PairWalletHistory start after

def PairWalletActionOrdinary
    (action : PairWalletAction) (_before _after : PairWalletWorldState) : Prop :=
  match action with
  | PairWalletAction.callerSwap give0 give1 _ _ =>
      give0 = 0 ∧ give1 = 0
  | PairWalletAction.callerBurn _ _ transferredLiquidity burnedLiquidity =>
      transferredLiquidity = burnedLiquidity
  | _ => True

inductive OrdinaryPairWalletHistory :
    PairWalletWorldState → PairWalletWorldState → Prop where
  | refl (w : PairWalletWorldState) :
      PairWalletFlowEmpty w →
      OrdinaryPairWalletHistory w w
  | step {start before after : PairWalletWorldState} (action : PairWalletAction) :
      OrdinaryPairWalletHistory start before →
      PairWalletStep action before after →
      PairWalletActionOrdinary action before after →
      OrdinaryPairWalletHistory start after

def pair_wallet_single_caller_history_no_extraction
    (before after : PairWalletWorldState) : Prop :=
  PairWalletGood before → PairWalletFlowEmpty before →
    0 < before.pair.totalSupply → 0 < before.pair.reserve0 →
      0 < before.pair.reserve1 → PairWalletHistory before after →
        PairWalletFlowReceivedValueAtSpot before.pair after ≤
          PairWalletFlowGivenValueAtSpot before.pair after +
            PairWalletInitialClaimValueAtSpot before.pair before

inductive PairWorldPathNoBurn : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathNoBurn w w
  | step {start before after : PairWorldState} (action : PairWorldAction) :
      PairWorldPathNoBurn start before →
      PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      PairWorldPathNoBurn start after

inductive PairWorldPathNoMint : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathNoMint w w
  | step {start before after : PairWorldState} (action : PairWorldAction) :
      PairWorldPathNoMint start before →
      PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
      PairWorldPathNoMint start after

inductive PairWorldPathNoMintBurn : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathNoMintBurn w w
  | step {start before after : PairWorldState} (action : PairWorldAction) :
      PairWorldPathNoMintBurn start before →
      PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      PairWorldPathNoMintBurn start after

inductive PairWorldPathNoReserveUpdate : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathNoReserveUpdate w w
  | step {start before after : PairWorldState} (action : PairWorldAction) :
      PairWorldPathNoReserveUpdate start before →
      PairWorldStep action before after →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.mint amount0 amount1 liquidity) →
      (∀ amount0 amount1 liquidity,
        action ≠ PairWorldAction.burn amount0 amount1 liquidity) →
      (∀ amount0In amount1In amount0Out amount1Out,
        action ≠ PairWorldAction.swap amount0In amount1In amount0Out amount1Out) →
      action ≠ PairWorldAction.sync →
      PairWorldPathNoReserveUpdate start after

inductive PairWorldPathNoDonation : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathNoDonation w w
  | step {start before after : PairWorldState} (action : PairWorldAction) :
      PairWorldPathNoDonation start before →
      PairWorldStep action before after →
      (∀ amount0 amount1, action ≠ PairWorldAction.donate amount0 amount1) →
      PairWorldPathNoDonation start after

inductive PairWorldPathShareBookkeeping : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathShareBookkeeping w w
  | approve
      {start before after : PairWorldState}
      (ownerAddr spender : Address) (amount : Nat) :
      PairWorldPathShareBookkeeping start before →
      PairWorldStep (PairWorldAction.approve ownerAddr spender amount) before after →
      PairWorldPathShareBookkeeping start after
  | transfer
      {start before after : PairWorldState}
      (fromAddr toAddr : Address) (amount : Nat) :
      PairWorldPathShareBookkeeping start before →
      PairWorldStep (PairWorldAction.transfer fromAddr toAddr amount) before after →
      PairWorldPathShareBookkeeping start after
  | transferFrom
      {start before after : PairWorldState}
      (spender fromAddr toAddr : Address) (amount : Nat) :
      PairWorldPathShareBookkeeping start before →
      PairWorldStep
        (PairWorldAction.transferFrom spender fromAddr toAddr amount)
        before after →
      PairWorldPathShareBookkeeping start after

inductive PairWorldPathSkimSync : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathSkimSync w w
  | skim {start before after : PairWorldState} :
      PairWorldPathSkimSync start before →
      PairWorldStep PairWorldAction.skim before after →
      PairWorldPathSkimSync start after
  | sync {start before after : PairWorldState} :
      PairWorldPathSkimSync start before →
      PairWorldStep PairWorldAction.sync before after →
      PairWorldPathSkimSync start after

inductive PairWorldPathLpBookkeepingSkimSync : PairWorldState → PairWorldState → Prop where
  | refl (w : PairWorldState) : PairWorldPathLpBookkeepingSkimSync w w
  | approve
      {start before after : PairWorldState}
      (ownerAddr spender : Address) (amount : Nat) :
      PairWorldPathLpBookkeepingSkimSync start before →
      PairWorldStep (PairWorldAction.approve ownerAddr spender amount) before after →
      PairWorldPathLpBookkeepingSkimSync start after
  | transfer
      {start before after : PairWorldState}
      (fromAddr toAddr : Address) (amount : Nat) :
      PairWorldPathLpBookkeepingSkimSync start before →
      PairWorldStep (PairWorldAction.transfer fromAddr toAddr amount) before after →
      PairWorldPathLpBookkeepingSkimSync start after
  | transferFrom
      {start before after : PairWorldState}
      (spender fromAddr toAddr : Address) (amount : Nat) :
      PairWorldPathLpBookkeepingSkimSync start before →
      PairWorldStep
        (PairWorldAction.transferFrom spender fromAddr toAddr amount)
        before after →
      PairWorldPathLpBookkeepingSkimSync start after
  | skim {start before after : PairWorldState} :
      PairWorldPathLpBookkeepingSkimSync start before →
      PairWorldStep PairWorldAction.skim before after →
      PairWorldPathLpBookkeepingSkimSync start after
  | sync {start before after : PairWorldState} :
      PairWorldPathLpBookkeepingSkimSync start before →
      PairWorldStep PairWorldAction.sync before after →
      PairWorldPathLpBookkeepingSkimSync start after

end TamaUniV2.Common.UniswapV2PairGhost
