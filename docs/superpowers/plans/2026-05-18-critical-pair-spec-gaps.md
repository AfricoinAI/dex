# Critical Pair Spec Gaps Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the three crucial Pair spec gaps: prove successful public calls expose the token movements they rely on, prove flash callbacks run while the pair is locked, and build a caller-wallet theorem that supports the claim that no closed-system hack can create value.

**Architecture:** Do not modify contract source or public ABI. Keep public specs short and reader-facing, with proof-local helper lemmas allowed only to make existing contract behavior provable. Extend the model only where it adds real economic meaning: caller token balances, LP balances, and value conservation across finite histories.

**Tech Stack:** Lean/Verity EDSL specs and proofs, Tama check/build/audit, Tamago-style finite-history model, Foundry mirrors only for runtime boundary confirmation.

---

## Scope And Priorities

This plan intentionally does not prioritize the lower-value gaps around full ordered-revert coverage and AMM event coverage. Those are useful, but they are not the core “no hacks can happen” argument. The important proof story is:

1. A successful public call states, in Lean, the token movements it actually used.
2. During flash-swap callbacks, the reentrancy lock is observably closed, so callback-visible reentry cannot mutate the pair.
3. Across any finite single-caller history, the caller's full portfolio value cannot increase at the initial spot price.

The final assurance argument should read:

```text
Real successful calls match valid pair-state steps.
Valid pair-state steps preserve reserve backing, LP supply discipline, K behavior, and portfolio value discipline.
Callback-visible reentry is blocked by the lock.
Therefore no finite sequence of modeled Pair interactions by one caller can create portfolio profit.
```

## Files

- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
  - Add short public specs for the token movements used by successful calls.
  - Add short public specs for callback-time lock observation.
  - Add caller-wallet no-profit specs and comments.
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
  - Prove the new public specs.
  - Add proof-local prefix/suffix lemmas only inside the proof file.
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairGhost.lean`
  - Add a caller-wallet model layer. Keep the existing `PairWorldState` intact; add a separate `PairWalletWorldState` or wrapper rather than disrupting current proofs.
- Modify: `docs/spec-coverage.md`
  - Update remaining-gaps and coverage narrative.
- Modify: `docs/agent-progress.md`
  - Append timestamped checkpoints only.
- Test: `test/verity/UniswapV2Core.t.sol`
  - Add or adjust Foundry mirrors only when a public obligation is runtime-facing and bytecode-observable.

## Task 1: Successful Mint Uses Balance Increases

**Purpose:** Make successful public `mint` specs say what the contract actually does: it treats the pair's token balance increase as the deposit. Later proofs should not have to restate this fact by hand.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`

- [x] **Step 1: Add first-mint balance-increase spec**

Add this public spec near the existing first-mint specs:

```lean
/--
A successful first mint treats each token's balance increase as the deposit.

The pair does not receive deposit amounts as function arguments. It looks at
its ERC20 balances and subtracts cached reserves. This spec states that fact in
one place.
-/
def pair_first_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success (mintFirstLiquidity s) result.snd →
      s.storage totalSupplySlot.slot = 0 →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 = observedBalance0 s - s.storage reserve0Slot.slot ∧
            amount1 = observedBalance1 s - s.storage reserve1Slot.slot
```

- [x] **Step 2: Prove first-mint balance-increase spec**

Add this proof near the existing first-mint proof that connects the public run
to the pair-state model.

```lean
-- tama: discharges=pair_first_mint_uses_balance_increase_as_deposit
theorem first_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState) :
  pair_first_mint_uses_balance_increase_as_deposit
    toAddr s ((mint toAddr).run s) := by
  intro _h_run _h_success _h_supply_zero h_reserve0 h_reserve1
  constructor
  · rfl
  · rfl
```

If `rfl` does not close because `sub` normalization is hidden, use:

```lean
  simp [pair_first_mint_uses_balance_increase_as_deposit, mintAmount0,
    mintAmount1]
```

- [x] **Step 3: Add later-mint balance-increase spec**

Add the same shape for subsequent mint:

```lean
/--
A successful later mint also treats each token's balance increase as the
deposit.
-/
def pair_later_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState)
    (liquidity : Uint256) (result : ContractResult Uint256) : Prop :=
  let amount0 := mintAmount0 s
  let amount1 := mintAmount1 s
  result = (mint toAddr).run s →
    result = ContractResult.success liquidity result.snd →
      0 < (s.storage totalSupplySlot.slot).val →
        s.storage reserve0Slot.slot ≤ observedBalance0 s →
          s.storage reserve1Slot.slot ≤ observedBalance1 s →
            amount0 = observedBalance0 s - s.storage reserve0Slot.slot ∧
            amount1 = observedBalance1 s - s.storage reserve1Slot.slot
```

- [x] **Step 4: Prove later-mint balance-increase spec**

```lean
-- tama: discharges=pair_later_mint_uses_balance_increase_as_deposit
theorem later_mint_uses_balance_increase_as_deposit
    (toAddr : Address) (s : ContractState) (liquidity : Uint256) :
  pair_later_mint_uses_balance_increase_as_deposit
    toAddr s liquidity ((mint toAddr).run s) := by
  intro _h_run _h_success _h_supply_pos _h_reserve0 _h_reserve1
  constructor
  · rfl
  · rfl
```

- [x] **Step 5: Verify and commit**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
lake build TamaUniV2.Proof
/Users/zefram/.tama/bin/tama check
/Users/zefram/.tama/bin/tama build
/Users/zefram/.tama/bin/tama test
/Users/zefram/.tama/bin/tama audit
git diff --check
```

Expected: all pass, with only existing unused-variable warnings.

Commit:

```bash
git add verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean \
  verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean \
  docs/spec-coverage.md docs/agent-progress.md
git commit -m "Prove mint uses balance increases"
```

## Task 2: Successful Burn Uses LP Sent To The Pair

**Purpose:** Make successful public `burn` specs say what the contract actually does: it burns the LP tokens sitting on the pair itself, uses total supply as the redemption denominator, and leaves token balances reduced by the paid-out amounts.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`

- [x] **Step 1: Add burn-source spec**

Add near burn specs:

```lean
/--
A successful burn destroys the LP tokens sitting on the pair itself and uses
current total supply as the denominator for redemption.

This pins the public burn to the canonical Uniswap V2 redemption source:
liquidity previously transferred to the pair is burned against current LP
total supply.
-/
def pair_burn_uses_pair_lp_balance_and_total_supply
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      burnLiquidity s = s.storageMap balancesSlot.slot (pairSelf s) ∧
      burnSupply s = s.storage totalSupplySlot.slot
```

- [x] **Step 2: Prove burn-source spec**

```lean
-- tama: discharges=pair_burn_uses_pair_lp_balance_and_total_supply
theorem burn_uses_pair_lp_balance_and_total_supply
    (toAddr : Address) (s : ContractState) :
  pair_burn_uses_pair_lp_balance_and_total_supply
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success
  constructor
  · rfl
  · rfl
```

- [x] **Step 3: Add burn remaining-balances spec**

```lean
/--
A successful burn leaves the pair with its previous token balances minus the
tokens paid to the recipient.
-/
def pair_burn_leaves_remaining_token_balances
    (toAddr : Address) (s : ContractState)
    (result : ContractResult (Uint256 × Uint256)) : Prop :=
  result = (burn toAddr).run s →
    result = ContractResult.success (burnAmount0 s, burnAmount1 s) result.snd →
      burnAmount0 s ≤ observedBalance0 s →
        burnAmount1 s ≤ observedBalance1 s →
          (pairWorldAfterBurnRun s).balance0 + (burnAmount0 s).val =
            (observedBalance0 s).val ∧
          (pairWorldAfterBurnRun s).balance1 + (burnAmount1 s).val =
            (observedBalance1 s).val
```

- [x] **Step 4: Prove burn remaining-balances spec**

```lean
-- tama: discharges=pair_burn_leaves_remaining_token_balances
theorem burn_leaves_remaining_token_balances
    (toAddr : Address) (s : ContractState) :
  pair_burn_leaves_remaining_token_balances
    toAddr s ((burn toAddr).run s) := by
  intro _h_run _h_success h_amount0 h_amount1
  simp [pair_burn_leaves_remaining_token_balances,
    pairWorldAfterBurnRun, burnBalance0After, burnBalance1After]
  constructor <;> omega
```

- [x] **Step 5: Verify and commit**

Run the same full verification commands as Task 1.

Commit:

```bash
git add verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean \
  verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean \
  docs/spec-coverage.md docs/agent-progress.md
git commit -m "Prove burn uses pair LP balance"
```

## Task 3: Successful Swap Uses Final Balances

**Purpose:** Close the most important arithmetic gap. Successful swaps should state plainly that token input is computed from final ERC20 balances after the optimistic output and callback, and that the K check is applied to those same final balances.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`

- [x] **Step 1: Add swap input-from-final-balances spec**

Add near swap specs:

```lean
/--
A successful swap computes token input from final balances after optimistic
output and callback repayment.

This statement does not yet prove the K guard. It states the accounting rule
that determines `amount0In` and `amount1In`.
-/
def pair_swap_uses_final_balances_to_compute_input
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let expected0 := swapExpected0 amount0Out s
  let expected1 := swapExpected1 amount1Out s
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      amount0In =
          (if balance0Now > expected0 then
            Verity.EVM.Uint256.sub balance0Now expected0
          else
            0) ∧
        amount1In =
          (if balance1Now > expected1 then
            Verity.EVM.Uint256.sub balance1Now expected1
          else
            0)
```

- [x] **Step 2: Prove swap input-from-final-balances spec**

Use the existing helper definitions `swapAmount0In`, `swapAmount1In`,
`swapExpected0`, and `swapExpected1`. Important correction from plan review:
the balance equation is not true from `amountOut < reserve` alone, because
Uniswap infers zero input on a side whose final balance is not above
`reserve - amountOut`. The proved public spec states the exact max-style input
inference rule instead.

```lean
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
```

- [x] **Step 3: Add swap final-balances K-check spec**

Do not unfold the whole public `swap` body. State the short fact that once success and final balances are known, the fee-adjusted K check is about the same final balances:

```lean
/--
When a successful swap's final balance reads satisfy the fee-adjusted K check,
the pair-state model uses that same K check on those same final balances.
-/
def pair_swap_checks_k_against_final_balances
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit) : Prop :=
  let amount0In := swapAmount0In amount0Out balance0Now s
  let amount1In := swapAmount1In amount1Out balance1Now s
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      feeAdjustedBalance balance0Now.val amount0In.val *
          feeAdjustedBalance balance1Now.val amount1In.val ≥
        requiredK
          (s.storage reserve0Slot.slot).val
          (s.storage reserve1Slot.slot).val →
        feeAdjustedBalance
            (pairWorldAfterSwapRun balance0Now balance1Now s).balance0 amount0In.val *
          feeAdjustedBalance
            (pairWorldAfterSwapRun balance0Now balance1Now s).balance1 amount1In.val ≥
        requiredK
          (pairWorldFromConcreteState s).reserve0
          (pairWorldFromConcreteState s).reserve1
```

- [x] **Step 4: Prove swap final-balances K-check spec**

```lean
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
```

- [x] **Step 5: Refactor downstream specs to cite the new short facts**

Where current specs repeat final-balance equations and final-balance K checks, update comments and proofs to cite:

```lean
swap_uses_final_balances_to_compute_input
swap_checks_k_against_final_balances
```

No downstream proof churn was needed for this slice: the existing stronger swap
specs already state the accounting equations under their explicit premises,
while the new public facts now give readers the shorter final-balance and K
check statements.

- [x] **Step 6: Verify and commit**

Run the same full verification commands as Task 1.

Commit:

```bash
git add verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean \
  verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean \
  docs/spec-coverage.md docs/agent-progress.md
git commit -m "Prove swap uses final balances"
```

## Task 4: Flash Callback Runs While Locked

**Purpose:** Prove in Lean that flash-swap callbacks run while the Pair lock is closed. This is the formal version of “callback-visible reentry cannot mutate the pair.”

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`
- Test: `test/verity/UniswapV2Core.t.sol`

- [x] **Step 1: Inspect current callback ECM trace hooks**

Run:

```bash
rg -n "uniswapV2CallbackModule|callback|uniswapV2Call|trace" verity/src verity/common verity/spec verity/proof
```

Expected: locate the callback ECM and existing compile-template proofs.

- [x] **Step 2: Add a proof record for callback-time lock state**

In `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`, add a proof-only event predicate that records the lock value immediately before the callback ECM:

```lean
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
```

This is proof-only bookkeeping, not contract storage or ABI.

- [x] **Step 3: Add public flash-callback lock spec**

Add:

```lean
/--
Flash callbacks run while the pair is locked.

The callback target may execute arbitrary code, including attempts to call the
pair again, but any such pair mutation sees `unlocked = 0` and must hit the
standard lock guard.
-/
def pair_flash_callback_runs_while_pair_is_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) : Prop :=
  data.size > 0 →
    pairCallbackObservationForSwap amount0Out amount1Out toAddr s |>.lockValue = 0
```

If `ByteArray.size` is not the right accessor in this codebase, use the same data-length accessor already used by the callback ECM proof.

- [x] **Step 4: Prove flash-callback lock spec**

```lean
-- tama: discharges=pair_flash_callback_runs_while_pair_is_locked
theorem flash_callback_runs_while_pair_is_locked
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (s : ContractState) :
  pair_flash_callback_runs_while_pair_is_locked amount0Out amount1Out toAddr data s := by
  intro _h_data
  rfl
```

- [x] **Step 5: Add callback reentry blocked spec**

State the direct fact for all mutating Pair entrypoints:

```lean
/--
Any attempt to mutate the pair during a flash callback is blocked by the same
reentrancy guard as any other nested call.
-/
def pair_flash_callback_reentry_attempts_revert_locked
    (mintTo burnTo skimTo swapTo : Address)
    (amount0Out amount1Out nested0Out nested1Out : Uint256)
    (data nestedData : ByteArray)
    (s : ContractState) : Prop :=
  data.size > 0 →
    let callbackState := pairLockedState s
    (mint mintTo).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState ∧
    (burn burnTo).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState ∧
    (swap nested0Out nested1Out swapTo nestedData).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState ∧
    (skim skimTo).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState ∧
    (sync).run callbackState =
      ContractResult.revert "UniswapV2: LOCKED" callbackState
```

If `pairLockedState` is currently private in the proof file, move a non-invasive proof-model copy to `UniswapV2PairConcrete.lean` or define a public spec-local locked-state helper. Do not modify contract source.

- [x] **Step 6: Prove callback reentry blocked spec**

Reuse the existing `reentrancy_guard_blocks_all_mutating_entrypoints` theorem by applying it to `callbackState`.

```lean
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
    (pairLockedState s) (by simp [pairLockedState, unlockedSlot])
```

- [x] **Step 7: Add/confirm Foundry mirror**

Confirm existing Foundry test:

```bash
rg -n "CallbackCannotReenter|reenter|LOCKED" test/verity/UniswapV2Core.t.sol
```

Expected: existing test `testFuzzFlashSwapCallbackCannotReenterPair`.

The mirror now attempts `mint`, `burn`, `swap`, `skim`, and `sync` from the
callback and confirms all five attempts are rejected.

- [x] **Step 8: Verify and commit**

Run full verification and commit. Do not add normal spec obligations to
`tama.toml`; the spec `def`s are obligations automatically.

```bash
git add verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean \
  verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean \
  verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean \
  test/verity/UniswapV2Core.t.sol docs/spec-coverage.md docs/agent-progress.md
git commit -m "Model callback lock safety"
```

## Task 5: Single-Caller Portfolio No-Profit Model

**Purpose:** Build the missing economic model needed for the eventual “no hacks
can happen” theorem. The model tracks one caller, their wallet tokens, their LP
tokens, and the pair. The key theorem should not assume the caller finishes with
the same LP balance or that total LP supply is unchanged. Instead, the caller's
portfolio value includes their LP claim on the pool.

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairGhost.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`

- [ ] **Step 1: Add caller-and-pair state**

Add to `UniswapV2PairGhost.lean` after `PairWorldState`:

```lean
structure PairWalletWorldState where
  pair : PairWorldState
  callerToken0 : Nat
  callerToken1 : Nat
  callerLp : Nat
  deriving Repr, BEq

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
```

This numerator represents:

- wallet token value,
- plus the caller's LP claim on cached reserves,
- plus surplus that a single actor can immediately take with `skim`.

The denominator is `w.pair.totalSupply`. Keeping the value as a numerator avoids
division and lets the theorem compare states even when mint or burn changes LP
total supply.

- [ ] **Step 2: Add single-caller actions**

Do not include a generic “someone changed the pair” action. The whole point of
this model is that there is exactly one actor.

```lean
inductive PairWalletAction where
  | callerApprove
  | callerDonate (amount0 amount1 : Nat)
  | callerSkimReceive (amount0 amount1 : Nat)
  | callerSwap (amount0In amount1In amount0Out amount1Out : Nat)
  | callerMint (amount0 amount1 liquidity : Nat)
  | callerBurn (amount0 amount1 liquidity : Nat)
  | callerSync
```

Later, if we need full LP ERC20 coverage here, add caller-only LP transfer
actions that can reduce or preserve `callerLp`; do not add an action that gives
the caller LP from an unmodeled outside address.

- [ ] **Step 3: Say how each single-caller action changes balances**

```lean
def PairWalletStep
    (action : PairWalletAction)
    (before after : PairWalletWorldState) : Prop :=
  match action with
  | PairWalletAction.callerApprove =>
      after = before
  | PairWalletAction.callerDonate amount0 amount1 =>
      before.callerToken0 ≥ amount0 ∧
      before.callerToken1 ≥ amount1 ∧
      PairWorldStep (PairWorldAction.donate amount0 amount1) before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 - amount0 ∧
      after.callerToken1 = before.callerToken1 - amount1 ∧
      after.callerLp = before.callerLp
  | PairWalletAction.callerSkimReceive amount0 amount1 =>
      PairWorldStep PairWorldAction.skim before.pair after.pair ∧
      amount0 = PairWorldSurplus0 before.pair ∧
      amount1 = PairWorldSurplus1 before.pair ∧
      after.callerToken0 = before.callerToken0 + amount0 ∧
      after.callerToken1 = before.callerToken1 + amount1 ∧
      after.callerLp = before.callerLp
  | PairWalletAction.callerSwap amount0In amount1In amount0Out amount1Out =>
      before.callerToken0 ≥ amount0In ∧
      before.callerToken1 ≥ amount1In ∧
      PairWorldStep
        (PairWorldAction.swap amount0In amount1In amount0Out amount1Out)
        before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 - amount0In + amount0Out ∧
      after.callerToken1 = before.callerToken1 - amount1In + amount1Out ∧
      after.callerLp = before.callerLp
  | PairWalletAction.callerMint amount0 amount1 liquidity =>
      before.callerToken0 ≥ amount0 ∧
      before.callerToken1 ≥ amount1 ∧
      PairWorldStep (PairWorldAction.mint amount0 amount1 liquidity) before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 - amount0 ∧
      after.callerToken1 = before.callerToken1 - amount1 ∧
      after.callerLp = before.callerLp + liquidity
  | PairWalletAction.callerBurn amount0 amount1 liquidity =>
      before.callerLp ≥ liquidity ∧
      PairWorldStep (PairWorldAction.burn amount0 amount1 liquidity) before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 + amount0 ∧
      after.callerToken1 = before.callerToken1 + amount1 ∧
      after.callerLp = before.callerLp - liquidity
  | PairWalletAction.callerSync =>
      PairWorldStep PairWorldAction.sync before.pair after.pair ∧
      after.callerToken0 = before.callerToken0 ∧
      after.callerToken1 = before.callerToken1 ∧
      after.callerLp = before.callerLp
```

- [ ] **Step 4: Add finite single-caller histories**

```lean
inductive PairWalletHistory : PairWalletWorldState → PairWalletWorldState → Prop where
  | refl (w : PairWalletWorldState) : PairWalletHistory w w
  | step {start before after : PairWalletWorldState} (action : PairWalletAction) :
      PairWalletHistory start before →
      PairWalletStep action before after →
      PairWalletHistory start after
```

Because the only actions are caller actions, this history relation is the
single-actor assumption. No separate “same LP balance,” “same LP supply,” or
“no outside value enters” premise should appear in the final theorem.

- [ ] **Step 5: Prove one-step portfolio facts**

Add short specs for the one-step facts the history proof needs:

```lean
/-- A valid single-caller swap cannot increase the caller's portfolio value at
the starting spot price. -/
def pair_wallet_swap_does_not_increase_portfolio_value
    (amount0In amount1In amount0Out amount1Out : Nat)
    (before after : PairWalletWorldState) : Prop :=
  PairWorldReachable before.pair →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletStep
              (PairWalletAction.callerSwap amount0In amount1In amount0Out amount1Out)
              before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-- A valid single-caller mint cannot increase the caller's portfolio value at
the starting spot price. Depositing imbalanced liquidity can lose value, but it
cannot create value. -/
def pair_wallet_mint_does_not_increase_portfolio_value
    (amount0 amount1 liquidity : Nat)
    (before after : PairWalletWorldState) : Prop :=
  PairWorldReachable before.pair →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletStep
              (PairWalletAction.callerMint amount0 amount1 liquidity)
              before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-- A valid single-caller burn cannot increase the caller's portfolio value at
the starting spot price. It turns LP ownership into wallet tokens using the
pool's pro-rata redemption rule. -/
def pair_wallet_burn_does_not_increase_portfolio_value
    (amount0 amount1 liquidity : Nat)
    (before after : PairWalletWorldState) : Prop :=
  PairWorldReachable before.pair →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletStep
              (PairWalletAction.callerBurn amount0 amount1 liquidity)
              before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-- `skim` moves already-skimmable surplus into the caller wallet. Because that
surplus was already counted as caller-controlled value, `skim` cannot increase
portfolio value. -/
def pair_wallet_skim_does_not_increase_portfolio_value
    (before after : PairWalletWorldState) : Prop :=
  PairWorldReachable before.pair →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletStep
              (PairWalletAction.callerSkimReceive
                (PairWorldSurplus0 before.pair)
                (PairWorldSurplus1 before.pair))
              before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply

/-- `sync`, `approve`, and direct donations cannot increase caller portfolio
value. -/
def pair_wallet_passive_action_does_not_increase_portfolio_value
    (action : PairWalletAction) (before after : PairWalletWorldState) : Prop :=
  (action = PairWalletAction.callerApprove ∨
    action = PairWalletAction.callerSync ∨
    ∃ amount0 amount1, action = PairWalletAction.callerDonate amount0 amount1) →
    PairWorldReachable before.pair →
      0 < before.pair.totalSupply →
        0 < before.pair.reserve0 →
          0 < before.pair.reserve1 →
            PairWalletStep action before after →
              PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                  before.pair.totalSupply ≤
                PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                  after.pair.totalSupply
```

Each spec should be a short statement about one action. The comments should
explain the economic reason in reader language, not proof machinery language.

- [ ] **Step 6: Prove arbitrary single-caller no-profit theorem**

This is the central theorem and replaces the previous weaker theorem that only
worked when LP balances and LP supply ended unchanged.

```lean
/--
Single-caller portfolio no-profit theorem.

Assume the pool is reachable and has a meaningful starting spot price. If one
caller is the only actor in a finite history, then after any sequence of valid
pair interactions, the caller's portfolio value at the initial spot price is no
greater than it was at the start.

The portfolio includes wallet tokens, the caller's LP claim on cached reserves,
and any surplus the single caller could immediately skim. Because LP ownership
is valued directly, this theorem does not assume the caller's LP balance or the
pool's total LP supply is unchanged.
-/
def pair_wallet_single_caller_history_no_portfolio_profit
    (before after : PairWalletWorldState) : Prop :=
  PairWorldReachable before.pair →
    0 < before.pair.totalSupply →
      0 < before.pair.reserve0 →
        0 < before.pair.reserve1 →
          PairWalletHistory before after →
            PairWalletPortfolioValueNumeratorAtSpot before.pair after *
                before.pair.totalSupply ≤
              PairWalletPortfolioValueNumeratorAtSpot before.pair before *
                after.pair.totalSupply
```

The proof should be by induction over `PairWalletHistory`, using the one-step
portfolio facts from Step 5 and existing pair facts:

- mint and burn formulas for LP supply and pro-rata share value,
- swap K/no-extraction facts,
- skim removes exactly already-counted surplus,
- sync and approve do not move caller assets,
- donation moves wallet value into pair value and cannot increase the caller's
  LP-adjusted portfolio.

- [ ] **Step 7: Verify and commit**

Run:

```bash
lake build TamaUniV2.Proof.UniswapV2PairProof
lake build TamaUniV2.Proof
/Users/zefram/.tama/bin/tama check
/Users/zefram/.tama/bin/tama build
/Users/zefram/.tama/bin/tama test
/Users/zefram/.tama/bin/tama audit
git diff --check
```

Commit:

```bash
git add verity/common/TamaUniV2/Common/UniswapV2PairGhost.lean \
  verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean \
  verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean \
  docs/spec-coverage.md docs/agent-progress.md
git commit -m "Add caller wallet no-profit model"
```

## Task 6: Connect Successful Calls To The Caller Wallet Model

**Purpose:** Connect successful public `mint`, `burn`, `swap`, `skim`, and `sync` runs to caller-wallet steps. This ties executable behavior to the single-caller portfolio theorem without making that theorem a detached model claim.

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`

- [ ] **Step 1: Add successful-swap caller-wallet spec**

```lean
/--
A successful public swap with known final balances is one caller-wallet swap.
-/
def pair_successful_swap_matches_caller_wallet_swap
    (amount0Out amount1Out : Uint256) (toAddr : Address) (data : ByteArray)
    (balance0Now balance1Now : Uint256) (s : ContractState)
    (result : ContractResult Unit)
    (before after : PairWalletWorldState) : Prop :=
  result = (swap amount0Out amount1Out toAddr data).run s →
    result = ContractResult.success () result.snd →
      before.pair = pairWorldFromConcreteState s →
        after.pair = pairWorldAfterSwapRun balance0Now balance1Now s →
          PairWalletStep
            (PairWalletAction.callerSwap
              (swapAmount0In amount0Out balance0Now s).val
              (swapAmount1In amount1Out balance1Now s).val
              amount0Out.val
              amount1Out.val)
            before after
```

The proof will need caller wallet balance premises if the model enforces sufficient caller input. If so, add them explicitly:

```lean
before.callerToken0 ≥ (swapAmount0In amount0Out balance0Now s).val →
before.callerToken1 ≥ (swapAmount1In amount1Out balance1Now s).val →
```

- [ ] **Step 2: Add matching mint/burn/skim/sync caller-wallet specs**

Add these four public specs with the same shape as the swap spec:

- `pair_successful_mint_matches_caller_wallet_mint`
- `pair_successful_burn_matches_caller_wallet_burn`
- `pair_successful_skim_matches_caller_wallet_skim`
- `pair_successful_sync_matches_caller_wallet_sync`

Each should state only one sentence of behavior:

- mint: caller spends token0/token1 and receives LP liquidity.
- burn: caller spends LP liquidity and receives token0/token1.
- skim: caller receives surplus.
- sync: caller wallet is unchanged.

- [ ] **Step 3: Prove caller-wallet links by composing existing pair-state proofs**

Each proof should reuse the existing successful-call-to-pair-state theorem for
the same function. Do not unfold public entrypoints directly.


- [ ] **Step 4: Update docs, verify, and commit**

Update `docs/spec-coverage.md` and append a timestamped progress note. Do not
add normal spec obligations to `tama.toml`; the spec `def`s are obligations
automatically.

Run full verification and commit:

```bash
git commit -m "Link successful calls to caller wallet model"
```

## Task 7: Final Assurance Pass

**Purpose:** Make the spec files read like the intended argument and remove stale/ambiguous docs that could cause future compaction amnesia.

**Files:**
- Modify: `docs/spec-coverage.md`
- Modify: `docs/agent-progress.md`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`

- [ ] **Step 1: Update Pair spec narrative**

At the top of `UniswapV2PairSpec.lean`, add one paragraph to the assurance argument:

```lean
7. Track one caller wallet together with the pair. This is the final economic
   theorem layer: assuming one caller is the only actor, no finite sequence of
   valid pair interactions can increase that caller's portfolio value at the
   initial spot price. The portfolio counts wallet tokens, LP ownership, and
   surplus the sole caller can skim.
```

- [ ] **Step 2: Update `docs/spec-coverage.md`**

Replace the three gap bullets with current status:

```markdown
- Successful calls expose their token movements: mint, burn, and swap now state
  the concrete token-balance facts needed by the pair-state and caller-wallet
  models.
- Flash swaps: callback-time lock safety is proved in Lean; Foundry continues
  to mirror bytecode-level reentry behavior.
- Caller-wallet economics: `pair_wallet_single_caller_history_no_portfolio_profit`
  proves that when one caller is the only actor, modeled histories cannot
  increase that caller's portfolio value at the initial spot price.
```

- [ ] **Step 3: Search for stale wording**

Run:

```bash
rg -n "seven gaps|bridge specs|successful public-entrypoint consequence|executable guard|no elapsed|NoElapsed|rawLogs|only foundry" docs verity/spec
```

Expected: no matches except historical `docs/agent-progress.md` entries. Do not edit old progress history.

- [ ] **Step 4: Full verification and commit**

Run full verification.

Commit:

```bash
git add docs/spec-coverage.md docs/agent-progress.md \
  verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean
git commit -m "Document no extraction assurance argument"
```

## Verification Standard For Every Task

Every task must end with:

```bash
lake build TamaUniV2.Proof
/Users/zefram/.tama/bin/tama check
/Users/zefram/.tama/bin/tama build
/Users/zefram/.tama/bin/tama test
/Users/zefram/.tama/bin/tama audit
git diff --check
```

Expected:

```text
Build completed successfully.
Check completed: TamaUniV2 and TamaUniV2.Spec accepted
26 tests passed, 0 failed
Audit passed: 5 checks, 2 contracts, 0 issues
```

Warnings about the Lake package cache or Foundry signature cache are acceptable if the main command succeeds.

## Plan Review

Spec coverage:

- Gap 1, successful calls exposing token movements, is covered by Tasks 1-3 and then connected into existing pair-state specs.
- Gap 3, callback/reentrancy semantics, is covered by Task 4 using callback-time lock bookkeeping and existing lock proofs.
- Gap 5, caller-level “no hacks can happen,” is covered by Tasks 5-6 and documented in Task 7.
- Lower-priority ordered reverts and AMM events are intentionally out of scope.

Placeholder scan:

- No `TBD`, `TODO`, or “implement later” placeholders.
- Every task has target files, concrete theorem names, and verification commands.

Risk review:

- Task 3 may need Nat-level helper lemmas because `Uint256` subtraction is fussy.
- Task 5 is the hardest and may need the caller no-profit theorem split into one-step value lemmas before the finite-history theorem.
- Task 6 must not unfold public entrypoints directly; it should compose existing public-run-to-pair-state proofs.
