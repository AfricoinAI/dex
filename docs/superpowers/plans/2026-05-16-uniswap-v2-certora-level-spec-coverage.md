# Uniswap V2 Certora-Level Spec Coverage Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the seven major spec gaps so the supported fee-off Uniswap V2 core surface has executable success specs, ordered revert specs, event/trace specs, and closed-world economic invariants comparable in scope to the v2-core Certora rules.

**Architecture:** Follow Tamago ERC4626 style: concrete helper formulas and ghost trace models live in `verity/common`, public obligations live in `verity/spec`, and proofs first establish actual `(entrypoint ...).run s` postconditions before connecting them to closed-world transitions. External effects are modeled by local trace events emitted only after successful ECM calls; no new axioms or trust surfaces are added for internal contract logic.

**Tech Stack:** Verity EDSL, Lean proofs, Tama CLI, Tamago FixedPointMathLib, Foundry mirror tests.

---

### Task 1: Event And External-Effect Trace Layer

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`

- [ ] **Step 1: Add local event helper constructors**

Add helper events for LP `Approval`, LP `Transfer`, `Mint`, `Burn`, `Swap`, and `Sync` in the common module. Keep them out of `verity/spec` so helper names are not public obligations.

- [ ] **Step 2: Add proved LP event obligations**

Add public specs and proofs for `approve`, `transfer`, and `transferFrom` event emission on successful paths, using the actual run result.

- [ ] **Step 3: Extend token-transfer trace obligations**

Add burn/swap/skim obligations that check the exact token address, pair source address, recipient, and amount for every successful `pairSafeTransfer` path.

- [ ] **Step 4: Verify**

Run: `lake build TamaUniV2.Proof.UniswapV2PairProof`

Expected: proofs compile without adding trust entries.

### Task 2: Executable Mint Success Coverage

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Modify: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Split first-mint postconditions**

Add small specs for actual first-mint success: return liquidity, locked minimum liquidity, recipient liquidity, total supply equals Tamago sqrt root, reserves equal observed balances, timestamp updates, `Sync`/`Mint`/`Transfer` events, and `unlocked == 1` after success.

- [ ] **Step 2: Consume Tamago sqrt facts**

Use Tamago FixedPointMathLib sqrt specs/proofs for square/root bounds. Do not duplicate the sqrt algorithm proof and do not add assumptions.

- [ ] **Step 3: Add subsequent-mint postconditions**

Add actual-run specs for pro-rata `min(amount0 * supply / reserve0, amount1 * supply / reserve1)`, total-supply increase, recipient-balance increase, reserve/TWAP update, events, and lock restoration.

- [ ] **Step 4: Bridge executable runs to `PairWorldMintStep`**

Replace the current success-conditional bridge with executable postcondition consumption: actual successful first/subsequent mint implies the corresponding closed-world mint transition.

### Task 3: Executable Burn Success Coverage

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Modify: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Add burn formula helpers**

Define concrete `burnAmount0`, `burnAmount1`, and post-transfer balance helpers in `verity/common`.

- [ ] **Step 2: Add burn success specs**

Specify actual-run burn return amounts, LP balance burn from `self`, total-supply decrease, token transfer traces, reserve/TWAP update, `Transfer`/`Sync`/`Burn` events, and lock restoration.

- [ ] **Step 3: Bridge burn to closed world**

Prove successful burn postconditions imply `PairWorldBurnStep`.

### Task 4: Executable Swap Success Coverage

**Files:**
- Modify: `verity/common/TamaUniV2/Common/UniswapV2PairConcrete.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`
- Modify: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Add swap arithmetic helpers**

Define adjusted-balance, fee-adjusted product, required-product, and amount-in helpers matching the source implementation.

- [ ] **Step 2: Add swap success specs**

Specify actual-run output transfers, optional flash callback trace boundary, amount-in derivation, adjusted-K inequality, reserve/TWAP update, `Sync`/`Swap` events, and lock restoration.

- [ ] **Step 3: Bridge swap to closed world**

Prove successful swap postconditions imply `PairWorldSwapStep` and the fee-adjusted K invariant.

### Task 5: Factory `createPair` Success Coverage

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2FactorySpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2FactoryProof.lean`
- Modify: `tama.toml`
- Modify: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Add sorting and deterministic-result specs**

Specify sorted token order, nonzero pair result, and the CREATE2 boundary as the only deployment assumption.

- [ ] **Step 2: Add storage update specs**

Specify bidirectional mappings, append at old length, length increment, pair initialize call boundary, and `PairCreated` event.

- [ ] **Step 3: Add ordered createPair reverts**

Add exact run-result specs for CREATE2 failure and pair-count overflow after proving earlier guards pass.

### Task 6: Reentrancy Guard Success And Revert Frames

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `tama.toml`

- [ ] **Step 1: Add success restoration specs**

For every successful guarded entrypoint (`mint`, `burn`, `swap`, `skim`, `sync`), prove `result.snd.storage unlockedSlot.slot = 1` from the actual run.

- [ ] **Step 2: Add revert-frame specs**

For guarded entrypoint reverts, prove the returned state is exactly the pre-state and no durable pair token transfer trace is appended.

### Task 7: Ordered Revert Matrix

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2PairProof.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2FactorySpec.lean`
- Modify: `verity/proof/TamaUniV2/Proof/UniswapV2FactoryProof.lean`
- Modify: `tama.toml`
- Modify: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Add ordered mint revert specs**

Cover locked, overflow, balance-below-reserve, zero amount, product overflow, insufficient liquidity minted, reserve missing for subsequent mint, supply overflow, and recipient balance overflow.

- [ ] **Step 2: Add ordered burn revert specs**

Cover locked, zero liquidity, product overflow, zero output, transfer failure boundary, and reserve overflow after transfers.

- [ ] **Step 3: Add ordered swap revert specs**

Cover locked, zero output, insufficient liquidity, invalid `to`, transfer/callback failure boundary, insufficient input, K overflow, K violation, and reserve overflow.

- [ ] **Step 4: Add ordered skim/sync/factory revert specs**

Cover skim balance-below-reserve priority, sync overflow priority, factory identical/zero/duplicate/create2/length-overflow priority.

### Task 8: Full Verification And Commit

**Files:**
- Modify: `docs/agent-progress.md`
- Modify: `docs/spec-coverage.md`
- Generated: `src/generated/verity/*` only if ABI/build output changes

- [ ] **Step 1: Update durable notes**

Record completed obligations, remaining gaps, and any proof tactics that failed so compaction does not repeat work.

- [ ] **Step 2: Run full verification**

Run:
- `lake build`
- `/Users/zefram/.tama/bin/tama check`
- `/Users/zefram/.tama/bin/tama build`
- `/Users/zefram/.tama/bin/tama test`
- `/Users/zefram/.tama/bin/tama audit`

- [ ] **Step 3: Commit**

Commit in coherent slices rather than one massive commit: event/trace layer, mint, burn, swap, factory, revert matrix, and docs.
