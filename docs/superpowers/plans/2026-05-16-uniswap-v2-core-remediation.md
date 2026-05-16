# Uniswap V2 Core Remediation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bring the Verity Uniswap V2 core implementation closer to official fee-off v2-core behavior, with stronger tests/spec coverage and no local sqrt implementation.

**Architecture:** Keep the current Verity Pair/Factory architecture and generated Solidity interface flow. Refactor contracts to Tamago-style `Base` contract plus wrapper `spec` so native `emit` statements are backed by event definitions, and use the installed Tamago package for `FixedPointMathLib.sqrt`.

**Tech Stack:** Verity EDSL, Tama CLI, Tamago, Lean specs, Foundry mirror tests.

---

### Task 1: Add Failing Parity Tests

**Files:**
- Modify: `test/verity/UniswapV2Core.t.sol`

- [x] **Step 1: Add tests that expose the reviewed gaps**

Add:
- Large first mint test expecting `sqrt(amount0 * amount1)` to mint the exact fee-off supply.
- `allPairs` out-of-bounds revert test.
- event tests for `PairCreated`, LP `Approval`, LP `Transfer`, `Mint`, `Burn`, `Swap`, and `Sync`.
- deterministic CREATE2 address test using `keccak256(abi.encodePacked(token0, token1))`.

- [x] **Step 2: Run the test file and verify failures**

Run: `/Users/zefram/.tama/bin/tama test`

Expected: failures before implementation because current Pair exposes/fails the local bounded sqrt for large values, Factory returns zero for out-of-bounds `allPairs`, emits no events, and uses a 64-byte salt.

### Task 2: Use Installed Tamago Sqrt

**Files:**
- Modify: `verity/src/TamaUniV2/UniswapV2Pair.lean`

- [x] **Step 1: Import Tamago sqrt**

Add `import Tamago.Utils.FixedPointMathLib` and replace the local public `sqrt` function with `Tamago.Utils.FixedPointMathLib.sqrt` inside first mint.

- [x] **Step 2: Remove the public `sqrt(uint256)` ABI**

Delete the Pair `function view sqrt` so the generated ABI no longer includes a public helper that is not in Uniswap V2 core.

- [x] **Step 3: Verify the large mint test passes after build**

Run: `/Users/zefram/.tama/bin/tama build` then `/Users/zefram/.tama/bin/tama test`.

### Task 3: Native Event Emission

**Files:**
- Modify: `verity/src/TamaUniV2/UniswapV2Pair.lean`
- Modify: `verity/src/TamaUniV2/UniswapV2Factory.lean`

- [x] **Step 1: Refactor to Tamago wrapper shape**

Rename `UniswapV2Pair` to `UniswapV2PairBase` and `UniswapV2Factory` to `UniswapV2FactoryBase`. Add `namespace UniswapV2Pair` and `namespace UniswapV2Factory` wrappers with abbrevs for storage/constants/functions and `def spec := { Base.spec with name := "...", events := [...] }`.

- [x] **Step 2: Add native event definitions**

Reuse `Tamago.Common.Events.transfer` and `.approval`. Add local EventDefs for `Mint`, `Burn`, `Swap`, `Sync`, and `PairCreated`. Use native `emit "..." [...]` inside the implementation. Note that native Verity events currently support `uint256` rather than `uint112`, so `Sync` is emitted as `Sync(uint256,uint256)` at the ABI-signature layer.

- [x] **Step 3: Add emits at state transition points**

Emit:
- `Approval` in `approve`.
- `Transfer` in `transfer`, `transferFrom`, first-mint lock mint, user LP mint, and burn.
- `Mint` after reserve update in `mint`.
- `Burn` after reserve update in `burn`.
- `Swap` after reserve update in `swap`.
- `Sync` in every reserve update path.
- `PairCreated` after the factory records a new pair.

### Task 4: Factory Parity Fixes

**Files:**
- Modify: `verity/src/TamaUniV2/UniswapV2Factory.lean`

- [x] **Step 1: Enforce `allPairs` bounds**

In `allPairs(index)`, read `allPairsLengthSlot` and require `index < length`.

- [x] **Step 2: Use packed CREATE2 salt**

In `pairCreate2Module`, compute salt from 40 bytes using `mstore(0, shl(96, token0))`, `mstore(20, shl(96, token1))`, and `keccak256(0, 40)`.

### Task 5: Strengthen Specs And Mirror Links

**Files:**
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2PairSpec.lean`
- Modify: `verity/spec/TamaUniV2/Spec/UniswapV2FactorySpec.lean`
- Modify: `test/verity/UniswapV2Core.t.sol`

- [ ] **Step 1: Add behavior-level spec predicates**

Add named predicates for LP approve/transfer, first mint minimum-liquidity lock, burn pro-rata output, swap adjusted-K, sync reserve update, skim excess transfer, factory duplicate prevention, bounds, reverse mapping, and deterministic create2 salt.

- [ ] **Step 2: Link mirror tests**

Add `// tama: mirrors=...` comments to the Foundry tests so Tama audit sees behavioral coverage in addition to the small proved storage getter specs.

Outcome: not completed in this remediation pass. Tama treats spec predicates in
`verity/spec` as coverage obligations that need real Lean dischargers or mirror
metadata, so the attempted behavior predicates/mirror tags were not left in the
tree. The behavior-level coverage is currently in Foundry tests, while the Lean
spec/proof layer remains limited to discharged ABI/storage view properties.

### Task 6: Rebuild, Audit, And Review

**Files:**
- Generated files under `src/generated/verity/`

- [x] **Step 1: Run checks**

Run:
- `/Users/zefram/.tama/bin/tama check`
- `/Users/zefram/.tama/bin/tama build`
- `/Users/zefram/.tama/bin/tama test`
- `/Users/zefram/.tama/bin/tama audit`

- [x] **Step 2: Inspect ABI/artifacts**

Confirm generated Pair ABI has no `sqrt`, Pair/Factory events are present, and no `UniswapV2Math` artifact remains.

- [x] **Step 3: Final review**

Review for remaining parity gaps. Explicitly call out any Verity limitation that prevents exact official ABI parity, especially `Sync(uint112,uint112)`.
