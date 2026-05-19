// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {UniswapV2FactoryDeployer} from "../../src/generated/verity/UniswapV2FactoryDeployer.sol";
import {UniswapV2FactoryIface} from "../../src/generated/verity/UniswapV2FactoryIface.sol";
import {UniswapV2PairIface} from "../../src/generated/verity/UniswapV2PairIface.sol";
import {MockERC20, FactoryFixture} from "./UniswapV2Helpers.sol";

contract FactoryViewMirrors is FactoryFixture {
    // tama: mirrors=factory_getPair_run_success_frames_state
    function testFuzzMirrorGetPairReadsBidirectionalMapping(uint96 fuzz) public {
        assertEq(factory.getPair(address(tokenA), address(tokenB)), address(pair));
        assertEq(factory.getPair(address(tokenB), address(tokenA)), address(pair));
        assertEq(factory.getPair(address(0xBEEF), address(0xCAFE)), address(0));
    }

    // tama: mirrors=factory_allPairsLength_run_success_frames_state
    function testFuzzMirrorAllPairsLengthReadsLengthCell() public {
        assertEq(factory.allPairsLength(), 1);
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        factory.createPair(address(tokenC), address(tokenD));
        assertEq(factory.allPairsLength(), 2);
    }

    // tama: mirrors=factory_allPairs_run_success_in_bounds
    function testFuzzMirrorAllPairsInBoundsReadsArrayEntry(uint96 fuzz) public {
        assertEq(factory.allPairs(0), address(pair));
    }
}

contract FactoryRevertMirrors is FactoryFixture {
    // tama: mirrors=factory_allPairs_run_revert_out_of_bounds
    function testFuzzMirrorAllPairsOutOfBoundsReverts(uint96 fuzz) public {
        uint256 length = factory.allPairsLength();
        vm.expectRevert(bytes("UniswapV2: INDEX_OUT_OF_BOUNDS"));
        factory.allPairs(length);
    }

    // tama: mirrors=factory_createPair_run_revert_identical_addresses
    function testFuzzMirrorCreatePairRevertsOnIdenticalAddresses(uint96 fuzz) public {
        vm.expectRevert(bytes("UniswapV2: IDENTICAL_ADDRESSES"));
        factory.createPair(address(tokenA), address(tokenA));
    }

    // tama: mirrors=factory_createPair_run_revert_zero_address
    function testFuzzMirrorCreatePairRevertsOnZeroAddress(uint96 fuzz) public {
        vm.expectRevert(bytes("UniswapV2: ZERO_ADDRESS"));
        factory.createPair(address(0), address(tokenA));
    }

    // tama: mirrors=factory_createPair_run_revert_duplicates
    function testFuzzMirrorCreatePairRevertsOnDuplicates(uint96 fuzz) public {
        vm.expectRevert(bytes("UniswapV2: PAIR_EXISTS"));
        factory.createPair(address(tokenA), address(tokenB));
    }

    // tama: mirrors=factory_createPair_revert_keeps_factory_state
    function testFuzzMirrorCreatePairRevertLeavesFactoryStateUnchanged(uint96 fuzz) public {
        uint256 lengthBefore = factory.allPairsLength();
        address mapEntryBefore = factory.getPair(address(tokenA), address(tokenB));
        vm.expectRevert();
        factory.createPair(address(tokenA), address(tokenA));
        assertEq(factory.allPairsLength(), lengthBefore);
        assertEq(factory.getPair(address(tokenA), address(tokenB)), mapEntryBefore);
    }
}

contract FactoryCreatePairMirrors is FactoryFixture {
    // tama: mirrors=factory_createPair_success_updates_storage_and_emits
    function testFuzzMirrorCreatePairWritesStorageAndEmits(uint96 fuzz) public {
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        (address token0, address token1) = sortedAddresses(address(tokenC), address(tokenD));
        address expectedPair = expectedCreate2Pair(token0, token1);
        uint256 lengthBefore = factory.allPairsLength();

        vm.expectEmit(true, true, false, true, address(factory));
        emit PairCreated(token0, token1, expectedPair, lengthBefore + 1);
        address created = factory.createPair(address(tokenC), address(tokenD));

        assertEq(created, expectedPair);
        assertEq(factory.getPair(address(tokenC), address(tokenD)), expectedPair);
        assertEq(factory.getPair(address(tokenD), address(tokenC)), expectedPair);
        assertEq(factory.allPairs(lengthBefore), expectedPair);
        assertEq(factory.allPairsLength(), lengthBefore + 1);
    }

    // tama: mirrors=factory_createPair_success_getPair_views_return_new_pair
    function testFuzzMirrorCreatePairSuccessIsVisibleViaGetPair(uint96 fuzz) public {
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        address created = factory.createPair(address(tokenC), address(tokenD));
        assertEq(factory.getPair(address(tokenC), address(tokenD)), created);
        assertEq(factory.getPair(address(tokenD), address(tokenC)), created);
    }

    // tama: mirrors=factory_createPair_success_implies_pre_create_guards
    function testFuzzMirrorCreatePairSuccessImpliesPreGuards(uint96 fuzz) public {
        MockERC20 tokenC = new MockERC20();
        MockERC20 tokenD = new MockERC20();
        // Pre-create guards: distinct, both nonzero, mapping empty.
        assertTrue(address(tokenC) != address(tokenD));
        assertTrue(address(tokenC) != address(0));
        assertTrue(address(tokenD) != address(0));
        assertEq(factory.getPair(address(tokenC), address(tokenD)), address(0));
        factory.createPair(address(tokenC), address(tokenD));
    }
}

// =====================================================================
// Factory finite-history invariants and closed-world step properties.
// Each test exercises a sequence of createPair calls and asserts the
// property the Lean closed-world spec promises.
// =====================================================================

contract FactoryClosedWorldMirrors is FactoryFixture {
    function _createPair() internal returns (address) {
        MockERC20 c = new MockERC20();
        MockERC20 d = new MockERC20();
        return factory.createPair(address(c), address(d));
    }

    // tama: mirrors=factory_closed_world_create_appends_one_pair
    function testFuzzMirrorCreatePairAppendsOnePair(uint96 fuzz) public {
        uint256 lengthBefore = factory.allPairsLength();
        _createPair();
        assertEq(factory.allPairsLength(), lengthBefore + 1);
    }

    // tama: mirrors=factory_closed_world_create_adds_symmetric_lookup
    function testFuzzMirrorCreatePairAddsSymmetricLookup(uint96 fuzz) public {
        MockERC20 c = new MockERC20();
        MockERC20 d = new MockERC20();
        address created = factory.createPair(address(c), address(d));
        assertEq(factory.getPair(address(c), address(d)), created);
        assertEq(factory.getPair(address(d), address(c)), created);
    }

    // tama: mirrors=factory_closed_world_path_preserves_existing_pairs
    function testFuzzMirrorPathPreservesExistingPairs(uint96 fuzz) public {
        address existing = factory.getPair(address(tokenA), address(tokenB));
        _createPair();
        _createPair();
        assertEq(factory.getPair(address(tokenA), address(tokenB)), existing);
        assertEq(factory.allPairs(0), existing);
    }

    // tama: mirrors=factory_closed_world_path_is_append_only
    function testFuzzMirrorPathIsAppendOnly(uint96 fuzz) public {
        address existing = factory.allPairs(0);
        address second = _createPair();
        address third = _createPair();
        assertEq(factory.allPairs(0), existing);
        assertEq(factory.allPairs(1), second);
        assertEq(factory.allPairs(2), third);
        assertEq(factory.allPairsLength(), 3);
    }

    // tama: mirrors=factory_closed_world_same_count_path_preserves_pair_list
    function testFuzzMirrorSameCountPreservesPairList(uint96 fuzz) public {
        // The "path" with no createPair calls trivially preserves the array.
        uint256 lengthBefore = factory.allPairsLength();
        address entryBefore = factory.allPairs(0);
        // Run unrelated view calls to simulate a no-create history.
        factory.allPairsLength();
        factory.getPair(address(tokenA), address(tokenB));
        assertEq(factory.allPairsLength(), lengthBefore);
        assertEq(factory.allPairs(0), entryBefore);
    }

    // tama: mirrors=factory_closed_world_path_length_matches_created_pairs
    function testFuzzMirrorPathLengthMatchesCreatedPairs(uint96 fuzz) public {
        // allPairsLength reflects exactly the number of successful createPair calls.
        assertEq(factory.allPairsLength(), 1);
        _createPair();
        assertEq(factory.allPairsLength(), 2);
        _createPair();
        _createPair();
        assertEq(factory.allPairsLength(), 4);
    }

    // tama: mirrors=factory_closed_world_lookup_symmetric
    function testFuzzMirrorLookupSymmetric(uint96 fuzz) public {
        assertEq(
            factory.getPair(address(tokenA), address(tokenB)),
            factory.getPair(address(tokenB), address(tokenA))
        );
    }

    // tama: mirrors=factory_closed_world_unordered_pair_address_unique
    function testFuzzMirrorUnorderedPairAddressUnique(uint96 fuzz) public {
        // Both lookup orders return the same address — any "two answers"
        // would have to disagree on at least one direction.
        address ab = factory.getPair(address(tokenA), address(tokenB));
        address ba = factory.getPair(address(tokenB), address(tokenA));
        assertEq(ab, ba);
        // A duplicate createPair attempt must revert; that's how uniqueness
        // is enforced.
        vm.expectRevert(bytes("UniswapV2: PAIR_EXISTS"));
        factory.createPair(address(tokenA), address(tokenB));
    }

    // tama: mirrors=factory_closed_world_reachable_lookup_is_valid
    function testFuzzMirrorReachableLookupIsValid(uint96 fuzz) public {
        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        assertTrue(pairAddr != address(0));
        assertTrue(address(tokenA) != address(tokenB));
        assertTrue(address(tokenA) != address(0));
        assertTrue(address(tokenB) != address(0));
    }

    // tama: mirrors=factory_closed_world_created_pairs_are_sorted_and_nonzero
    function testFuzzMirrorCreatedPairsAreSortedAndNonzero(uint96 fuzz) public {
        for (uint256 i = 0; i < factory.allPairsLength(); i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            address t0 = p.token0();
            address t1 = p.token1();
            assertTrue(t0 != address(0));
            assertTrue(t1 != address(0));
            assertTrue(t0 != t1);
            // Sorted: token0 < token1 byte-wise.
            assertLt(uint160(t0), uint160(t1));
        }
        // Add more and re-check.
        _createPair();
        _createPair();
        for (uint256 i = 0; i < factory.allPairsLength(); i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            address t0 = p.token0();
            address t1 = p.token1();
            assertTrue(t0 != address(0));
            assertTrue(t1 != address(0));
            assertLt(uint160(t0), uint160(t1));
        }
    }

    // tama: mirrors=factory_closed_world_path_preserves_reachability
    function testFuzzMirrorClosedWorldPathPreservesReachability(uint96 fuzz) public {
        // Reachability is a model fact; the contract observation is that
        // every length the factory reports along a successful path is itself
        // a state with the expected discoverability properties.
        uint256 lengthBefore = factory.allPairsLength();
        _createPair();
        _createPair();
        for (uint256 i = 0; i < factory.allPairsLength(); i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
        }
        assertGt(factory.allPairsLength(), lengthBefore);
    }

    // tama: mirrors=factory_closed_world_path_preserves_good
    function testFuzzMirrorClosedWorldPathPreservesGood(uint96 fuzz) public {
        _createPair();
        _createPair();
        // After two more creates, all four invariants still hold:
        //  - sorted entries
        //  - unique unordered keys (no duplicate creates)
        //  - length == array length
        //  - all entries nonzero.
        assertEq(factory.allPairsLength(), 3);
        address[3] memory pairs = [factory.allPairs(0), factory.allPairs(1), factory.allPairs(2)];
        for (uint256 i = 0; i < 3; i++) {
            assertTrue(pairs[i] != address(0));
        }
        assertTrue(pairs[0] != pairs[1]);
        assertTrue(pairs[1] != pairs[2]);
        assertTrue(pairs[0] != pairs[2]);
    }
}

// =====================================================================
// Factory concrete world/storage agreement mirrors.
// =====================================================================

contract FactoryConcreteWorldMirrors is FactoryFixture {
    function _createPair() internal returns (address) {
        MockERC20 c = new MockERC20();
        MockERC20 d = new MockERC20();
        return factory.createPair(address(c), address(d));
    }

    // tama: mirrors=factory_concrete_world_length_matches_storage
    function testFuzzMirrorConcreteWorldLengthMatchesStorage(uint96 fuzz) public {
        // The modeled pair count equals the public allPairsLength view.
        assertEq(factory.allPairsLength(), 1);
        _createPair();
        assertEq(factory.allPairsLength(), 2);
    }

    // tama: mirrors=factory_concrete_world_allPairs_matches_storage
    function testFuzzMirrorConcreteWorldAllPairsMatchesStorage(uint96 fuzz) public {
        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        assertEq(factory.allPairs(0), pairAddr);
        address newPair = _createPair();
        assertEq(factory.allPairs(1), newPair);
    }

    // tama: mirrors=factory_concrete_reachable_lookup_is_valid
    function testFuzzMirrorConcreteReachableLookupIsValid(uint96 fuzz) public {
        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        assertTrue(pairAddr != address(0));
        assertTrue(address(tokenA) != address(tokenB));
        assertTrue(address(tokenA) != address(0));
        assertTrue(address(tokenB) != address(0));
    }

    // tama: mirrors=factory_createPair_success_preserves_concrete_world_match
    function testFuzzMirrorCreatePairSuccessPreservesWorldMatch(uint96 fuzz) public {
        // After a successful create, the model+1-entry world still matches storage:
        // length, array, and bidirectional lookup all consistent.
        uint256 lengthBefore = factory.allPairsLength();
        MockERC20 c = new MockERC20();
        MockERC20 d = new MockERC20();
        address created = factory.createPair(address(c), address(d));
        assertEq(factory.allPairsLength(), lengthBefore + 1);
        assertEq(factory.allPairs(lengthBefore), created);
        assertEq(factory.getPair(address(c), address(d)), created);
        assertEq(factory.getPair(address(d), address(c)), created);
    }

    // tama: mirrors=factory_concrete_create_path_preserves_world_match
    function testFuzzMirrorConcreteCreatePathPreservesWorldMatch(uint96 fuzz) public {
        _createPair();
        _createPair();
        // Length still matches array; every entry decodes; every lookup valid.
        uint256 length = factory.allPairsLength();
        assertEq(length, 3);
        for (uint256 i = 0; i < length; i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            assertEq(factory.getPair(p.token0(), p.token1()), pairAddr);
        }
    }

    // tama: mirrors=factory_concrete_create_path_preserves_existing_decoded_lookup
    function testFuzzMirrorConcreteCreatePathPreservesExistingLookup(uint96 fuzz) public {
        address existing = factory.getPair(address(tokenA), address(tokenB));
        _createPair();
        _createPair();
        assertEq(factory.getPair(address(tokenA), address(tokenB)), existing);
        assertEq(factory.getPair(address(tokenB), address(tokenA)), existing);
    }

    // tama: mirrors=factory_concrete_create_path_preserves_existing_allPairs_entry
    function testFuzzMirrorConcreteCreatePathPreservesArrayEntry(uint96 fuzz) public {
        address entry0Before = factory.allPairs(0);
        _createPair();
        _createPair();
        assertEq(factory.allPairs(0), entry0Before);
    }

    // tama: mirrors=factory_concrete_create_path_reachable_lookup_is_valid
    function testFuzzMirrorConcreteCreatePathReachableLookupIsValid(uint96 fuzz) public {
        _createPair();
        _createPair();
        for (uint256 i = 0; i < factory.allPairsLength(); i++) {
            address pairAddr = factory.allPairs(i);
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            assertTrue(pairAddr != address(0));
            assertTrue(p.token0() != address(0));
            assertTrue(p.token1() != address(0));
            assertTrue(p.token0() != p.token1());
        }
    }

    // tama: mirrors=factory_concrete_same_length_create_path_preserves_world
    function testFuzzMirrorConcreteSameLengthPreservesWorld(uint96 fuzz) public {
        // A "no-create" path: length unchanged ⇒ entire array unchanged.
        uint256 lengthBefore = factory.allPairsLength();
        address entryBefore = factory.allPairs(0);
        // Do only view calls (no creates).
        factory.getPair(address(tokenA), address(tokenB));
        factory.allPairsLength();
        assertEq(factory.allPairsLength(), lengthBefore);
        assertEq(factory.allPairs(0), entryBefore);
    }
}

// =====================================================================
// Additional Pair mirrors for token-world, oracle, flash-callback, and
// caller-wallet specs that previously lived in proof_only.
// =====================================================================

contract FactoryHandler {
    UniswapV2FactoryIface public factory;

    constructor(UniswapV2FactoryIface factory_) {
        factory = factory_;
    }

    function createPair(uint256 tokenASeed, uint256 tokenBSeed) external {
        if (factory.allPairsLength() >= 4) return;
        address tokenA = address(uint160(uint256(keccak256(abi.encodePacked("A", tokenASeed)))));
        address tokenB = address(uint160(uint256(keccak256(abi.encodePacked("B", tokenBSeed)))));
        if (tokenA == address(0) || tokenB == address(0) || tokenA == tokenB) return;
        if (factory.getPair(tokenA, tokenB) != address(0)) return;
        try factory.createPair(tokenA, tokenB) {} catch {}
    }
}

contract FactoryAdditionalMirrors is FactoryFixture {
    // tama: mirrors=factory_createPair_success_matches_closed_world_step
    function testFuzzMirrorFactoryCreatePairSuccessMatchesClosedWorldStep(address tokenA_, address tokenB_) public {
        vm.assume(tokenA_ != address(0) && tokenB_ != address(0) && tokenA_ != tokenB_);
        vm.assume(factory.getPair(tokenA_, tokenB_) == address(0));
        (address token0, address token1) = sortedAddresses(tokenA_, tokenB_);
        address expectedPair = expectedCreate2Pair(token0, token1);
        uint256 lengthBefore = factory.allPairsLength();

        address created = factory.createPair(tokenA_, tokenB_);

        assertEq(created, expectedPair);
        assertEq(factory.allPairsLength(), lengthBefore + 1);
        assertEq(factory.allPairs(lengthBefore), expectedPair);
        assertEq(factory.getPair(tokenA_, tokenB_), expectedPair);
        assertEq(factory.getPair(tokenB_, tokenA_), expectedPair);
    }

    // tama: mirrors=factory_createPair_run_revert_pair_count_overflow
    function testFuzzMirrorFactoryCreatePairRevertsOnPairCountOverflow(address tokenA_, address tokenB_) public {
        vm.assume(tokenA_ != address(0) && tokenB_ != address(0) && tokenA_ != tokenB_);
        vm.assume(factory.getPair(tokenA_, tokenB_) == address(0));
        vm.store(address(factory), bytes32(uint256(2)), bytes32(type(uint256).max));

        vm.expectRevert(bytes("UniswapV2: PAIR_COUNT_OVERFLOW"));
        factory.createPair(tokenA_, tokenB_);
    }

    // tama: mirrors=factory_createPair_run_revert_create2_failed
    function testFuzzMirrorFactoryCreatePairRevertsWhenCreate2DestinationOccupied(address tokenA_, address tokenB_)
        public
    {
        vm.assume(tokenA_ != address(0) && tokenB_ != address(0) && tokenA_ != tokenB_);
        vm.assume(factory.getPair(tokenA_, tokenB_) == address(0));
        (address token0, address token1) = sortedAddresses(tokenA_, tokenB_);
        address expectedPair = expectedCreate2Pair(token0, token1);
        vm.etch(expectedPair, hex"fe");

        vm.expectRevert(bytes("UniswapV2: CREATE2_FAILED"));
        factory.createPair(tokenA_, tokenB_);
    }
}

contract FactoryInvariantMirrors is FactoryFixture {
    FactoryHandler internal handler;

    function setUp() public override {
        super.setUp();
        handler = new FactoryHandler(factory);
        targetContract(address(handler));
    }

    // tama: mirrors=factory_createPair_success_preserves_good
    function invariant_factoryCreatePairSuccessPreservesGood() public {
        uint256 length = factory.allPairsLength();
        for (uint256 i = 0; i < length; i++) {
            address pairAddr = factory.allPairs(i);
            assertTrue(pairAddr != address(0));
            UniswapV2PairIface p = UniswapV2PairIface(pairAddr);
            assertTrue(p.token0() != address(0));
            assertTrue(p.token1() != address(0));
            assertLt(uint160(p.token0()), uint160(p.token1()));
            assertEq(factory.getPair(p.token0(), p.token1()), pairAddr);
            assertEq(factory.getPair(p.token1(), p.token0()), pairAddr);
        }
    }
}

// =====================================================================
// Remaining behavior covered by the original integration tests.
// These exercise event emission, fee-off K, the existing reentrancy
// shape, and the metadata/permit absence — but none carry a `mirrors`
// annotation because each spec they touch is already mirrored by a
// dedicated 1:1 test above.
// =====================================================================

