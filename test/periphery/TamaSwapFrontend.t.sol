// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {TamaSwapFrontend} from "../../src/TamaSwapFrontend.sol";

contract TamaSwapFrontendTest is Test {
    TamaSwapFrontend internal frontend;
    address internal constant FACTORY = address(0x1111111111111111111111111111111111111111);
    address internal constant ROUTER = address(0x2222222222222222222222222222222222222222);
    uint256 internal constant EIP_170_CAP = 24576;
    uint256 internal constant MIN_WRAPPER_MARGIN = 8000;

    function setUp() public {
        frontend = new TamaSwapFrontend(FACTORY, ROUTER);
    }

    function testHtmlInjectsFactoryAndRouter() public view {
        bytes memory html = bytes(frontend.html());

        assertTrue(_contains(html, bytes(_addr(FACTORY))), "factory missing");
        assertTrue(_contains(html, bytes(_addr(ROUTER))), "router missing");
        assertFalse(_contains(html, bytes("__FACTORY__")), "factory placeholder present");
        assertFalse(_contains(html, bytes("__ROUTER__")), "router placeholder present");
    }

    function testHtmlStructureAndDataChunks() public view {
        assertLe(address(frontend).code.length, EIP_170_CAP, "wrapper exceeds EIP-170");
        assertGe(EIP_170_CAP - address(frontend).code.length, MIN_WRAPPER_MARGIN, "wrapper margin too small");
        _assertDataOk(frontend.PAYLOAD(), "PAYLOAD");

        bytes memory html = bytes(frontend.html());
        assertEq(string(_slice(html, 0, 15)), "<!doctype html>");
        assertTrue(_contains(html, bytes("TamaSwap")));
        assertTrue(_contains(html, bytes("DecompressionStream(\"gzip\")")), "gzip stream missing");
        assertTrue(_contains(html, bytes("document.open().write(h)")), "document write missing");
        assertFalse(_contains(html, bytes("0x38ed1739")), "raw app should be compressed");
    }

    function testHtmlUsesCompressedBootstrapAndSinglePayloadChunk() public view {
        bytes memory html = bytes(frontend.html());

        assertTrue(_contains(html, bytes("DecompressionStream")), "gzip bootstrap missing");
        assertTrue(_contains(html, bytes("atob(")), "base64 decode missing");
        assertEq(
            keccak256(bytes(_data(frontend.PAYLOAD()))),
            keccak256(bytes(vm.toBase64(vm.readFileBinary("artifacts/tamaswap.min.html.gz"))))
        );

        (bool headOk,) = address(frontend).staticcall(abi.encodeWithSignature("HEAD()"));
        assertFalse(headOk, "unexpected HEAD chunk");
        (bool tailOk,) = address(frontend).staticcall(abi.encodeWithSignature("TAIL()"));
        assertFalse(tailOk, "unexpected TAIL chunk");
        (bool middleOk,) = address(frontend).staticcall(abi.encodeWithSignature("MIDDLE()"));
        assertFalse(middleOk, "unexpected MIDDLE chunk");
        (bool ok,) = address(frontend).staticcall(abi.encodeWithSignature("TAIL2()"));
        assertFalse(ok, "unexpected TAIL2 chunk");
    }

    function testHtmlMatchesGeneratedCompressedBootstrap() public view {
        bytes memory compressed = vm.readFileBinary("artifacts/tamaswap.min.html.gz");
        string memory expected = _expectedBootstrap(vm.toBase64(compressed));

        assertEq(keccak256(bytes(frontend.html())), keccak256(bytes(expected)));
    }

    function testRequestReturnsHtmlHeaders() public view {
        string[] memory resource = new string[](0);
        TamaSwapFrontend.KeyValue[] memory params = new TamaSwapFrontend.KeyValue[](0);
        (uint16 status, string memory body, TamaSwapFrontend.KeyValue[] memory headers) =
            frontend.request(resource, params);

        assertEq(status, 200);
        assertEq(keccak256(bytes(body)), keccak256(bytes(frontend.html())));
        assertEq(headers.length, 3);
        assertEq(headers[0].key, "Content-Type");
        assertEq(headers[0].value, "text/html; charset=utf-8");
        assertEq(headers[1].key, "Cache-Control");
        assertEq(headers[1].value, "public, max-age=31536000, immutable");
        assertEq(headers[2].key, "Content-Security-Policy");
        assertTrue(_contains(bytes(headers[2].value), bytes("default-src 'none'")));
        assertTrue(
            _contains(bytes(headers[2].value), bytes("connect-src https: http://localhost:* http://127.0.0.1:*"))
        );
    }

    function testRequestReturns404ForUnrelatedResource() public view {
        string[] memory resource = new string[](1);
        resource[0] = "robots.txt";
        TamaSwapFrontend.KeyValue[] memory params = new TamaSwapFrontend.KeyValue[](0);
        (uint16 status, string memory body, TamaSwapFrontend.KeyValue[] memory headers) =
            frontend.request(resource, params);

        assertEq(status, 404);
        assertEq(body, "Not found");
        assertEq(headers.length, 1);
        assertEq(headers[0].key, "Content-Type");
        assertEq(headers[0].value, "text/plain; charset=utf-8");
    }

    function testMetadata() public view {
        assertEq(frontend.NAME(), "TamaSwap");
        assertEq(frontend.VERSION(), "0.1");
        assertEq(frontend.factory(), FACTORY);
        assertEq(frontend.router(), ROUTER);
        assertEq(frontend.resolveMode(), bytes32("5219"));
    }

    function _expectedBootstrap(string memory encoded) internal pure returns (string memory) {
        return string.concat(
            "<!doctype html><script>(async()=>{const F=\"",
            _addr(FACTORY),
            "\",R=\"",
            _addr(ROUTER),
            "\",B=\"",
            encoded,
            "\";try{let u=Uint8Array.from(atob(B),c=>c.charCodeAt()),h=await new Response(new Blob([u]).stream().pipeThrough(new DecompressionStream(\"gzip\"))).text();h=h.replace(\"__\"+\"FACTORY__\",F).replace(\"__\"+\"ROUTER__\",R);document.open().write(h);document.close()}catch{document.body.textContent=\"TamaSwap load failed\"}})()</script>"
        );
    }

    function _assertDataOk(address d, string memory label) internal view {
        uint256 size = d.code.length;
        assertGt(size, 0, string.concat(label, " empty"));
        assertLe(size, EIP_170_CAP, string.concat(label, " exceeds EIP-170"));
    }

    function _data(address target) internal view returns (string memory s) {
        assembly ("memory-safe") {
            let size := extcodesize(target)
            s := mload(0x40)
            mstore(s, size)
            let ptr := add(s, 0x20)
            extcodecopy(target, ptr, 0, size)
            let padded := and(add(size, 0x1f), not(0x1f))
            mstore(0x40, add(add(s, 0x20), padded))
        }
    }

    function _slice(bytes memory src, uint256 a, uint256 z) internal pure returns (bytes memory out) {
        out = new bytes(z - a);
        for (uint256 i = 0; i < z - a; i++) {
            out[i] = src[a + i];
        }
    }

    function _contains(bytes memory hay, bytes memory needle) internal pure returns (bool) {
        if (needle.length == 0) return true;
        if (needle.length > hay.length) return false;
        for (uint256 i = 0; i + needle.length <= hay.length; i++) {
            bool ok = true;
            for (uint256 j = 0; j < needle.length; j++) {
                if (hay[i + j] != needle[j]) {
                    ok = false;
                    break;
                }
            }
            if (ok) return true;
        }
        return false;
    }

    function _addr(address a) internal pure returns (string memory) {
        bytes20 value = bytes20(a);
        bytes16 symbols = "0123456789abcdef";
        bytes memory out = new bytes(42);
        out[0] = "0";
        out[1] = "x";
        for (uint256 i = 0; i < 20; i++) {
            out[2 + i * 2] = symbols[uint8(value[i] >> 4)];
            out[3 + i * 2] = symbols[uint8(value[i] & 0x0f)];
        }
        return string(out);
    }
}
