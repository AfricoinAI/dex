// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {TamaSwapFrontend} from "../../src/TamaSwapFrontend.sol";

contract TamaSwapFrontendTest is Test {
    TamaSwapFrontend internal frontend;
    address internal constant FACTORY = address(0x1111111111111111111111111111111111111111);
    address internal constant ROUTER = address(0x2222222222222222222222222222222222222222);
    uint256 internal constant EIP_170_CAP = 24576;

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
        _assertDataOk(frontend.HEAD(), "HEAD");
        _assertDataOk(frontend.MIDDLE(), "MIDDLE");
        _assertDataOk(frontend.TAIL(), "TAIL");

        bytes memory html = bytes(frontend.html());
        assertEq(string(_slice(html, 0, 15)), "<!doctype html>");
        assertTrue(_contains(html, bytes("TamaSwap")));
        assertTrue(_contains(html, bytes("0x38ed1739")));
    }

    function testRequestReturnsHtmlHeaders() public view {
        string[] memory resource = new string[](0);
        TamaSwapFrontend.KeyValue[] memory params = new TamaSwapFrontend.KeyValue[](0);
        (uint16 status, string memory body, TamaSwapFrontend.KeyValue[] memory headers) =
            frontend.request(resource, params);

        assertEq(status, 200);
        assertEq(keccak256(bytes(body)), keccak256(bytes(frontend.html())));
        assertEq(headers.length, 2);
        assertEq(headers[0].key, "Content-Type");
        assertEq(headers[0].value, "text/html; charset=utf-8");
        assertEq(headers[1].key, "Cache-Control");
        assertEq(headers[1].value, "public, max-age=31536000, immutable");
    }

    function testMetadata() public view {
        assertEq(frontend.NAME(), "TamaSwap");
        assertEq(frontend.VERSION(), "0.1");
        assertEq(frontend.factory(), FACTORY);
        assertEq(frontend.router(), ROUTER);
        assertEq(frontend.resolveMode(), bytes32("5219"));
    }

    function _assertDataOk(address d, string memory label) internal view {
        uint256 size = d.code.length;
        assertGt(size, 0, string.concat(label, " empty"));
        assertLe(size, EIP_170_CAP, string.concat(label, " exceeds EIP-170"));
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
