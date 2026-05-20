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
        assertTrue(_contains(html, bytes("0x8803dbee")), "exact output swap missing");
        assertTrue(_contains(html, bytes("0x1f00ca74")), "exact output quote missing");
        assertTrue(_contains(html, bytes("0xad5c4648")), "WETH lookup missing");
        assertTrue(_contains(html, bytes("0x7ff36ab5")), "exact ETH input swap missing");
        assertTrue(_contains(html, bytes("0x4a25d94a")), "exact ETH output swap missing");
        assertTrue(_contains(html, bytes("0x406ee863")), "wrap ETH missing");
        assertTrue(_contains(html, bytes("0x2e59d848")), "unwrap ETH missing");
        assertTrue(_contains(html, bytes("Maximum sold")), "exact output slippage label missing");
        assertTrue(_contains(html, bytes("Select token")), "token selector missing");
        assertTrue(_contains(html, bytes("tokens.uniswap.org")), "default token list missing");
        assertTrue(_contains(html, bytes("coins.llama.fi")), "DeFiLlama pricing missing");
        assertTrue(_contains(html, bytes("Price unavailable")), "price fallback missing");
        assertTrue(_contains(html, bytes("Connect wallet")), "wallet picker missing");
        assertTrue(_contains(html, bytes("eip6963:requestProvider")), "wallet discovery missing");
        assertTrue(_contains(html, bytes("id=swapReview class=\"review hide\"")), "swap review should start hidden");
        assertTrue(_contains(html, bytes("id=lpReview class=\"review hide\"")), "lp review should start hidden");
        assertTrue(_contains(html, bytes("id=burnReview class=\"review hide\"")), "burn review should start hidden");
        assertTrue(_contains(html, bytes("CHAIN")), "chain metadata missing");
        assertTrue(_contains(html, bytes("mega.etherscan.io")), "MegaETH explorer missing");
        assertTrue(_contains(html, bytes("monadvision.com")), "Monad explorer missing");
        assertFalse(_contains(html, bytes("swell")), "dead Swellchain metadata present");
        assertTrue(_contains(html, bytes("burnOut")), "remove quote missing");
        assertTrue(_contains(html, bytes("poolSettings")), "pool settings missing");
        assertTrue(_contains(html, bytes("fmtFull")), "balance fill helper missing");
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
