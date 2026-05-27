// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {TamaSwapFrontend} from "../../src/TamaSwapFrontend.sol";

contract TamaSwapFrontendTest is Test {
    TamaSwapFrontend internal frontend;
    bytes20 internal constant GLOBAL_FACTORY = hex"00000021543ed46b665a74484c82b71e4eb61e34";
    bytes20 internal constant GLOBAL_ROUTER = hex"000000bb6b44dcd2c5d05911e830c176aa680579";
    bytes32 internal constant ERC_5219_MODE = 0x3532313900000000000000000000000000000000000000000000000000000000;
    uint256 internal constant EIP_170_CAP = 24576;
    uint256 internal constant EIP_3860_INITCODE_CAP = 49152;
    uint256 internal constant MIN_WRAPPER_MARGIN = 1024;
    uint256 internal constant MIN_INITCODE_MARGIN = 700;

    function setUp() public {
        frontend = new TamaSwapFrontend();
    }

    function testGeneratedAppInjectsGlobalAddressesAndResourcePaths() public view {
        bytes memory app = bytes(vm.readFile("artifacts/tamaswap.min.html"));

        assertTrue(_contains(app, bytes("0x00000021543ed46b665a74484c82b71e4eb61e34")), "factory missing");
        assertTrue(_contains(app, bytes("0x000000bb6b44dcd2c5d05911e830c176aa680579")), "router missing");
        assertEq(GLOBAL_FACTORY[0], bytes1(0), "factory vanity byte 0");
        assertEq(GLOBAL_FACTORY[1], bytes1(0), "factory vanity byte 1");
        assertEq(GLOBAL_FACTORY[2], bytes1(0), "factory vanity byte 2");
        assertEq(GLOBAL_ROUTER[0], bytes1(0), "router vanity byte 0");
        assertEq(GLOBAL_ROUTER[1], bytes1(0), "router vanity byte 1");
        assertEq(GLOBAL_ROUTER[2], bytes1(0), "router vanity byte 2");
        assertTrue(_contains(app, bytes("/deployment-code")), "deployment resource missing");
        assertFalse(_contains(app, bytes("__FACTORY__")), "factory placeholder present");
        assertFalse(_contains(app, bytes("__ROUTER__")), "router placeholder present");
        assertFalse(_contains(app, bytes("__LOCAL_WETH__")), "local weth placeholder present");
    }

    function testGeneratedAppIncludesFooterLinks() public view {
        bytes memory app = bytes(vm.readFile("artifacts/tamaswap.min.html"));

        assertTrue(_contains(app, bytes("Onchain HTML, forever online.")), "footer copy missing");
        assertTrue(_contains(app, bytes("Built with <a href=\"https://tama.tools\"")), "tama link missing");
        assertTrue(_contains(app, bytes("<a href=\"https://veritylang.com\"")), "verity link missing");
        assertTrue(_contains(app, bytes("Made by <a href=\"https://x.com/foglightprivacy\"")), "foglight link missing");
    }

    function testGeneratedAppUsesChainLabelsInBootstrapMessages() public view {
        bytes memory app = bytes(vm.readFile("artifacts/tamaswap.min.html"));

        assertFalse(_contains(app, bytes("not deployed on chain \"+CID")), "bootstrap messages should use chain labels");
        assertTrue(_contains(app, bytes("not deployed on chain \"+chainLabel()")), "bootstrap label helper missing");
    }

    function testHtmlStructureAndDataChunks() public view {
        assertLe(address(frontend).code.length, EIP_170_CAP, "wrapper exceeds EIP-170");
        assertGe(EIP_170_CAP - address(frontend).code.length, MIN_WRAPPER_MARGIN, "wrapper margin too small");
        _assertRawDataOk(
            frontend.HTML_DATA(), bytes(vm.toBase64(vm.readFileBinary("artifacts/tamaswap.min.html.gz"))), "HTML_DATA"
        );
        _assertRawDataOk(frontend.DEPLOYMENT_DATA(), bytes(_requestBody("deployment-code")), "DEPLOYMENT_DATA");

        bytes memory html = bytes(frontend.html());
        assertEq(string(_slice(html, 0, 15)), "<!doctype html>");
        assertTrue(_contains(html, bytes("DecompressionStream(\"gzip\")")), "gzip stream missing");
        assertFalse(_contains(html, bytes("document.open().write(h)")), "document write should not replace provider bridge");
        assertTrue(_contains(html, bytes("new DOMParser().parseFromString")), "DOM parser bootstrap missing");
        assertTrue(_contains(html, bytes("document.head.replaceChildren")), "head replacement missing");
        assertTrue(_contains(html, bytes("document.body.replaceChildren")), "body replacement missing");
        assertTrue(_contains(html, bytes("document.createElement(\"script\")")), "script re-exec missing");
        assertFalse(_contains(html, bytes("0x38ed1739")), "raw app should be compressed");
        assertFalse(_contains(html, bytes("deployment-code")), "deployment resource should not be in root html");
    }

    function testHtmlUsesCompressedBootstrapAndExternalDeploymentResources() public view {
        bytes memory html = bytes(frontend.html());

        assertTrue(_contains(html, bytes("DecompressionStream")), "gzip bootstrap missing");
        assertTrue(_contains(html, bytes("atob(")), "base64 decode missing");
        assertEq(
            keccak256(frontend.HTML_DATA().code),
            keccak256(bytes(vm.toBase64(vm.readFileBinary("artifacts/tamaswap.min.html.gz"))))
        );
        assertGt(bytes(_requestBody("deployment-code")).length, 0, "deployment bundle empty");

        (bool data2Ok,) = address(frontend).staticcall(abi.encodeWithSignature("HTML_DATA_2()"));
        assertFalse(data2Ok, "unexpected second data contract");
        (bool faviconDataOk,) = address(frontend).staticcall(abi.encodeWithSignature("FAVICON_DATA()"));
        assertFalse(faviconDataOk, "unexpected favicon data contract");
        (bool socialDataOk,) = address(frontend).staticcall(abi.encodeWithSignature("SOCIAL_DATA()"));
        assertFalse(socialDataOk, "unexpected social data contract");

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

    function testBootstrapIncludesFaviconAndSocialMetadata() public view {
        bytes memory html = bytes(frontend.html());

        assertTrue(
            _contains(html, bytes("<link rel=\"icon\" type=\"image/svg+xml\" href=\"data:image/svg+xml,")),
            "favicon data URI missing"
        );
        assertTrue(_contains(html, bytes("<meta property=\"og:title\" content=\"TamaSwap\">")), "og title missing");
        assertTrue(_contains(html, bytes("<meta property=\"og:image\" content=\"social.svg\">")), "og image missing");
        assertTrue(
            _contains(html, bytes("<meta property=\"og:image:type\" content=\"image/svg+xml\">")),
            "og image type missing"
        );
        assertTrue(
            _contains(html, bytes("<meta name=\"twitter:card\" content=\"summary_large_image\">")),
            "twitter card missing"
        );
        assertTrue(
            _contains(html, bytes("<meta name=\"twitter:image\" content=\"social.svg\">")), "twitter image missing"
        );
    }

    function testRequestReturnsBrandImages() public view {
        (uint16 socialStatus, string memory social, TamaSwapFrontend.KeyValue[] memory socialHeaders) =
            _request("social.svg");
        assertEq(socialStatus, 200);
        assertEq(socialHeaders.length, 2);
        assertEq(socialHeaders[0].key, "Content-Type");
        assertEq(socialHeaders[0].value, "image/svg+xml");
        assertTrue(_contains(bytes(social), bytes("width=\"1200\"")), "social width missing");
        assertTrue(_contains(bytes(social), bytes("height=\"630\"")), "social height missing");
        assertFalse(_contains(bytes(social), bytes("<circle")), "social image should not use background circles");
        assertTrue(_contains(bytes(social), bytes("translate(600 170)")), "social logo should be centered");
        assertTrue(_contains(bytes(social), bytes("x=\"600\"")), "social text should be centered");
        assertTrue(_contains(bytes(social), bytes("text-anchor=\"middle\"")), "social text anchor missing");
        assertTrue(_contains(bytes(social), bytes("TamaSwap")), "social wordmark missing");
        assertTrue(
            _contains(bytes(social), bytes("The first provably unhackable DEX, forever online.")),
            "social description missing"
        );
        assertTrue(_contains(bytes(social), bytes(unicode"玉")), "social logo missing");

        (uint16 faviconStatus, string memory favicon, TamaSwapFrontend.KeyValue[] memory faviconHeaders) =
            _request("favicon.ico");
        assertEq(faviconStatus, 200);
        assertEq(faviconHeaders[0].key, "Content-Type");
        assertEq(faviconHeaders[0].value, "image/svg+xml");
        assertTrue(_contains(bytes(favicon), bytes("viewBox=\"0 0 64 64\"")), "favicon viewbox missing");
        assertTrue(_contains(bytes(favicon), bytes(unicode"玉")), "favicon logo missing");
    }

    function testWrapperRuntimeAndInitcodeStaySmall() public view {
        assertLe(address(frontend).code.length, EIP_170_CAP, "wrapper exceeds EIP-170");
        assertGe(EIP_170_CAP - address(frontend).code.length, MIN_WRAPPER_MARGIN, "wrapper margin too small");
        assertGe(
            EIP_3860_INITCODE_CAP - type(TamaSwapFrontend).creationCode.length,
            MIN_INITCODE_MARGIN,
            "initcode margin too small"
        );
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
        assertTrue(_contains(bytes(headers[2].value), bytes("connect-src 'self' https:")));
        assertFalse(_contains(bytes(headers[2].value), bytes("localhost")));
    }

    function testRequestReturnsDeploymentResources() public view {
        string memory deploymentCode = _requestBody("deployment-code");
        assertGt(bytes(deploymentCode).length, 0, "deployment bundle empty");
        assertFalse(_contains(bytes(deploymentCode), bytes("0x38ed1739")), "deployment bundle should stay compressed");
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
        assertEq(frontend.resolveMode(), ERC_5219_MODE);

        (bool factoryOk,) = address(frontend).staticcall(abi.encodeWithSignature("factory()"));
        assertFalse(factoryOk, "unexpected factory getter");
        (bool routerOk,) = address(frontend).staticcall(abi.encodeWithSignature("router()"));
        assertFalse(routerOk, "unexpected router getter");
    }

    function testConstructorDeploysDataContracts() public view {
        assertTrue(frontend.HTML_DATA() != address(0), "html data missing");
        assertTrue(frontend.DEPLOYMENT_DATA() != address(0), "deployment data missing");
    }

    function _expectedBootstrap(string memory encoded) internal pure returns (string memory) {
        return string.concat(
            "<!doctype html>",
            _bootstrapMeta(),
            "<script>(async()=>{const B=\"",
            encoded,
            "\";try{let u=Uint8Array.from(atob(B),c=>c.charCodeAt()),h=await new Response(new Blob([u]).stream().pipeThrough(new DecompressionStream(\"gzip\"))).text(),d=new DOMParser().parseFromString(h,\"text/html\"),im=n=>document.importNode(n,true);document.head.replaceChildren(...[...d.head.childNodes].map(im));document.body.replaceChildren(...[...d.body.childNodes].map(im));for(let o of [...document.scripts]){let s=document.createElement(\"script\");for(let a of o.attributes)s.setAttribute(a.name,a.value);s.text=o.textContent;o.replaceWith(s)}}catch{document.body.textContent=\"TamaSwap load failed\"}})()</script>"
        );
    }

    function _bootstrapMeta() internal pure returns (string memory) {
        return string.concat(
            "<meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><title>TamaSwap</title>",
            "<meta name=\"description\" content=\"The first provably unhackable DEX, forever online.\"><meta property=\"og:title\" content=\"TamaSwap\">",
            "<meta property=\"og:description\" content=\"The first provably unhackable DEX, forever online.\"><meta property=\"og:image\" content=\"social.svg\">",
            "<meta property=\"og:image:type\" content=\"image/svg+xml\"><meta property=\"og:image:width\" content=\"1200\">",
            "<meta property=\"og:image:height\" content=\"630\"><meta name=\"twitter:card\" content=\"summary_large_image\">",
            "<meta name=\"twitter:title\" content=\"TamaSwap\"><meta name=\"twitter:description\" content=\"The first provably unhackable DEX, forever online.\">",
            "<meta name=\"twitter:image\" content=\"social.svg\"><link rel=\"icon\" type=\"image/svg+xml\" href=\"",
            _faviconDataUri(),
            "\">"
        );
    }

    function _faviconDataUri() internal pure returns (string memory) {
        return "data:image/svg+xml,%3Csvg%20xmlns%3D%22http%3A%2F%2Fwww.w3.org%2F2000%2Fsvg%22%20viewBox%3D%220%200%2064%2064%22%3E%3Cg%20transform%3D%22rotate(-6%2032%2032)%22%3E%3Crect%20x%3D%228%22%20y%3D%228%22%20width%3D%2248%22%20height%3D%2248%22%20rx%3D%228%22%20fill%3D%22%23b9442e%22%2F%3E%3Ctext%20x%3D%2232%22%20y%3D%2244%22%20text-anchor%3D%22middle%22%20font-family%3D%22serif%22%20font-size%3D%2236%22%20font-weight%3D%22600%22%20fill%3D%22%23fffdf6%22%3E%E7%8E%89%3C%2Ftext%3E%3C%2Fg%3E%3C%2Fsvg%3E";
    }

    function _assertTextResource(string memory name, string memory expected) internal view {
        string memory body = _requestBody(name);
        assertEq(body, expected);
    }

    function _requestBody(string memory name) internal view returns (string memory body) {
        (uint16 status, string memory response, TamaSwapFrontend.KeyValue[] memory headers) = _request(name);

        assertEq(status, 200);
        assertEq(headers.length, 2);
        assertEq(headers[0].key, "Content-Type");
        assertEq(headers[0].value, "text/plain; charset=utf-8");
        return response;
    }

    function _request(string memory name)
        internal
        view
        returns (uint16 status, string memory response, TamaSwapFrontend.KeyValue[] memory headers)
    {
        string[] memory resource = new string[](1);
        resource[0] = name;
        TamaSwapFrontend.KeyValue[] memory params = new TamaSwapFrontend.KeyValue[](0);
        return frontend.request(resource, params);
    }

    function _assertRawDataOk(address d, bytes memory expected, string memory label) internal view {
        uint256 size = d.code.length;
        assertGt(size, 0, string.concat(label, " empty"));
        assertLe(size, EIP_170_CAP, string.concat(label, " exceeds EIP-170"));
        assertEq(size, expected.length, string.concat(label, " length mismatch"));
        assertEq(keccak256(d.code), keccak256(expected), string.concat(label, " content mismatch"));
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
}
