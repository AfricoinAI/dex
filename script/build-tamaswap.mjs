#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { minify } from "terser";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, "..");
const HTML_PATH = path.join(ROOT, "html", "tamaswap.html");
const MIN_HTML_PATH = path.join(ROOT, "artifacts", "tamaswap.min.html");
const GZIP_HTML_PATH = path.join(ROOT, "artifacts", "tamaswap.min.html.gz");
const DEPLOYMENT_CODE_PATH = path.join(ROOT, "artifacts", "tamaswap.deployment-code.txt");
const OUT_SOL = path.join(ROOT, "src", "TamaSwapFrontend.sol");
const FACTORY_DEPLOYER_PATH = path.join(ROOT, "src", "generated", "verity", "UniswapV2FactoryDeployer.sol");
const ROUTER_ARTIFACT_PATH = path.join(ROOT, "out", "TamaRouter.sol", "TamaRouter.json");
const LOCAL_WETH_ARTIFACT_PATH = path.join(ROOT, "out", "E2ETokens.sol", "E2EWETH.json");

const EIP_170_CAP = 24576;
const EIP_3860_INITCODE_CAP = 49152;
const STRING_CHUNK_BYTES = 1024;
const ARACHNID_CREATE2 = "0x4e59b44847b379578588920cA78FbF26c0B4956C";
const FACTORY_SALT = "e7de01c00746d6ee6cacea2e58353be0f49b1826adaa8a7adaafaf5a235dbfcd";
const ROUTER_SALT = "91a6fe37677fd168cdb604b5f0b46515ae2e3f403fa634a5c8b32dd5b6ba6b41";
const LOCAL_WETH_SALT = keccakUtf8("tama-uni-v2.local-weth");
const SOCIAL_DESCRIPTION = "The first provably unhackable DEX, forever online.";
const FAVICON_SVG =
  '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64"><g transform="rotate(-6 32 32)"><rect x="8" y="8" width="48" height="48" rx="8" fill="#b9442e"/><text x="32" y="44" text-anchor="middle" font-family="serif" font-size="36" font-weight="600" fill="#fffdf6">玉</text></g></svg>';
const FAVICON_DATA_URI = `data:image/svg+xml,${encodeURIComponent(FAVICON_SVG)}`;
const SOCIAL_SVG =
  `<svg xmlns="http://www.w3.org/2000/svg" width="1200" height="630" viewBox="0 0 1200 630"><rect width="1200" height="630" fill="#fff8fb"/><g transform="translate(600 170) rotate(-6)"><rect x="-100" y="-100" width="200" height="200" rx="28" fill="#b9442e"/><rect x="-90" y="-90" width="180" height="180" rx="20" fill="none" stroke="#fff0e6" stroke-opacity=".58" stroke-width="7"/><text y="58" text-anchor="middle" font-family="serif" font-size="118" font-weight="600" fill="#fffdf6">玉</text></g><text x="600" y="390" text-anchor="middle" font-family="Georgia,serif" font-size="112" font-weight="700" fill="#111827">TamaSwap</text><text x="600" y="462" text-anchor="middle" font-family="system-ui,sans-serif" font-size="34" font-weight="600" fill="#6b7280">${SOCIAL_DESCRIPTION}</text></svg>`;
const BOOT_META =
  `<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>TamaSwap</title><meta name="description" content="${SOCIAL_DESCRIPTION}"><meta property="og:title" content="TamaSwap"><meta property="og:description" content="${SOCIAL_DESCRIPTION}"><meta property="og:image" content="social.svg"><meta property="og:image:type" content="image/svg+xml"><meta property="og:image:width" content="1200"><meta property="og:image:height" content="630"><meta name="twitter:card" content="summary_large_image"><meta name="twitter:title" content="TamaSwap"><meta name="twitter:description" content="${SOCIAL_DESCRIPTION}"><meta name="twitter:image" content="social.svg"><link rel="icon" type="image/svg+xml" href="${FAVICON_DATA_URI}">`;
const BOOT_SCRIPT_HEAD =
  '<script>(async()=>{const B="';
const BOOT_SCRIPT_TAIL =
  '";try{let u=Uint8Array.from(atob(B),c=>c.charCodeAt()),h=await new Response(new Blob([u]).stream().pipeThrough(new DecompressionStream("gzip"))).text(),d=new DOMParser().parseFromString(h,"text/html"),im=n=>document.importNode(n,true);document.head.replaceChildren(...[...d.head.childNodes].map(im));document.body.replaceChildren(...[...d.body.childNodes].map(im));for(let o of [...document.scripts]){let s=document.createElement("script");for(let a of o.attributes)s.setAttribute(a.name,a.value);s.text=o.textContent;o.replaceWith(s)}}catch{document.body.textContent="TamaSwap load failed"}})()</script>';

function solString(value, indent = "        ") {
  const parts = [];
  for (let i = 0; i < value.length; i += STRING_CHUNK_BYTES) {
    const chunk = value
      .slice(i, i + STRING_CHUNK_BYTES)
      .replace(/\\/g, "\\\\")
      .replace(/"/g, '\\"');
    parts.push(`${indent}"${chunk}"`);
  }
  if (parts.length === 1) return parts[0].trimStart();
  return `string.concat(\n${parts.join(",\n")}\n${indent})`;
}

function normalizeHex(value, label) {
  let hex = String(value || "").trim().replace(/^0x/i, "").replace(/\s+/g, "").toLowerCase();
  if (!hex || hex.length % 2 !== 0 || /[^0-9a-f]/.test(hex)) {
    throw new Error(`${label} must be non-empty even-length hex`);
  }
  return hex;
}

function hexToBytes(hex, label = "hex") {
  return Buffer.from(normalizeHex(hex, label), "hex");
}

function keccakHex(hex, label = "hex") {
  const input = `0x${normalizeHex(hex, label)}`;
  try {
    return normalizeHex(execFileSync("cast", ["keccak", input], { encoding: "utf8" }), "keccak output");
  } catch (err) {
    const message = err?.stderr?.toString?.().trim() || err.message;
    throw new Error(`cast keccak failed for ${label}: ${message}`);
  }
}

function keccakUtf8(value) {
  return keccakHex(Buffer.from(value, "utf8").toString("hex"), value);
}

function keccakBytes(bytes) {
  return hexToBytes(keccakHex(Buffer.from(bytes).toString("hex"), "bytes"), "keccak output");
}

function create2Address(saltHex, initHex) {
  const payload = Buffer.concat([
    Buffer.from("ff", "hex"),
    hexToBytes(ARACHNID_CREATE2, "Arachnid CREATE2 address"),
    hexToBytes(saltHex, "salt"),
    keccakBytes(hexToBytes(initHex, "initcode")),
  ]);
  return `0x${keccakBytes(payload).toString("hex").slice(-40)}`;
}

function abiEncodeAddress(address) {
  return normalizeHex(address, "address").padStart(64, "0");
}

function factoryCreationCode() {
  const source = fs.readFileSync(FACTORY_DEPLOYER_PATH, "utf8");
  const match =
    source.match(/\bbytes\s+memory\s+code\s*=\s*hex"([0-9a-fA-F]+)";/) ||
    source.match(/function\s+creationCode\(\)\s+internal\s+pure\s+returns\s+\(bytes\s+memory\)[\s\S]*?return\s+hex"([0-9a-fA-F]+)";/);
  if (!match) {
    throw new Error(`could not find factory bytecode hex in ${path.relative(ROOT, FACTORY_DEPLOYER_PATH)}`);
  }
  return normalizeHex(match[1], "factory creation code");
}

function minifyCss(css) {
  return css
    .replace(/\/\*[\s\S]*?\*\//g, "")
    .replace(/\s*([{}:;,>+~])\s*/g, "$1")
    .replace(/;}/g, "}")
    .trim();
}

async function minifyScript(js) {
  const result = await minify(js, {
    compress: { passes: 2 },
    ecma: 2020,
    format: { comments: false },
    mangle: { toplevel: false },
    module: false,
    toplevel: false,
  });
  if (!result.code) throw new Error("terser returned empty output");
  return result.code;
}

async function minifyHtml(html) {
  let out = html.replace(/<style>([\s\S]*?)<\/style>/g, (_, css) => `<style>${minifyCss(css)}</style>`);
  const scripts = [];
  out = out.replace(/<script>([\s\S]*?)<\/script>/g, (_, js) => {
    scripts.push(js);
    return `<script>__TAMA_SCRIPT_${scripts.length - 1}__</script>`;
  });
  for (let i = 0; i < scripts.length; i++) {
    out = out.replace(`__TAMA_SCRIPT_${i}__`, await minifyScript(scripts[i]));
  }
  return out.replace(/>\s+</g, "><").trim();
}

function assertScriptsParse(html) {
  for (const match of html.matchAll(/<script>([\s\S]*?)<\/script>/g)) {
    new Function(match[1]);
  }
}

function render({
  head,
  tail,
  encodedHex,
  deploymentEncodedHex,
  socialHex,
  deploymentEncoded,
  factoryAddress,
  routerAddress,
  total,
  compressed,
  deploymentCompressed,
}) {
  const faviconHex = Buffer.from(FAVICON_SVG, "utf8").toString("hex");
  return `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title TamaSwap onchain frontend
/// @notice ERC-5219 HTML frontend for the Tama Uniswap V2 router and factory.
/// @dev Generated from html/tamaswap.html by script/build-tamaswap.mjs.
contract TamaSwapFrontend {
    /// @notice Human-readable frontend name.
    string public constant NAME = "TamaSwap";

    /// @notice Human-readable frontend version.
    string public constant VERSION = "0.1";

    /// @notice Address containing the gzipped/base64-encoded HTML payload as contract code.
    address public immutable HTML_DATA;

    /// @notice Address containing the gzipped/base64-encoded deployment bundle as contract code.
    address public immutable DEPLOYMENT_DATA;

    /// @notice SVG favicon served by ERC-5219 resource requests.
    bytes private constant FAVICON_SVG = hex"${faviconHex}";

    /// @notice SVG social preview image served by ERC-5219 resource requests.
    bytes private constant SOCIAL_SVG = hex"${socialHex}";

    /// @notice HTTP-style response header key/value pair.
    struct KeyValue { string key; string value; }

    /// @notice Deploys the HTML and deployment payloads into data contracts.
    constructor() payable {
        HTML_DATA = _deployData(hex"${encodedHex}");
        DEPLOYMENT_DATA = _deployData(hex"${deploymentEncodedHex}");
    }

    /// @notice Deploys a byte payload as contract code and returns its data address.
    /// @param payload Data bytes to store as contract runtime code.
    /// @return d Address of the deployed data contract.
    function _deployData(bytes memory payload) private returns (address d) {
        require(payload.length <= 0xFFFF, "payload too big");
        bytes memory initcode = bytes.concat(hex"61", bytes2(uint16(payload.length)), hex"80600a5f395ff3", payload);
        assembly ("memory-safe") {
            d := create(0, add(initcode, 0x20), mload(initcode))
        }
        require(d != address(0), "deploy failed");
    }

    /// @notice Returns the complete bootstrapping HTML document.
    /// @return The HTML document as a string.
    function html() external view returns (string memory) {
        return _html();
    }

    /// @notice Serves ERC-5219 resources for the frontend, deployment bundle, favicon, and social image.
    /// @param resource Requested path segments.
    /// @dev The unnamed ERC-5219 request metadata argument is ignored.
    /// @return statusCode HTTP-style response status code.
    /// @return body Response body.
    /// @return headers HTTP-style response headers.
    function request(string[] memory resource, KeyValue[] memory)
        external
        view
        returns (uint16 statusCode, string memory body, KeyValue[] memory headers)
    {
        if (!_isIndexResource(resource)) {
            if (resource.length == 1) {
                bytes32 value = keccak256(bytes(resource[0]));
                if (value == keccak256(bytes("deployment-code"))) {
                    statusCode = 200;
                    body = _deploymentCode();
                    headers = _textHeaders();
                    return (statusCode, body, headers);
                }
                if (value == keccak256(bytes("social.svg"))) {
                    statusCode = 200;
                    body = string(SOCIAL_SVG);
                    headers = _svgHeaders();
                    return (statusCode, body, headers);
                }
                if (value == keccak256(bytes("favicon.ico")) || value == keccak256(bytes("favicon.svg"))) {
                    statusCode = 200;
                    body = string(FAVICON_SVG);
                    headers = _svgHeaders();
                    return (statusCode, body, headers);
                }
            }
            statusCode = 404;
            body = "Not found";
            headers = new KeyValue[](1);
            headers[0] = KeyValue("Content-Type", "text/plain; charset=utf-8");
            return (statusCode, body, headers);
        }
        statusCode = 200;
        body = _html();
        headers = new KeyValue[](3);
        headers[0] = KeyValue("Content-Type", "text/html; charset=utf-8");
        headers[1] = KeyValue("Cache-Control", "public, max-age=31536000, immutable");
        headers[2] = KeyValue("Content-Security-Policy", "default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src 'self' https: data:; connect-src 'self' https:; base-uri 'none'; form-action 'none'");
    }

    /// @notice Returns the ERC-5219 resolver mode identifier.
    /// @return ERC-5219 mode value.
    function resolveMode() external pure returns (bytes32) {
        return "5219";
    }

    /// @notice Checks whether a resource path should return the main HTML document.
    /// @param resource Requested path segments.
    /// @return True when the resource is the root, slash, empty string, or index.html path.
    function _isIndexResource(string[] memory resource) private pure returns (bool) {
        if (resource.length == 0) return true;
        if (resource.length == 1) {
            bytes32 value = keccak256(bytes(resource[0]));
            return value == keccak256(bytes("")) || value == keccak256(bytes("/")) || value == keccak256(bytes("index.html"));
        }
        return false;
    }

    /// @notice Builds the complete HTML document from the shell and stored payload.
    /// @return The HTML document as a string.
    function _html() private view returns (string memory) {
        return string.concat(
            ${solString(head, "            ")},
            _readData(HTML_DATA),
            ${solString(tail, "            ")}
        );
    }

    /// @notice Returns the encoded deployment bundle consumed by the frontend.
    /// @return The deployment bundle as a string.
    function _deploymentCode() private view returns (string memory) {
        return _readData(DEPLOYMENT_DATA);
    }

    /// @notice Reads all runtime code bytes from a data contract as a string.
    /// @param d Address of the data contract to read.
    /// @return s Runtime code copied from the data contract.
    function _readData(address d) private view returns (string memory s) {
        assembly ("memory-safe") {
            let sz := extcodesize(d)
            s := mload(0x40)
            mstore(s, sz)
            let ptr := add(s, 0x20)
            extcodecopy(d, ptr, 0, sz)
            let padded := and(add(sz, 0x1f), not(0x1f))
            mstore(add(ptr, padded), 0)
            mstore(0x40, add(add(ptr, padded), 0x20))
        }
    }

    /// @notice Returns immutable text/plain cache headers.
    /// @return headers Headers for plain text responses.
    function _textHeaders() private pure returns (KeyValue[] memory headers) {
        headers = new KeyValue[](2);
        headers[0] = KeyValue("Content-Type", "text/plain; charset=utf-8");
        headers[1] = KeyValue("Cache-Control", "public, max-age=31536000, immutable");
    }

    /// @notice Returns immutable SVG image cache headers.
    /// @return headers Headers for SVG responses.
    function _svgHeaders() private pure returns (KeyValue[] memory headers) {
        headers = new KeyValue[](2);
        headers[0] = KeyValue("Content-Type", "image/svg+xml");
        headers[1] = KeyValue("Cache-Control", "public, max-age=31536000, immutable");
    }
}

/* ===== tamaswap.html source, ${total} bytes minified, ${compressed} bytes gzip before base64 =====
   ===== deployment bundle, ${deploymentCompressed} bytes gzip before base64 =====

${fs.readFileSync(HTML_PATH, "utf8")}
===== end tamaswap.html source ===== */
`;
}

async function main() {
  const factoryInit = factoryCreationCode();
  const factoryAddress = create2Address(FACTORY_SALT, factoryInit);
  const routerArtifact = JSON.parse(fs.readFileSync(ROUTER_ARTIFACT_PATH, "utf8"));
  const routerCreation = normalizeHex(routerArtifact?.bytecode?.object, "router creation bytecode");
  const routerInit = `${routerCreation}${abiEncodeAddress(factoryAddress)}`;
  const routerAddress = create2Address(ROUTER_SALT, routerInit);
  const localWethArtifact = JSON.parse(fs.readFileSync(LOCAL_WETH_ARTIFACT_PATH, "utf8"));
  const localWethInit = normalizeHex(localWethArtifact?.bytecode?.object, "local WETH creation bytecode");
  const localWethAddress = create2Address(LOCAL_WETH_SALT, localWethInit);

  let htmlSource = fs.readFileSync(HTML_PATH, "utf8");
  htmlSource = htmlSource
    .replaceAll("__FACTORY__", factoryAddress)
    .replaceAll("__ROUTER__", routerAddress)
    .replaceAll("__FACTORY_SALT__", `0x${FACTORY_SALT}`)
    .replaceAll("__ROUTER_SALT__", `0x${ROUTER_SALT}`)
    .replaceAll("__LOCAL_WETH__", localWethAddress);
  const app = await minifyHtml(htmlSource);
  assertScriptsParse(app);
  if (
    app.includes("__FACTORY__") ||
    app.includes("__ROUTER__") ||
    app.includes("__FACTORY_SALT__") ||
    app.includes("__ROUTER_SALT__") ||
    app.includes("__LOCAL_WETH__")
  ) {
    throw new Error("factory/router placeholders must be replaced before gzip");
  }
  const compressed = zlib.gzipSync(Buffer.from(app, "utf8"), { level: 9 });
  const encoded = compressed.toString("base64");
  const encodedHex = Buffer.from(encoded, "utf8").toString("hex");
  const deploymentJson = JSON.stringify({ f: `0x${factoryInit}`, r: `0x${routerInit}` });
  const deploymentCompressed = zlib.gzipSync(Buffer.from(deploymentJson, "utf8"), { level: 9 });
  const deploymentEncoded = deploymentCompressed.toString("base64");
  const deploymentEncodedHex = Buffer.from(deploymentEncoded, "utf8").toString("hex");
  const socialHex = Buffer.from(SOCIAL_SVG, "utf8").toString("hex");
  const template =
    `<!doctype html>${BOOT_META}${BOOT_SCRIPT_HEAD}${encoded}${BOOT_SCRIPT_TAIL}`;
  const payloadIndex = template.indexOf(encoded);
  if (payloadIndex < 0) {
    throw new Error("expected payload in bootstrap template");
  }
  if (template.indexOf(encoded, payloadIndex + 1) >= 0) {
    throw new Error("encoded payload must appear exactly once");
  }
  if (template.includes("*/") || template.includes("/*")) {
    throw new Error("HTML contains block comment delimiters");
  }

  const head = template.slice(0, payloadIndex);
  const tail = template.slice(payloadIndex + encoded.length);
  if (Buffer.byteLength(encoded, "utf8") > EIP_170_CAP) {
    throw new Error(`PAYLOAD ${Buffer.byteLength(encoded, "utf8")} B exceeds EIP-170`);
  }
  if (Buffer.byteLength(deploymentEncoded, "utf8") > EIP_170_CAP) {
    throw new Error(`DEPLOYMENT_DATA ${Buffer.byteLength(deploymentEncoded, "utf8")} B exceeds EIP-170`);
  }
  const sol = render({
    head,
    tail,
    encodedHex,
    deploymentEncodedHex,
    socialHex,
    deploymentEncoded,
    factoryAddress,
    routerAddress,
    total: Buffer.byteLength(app, "utf8"),
    compressed: compressed.length,
    deploymentCompressed: deploymentCompressed.length,
  });
  if (Buffer.byteLength(encoded, "utf8") + Buffer.byteLength(deploymentEncoded, "utf8") > EIP_3860_INITCODE_CAP) {
    throw new Error("combined data payloads may exceed EIP-3860 after constructor overhead");
  }
  fs.mkdirSync(path.dirname(OUT_SOL), { recursive: true });
  fs.mkdirSync(path.dirname(MIN_HTML_PATH), { recursive: true });
  fs.writeFileSync(MIN_HTML_PATH, app);
  fs.writeFileSync(GZIP_HTML_PATH, compressed);
  fs.writeFileSync(DEPLOYMENT_CODE_PATH, deploymentEncoded);
  fs.writeFileSync(OUT_SOL, sol);

  console.log(`HEAD bytes:   ${Buffer.byteLength(head, "utf8")}`);
  console.log(`SHELL bytes:  ${Buffer.byteLength(head + tail, "utf8")}`);
  console.log(`PAYLOAD bytes:${Buffer.byteLength(encoded, "utf8")}`);
  console.log(`DATA bytes:   ${Buffer.byteLength(deploymentEncoded, "utf8")}`);
  console.log(`FACTORY_INIT: ${hexToBytes(factoryInit, "factory init bytecode").length} bytes`);
  console.log(`ROUTER_INIT:  ${hexToBytes(routerInit, "router init bytecode").length} bytes`);
  console.log(`FACTORY addr: ${factoryAddress}`);
  console.log(`ROUTER addr:  ${routerAddress}`);
  console.log(`LOCAL WETH:   ${localWethAddress}`);
  console.log(`FACTORY salt: 0x${FACTORY_SALT}`);
  console.log(`ROUTER salt:  0x${ROUTER_SALT}`);
  console.log(`WETH salt:    0x${LOCAL_WETH_SALT}`);
  console.log(`APP bytes:    ${Buffer.byteLength(app, "utf8")}`);
  console.log(`GZIP bytes:   ${compressed.length}`);
  console.log(`DATA gzip:    ${deploymentCompressed.length}`);
  console.log(`BOOT bytes:   ${Buffer.byteLength(template, "utf8")}`);
  console.log(`wrote         ${path.relative(ROOT, DEPLOYMENT_CODE_PATH)}`);
  console.log(`wrote         ${path.relative(ROOT, OUT_SOL)}`);
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
