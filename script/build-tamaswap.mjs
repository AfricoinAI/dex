#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, "..");
const HTML_PATH = path.join(ROOT, "html", "tamaswap.html");
const MIN_HTML_PATH = path.join(ROOT, "artifacts", "tamaswap.min.html");
const GZIP_HTML_PATH = path.join(ROOT, "artifacts", "tamaswap.min.html.gz");
const OUT_SOL = path.join(ROOT, "src", "TamaSwapFrontend.sol");
const FACTORY_DEPLOYER_PATH = path.join(ROOT, "src", "generated", "verity", "UniswapV2FactoryDeployer.sol");
const ROUTER_ARTIFACT_PATH = path.join(ROOT, "out", "TamaRouter.sol", "TamaRouter.json");
const LOCAL_WETH_ARTIFACT_PATH = path.join(ROOT, "out", "E2ETokens.sol", "E2EWETH.json");

const EIP_170_CAP = 24576;
const STRING_CHUNK_BYTES = 1024;
const HEX_CHUNK_BYTES = 1024;
const ARACHNID_CREATE2 = "0x4e59b44847b379578588920cA78FbF26c0B4956C";
const FACTORY_SALT = keccakUtf8("tama-uni-v2.factory");
const ROUTER_SALT = keccakUtf8("tama-uni-v2.router");
const LOCAL_WETH_SALT = keccakUtf8("tama-uni-v2.local-weth");

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

function solHexBytes(rawHex, indent = "        ") {
  const parts = [];
  for (let i = 0; i < rawHex.length; i += HEX_CHUNK_BYTES * 2) {
    parts.push(`${indent}hex"${rawHex.slice(i, i + HEX_CHUNK_BYTES * 2)}"`);
  }
  if (parts.length === 1) return parts[0].trimStart();
  return `bytes.concat(\n${parts.join(",\n")}\n${indent})`;
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
  const match = source.match(/function\s+creationCode\(\)\s+internal\s+pure\s+returns\s+\(bytes\s+memory\)[\s\S]*?return\s+hex"([0-9a-fA-F]+)";/);
  if (!match) {
    throw new Error(`could not find factory creationCode() hex in ${path.relative(ROOT, FACTORY_DEPLOYER_PATH)}`);
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

function minifyJs(js) {
  let out = "";
  let mode = "";
  let escaped = false;
  const word = (c) => /[A-Za-z0-9_$]/.test(c || "");
  const last = () => out[out.length - 1] || "";
  const nextNonSpace = (i) => {
    while (i < js.length && /\s/.test(js[i])) i++;
    return js[i] || "";
  };
  const nextWord = (i) => {
    while (i < js.length && /\s/.test(js[i])) i++;
    const m = js.slice(i).match(/^[A-Za-z_$][A-Za-z0-9_$]*/);
    return m ? m[0] : "";
  };
  const regexAllowedAfter = (c) => !c || "({[=,:;!&|?+-*~^<>".includes(c);
  const asiBoundary = (prev, next, i) => {
    if (!prev || !next || ",;:{([=+-*/%!&|?<>".includes(prev)) return false;
    if (["else", "catch", "finally", "while"].includes(nextWord(i))) return false;
    return /[A-Za-z_$({[!~+-]/.test(next);
  };
  for (let i = 0; i < js.length; i++) {
    const c = js[i];
    if (mode) {
      out += c;
      if (escaped) {
        escaped = false;
      } else if (c === "\\") {
        escaped = true;
      } else if (c === mode) {
        mode = "";
      }
      continue;
    }
    if (c === "\"" || c === "'" || c === "`") {
      mode = c;
      out += c;
      continue;
    }
    if (c === "/" && js[i + 1] === "/") {
      while (i < js.length && js[i] !== "\n") i++;
      continue;
    }
    if (c === "/" && js[i + 1] === "*") {
      i += 2;
      while (i < js.length && !(js[i] === "*" && js[i + 1] === "/")) i++;
      i++;
      continue;
    }
    if (c === "/" && regexAllowedAfter(last())) {
      out += c;
      i++;
      let inClass = false;
      for (; i < js.length; i++) {
        const r = js[i];
        out += r;
        if (r === "\\") {
          out += js[++i] || "";
        } else if (r === "[") {
          inClass = true;
        } else if (r === "]") {
          inClass = false;
        } else if (r === "/" && !inClass) {
          while (/[A-Za-z]/.test(js[i + 1] || "")) out += js[++i];
          break;
        }
      }
      continue;
    }
    if (/\s/.test(c)) {
      let hasNewline = c === "\n" || c === "\r";
      const start = i;
      const n = nextNonSpace(i + 1);
      if (word(last()) && word(n)) out += " ";
      while (i + 1 < js.length && /\s/.test(js[i + 1])) {
        i++;
        hasNewline = hasNewline || js[i] === "\n" || js[i] === "\r";
      }
      if (hasNewline && !word(last()) && asiBoundary(last(), n, start + 1)) out += ";";
      continue;
    }
    out += c;
  }
  return out.trim();
}

function minifyHtml(html) {
  let out = html.replace(/<style>([\s\S]*?)<\/style>/g, (_, css) => `<style>${minifyCss(css)}</style>`);
  out = out.replace(/<script>([\s\S]*?)<\/script>/g, (_, js) => `<script>${minifyJs(js)}</script>`);
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
  encoded,
  deploymentEncoded,
  factoryAddress,
  routerAddress,
  total,
  compressed,
  deploymentCompressed,
}) {
  return `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface ITamaSwapFrontendData {
    function htmlPayload() external view returns (string memory);
}

/// @title TamaSwap onchain frontend HTML data
/// @notice Single companion data contract for the compressed frontend payload.
contract TamaSwapFrontendData {
    function htmlPayload() external pure returns (string memory) {
        return ${solString(encoded, "            ")};
    }
}

/// @title TamaSwap onchain frontend
/// @notice ERC-5219 HTML frontend for the Tama Uniswap V2 router and factory.
/// @dev Generated from html/tamaswap.html by script/build-tamaswap.mjs.
contract TamaSwapFrontend {
    string public constant NAME = "TamaSwap";
    string public constant VERSION = "0.1";

    address public immutable HTML_DATA;
    struct KeyValue { string key; string value; }

    constructor(address htmlData) payable {
        require(htmlData.code.length != 0, "missing data");
        HTML_DATA = htmlData;
    }

    function html() external view returns (string memory) {
        return _html();
    }

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
        headers[2] = KeyValue("Content-Security-Policy", "default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src 'self' https: data: http://localhost:* http://127.0.0.1:*; connect-src 'self' https: http://localhost:* http://127.0.0.1:*; base-uri 'none'; form-action 'none'");
    }

    function resolveMode() external pure returns (bytes32) {
        return "5219";
    }

    function _isIndexResource(string[] memory resource) private pure returns (bool) {
        if (resource.length == 0) return true;
        if (resource.length == 1) {
            bytes32 value = keccak256(bytes(resource[0]));
            return value == keccak256(bytes("")) || value == keccak256(bytes("/")) || value == keccak256(bytes("index.html"));
        }
        return false;
    }

    function _html() private view returns (string memory) {
        return string.concat(
            ${solString(head, "            ")},
            ITamaSwapFrontendData(HTML_DATA).htmlPayload(),
            ${solString(tail, "            ")}
        );
    }

    function _deploymentCode() private pure returns (string memory) {
        return ${solString(deploymentEncoded, "        ")};
    }

    function _textHeaders() private pure returns (KeyValue[] memory headers) {
        headers = new KeyValue[](2);
        headers[0] = KeyValue("Content-Type", "text/plain; charset=utf-8");
        headers[1] = KeyValue("Cache-Control", "public, max-age=31536000, immutable");
    }
}

/* ===== tamaswap.html source, ${total} bytes minified, ${compressed} bytes gzip before base64 =====
   ===== deployment bundle, ${deploymentCompressed} bytes gzip before base64 =====

${fs.readFileSync(HTML_PATH, "utf8")}
===== end tamaswap.html source ===== */
`;
}

function main() {
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
  const app = minifyHtml(htmlSource);
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
  const deploymentJson = JSON.stringify({ f: `0x${factoryInit}`, r: `0x${routerInit}` });
  const deploymentCompressed = zlib.gzipSync(Buffer.from(deploymentJson, "utf8"), { level: 9 });
  const deploymentEncoded = deploymentCompressed.toString("base64");
  const template =
    `<!doctype html><script>(async()=>{const B="${encoded}";try{let u=Uint8Array.from(atob(B),c=>c.charCodeAt()),h=await new Response(new Blob([u]).stream().pipeThrough(new DecompressionStream("gzip"))).text();document.open().write(h);document.close()}catch{document.body.textContent="TamaSwap load failed"}})()</script>`;
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
    encoded,
    deploymentEncoded,
    factoryAddress,
    routerAddress,
    total: Buffer.byteLength(app, "utf8"),
    compressed: compressed.length,
    deploymentCompressed: deploymentCompressed.length,
  });
  fs.mkdirSync(path.dirname(OUT_SOL), { recursive: true });
  fs.mkdirSync(path.dirname(MIN_HTML_PATH), { recursive: true });
  fs.writeFileSync(MIN_HTML_PATH, app);
  fs.writeFileSync(GZIP_HTML_PATH, compressed);
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
  console.log(`wrote         ${path.relative(ROOT, OUT_SOL)}`);
}

main();
