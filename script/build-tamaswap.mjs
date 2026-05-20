#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, "..");
const HTML_PATH = path.join(ROOT, "html", "tamaswap.html");
const MIN_HTML_PATH = path.join(ROOT, "artifacts", "tamaswap.min.html");
const GZIP_HTML_PATH = path.join(ROOT, "artifacts", "tamaswap.min.html.gz");
const OUT_SOL = path.join(ROOT, "src", "TamaSwapFrontend.sol");

const EIP_170_CAP = 24576;
const STRING_CHUNK_BYTES = 1024;

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

function render({ head, middle, afterRouter, tail, encoded, total, compressed }) {
  return `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title TamaSwap onchain frontend
/// @notice ERC-5219 HTML frontend for the Tama Uniswap V2 router and factory.
/// @dev Generated from html/tamaswap.html by script/build-tamaswap.mjs.
contract TamaSwapFrontend {
    string public constant NAME = "TamaSwap";
    string public constant VERSION = "0.1";

    address public immutable factory;
    address public immutable router;
    address public immutable PAYLOAD;

    struct KeyValue { string key; string value; }

    constructor(address factory_, address router_) payable {
        require(factory_ != address(0), "factory zero");
        require(router_ != address(0), "router zero");
        factory = factory_;
        router = router_;
        PAYLOAD = _deployData(bytes(${solString(encoded, "            ")}));
    }

    function _deployData(bytes memory payload) private returns (address d) {
        require(payload.length <= 0xFFFF, "payload too big");
        bytes memory initcode = bytes.concat(hex"61", bytes2(uint16(payload.length)), hex"80600a5f395ff3", payload);
        assembly ("memory-safe") { d := create(0, add(initcode, 0x20), mload(initcode)) }
        require(d != address(0), "deploy failed");
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
        headers[2] = KeyValue("Content-Security-Policy", "default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; img-src https: data: http://localhost:* http://127.0.0.1:*; connect-src https: http://localhost:* http://127.0.0.1:*; base-uri 'none'; form-action 'none'");
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
            _addr(factory),
            ${solString(middle, "            ")},
            _addr(router),
            ${solString(afterRouter, "            ")},
            _data(PAYLOAD),
            ${solString(tail, "            ")}
        );
    }

    function _data(address target) private view returns (string memory s) {
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

    function _addr(address account) private pure returns (string memory) {
        bytes20 value = bytes20(account);
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

/* ===== tamaswap.html source, ${total} bytes minified, ${compressed} bytes gzip before base64 =====

${fs.readFileSync(HTML_PATH, "utf8")}
===== end tamaswap.html source ===== */
`;
}

function main() {
  const app = minifyHtml(fs.readFileSync(HTML_PATH, "utf8"));
  assertScriptsParse(app);
  const compressed = zlib.gzipSync(Buffer.from(app, "utf8"), { level: 9 });
  const encoded = compressed.toString("base64");
  const template =
    `<!doctype html><script>(async()=>{const F="__FACTORY__",R="__ROUTER__",B="${encoded}";try{let u=Uint8Array.from(atob(B),c=>c.charCodeAt()),h=await new Response(new Blob([u]).stream().pipeThrough(new DecompressionStream("gzip"))).text();h=h.replace("__"+"FACTORY__",F).replace("__"+"ROUTER__",R);document.open().write(h);document.close()}catch{document.body.textContent="TamaSwap load failed"}})()</script>`;
  const factoryIndex = template.indexOf("__FACTORY__");
  const routerIndex = template.indexOf("__ROUTER__");
  if (factoryIndex < 0 || routerIndex < 0 || factoryIndex > routerIndex) {
    throw new Error("expected __FACTORY__ before __ROUTER__");
  }
  if (template.indexOf("__FACTORY__", factoryIndex + 1) >= 0 || template.indexOf("__ROUTER__", routerIndex + 1) >= 0) {
    throw new Error("address placeholders must appear exactly once");
  }
  if (template.includes("*/") || template.includes("/*")) {
    throw new Error("HTML contains block comment delimiters");
  }

  const head = template.slice(0, factoryIndex);
  const middle = template.slice(factoryIndex + "__FACTORY__".length, routerIndex);
  const tailWithPayload = template.slice(routerIndex + "__ROUTER__".length);
  if (middle !== '",R="') {
    throw new Error(`unexpected middle segment: ${JSON.stringify(middle)}`);
  }
  const payloadIndex = tailWithPayload.indexOf(encoded);
  if (payloadIndex < 0 || tailWithPayload.indexOf(encoded, payloadIndex + 1) >= 0) {
    throw new Error("encoded payload must appear exactly once");
  }
  const afterRouter = tailWithPayload.slice(0, payloadIndex);
  const tail = tailWithPayload.slice(payloadIndex + encoded.length);
  if (Buffer.byteLength(encoded, "utf8") > EIP_170_CAP) {
    throw new Error(`PAYLOAD ${Buffer.byteLength(encoded, "utf8")} B exceeds EIP-170`);
  }
  const sol = render({ head, middle, afterRouter, tail, encoded, total: Buffer.byteLength(app, "utf8"), compressed: compressed.length });
  fs.mkdirSync(path.dirname(OUT_SOL), { recursive: true });
  fs.mkdirSync(path.dirname(MIN_HTML_PATH), { recursive: true });
  fs.writeFileSync(MIN_HTML_PATH, app);
  fs.writeFileSync(GZIP_HTML_PATH, compressed);
  fs.writeFileSync(OUT_SOL, sol);

  console.log(`HEAD bytes:   ${Buffer.byteLength(head, "utf8")}`);
  console.log(`SHELL bytes:  ${Buffer.byteLength(head + middle + afterRouter + tail, "utf8")}`);
  console.log(`PAYLOAD bytes:${Buffer.byteLength(encoded, "utf8")}`);
  console.log(`APP bytes:    ${Buffer.byteLength(app, "utf8")}`);
  console.log(`GZIP bytes:   ${compressed.length}`);
  console.log(`BOOT bytes:   ${Buffer.byteLength(template, "utf8")}`);
  console.log(`wrote         ${path.relative(ROOT, OUT_SOL)}`);
}

main();
