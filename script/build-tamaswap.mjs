#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, "..");
const HTML_PATH = path.join(ROOT, "html", "tamaswap.html");
const OUT_SOL = path.join(ROOT, "src", "TamaSwapFrontend.sol");

const EIP_170_CAP = 24576;
const HEX_CHUNK_BYTES = 128;

function chunks(hex) {
  const out = [];
  const n = HEX_CHUNK_BYTES * 2;
  for (let i = 0; i < hex.length; i += n) {
    out.push(`            hex"${hex.slice(i, i + n)}"`);
  }
  return out.join("\n");
}

function dataExpr(buf) {
  if (buf.length === 0) return "hex\"\"";
  return `bytes.concat(\n${chunks(buf.toString("hex"))}\n        )`;
}

function render({ head, tail, total }) {
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
    address public immutable HEAD;
    address public immutable TAIL;

    struct KeyValue { string key; string value; }

    constructor(address factory_, address router_) payable {
        require(factory_ != address(0), "factory zero");
        require(router_ != address(0), "router zero");
        factory = factory_;
        router = router_;
        HEAD = _deployData(${dataExpr(head)});
        TAIL = _deployData(${dataExpr(tail)});
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

    function request(string[] memory, KeyValue[] memory)
        external
        view
        returns (uint16 statusCode, string memory body, KeyValue[] memory headers)
    {
        statusCode = 200;
        body = _html();
        headers = new KeyValue[](2);
        headers[0] = KeyValue("Content-Type", "text/html; charset=utf-8");
        headers[1] = KeyValue("Cache-Control", "public, max-age=31536000, immutable");
    }

    function resolveMode() external pure returns (bytes32) {
        return "5219";
    }

    function _html() private view returns (string memory) {
        return string.concat(_data(HEAD), _addr(factory), "\\",ROUTER=\\"", _addr(router), _data(TAIL));
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

/* ===== tamaswap.html source, ${total} bytes before address injection =====

${fs.readFileSync(HTML_PATH, "utf8")}
===== end tamaswap.html source ===== */
`;
}

function main() {
  const template = fs.readFileSync(HTML_PATH, "utf8");
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

  const head = Buffer.from(template.slice(0, factoryIndex), "utf8");
  const middle = Buffer.from(template.slice(factoryIndex + "__FACTORY__".length, routerIndex), "utf8");
  const tail = Buffer.from(template.slice(routerIndex + "__ROUTER__".length), "utf8");
  if (middle.toString("utf8") !== '",ROUTER="') {
    throw new Error(`unexpected middle segment: ${JSON.stringify(middle.toString("utf8"))}`);
  }
  for (const [name, part] of [["HEAD", head], ["TAIL", tail]]) {
    if (part.length > EIP_170_CAP) throw new Error(`${name} ${part.length} B exceeds EIP-170`);
  }

  const sol = render({ head, tail, total: Buffer.byteLength(template, "utf8") });
  fs.mkdirSync(path.dirname(OUT_SOL), { recursive: true });
  fs.writeFileSync(OUT_SOL, sol);

  console.log(`HEAD bytes:   ${head.length}`);
  console.log(`TAIL bytes:   ${tail.length}`);
  console.log(`wrote         ${path.relative(ROOT, OUT_SOL)}`);
}

main();
