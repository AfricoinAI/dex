#!/usr/bin/env node
import fs from "node:fs";
import http from "node:http";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, "..");
const HOST = process.env.HOST || "127.0.0.1";
const PORT = Number(process.env.PORT || 4173);
const HTML_PATH = path.join(ROOT, "artifacts", "tamaswap.min.html");
const DEPLOYMENT_CODE_PATH = path.join(ROOT, "artifacts", "tamaswap.deployment-code.txt");

function readArtifact(file) {
  try {
    return fs.readFileSync(file);
  } catch (err) {
    if (err?.code === "ENOENT") {
      throw new Error(`Missing ${path.relative(ROOT, file)}. Run node script/build-tamaswap.mjs first.`);
    }
    throw err;
  }
}

function send(res, status, headers, body) {
  res.writeHead(status, headers);
  res.end(body);
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url || "/", `http://${HOST}:${PORT}`);
  if (url.pathname === "/" || url.pathname === "/index.html") {
    send(
      res,
      200,
      { "content-type": "text/html; charset=utf-8", "cache-control": "no-store" },
      readArtifact(HTML_PATH),
    );
    return;
  }
  if (url.pathname === "/deployment-code") {
    send(
      res,
      200,
      { "content-type": "text/plain; charset=utf-8", "cache-control": "no-store" },
      readArtifact(DEPLOYMENT_CODE_PATH),
    );
    return;
  }
  send(res, 404, { "content-type": "text/plain; charset=utf-8" }, "Not found");
});

server.listen(PORT, HOST, () => {
  console.log(`TamaSwap frontend server http://${HOST}:${PORT}`);
});
