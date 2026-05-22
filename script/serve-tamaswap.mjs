#!/usr/bin/env node
import fs from "node:fs";
import http from "node:http";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(__dirname, "..");
const HOST = process.env.HOST || "127.0.0.1";
const PORT = Number(process.env.PORT || 4173);
const GZIP_HTML_PATH = path.join(ROOT, "artifacts", "tamaswap.min.html.gz");
const DEPLOYMENT_CODE_PATH = path.join(ROOT, "artifacts", "tamaswap.deployment-code.txt");
const SOCIAL_DESCRIPTION = "The first provably unhackable DEX, forever online.";
const FAVICON_SVG =
  '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64"><g transform="rotate(-6 32 32)"><rect x="8" y="8" width="48" height="48" rx="8" fill="#b9442e"/><text x="32" y="44" text-anchor="middle" font-family="serif" font-size="36" font-weight="600" fill="#fffdf6">玉</text></g></svg>';
const FAVICON_DATA_URI = `data:image/svg+xml,${encodeURIComponent(FAVICON_SVG)}`;
const BOOT_META =
  `<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>TamaSwap</title><meta name="description" content="${SOCIAL_DESCRIPTION}"><meta property="og:title" content="TamaSwap"><meta property="og:description" content="${SOCIAL_DESCRIPTION}"><meta property="og:image" content="social.svg"><meta property="og:image:type" content="image/svg+xml"><meta property="og:image:width" content="1200"><meta property="og:image:height" content="630"><meta name="twitter:card" content="summary_large_image"><meta name="twitter:title" content="TamaSwap"><meta name="twitter:description" content="${SOCIAL_DESCRIPTION}"><meta name="twitter:image" content="social.svg"><link rel="icon" type="image/svg+xml" href="${FAVICON_DATA_URI}">`;

function bootstrapHtml() {
  const encoded = readArtifact(GZIP_HTML_PATH).toString("base64");
  return `<!doctype html>${BOOT_META}<script>(async()=>{const B="${encoded}";try{let u=Uint8Array.from(atob(B),c=>c.charCodeAt()),h=await new Response(new Blob([u]).stream().pipeThrough(new DecompressionStream("gzip"))).text(),d=new DOMParser().parseFromString(h,"text/html"),im=n=>document.importNode(n,true);document.head.replaceChildren(...[...d.head.childNodes].map(im));document.body.replaceChildren(...[...d.body.childNodes].map(im));for(let o of [...document.scripts]){let s=document.createElement("script");for(let a of o.attributes)s.setAttribute(a.name,a.value);s.text=o.textContent;o.replaceWith(s)}}catch{document.body.textContent="TamaSwap load failed"}})()</script>`;
}

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
      bootstrapHtml(),
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
  if (url.pathname === "/favicon.ico" || url.pathname === "/favicon.svg") {
    send(
      res,
      200,
      { "content-type": "image/svg+xml", "cache-control": "no-store" },
      FAVICON_SVG,
    );
    return;
  }
  send(res, 404, { "content-type": "text/plain; charset=utf-8" }, "Not found");
});

server.listen(PORT, HOST, () => {
  console.log(`TamaSwap frontend server http://${HOST}:${PORT}`);
});
