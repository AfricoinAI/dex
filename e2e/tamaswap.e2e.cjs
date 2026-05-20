#!/usr/bin/env node
const assert = require("node:assert/strict");
const fs = require("node:fs");
const http = require("node:http");
const os = require("node:os");
const path = require("node:path");
const { spawn, spawnSync } = require("node:child_process");

const ROOT = path.resolve(__dirname, "..");
const RPC_URL = process.env.E2E_RPC_URL || "http://127.0.0.1:18545";
const PRIVATE_KEY =
  process.env.PRIVATE_KEY || "0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80";
const TMP = path.join(__dirname, ".tmp");
const DEPLOYMENT = path.join(TMP, "deployment.json");

function playwright() {
  const candidates = [
    "playwright",
    process.env.PLAYWRIGHT_PATH,
    path.join(os.homedir(), ".npm/_npx/9833c18b2d85bc59/node_modules/playwright"),
  ].filter(Boolean);
  for (const candidate of candidates) {
    try {
      return require(candidate);
    } catch (_) {}
  }
  throw new Error("Playwright is not installed. Run `npm install playwright` or set PLAYWRIGHT_PATH.");
}

function run(cmd, args, options = {}) {
  const out = spawnSync(cmd, args, {
    cwd: ROOT,
    encoding: "utf8",
    stdio: options.stdio || "pipe",
    env: { ...process.env, ...options.env },
  });
  if (out.status !== 0) {
    throw new Error(`${cmd} ${args.join(" ")} failed\n${out.stdout || ""}${out.stderr || ""}`);
  }
  return out.stdout;
}

function start(command, args, ready) {
  const child = spawn(command, args, { cwd: ROOT, stdio: ["ignore", "pipe", "pipe"] });
  let text = "";
  child.stdout.on("data", (chunk) => (text += chunk));
  child.stderr.on("data", (chunk) => (text += chunk));
  return new Promise((resolve, reject) => {
    let resolved = false;
    const timer = setTimeout(() => reject(new Error(`${command} did not become ready\n${text}`)), 15000);
    child.on("exit", (code) => {
      if (!resolved) reject(new Error(`${command} exited with ${code}\n${text}`));
    });
    const poll = setInterval(() => {
      if (ready(text)) {
        resolved = true;
        clearInterval(poll);
        clearTimeout(timer);
        resolve(child);
      }
    }, 100);
  });
}

async function rpc(method, params = []) {
  const response = await fetch(RPC_URL, {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ jsonrpc: "2.0", id: 1, method, params }),
  });
  const json = await response.json();
  if (json.error) throw new Error(`${method}: ${json.error.message}`);
  return json.result;
}

async function waitRpc() {
  const started = Date.now();
  while (Date.now() - started < 15000) {
    try {
      await rpc("eth_chainId");
      return;
    } catch (_) {
      await new Promise((resolve) => setTimeout(resolve, 100));
    }
  }
  throw new Error("Anvil RPC did not become ready");
}

function abiBalanceOf(account) {
  return `0x70a08231${account.toLowerCase().slice(2).padStart(64, "0")}`;
}

function serve(deployment) {
  const html = fs
    .readFileSync(path.join(ROOT, "html/tamaswap.html"), "utf8")
    .replace("__FACTORY__", deployment.factory)
    .replace("__ROUTER__", deployment.router);
  const tokenList = JSON.stringify({
    name: "TamaSwap E2E",
    timestamp: new Date(0).toISOString(),
    version: { major: 1, minor: 0, patch: 0 },
    tokens: [
      { chainId: 31337, address: deployment.tokenA, name: "Test Token A", symbol: "TKA", decimals: 18 },
      { chainId: 31337, address: deployment.tokenB, name: "Test Token B", symbol: "TKB", decimals: 18 },
    ],
  });
  const server = http.createServer((req, res) => {
    if (req.url === "/tokenlist.json") {
      res.writeHead(200, { "content-type": "application/json" });
      res.end(tokenList);
      return;
    }
    res.writeHead(200, { "content-type": "text/html" });
    res.end(html);
  });
  return new Promise((resolve) => server.listen(0, "127.0.0.1", () => resolve(server)));
}

function browserLaunchOptions() {
  const chrome = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
  return fs.existsSync(chrome) ? { headless: true, executablePath: chrome } : { headless: true };
}

async function chooseToken(page, button, symbol) {
  await page.locator(button).click();
  await page.locator(".item", { hasText: symbol }).first().click();
}

async function main() {
  fs.mkdirSync(TMP, { recursive: true });
  const { chromium } = playwright();
  const anvil = await start(
    "anvil",
    ["--host", "127.0.0.1", "--port", "18545", "--chain-id", "31337"],
    (text) => text.includes("Listening on"),
  );
  try {
    await waitRpc();
    run("forge", [
      "script",
      "script/DeployE2E.s.sol:DeployE2E",
      "--rpc-url",
      RPC_URL,
      "--broadcast",
      "--private-key",
      PRIVATE_KEY,
    ], {
      env: { PRIVATE_KEY, E2E_OUT: DEPLOYMENT },
    });
    const deployment = JSON.parse(fs.readFileSync(DEPLOYMENT, "utf8"));
    const server = await serve(deployment);
    const url = `http://127.0.0.1:${server.address().port}/`;
    const browser = await chromium.launch(browserLaunchOptions());
    try {
      const page = await browser.newPage();
      page.on("console", (msg) => {
        if (msg.type() === "error") throw new Error(msg.text());
      });
      await page.route("https://tokens.uniswap.org/", (route) => route.fulfill({ json: { tokens: [] } }));
      await page.route("https://coins.llama.fi/**", (route) => route.abort());
      await page.addInitScript(
        ({ account, rpcUrl }) => {
          let connected = false;
          async function send(method, params = []) {
            const response = await fetch(rpcUrl, {
              method: "POST",
              headers: { "content-type": "application/json" },
              body: JSON.stringify({ jsonrpc: "2.0", id: 1, method, params }),
            });
            const json = await response.json();
            if (json.error) throw new Error(json.error.message);
            return json.result;
          }
          window.ethereum = {
            isMetaMask: true,
            request: async ({ method, params = [] }) => {
              if (method === "eth_requestAccounts") {
                connected = true;
                return [account];
              }
              if (method === "eth_accounts") return connected ? [account] : [];
              return send(method, params);
            },
            on: () => {},
            removeListener: () => {},
          };
        },
        { account: deployment.account, rpcUrl: RPC_URL },
      );

      await page.goto(url);
      await page.evaluate((listUrl) => localStorage.setItem("tamaLists", JSON.stringify([listUrl])), `${url}tokenlist.json`);
      await page.reload();
      await page.getByRole("button", { name: "Connect" }).click();
      await page.waitForFunction(() => document.querySelector("#connect").textContent.startsWith("0x"));
      await assert.equal(await page.locator("#chain").textContent(), "Chain 31337");
      await page.waitForFunction(() => document.querySelector("#listStat").textContent.includes("2 tokens loaded"));

      await chooseToken(page, "#pickIn", "TKA");
      await chooseToken(page, "#pickOut", "TKB");
      await page.locator("#swapAmt").fill("1");
      await assert.equal(await page.locator("#priceState").textContent(), "Price unavailable");

      await page.locator("#tabPool").click();
      await chooseToken(page, "#pickLpA", "TKA");
      await chooseToken(page, "#pickLpB", "TKB");
      await page.locator("#lpAmtA").fill("1000");
      await page.locator("#lpAmtB").fill("1000");
      await page.locator("#approveLp").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.startsWith("0x"));
      await page.locator("#doLp").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.startsWith("0x"));

      await page.locator("#tabSwap").click();
      await page.locator("#swapAmt").fill("1");
      await page.waitForFunction(() => document.querySelector("#swapOutAmt").value.length > 0);
      await page.locator("#approveSwap").click();
      await page.waitForFunction(() => document.querySelector("#stat").textContent.startsWith("0x"));
      await page.locator("#doSwap").click();
      await page.waitForFunction(() => document.querySelector("#stat").textContent.startsWith("0x"));

      const pair = await rpc("eth_call", [
        { to: deployment.factory, data: `0xe6a43905${deployment.tokenA.slice(2).padStart(64, "0")}${deployment.tokenB.slice(2).padStart(64, "0")}` },
        "latest",
      ]);
      assert.notEqual(BigInt(`0x${pair.slice(26)}`), 0n);
      const tokenBBalance = await rpc("eth_call", [{ to: deployment.tokenB, data: abiBalanceOf(deployment.account) }, "latest"]);
      assert(BigInt(tokenBBalance) > 0n);
      console.log("TamaSwap E2E passed");
    } finally {
      await browser.close();
      await new Promise((resolve) => server.close(resolve));
    }
  } finally {
    anvil.kill("SIGTERM");
  }
}

main().catch((error) => {
  console.error(error);
  process.exit(1);
});
