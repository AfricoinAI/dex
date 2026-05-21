#!/usr/bin/env node
const assert = require("node:assert/strict");
const fs = require("node:fs");
const http = require("node:http");
const os = require("node:os");
const path = require("node:path");
const zlib = require("node:zlib");
const { spawn, spawnSync } = require("node:child_process");

const ROOT = path.resolve(__dirname, "..");
const RPC_URL = process.env.E2E_RPC_URL || "http://127.0.0.1:18546";
const RPC = new URL(RPC_URL);
const PRIVATE_KEY =
  process.env.PRIVATE_KEY || "0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80";
const TMP = path.join(__dirname, ".tmp");
const DEPLOYMENT = path.join(TMP, "deployment.json");
const ARACHNID_CREATE2 = "0x4e59b44847b379578588920ca78fbf26c0b4956c";
const GLOBAL_FACTORY = "0x00000060cc856a2b760b870290faad078c146258";
const GLOBAL_ROUTER = "0x0000002ec9919637129644e17039ee41d9bf9bce";
const GLOBAL_FRONTEND = "0x00000062f71c1800e171221d4905228e4f7bbac5";

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

function deploymentCodeCalldata() {
  return run("cast", ["calldata", "request(string[],(string,string)[])", "[\"deployment-code\"]", "[]"]).trim();
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

async function ensureArachnidCreate2() {
  assert.notEqual(await rpc("eth_getCode", [ARACHNID_CREATE2, "latest"]), "0x");
}

function abiBalanceOf(account) {
  return `0x70a08231${account.toLowerCase().slice(2).padStart(64, "0")}`;
}

function decodeAbiString(data) {
  if (!/^0x[0-9a-fA-F]*$/.test(data) || data.length < 130) throw new Error("Invalid ABI string");
  return decodeAbiReturnString(data, 0);
}

function decodeAbiReturnString(data, wordIndex) {
  if (!/^0x[0-9a-fA-F]*$/.test(data) || data.length < 130) throw new Error("Invalid ABI string");
  const hex = data.slice(2);
  const head = wordIndex * 64;
  const offset = Number(BigInt(`0x${hex.slice(head, head + 64)}`));
  const length = Number(BigInt(`0x${hex.slice(offset * 2, offset * 2 + 64)}`));
  const start = (offset + 32) * 2;
  return Buffer.from(hex.slice(start, start + length * 2), "hex").toString("utf8");
}

async function frontendHtml(frontend) {
  const data = await rpc("eth_call", [{ to: frontend, data: "0x33c34ac3", gas: "0x20000000" }, "latest"]);
  return decodeAbiString(data);
}

function serve(deployment, html) {
  const tokenList = JSON.stringify({
    name: "TamaSwap E2E",
    timestamp: new Date(0).toISOString(),
    version: { major: 1, minor: 0, patch: 0 },
    tokens: [
      {
        chainId: 31337,
        address: deployment.tokenA,
        name: "Test\u202e Token\u0000 A With Very Very Very Very Very Very Long Name",
        symbol: "TK\u202eA\u0000",
        decimals: 18,
        logoURI: "javascript:alert(1)",
      },
      {
        chainId: 31337,
        address: deployment.tokenB,
        name: "Test Token B",
        symbol: "TKB",
        decimals: 6,
        logoURI:
          "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 1 1'%3E%3Crect width='1' height='1' fill='%23ff4da6'/%3E%3C/svg%3E",
      },
    ],
  });
  const server = http.createServer((req, res) => {
    if (req.url === "/deployment-code") {
      res.writeHead(200, { "content-type": "text/plain; charset=utf-8" });
      res.end(deployment.deploymentCode);
      return;
    }
    if (req.url === "/tokenlist.json") {
      res.writeHead(200, { "content-type": "application/json" });
      res.end(tokenList);
      return;
    }
    if (req.url === "/" || req.url === "/index.html") {
      res.writeHead(200, { "content-type": "text/html; charset=utf-8" });
      res.end(html);
      return;
    }
    res.writeHead(404, { "content-type": "text/plain; charset=utf-8" });
    res.end("Not found");
  });
  return new Promise((resolve) => server.listen(0, "127.0.0.1", () => resolve(server)));
}

function browserLaunchOptions() {
  const chrome = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
  return fs.existsSync(chrome) ? { headless: true, executablePath: chrome } : { headless: true };
}

async function chooseToken(page, button, symbol) {
  await page.locator(button).click();
  await page.locator("#search").fill("");
  await page.locator(".item", { hasText: symbol }).first().click();
}

async function ensureConnected(page) {
  await page.waitForFunction(() => document.readyState === "complete");
  for (let attempt = 0; attempt < 3; attempt++) {
    if ((await page.locator("#connect").textContent()).startsWith("0x")) break;
    await page.locator("#connect").click();
    await page
      .waitForFunction(
        () =>
          document.querySelector("#connect").textContent.startsWith("0x") ||
          document.querySelector("#walletModal.on #wallets .item"),
        null,
        { timeout: 6000 },
      )
      .catch(() => {});
    if (!(await page.locator("#connect").textContent()).startsWith("0x")) {
      if (await page.locator("#walletModal.on #wallets .item").count()) {
        await page.locator("#walletModal.on #wallets .item").first().click();
      }
      await page
        .waitForFunction(() => document.querySelector("#connect").textContent.startsWith("0x"), null, { timeout: 6000 })
        .catch(() => {});
    }
  }
  await page.waitForFunction(() => document.querySelector("#connect").textContent.startsWith("0x"));
  if (await page.locator("#walletModal").evaluate((el) => el.classList.contains("on")).catch(() => false)) {
    await page.locator("#closeWallet").click();
  }
}

async function main() {
  fs.mkdirSync(TMP, { recursive: true });
  const { chromium } = playwright();
  const anvil = await start(
    "anvil",
    [
      "--host",
      RPC.hostname,
      "--port",
      RPC.port || "8545",
      "--chain-id",
      "31337",
      "--steps-tracing",
      "--disable-code-size-limit",
      "--disable-block-gas-limit",
      "--no-request-size-limit",
    ],
    (text) => text.includes("Listening on"),
  );
  try {
    await waitRpc();
    await ensureArachnidCreate2();
    run("forge", [
      "script",
      "script/DeployE2E.s.sol:DeployE2E",
      "--rpc-url",
      RPC_URL,
      "--broadcast",
      "--non-interactive",
      "--private-key",
      PRIVATE_KEY,
    ], {
      env: { PRIVATE_KEY, E2E_OUT: DEPLOYMENT },
    });
    const deployment = JSON.parse(fs.readFileSync(DEPLOYMENT, "utf8"));
    deployment.deploymentCode = decodeAbiReturnString(await rpc("eth_call", [
      { to: deployment.frontend, data: deploymentCodeCalldata(), gas: "0x20000000" },
      "latest",
    ]), 1);
    const initcodes = JSON.parse(zlib.gunzipSync(Buffer.from(deployment.deploymentCode, "base64")).toString("utf8"));
    deployment.factoryInitcode = initcodes.f;
    deployment.routerInitcode = initcodes.r;
    assert.equal(deployment.factory.toLowerCase(), GLOBAL_FACTORY);
    assert.equal(deployment.router.toLowerCase(), GLOBAL_ROUTER);
    assert.equal(deployment.frontend.toLowerCase(), GLOBAL_FRONTEND);
    assert.match(deployment.factoryInitcode, /^0x[0-9a-f]+$/);
    assert.match(deployment.routerInitcode, /^0x[0-9a-f]+$/);
    assert.notEqual(await rpc("eth_getCode", [deployment.factory, "latest"]), "0x");
    assert.notEqual(await rpc("eth_getCode", [deployment.router, "latest"]), "0x");
    const html = await frontendHtml(deployment.frontend);
    assert(html.includes("DecompressionStream"), "E2E did not load compressed onchain frontend");
    const server = await serve(deployment, html);
    const url = `http://127.0.0.1:${server.address().port}/`;
    const browser = await chromium.launch(browserLaunchOptions());
    try {
      const page = await browser.newPage();
      const pageErrors = [];
      const requestErrors = [];
      page.on("console", (msg) => {
        if (msg.type() === "error") pageErrors.push(msg.text());
      });
      page.on("pageerror", (error) => pageErrors.push(error.stack || error.message));
      page.on("requestfailed", (request) => {
        const failure = request.failure()?.errorText || "";
        if (failure === "net::ERR_ABORTED") return;
        requestErrors.push(`${request.url()} ${failure}`.trim());
      });
      await page.route("https://tokens.uniswap.org/", (route) => route.fulfill({ json: { tokens: [] } }));
      await page.route("https://coins.llama.fi/**", (route) => route.fulfill({ json: { coins: {} } }));
      await page.addInitScript(
        ({ account, brokenToken, factory, manualToken, rpcUrl }) => {
          function makeProvider(activeAccount) {
            let connected = localStorage.__walletConnected === "1";
            return {
              request: async ({ method, params = [] }) => {
                if (method === "eth_requestAccounts") {
                  connected = true;
                  localStorage.__walletConnected = "1";
                  return [activeAccount];
                }
                if (method === "eth_accounts") return connected ? [activeAccount] : [];
                return send(method, params);
              },
              on: () => {},
              removeListener: () => {},
            };
          }
          function wordHex(value) {
            return BigInt(value).toString(16).padStart(64, "0");
          }
          function abiString(value) {
            const bytes = Array.from(new TextEncoder().encode(value));
            const data = bytes.map((byte) => byte.toString(16).padStart(2, "0")).join("");
            return `0x${wordHex(32)}${wordHex(bytes.length)}${data.padEnd(Math.ceil(data.length / 64) * 64, "0")}`;
          }
          async function send(method, params = []) {
            if (method === "eth_chainId" && localStorage.__chainIdOverride) return localStorage.__chainIdOverride;
            if (method === "eth_getTransactionReceipt" && window.__holdReceipts) return null;
            if (method === "eth_getCode" && window.__missingFactory && params[0]?.toLowerCase() === factory.toLowerCase()) {
              return "0x";
            }
            if (method === "eth_call") {
              const call = params[0] || {};
              const to = call.to?.toLowerCase();
              const data = call.data || "";
              if (to === manualToken.toLowerCase()) {
                if (data.startsWith("0x313ce567")) return `0x${wordHex(6)}`;
                if (data.startsWith("0x95d89b41")) return abiString("CU\u202eST\u0000");
                if (data.startsWith("0x06fdde03")) return abiString("Custom\u202e Token");
              }
              if (to === brokenToken.toLowerCase() && ["0x313ce567", "0x95d89b41", "0x06fdde03"].some((selector) => data.startsWith(selector))) {
                return "0x";
              }
            }
            if (method === "eth_call" && params[0]?.data?.startsWith("0xdd62ed3e") && window.__forceZeroAllowance) {
              return "0x" + "0".repeat(64);
            }
            if (method === "eth_sendTransaction") {
              window.__sentTxs = window.__sentTxs || [];
              window.__sentTxs.push(params[0]);
              if (params[0]?.data?.startsWith("0x095ea7b3") && window.__rejectNextApproval) {
                window.__rejectNextApproval = false;
                await new Promise((resolve) => setTimeout(resolve, 200));
                throw new Error("User rejected approval");
              }
              if (params[0]?.data?.startsWith("0x095ea7b3") && window.__holdApprovals) {
                window.__releaseApprovals = window.__releaseApprovals || [];
                await new Promise((resolve) => window.__releaseApprovals.push(resolve));
              }
            }
            const response = await fetch(rpcUrl, {
              method: "POST",
              headers: { "content-type": "application/json" },
              body: JSON.stringify({ jsonrpc: "2.0", id: 1, method, params }),
            });
            const json = await response.json();
            if (json.error) throw new Error(json.error.message);
            return json.result;
          }
          const icon = "data:image/svg+xml,<svg xmlns='http://www.w3.org/2000/svg'/>";
          const wallets = [
            { info: { uuid: "primary", name: "Primary Wallet", icon, rdns: "test.primary" }, provider: makeProvider(account) },
            { info: { uuid: "secondary", name: "Secondary Wallet", icon, rdns: "test.secondary" }, provider: makeProvider("0x70997970C51812dc3A010C7d01b50e0d17dc79C8") },
          ];
          wallets[0].provider.name = "Primary Wallet";
          wallets[1].provider.name = "Secondary Wallet";
          if (!localStorage.__delayWallets) {
            window.ethereum = wallets[0].provider;
            window.ethereum.providers = wallets.map((wallet) => wallet.provider);
          }
          window.addEventListener("eip6963:requestProvider", () => {
            setTimeout(
              () => {
                for (const detail of wallets) {
                  window.dispatchEvent(new CustomEvent("eip6963:announceProvider", { detail }));
                }
              },
              localStorage.__delayWallets ? 750 : 0,
            );
          });
          if (localStorage.__delayWallets) {
            for (const delay of [750, 1400]) {
              setTimeout(() => {
                for (const detail of wallets) {
                  window.dispatchEvent(new CustomEvent("eip6963:announceProvider", { detail }));
                }
              }, delay);
            }
          }
        },
        {
          account: deployment.account,
          brokenToken: "0x8888888888888888888888888888888888888888",
          factory: deployment.factory,
          manualToken: "0x9999999999999999999999999999999999999999",
          rpcUrl: RPC_URL,
        },
      );

      await page.goto(url);
      await page.evaluate(() => {
        localStorage.setItem("__walletConnected", "1");
      });
      await page.reload();
      await page.waitForTimeout(900);
      assert.equal(await page.locator("#connect").textContent(), "Connect");
      await page.evaluate(() => {
        localStorage.removeItem("__walletConnected");
      });
      await page.reload();
      const mark = await page.locator(".mark");
      assert.equal(await mark.textContent(), "玉");
      const markStyle = await mark.evaluate((el) => {
        const s = getComputedStyle(el);
        return { background: s.background, borderRadius: s.borderRadius, color: s.color, transform: s.transform };
      });
      assert.match(markStyle.background, /rgb\(185, 68, 46\)/);
      assert.equal(markStyle.borderRadius, "4px");
      assert.equal(markStyle.color, "rgb(255, 253, 246)");
      assert.notEqual(markStyle.transform, "none");
      await page.evaluate(() => {
        window.__missingFactory = true;
      });
      await page.getByRole("button", { name: "Connect" }).click();
      await page.getByRole("button", { name: /Primary Wallet/ }).click();
      await page.waitForFunction(() => document.querySelector("#bootView").textContent.includes("Deploy factory"));
      assert.equal(await page.locator("#bootView").isVisible(), true);
      assert.equal(await page.locator("#swapView").isVisible(), false);
      assert.equal(await page.locator("#poolView").isVisible(), false);
      assert.equal(await page.locator("#tabSwap").isVisible(), false);
      assert.equal(await page.locator("#tabPool").isVisible(), false);
      assert.equal(await page.locator("#bootView .pill").textContent(), "Anvil");
      await page.evaluate(() => {
        window.__missingFactory = false;
      });
      await page.reload();
      await page.evaluate(() => {
        localStorage.setItem("tamaLists", "{not valid json");
        localStorage.setItem("tamaExplorer:31337", "javascript:alert(1)");
      });
      await page.reload();
      await ensureConnected(page);
      assert.equal(await page.locator("#bootView").isVisible(), false);
      assert.equal(await page.locator("#swapView").isVisible(), true);
      await page.waitForFunction(() => document.querySelector("#listStat").textContent.includes("2 tokens loaded"));
      pageErrors.length = 0;
      requestErrors.length = 0;
      const unsafeExplorer = await page.evaluate(() => {
        done(`0x${"1".repeat(64)}`);
        return {
          text: document.querySelector("#stat").textContent,
          links: document.querySelectorAll("#stat a").length,
        };
      });
      assert.match(unsafeExplorer.text, /^Transaction submitted 0x1111/);
      assert.equal(unsafeExplorer.links, 0);
      await page.locator("#pickIn").click();
      await page.locator("#listUrl").fill("http://evil.example/tokenlist.json");
      await page.locator("#loadList").click();
      await assert.equal(
        await page.locator("#listStat").textContent(),
        "Use an HTTPS token list URL or localhost development URL.",
      );
      await page.locator("#closeModal").click();
      assert.deepEqual({ pageErrors, requestErrors }, { pageErrors: [], requestErrors: [] });

      await page.evaluate((listUrl) => {
        localStorage.setItem("tamaLists", JSON.stringify([listUrl]));
        localStorage.setItem("tamaExplorer:31337", "explorer.local");
        localStorage.setItem("__walletConnected", "1");
        localStorage.setItem("__delayWallets", "1");
      }, `${url}tokenlist.json`);
      await page.reload();
      pageErrors.length = 0;
      requestErrors.length = 0;
      await page.waitForFunction(() => document.querySelector("#connect").textContent.startsWith("0x"));
      await page.evaluate(() => localStorage.removeItem("__delayWallets"));
      await page.waitForFunction(() => document.querySelector("#connect").textContent.startsWith("0x"));
      assert.equal(await page.locator("#bootView").isVisible(), false);
      assert.equal(await page.locator("#swapView").isVisible(), true);
      await assert.equal(await page.locator("#swapChain").textContent(), "Anvil");
      await page.locator("#tabPool").click();
      await assert.equal(await page.locator("#chain").textContent(), "Anvil");
      await page.locator("#tabSwap").click();
      await page.waitForFunction(() => document.querySelector("#listStat").textContent.includes("4 tokens loaded"));
      await assert.match(await page.locator("#swapReview").getAttribute("class"), /hide/);
      assert.equal(await page.evaluate(() => safeUrl("http://localhost:31337/admin")), "");

      await page.locator("#pickIn").click();
      await page.locator("#search").fill("TKA");
      const tokenAText = await page.locator(".item", { hasText: "TKA" }).first().textContent();
      assert.doesNotMatch(tokenAText, /[\u0000-\u001f\u007f-\u009f\u200b-\u200f\u202a-\u202e\u2066-\u2069]/);
      assert.match(tokenAText, /Test Token A/);
      await page.locator(".item", { hasText: "TKA" }).first().click();
      assert.equal(await page.locator("#pickIn img").count(), 0);
      await page.locator("#pickOut").click();
      await page.locator("#search").fill("TKB");
      await page.locator(".item", { hasText: "TKB" }).first().click();
      assert.equal(await page.locator("#pickOut img").count(), 1);
      await page.locator("#pickOut").click();
      await page.locator("#search").fill("0x9999999999999999999999999999999999999999");
      await page.waitForFunction(() => document.querySelector(".item .sym")?.textContent === "CUST");
      const manualImportText = await page.locator(".item", { hasText: "CUST" }).first().textContent();
      assert.doesNotMatch(manualImportText, /Import/);
      assert.doesNotMatch(manualImportText, /[\u0000-\u001f\u007f-\u009f\u200b-\u200f\u202a-\u202e\u2066-\u2069]/);
      assert.match(manualImportText, /Unverified token/);
      assert.match(manualImportText, /0x9999\.\.\.9999/);
      await page.locator(".item", { hasText: "CUST" }).first().click();
      const storedManualToken = await page.evaluate(() => ({
        global: localStorage.getItem("tamaUserTokens"),
        mainnet: localStorage.getItem("tamaUserTokens:1"),
        anvil: JSON.parse(localStorage.getItem("tamaUserTokens:31337") || "[]"),
      }));
      assert.equal(storedManualToken.global, null);
      assert.equal(storedManualToken.mainnet, null);
      assert.equal(storedManualToken.anvil[0].chainId, 31337);
      assert.equal(storedManualToken.anvil[0].symbol, "CUST");
      await page.evaluate((deployment) => {
        const key = "tamaUserTokens:31337";
        const saved = JSON.parse(localStorage.getItem(key) || "[]");
        saved.unshift({
          chainId: 31337,
          address: deployment.tokenA,
          symbol: "FAKE",
          name: "Spoofed Canonical Token",
          decimals: 6,
          logoURI: "",
          unverified: true,
        });
        localStorage.setItem(key, JSON.stringify(saved));
      }, deployment);
      await page.reload();
      await ensureConnected(page);
      await page.waitForFunction(() => document.querySelector("#listStat").textContent.includes("tokens loaded"));
      await page.locator("#pickIn").click();
      await page.locator("#search").fill("TKA");
      assert.match(await page.locator(".item", { hasText: "TKA" }).first().textContent(), /Test Token A/);
      assert.equal(await page.locator(".item", { hasText: "FAKE" }).count(), 0);
      await page.locator(".item", { hasText: "TKA" }).first().click();
      await page.locator("#pickOut").click();
      await page.locator("#search").fill("0x8888888888888888888888888888888888888888");
      await page.waitForFunction(() => document.querySelector(".item .sym")?.textContent === "Invalid");
      const fallbackImportText = await page.locator(".item", { hasText: "Invalid" }).first().textContent();
      assert.match(fallbackImportText, /Token metadata unavailable/);
      assert.equal(await page.locator(".item", { hasText: "Invalid" }).first().isDisabled(), true);
      await page.locator("#closeModal").click();

      await page.getByRole("button", { name: "Settings" }).click();
      await page.locator("#slip").fill("1.25");
      await page.locator("#maxApproval").check();
      await page.locator("#closeSettings").click();
      await page.reload();
      await ensureConnected(page);
      await page.getByRole("button", { name: "Settings" }).click();
      assert.equal(await page.locator("#slip").inputValue(), "1.25");
      assert.equal(await page.locator("#maxApproval").isChecked(), true);
      await page.locator("#maxApproval").uncheck();
      await page.locator("#slip").fill("0.5");
      await page.locator("#closeSettings").click();
      await page.locator("#pickIn").click();
      await page.locator("#search").fill("0x9999999999999999999999999999999999999999");
      const persistedImportText = await page.locator(".item", { hasText: "CUST" }).first().textContent();
      assert.match(persistedImportText, /Unverified token/);
      await page.locator("#closeModal").click();
      await page.evaluate(() => localStorage.setItem("__chainIdOverride", "0x2105"));
      await page.reload();
      await ensureConnected(page);
      await page.waitForFunction(() => document.querySelector("#listStat").textContent.includes("chain 8453"));
      await page.locator("#pickIn").click();
      assert.equal(await page.locator(".item", { hasText: "CUST" }).count(), 0);
      await page.locator("#closeModal").click();
      await page.evaluate(() => localStorage.removeItem("__chainIdOverride"));
      await page.reload();
      await ensureConnected(page);
      await page.waitForFunction(() => document.querySelector("#listStat").textContent.includes("chain 31337"));

      await chooseToken(page, "#pickIn", "ETH");
      await chooseToken(page, "#pickOut", "WETH");
      await page.waitForFunction(() => document.querySelector("#balIn").dataset.value.length > 0);
      const nativeFullBalance = await page.locator("#balIn").getAttribute("data-value");
      await page.locator("#balIn").click();
      assert(BigInt(await page.evaluate((v) => parseAmt(v, 18).toString(), await page.locator("#swapAmt").inputValue())) < BigInt(await page.evaluate((v) => parseAmt(v, 18).toString(), nativeFullBalance)));
      await page.locator("#swapAmt").fill(nativeFullBalance);
      await page.waitForFunction(() => document.querySelector("#swapCta").textContent.startsWith("Insufficient"));
      await page.locator("#swapAmt").fill("1");
      await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Wrap");
      await page.locator("#swapCta").click();
      await page.waitForFunction(() => document.querySelector("#stat").textContent.includes("Transaction submitted"));
      await assert.match(await page.locator("#stat a").getAttribute("href"), /^https:\/\/explorer\.local\/tx\/0x/);
      await page.waitForFunction(() => document.querySelector("#balOut").textContent.includes("Balance:"));
      await chooseToken(page, "#pickIn", "WETH");
      await chooseToken(page, "#pickOut", "ETH");
      await page.locator("#swapAmt").fill("0.25");
      await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Unwrap");
      await page.locator("#swapCta").click();
      await page.waitForFunction(() => document.querySelector("#stat").textContent.includes("Transaction submitted"));

      await page.locator("#tabPool").click();
      await chooseToken(page, "#pickLpA", "ETH");
      await chooseToken(page, "#pickLpB", "TKA");
      await page.locator("#lpAmtA").fill("10");
      await page.locator("#lpAmtB").fill("100");
      await page.waitForFunction(() => document.querySelector("#lpCta").textContent === "Approve tokens");
      const approvalsBeforeHeldClick = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length);
      await page.evaluate(() => {
        window.__holdApprovals = true;
        window.__releaseApprovals = [];
      });
      await page.locator("#lpCta").click();
      await page.waitForFunction((count) => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length === count + 1, approvalsBeforeHeldClick);
      await page.evaluate(() => updateAll());
      await page.waitForFunction(() => document.querySelector("#lpCta").textContent === "Waiting for approvals");
      assert.equal(await page.locator("#lpCta").isDisabled(), true);
      assert.equal(
        await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length),
        approvalsBeforeHeldClick + 1,
      );
      await page.evaluate(() => {
        window.__holdApprovals = false;
        for (const release of window.__releaseApprovals || []) release();
        window.__releaseApprovals = [];
      });
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
      const ethPoolApprovals = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")));
      assert.equal(ethPoolApprovals.at(-1).data.slice(-64), (100n * 10n ** 18n).toString(16).padStart(64, "0"));
      await page.waitForFunction(() => document.querySelector("#lpCta").textContent.includes("Create pool"));
      await page.locator("#lpCta").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));

      await page.locator("#tabPool").click();
      await page.locator("[data-pool=add]").click();
      await chooseToken(page, "#pickLpA", "TKB");
      await chooseToken(page, "#pickLpB", "ETH");
      await page.locator("#lpAmtA").fill("3000");
      await page.locator("#lpAmtB").fill("1");
      await page.waitForFunction(() => document.querySelector("#lpCta").textContent === "Approve tokens");
      await page.locator("#lpCta").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
      await page.waitForFunction(() => document.querySelector("#lpCta").textContent.includes("Create pool"));
      await page.locator("#lpCta").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
      await page.locator("#lpAmtA").fill("0.01");
      await page.waitForFunction(() => document.querySelector("#lpAmtB").value.includes("0.000003"));
      assert.notEqual(await page.locator("#lpAmtB").inputValue(), "0.000003");
      await page.waitForFunction(() => ["Approve tokens", "Add liquidity"].includes(document.querySelector("#lpCta").textContent));
      if ((await page.locator("#lpCta").textContent()) === "Approve tokens") {
        await page.locator("#lpCta").click();
        await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
        await page.waitForFunction(() => document.querySelector("#lpCta").textContent === "Add liquidity");
      }
      await page.locator("#lpCta").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"), null, { timeout: 5000 }).catch(async (error) => {
        throw new Error(`${error.message}; pool status=${await page.locator("#poolStat").textContent}; amountA=${await page.locator("#lpAmtA").inputValue()}; amountB=${await page.locator("#lpAmtB").inputValue()}`);
      });

      await page.locator("#tabSwap").click();
      await chooseToken(page, "#pickIn", "TKA");
      await chooseToken(page, "#pickOut", "ETH");
      await page.locator("#swapAmt").fill("1");
      await page.waitForFunction(() => document.querySelector("#swapOutAmt").value.length > 0);
      await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Approve TKA");
      await page.evaluate(() => {
        window.__forceZeroAllowance = true;
        window.__rejectNextApproval = true;
      });
      await page.locator("#swapCta").click();
      await page.evaluate(() => updateAll());
      await page.waitForFunction(() => document.querySelector("#stat").textContent.includes("User rejected approval"));
      await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Approve TKA");
      await page.locator("#swapCta").click();
      await page.waitForFunction(() => document.querySelector("#stat").textContent.includes("Transaction submitted"));
      await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Waiting for approval");
      await page.evaluate(() => {
        window.__forceZeroAllowance = false;
        updateAll();
      });
      await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Swap");

      await chooseToken(page, "#pickIn", "ETH");
      await chooseToken(page, "#pickOut", "TKA");
      await page.locator("#swapAmt").fill("0.1");
      await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Swap");
      await page.locator("#swapCta").click();
      await page.waitForFunction(() => document.querySelector("#stat").textContent.includes("Transaction submitted"));

      await page.locator("#tabPool").click();
      await page.locator("[data-pool=remove]").click();
      await chooseToken(page, "#pickBurnA", "ETH");
      await chooseToken(page, "#pickBurnB", "TKA");
      await page.waitForFunction(() => document.querySelector("#lpBal").textContent.includes("Balance:"));
      await page.locator("#burnLiq").fill("1");
      await page.waitForFunction(() => ["Approve LP", "Remove liquidity"].includes(document.querySelector("#burnCta").textContent));
      if ((await page.locator("#burnCta").textContent()) === "Approve LP") {
        await page.locator("#burnCta").click();
        await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
        await page.waitForFunction(() => document.querySelector("#burnCta").textContent === "Remove liquidity");
      }
      await page.locator("#burnCta").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
      await page.locator("[data-pool=add]").click();
      await page.evaluate(() => {
        lpAmtA.value = "";
        lpAmtB.value = "";
        burnLiq.value = "";
        SEL.pickLpA = null;
        SEL.pickLpB = null;
        SEL.pickBurnA = null;
        SEL.pickBurnB = null;
        btn(pickLpA, null);
        btn(pickLpB, null);
        btn(pickBurnA, null);
        btn(pickBurnB, null);
        updateAll();
      });
      await page.locator("#tabSwap").click();

      await chooseToken(page, "#pickIn", "TKA");
      await chooseToken(page, "#pickOut", "TKB");
      await assert.match(await page.locator("#swapReview").getAttribute("class"), /hide/);
      await page.waitForFunction(() => document.querySelector("#balIn").textContent.includes("Balance:"));
      await page.locator("#balIn").click();
      await assert.match(await page.locator("#swapAmt").inputValue(), /^999/);
      await page.locator("#swapAmt").fill("1");
      await page.waitForFunction(() => !document.querySelector("#swapReview").classList.contains("hide"));
      await page.waitForFunction(() => document.querySelector("#priceState").textContent === "Price unavailable");
      await assert.equal(await page.locator("#priceState").textContent(), "Price unavailable");
      await assert.match(await page.locator("#balIn").textContent(), /Balance:/);
      await assert.equal(await page.locator("#swapCta").textContent(), "No liquidity");
      await page.getByRole("button", { name: "Settings" }).click();
      await page.locator("#slip").fill("1");
      await page.locator("#closeSettings").click();

      await page.locator("#tabPool").click();
      await page.locator("#poolSettings").click();
      await assert.equal(await page.locator("#slip").inputValue(), "1");
      await page.locator("#closeSettings").click();
      await assert.match(await page.locator("#lpReview").getAttribute("class"), /hide/);
      await chooseToken(page, "#pickLpA", "TKA");
      await chooseToken(page, "#pickLpB", "TKB");
      await assert.match(await page.locator("#lpReview").getAttribute("class"), /hide/);
      const addABox = await page.locator("#pickLpA").locator("xpath=ancestor::div[contains(@class,'box')]").boundingBox();
      const addBBox = await page.locator("#pickLpB").locator("xpath=ancestor::div[contains(@class,'box')]").boundingBox();
      assert(addBBox.y > addABox.y + 20, "add liquidity token boxes should be stacked vertically");
      await page.waitForFunction(() => document.querySelector("#lpBalA").textContent.includes("Balance:"));
      await page.locator("#lpBalA").click();
      await assert.match(await page.locator("#lpAmtA").inputValue(), /^999/);
      await page.locator("#lpBalB").click();
      await assert.match(await page.locator("#lpAmtB").inputValue(), /^996999\.99/);
      await page.locator("#lpAmtA").fill("1000");
      await page.locator("#lpAmtB").fill("1000");
      await page.waitForFunction(() => !document.querySelector("#lpReview").classList.contains("hide"));
      await assert.match(await page.locator("#lpBalA").textContent(), /Balance:/);
      await page.waitForFunction(() => document.querySelector("#lpPoolState").textContent.includes("New pool"));
      await assert.match(await page.locator("#lpPoolState").textContent(), /New pool/);
      await page.waitForFunction(() => document.querySelector("#lpPrice").textContent.includes("Initial price"));
      await assert.match(await page.locator("#lpPrice").textContent(), /Initial price/);
      await page.waitForFunction(() => document.querySelector("#lpCta").textContent === "Approve tokens");
      await assert.equal(await page.locator("#lpCta").textContent(), "Approve tokens");
      const bothApprovalsBefore = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length);
      await page.evaluate(() => {
        window.__holdReceipts = true;
      });
      await page.locator("#lpCta").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
      await page.waitForFunction(() => document.querySelector("#lpCta").textContent === "Waiting for approvals");
      assert.equal(
        await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length),
        bothApprovalsBefore + 1,
      );
      await page.evaluate(() => {
        window.__holdReceipts = false;
      });
      await assert.match(await page.locator("#poolStat a").getAttribute("href"), /^https:\/\/explorer\.local\/tx\/0x/);
      for (let i = 0; i < 4; i++) {
        await page.waitForFunction(() => document.querySelector("#lpCta").textContent !== "Waiting for approvals");
        const lpLabel = await page.locator("#lpCta").textContent();
        if (lpLabel.includes("Create pool")) break;
        assert.equal(lpLabel, "Approve tokens");
        const approvalsBeforeClick = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length);
        await page.locator("#lpCta").click();
        await page.waitForFunction(
          (count) =>
            window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length === count + 1 ||
            document.querySelector("#lpCta").textContent !== "Approve tokens",
          approvalsBeforeClick,
        );
        if (
          (await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length)) ===
          approvalsBeforeClick + 1
        ) {
          await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
        }
      }
      await page.waitForFunction(() => document.querySelector("#lpCta").textContent.includes("Create pool"));
      await page.locator("#lpCta").click();
      await page.waitForFunction(() => document.querySelector("#poolStat").textContent.includes("Transaction submitted"));
      await page.waitForFunction(() => document.querySelector("#lpPoolState").textContent.includes("existing pool"));
      await page.locator("#lpAmtA").fill("5");
      await page.waitForFunction(() => document.querySelector("#lpAmtB").value === "5");
      await page.locator("[data-pool=remove]").click();
      await assert.match(await page.locator("#burnReview").getAttribute("class"), /hide/);
      await chooseToken(page, "#pickBurnA", "TKA");
      await chooseToken(page, "#pickBurnB", "TKB");
      const burnABox = await page.locator("#pickBurnA").locator("xpath=ancestor::div[contains(@class,'box')]").boundingBox();
      const burnBBox = await page.locator("#pickBurnB").locator("xpath=ancestor::div[contains(@class,'box')]").boundingBox();
      assert(burnBBox.y > burnABox.y + 20, "remove liquidity token boxes should be stacked vertically");
      await page.waitForFunction(() => !document.querySelector("#burnReview").classList.contains("hide"));
      await assert.match(await page.locator("#pairInfo a").getAttribute("href"), /^https:\/\/explorer\.local\/address\/0x/);
      await assert.match(await page.locator("#burnOutRow").getAttribute("class"), /hide/);
      await page.waitForFunction(() => document.querySelector("#lpBal").textContent.includes("Balance:"));
      await page.locator("#lpBal").click();
      await assert.notEqual(await page.locator("#burnLiq").inputValue(), "");
      await page.waitForFunction(() => !document.querySelector("#burnOutRow").classList.contains("hide"));
      await page.locator("#burnLiq").fill("1");
      await page.waitForFunction(() => !document.querySelector("#burnOutRow").classList.contains("hide"));
      await assert.match(await page.locator("#burnOut").textContent(), /TKA .* TKB/);
      await assert.match(await page.locator("#burnMin").textContent(), /TKA .* TKB/);

      await page.locator("#tabSwap").click();
      await page.locator("#swapAmt").fill("1");
      await page.waitForFunction(() => document.querySelector("#swapOutAmt").value.length > 0);
      await page.waitForFunction(() => ["Approve TKA", "Swap"].includes(document.querySelector("#swapCta").textContent));
      if ((await page.locator("#swapCta").textContent()) === "Approve TKA") {
        const approvalsBeforeSwapClick = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length);
        await page.locator("#swapCta").click();
        await page.waitForFunction(() => document.querySelector("#stat").textContent.includes("Transaction submitted") || document.querySelector("#swapCta").textContent === "Swap").catch(async (error) => {
          throw new Error(
            `${error.message}; swapCta=${await page.locator("#swapCta").textContent()}; stat=${await page.locator("#stat").textContent()}; amount=${await page.locator("#swapAmt").inputValue()}; out=${await page.locator("#swapOutAmt").inputValue()}`,
          );
        });
        const swapApprovals = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")));
        if (swapApprovals.length > approvalsBeforeSwapClick) {
          assert.equal(swapApprovals.at(-1).data.slice(-64), (1n * 10n ** 18n).toString(16).padStart(64, "0"));
        }
        await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Swap");
      }
      await page.locator("#swapCta").click();
      await page.waitForFunction(() => document.querySelector("#stat").textContent.includes("Transaction submitted"), null, { timeout: 5000 }).catch(async (error) => {
        throw new Error(`${error.message}; swap status=${await page.locator("#stat").textContent()}`);
      });
      await assert.match(await page.locator("#stat a").getAttribute("href"), /^https:\/\/explorer\.local\/tx\/0x/);

      await page.getByRole("button", { name: "Settings" }).click();
      await page.locator("#maxApproval").check();
      await page.locator("#closeSettings").click();
      await page.locator("#swapOutAmt").fill("0.5");
      await page.waitForFunction(() => document.querySelector("#swapLimitLabel").textContent === "Maximum sold");
      await page.waitForFunction(() => Number(document.querySelector("#swapAmt").value) > 0);
      await page.waitForFunction(() => /^Price impact (?!0\.00%).+%$/.test(document.querySelector("#priceState").textContent));
      await page.waitForFunction(() => ["Approve TKA", "Swap"].includes(document.querySelector("#swapCta").textContent));
      if ((await page.locator("#swapCta").textContent()) === "Approve TKA") {
        let approvalsBeforeMaxClick = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length);
        await page.locator("#swapCta").click();
        await page.waitForFunction((count) => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length > count, approvalsBeforeMaxClick);
        let maxApprovals = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")));
        if (maxApprovals.at(-1).data.slice(-64) === "0".repeat(64)) {
          await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Approve TKA");
          approvalsBeforeMaxClick = maxApprovals.length;
          await page.locator("#swapCta").click();
          await page.waitForFunction((count) => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")).length > count, approvalsBeforeMaxClick);
          maxApprovals = await page.evaluate(() => window.__sentTxs.filter((tx) => tx.data?.startsWith("0x095ea7b3")));
        }
        assert.equal(maxApprovals.at(-1).data.slice(-64), "f".repeat(64));
        await page.waitForFunction(() => document.querySelector("#swapCta").textContent === "Swap");
      }
      await page.locator("#swapCta").click();
      await page.waitForFunction(() => document.querySelector("#stat").textContent.includes("Transaction submitted"), null, { timeout: 5000 }).catch(async (error) => {
        throw new Error(`${error.message}; exact-output swap status=${await page.locator("#stat").textContent()}`);
      });
      await assert.match(await page.locator("#stat a").getAttribute("href"), /^https:\/\/explorer\.local\/tx\/0x/);

      const pair = await rpc("eth_call", [
        { to: deployment.factory, data: `0xe6a43905${deployment.tokenA.slice(2).padStart(64, "0")}${deployment.tokenB.slice(2).padStart(64, "0")}` },
        "latest",
      ]);
      assert.notEqual(BigInt(`0x${pair.slice(26)}`), 0n);
      const tokenBBalance = await rpc("eth_call", [{ to: deployment.tokenB, data: abiBalanceOf(deployment.account) }, "latest"]);
      assert(BigInt(tokenBBalance) > 0n);
      assert.deepEqual({ pageErrors, requestErrors }, { pageErrors: [], requestErrors: [] });
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
