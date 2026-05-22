import { expect, test } from "bun:test";
import fs from "node:fs";

test("build script uses terser instead of a custom JavaScript minifier", () => {
  const source = fs.readFileSync("script/build-tamaswap.mjs", "utf8");

  expect(source).toMatch(/from "terser"/);
  expect(source).not.toMatch(/function\s+minifyJs\s*\(/);
});

test("build script emits raw bytecode data contracts from the wrapper constructor", () => {
  const source = fs.readFileSync("script/build-tamaswap.mjs", "utf8");

  expect(source).toMatch(/function _deployData\(bytes memory payload\) private returns \(address d\)/);
  expect(source).toMatch(/extcodecopy\(d, ptr, 0, sz\)/);
  expect(source).toMatch(/HTML_DATA = _deployData\(hex"\$\{encodedHex\}"\)/);
  expect(source).toMatch(/DEPLOYMENT_DATA = _deployData\(hex"\$\{deploymentEncodedHex\}"\)/);
  expect(source).toMatch(/tamaswap\.deployment-code\.txt/);
  expect(source).toMatch(/fs\.writeFileSync\(DEPLOYMENT_CODE_PATH, deploymentEncoded\)/);
  expect(source).toMatch(/bytes private constant SOCIAL_SVG = hex"\$\{socialHex\}"/);
  expect(source).not.toMatch(/FAVICON_DATA = _deployData/);
  expect(source).not.toMatch(/SOCIAL_DATA = _deployData/);
  expect(source).not.toMatch(/function solHexBytes/);
  expect(source).not.toMatch(/contract TamaSwapFrontendData/);
  expect(source).not.toMatch(/contract TamaSwapFrontendData2/);
  expect(source).not.toMatch(/htmlPayload/);
});

test("local frontend server exposes the deployment-code resource", () => {
  const source = fs.readFileSync("script/serve-tamaswap.mjs", "utf8");

  expect(source).toMatch(/tamaswap\.deployment-code\.txt/);
  expect(source).toContain('url.pathname === "/deployment-code"');
  expect(source).toMatch(/readArtifact\(DEPLOYMENT_CODE_PATH\)/);
});

test("frontend resets token selections when the wallet chain changes", () => {
  const source = fs.readFileSync("html/tamaswap.html", "utf8");

  expect(source).toMatch(/function resetSelections\(\)/);
  expect(source).toMatch(/chainChanged",async id=>\{CID=Number\(id\);await syncClock\(\);resetSelections\(\);refreshProvider\(\)\}/);
});

test("frontend requires explicit confirmation for high impact swaps", () => {
  const source = fs.readFileSync("html/tamaswap.html", "utf8");
  const impact = source.match(/async function impact\(seq,a,b,input,output,exactOut\)\{.*?\n\}/s)?.[0] || "";

  expect(source).toMatch(/HIGH_IMPACT_PPM=150000n/);
  expect(source).toMatch(/HIGH_IMPACT_OK=false/);
  expect(source).toContain('Confirm high impact swap');
  expect(impact).toMatch(/if\(\(lastAct\.swap==="in"\|\|lastAct\.swap==="out"\)&&IMPACT_PPM>=HIGH_IMPACT_PPM&&!HIGH_IMPACT_OK\)/);
});

test("frontend disables transaction CTAs while submit handlers are running", () => {
  const source = fs.readFileSync("html/tamaswap.html", "utf8");

  expect(source).toMatch(/async function submitWith\(b,fn\)/);
  expect(source).toMatch(/if\(b\.disabled\)return/);
  expect(source).toMatch(/finally\{b\.disabled=false;updateAll\(\)\}/);
  expect(source).toMatch(/swapCta\.onclick=\(\)=>submitWith\(swapCta,async\(\)=>/);
  expect(source).toMatch(/lpCta\.onclick=\(\)=>submitWith\(lpCta,async\(\)=>/);
  expect(source).toMatch(/burnCta\.onclick=\(\)=>submitWith\(burnCta,async\(\)=>/);
});

test("frontend disables remove liquidity when pair supply cannot be read", () => {
  const source = fs.readFileSync("html/tamaswap.html", "utf8");

  expect(source).toMatch(/async function totalSupply\(a\).*catch\(e\)\{return null\}/);
  expect(source).toContain('if(supply==null){burnCta.textContent="Pool supply unavailable";return}');
  expect(source).not.toContain("outA=supply?liq*ra/supply:0n");
});

test("frontend does not reuse pre-swap allowance while a finite approval spend is pending", () => {
  const source = fs.readFileSync("html/tamaswap.html", "utf8");

  expect(source).toMatch(/spendPending=new Map\(\)/);
  expect(source).toMatch(/allowSeq=0/);
  expect(source).toMatch(/function resetAllowanceCache\(\)\{allowSeq\+\+;allowCache\.clear\(\)\}/);
  expect(source).toMatch(/function markSpend\(t,spender=ROUTER\)/);
  expect(source).toMatch(/spendPending\.set\(k,pre\)/);
  expect(source).toMatch(/function spentValue\(v\)\{return v<0n\?-v-1n:null\}/);
  expect(source).toMatch(/function clearSpend\(k\)/);
  expect(source).toMatch(/async function settleSpend\(k\)/);
  expect(source).toMatch(/if\(v<pre\)\{spendPending\.set\(x,-v-1n\);allowSeq\+\+;break\}/);
  expect(source).toMatch(/spendPending\.has\(k\).*return 0n/);
  expect(source).toMatch(/let sp=spendPending\.get\(k\);if\(sp!=null\)return spentValue\(sp\)\?\?0n/);
  expect(source).toMatch(/let g=allowSeq/);
  expect(source).toMatch(/if\(g!==allowSeq\|\|spendPending\.has\(k\)\|\|pendingApprovals\.get\(k\)!=null\)return 0n/);
  expect(source).toMatch(/function submitted\(h,pool=false,spent=""\)/);
  expect(source).toMatch(/async function submitTx\(to,d,value=0n,pool=false,spent=""\)/);
  expect(source).toMatch(/else await settleSpend\(spent\);updateAll\(\)/);
  expect(source.match(/await submitTx\(ROUTER,d,0n,false,markSpend\(a\)\)/g)?.length).toBeGreaterThanOrEqual(4);
  expect(source).toContain("await submitTx(ROUTER,d,0n,true,[markSpend(a),markSpend(b)])");
  expect(source).toContain("await submitTx(ROUTER,d,0n,true,markSpend(pairTok))");
});

test("frontend wires DeFiLlama prices into visible swap USD helper text", () => {
  const source = fs.readFileSync("html/tamaswap.html", "utf8");

  expect(source).toContain("id=usdIn");
  expect(source).toContain("id=usdOut");
  expect(source).toMatch(/\.usd\{/);
  expect(source).toContain("updateUsd(swapAmt,a,usdIn)");
  expect(source).toContain("updateUsd(swapOutAmt,b,usdOut)");
});
