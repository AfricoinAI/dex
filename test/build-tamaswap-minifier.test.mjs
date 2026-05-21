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
