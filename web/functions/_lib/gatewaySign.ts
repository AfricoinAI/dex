// Africoin gateway app-HMAC signing. Pure Web Crypto so the same code runs in
// Cloudflare Workers/Pages Functions (workerd) and in the Vite dev server
// (Node 20+). No Node-only APIs.

// SHA-256 hex of the empty string — used as the body hash for GET/HEAD.
export const EMPTY_BODY_SHA256 =
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";

const encoder = new TextEncoder();

function toHex(bytes: ArrayBuffer): string {
  const view = new Uint8Array(bytes);
  let out = "";
  for (const b of view) out += b.toString(16).padStart(2, "0");
  return out;
}

export async function sha256Hex(input: string): Promise<string> {
  if (input === "") return EMPTY_BODY_SHA256;
  return toHex(await crypto.subtle.digest("SHA-256", encoder.encode(input)));
}

export async function hmacSha256Hex(secret: string, payload: string): Promise<string> {
  const key = await crypto.subtle.importKey(
    "raw",
    encoder.encode(secret),
    { name: "HMAC", hash: "SHA-256" },
    false,
    ["sign"],
  );
  return toHex(await crypto.subtle.sign("HMAC", key, encoder.encode(payload)));
}

export interface CanonicalParts {
  appId: string;
  keyId: string;
  method: string;
  /** Gateway path without query, e.g. "/v1/assets/list". */
  gatewayPath: string;
  /** Query string WITH a leading "?", or "" when there is none. */
  queryString: string;
  timestamp: string;
  nonce: string;
  bodySha256: string;
}

// The exact 10-line canonical payload the gateway recomputes and verifies.
export function buildCanonicalPayload(p: CanonicalParts): string {
  return [
    "AFRICOIN_APP_REQUEST",
    "v1",
    p.appId,
    p.keyId,
    p.method,
    p.gatewayPath,
    p.queryString,
    p.timestamp,
    p.nonce,
    p.bodySha256,
  ].join("\n");
}

export interface SignedHeaders {
  "x-app-id": string;
  "x-app-key-id": string;
  "x-app-timestamp": string;
  "x-app-nonce": string;
  "x-app-body-sha256": string;
  "x-app-signature": string;
  "x-africoin-client-origin": string;
}

export interface SignInput {
  appId: string;
  keyId: string;
  secret: string;
  clientOrigin: string;
  method: string;
  gatewayPath: string;
  queryString: string;
  bodySha256: string;
  timestamp: string;
  nonce: string;
}

export async function buildSignedHeaders(input: SignInput): Promise<SignedHeaders> {
  const canonical = buildCanonicalPayload(input);
  const signature = await hmacSha256Hex(input.secret, canonical);
  return {
    "x-app-id": input.appId,
    "x-app-key-id": input.keyId,
    "x-app-timestamp": input.timestamp,
    "x-app-nonce": input.nonce,
    "x-app-body-sha256": input.bodySha256,
    "x-app-signature": signature,
    "x-africoin-client-origin": input.clientOrigin,
  };
}
