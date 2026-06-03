// DEX-owned gateway proxy/BFF. The browser calls only this same-origin route;
// the proxy signs every upstream call with app HMAC headers server-side. The
// DEX gateway secret never leaves the server.
//
//   Browser:  GET /api/gateway/v1/assets/list?limit=200
//   Upstream: GET https://gateway.africoin.ai/v1/assets/list?limit=200  (signed)

import { EMPTY_BODY_SHA256, buildSignedHeaders } from "./gatewaySign";

export interface GatewayEnv {
  GATEWAY_URL?: string;
  DEX_APP_ID?: string;
  DEX_APP_KEY_ID?: string;
  DEX_GATEWAY_SECRET?: string;
  DEX_PUBLIC_ORIGIN?: string;
}

const PROXY_PREFIX = "/api/gateway";

// Read-only allowlist. The proxy never relays anything outside these prefixes,
// so it can't be abused as a generic signing oracle for write routes.
const ALLOWED_PREFIXES = [
  "/v1/assets",
  "/v1/exchange/assets",
  "/v1/prices",
  "/v1/rpc",
  "/v1/chain",
];

const REQUIRED_ENV: (keyof GatewayEnv)[] = [
  "GATEWAY_URL",
  "DEX_APP_ID",
  "DEX_APP_KEY_ID",
  "DEX_GATEWAY_SECRET",
  "DEX_PUBLIC_ORIGIN",
];

function json(status: number, body: unknown): Response {
  return new Response(JSON.stringify(body), {
    status,
    headers: { "content-type": "application/json", "cache-control": "no-store" },
  });
}

function isAllowed(gatewayPath: string): boolean {
  return ALLOWED_PREFIXES.some((p) => gatewayPath === p || gatewayPath.startsWith(`${p}/`));
}

export async function handleGatewayProxy(request: Request, env: GatewayEnv): Promise<Response> {
  // Read-only: write flows require a user session/signature path, not app auth.
  if (request.method !== "GET" && request.method !== "HEAD") {
    return json(405, { error: "method_not_allowed", message: "Gateway proxy is read-only." });
  }

  const missing = REQUIRED_ENV.filter((k) => !env[k]);
  if (missing.length > 0) {
    return json(500, {
      error: "proxy_not_configured",
      message: `Missing server env: ${missing.join(", ")}`,
    });
  }

  const url = new URL(request.url);
  if (url.pathname !== PROXY_PREFIX && !url.pathname.startsWith(`${PROXY_PREFIX}/`)) {
    return json(404, { error: "not_found", message: "Unknown proxy path." });
  }

  // Canonical path is the GATEWAY path, not the local proxy path.
  const gatewayPath = url.pathname.slice(PROXY_PREFIX.length) || "/";
  if (!isAllowed(gatewayPath)) {
    return json(403, {
      error: "path_not_allowed",
      message: `Path ${gatewayPath} is not in the read-only allowlist.`,
    });
  }

  const queryString = url.search; // leading "?" or ""
  const method = request.method;
  const timestamp = Math.floor(Date.now() / 1000).toString();
  const nonce = crypto.randomUUID();

  const headers = await buildSignedHeaders({
    appId: env.DEX_APP_ID as string,
    keyId: env.DEX_APP_KEY_ID as string,
    secret: env.DEX_GATEWAY_SECRET as string,
    clientOrigin: env.DEX_PUBLIC_ORIGIN as string,
    method,
    gatewayPath,
    queryString,
    bodySha256: EMPTY_BODY_SHA256, // GET/HEAD: empty body
    timestamp,
    nonce,
  });

  const target = `${(env.GATEWAY_URL as string).replace(/\/$/, "")}${gatewayPath}${queryString}`;

  let upstream: Response;
  try {
    upstream = await fetch(target, {
      method,
      headers: {
        ...headers,
        accept: request.headers.get("accept") ?? "application/json",
      },
    });
  } catch {
    return json(502, { error: "upstream_unavailable", message: "Africoin gateway is unreachable." });
  }

  // Pass through status + body; pin our own caching/content-type headers and
  // drop hop-by-hop / upstream auth echoes.
  const body = await upstream.arrayBuffer();
  return new Response(body, {
    status: upstream.status,
    headers: {
      "content-type": upstream.headers.get("content-type") ?? "application/json",
      "cache-control": upstream.headers.get("cache-control") ?? "no-store",
    },
  });
}
