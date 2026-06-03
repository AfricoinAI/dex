// Dev-only: make the same-origin /api/gateway/* proxy work under `vite dev`.
// Production uses the Cloudflare Pages Function at functions/api/gateway; this
// middleware reuses the identical shared handler so signing behaviour matches.
//
// The gateway secret is read here (Node side) and used only to sign upstream
// requests. It is NEVER exposed to the client bundle — these vars are not
// VITE_-prefixed, so Vite does not inject them into import.meta.env.

import type { IncomingMessage, ServerResponse } from "node:http";
import type { Plugin } from "vite";
import { handleGatewayProxy, type GatewayEnv } from "../functions/_lib/proxy";

function nodeToWebRequest(req: IncomingMessage): Request {
  const host = req.headers.host ?? "localhost";
  const url = new URL(req.url ?? "/", `http://${host}`);
  const headers = new Headers();
  for (const [key, value] of Object.entries(req.headers)) {
    if (Array.isArray(value)) headers.set(key, value.join(", "));
    else if (value !== undefined) headers.set(key, value);
  }
  // Read-only proxy: GET/HEAD only, so no request body to forward.
  return new Request(url.toString(), { method: req.method ?? "GET", headers });
}

async function writeWebResponse(res: ServerResponse, response: Response): Promise<void> {
  res.statusCode = response.status;
  response.headers.forEach((value, key) => res.setHeader(key, value));
  res.end(Buffer.from(await response.arrayBuffer()));
}

export function gatewayProxyPlugin(env: Record<string, string>): Plugin {
  const gwEnv: GatewayEnv = {
    GATEWAY_URL: env.GATEWAY_URL,
    DEX_APP_ID: env.DEX_APP_ID,
    DEX_APP_KEY_ID: env.DEX_APP_KEY_ID,
    DEX_GATEWAY_SECRET: env.DEX_GATEWAY_SECRET,
    DEX_PUBLIC_ORIGIN: env.DEX_PUBLIC_ORIGIN,
  };
  return {
    name: "africoin-gateway-proxy",
    configureServer(server) {
      server.middlewares.use((req, res, next) => {
        if (!req.url || !req.url.startsWith("/api/gateway")) return next();
        handleGatewayProxy(nodeToWebRequest(req), gwEnv)
          .then((response) => writeWebResponse(res, response))
          .catch((error: unknown) => {
            res.statusCode = 500;
            res.setHeader("content-type", "application/json");
            res.end(
              JSON.stringify({
                error: "proxy_error",
                message: error instanceof Error ? error.message : "Gateway proxy failed",
              }),
            );
          });
      });
    },
  };
}
