// Cloudflare Pages Function: catch-all for /api/gateway/* .
// All logic lives in the shared, runtime-agnostic handler so the Vite dev
// middleware can reuse it verbatim.

import { handleGatewayProxy, type GatewayEnv } from "../../_lib/proxy";

interface PagesContext {
  request: Request;
  env: GatewayEnv;
}

export const onRequest = (context: PagesContext): Promise<Response> =>
  handleGatewayProxy(context.request, context.env);
