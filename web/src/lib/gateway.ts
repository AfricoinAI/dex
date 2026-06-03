// Client for the DEX-owned, same-origin gateway proxy (/api/gateway/*).
// The browser never talks to the gateway, Supabase, or RPC providers directly,
// and never holds a secret — the proxy signs every upstream call server-side.

const PROXY_BASE = "/api/gateway";

type QueryValue = string | number | boolean | undefined;

async function gatewayGet<T>(path: string, params?: Record<string, QueryValue>): Promise<T> {
  const qs = new URLSearchParams();
  if (params) {
    for (const [key, value] of Object.entries(params)) {
      if (value !== undefined) qs.set(key, String(value));
    }
  }
  const suffix = qs.toString() ? `?${qs.toString()}` : "";
  const res = await fetch(`${PROXY_BASE}${path}${suffix}`, {
    headers: { accept: "application/json" },
  });
  if (!res.ok) {
    let detail = "";
    try {
      const body = (await res.json()) as { message?: string; error?: string };
      detail = body?.message ?? body?.error ?? "";
    } catch {
      /* non-JSON error body */
    }
    throw new Error(`gateway ${path} failed (${res.status})${detail ? `: ${detail}` : ""}`);
  }
  return (await res.json()) as T;
}

// Deployed Africoin platform asset, per /v1/assets/list.
export interface AfricoinAsset {
  id: string;
  token_name?: string;
  token_symbol?: string;
  total_supply?: string | number;
  decimals?: number;
  status?: string;
  contract_address?: string;
  erc20_contract_address?: string;
  factory_address?: string;
  deploy_tx_hash?: string;
  chain_id?: number;
  ipfs_metadata_hash?: string;
  created_at?: string;
  asset_type?: string;
  asset_name?: string;
  origin?: string;
  country?: string;
  country_code?: string;
  location?: string;
  description?: string;
  metadata?: Record<string, unknown>;
}

// Tolerate envelope variation ({assets|data|items|results: [...]} or a bare array).
function unwrapList(data: unknown): AfricoinAsset[] {
  if (Array.isArray(data)) return data as AfricoinAsset[];
  if (data && typeof data === "object") {
    const obj = data as Record<string, unknown>;
    for (const key of ["assets", "data", "items", "results"]) {
      if (Array.isArray(obj[key])) return obj[key] as AfricoinAsset[];
    }
  }
  return [];
}

export async function listAssets(opts?: { limit?: number; offset?: number }): Promise<AfricoinAsset[]> {
  const data = await gatewayGet<unknown>("/v1/assets/list", {
    limit: opts?.limit ?? 200,
    offset: opts?.offset ?? 0,
  });
  return unwrapList(data);
}

export async function readAsset(id: string): Promise<AfricoinAsset | null> {
  const data = await gatewayGet<unknown>("/v1/assets/read", { id });
  if (data && typeof data === "object" && "asset" in (data as Record<string, unknown>)) {
    return (data as { asset: AfricoinAsset }).asset;
  }
  return (data as AfricoinAsset) ?? null;
}

// --- Prices (read-only, gateway-cached) ----------------------------------

export interface SpotPrice {
  pair: string;
  price: number;
  [key: string]: unknown;
}

export function spotPrice(pair: string): Promise<SpotPrice> {
  return gatewayGet<SpotPrice>("/v1/prices/spot", { pair });
}

export function batchPrices(pairs: string[]): Promise<unknown> {
  return gatewayGet("/v1/prices/batch", { pairs: pairs.join(",") });
}

export function convertPrice(from: string, to: string, amount: number): Promise<unknown> {
  return gatewayGet("/v1/prices/convert", { from, to, amount });
}

// --- Chain reads (use instead of embedding RPC provider keys) -------------

export function blockNumber(): Promise<unknown> {
  return gatewayGet("/v1/rpc/block-number");
}

export function transactionReceipt(hash: string): Promise<unknown> {
  return gatewayGet("/v1/rpc/transaction-receipt", { hash });
}

export function addressTransactions(address: string, chainId: number): Promise<unknown> {
  return gatewayGet("/v1/chain/address-transactions", { address, chain_id: chainId });
}
