import type { Address } from "viem";

const cache = new Map<string, { price: number | null; ts: number }>();
const TTL = 60_000;

export async function fetchUsdPrice(chainSlug: string, token: Address): Promise<number | null> {
  if (!chainSlug) return null;
  const key = `${chainSlug}:${token.toLowerCase()}`;
  const hit = cache.get(key);
  if (hit && Date.now() - hit.ts < TTL) return hit.price;
  try {
    const res = await fetch(`https://coins.llama.fi/prices/current/${key}`);
    const json = (await res.json()) as { coins?: Record<string, { price?: number }> };
    const price = json?.coins?.[key]?.price;
    const out = typeof price === "number" && price > 0 ? price : null;
    cache.set(key, { price: out, ts: Date.now() });
    return out;
  } catch {
    cache.set(key, { price: null, ts: Date.now() });
    return null;
  }
}
