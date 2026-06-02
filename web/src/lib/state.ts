import { useEffect, useState } from "react";
import { useChainId } from "wagmi";
import { CONTRACTS } from "../config/contracts";
import { fetchTokenList, type Token } from "./tokenList";

export function useTokens(): { tokens: Token[]; ready: boolean; error: string | null } {
  const chainId = useChainId();
  const [tokens, setTokens] = useState<Token[]>([]);
  const [ready, setReady] = useState(false);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    let cancelled = false;
    setReady(false);
    setError(null);
    const cfg = CONTRACTS[chainId];
    if (!cfg) {
      setTokens([]);
      setReady(true);
      setError(`Chain ${chainId} not configured`);
      return;
    }
    // The token API is the sole source of tradeable tokens: no default list and
    // no auto-injected ETH/WETH. Until the endpoint is configured, surface an
    // explicit empty state rather than falling back to anything.
    if (!cfg.tokenListApiUrl) {
      setTokens([]);
      setReady(true);
      setError("Token list endpoint not configured");
      return;
    }
    fetchTokenList(cfg.tokenListApiUrl, chainId)
      .then((list) => {
        if (cancelled) return;
        setTokens(list);
        setReady(true);
      })
      .catch((e: Error) => {
        if (cancelled) return;
        setTokens([]);
        setReady(true);
        setError(e.message);
      });
    return () => {
      cancelled = true;
    };
  }, [chainId]);

  return { tokens, ready, error };
}

export function useSlippageBps(): bigint {
  const [bps, setBps] = useState<bigint>(50n);
  useEffect(() => {
    const stored = localStorage.getItem("tama:slippagePercent");
    if (stored && /^\d+(\.\d+)?$/.test(stored)) {
      const pct = Number(stored);
      if (pct > 0 && pct <= 50) setBps(BigInt(Math.round(pct * 100)));
    }
  }, []);
  return bps;
}
