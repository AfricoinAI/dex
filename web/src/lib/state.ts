import { useEffect, useState } from "react";
import { useChainId } from "wagmi";
import { CONTRACTS } from "../config/contracts";
import { listAssets } from "./gateway";
import { assetsToTokens, type Token } from "./tokenList";

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
    // The Africoin platform asset registry (via the same-origin gateway proxy)
    // is the sole source of tradeable tokens: no default list and no
    // auto-injected ETH/WETH.
    listAssets({ limit: 200, offset: 0 })
      .then((assets) => {
        if (cancelled) return;
        setTokens(assetsToTokens(assets, chainId));
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
