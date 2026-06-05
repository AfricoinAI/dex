import { useEffect, useState } from "react";
import { useChainId } from "wagmi";
import { CONTRACTS } from "../config/contracts";
import { listAssets } from "./gateway";
import { assetsToTokens, stablecoinTokens, type Token } from "./tokenList";

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
    // Tradeable tokens are the chain's native stablecoins (USDC/USDT) plus the
    // Africoin platform asset registry (via the same-origin gateway proxy):
    // no default list and no auto-injected ETH/WETH. Stablecoins stay listed
    // even when the registry is empty or unreachable.
    const stables = stablecoinTokens(chainId);
    listAssets({ limit: 200, offset: 0 })
      .then((assets) => {
        if (cancelled) return;
        const stableAddrs = new Set(stables.map((t) => t.address.toLowerCase()));
        const assetTokens = assetsToTokens(assets, chainId).filter(
          (t) => !stableAddrs.has(t.address.toLowerCase()),
        );
        setTokens([...stables, ...assetTokens]);
        setReady(true);
      })
      .catch((e: Error) => {
        if (cancelled) return;
        setTokens(stables);
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
