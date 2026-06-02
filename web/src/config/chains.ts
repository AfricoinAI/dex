import { mainnet, base } from "viem/chains";
import type { Chain } from "viem";

export const SUPPORTED_CHAINS: readonly [Chain, ...Chain[]] = [mainnet, base];

// Human-readable chain names, sourced from viem's canonical chain metadata
// (mainnet.name === "Ethereum", base.name === "Base").
const CHAIN_NAME: Record<number, string> = Object.fromEntries(
  SUPPORTED_CHAINS.map((c) => [c.id, c.name]),
);

export function chainName(chainId: number): string {
  return CHAIN_NAME[chainId] ?? `Chain ${chainId}`;
}
