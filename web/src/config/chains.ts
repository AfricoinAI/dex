import { mainnet, sepolia } from "viem/chains";
import type { Chain } from "viem";

// Sepolia first: it is the default chain while the platform is in test mode.
export const SUPPORTED_CHAINS: readonly [Chain, ...Chain[]] = [sepolia, mainnet];

// Human-readable chain names, sourced from viem's canonical chain metadata
// (mainnet.name === "Ethereum", sepolia.name === "Sepolia").
const CHAIN_NAME: Record<number, string> = Object.fromEntries(
  SUPPORTED_CHAINS.map((c) => [c.id, c.name]),
);

export function chainName(chainId: number): string {
  return CHAIN_NAME[chainId] ?? `Chain ${chainId}`;
}
