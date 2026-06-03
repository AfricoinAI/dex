import type { Address } from "viem";

export type ChainContracts = {
  factory: Address;
  router: Address;
  weth: Address;
  defillamaSlug: string;
};

// Deployed addresses from the root README "Deployments" table.
// TamaRouter is a deterministic CREATE2 deploy; addresses are mirrored
// across chains where it has been published.
export const CONTRACTS: Record<number, ChainContracts> = {
  // Ethereum
  1: {
    factory: "0x00000021543ed46B665A74484c82B71E4eB61e34",
    // TamaRouter address is identical across chains where deployed.
    // Fill in if/when the canonical router is published; until then the
    // factory address is the load-bearing one for pair discovery.
    router: "0x0000000000000000000000000000000000000000",
    weth: "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2",
    defillamaSlug: "ethereum",
  },
  // Base
  8453: {
    factory: "0x00000021543ed46B665A74484c82B71E4eB61e34",
    router: "0x0000000000000000000000000000000000000000",
    weth: "0x4200000000000000000000000000000000000006",
    defillamaSlug: "base",
  },
};

export const SUPPORTED_CHAIN_IDS = Object.keys(CONTRACTS).map(Number);

// On-ramp (Buy) destinations are stablecoins only: the user receives USDC or
// USDT. Per-chain token addresses; a missing entry disables that button on
// that chain.
export type StablecoinSymbol = "USDC" | "USDT";

export const ONRAMP_STABLECOINS: Record<number, Partial<Record<StablecoinSymbol, Address>>> = {
  // Ethereum
  1: {
    USDC: "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48",
    USDT: "0xdAC17F958D2ee523a2206206994597C13D831ec7",
  },
  // Base
  8453: {
    USDC: "0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913",
    // TODO: verify the Base USDT address before production use.
    USDT: "0xfde4C96c8593536E31F229EA8f37b2ADa2699bb2",
  },
};
