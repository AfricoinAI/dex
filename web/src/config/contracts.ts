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
  // Sepolia (testnet) — the default chain while the platform is in test mode.
  // Same deterministic CREATE2 factory address; canonical Sepolia WETH.
  // DefiLlama carries no testnet prices, so the empty slug disables USD
  // estimates there.
  11155111: {
    factory: "0x00000021543ed46B665A74484c82B71E4eB61e34",
    // TamaRouter address is identical across chains where deployed.
    // Fill in if/when the canonical router is published; until then the
    // factory address is the load-bearing one for pair discovery.
    router: "0x0000000000000000000000000000000000000000",
    weth: "0xfFf9976782d46CC05630D1f6eBAb18b2324d6B14",
    defillamaSlug: "",
  },
  // Ethereum
  1: {
    factory: "0x00000021543ed46B665A74484c82B71E4eB61e34",
    router: "0x0000000000000000000000000000000000000000",
    weth: "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2",
    defillamaSlug: "ethereum",
  },
};

export const SUPPORTED_CHAIN_IDS = Object.keys(CONTRACTS).map(Number);

// Stablecoins are native tradeable tokens, independent of the gateway asset
// registry: they form the quote side of every africoin pair. All entries are
// the canonical issuer deployments (Circle / Tether); Tether publishes no
// official Sepolia USDT, so the testnet carries USDC only.
export type TradeableStablecoin = {
  symbol: string;
  name: string;
  address: Address;
  decimals: number;
};

export const TRADEABLE_STABLECOINS: Record<number, TradeableStablecoin[]> = {
  // Sepolia (Circle's official testnet USDC)
  11155111: [
    {
      symbol: "USDC",
      name: "USD Coin",
      address: "0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238",
      decimals: 6,
    },
  ],
  // Ethereum
  1: [
    {
      symbol: "USDC",
      name: "USD Coin",
      address: "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48",
      decimals: 6,
    },
    {
      symbol: "USDT",
      name: "Tether USD",
      address: "0xdAC17F958D2ee523a2206206994597C13D831ec7",
      decimals: 6,
    },
  ],
};

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
  // Sepolia has no on-ramp: no entry, so the Buy buttons stay disabled there.
};
