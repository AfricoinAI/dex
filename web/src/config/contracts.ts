import type { Address } from "viem";

export type ChainContracts = {
  factory: Address;
  router: Address;
  weth: Address;
  defillamaSlug: string;
  // Endpoint that returns the tradeable token set for this chain. This is the
  // ONLY source of tradeable tokens — there is no default list and no
  // auto-injected ETH/WETH. Leave empty until the Tama token API is live; an
  // empty value surfaces an explicit "not configured" state in the UI.
  tokenListApiUrl: string;
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
    // TODO(token-api): set to the live Tama token API endpoint for Ethereum.
    tokenListApiUrl: "",
  },
  // Base
  8453: {
    factory: "0x00000021543ed46B665A74484c82B71E4eB61e34",
    router: "0x0000000000000000000000000000000000000000",
    weth: "0x4200000000000000000000000000000000000006",
    defillamaSlug: "base",
    // TODO(token-api): set to the live Tama token API endpoint for Base.
    tokenListApiUrl: "",
  },
};

export const SUPPORTED_CHAIN_IDS = Object.keys(CONTRACTS).map(Number);
