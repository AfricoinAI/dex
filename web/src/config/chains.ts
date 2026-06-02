import { mainnet, base } from "viem/chains";
import type { Chain } from "viem";

export const SUPPORTED_CHAINS: readonly [Chain, ...Chain[]] = [mainnet, base];
