import { type ReactNode } from "react";
import { DynamicContextProvider, mergeNetworks } from "@dynamic-labs/sdk-react-core";
import { EthereumWalletConnectors } from "@dynamic-labs/ethereum";
import { DynamicWagmiConnector } from "@dynamic-labs/wagmi-connector";
import { QueryClient, QueryClientProvider } from "@tanstack/react-query";
import { WagmiProvider, createConfig, http } from "wagmi";
import { mainnet, sepolia } from "wagmi/chains";
import { ErrorBoundary } from "./components/ErrorBoundary";

const queryClient = new QueryClient();

// Explicit CORS-friendly RPC endpoints: viem's defaults (eth.merkle.io) block
// browser origins. PublicNode is keyless; an Alchemy key upgrades both chains
// when provided.
const ALCHEMY_KEY = import.meta.env.VITE_ALCHEMY_API_KEY ?? "";

const RPC_URLS: Record<number, string> = {
  [sepolia.id]: ALCHEMY_KEY
    ? `https://eth-sepolia.g.alchemy.com/v2/${ALCHEMY_KEY}`
    : "https://ethereum-sepolia-rpc.publicnode.com",
  [mainnet.id]: ALCHEMY_KEY
    ? `https://eth-mainnet.g.alchemy.com/v2/${ALCHEMY_KEY}`
    : "https://ethereum-rpc.publicnode.com",
};

// Sepolia first: it is wagmi's default chain while the platform is in test mode.
const wagmiConfig = createConfig({
  chains: [sepolia, mainnet],
  multiInjectedProviderDiscovery: false,
  transports: {
    [sepolia.id]: http(RPC_URLS[sepolia.id]),
    [mainnet.id]: http(RPC_URLS[mainnet.id]),
  },
});

const DYNAMIC_ENV_ID = import.meta.env.VITE_DYNAMIC_ENVIRONMENT_ID ?? "";

// Sepolia isn't enabled in the Dynamic dashboard's network list, so its
// connectors reject the chain with "EVM network not found". Injecting the
// network here keeps the app self-contained instead of dashboard-dependent.
const DYNAMIC_EVM_NETWORKS = [
  {
    blockExplorerUrls: ["https://sepolia.etherscan.io"],
    chainId: sepolia.id,
    chainName: "Sepolia",
    iconUrls: ["https://app.dynamic.xyz/assets/networks/eth.svg"],
    name: "Sepolia",
    nativeCurrency: { decimals: 18, name: "Sepolia Ether", symbol: "ETH" },
    networkId: sepolia.id,
    rpcUrls: [RPC_URLS[sepolia.id]],
    vanityName: "Sepolia",
  },
];

// Wagmi + react-query are pure local state; they don't depend on Dynamic and
// should always mount. If Dynamic's provider throws (bad env ID, network
// fetch failure, etc.) the wagmi tree underneath still renders, so the rest
// of the app stays usable — only the Connect button is non-functional.
function CoreProviders({ children }: { children: ReactNode }) {
  return (
    <WagmiProvider config={wagmiConfig}>
      <QueryClientProvider client={queryClient}>{children}</QueryClientProvider>
    </WagmiProvider>
  );
}

// Render this fallback when there is no Dynamic env ID. The Connect button
// reads `useDynamicContext()`; if that hook throws because no provider is
// mounted, an ErrorBoundary catches it locally and shows a small banner.
function WithoutDynamic({ children }: { children: ReactNode }) {
  // eslint-disable-next-line no-console
  console.warn(
    "VITE_DYNAMIC_ENVIRONMENT_ID is empty. Copy web/.env.example to web/.env and paste an ID from https://app.dynamic.xyz",
  );
  return <CoreProviders>{children}</CoreProviders>;
}

function WithDynamic({ children }: { children: ReactNode }) {
  return (
    <DynamicContextProvider
      settings={{
        environmentId: DYNAMIC_ENV_ID,
        walletConnectors: [EthereumWalletConnectors],
        overrides: {
          evmNetworks: (networks) => mergeNetworks(DYNAMIC_EVM_NETWORKS, networks),
        },
      }}
    >
      <CoreProviders>
        <DynamicWagmiConnector>{children}</DynamicWagmiConnector>
      </CoreProviders>
    </DynamicContextProvider>
  );
}

export function Providers({ children }: { children: ReactNode }) {
  return (
    <ErrorBoundary label="Wallet providers">
      {DYNAMIC_ENV_ID ? <WithDynamic>{children}</WithDynamic> : <WithoutDynamic>{children}</WithoutDynamic>}
    </ErrorBoundary>
  );
}
