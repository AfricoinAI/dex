import { type ReactNode } from "react";
import { DynamicContextProvider } from "@dynamic-labs/sdk-react-core";
import { EthereumWalletConnectors } from "@dynamic-labs/ethereum";
import { DynamicWagmiConnector } from "@dynamic-labs/wagmi-connector";
import { QueryClient, QueryClientProvider } from "@tanstack/react-query";
import { WagmiProvider, createConfig, http } from "wagmi";
import { mainnet, base, sepolia } from "wagmi/chains";
import { ErrorBoundary } from "./components/ErrorBoundary";

const queryClient = new QueryClient();

const wagmiConfig = createConfig({
  chains: [mainnet, base, sepolia],
  multiInjectedProviderDiscovery: false,
  transports: {
    [mainnet.id]: http(),
    [base.id]: http(),
    [sepolia.id]: http(),
  },
});

const DYNAMIC_ENV_ID = import.meta.env.VITE_DYNAMIC_ENVIRONMENT_ID ?? "";

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
