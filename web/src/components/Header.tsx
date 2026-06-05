import { useDynamicContext } from "@dynamic-labs/sdk-react-core";
import { useAccount, useChainId, useSwitchChain } from "wagmi";
import { CONTRACTS } from "../config/contracts";
import { SUPPORTED_CHAINS, chainName } from "../config/chains";
import { short } from "../lib/format";
import { ErrorBoundary } from "./ErrorBoundary";

type Tab = "swap" | "pool" | "buy";

// Segmented control over the configured chains. When a wallet is connected,
// wagmi asks it to switch (and to add the chain if missing); when not,
// wagmi just repoints its own active chain, so browsing works either way.
function ChainSwitcher() {
  const chainId = useChainId();
  const { switchChain, isPending } = useSwitchChain();
  return (
    <div className="nav chains">
      {SUPPORTED_CHAINS.map((c) => (
        <button
          key={c.id}
          className={chainId === c.id ? "on" : ""}
          disabled={isPending}
          onClick={() => switchChain({ chainId: c.id })}
          title={`Switch to ${c.name}`}
        >
          {c.name}
        </button>
      ))}
    </div>
  );
}

// Split out so a Dynamic provider crash only takes down the wallet button,
// not the whole header. The boundary below falls back to a disabled pill.
function ConnectButton() {
  const { setShowAuthFlow, handleLogOut, user } = useDynamicContext();
  const { address, isConnected } = useAccount();
  const chainId = useChainId();
  const chainLabel = chainId in CONTRACTS ? chainName(chainId) : "Unsupported chain";
  const loggedIn = isConnected || !!user;
  return (
    <button
      className={isConnected ? "wallet ok" : "wallet"}
      onClick={() => (loggedIn ? handleLogOut() : setShowAuthFlow(true))}
      title={isConnected ? chainLabel : "Connect a wallet via Dynamic"}
    >
      {isConnected && address ? short(address) : "Connect"}
    </button>
  );
}

export function Header({ tab, setTab }: { tab: Tab; setTab: (t: Tab) => void }) {
  return (
    <div className="top">
      <div className="brand">
        <img className="brandLogo" src="/logo-header.png" alt="Africoin" />
      </div>
      <div className="nav">
        <button className={tab === "swap" ? "on" : ""} onClick={() => setTab("swap")}>
          Swap
        </button>
        <button className={tab === "pool" ? "on" : ""} onClick={() => setTab("pool")}>
          Pool
        </button>
        <button className={tab === "buy" ? "on" : ""} onClick={() => setTab("buy")}>
          Buy
        </button>
      </div>
      <div className="walletGroup">
        <ChainSwitcher />
        <ErrorBoundary
          label="ConnectButton"
          fallback={(error) => (
            <button
              className="wallet"
              disabled
              title={`Wallet unavailable: ${error.message}`}
              style={{ opacity: 0.6, cursor: "not-allowed" }}
            >
              Wallet unavailable
            </button>
          )}
        >
          <ConnectButton />
        </ErrorBoundary>
      </div>
    </div>
  );
}
