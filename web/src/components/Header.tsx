import { useDynamicContext } from "@dynamic-labs/sdk-react-core";
import { useAccount, useChainId } from "wagmi";
import { CONTRACTS } from "../config/contracts";
import { short } from "../lib/format";
import { ErrorBoundary } from "./ErrorBoundary";

type Tab = "swap" | "pool" | "buy";

const CHAIN_LABEL: Record<number, string> = {
  1: "Ethereum",
  8453: "Base",
};

// Split out so a Dynamic provider crash only takes down the wallet button,
// not the whole header. The boundary below falls back to a disabled pill.
function ConnectButton() {
  const { setShowAuthFlow, handleLogOut, user } = useDynamicContext();
  const { address, isConnected } = useAccount();
  const chainId = useChainId();
  const chainLabel = chainId in CONTRACTS ? CHAIN_LABEL[chainId] ?? `Chain ${chainId}` : "Unsupported chain";
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
        <div className="mark">玉</div>
        <span>TamaSwap</span>
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
  );
}
