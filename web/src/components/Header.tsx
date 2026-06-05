import { useRef, useState } from "react";
import { useDynamicContext } from "@dynamic-labs/sdk-react-core";
import { useAccount, useChainId, useSwitchChain } from "wagmi";
import { CONTRACTS } from "../config/contracts";
import { SUPPORTED_CHAINS, chainName } from "../config/chains";
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

// Full address with the first/last four hex digits emphasized; clicking
// copies it to the clipboard.
function CopyAddress({ address }: { address: string }) {
  const [copied, setCopied] = useState(false);
  const timer = useRef<number | undefined>(undefined);
  const copy = async () => {
    await navigator.clipboard.writeText(address);
    setCopied(true);
    window.clearTimeout(timer.current);
    timer.current = window.setTimeout(() => setCopied(false), 1200);
  };
  return (
    <button className="wallet ok addr" onClick={copy} title="Copy address">
      <b>{address.slice(0, 6)}</b>
      {address.slice(6, -4)}
      <b>{address.slice(-4)}</b>
      <span className="copyMark">{copied ? "✓" : "⧉"}</span>
    </button>
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
  if (isConnected && address) {
    return (
      <>
        <CopyAddress address={address} />
        <button className="wallet" onClick={() => handleLogOut()} title={`${chainLabel} — disconnect`}>
          Disconnect
        </button>
      </>
    );
  }
  return (
    <button
      className="wallet"
      onClick={() => (loggedIn ? handleLogOut() : setShowAuthFlow(true))}
      title="Connect a wallet via Dynamic"
    >
      Connect
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
