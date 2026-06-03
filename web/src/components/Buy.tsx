import { useEffect, useMemo, useState } from "react";
import { useAccount, useChainId } from "wagmi";
import {
  peerExtensionSdk,
  type PeerExtensionOnrampParams,
  type PeerOnrampPreparedTransactionCallback,
} from "@zkp2p/sdk";
import { CONTRACTS, ONRAMP_STABLECOINS, type StablecoinSymbol } from "../config/contracts";
import { chainName } from "../config/chains";
import { short } from "../lib/format";

const RECEIVE_OPTIONS: readonly StablecoinSymbol[] = ["USDC", "USDT"];

// peer.xyz redirect-onramp surface, per
// https://docs.peer.xyz/developer/integrate-zkp2p/integrate-redirect-onramp
type ExtensionState = "ready" | "needs_install" | "needs_connection" | "unknown";

const PAYMENT_PLATFORMS = [
  { value: "venmo", label: "Venmo (USD)" },
  { value: "revolut", label: "Revolut (EUR)" },
  { value: "wise", label: "Wise (USD/EUR)" },
  { value: "cashapp", label: "Cash App (USD)" },
] as const;

const CURRENCIES = ["USD", "EUR", "GBP", "INR"] as const;

export function Buy() {
  const chainId = useChainId();
  const cfg = CONTRACTS[chainId];
  const { address } = useAccount();

  const stables = ONRAMP_STABLECOINS[chainId] ?? {};
  const [state, setState] = useState<ExtensionState>("unknown");
  const [receive, setReceive] = useState<StablecoinSymbol>("USDC");
  const selectedAddress = stables[receive];
  const [platform, setPlatform] = useState<(typeof PAYMENT_PLATFORMS)[number]["value"]>("venmo");
  const [currency, setCurrency] = useState<(typeof CURRENCIES)[number]>("USD");
  const [amount, setAmount] = useState("25");
  const [recipient, setRecipient] = useState("");
  // Set once the quote → signalIntent flow is wired; required by the on-ramp.
  const [intentHash] = useState("");
  const [busy, setBusy] = useState(false);
  const [status, setStatus] = useState<string | null>(null);
  const [errMsg, setErrMsg] = useState<string | null>(null);

  useEffect(() => {
    setRecipient(address ?? "");
  }, [address]);

  useEffect(() => {
    let cancelled = false;
    (async () => {
      try {
        const s = (await peerExtensionSdk.getState()) as ExtensionState;
        if (!cancelled) setState(s);
      } catch {
        if (!cancelled) setState("unknown");
      }
    })();
    return () => {
      cancelled = true;
    };
  }, []);

  // The Peer extension prepares the on-ramp transaction and delivers it here as
  // `calldata_ready`. A full integration then submits `result.transaction` with
  // the connected wallet; for now we surface the prepared intent to the user.
  const onPreparedTransaction: PeerOnrampPreparedTransactionCallback = (result) => {
    setStatus(
      `On-ramp intent ${short(result.intentHash)} is ${result.status} — submit the ` +
        `returned transaction on chain ${result.transaction.chainId}.`,
    );
  };

  const toTokenParam = useMemo(() => {
    if (!cfg || !selectedAddress) return "";
    return `${chainId}:${selectedAddress}`;
  }, [cfg, chainId, selectedAddress]);

  async function buy() {
    setBusy(true);
    setErrMsg(null);
    setStatus(null);
    try {
      let current = state;
      if (current === "unknown") {
        try {
          current = (await peerExtensionSdk.getState()) as ExtensionState;
          setState(current);
        } catch {
          throw new Error("Peer extension is unavailable in this browser");
        }
      }
      if (current === "needs_install") {
        peerExtensionSdk.openInstallPage();
        setStatus("Install the Peer extension, then click Buy again.");
        return;
      }
      if (current === "needs_connection") {
        await peerExtensionSdk.requestConnection();
      }
      if (!recipient) throw new Error("Recipient address is required");
      if (!toTokenParam) throw new Error(`${receive} is not available on this chain`);
      // zkp2p binds an on-ramp to an on-chain intent: `intentHash` is required
      // and comes from a prior quote → signalIntent step (Zkp2pClient) that this
      // screen does not perform yet. Surface that clearly instead of failing
      // inside the SDK.
      if (!intentHash) {
        throw new Error(
          "On-ramp intent not signed yet — the quote/signalIntent step that produces an intentHash is not wired in this build.",
        );
      }

      const params: PeerExtensionOnrampParams = {
        intentHash,
        referrer: "Africoin",
        referrerLogo: `${window.location.origin}/favicon.png`,
        inputCurrency: currency,
        inputAmount: amount,
        paymentPlatform: platform,
        toToken: toTokenParam,
        recipientAddress: recipient,
      };
      peerExtensionSdk.onramp(params, onPreparedTransaction);
      setStatus("Onramp opened in the Peer side-panel. Complete the payment to release funds.");
    } catch (e) {
      setErrMsg(e instanceof Error ? e.message : "Onramp failed");
    } finally {
      setBusy(false);
    }
  }

  return (
    <section className="card">
      <div className="head">
        <div className="title">Buy</div>
        <span className="pill tiny">{cfg ? chainName(chainId) : "Unsupported chain"}</span>
      </div>

      <div className="box">
        <div className="field">
          <label>You pay</label>
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 8 }}>
            <input
              type="text"
              inputMode="decimal"
              value={amount}
              onChange={(e) => setAmount(e.target.value)}
              placeholder="25"
            />
            <select value={currency} onChange={(e) => setCurrency(e.target.value as (typeof CURRENCIES)[number])}>
              {CURRENCIES.map((c) => (
                <option key={c} value={c}>
                  {c}
                </option>
              ))}
            </select>
          </div>
        </div>
        <div className="field">
          <label>Payment platform</label>
          <select value={platform} onChange={(e) => setPlatform(e.target.value as (typeof PAYMENT_PLATFORMS)[number]["value"])}>
            {PAYMENT_PLATFORMS.map((p) => (
              <option key={p.value} value={p.value}>
                {p.label}
              </option>
            ))}
          </select>
        </div>
      </div>

      <div className="box">
        <div className="field">
          <label>You receive</label>
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 8 }}>
            {RECEIVE_OPTIONS.map((sym) => {
              const available = Boolean(stables[sym]);
              return (
                <button
                  key={sym}
                  className={receive === sym ? "tok selected" : "tok"}
                  disabled={!available}
                  onClick={() => setReceive(sym)}
                  style={{ justifyContent: "center", opacity: available ? 1 : 0.5 }}
                >
                  {sym}
                </button>
              );
            })}
          </div>
        </div>
        <div className="field">
          <label>Recipient address</label>
          <input
            type="text"
            value={recipient}
            onChange={(e) => setRecipient(e.target.value)}
            placeholder="0x…"
          />
        </div>
      </div>

      <button
        className="cta"
        disabled={busy || !cfg || !selectedAddress || !recipient}
        onClick={buy}
      >
        {busy
          ? "Opening side-panel…"
          : state === "needs_install"
            ? "Install Peer extension"
            : "Buy"}
      </button>

      <div className={errMsg ? "status err" : "status"}>
        {errMsg ?? status ?? "Powered by the Peer browser extension. Each on-ramp uses a zkTLS proof of a real fiat transfer to release crypto."}
      </div>
    </section>
  );
}
