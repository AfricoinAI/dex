import { useEffect, useMemo, useState } from "react";
import { useAccount, useChainId } from "wagmi";
import { peerExtensionSdk } from "@zkp2p/sdk";
import { CONTRACTS } from "../config/contracts";
import { useTokens } from "../lib/state";
import type { Token } from "../lib/tokenList";
import { short } from "../lib/format";
import { TokenPicker } from "./TokenPicker";

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
  const { tokens } = useTokens();

  const [state, setState] = useState<ExtensionState>("unknown");
  const [picker, setPicker] = useState(false);
  const [toToken, setToToken] = useState<Token | null>(null);
  const [platform, setPlatform] = useState<(typeof PAYMENT_PLATFORMS)[number]["value"]>("venmo");
  const [currency, setCurrency] = useState<(typeof CURRENCIES)[number]>("USD");
  const [amount, setAmount] = useState("25");
  const [recipient, setRecipient] = useState("");
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

  useEffect(() => {
    const off = peerExtensionSdk.onIntentFulfilled?.((result: { intentHash?: string; fulfillTxHash?: string }) => {
      setStatus(
        `Intent fulfilled: ${result.intentHash ? short(result.intentHash) : ""}${
          result.fulfillTxHash ? ` · tx ${short(result.fulfillTxHash)}` : ""
        }`,
      );
    });
    return () => {
      if (typeof off === "function") off();
    };
  }, []);

  // Default the destination token to a sensible one for the chain: native ETH first.
  useEffect(() => {
    if (!toToken && tokens.length > 0) setToToken(tokens[0]);
  }, [tokens, toToken]);

  const toTokenParam = useMemo(() => {
    if (!toToken || !cfg) return "";
    // Per peer.xyz: native asset is encoded with the zero address.
    const tokenAddress = toToken.native ? "0x0000000000000000000000000000000000000000" : toToken.address;
    return `${chainId}:${tokenAddress}`;
  }, [toToken, cfg, chainId]);

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
      if (!toTokenParam) throw new Error("Select a destination token");

      await peerExtensionSdk.onramp({
        referrer: "TamaSwap",
        referrerLogo: "https://swap.tama.tools/favicon.svg",
        inputCurrency: currency,
        inputAmount: amount,
        paymentPlatform: platform,
        toToken: toTokenParam,
        recipientAddress: recipient,
      });
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
        <span className="pill tiny">{cfg ? `Chain ${chainId}` : "Unsupported chain"}</span>
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
          <button
            className={toToken ? "tok" : "tok empty"}
            onClick={() => setPicker(true)}
            style={{ alignSelf: "start" }}
          >
            {toToken ? toToken.symbol : "Select token"}
          </button>
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
        disabled={busy || !cfg || !toToken || !recipient}
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

      <TokenPicker
        open={picker}
        tokens={tokens}
        onPick={setToToken}
        onClose={() => setPicker(false)}
      />
    </section>
  );
}
