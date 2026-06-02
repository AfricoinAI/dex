import { useEffect, useMemo, useState } from "react";
import { useAccount, useChainId, usePublicClient, useWalletClient } from "wagmi";
import { type Address, formatUnits, maxUint256 } from "viem";
import { CONTRACTS } from "../config/contracts";
import { erc20Abi, routerAbi, wethAbi } from "../lib/abi";
import { deadline, fmtAmt, fmtFull, maxWithSlip, minWithSlip, money, parseAmt, short } from "../lib/format";
import { fetchUsdPrice } from "../lib/prices";
import { useSlippageBps, useTokens } from "../lib/state";
import type { Token } from "../lib/tokenList";
import { TokenPicker } from "./TokenPicker";
import { SettingsModal } from "./SettingsModal";

type Quote = { amountIn: bigint; amountOut: bigint };
type Mode = "swap" | "wrap" | "unwrap";

export function Swap() {
  const chainId = useChainId();
  const cfg = CONTRACTS[chainId];
  const { address } = useAccount();
  const publicClient = usePublicClient();
  const { data: walletClient } = useWalletClient();
  const { tokens, ready, error: tokenError } = useTokens();
  const slipBps = useSlippageBps();

  const [tokenIn, setTokenIn] = useState<Token | null>(null);
  const [tokenOut, setTokenOut] = useState<Token | null>(null);
  const [amountInStr, setAmountInStr] = useState("");
  const [quote, setQuote] = useState<Quote | null>(null);
  const [quoteError, setQuoteError] = useState<string | null>(null);
  const [busy, setBusy] = useState(false);
  const [status, setStatus] = useState<{ text: string; href?: string } | null>(null);
  const [errMsg, setErrMsg] = useState<string | null>(null);
  const [picker, setPicker] = useState<"in" | "out" | null>(null);
  const [settingsOpen, setSettingsOpen] = useState(false);
  const [balanceIn, setBalanceIn] = useState<bigint | null>(null);
  const [balanceOut, setBalanceOut] = useState<bigint | null>(null);
  const [allowance, setAllowance] = useState<bigint | null>(null);
  const [usdIn, setUsdIn] = useState<number | null>(null);
  const [usdOut, setUsdOut] = useState<number | null>(null);

  // Seed token-in to native once the token list arrives, so the form is usable.
  useEffect(() => {
    if (ready && !tokenIn && tokens.length > 0) setTokenIn(tokens[0]);
  }, [ready, tokens, tokenIn]);

  // Reset selections on chain change so we don't reuse cross-chain addresses.
  useEffect(() => {
    setTokenIn(null);
    setTokenOut(null);
    setQuote(null);
    setStatus(null);
    setErrMsg(null);
  }, [chainId]);

  const mode: Mode | null = useMemo(() => {
    if (!tokenIn || !tokenOut || !cfg) return null;
    const sameAddr = tokenIn.address.toLowerCase() === tokenOut.address.toLowerCase();
    if (sameAddr && tokenIn.native && !tokenOut.native) return "wrap";
    if (sameAddr && !tokenIn.native && tokenOut.native) return "unwrap";
    if (sameAddr) return null;
    return "swap";
  }, [tokenIn, tokenOut, cfg]);

  // Refresh balances + allowance whenever the inputs change.
  useEffect(() => {
    if (!publicClient || !address || !tokenIn) {
      setBalanceIn(null);
      setAllowance(null);
      return;
    }
    let cancelled = false;
    (async () => {
      try {
        if (tokenIn.native) {
          const bal = await publicClient.getBalance({ address });
          if (!cancelled) setBalanceIn(bal);
          if (!cancelled) setAllowance(maxUint256);
        } else {
          const [bal, all] = await Promise.all([
            publicClient.readContract({ abi: erc20Abi, address: tokenIn.address, functionName: "balanceOf", args: [address] }),
            cfg ? publicClient.readContract({ abi: erc20Abi, address: tokenIn.address, functionName: "allowance", args: [address, cfg.router] }) : Promise.resolve(0n),
          ]);
          if (!cancelled) {
            setBalanceIn(bal);
            setAllowance(all);
          }
        }
      } catch {
        if (!cancelled) {
          setBalanceIn(null);
          setAllowance(null);
        }
      }
    })();
    return () => {
      cancelled = true;
    };
  }, [publicClient, address, tokenIn, cfg, status]);

  useEffect(() => {
    if (!publicClient || !address || !tokenOut) {
      setBalanceOut(null);
      return;
    }
    let cancelled = false;
    (async () => {
      try {
        const bal = tokenOut.native
          ? await publicClient.getBalance({ address })
          : await publicClient.readContract({ abi: erc20Abi, address: tokenOut.address, functionName: "balanceOf", args: [address] });
        if (!cancelled) setBalanceOut(bal);
      } catch {
        if (!cancelled) setBalanceOut(null);
      }
    })();
    return () => {
      cancelled = true;
    };
  }, [publicClient, address, tokenOut, status]);

  // USD pricing via DeFiLlama for both sides.
  useEffect(() => {
    let cancelled = false;
    if (!cfg) return;
    (async () => {
      const [pIn, pOut] = await Promise.all([
        tokenIn ? fetchUsdPrice(cfg.defillamaSlug, tokenIn.address) : Promise.resolve(null),
        tokenOut ? fetchUsdPrice(cfg.defillamaSlug, tokenOut.address) : Promise.resolve(null),
      ]);
      if (cancelled) return;
      setUsdIn(pIn);
      setUsdOut(pOut);
    })();
    return () => {
      cancelled = true;
    };
  }, [cfg, tokenIn, tokenOut]);

  // Quote whenever the input amount or selection changes.
  useEffect(() => {
    if (!publicClient || !cfg || !tokenIn || !tokenOut || !amountInStr || mode === null) {
      setQuote(null);
      setQuoteError(null);
      return;
    }
    let cancelled = false;
    (async () => {
      try {
        const amountIn = parseAmt(amountInStr, tokenIn.decimals);
        if (amountIn === 0n) {
          setQuote(null);
          setQuoteError(null);
          return;
        }
        if (mode === "wrap" || mode === "unwrap") {
          if (!cancelled) {
            setQuote({ amountIn, amountOut: amountIn });
            setQuoteError(null);
          }
          return;
        }
        const path = [
          tokenIn.native ? cfg.weth : tokenIn.address,
          tokenOut.native ? cfg.weth : tokenOut.address,
        ];
        const amounts = (await publicClient.readContract({
          abi: routerAbi,
          address: cfg.router,
          functionName: "getAmountsOut",
          args: [amountIn, path],
        })) as readonly bigint[];
        if (cancelled) return;
        setQuote({ amountIn, amountOut: amounts[amounts.length - 1] });
        setQuoteError(null);
      } catch (e) {
        if (cancelled) return;
        setQuote(null);
        setQuoteError(e instanceof Error ? e.message : "Quote failed");
      }
    })();
    return () => {
      cancelled = true;
    };
  }, [publicClient, cfg, tokenIn, tokenOut, amountInStr, mode]);

  const minOut = quote ? minWithSlip(quote.amountOut, slipBps) : null;
  const maxIn = quote ? maxWithSlip(quote.amountIn, slipBps) : null;
  void maxIn;

  const needsApproval = !!(
    tokenIn &&
    !tokenIn.native &&
    quote &&
    allowance != null &&
    allowance < quote.amountIn
  );

  const insufficient = balanceIn != null && quote != null && balanceIn < quote.amountIn;

  const canSwap =
    !!cfg &&
    !!tokenIn &&
    !!tokenOut &&
    !!quote &&
    !!address &&
    !!walletClient &&
    !needsApproval &&
    !insufficient &&
    mode !== null;

  const ctaLabel = (() => {
    if (!address) return "Connect wallet";
    if (!cfg) return "Unsupported chain";
    if (!tokenIn || !tokenOut) return "Select tokens";
    if (mode === null) return "Select different tokens";
    if (!amountInStr || quote?.amountIn === 0n) return "Enter an amount";
    if (quoteError) return "No route";
    if (insufficient) return `Insufficient ${tokenIn.symbol}`;
    if (needsApproval) return `Approve ${tokenIn.symbol}`;
    if (mode === "wrap") return "Wrap";
    if (mode === "unwrap") return "Unwrap";
    return "Swap";
  })();

  async function approve() {
    if (!walletClient || !cfg || !tokenIn || !quote || tokenIn.native) return;
    setBusy(true);
    setErrMsg(null);
    try {
      const hash = await walletClient.writeContract({
        abi: erc20Abi,
        address: tokenIn.address,
        functionName: "approve",
        args: [cfg.router, quote.amountIn],
      });
      setStatus({ text: `Approval submitted ${short(hash)}` });
      await publicClient!.waitForTransactionReceipt({ hash });
      setStatus({ text: `Approval confirmed` });
    } catch (e) {
      setErrMsg(e instanceof Error ? e.message : "Approval failed");
    } finally {
      setBusy(false);
    }
  }

  async function execute() {
    if (!walletClient || !cfg || !tokenIn || !tokenOut || !quote || !address) return;
    setBusy(true);
    setErrMsg(null);
    setStatus(null);
    try {
      let hash: `0x${string}`;
      if (mode === "wrap") {
        hash = await walletClient.writeContract({
          abi: wethAbi,
          address: cfg.weth,
          functionName: "deposit",
          value: quote.amountIn,
        });
      } else if (mode === "unwrap") {
        hash = await walletClient.writeContract({
          abi: wethAbi,
          address: cfg.weth,
          functionName: "withdraw",
          args: [quote.amountIn],
        });
      } else {
        const dl = deadline();
        const min = minWithSlip(quote.amountOut, slipBps);
        const path: Address[] = [
          tokenIn.native ? cfg.weth : tokenIn.address,
          tokenOut.native ? cfg.weth : tokenOut.address,
        ];
        if (tokenIn.native) {
          hash = await walletClient.writeContract({
            abi: routerAbi,
            address: cfg.router,
            functionName: "swapExactETHForTokens",
            args: [min, path, address, dl],
            value: quote.amountIn,
          });
        } else if (tokenOut.native) {
          hash = await walletClient.writeContract({
            abi: routerAbi,
            address: cfg.router,
            functionName: "swapExactTokensForETH",
            args: [quote.amountIn, min, path, address, dl],
          });
        } else {
          hash = await walletClient.writeContract({
            abi: routerAbi,
            address: cfg.router,
            functionName: "swapExactTokensForTokens",
            args: [quote.amountIn, min, path, address, dl],
          });
        }
      }
      setStatus({ text: `Submitted ${short(hash)}` });
      await publicClient!.waitForTransactionReceipt({ hash });
      setStatus({ text: `Confirmed ${short(hash)}` });
      setAmountInStr("");
    } catch (e) {
      setErrMsg(e instanceof Error ? e.message : "Swap failed");
    } finally {
      setBusy(false);
    }
  }

  function setMaxInput() {
    if (balanceIn == null || !tokenIn) return;
    const value = tokenIn.native ? (balanceIn > 10n ** 16n ? balanceIn - 10n ** 16n : 0n) : balanceIn;
    setAmountInStr(fmtFull(value, tokenIn.decimals));
  }

  return (
    <section className="card">
      <div className="head">
        <div className="title">Swap</div>
        <div>
          <span className="pill tiny">{cfg ? `Chain ${chainId}` : "Unsupported chain"}</span>{" "}
          <button className="gear" onClick={() => setSettingsOpen(true)}>
            Settings
          </button>
        </div>
      </div>

      <div className="box">
        <div className="lbl">
          <span>You pay</span>
          {tokenIn && balanceIn != null && (
            <span className="bal click" onClick={setMaxInput}>
              Balance: {fmtAmt(balanceIn, tokenIn.decimals)} {tokenIn.symbol}
            </span>
          )}
        </div>
        <div className="amount">
          <input
            inputMode="decimal"
            placeholder="0"
            value={amountInStr}
            onChange={(e) => setAmountInStr(e.target.value)}
          />
          <button
            className={tokenIn ? "tok" : "tok empty"}
            onClick={() => setPicker("in")}
          >
            {tokenIn ? (
              <>
                <span className="logo">
                  {tokenIn.logoURI ? <img src={tokenIn.logoURI} alt="" /> : tokenIn.symbol.slice(0, 2)}
                </span>
                <span>{tokenIn.symbol}</span>
              </>
            ) : (
              "Select token"
            )}
          </button>
        </div>
        <div className="usd">
          {usdIn != null && quote ? `≈ ${money(usdIn * Number(formatUnits(quote.amountIn, tokenIn?.decimals ?? 18)))}` : ""}
        </div>
      </div>

      <div className="flip">
        <button
          onClick={() => {
            const a = tokenIn;
            const b = tokenOut;
            setTokenIn(b);
            setTokenOut(a);
            setAmountInStr("");
            setQuote(null);
          }}
        >
          ↕
        </button>
      </div>

      <div className="box">
        <div className="lbl">
          <span>You receive</span>
          {tokenOut && balanceOut != null && (
            <span className="bal">Balance: {fmtAmt(balanceOut, tokenOut.decimals)} {tokenOut.symbol}</span>
          )}
        </div>
        <div className="amount">
          <input
            readOnly
            placeholder="0"
            value={quote && tokenOut ? fmtFull(quote.amountOut, tokenOut.decimals) : ""}
          />
          <button
            className={tokenOut ? "tok" : "tok empty"}
            onClick={() => setPicker("out")}
          >
            {tokenOut ? (
              <>
                <span className="logo">
                  {tokenOut.logoURI ? <img src={tokenOut.logoURI} alt="" /> : tokenOut.symbol.slice(0, 2)}
                </span>
                <span>{tokenOut.symbol}</span>
              </>
            ) : (
              "Select token"
            )}
          </button>
        </div>
        <div className="usd">
          {usdOut != null && quote && tokenOut
            ? `≈ ${money(usdOut * Number(formatUnits(quote.amountOut, tokenOut.decimals)))}`
            : ""}
        </div>
      </div>

      {quote && tokenOut && minOut != null && mode === "swap" && (
        <div className="review">
          <div>
            <span className="muted">Minimum received</span>
            <b>{fmtAmt(minOut, tokenOut.decimals)} {tokenOut.symbol}</b>
          </div>
          <div>
            <span className="muted">Slippage</span>
            <span>{(Number(slipBps) / 100).toFixed(2)}%</span>
          </div>
        </div>
      )}

      <button
        className="cta"
        disabled={busy || (!needsApproval && !canSwap)}
        onClick={needsApproval ? approve : execute}
      >
        {busy ? "Submitting…" : ctaLabel}
      </button>

      <div className={errMsg ? "status err" : "status"}>
        {errMsg ?? status?.text ?? (tokenError ?? quoteError ?? "")}
      </div>

      <TokenPicker
        open={picker !== null}
        tokens={tokens}
        exclude={picker === "in" ? tokenOut : tokenIn}
        onPick={(t) => {
          if (picker === "in") setTokenIn(t);
          else setTokenOut(t);
        }}
        onClose={() => setPicker(null)}
      />
      <SettingsModal open={settingsOpen} onClose={() => setSettingsOpen(false)} />
    </section>
  );
}
