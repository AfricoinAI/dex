import { useEffect, useMemo, useState } from "react";
import { useAccount, useChainId, usePublicClient, useWalletClient } from "wagmi";
import { type Address, formatUnits, maxUint256 } from "viem";
import { CONTRACTS, routerDeployed } from "../config/contracts";
import { chainName } from "../config/chains";
import { erc20Abi, routerAbi, wethAbi } from "../lib/abi";
import { deadline, fmtAmt, fmtFull, maxWithSlip, minWithSlip, money, parseAmt, short } from "../lib/format";
import { fetchUsdPrice } from "../lib/prices";
import { useSlippageBps, useTokens } from "../lib/state";
import type { Token } from "../lib/tokenList";
import { TokenPicker } from "./TokenPicker";
import { SettingsModal } from "./SettingsModal";

// `exact` records which side the user fixed; the other side is quoted and the
// swap executes with the matching exact-in/exact-out router function.
type Quote = { amountIn: bigint; amountOut: bigint; exact: "in" | "out" };
type Mode = "swap" | "wrap" | "unwrap";

export function Swap() {
  const chainId = useChainId();
  const cfg = CONTRACTS[chainId];
  const { address } = useAccount();
  const publicClient = usePublicClient();
  const { data: walletClient, error: walletClientError } = useWalletClient();
  const { tokens, ready, error: tokenError } = useTokens();
  const slipBps = useSlippageBps();

  const [tokenIn, setTokenIn] = useState<Token | null>(null);
  const [tokenOut, setTokenOut] = useState<Token | null>(null);
  const [amountInStr, setAmountInStr] = useState("");
  const [amountOutStr, setAmountOutStr] = useState("");
  const [exact, setExact] = useState<"in" | "out">("in");
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

  // Seed the form once the token list arrives: pay with the first stablecoin,
  // receive the first africoin asset.
  useEffect(() => {
    if (!ready || tokenIn || tokens.length === 0) return;
    setTokenIn(tokens[0]);
    const firstAsset = tokens.find((t) => !t.stablecoin);
    if (firstAsset && !tokenOut) setTokenOut(firstAsset);
  }, [ready, tokens, tokenIn, tokenOut]);

  // Reset selections on chain change so we don't reuse cross-chain addresses.
  useEffect(() => {
    setTokenIn(null);
    setTokenOut(null);
    setAmountInStr("");
    setAmountOutStr("");
    setExact("in");
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

  // Quote whenever the fixed-side amount or selection changes: exact-in
  // quotes the output via getAmountsOut, exact-out quotes the required input
  // via getAmountsIn.
  useEffect(() => {
    const editedStr = exact === "in" ? amountInStr : amountOutStr;
    if (!publicClient || !cfg || !tokenIn || !tokenOut || !editedStr || mode === null) {
      setQuote(null);
      setQuoteError(null);
      return;
    }
    let cancelled = false;
    (async () => {
      try {
        const editedToken = exact === "in" ? tokenIn : tokenOut;
        const amount = parseAmt(editedStr, editedToken.decimals);
        if (amount === 0n) {
          setQuote(null);
          setQuoteError(null);
          return;
        }
        if (mode === "wrap" || mode === "unwrap") {
          if (!cancelled) {
            setQuote({ amountIn: amount, amountOut: amount, exact });
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
          functionName: exact === "in" ? "getAmountsOut" : "getAmountsIn",
          args: [amount, path],
        })) as readonly bigint[];
        if (cancelled) return;
        setQuote(
          exact === "in"
            ? { amountIn: amount, amountOut: amounts[amounts.length - 1], exact }
            : { amountIn: amounts[0], amountOut: amount, exact },
        );
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
  }, [publicClient, cfg, tokenIn, tokenOut, amountInStr, amountOutStr, exact, mode]);

  const minOut = quote ? minWithSlip(quote.amountOut, slipBps) : null;
  const maxIn = quote ? maxWithSlip(quote.amountIn, slipBps) : null;
  // Exact-out swaps may pull up to maxIn; approvals and balance checks must
  // cover that ceiling, not the quoted midpoint.
  const requiredIn = quote ? (quote.exact === "out" ? maxIn! : quote.amountIn) : null;

  const needsApproval = !!(
    routerDeployed(cfg) &&
    tokenIn &&
    !tokenIn.native &&
    requiredIn != null &&
    allowance != null &&
    allowance < requiredIn
  );

  const insufficient = balanceIn != null && requiredIn != null && balanceIn < requiredIn;

  const canSwap =
    routerDeployed(cfg) &&
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
    if (!routerDeployed(cfg)) return "Trading not live on this chain yet";
    if (!tokenIn || !tokenOut) return "Select tokens";
    if (mode === null) return "Select different tokens";
    if (!(exact === "in" ? amountInStr : amountOutStr) || quote?.amountIn === 0n) return "Enter an amount";
    if (quoteError) return "No route";
    if (insufficient) return `Insufficient ${tokenIn.symbol}`;
    if (needsApproval) return `Approve ${tokenIn.symbol}`;
    if (mode === "wrap") return "Wrap";
    if (mode === "unwrap") return "Unwrap";
    return "Swap";
  })();

  async function approve() {
    if (!cfg || !tokenIn || !quote || tokenIn.native) return;
    if (!walletClient) {
      setErrMsg(
        walletClientError
          ? `Wallet client unavailable: ${walletClientError.message}`
          : "Wallet client not ready — reconnect the wallet and try again.",
      );
      return;
    }
    setBusy(true);
    setErrMsg(null);
    try {
      const hash = await walletClient.writeContract({
        abi: erc20Abi,
        address: tokenIn.address,
        functionName: "approve",
        args: [cfg.router, quote.exact === "out" ? maxWithSlip(quote.amountIn, slipBps) : quote.amountIn],
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
    if (!cfg || !tokenIn || !tokenOut || !quote || !address) return;
    if (!walletClient) {
      setErrMsg(
        walletClientError
          ? `Wallet client unavailable: ${walletClientError.message}`
          : "Wallet client not ready — reconnect the wallet and try again.",
      );
      return;
    }
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
      } else if (quote.exact === "in") {
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
      } else {
        // Exact-out: the user fixed the receive amount; the router pulls at
        // most maxWithSlip(amountIn) and refunds any unspent native value.
        const dl = deadline();
        const max = maxWithSlip(quote.amountIn, slipBps);
        const path: Address[] = [
          tokenIn.native ? cfg.weth : tokenIn.address,
          tokenOut.native ? cfg.weth : tokenOut.address,
        ];
        if (tokenIn.native) {
          hash = await walletClient.writeContract({
            abi: routerAbi,
            address: cfg.router,
            functionName: "swapETHForExactTokens",
            args: [quote.amountOut, path, address, dl],
            value: max,
          });
        } else if (tokenOut.native) {
          hash = await walletClient.writeContract({
            abi: routerAbi,
            address: cfg.router,
            functionName: "swapTokensForExactETH",
            args: [quote.amountOut, max, path, address, dl],
          });
        } else {
          hash = await walletClient.writeContract({
            abi: routerAbi,
            address: cfg.router,
            functionName: "swapTokensForExactTokens",
            args: [quote.amountOut, max, path, address, dl],
          });
        }
      }
      setStatus({ text: `Submitted ${short(hash)}` });
      await publicClient!.waitForTransactionReceipt({ hash });
      setStatus({ text: `Confirmed ${short(hash)}` });
      setAmountInStr("");
      setAmountOutStr("");
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
    setExact("in");
  }

  return (
    <section className="card">
      <div className="head">
        <div className="title">Swap</div>
        <div>
          <span className="pill tiny">{cfg ? chainName(chainId) : "Unsupported chain"}</span>{" "}
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
            value={exact === "in" ? amountInStr : quote && tokenIn ? fmtFull(quote.amountIn, tokenIn.decimals) : ""}
            onChange={(e) => {
              setAmountInStr(e.target.value);
              setExact("in");
            }}
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
            setAmountOutStr("");
            setExact("in");
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
            inputMode="decimal"
            placeholder="0"
            value={exact === "out" ? amountOutStr : quote && tokenOut ? fmtFull(quote.amountOut, tokenOut.decimals) : ""}
            onChange={(e) => {
              setAmountOutStr(e.target.value);
              setExact("out");
            }}
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

      {quote && tokenIn && tokenOut && minOut != null && maxIn != null && mode === "swap" && (
        <div className="review">
          {quote.exact === "in" ? (
            <div>
              <span className="muted">Minimum received</span>
              <b>{fmtAmt(minOut, tokenOut.decimals)} {tokenOut.symbol}</b>
            </div>
          ) : (
            <div>
              <span className="muted">Maximum sold</span>
              <b>{fmtAmt(maxIn, tokenIn.decimals)} {tokenIn.symbol}</b>
            </div>
          )}
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
