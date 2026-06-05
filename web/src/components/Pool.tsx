import { useEffect, useMemo, useState } from "react";
import { useAccount, useChainId, usePublicClient, useWalletClient } from "wagmi";
import { type Address, zeroAddress } from "viem";
import { CONTRACTS, routerDeployed } from "../config/contracts";
import { chainName } from "../config/chains";
import { erc20Abi, factoryAbi, pairAbi, routerAbi } from "../lib/abi";
import { deadline, fmtAmt, fmtFull, minWithSlip, parseAmt, short } from "../lib/format";
import { useSlippageBps, useTokens } from "../lib/state";
import type { Token } from "../lib/tokenList";
import { TokenPicker } from "./TokenPicker";

type Mode = "add" | "remove";

export function Pool() {
  const chainId = useChainId();
  const cfg = CONTRACTS[chainId];
  const { address } = useAccount();
  const publicClient = usePublicClient();
  const { data: walletClient, error: walletClientError } = useWalletClient();
  const { tokens } = useTokens();
  const slipBps = useSlippageBps();

  const [mode, setMode] = useState<Mode>("add");
  const [tokenA, setTokenA] = useState<Token | null>(null);
  const [tokenB, setTokenB] = useState<Token | null>(null);
  const [amountA, setAmountA] = useState("");
  const [amountB, setAmountB] = useState("");
  const [lpAmount, setLpAmount] = useState("");
  const [picker, setPicker] = useState<"a" | "b" | null>(null);
  const [pair, setPair] = useState<Address | null>(null);
  const [reserves, setReserves] = useState<{ a: bigint; b: bigint } | null>(null);
  const [lpBalance, setLpBalance] = useState<bigint | null>(null);
  const [lpSupply, setLpSupply] = useState<bigint | null>(null);
  const [busy, setBusy] = useState(false);
  const [status, setStatus] = useState<string | null>(null);
  const [errMsg, setErrMsg] = useState<string | null>(null);

  useEffect(() => {
    setTokenA(null);
    setTokenB(null);
    setPair(null);
    setReserves(null);
    setLpBalance(null);
  }, [chainId]);

  // Look up the pair address + reserves whenever the token selection changes.
  useEffect(() => {
    if (!publicClient || !cfg || !tokenA || !tokenB) {
      setPair(null);
      setReserves(null);
      return;
    }
    let cancelled = false;
    (async () => {
      try {
        const a = tokenA.native ? cfg.weth : tokenA.address;
        const b = tokenB.native ? cfg.weth : tokenB.address;
        const pairAddr = (await publicClient.readContract({
          abi: factoryAbi,
          address: cfg.factory,
          functionName: "getPair",
          args: [a, b],
        })) as Address;
        if (cancelled) return;
        if (pairAddr === zeroAddress) {
          setPair(null);
          setReserves(null);
          return;
        }
        setPair(pairAddr);
        const [token0, [reserve0, reserve1], supply] = await Promise.all([
          publicClient.readContract({ abi: pairAbi, address: pairAddr, functionName: "token0" }) as Promise<Address>,
          publicClient.readContract({ abi: pairAbi, address: pairAddr, functionName: "getReserves" }) as Promise<[bigint, bigint, number]>,
          publicClient.readContract({ abi: pairAbi, address: pairAddr, functionName: "totalSupply" }) as Promise<bigint>,
        ]);
        if (cancelled) return;
        const aIsToken0 = token0.toLowerCase() === a.toLowerCase();
        setReserves({ a: aIsToken0 ? reserve0 : reserve1, b: aIsToken0 ? reserve1 : reserve0 });
        setLpSupply(supply);
      } catch {
        if (!cancelled) {
          setPair(null);
          setReserves(null);
        }
      }
    })();
    return () => {
      cancelled = true;
    };
  }, [publicClient, cfg, tokenA, tokenB, status]);

  // LP balance for remove mode.
  useEffect(() => {
    if (!publicClient || !address || !pair) {
      setLpBalance(null);
      return;
    }
    let cancelled = false;
    (async () => {
      try {
        const bal = await publicClient.readContract({ abi: erc20Abi, address: pair, functionName: "balanceOf", args: [address] });
        if (!cancelled) setLpBalance(bal);
      } catch {
        if (!cancelled) setLpBalance(null);
      }
    })();
    return () => {
      cancelled = true;
    };
  }, [publicClient, address, pair, status]);

  const burnAmounts = useMemo(() => {
    if (!reserves || !lpSupply || lpSupply === 0n) return null;
    let liq: bigint;
    try {
      liq = parseAmt(lpAmount, 18);
    } catch {
      return null;
    }
    if (liq === 0n) return null;
    return { a: (liq * reserves.a) / lpSupply, b: (liq * reserves.b) / lpSupply, liq };
  }, [reserves, lpSupply, lpAmount]);

  async function ensureAllowance(token: Token, amount: bigint): Promise<boolean> {
    if (!walletClient || !cfg || token.native) return true;
    const current = (await publicClient!.readContract({
      abi: erc20Abi,
      address: token.address,
      functionName: "allowance",
      args: [address!, cfg.router],
    })) as bigint;
    if (current >= amount) return true;
    const hash = await walletClient.writeContract({
      abi: erc20Abi,
      address: token.address,
      functionName: "approve",
      args: [cfg.router, amount],
    });
    setStatus(`Approval submitted ${short(hash)}`);
    await publicClient!.waitForTransactionReceipt({ hash });
    return true;
  }

  async function executeAdd() {
    if (!cfg || !tokenA || !tokenB || !address) return;
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
      const aAmt = parseAmt(amountA, tokenA.decimals);
      const bAmt = parseAmt(amountB, tokenB.decimals);
      if (aAmt === 0n || bAmt === 0n) throw new Error("Enter both amounts");
      if (!tokenA.native) await ensureAllowance(tokenA, aAmt);
      if (!tokenB.native) await ensureAllowance(tokenB, bAmt);

      const dl = deadline();
      let hash: `0x${string}`;
      if (tokenA.native || tokenB.native) {
        const token = tokenA.native ? tokenB : tokenA;
        const tokenAmt = tokenA.native ? bAmt : aAmt;
        const ethAmt = tokenA.native ? aAmt : bAmt;
        hash = await walletClient.writeContract({
          abi: routerAbi,
          address: cfg.router,
          functionName: "addLiquidityETH",
          args: [token.address, tokenAmt, minWithSlip(tokenAmt, slipBps), minWithSlip(ethAmt, slipBps), address, dl],
          value: ethAmt,
        });
      } else {
        hash = await walletClient.writeContract({
          abi: routerAbi,
          address: cfg.router,
          functionName: "addLiquidity",
          args: [tokenA.address, tokenB.address, aAmt, bAmt, minWithSlip(aAmt, slipBps), minWithSlip(bAmt, slipBps), address, dl],
        });
      }
      setStatus(`Submitted ${short(hash)}`);
      await publicClient!.waitForTransactionReceipt({ hash });
      setStatus(`Confirmed ${short(hash)}`);
      setAmountA("");
      setAmountB("");
    } catch (e) {
      setErrMsg(e instanceof Error ? e.message : "Add liquidity failed");
    } finally {
      setBusy(false);
    }
  }

  async function executeRemove() {
    if (!cfg || !tokenA || !tokenB || !address || !pair || !burnAmounts) return;
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
      // Approve the router to pull the LP tokens.
      const current = (await publicClient!.readContract({
        abi: erc20Abi,
        address: pair,
        functionName: "allowance",
        args: [address, cfg.router],
      })) as bigint;
      if (current < burnAmounts.liq) {
        const approveHash = await walletClient.writeContract({
          abi: erc20Abi,
          address: pair,
          functionName: "approve",
          args: [cfg.router, burnAmounts.liq],
        });
        setStatus(`LP approval submitted ${short(approveHash)}`);
        await publicClient!.waitForTransactionReceipt({ hash: approveHash });
      }
      const dl = deadline();
      let hash: `0x${string}`;
      if (tokenA.native || tokenB.native) {
        const token = tokenA.native ? tokenB : tokenA;
        const minToken = tokenA.native ? minWithSlip(burnAmounts.b, slipBps) : minWithSlip(burnAmounts.a, slipBps);
        const minEth = tokenA.native ? minWithSlip(burnAmounts.a, slipBps) : minWithSlip(burnAmounts.b, slipBps);
        hash = await walletClient.writeContract({
          abi: routerAbi,
          address: cfg.router,
          functionName: "removeLiquidityETH",
          args: [token.address, burnAmounts.liq, minToken, minEth, address, dl],
        });
      } else {
        hash = await walletClient.writeContract({
          abi: routerAbi,
          address: cfg.router,
          functionName: "removeLiquidity",
          args: [
            tokenA.address,
            tokenB.address,
            burnAmounts.liq,
            minWithSlip(burnAmounts.a, slipBps),
            minWithSlip(burnAmounts.b, slipBps),
            address,
            dl,
          ],
        });
      }
      setStatus(`Submitted ${short(hash)}`);
      await publicClient!.waitForTransactionReceipt({ hash });
      setStatus(`Confirmed ${short(hash)}`);
      setLpAmount("");
    } catch (e) {
      setErrMsg(e instanceof Error ? e.message : "Remove liquidity failed");
    } finally {
      setBusy(false);
    }
  }

  function pickerExclude() {
    return picker === "a" ? tokenB : tokenA;
  }

  return (
    <section className="card">
      <div className="head">
        <div className="title">Pool</div>
        <span className="pill tiny">{cfg ? chainName(chainId) : "Unsupported chain"}</span>
      </div>

      <div className="poolMode">
        <button className={mode === "add" ? "on" : ""} onClick={() => setMode("add")}>
          Add
        </button>
        <button className={mode === "remove" ? "on" : ""} onClick={() => setMode("remove")}>
          Remove
        </button>
      </div>

      <div className="box">
        <div className="lbl">
          <span>Token A</span>
        </div>
        <div className="amount">
          {mode === "add" && (
            <input
              inputMode="decimal"
              placeholder="0"
              value={amountA}
              onChange={(e) => setAmountA(e.target.value)}
            />
          )}
          <button className={tokenA ? "tok" : "tok empty"} onClick={() => setPicker("a")}>
            {tokenA ? tokenA.symbol : "Select token"}
          </button>
        </div>
      </div>

      <div className="box">
        <div className="lbl">
          <span>Token B</span>
        </div>
        <div className="amount">
          {mode === "add" && (
            <input
              inputMode="decimal"
              placeholder="0"
              value={amountB}
              onChange={(e) => setAmountB(e.target.value)}
            />
          )}
          <button className={tokenB ? "tok" : "tok empty"} onClick={() => setPicker("b")}>
            {tokenB ? tokenB.symbol : "Select token"}
          </button>
        </div>
      </div>

      {mode === "remove" && (
        <div className="box">
          <div className="lbl">
            <span>LP amount</span>
            {lpBalance != null && pair && (
              <span className="bal click" onClick={() => setLpAmount(fmtFull(lpBalance, 18))}>
                Balance: {fmtAmt(lpBalance, 18)} LP
              </span>
            )}
          </div>
          <div className="amount">
            <input
              inputMode="decimal"
              placeholder="0"
              value={lpAmount}
              onChange={(e) => setLpAmount(e.target.value)}
            />
          </div>
        </div>
      )}

      {pair && reserves && tokenA && tokenB && (
        <div className="review">
          <div>
            <span className="muted">Pair</span>
            <span>{short(pair)}</span>
          </div>
          <div>
            <span className="muted">Reserves</span>
            <span>
              {fmtAmt(reserves.a, tokenA.decimals)} {tokenA.symbol} / {fmtAmt(reserves.b, tokenB.decimals)} {tokenB.symbol}
            </span>
          </div>
          {mode === "remove" && burnAmounts && (
            <div>
              <span className="muted">You receive</span>
              <span>
                {fmtAmt(burnAmounts.a, tokenA.decimals)} {tokenA.symbol} / {fmtAmt(burnAmounts.b, tokenB.decimals)} {tokenB.symbol}
              </span>
            </div>
          )}
        </div>
      )}

      <button
        className="cta"
        disabled={busy || !address || !routerDeployed(cfg) || !tokenA || !tokenB || (mode === "remove" && !burnAmounts)}
        onClick={mode === "add" ? executeAdd : executeRemove}
      >
        {busy
          ? "Submitting…"
          : !routerDeployed(cfg)
            ? "Trading not live on this chain yet"
            : mode === "add"
              ? (pair ? "Add liquidity" : "Create pool and add liquidity")
              : "Remove liquidity"}
      </button>

      <div className={errMsg ? "status err" : "status"}>{errMsg ?? status ?? ""}</div>

      <TokenPicker
        open={picker !== null}
        tokens={tokens}
        exclude={pickerExclude()}
        onPick={(t) => {
          if (picker === "a") setTokenA(t);
          else setTokenB(t);
        }}
        onClose={() => setPicker(null)}
      />
    </section>
  );
}
