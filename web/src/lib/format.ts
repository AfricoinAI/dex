import { type Address, isAddress } from "viem";

export function parseAmt(raw: string, decimals: number): bigint {
  const s = (raw ?? "").trim();
  if (!s) return 0n;
  if (!/^\d*(\.\d*)?$/.test(s) || s === ".") throw new Error("Invalid amount");
  const [i, f = ""] = s.split(".");
  const padded = (f + "0".repeat(decimals)).slice(0, decimals);
  return BigInt(i || "0") * 10n ** BigInt(decimals) + BigInt(padded || "0");
}

export function fmtAmt(value: bigint | null | undefined, decimals: number): string {
  if (value == null) return "";
  const n = BigInt(value);
  const s = n.toString().padStart(decimals + 1, "0");
  const i = s.slice(0, -decimals) || "0";
  const f = s.slice(-decimals).replace(/0+$/, "");
  return f ? `${i}.${f.slice(0, 6)}` : i;
}

export function fmtFull(value: bigint | null | undefined, decimals: number): string {
  if (value == null) return "";
  const n = BigInt(value);
  const s = n.toString().padStart(decimals + 1, "0");
  const i = s.slice(0, -decimals) || "0";
  const f = s.slice(-decimals).replace(/0+$/, "");
  return f ? `${i}.${f}` : i;
}

export function short(address: Address | string | undefined): string {
  if (!address) return "";
  return `${address.slice(0, 6)}…${address.slice(-4)}`;
}

export const isAddr = (s: string): s is Address => isAddress(s);

export function money(value: number | null | undefined): string {
  if (value == null || !isFinite(value)) return "";
  if (value >= 1) return `$${value.toLocaleString(undefined, { maximumFractionDigits: 2 })}`;
  return `$${value.toPrecision(3)}`;
}

export function minWithSlip(amount: bigint, slipBps: bigint): bigint {
  return (amount * (10000n - slipBps)) / 10000n;
}

export function maxWithSlip(amount: bigint, slipBps: bigint): bigint {
  return (amount * (10000n + slipBps)) / 10000n;
}

export function deadline(seconds = 1200): bigint {
  return BigInt(Math.floor(Date.now() / 1000) + seconds);
}
