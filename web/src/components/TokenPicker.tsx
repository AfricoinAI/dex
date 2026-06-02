import { useState } from "react";
import type { Token } from "../lib/tokenList";
import { short } from "../lib/format";

type Props = {
  open: boolean;
  tokens: Token[];
  onPick: (t: Token) => void;
  onClose: () => void;
  exclude?: Token | null;
};

export function TokenPicker({ open, tokens, onPick, onClose, exclude }: Props) {
  const [query, setQuery] = useState("");
  if (!open) return null;
  const q = query.trim().toLowerCase();
  const filtered = tokens
    .filter((t) => (exclude ? t.address.toLowerCase() !== exclude.address.toLowerCase() || t.native !== exclude.native : true))
    .filter((t) =>
      !q ||
      t.symbol.toLowerCase().includes(q) ||
      t.name.toLowerCase().includes(q) ||
      t.address.toLowerCase().includes(q),
    )
    .slice(0, 100);

  return (
    <div className="modal on" onClick={(e) => e.target === e.currentTarget && onClose()}>
      <div className="sheet">
        <div className="sheetHead">
          <b>Select token</b>
          <button className="x" onClick={onClose}>
            ×
          </button>
        </div>
        <input
          className="search"
          placeholder="Search name or paste address"
          value={query}
          onChange={(e) => setQuery(e.target.value)}
          autoComplete="off"
          spellCheck={false}
        />
        <div className="list">
          {filtered.map((t) => (
            <button
              key={`${t.native ? "native" : t.address}`}
              className="item"
              onClick={() => {
                onPick(t);
                onClose();
              }}
            >
              <span className="logo">
                {t.logoURI ? <img src={t.logoURI} alt="" /> : t.symbol.slice(0, 2)}
              </span>
              <div>
                <div className="sym">{t.symbol}</div>
                <div className="addr">{t.native ? "Native ETH" : `${t.name} · ${short(t.address)}`}</div>
              </div>
            </button>
          ))}
          {filtered.length === 0 && (
            <div className="tiny" style={{ padding: 16 }}>
              No tokens match. Try a different query.
            </div>
          )}
        </div>
      </div>
    </div>
  );
}
