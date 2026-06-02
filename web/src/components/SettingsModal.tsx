import { useEffect, useState } from "react";

const KEY = "tama:slippagePercent";

export function SettingsModal({ open, onClose }: { open: boolean; onClose: () => void }) {
  const [value, setValue] = useState("0.5");

  useEffect(() => {
    const stored = localStorage.getItem(KEY);
    if (stored && /^\d+(\.\d+)?$/.test(stored)) setValue(stored);
  }, []);

  function save(next: string) {
    setValue(next);
    if (/^\d+(\.\d+)?$/.test(next)) {
      const n = Number(next);
      if (n > 0 && n <= 50) localStorage.setItem(KEY, next);
    }
  }

  if (!open) return null;
  return (
    <div className="modal on" onClick={(e) => e.target === e.currentTarget && onClose()}>
      <div className="sheet">
        <div className="sheetHead">
          <b>Settings</b>
          <button className="x" onClick={onClose}>
            ×
          </button>
        </div>
        <div className="setrow">
          <span>Max slippage</span>
          <label>
            <input type="text" inputMode="decimal" value={value} onChange={(e) => save(e.target.value)} /> %
          </label>
        </div>
        <div className="manage">
          <div className="tiny">
            Slippage applies to every swap and liquidity add. The new value takes effect on the
            next quote.
          </div>
        </div>
      </div>
    </div>
  );
}
