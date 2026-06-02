import { useState } from "react";
import { Header } from "./components/Header";
import { Swap } from "./components/Swap";
import { Pool } from "./components/Pool";
import { Buy } from "./components/Buy";

type Tab = "swap" | "pool" | "buy";

export function App() {
  const [tab, setTab] = useState<Tab>("swap");
  return (
    <>
      <Header tab={tab} setTab={setTab} />
      <main className="shell">
        {tab === "swap" && <Swap />}
        {tab === "pool" && <Pool />}
        {tab === "buy" && <Buy />}
      </main>
      <footer className="foot tiny">
        Built with{" "}
        <a href="https://tama.tools" target="_blank" rel="noopener noreferrer">
          Tama
        </a>{" "}
        &amp;{" "}
        <a href="https://veritylang.com" target="_blank" rel="noopener noreferrer">
          Verity
        </a>
        . Wallets via{" "}
        <a href="https://www.dynamic.xyz" target="_blank" rel="noopener noreferrer">
          Dynamic
        </a>
        . On-ramp via{" "}
        <a href="https://docs.peer.xyz" target="_blank" rel="noopener noreferrer">
          zkp2p
        </a>
        .
      </footer>
    </>
  );
}
