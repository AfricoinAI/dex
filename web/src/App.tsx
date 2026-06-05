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
    </>
  );
}
