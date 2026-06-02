import React from "react";
import ReactDOM from "react-dom/client";
import { App } from "./App";
import { Providers } from "./providers";
import { ErrorBoundary } from "./components/ErrorBoundary";
import "./styles.css";

ReactDOM.createRoot(document.getElementById("root")!).render(
  <React.StrictMode>
    <ErrorBoundary label="App">
      <Providers>
        <App />
      </Providers>
    </ErrorBoundary>
  </React.StrictMode>,
);
