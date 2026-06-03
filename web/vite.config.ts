import { defineConfig, loadEnv } from "vite";
import react from "@vitejs/plugin-react";
import { gatewayProxyPlugin } from "./dev/gatewayProxyPlugin";

export default defineConfig(({ mode }) => {
  // Load ALL env (incl. non-VITE server-only keys) for the dev gateway proxy.
  // These are used only inside the Node-side dev middleware and are never
  // injected into the client bundle (Vite only exposes VITE_-prefixed vars).
  const env = loadEnv(mode, process.cwd(), "");
  return {
    plugins: [react(), gatewayProxyPlugin(env)],
    build: {
      target: "es2022",
      sourcemap: false,
    },
  };
});
