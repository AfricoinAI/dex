# Africoin web app

React + Vite frontend for Africoin. Replaces the prior onchain HTML wrapper.

- **Wallet:** [Dynamic](https://www.dynamic.xyz) via `@dynamic-labs/sdk-react-core`
  with the wagmi connector.
- **On-ramp:** [zkp2p](https://docs.peer.xyz/protocol/zkp2p-protocol) via the
  Peer browser extension (`@zkp2p/sdk`).
- **Contracts:** the same deployed `UniswapV2Factory`, `UniswapV2Pair`, and
  `TamaRouter` addresses described in the root README. The web app does not
  redeploy or modify any of them.

## Setup

```sh
cd web
cp .env.example .env
# Paste your Dynamic environment ID from https://app.dynamic.xyz
npm install
npm run dev
```

## Build

```sh
npm run build
# emits ./dist
```

## Deploy (Cloudflare Pages)

Connect this repo to Cloudflare Pages with:

- Build command: `cd web && npm install && npm run build`
- Build output directory: `web/dist`
- Environment variable: `VITE_DYNAMIC_ENVIRONMENT_ID`

The app is a fully static SPA — no serverless functions, no API routes.
