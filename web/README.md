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

- Root directory: `web`
- Build command: `npm run build`
- Build output directory: `dist`
- Environment variables: `VITE_DYNAMIC_ENVIRONMENT_ID`, `GATEWAY_URL`,
  `DEX_APP_ID`, `DEX_APP_KEY_ID`, `DEX_GATEWAY_SECRET`, `DEX_PUBLIC_ORIGIN`

The app is a Vite SPA plus a Cloudflare Pages Function under
`functions/api/gateway/*`, used as the server-side signing proxy for the
Africoin gateway. Set `DEX_GATEWAY_SECRET` as an encrypted secret.
