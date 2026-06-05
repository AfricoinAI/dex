#!/usr/bin/env bash
# Deploys TamaRouter to Sepolia against the published CREATE2 factory and the
# canonical Sepolia WETH. The deployer key is read from SEPOLIA_DEPLOYER_KEY,
# then ~/.sepolia_deployer_key, then a hidden interactive prompt — it is never
# echoed or written anywhere. Paste the printed "Deployed to:" address into
# web/src/config/contracts.ts (router, chain 11155111).
set -euo pipefail
cd "$(dirname "$0")/.."

RPC="${SEPOLIA_RPC_URL:-https://ethereum-sepolia-rpc.publicnode.com}"
FACTORY=0x00000021543ed46B665A74484c82B71E4eB61e34
WETH=0xfFf9976782d46CC05630D1f6eBAb18b2324d6B14

KEY="${SEPOLIA_DEPLOYER_KEY:-}"
if [ -z "$KEY" ] && [ -f "$HOME/.sepolia_deployer_key" ]; then
  KEY="$(cat "$HOME/.sepolia_deployer_key")"
fi
if [ -z "$KEY" ]; then
  read -rsp "Sepolia deployer private key (input hidden): " KEY
  echo
fi

ADDR=$(cast wallet address --private-key "$KEY")
BAL_WEI=$(cast balance "$ADDR" --rpc-url "$RPC")
echo "Deployer: $ADDR"
echo "Balance:  $(cast from-wei "$BAL_WEI") ETH (Sepolia)"
if [ "$BAL_WEI" = "0" ]; then
  echo "ERROR: deployer has no Sepolia ETH" >&2
  exit 1
fi

forge create src/TamaRouter.sol:TamaRouter \
  --rpc-url "$RPC" \
  --private-key "$KEY" \
  --broadcast \
  --constructor-args "$FACTORY" "$WETH"
