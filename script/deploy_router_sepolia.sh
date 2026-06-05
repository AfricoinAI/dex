#!/usr/bin/env bash
# Deploys TamaRouter to Sepolia against the published CREATE2 factory and the
# canonical Sepolia WETH. The deployer credential is read from
# SEPOLIA_DEPLOYER_KEY, then ~/.sepolia_deployer_key, then a hidden
# interactive prompt — it is never echoed or written anywhere. Either a raw
# 0x private key or a 12/24-word seed phrase works; a phrase is scanned for
# the account matching DEPLOYER below. Paste the printed "Deployed to:"
# address into web/src/config/contracts.ts (router, chain 11155111).
set -euo pipefail
cd "$(dirname "$0")/.."

RPC="${SEPOLIA_RPC_URL:-https://ethereum-sepolia-rpc.publicnode.com}"
FACTORY=0x00000021543ed46B665A74484c82B71E4eB61e34
WETH=0xfFf9976782d46CC05630D1f6eBAb18b2324d6B14
DEPLOYER=0x4F0Ed0Db7B27c3986150110488E2BE4794D2C821

KEY="${SEPOLIA_DEPLOYER_KEY:-}"
if [ -z "$KEY" ] && [ -f "$HOME/.sepolia_deployer_key" ]; then
  KEY="$(cat "$HOME/.sepolia_deployer_key")"
fi
if [ -z "$KEY" ]; then
  read -rsp "Sepolia deployer private key or seed phrase (input hidden): " KEY
  echo
fi

# A credential containing spaces is a seed phrase: scan the standard BIP-44
# indices (m/44'/60'/0'/0/i, MetaMask's derivation) for the expected deployer.
case "$KEY" in
  *" "*)
    FOUND=""
    for i in $(seq 0 19); do
      CAND=$(cast wallet private-key "$KEY" "$i")
      if [ "$(cast wallet address --private-key "$CAND" | tr '[:upper:]' '[:lower:]')" = \
           "$(echo "$DEPLOYER" | tr '[:upper:]' '[:lower:]')" ]; then
        FOUND="$CAND"
        echo "Found deployer at mnemonic index $i"
        break
      fi
    done
    if [ -z "$FOUND" ]; then
      echo "ERROR: no account in the first 20 indices of this phrase matches $DEPLOYER" >&2
      exit 1
    fi
    KEY="$FOUND"
    ;;
esac

ADDR=$(cast wallet address --private-key "$KEY")
if [ "$(echo "$ADDR" | tr '[:upper:]' '[:lower:]')" != "$(echo "$DEPLOYER" | tr '[:upper:]' '[:lower:]')" ]; then
  echo "ERROR: credential resolves to $ADDR, expected deployer $DEPLOYER" >&2
  exit 1
fi
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
