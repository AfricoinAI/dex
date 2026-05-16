import Contracts.Common
import Compiler.ECM
import Compiler.Modules.ERC20

namespace TamaUniV2

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Compiler.Yul
open Compiler.ECM

def uniswapV2CallbackModule : ExternalCallModule where
  name := "uniswapV2Call"
  numArgs := 4
  resultVars := []
  writesState := true
  readsState := false
  axioms := ["uniswap_v2_callback_interface"]
  proofStatus := .assumed
  compile := fun ctx args => do
    let [targetExpr, senderExpr, amount0OutExpr, amount1OutExpr] := args
      | throw "uniswapV2Call expects 4 arguments (target, sender, amount0Out, amount1Out)"
    let selectorExpr := YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x10d1e85c]
    let bytesLenExpr := YulExpr.ident "data_length"
    let bytesDataOffset := YulExpr.ident "data_data_offset"
    let bytesDataSlot := 4 + (3 + 2) * 32
    let paddedBytesLen := YulExpr.call "and" [
      YulExpr.call "add" [bytesLenExpr, YulExpr.lit 31],
      YulExpr.call "not" [YulExpr.lit 31]
    ]
    let totalSize := YulExpr.call "add" [YulExpr.lit bytesDataSlot, paddedBytesLen]
    let copyBytes := dynamicCopyData ctx (YulExpr.lit bytesDataSlot) bytesDataOffset bytesLenExpr
    let callBlock :=
      [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, selectorExpr])
      , YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, senderExpr])
      , YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, amount0OutExpr])
      , YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 68, amount1OutExpr])
      , YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 100, YulExpr.lit 128])
      , YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 132, bytesLenExpr])
      ] ++ copyBytes ++
      [ YulStmt.let_ "__uv2_cb_success" (YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          YulExpr.lit 0,
          YulExpr.lit 0, totalSize,
          YulExpr.lit 0, YulExpr.lit 0
        ])
      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__uv2_cb_success"]) [
          YulStmt.let_ "__uv2_cb_rds" (YulExpr.call "returndatasize" []),
          YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__uv2_cb_rds"]),
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__uv2_cb_rds"])
        ]
      ]
    pure [YulStmt.if_ (YulExpr.call "gt" [bytesLenExpr, YulExpr.lit 0]) [YulStmt.block callBlock]]

verity_contract UniswapV2Pair where
  storage
    factorySlot : Address := slot 0
    token0Slot : Address := slot 1
    token1Slot : Address := slot 2
    reserve0Slot : Uint256 := slot 3
    reserve1Slot : Uint256 := slot 4
    blockTimestampLastSlot : Uint256 := slot 5
    price0CumulativeLastSlot : Uint256 := slot 6
    price1CumulativeLastSlot : Uint256 := slot 7
    totalSupplySlot : Uint256 := slot 8
    balancesSlot : Address → Uint256 := slot 9
    allowancesSlot : Address → Address → Uint256 := slot 10
    unlockedSlot : Uint256 := slot 11

  constants
    minimumLiquidity : Uint256 := 1000
    feeDenominator : Uint256 := 1000
    feeAdjustment : Uint256 := 3
    maxUint112 : Uint256 := 5192296858534827628530496329220095
    q112 : Uint256 := 5192296858534827628530496329220096
    uint32Modulus : Uint256 := 4294967296
    maxUint256 : Uint256 := 115792089237316195423570985008687907853269984665640564039457584007913129639935

  constructor () := do
    let sender ← msgSender
    setStorageAddr factorySlot sender
    setStorage unlockedSlot 1

  function view decimals () : Uint256 := do
    return 18

  function view totalSupply () : Uint256 := do
    let supply ← getStorage totalSupplySlot
    return supply

  function view balanceOf (owner : Address) : Uint256 := do
    let balanceValue ← getMapping balancesSlot owner
    return balanceValue

  function view allowance (owner : Address, spender : Address) : Uint256 := do
    let allowed ← getMapping2 allowancesSlot owner spender
    return allowed

  function view factory () : Address := do
    let addr ← getStorageAddr factorySlot
    return addr

  function view token0 () : Address := do
    let addr ← getStorageAddr token0Slot
    return addr

  function view token1 () : Address := do
    let addr ← getStorageAddr token1Slot
    return addr

  function view MINIMUM_LIQUIDITY () : Uint256 := do
    return minimumLiquidity

  function view getReserves () : Tuple [Uint256, Uint256, Uint256] := do
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    let blockTimestampLastValue ← getStorage blockTimestampLastSlot
    return (reserve0Value, reserve1Value, blockTimestampLastValue)

  function view price0CumulativeLast () : Uint256 := do
    let price ← getStorage price0CumulativeLastSlot
    return price

  function view price1CumulativeLast () : Uint256 := do
    let price ← getStorage price1CumulativeLastSlot
    return price

  function view kLast () : Uint256 := do
    return 0

  function «initialize» (token0Value : Address, token1Value : Address) : Unit := do
    let sender ← msgSender
    let factoryValue ← getStorageAddr factorySlot
    require (sender == factoryValue) "UniswapV2: FORBIDDEN"
    let existing0 ← getStorageAddr token0Slot
    let existing1 ← getStorageAddr token1Slot
    require (existing0 == zeroAddress && existing1 == zeroAddress) "UniswapV2: ALREADY_INITIALIZED"
    setStorageAddr token0Slot token0Value
    setStorageAddr token1Slot token1Value

  function approve (spender : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    setMapping2 allowancesSlot sender spender amount
    return true

  function transfer (toAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    require (toAddr != zeroAddress) "UniswapV2: TRANSFER_TO_ZERO_ADDRESS"
    let senderBalance ← getMapping balancesSlot sender
    require (senderBalance >= amount) "UniswapV2: INSUFFICIENT_BALANCE"
    if sender == toAddr then
      pure ()
    else
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance amount) "UniswapV2: BALANCE_OVERFLOW"
      setMapping balancesSlot sender (sub senderBalance amount)
      setMapping balancesSlot toAddr newToBalance
    return true

  function transferFrom (fromAddr : Address, toAddr : Address, amount : Uint256) : Bool := do
    let spender ← msgSender
    require (toAddr != zeroAddress) "UniswapV2: TRANSFER_TO_ZERO_ADDRESS"
    let currentAllowance ← getMapping2 allowancesSlot fromAddr spender
    require (currentAllowance >= amount) "UniswapV2: INSUFFICIENT_ALLOWANCE"
    let fromBalance ← getMapping balancesSlot fromAddr
    require (fromBalance >= amount) "UniswapV2: INSUFFICIENT_BALANCE"
    if fromAddr == toAddr then
      pure ()
    else
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance amount) "UniswapV2: BALANCE_OVERFLOW"
      setMapping balancesSlot fromAddr (sub fromBalance amount)
      setMapping balancesSlot toAddr newToBalance
    if currentAllowance == maxUint256 then
      pure ()
    else
      setMapping2 allowancesSlot fromAddr spender (sub currentAllowance amount)
    return true

  function view sqrt (y : Uint256) : Uint256 := do
    let mut z := 1
    if y == 0 then
      z := 0
    else
      pure ()
    if y > 3 then
      z := y
      let mut x := add (div y 2) 1
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
      if x < z then
        z := x
        x := div (add (div y x) x) 2
      else
        pure ()
    else
      pure ()
    return z

  function allow_post_interaction_writes mint (toAddr : Address) : Uint256 := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    setStorage unlockedSlot 0
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    let selfAddr ← Verity.contractAddress
    let balance0Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token0Value, selfAddr]
    let balance1Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token1Value, selfAddr]
    require (balance0Now <= maxUint112 && balance1Now <= maxUint112) "UniswapV2: OVERFLOW"
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    require (balance0Now >= reserve0Value && balance1Now >= reserve1Value) "UniswapV2: INSUFFICIENT_AMOUNT"
    let amount0 := sub balance0Now reserve0Value
    let amount1 := sub balance1Now reserve1Value
    require (amount0 > 0 && amount1 > 0) "UniswapV2: INSUFFICIENT_AMOUNT"
    let supply ← getStorage totalSupplySlot
    let mut liquidity := 0
    if supply == 0 then
      let product := mul amount0 amount1
      require (amount0 == 0 || div product amount0 == amount1) "UniswapV2: MINT_OVERFLOW"
      let root ← sqrt product
      require (root > minimumLiquidity) "UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED"
      liquidity := sub root minimumLiquidity
      setStorage totalSupplySlot root
      setMapping balancesSlot zeroAddress minimumLiquidity
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance liquidity) "UniswapV2: BALANCE_OVERFLOW"
      setMapping balancesSlot toAddr newToBalance
    else
      require (reserve0Value > 0 && reserve1Value > 0) "UniswapV2: INSUFFICIENT_LIQUIDITY"
      let liq0Product := mul amount0 supply
      require (amount0 == 0 || div liq0Product amount0 == supply) "UniswapV2: MINT_OVERFLOW"
      let liq1Product := mul amount1 supply
      require (amount1 == 0 || div liq1Product amount1 == supply) "UniswapV2: MINT_OVERFLOW"
      let liq0 := div liq0Product reserve0Value
      let liq1 := div liq1Product reserve1Value
      liquidity := min liq0 liq1
      require (liquidity > 0) "UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED"
      let newSupply ← requireSomeUint (safeAdd supply liquidity) "UniswapV2: SUPPLY_OVERFLOW"
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance liquidity) "UniswapV2: BALANCE_OVERFLOW"
      setStorage totalSupplySlot newSupply
      setMapping balancesSlot toAddr newToBalance
    let currentTimestamp ← Verity.blockTimestamp
    let timestamp32 := mod currentTimestamp uint32Modulus
    let previousTimestamp ← getStorage blockTimestampLastSlot
    let mut elapsed := 0
    if timestamp32 >= previousTimestamp then
      elapsed := sub timestamp32 previousTimestamp
    else
      elapsed := add (sub uint32Modulus previousTimestamp) timestamp32
    if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
      let price0 := div (mul reserve1Value q112) reserve0Value
      let price1 := div (mul reserve0Value q112) reserve1Value
      let price0Last ← getStorage price0CumulativeLastSlot
      let price1Last ← getStorage price1CumulativeLastSlot
      setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
      setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
    else
      pure ()
    setStorage reserve0Slot balance0Now
    setStorage reserve1Slot balance1Now
    setStorage blockTimestampLastSlot timestamp32
    setStorage unlockedSlot 1
    return liquidity

  function allow_post_interaction_writes burn (toAddr : Address) : Tuple [Uint256, Uint256] := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    setStorage unlockedSlot 0
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    let selfAddr ← Verity.contractAddress
    let balance0Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token0Value, selfAddr]
    let balance1Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token1Value, selfAddr]
    let liquidity ← getMapping balancesSlot selfAddr
    let supply ← getStorage totalSupplySlot
    require (liquidity > 0 && supply > 0) "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED"
    let amount0Product := mul liquidity balance0Now
    require (liquidity == 0 || div amount0Product liquidity == balance0Now) "UniswapV2: BURN_OVERFLOW"
    let amount1Product := mul liquidity balance1Now
    require (liquidity == 0 || div amount1Product liquidity == balance1Now) "UniswapV2: BURN_OVERFLOW"
    let amount0 := div amount0Product supply
    let amount1 := div amount1Product supply
    require (amount0 > 0 && amount1 > 0) "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED"
    setMapping balancesSlot selfAddr 0
    setStorage totalSupplySlot (sub supply liquidity)
    safeTransfer token0Value toAddr amount0
    safeTransfer token1Value toAddr amount1
    let balance0After ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token0Value, selfAddr]
    let balance1After ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token1Value, selfAddr]
    require (balance0After <= maxUint112 && balance1After <= maxUint112) "UniswapV2: OVERFLOW"
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    let currentTimestamp ← Verity.blockTimestamp
    let timestamp32 := mod currentTimestamp uint32Modulus
    let previousTimestamp ← getStorage blockTimestampLastSlot
    let mut elapsed := 0
    if timestamp32 >= previousTimestamp then
      elapsed := sub timestamp32 previousTimestamp
    else
      elapsed := add (sub uint32Modulus previousTimestamp) timestamp32
    if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
      let price0 := div (mul reserve1Value q112) reserve0Value
      let price1 := div (mul reserve0Value q112) reserve1Value
      let price0Last ← getStorage price0CumulativeLastSlot
      let price1Last ← getStorage price1CumulativeLastSlot
      setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
      setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
    else
      pure ()
    setStorage reserve0Slot balance0After
    setStorage reserve1Slot balance1After
    setStorage blockTimestampLastSlot timestamp32
    setStorage unlockedSlot 1
    return (amount0, amount1)

  function allow_post_interaction_writes swap (amount0Out : Uint256, amount1Out : Uint256, toAddr : Address, data : Bytes) : Unit := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    setStorage unlockedSlot 0
    require (amount0Out > 0 || amount1Out > 0) "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    require (amount0Out < reserve0Value && amount1Out < reserve1Value) "UniswapV2: INSUFFICIENT_LIQUIDITY"
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    require (toAddr != token0Value && toAddr != token1Value) "UniswapV2: INVALID_TO"
    if amount0Out > 0 then
      safeTransfer token0Value toAddr amount0Out
    else
      pure ()
    if amount1Out > 0 then
      safeTransfer token1Value toAddr amount1Out
    else
      pure ()
    let sender ← msgSender
    ecmDo uniswapV2CallbackModule [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out]
    let selfAddr ← Verity.contractAddress
    let balance0Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token0Value, selfAddr]
    let balance1Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token1Value, selfAddr]
    let expected0 := sub reserve0Value amount0Out
    let expected1 := sub reserve1Value amount1Out
    let mut amount0In := 0
    if balance0Now > expected0 then
      amount0In := sub balance0Now expected0
    else
      pure ()
    let mut amount1In := 0
    if balance1Now > expected1 then
      amount1In := sub balance1Now expected1
    else
      pure ()
    require (amount0In > 0 || amount1In > 0) "UniswapV2: INSUFFICIENT_INPUT_AMOUNT"
    let balance0Scaled := mul balance0Now feeDenominator
    require (balance0Now == 0 || div balance0Scaled balance0Now == feeDenominator) "UniswapV2: K_OVERFLOW"
    let balance1Scaled := mul balance1Now feeDenominator
    require (balance1Now == 0 || div balance1Scaled balance1Now == feeDenominator) "UniswapV2: K_OVERFLOW"
    let amount0Fee := mul amount0In feeAdjustment
    require (amount0In == 0 || div amount0Fee amount0In == feeAdjustment) "UniswapV2: K_OVERFLOW"
    let amount1Fee := mul amount1In feeAdjustment
    require (amount1In == 0 || div amount1Fee amount1In == feeAdjustment) "UniswapV2: K_OVERFLOW"
    require (balance0Scaled >= amount0Fee && balance1Scaled >= amount1Fee) "UniswapV2: K"
    let balance0Adjusted := sub balance0Scaled amount0Fee
    let balance1Adjusted := sub balance1Scaled amount1Fee
    let adjustedProduct := mul balance0Adjusted balance1Adjusted
    require (balance0Adjusted == 0 || div adjustedProduct balance0Adjusted == balance1Adjusted) "UniswapV2: K_OVERFLOW"
    let reserveProduct := mul reserve0Value reserve1Value
    require (reserve0Value == 0 || div reserveProduct reserve0Value == reserve1Value) "UniswapV2: K_OVERFLOW"
    let scaleProduct := mul feeDenominator feeDenominator
    require (div scaleProduct feeDenominator == feeDenominator) "UniswapV2: K_OVERFLOW"
    let requiredProduct := mul reserveProduct scaleProduct
    require (reserveProduct == 0 || div requiredProduct reserveProduct == scaleProduct) "UniswapV2: K_OVERFLOW"
    require (adjustedProduct >= requiredProduct) "UniswapV2: K"
    require (balance0Now <= maxUint112 && balance1Now <= maxUint112) "UniswapV2: OVERFLOW"
    let currentTimestamp ← Verity.blockTimestamp
    let timestamp32 := mod currentTimestamp uint32Modulus
    let previousTimestamp ← getStorage blockTimestampLastSlot
    let mut elapsed := 0
    if timestamp32 >= previousTimestamp then
      elapsed := sub timestamp32 previousTimestamp
    else
      elapsed := add (sub uint32Modulus previousTimestamp) timestamp32
    if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
      let price0 := div (mul reserve1Value q112) reserve0Value
      let price1 := div (mul reserve0Value q112) reserve1Value
      let price0Last ← getStorage price0CumulativeLastSlot
      let price1Last ← getStorage price1CumulativeLastSlot
      setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
      setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
    else
      pure ()
    setStorage reserve0Slot balance0Now
    setStorage reserve1Slot balance1Now
    setStorage blockTimestampLastSlot timestamp32
    setStorage unlockedSlot 1

  function allow_post_interaction_writes skim (toAddr : Address) : Unit := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    setStorage unlockedSlot 0
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    let selfAddr ← Verity.contractAddress
    let balance0Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token0Value, selfAddr]
    let balance1Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token1Value, selfAddr]
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    require (balance0Now >= reserve0Value && balance1Now >= reserve1Value) "UniswapV2: INSUFFICIENT_BALANCE"
    safeTransfer token0Value toAddr (sub balance0Now reserve0Value)
    safeTransfer token1Value toAddr (sub balance1Now reserve1Value)
    setStorage unlockedSlot 1

  function allow_post_interaction_writes sync () : Unit := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    setStorage unlockedSlot 0
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    let selfAddr ← Verity.contractAddress
    let balance0Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token0Value, selfAddr]
    let balance1Now ← ecmCall (fun resultVar => Compiler.Modules.ERC20.balanceOfModule resultVar) [token1Value, selfAddr]
    require (balance0Now <= maxUint112 && balance1Now <= maxUint112) "UniswapV2: OVERFLOW"
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    let currentTimestamp ← Verity.blockTimestamp
    let timestamp32 := mod currentTimestamp uint32Modulus
    let previousTimestamp ← getStorage blockTimestampLastSlot
    let mut elapsed := 0
    if timestamp32 >= previousTimestamp then
      elapsed := sub timestamp32 previousTimestamp
    else
      elapsed := add (sub uint32Modulus previousTimestamp) timestamp32
    if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
      let price0 := div (mul reserve1Value q112) reserve0Value
      let price1 := div (mul reserve0Value q112) reserve1Value
      let price0Last ← getStorage price0CumulativeLastSlot
      let price1Last ← getStorage price1CumulativeLastSlot
      setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
      setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
    else
      pure ()
    setStorage reserve0Slot balance0Now
    setStorage reserve1Slot balance1Now
    setStorage blockTimestampLastSlot timestamp32
    setStorage unlockedSlot 1

end TamaUniV2
