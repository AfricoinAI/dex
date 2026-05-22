import Contracts.Common
import Compiler.ECM
import Compiler.CompilationModel
import Compiler.Modules.ERC20
import Tamago.Common.Events
import Tamago.Utils.FixedPointMathLib

namespace TamaUniV2

open Verity hiding pure bind
open Contracts
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Compiler.CompilationModel
open Compiler.Yul
open Compiler.ECM
open Tamago.Utils

namespace UniswapV2PairEvents

def indexedAddress (name : String) : EventParam :=
  { name := name, ty := ParamType.address, kind := EventParamKind.indexed }

def address (name : String) : EventParam :=
  { name := name, ty := ParamType.address, kind := EventParamKind.unindexed }

def uint256 (name : String) : EventParam :=
  { name := name, ty := ParamType.uint256, kind := EventParamKind.unindexed }

def uint112 (name : String) : EventParam :=
  { name := name, ty := ParamType.newtypeOf "uint112" ParamType.uint256, kind := EventParamKind.unindexed }

def syncTopic0 : Uint256 :=
  0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1

def mint : EventDef :=
  { name := "Mint"
    params := [
      indexedAddress "sender",
      uint256 "amount0",
      uint256 "amount1"
    ] }

def burn : EventDef :=
  { name := "Burn"
    params := [
      indexedAddress "sender",
      uint256 "amount0",
      uint256 "amount1",
      indexedAddress "to"
    ] }

def swap : EventDef :=
  { name := "Swap"
    params := [
      indexedAddress "sender",
      uint256 "amount0In",
      uint256 "amount1In",
      uint256 "amount0Out",
      uint256 "amount1Out",
      indexedAddress "to"
    ] }

def sync : EventDef :=
  { name := "Sync"
    params := [
      uint112 "reserve0",
      uint112 "reserve1"
    ] }

end UniswapV2PairEvents

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

def erc20BalanceOf (token owner : Address) : Contract Uint256 :=
  Contracts.balanceOf token owner

def pairTokenSafeTransferEvent
    (token fromAddr toAddr : Address) (amount : Uint256) : Event :=
  {
    name := "UniswapV2PairTokenSafeTransfer",
    args := [addressToWord token, addressToWord fromAddr, addressToWord toAddr, amount],
    indexedArgs := []
  }

def tracePairTokenSafeTransfer
    (token toAddr : Address) (amount : Uint256) : Contract Unit :=
  fun state =>
    ContractResult.success () { state with
      events :=
        state.events ++
          [pairTokenSafeTransferEvent token state.thisAddress toAddr amount]
    }

def pairSafeTransfer (token toAddr : Address) (amount : Uint256) : Contract Uint256 := do
  Contracts.safeTransfer token toAddr amount
  tracePairTokenSafeTransfer token toAddr amount
  return 1

def erc20BalanceOf_model : FunctionSpec := {
  name := "erc20BalanceOf"
  params := [
    { name := "token", ty := ParamType.address },
    { name := "owner", ty := ParamType.address }
  ]
  returnType := some FieldType.uint256
  returns := [ParamType.uint256]
  body := [
    Stmt.ecm (Compiler.Modules.ERC20.balanceOfModule "erc20BalanceResult") [
      Expr.param "token",
      Expr.param "owner"
    ],
    Stmt.return (Expr.localVar "erc20BalanceResult")
  ]
}

def pairSafeTransfer_model : FunctionSpec := {
  name := "pairSafeTransfer"
  params := [
    { name := "token", ty := ParamType.address },
    { name := "toAddr", ty := ParamType.address },
    { name := "amount", ty := ParamType.uint256 }
  ]
  returnType := some FieldType.uint256
  returns := [ParamType.uint256]
  body := [
    Stmt.ecm Compiler.Modules.ERC20.safeTransferModule [
      Expr.param "token",
      Expr.param "toAddr",
      Expr.param "amount"
    ],
    Stmt.return (Expr.literal 1)
  ]
}

verity_contract UniswapV2PairBase where
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
    maxUint256 : Uint256 := (sub 0 1)

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
    emit "Approval" [addressToWord sender, addressToWord spender, amount]
    return true

  function transfer (toAddr : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let senderBalance ← getMapping balancesSlot sender
    require (senderBalance >= amount) "UniswapV2: INSUFFICIENT_BALANCE"
    if sender == toAddr then
      pure ()
    else
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance amount) "UniswapV2: BALANCE_OVERFLOW"
      setMapping balancesSlot sender (sub senderBalance amount)
      setMapping balancesSlot toAddr newToBalance
    emit "Transfer" [addressToWord sender, addressToWord toAddr, amount]
    return true

  function transferFrom (fromAddr : Address, toAddr : Address, amount : Uint256) : Bool := do
    let spender ← msgSender
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
    emit "Transfer" [addressToWord fromAddr, addressToWord toAddr, amount]
    return true

  function allow_post_interaction_writes mint (toAddr : Address) : Uint256 := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    setStorage unlockedSlot 0
    let sender ← msgSender
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    let selfAddr ← Verity.contractAddress
    let balance0Now ← TamaUniV2.erc20BalanceOf token0Value selfAddr
    let balance1Now ← TamaUniV2.erc20BalanceOf token1Value selfAddr
    require (balance0Now <= maxUint112 && balance1Now <= maxUint112) "UniswapV2: OVERFLOW"
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    require (balance0Now >= reserve0Value && balance1Now >= reserve1Value) "UniswapV2: INSUFFICIENT_AMOUNT"
    let amount0 := sub balance0Now reserve0Value
    let amount1 := sub balance1Now reserve1Value
    require (amount0 > 0 && amount1 > 0) "UniswapV2: INSUFFICIENT_AMOUNT"
    let supply ← getStorage totalSupplySlot
    if supply == 0 then
      let product := mul amount0 amount1
      require (amount0 == 0 || div product amount0 == amount1) "UniswapV2: MINT_OVERFLOW"
      let root ← FixedPointMathLibBase.sqrt product
      require (root > minimumLiquidity) "UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED"
      let liquidity := sub root minimumLiquidity
      setStorage totalSupplySlot root
      setMapping balancesSlot zeroAddress minimumLiquidity
      emit "Transfer" [addressToWord zeroAddress, addressToWord zeroAddress, minimumLiquidity]
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance liquidity) "UniswapV2: BALANCE_OVERFLOW"
      setMapping balancesSlot toAddr newToBalance
      emit "Transfer" [addressToWord zeroAddress, addressToWord toAddr, liquidity]
      let currentTimestamp ← Verity.blockTimestamp
      let timestamp32 := mod currentTimestamp uint32Modulus
      let previousTimestamp ← getStorage blockTimestampLastSlot
      if timestamp32 != previousTimestamp then
        let elapsed := mod (sub (add timestamp32 uint32Modulus) previousTimestamp) uint32Modulus
        if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
          let price0 := div (mul reserve1Value q112) reserve0Value
          let price1 := div (mul reserve0Value q112) reserve1Value
          let price0Last ← getStorage price0CumulativeLastSlot
          let price1Last ← getStorage price1CumulativeLastSlot
          setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
          setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
        else
          pure ()
      else
        pure ()
      setStorage reserve0Slot balance0Now
      setStorage reserve1Slot balance1Now
      setStorage blockTimestampLastSlot timestamp32
      unsafe "emit canonical Uniswap V2 Sync(uint112,uint112) log" do
        mstore 0 balance0Now
        mstore 32 balance1Now
        rawLog [0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1] 0 64
      emit "Mint" [addressToWord sender, amount0, amount1]
      setStorage unlockedSlot 1
      return liquidity
    else
      require (reserve0Value > 0 && reserve1Value > 0) "UniswapV2: INSUFFICIENT_LIQUIDITY"
      let liq0Product := mul amount0 supply
      require (amount0 == 0 || div liq0Product amount0 == supply) "UniswapV2: MINT_OVERFLOW"
      let liq1Product := mul amount1 supply
      require (amount1 == 0 || div liq1Product amount1 == supply) "UniswapV2: MINT_OVERFLOW"
      let liq0 := div liq0Product reserve0Value
      let liq1 := div liq1Product reserve1Value
      let liquidity := min liq0 liq1
      require (liquidity > 0) "UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED"
      let newSupply ← requireSomeUint (safeAdd supply liquidity) "UniswapV2: SUPPLY_OVERFLOW"
      let toBalance ← getMapping balancesSlot toAddr
      let newToBalance ← requireSomeUint (safeAdd toBalance liquidity) "UniswapV2: BALANCE_OVERFLOW"
      setStorage totalSupplySlot newSupply
      setMapping balancesSlot toAddr newToBalance
      emit "Transfer" [addressToWord zeroAddress, addressToWord toAddr, liquidity]
      let currentTimestamp ← Verity.blockTimestamp
      let timestamp32 := mod currentTimestamp uint32Modulus
      let previousTimestamp ← getStorage blockTimestampLastSlot
      if timestamp32 != previousTimestamp then
        let elapsed := mod (sub (add timestamp32 uint32Modulus) previousTimestamp) uint32Modulus
        if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
          let price0 := div (mul reserve1Value q112) reserve0Value
          let price1 := div (mul reserve0Value q112) reserve1Value
          let price0Last ← getStorage price0CumulativeLastSlot
          let price1Last ← getStorage price1CumulativeLastSlot
          setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
          setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
        else
          pure ()
      else
        pure ()
      setStorage reserve0Slot balance0Now
      setStorage reserve1Slot balance1Now
      setStorage blockTimestampLastSlot timestamp32
      unsafe "emit canonical Uniswap V2 Sync(uint112,uint112) log" do
        mstore 0 balance0Now
        mstore 32 balance1Now
        rawLog [0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1] 0 64
      emit "Mint" [addressToWord sender, amount0, amount1]
      setStorage unlockedSlot 1
      return liquidity

  function allow_post_interaction_writes burn (toAddr : Address) : Tuple [Uint256, Uint256] := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    let currentTimestamp ← Verity.blockTimestamp
    let timestamp32 := mod currentTimestamp uint32Modulus
    let previousTimestamp ← getStorage blockTimestampLastSlot
    setStorage unlockedSlot 0
    let sender ← msgSender
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    let selfAddr ← Verity.contractAddress
    let balance0Now ← TamaUniV2.erc20BalanceOf token0Value selfAddr
    let balance1Now ← TamaUniV2.erc20BalanceOf token1Value selfAddr
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
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    setMapping balancesSlot selfAddr 0
    setStorage totalSupplySlot (sub supply liquidity)
    emit "Transfer" [addressToWord selfAddr, addressToWord zeroAddress, liquidity]
    let _transfer0Done ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0
    let _transfer1Done ← TamaUniV2.pairSafeTransfer token1Value toAddr amount1
    let balance0After ← TamaUniV2.erc20BalanceOf token0Value selfAddr
    let balance1After ← TamaUniV2.erc20BalanceOf token1Value selfAddr
    require (balance0After <= maxUint112 && balance1After <= maxUint112) "UniswapV2: OVERFLOW"
    unsafe "restore free memory pointer before native events after ERC20 transfer ECMs" do
      mstore 64 128
    if timestamp32 != previousTimestamp then
      let elapsed := mod (sub (add timestamp32 uint32Modulus) previousTimestamp) uint32Modulus
      if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
        let price0 := div (mul reserve1Value q112) reserve0Value
        let price1 := div (mul reserve0Value q112) reserve1Value
        let price0Last ← getStorage price0CumulativeLastSlot
        let price1Last ← getStorage price1CumulativeLastSlot
        setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
        setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
      else
        pure ()
    else
      pure ()
    setStorage reserve0Slot balance0After
    setStorage reserve1Slot balance1After
    setStorage blockTimestampLastSlot timestamp32
    unsafe "emit canonical Uniswap V2 Sync(uint112,uint112) log" do
      mstore 0 balance0After
      mstore 32 balance1After
      rawLog [0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1] 0 64
    emit "Burn" [addressToWord sender, amount0, amount1, addressToWord toAddr]
    setStorage unlockedSlot 1
    return (amount0, amount1)

  function allow_post_interaction_writes swap (amount0Out : Uint256, amount1Out : Uint256, toAddr : Address, data : Bytes) : Unit := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    let currentTimestamp ← Verity.blockTimestamp
    let timestamp32 := mod currentTimestamp uint32Modulus
    let previousTimestamp ← getStorage blockTimestampLastSlot
    require (amount0Out > 0 || amount1Out > 0) "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT"
    setStorage unlockedSlot 0
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    require (amount0Out < reserve0Value && amount1Out < reserve1Value) "UniswapV2: INSUFFICIENT_LIQUIDITY"
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    require (toAddr != token0Value && toAddr != token1Value) "UniswapV2: INVALID_TO"
    if amount0Out > 0 then
      let _transfer0Done ← TamaUniV2.pairSafeTransfer token0Value toAddr amount0Out
    else
      pure ()
    if amount1Out > 0 then
      let _transfer1Done ← TamaUniV2.pairSafeTransfer token1Value toAddr amount1Out
    else
      pure ()
    let sender ← msgSender
    ecmDo uniswapV2CallbackModule [addressToWord toAddr, addressToWord sender, amount0Out, amount1Out]
    let selfAddr ← Verity.contractAddress
    let balance0Now ← TamaUniV2.erc20BalanceOf token0Value selfAddr
    let balance1Now ← TamaUniV2.erc20BalanceOf token1Value selfAddr
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
    unsafe "restore free memory pointer before native events after callback/transfer ECMs" do
      mstore 64 128
    if timestamp32 != previousTimestamp then
      let elapsed := mod (sub (add timestamp32 uint32Modulus) previousTimestamp) uint32Modulus
      if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
        let price0 := div (mul reserve1Value q112) reserve0Value
        let price1 := div (mul reserve0Value q112) reserve1Value
        let price0Last ← getStorage price0CumulativeLastSlot
        let price1Last ← getStorage price1CumulativeLastSlot
        setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
        setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
      else
        pure ()
    else
      pure ()
    setStorage reserve0Slot balance0Now
    setStorage reserve1Slot balance1Now
    setStorage blockTimestampLastSlot timestamp32
    unsafe "emit canonical Uniswap V2 Sync(uint112,uint112) log" do
      mstore 0 balance0Now
      mstore 32 balance1Now
      rawLog [0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1] 0 64
    emit "Swap" [
      addressToWord sender,
      amount0In,
      amount1In,
      amount0Out,
      amount1Out,
      addressToWord toAddr
    ]
    setStorage unlockedSlot 1

  function allow_post_interaction_writes skim (toAddr : Address) : Unit := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    setStorage unlockedSlot 0
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    let selfAddr ← Verity.contractAddress
    let balance0Now ← TamaUniV2.erc20BalanceOf token0Value selfAddr
    let balance1Now ← TamaUniV2.erc20BalanceOf token1Value selfAddr
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    require (balance0Now >= reserve0Value && balance1Now >= reserve1Value) "UniswapV2: INSUFFICIENT_BALANCE"
    let _transfer0Done ← TamaUniV2.pairSafeTransfer token0Value toAddr (sub balance0Now reserve0Value)
    let _transfer1Done ← TamaUniV2.pairSafeTransfer token1Value toAddr (sub balance1Now reserve1Value)
    setStorage unlockedSlot 1

  function allow_post_interaction_writes sync () : Unit := do
    let lockValue ← getStorage unlockedSlot
    require (lockValue == 1) "UniswapV2: LOCKED"
    let currentTimestamp ← Verity.blockTimestamp
    let timestamp32 := mod currentTimestamp uint32Modulus
    let previousTimestamp ← getStorage blockTimestampLastSlot
    setStorage unlockedSlot 0
    let token0Value ← getStorageAddr token0Slot
    let token1Value ← getStorageAddr token1Slot
    let selfAddr ← Verity.contractAddress
    let balance0Now ← TamaUniV2.erc20BalanceOf token0Value selfAddr
    let balance1Now ← TamaUniV2.erc20BalanceOf token1Value selfAddr
    require (balance0Now <= maxUint112 && balance1Now <= maxUint112) "UniswapV2: OVERFLOW"
    let reserve0Value ← getStorage reserve0Slot
    let reserve1Value ← getStorage reserve1Slot
    if timestamp32 != previousTimestamp then
      let elapsed := mod (sub (add timestamp32 uint32Modulus) previousTimestamp) uint32Modulus
      if elapsed > 0 && reserve0Value > 0 && reserve1Value > 0 then
        let price0 := div (mul reserve1Value q112) reserve0Value
        let price1 := div (mul reserve0Value q112) reserve1Value
        let price0Last ← getStorage price0CumulativeLastSlot
        let price1Last ← getStorage price1CumulativeLastSlot
        setStorage price0CumulativeLastSlot (add price0Last (mul price0 elapsed))
        setStorage price1CumulativeLastSlot (add price1Last (mul price1 elapsed))
      else
        pure ()
    else
      pure ()
    setStorage reserve0Slot balance0Now
    setStorage reserve1Slot balance1Now
    setStorage blockTimestampLastSlot timestamp32
    unsafe "emit canonical Uniswap V2 Sync(uint112,uint112) log" do
      mstore 0 balance0Now
      mstore 32 balance1Now
      rawLog [0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1] 0 64
    setStorage unlockedSlot 1

namespace UniswapV2Pair

abbrev factorySlot := UniswapV2PairBase.factorySlot
abbrev token0Slot := UniswapV2PairBase.token0Slot
abbrev token1Slot := UniswapV2PairBase.token1Slot
abbrev reserve0Slot := UniswapV2PairBase.reserve0Slot
abbrev reserve1Slot := UniswapV2PairBase.reserve1Slot
abbrev blockTimestampLastSlot := UniswapV2PairBase.blockTimestampLastSlot
abbrev price0CumulativeLastSlot := UniswapV2PairBase.price0CumulativeLastSlot
abbrev price1CumulativeLastSlot := UniswapV2PairBase.price1CumulativeLastSlot
abbrev totalSupplySlot := UniswapV2PairBase.totalSupplySlot
abbrev balancesSlot := UniswapV2PairBase.balancesSlot
abbrev allowancesSlot := UniswapV2PairBase.allowancesSlot
abbrev unlockedSlot := UniswapV2PairBase.unlockedSlot

abbrev minimumLiquidity := UniswapV2PairBase.minimumLiquidity
abbrev feeDenominator := UniswapV2PairBase.feeDenominator
abbrev feeAdjustment := UniswapV2PairBase.feeAdjustment
abbrev maxUint112 := UniswapV2PairBase.maxUint112
abbrev q112 := UniswapV2PairBase.q112
abbrev uint32Modulus := UniswapV2PairBase.uint32Modulus
abbrev maxUint256 := UniswapV2PairBase.maxUint256

abbrev decimals := UniswapV2PairBase.decimals
abbrev totalSupply := UniswapV2PairBase.totalSupply
abbrev balanceOf := UniswapV2PairBase.balanceOf
abbrev allowance := UniswapV2PairBase.allowance
abbrev factory := UniswapV2PairBase.factory
abbrev token0 := UniswapV2PairBase.token0
abbrev token1 := UniswapV2PairBase.token1
abbrev MINIMUM_LIQUIDITY := UniswapV2PairBase.MINIMUM_LIQUIDITY
abbrev getReserves := UniswapV2PairBase.getReserves
abbrev price0CumulativeLast := UniswapV2PairBase.price0CumulativeLast
abbrev price1CumulativeLast := UniswapV2PairBase.price1CumulativeLast
abbrev kLast := UniswapV2PairBase.kLast
abbrev «initialize» := UniswapV2PairBase.«initialize»
abbrev approve := UniswapV2PairBase.approve
abbrev transfer := UniswapV2PairBase.transfer
abbrev transferFrom := UniswapV2PairBase.transferFrom
abbrev mint := UniswapV2PairBase.mint
abbrev burn := UniswapV2PairBase.burn
abbrev swap := UniswapV2PairBase.swap
abbrev skim := UniswapV2PairBase.skim
abbrev sync := UniswapV2PairBase.sync

def spec : CompilationModel :=
  { UniswapV2PairBase.spec with
    name := "UniswapV2Pair"
    events := [
      Tamago.Common.Events.transfer,
      Tamago.Common.Events.approval,
      UniswapV2PairEvents.mint,
      UniswapV2PairEvents.burn,
      UniswapV2PairEvents.swap,
      UniswapV2PairEvents.sync
    ] }

end UniswapV2Pair

end TamaUniV2
