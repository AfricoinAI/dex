// SPDX-License-Identifier: AGPL-3.0-only
pragma solidity ^0.8.20;

import {UniswapV2FactoryIface} from "./generated/verity/UniswapV2FactoryIface.sol";
import {UniswapV2PairIface} from "./generated/verity/UniswapV2PairIface.sol";

/// @title Minimal ERC-20 interface
/// @notice ERC-20 transfer surface used by TamaRouter for token movements.
/// @dev Supports tokens that either return true or return no data on success.
interface IERC20Minimal {
    /// @notice Transfers tokens from the caller to another address.
    /// @param to Recipient of the transferred tokens.
    /// @param value Amount of tokens to transfer.
    /// @return True when the token reports a successful transfer.
    function transfer(address to, uint256 value) external returns (bool);

    /// @notice Transfers tokens from an approved owner to another address.
    /// @param from Owner address whose allowance is spent.
    /// @param to Recipient of the transferred tokens.
    /// @param value Amount of tokens to transfer.
    /// @return True when the token reports a successful transfer.
    function transferFrom(address from, address to, uint256 value) external returns (bool);
}

/// @title Minimal wrapped native token interface
/// @notice Wrapped native token surface used for ETH-style router routes.
/// @dev Extends the minimal ERC-20 transfer surface with deposit and withdraw.
interface IWrappedNativeMinimal is IERC20Minimal {
    /// @notice Wraps the native asset sent with the call.
    function deposit() external payable;

    /// @notice Unwraps wrapped native tokens into native asset.
    function withdraw(uint256) external;
}

/// @title TamaRouter
/// @notice Uniswap V2-style router for adding/removing liquidity and swapping through Tama pairs.
/// @dev Uses the configured factory for pair lookup/creation and supports explicit wrapped-native routes.
contract TamaRouter {
    address public immutable factory;
    /// @notice Canonical wrapped-native token this router wraps/unwraps for ETH routes.
    /// @dev Fixed at construction so callers cannot substitute an arbitrary wrapper per call.
    address public immutable WETH;

    /// @dev Reentrancy guard state: 1 = unlocked, 2 = entered.
    uint256 private _locked = 1;

    modifier ensure(uint256 deadline) {
        require(deadline >= block.timestamp, "TamaRouter: EXPIRED");
        _;
    }

    /// @dev Blocks reentrant calls into any mutating entrypoint.
    modifier nonReentrant() {
        require(_locked == 1, "TamaRouter: REENTRANT");
        _locked = 2;
        _;
        _locked = 1;
    }

    /// @notice Creates a router bound to a Uniswap V2-compatible factory and wrapped-native token.
    /// @param factory_ Factory address used to find and create pairs.
    /// @param weth_ Canonical wrapped-native token used for ETH routes.
    constructor(address factory_, address weth_) {
        require(factory_ != address(0), "TamaRouter: ZERO_FACTORY");
        require(weth_ != address(0), "TamaRouter: ZERO_WETH");
        factory = factory_;
        WETH = weth_;
    }

    receive() external payable {}

    /// @notice Sorts two token addresses into canonical pair order.
    /// @param tokenA First token address.
    /// @param tokenB Second token address.
    /// @return token0 Lower-address token.
    /// @return token1 Higher-address token.
    function sortTokens(address tokenA, address tokenB) public pure returns (address token0, address token1) {
        require(tokenA != tokenB, "TamaRouter: IDENTICAL_ADDRESSES");
        (token0, token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
        require(token0 != address(0), "TamaRouter: ZERO_ADDRESS");
    }

    /// @notice Returns the existing pair for two tokens.
    /// @param tokenA First token address.
    /// @param tokenB Second token address.
    /// @return pair Pair address from the factory.
    function pairFor(address tokenA, address tokenB) public view returns (address pair) {
        pair = UniswapV2FactoryIface(factory).getPair(tokenA, tokenB);
        require(pair != address(0), "TamaRouter: PAIR_NOT_FOUND");
    }

    /// @notice Returns pair reserves ordered to match the input token order.
    /// @param tokenA First token address.
    /// @param tokenB Second token address.
    /// @return reserveA Reserve for tokenA.
    /// @return reserveB Reserve for tokenB.
    function getReserves(address tokenA, address tokenB) public view returns (uint256 reserveA, uint256 reserveB) {
        (address token0,) = sortTokens(tokenA, tokenB);
        (uint256 reserve0, uint256 reserve1,) = UniswapV2PairIface(pairFor(tokenA, tokenB)).getReserves();
        (reserveA, reserveB) = tokenA == token0 ? (reserve0, reserve1) : (reserve1, reserve0);
    }

    /// @notice Quotes the equivalent amount of token B for token A at the current reserve ratio.
    /// @param amountA Amount of token A.
    /// @param reserveA Reserve of token A.
    /// @param reserveB Reserve of token B.
    /// @return amountB Equivalent amount of token B.
    function quote(uint256 amountA, uint256 reserveA, uint256 reserveB) public pure returns (uint256 amountB) {
        require(amountA > 0, "TamaRouter: INSUFFICIENT_AMOUNT");
        require(reserveA > 0 && reserveB > 0, "TamaRouter: INSUFFICIENT_LIQUIDITY");
        amountB = (amountA * reserveB) / reserveA;
    }

    /// @notice Computes the maximum output amount for an exact-input swap after the 0.3% fee.
    /// @param amountIn Input token amount.
    /// @param reserveIn Reserve of the input token.
    /// @param reserveOut Reserve of the output token.
    /// @return amountOut Output token amount.
    function getAmountOut(uint256 amountIn, uint256 reserveIn, uint256 reserveOut)
        public
        pure
        returns (uint256 amountOut)
    {
        require(amountIn > 0, "TamaRouter: INSUFFICIENT_INPUT_AMOUNT");
        require(reserveIn > 0 && reserveOut > 0, "TamaRouter: INSUFFICIENT_LIQUIDITY");
        uint256 amountInWithFee = amountIn * 997;
        amountOut = (amountInWithFee * reserveOut) / (reserveIn * 1000 + amountInWithFee);
    }

    /// @notice Computes the required input amount for an exact-output swap after the 0.3% fee.
    /// @param amountOut Desired output token amount.
    /// @param reserveIn Reserve of the input token.
    /// @param reserveOut Reserve of the output token.
    /// @return amountIn Required input token amount.
    function getAmountIn(uint256 amountOut, uint256 reserveIn, uint256 reserveOut)
        public
        pure
        returns (uint256 amountIn)
    {
        require(amountOut > 0, "TamaRouter: INSUFFICIENT_OUTPUT_AMOUNT");
        require(reserveIn > 0 && reserveOut > 0, "TamaRouter: INSUFFICIENT_LIQUIDITY");
        require(amountOut < reserveOut, "TamaRouter: INSUFFICIENT_LIQUIDITY");
        amountIn = (reserveIn * amountOut * 1000) / ((reserveOut - amountOut) * 997) + 1;
    }

    /// @notice Computes all output amounts along a path for an exact-input swap.
    /// @param amountIn Input amount for the first token in the path.
    /// @param path Ordered token path from input token to output token.
    /// @return amounts Input and output amounts for each path token.
    function getAmountsOut(uint256 amountIn, address[] memory path) public view returns (uint256[] memory amounts) {
        require(path.length >= 2, "TamaRouter: INVALID_PATH");
        amounts = new uint256[](path.length);
        amounts[0] = amountIn;
        for (uint256 i = 0; i < path.length - 1; i++) {
            (uint256 reserveIn, uint256 reserveOut) = getReserves(path[i], path[i + 1]);
            amounts[i + 1] = getAmountOut(amounts[i], reserveIn, reserveOut);
        }
    }

    /// @notice Computes all required input amounts along a path for an exact-output swap.
    /// @param amountOut Desired output amount for the last token in the path.
    /// @param path Ordered token path from input token to output token.
    /// @return amounts Input and output amounts for each path token.
    function getAmountsIn(uint256 amountOut, address[] memory path) public view returns (uint256[] memory amounts) {
        require(path.length >= 2, "TamaRouter: INVALID_PATH");
        amounts = new uint256[](path.length);
        amounts[amounts.length - 1] = amountOut;
        for (uint256 i = path.length - 1; i > 0; i--) {
            (uint256 reserveIn, uint256 reserveOut) = getReserves(path[i - 1], path[i]);
            amounts[i - 1] = getAmountIn(amounts[i], reserveIn, reserveOut);
        }
    }

    /// @notice Adds liquidity to a token-token pair, creating the pair if needed.
    /// @param tokenA First token address.
    /// @param tokenB Second token address.
    /// @param amountADesired Desired amount of tokenA to deposit.
    /// @param amountBDesired Desired amount of tokenB to deposit.
    /// @param amountAMin Minimum acceptable amount of tokenA to deposit.
    /// @param amountBMin Minimum acceptable amount of tokenB to deposit.
    /// @param to Recipient of the minted liquidity tokens.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amountA Amount of tokenA deposited.
    /// @return amountB Amount of tokenB deposited.
    /// @return liquidity Amount of liquidity tokens minted.
    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external ensure(deadline) nonReentrant returns (uint256 amountA, uint256 amountB, uint256 liquidity) {
        address pair;
        (amountA, amountB, pair) = _addLiquidity(tokenA, tokenB, amountADesired, amountBDesired, amountAMin, amountBMin);
        _safeTransferFrom(tokenA, msg.sender, pair, amountA);
        _safeTransferFrom(tokenB, msg.sender, pair, amountB);
        liquidity = UniswapV2PairIface(pair).mint(to);
    }

    /// @notice Adds liquidity to a token-wrapped-native pair using native asset input.
    /// @param token ERC-20 token address paired with the wrapped native token.
    /// @param amountTokenDesired Desired amount of token to deposit.
    /// @param amountTokenMin Minimum acceptable amount of token to deposit.
    /// @param amountETHMin Minimum acceptable amount of native asset to wrap and deposit.
    /// @param to Recipient of the minted liquidity tokens.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amountToken Amount of token deposited.
    /// @return amountETH Amount of native asset wrapped and deposited.
    /// @return liquidity Amount of liquidity tokens minted.
    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external payable ensure(deadline) nonReentrant returns (uint256 amountToken, uint256 amountETH, uint256 liquidity) {
        address pair;
        (amountToken, amountETH, pair) =
            _addLiquidity(token, WETH, amountTokenDesired, msg.value, amountTokenMin, amountETHMin);
        _safeTransferFrom(token, msg.sender, pair, amountToken);
        _depositWrappedNative(WETH, amountETH);
        _safeTransfer(WETH, pair, amountETH);
        liquidity = UniswapV2PairIface(pair).mint(to);
        if (msg.value > amountETH) _safeTransferETH(msg.sender, msg.value - amountETH);
    }

    /// @notice Removes liquidity from a token-token pair.
    /// @param tokenA First token address.
    /// @param tokenB Second token address.
    /// @param liquidity Amount of liquidity tokens to burn.
    /// @param amountAMin Minimum acceptable amount of tokenA to receive.
    /// @param amountBMin Minimum acceptable amount of tokenB to receive.
    /// @param to Recipient of the withdrawn tokens.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amountA Amount of tokenA received.
    /// @return amountB Amount of tokenB received.
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external ensure(deadline) nonReentrant returns (uint256 amountA, uint256 amountB) {
        (amountA, amountB) = _removeLiquidity(tokenA, tokenB, liquidity, amountAMin, amountBMin, to);
    }

    /// @notice Removes liquidity from a token-wrapped-native pair and unwraps native asset to the recipient.
    /// @param token ERC-20 token address paired with the wrapped native token.
    /// @param liquidity Amount of liquidity tokens to burn.
    /// @param amountTokenMin Minimum acceptable amount of token to receive.
    /// @param amountETHMin Minimum acceptable amount of native asset to receive.
    /// @param to Recipient of the withdrawn token and native asset.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amountToken Amount of token received.
    /// @return amountETH Amount of native asset received.
    function removeLiquidityETH(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external ensure(deadline) nonReentrant returns (uint256 amountToken, uint256 amountETH) {
        (amountToken, amountETH) = _removeLiquidity(token, WETH, liquidity, amountTokenMin, amountETHMin, address(this));
        _safeTransfer(token, to, amountToken);
        _withdrawWrappedNative(WETH, amountETH);
        _safeTransferETH(to, amountETH);
    }

    /// @notice Pulls liquidity tokens, burns them, and checks minimum token outputs.
    /// @param tokenA First token address.
    /// @param tokenB Second token address.
    /// @param liquidity Amount of liquidity tokens to burn.
    /// @param amountAMin Minimum acceptable amount of tokenA to receive.
    /// @param amountBMin Minimum acceptable amount of tokenB to receive.
    /// @param to Recipient passed to the pair burn.
    /// @return amountA Amount of tokenA received.
    /// @return amountB Amount of tokenB received.
    function _removeLiquidity(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to
    ) internal returns (uint256 amountA, uint256 amountB) {
        address pair = pairFor(tokenA, tokenB);
        _safeTransferFrom(pair, msg.sender, pair, liquidity);
        (uint256 amount0, uint256 amount1) = UniswapV2PairIface(pair).burn(to);
        (address token0,) = sortTokens(tokenA, tokenB);
        (amountA, amountB) = tokenA == token0 ? (amount0, amount1) : (amount1, amount0);
        require(amountA >= amountAMin, "TamaRouter: INSUFFICIENT_A_AMOUNT");
        require(amountB >= amountBMin, "TamaRouter: INSUFFICIENT_B_AMOUNT");
    }

    /// @notice Swaps an exact amount of input tokens for as many output tokens as possible.
    /// @param amountIn Exact amount of the input token to spend.
    /// @param amountOutMin Minimum acceptable amount of the final output token.
    /// @param path Ordered token path from input token to output token.
    /// @param to Recipient of the final output tokens.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amounts Input and output amounts for each path token.
    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external ensure(deadline) nonReentrant returns (uint256[] memory amounts) {
        amounts = getAmountsOut(amountIn, path);
        require(amounts[amounts.length - 1] >= amountOutMin, "TamaRouter: INSUFFICIENT_OUTPUT_AMOUNT");
        _safeTransferFrom(path[0], msg.sender, pairFor(path[0], path[1]), amounts[0]);
        _swap(amounts, path, to);
    }

    /// @notice Swaps as few input tokens as needed for an exact amount of output tokens.
    /// @param amountOut Exact amount of the final output token to receive.
    /// @param amountInMax Maximum acceptable amount of the input token to spend.
    /// @param path Ordered token path from input token to output token.
    /// @param to Recipient of the final output tokens.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amounts Input and output amounts for each path token.
    function swapTokensForExactTokens(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external ensure(deadline) nonReentrant returns (uint256[] memory amounts) {
        amounts = getAmountsIn(amountOut, path);
        require(amounts[0] <= amountInMax, "TamaRouter: EXCESSIVE_INPUT_AMOUNT");
        _safeTransferFrom(path[0], msg.sender, pairFor(path[0], path[1]), amounts[0]);
        _swap(amounts, path, to);
    }

    /// @notice Swaps an exact native asset amount for as many output tokens as possible.
    /// @param amountOutMin Minimum acceptable amount of the final output token.
    /// @param path Ordered token path beginning with the wrapped native token.
    /// @param to Recipient of the final output tokens.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amounts Input and output amounts for each path token.
    function swapExactETHForTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable ensure(deadline) nonReentrant returns (uint256[] memory amounts) {
        require(path.length >= 2, "TamaRouter: INVALID_PATH");
        require(path[0] == WETH, "TamaRouter: INVALID_PATH");
        amounts = getAmountsOut(msg.value, path);
        require(amounts[amounts.length - 1] >= amountOutMin, "TamaRouter: INSUFFICIENT_OUTPUT_AMOUNT");
        _depositWrappedNative(WETH, amounts[0]);
        _safeTransfer(WETH, pairFor(path[0], path[1]), amounts[0]);
        _swap(amounts, path, to);
    }

    /// @notice Swaps as few input tokens as needed for an exact native asset output.
    /// @param amountOut Exact amount of native asset to receive.
    /// @param amountInMax Maximum acceptable amount of the input token to spend.
    /// @param path Ordered token path ending with the wrapped native token.
    /// @param to Recipient of the native asset output.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amounts Input and output amounts for each path token.
    function swapTokensForExactETH(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external ensure(deadline) nonReentrant returns (uint256[] memory amounts) {
        require(path.length >= 2, "TamaRouter: INVALID_PATH");
        require(path[path.length - 1] == WETH, "TamaRouter: INVALID_PATH");
        amounts = getAmountsIn(amountOut, path);
        require(amounts[0] <= amountInMax, "TamaRouter: EXCESSIVE_INPUT_AMOUNT");
        _safeTransferFrom(path[0], msg.sender, pairFor(path[0], path[1]), amounts[0]);
        _swap(amounts, path, address(this));
        _withdrawWrappedNative(WETH, amounts[amounts.length - 1]);
        _safeTransferETH(to, amounts[amounts.length - 1]);
    }

    /// @notice Swaps an exact token amount for as much native asset as possible.
    /// @param amountIn Exact amount of the input token to spend.
    /// @param amountOutMin Minimum acceptable amount of native asset to receive.
    /// @param path Ordered token path ending with the wrapped native token.
    /// @param to Recipient of the native asset output.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amounts Input and output amounts for each path token.
    function swapExactTokensForETH(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external ensure(deadline) nonReentrant returns (uint256[] memory amounts) {
        require(path.length >= 2, "TamaRouter: INVALID_PATH");
        require(path[path.length - 1] == WETH, "TamaRouter: INVALID_PATH");
        amounts = getAmountsOut(amountIn, path);
        require(amounts[amounts.length - 1] >= amountOutMin, "TamaRouter: INSUFFICIENT_OUTPUT_AMOUNT");
        _safeTransferFrom(path[0], msg.sender, pairFor(path[0], path[1]), amounts[0]);
        _swap(amounts, path, address(this));
        _withdrawWrappedNative(WETH, amounts[amounts.length - 1]);
        _safeTransferETH(to, amounts[amounts.length - 1]);
    }

    /// @notice Swaps native asset for an exact amount of output tokens and refunds excess native asset.
    /// @param amountOut Exact amount of the final output token to receive.
    /// @param path Ordered token path beginning with the wrapped native token.
    /// @param to Recipient of the final output tokens.
    /// @param deadline Latest timestamp at which the transaction may execute.
    /// @return amounts Input and output amounts for each path token.
    function swapETHForExactTokens(
        uint256 amountOut,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable ensure(deadline) nonReentrant returns (uint256[] memory amounts) {
        require(path.length >= 2, "TamaRouter: INVALID_PATH");
        require(path[0] == WETH, "TamaRouter: INVALID_PATH");
        amounts = getAmountsIn(amountOut, path);
        require(amounts[0] <= msg.value, "TamaRouter: EXCESSIVE_INPUT_AMOUNT");
        _depositWrappedNative(WETH, amounts[0]);
        _safeTransfer(WETH, pairFor(path[0], path[1]), amounts[0]);
        _swap(amounts, path, to);
        if (msg.value > amounts[0]) _safeTransferETH(msg.sender, msg.value - amounts[0]);
    }

    /// @notice Determines optimal deposit amounts and creates the pair if it does not exist.
    /// @param tokenA First token address.
    /// @param tokenB Second token address.
    /// @param amountADesired Desired amount of tokenA to deposit.
    /// @param amountBDesired Desired amount of tokenB to deposit.
    /// @param amountAMin Minimum acceptable amount of tokenA to deposit.
    /// @param amountBMin Minimum acceptable amount of tokenB to deposit.
    /// @return amountA Amount of tokenA to deposit.
    /// @return amountB Amount of tokenB to deposit.
    /// @return pair Pair address used for the liquidity deposit.
    function _addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin
    ) internal returns (uint256 amountA, uint256 amountB, address pair) {
        pair = UniswapV2FactoryIface(factory).getPair(tokenA, tokenB);
        if (pair == address(0)) {
            pair = UniswapV2FactoryIface(factory).createPair(tokenA, tokenB);
        }
        (address token0,) = sortTokens(tokenA, tokenB);
        (uint256 reserve0, uint256 reserve1,) = UniswapV2PairIface(pair).getReserves();
        (uint256 reserveA, uint256 reserveB) = tokenA == token0 ? (reserve0, reserve1) : (reserve1, reserve0);
        if (reserveA == 0 && reserveB == 0) {
            (amountA, amountB) = (amountADesired, amountBDesired);
        } else {
            uint256 amountBOptimal = quote(amountADesired, reserveA, reserveB);
            if (amountBOptimal <= amountBDesired) {
                require(amountBOptimal >= amountBMin, "TamaRouter: INSUFFICIENT_B_AMOUNT");
                (amountA, amountB) = (amountADesired, amountBOptimal);
            } else {
                uint256 amountAOptimal = quote(amountBDesired, reserveB, reserveA);
                require(amountAOptimal <= amountADesired, "TamaRouter: EXCESSIVE_A_AMOUNT");
                require(amountAOptimal >= amountAMin, "TamaRouter: INSUFFICIENT_A_AMOUNT");
                (amountA, amountB) = (amountAOptimal, amountBDesired);
            }
        }
        require(amountA >= amountAMin, "TamaRouter: INSUFFICIENT_A_AMOUNT");
        require(amountB >= amountBMin, "TamaRouter: INSUFFICIENT_B_AMOUNT");
    }

    /// @notice Executes a multi-hop swap after the initial input has been sent to the first pair.
    /// @param amounts Input and output amounts for each path token.
    /// @param path Ordered token path from input token to output token.
    /// @param to Recipient of the final output tokens.
    function _swap(uint256[] memory amounts, address[] calldata path, address to) internal {
        for (uint256 i = 0; i < path.length - 1; i++) {
            (address input, address output) = (path[i], path[i + 1]);
            (address token0,) = sortTokens(input, output);
            uint256 amountOut = amounts[i + 1];
            (uint256 amount0Out, uint256 amount1Out) =
                input == token0 ? (uint256(0), amountOut) : (amountOut, uint256(0));
            address nextTo = i < path.length - 2 ? pairFor(output, path[i + 2]) : to;
            UniswapV2PairIface(pairFor(input, output)).swap(amount0Out, amount1Out, nextTo, "");
        }
    }

    /// @notice Performs a low-level ERC-20 transferFrom and accepts empty or true return data.
    /// @param token Token contract to call.
    /// @param from Token owner address.
    /// @param to Token recipient address.
    /// @param value Amount of tokens to transfer.
    function _safeTransferFrom(address token, address from, address to, uint256 value) internal {
        require(token.code.length > 0, "TamaRouter: NON_CONTRACT_TOKEN");
        (bool success, bytes memory data) = token.call(abi.encodeCall(IERC20Minimal.transferFrom, (from, to, value)));
        require(success && (data.length == 0 || abi.decode(data, (bool))), "TamaRouter: TRANSFER_FROM_FAILED");
    }

    /// @notice Performs a low-level ERC-20 transfer and accepts empty or true return data.
    /// @param token Token contract to call.
    /// @param to Token recipient address.
    /// @param value Amount of tokens to transfer.
    function _safeTransfer(address token, address to, uint256 value) internal {
        require(token.code.length > 0, "TamaRouter: NON_CONTRACT_TOKEN");
        (bool success, bytes memory data) = token.call(abi.encodeCall(IERC20Minimal.transfer, (to, value)));
        require(success && (data.length == 0 || abi.decode(data, (bool))), "TamaRouter: TRANSFER_FAILED");
    }

    /// @notice Wraps native asset into the wrapped native token.
    /// @param weth Wrapped native token address.
    /// @param value Amount of native asset to wrap.
    function _depositWrappedNative(address weth, uint256 value) internal {
        require(weth.code.length > 0, "TamaRouter: NON_CONTRACT_WETH");
        IWrappedNativeMinimal(weth).deposit{value: value}();
    }

    /// @notice Unwraps wrapped native tokens and verifies the router received the native asset.
    /// @param weth Wrapped native token address.
    /// @param value Amount of wrapped native tokens to unwrap.
    function _withdrawWrappedNative(address weth, uint256 value) internal {
        require(weth.code.length > 0, "TamaRouter: NON_CONTRACT_WETH");
        uint256 balanceBefore = address(this).balance;
        IWrappedNativeMinimal(weth).withdraw(value);
        require(address(this).balance >= balanceBefore + value, "TamaRouter: WETH_WITHDRAW_FAILED");
    }

    /// @notice Sends native asset from the router.
    /// @param to Recipient of the native asset.
    /// @param value Amount of native asset to send.
    function _safeTransferETH(address to, uint256 value) internal {
        (bool success,) = to.call{value: value}("");
        require(success, "TamaRouter: ETH_TRANSFER_FAILED");
    }
}
