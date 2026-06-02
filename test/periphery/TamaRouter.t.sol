// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {TamaRouter} from "../../src/TamaRouter.sol";
import {UniswapV2FactoryDeployer} from "../../src/generated/verity/UniswapV2FactoryDeployer.sol";
import {UniswapV2FactoryIface} from "../../src/generated/verity/UniswapV2FactoryIface.sol";
import {UniswapV2PairIface} from "../../src/generated/verity/UniswapV2PairIface.sol";
import {MockERC20} from "../verity/UniswapV2Helpers.sol";

contract MockWETH is MockERC20 {
    string public constant name = "Wrapped Ether";
    string public constant symbol = "WETH";
    uint8 public constant decimals = 18;

    event Deposit(address indexed dst, uint256 wad);
    event Withdrawal(address indexed src, uint256 wad);

    function deposit() external payable {
        balanceOf[msg.sender] += msg.value;
        totalSupply += msg.value;
        emit Deposit(msg.sender, msg.value);
        emit Transfer(address(0), msg.sender, msg.value);
    }

    function withdraw(uint256 amount) external {
        require(balanceOf[msg.sender] >= amount, "BALANCE");
        balanceOf[msg.sender] -= amount;
        totalSupply -= amount;
        emit Transfer(msg.sender, address(0), amount);
        emit Withdrawal(msg.sender, amount);
        payable(msg.sender).transfer(amount);
    }

    receive() external payable {
        this.deposit{value: msg.value}();
    }
}

contract FakeWETH is MockERC20 {
    function deposit() external payable {
        balanceOf[msg.sender] += msg.value;
        totalSupply += msg.value;
        emit Transfer(address(0), msg.sender, msg.value);
    }

    function withdraw(uint256) external pure {}
}

/// @dev Reenters the router from its ETH-refund callback to exercise the reentrancy guard.
contract ReentryAttacker {
    TamaRouter internal immutable router;
    bool public attempted;
    string public reentryRevertReason;

    constructor(TamaRouter router_) {
        router = router_;
    }

    function attack(uint256 amountOut, address[] calldata path) external payable {
        // Excess ETH is refunded to msg.sender (this contract), triggering receive().
        router.swapETHForExactTokens{value: msg.value}(amountOut, path, address(this), block.timestamp);
    }

    receive() external payable {
        if (attempted) return;
        attempted = true;
        address[] memory p = new address[](2);
        p[0] = address(1);
        p[1] = address(2);
        // The guard reverts before the body runs, so this captures REENTRANT
        // rather than any downstream PAIR_NOT_FOUND error.
        try router.swapExactTokensForTokens(1, 0, p, address(this), block.timestamp) {
            reentryRevertReason = "NO_REVERT";
        } catch Error(string memory reason) {
            reentryRevertReason = reason;
        }
    }
}

contract TamaRouterTest is Test {
    UniswapV2FactoryIface internal factory;
    TamaRouter internal router;
    MockWETH internal weth;
    MockERC20 internal tokenA;
    MockERC20 internal tokenB;
    MockERC20 internal tokenC;

    function setUp() public {
        factory = UniswapV2FactoryDeployer.deploy();
        weth = new MockWETH();
        router = new TamaRouter(address(factory), address(weth));
        tokenA = new MockERC20();
        tokenB = new MockERC20();
        tokenC = new MockERC20();
        tokenA.mint(address(this), 1_000_000 ether);
        tokenB.mint(address(this), 1_000_000 ether);
        tokenC.mint(address(this), 1_000_000 ether);
        tokenA.approve(address(router), type(uint256).max);
        tokenB.approve(address(router), type(uint256).max);
        tokenC.approve(address(router), type(uint256).max);
    }

    receive() external payable {}

    function testReceiveAcceptsNativeEthFromAnySender() public {
        (bool ok,) = address(router).call{value: 1 ether}("");

        assertTrue(ok);
        assertEq(address(router).balance, 1 ether);
    }

    function testAddLiquidityCreatesPairAndMintsLp() public {
        (uint256 amountA, uint256 amountB, uint256 liquidity) = router.addLiquidity(
            address(tokenA),
            address(tokenB),
            100_000 ether,
            200_000 ether,
            100_000 ether,
            200_000 ether,
            address(this),
            block.timestamp
        );

        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        UniswapV2PairIface pair = UniswapV2PairIface(pairAddr);

        assertTrue(pairAddr != address(0));
        assertEq(amountA, 100_000 ether);
        assertEq(amountB, 200_000 ether);
        assertGt(liquidity, 0);
        assertEq(pair.balanceOf(address(this)), liquidity);
        assertEq(tokenA.balanceOf(pairAddr), 100_000 ether);
        assertEq(tokenB.balanceOf(pairAddr), 200_000 ether);
    }

    function testAddLiquidityUsesOptimalAmountForExistingPool() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 200_000 ether, 0, 0, address(this), block.timestamp
        );

        (uint256 amountA, uint256 amountB,) = router.addLiquidity(
            address(tokenA), address(tokenB), 10_000 ether, 30_000 ether, 0, 0, address(this), block.timestamp
        );

        assertEq(amountA, 10_000 ether);
        assertEq(amountB, 20_000 ether);
    }

    function testSwapExactTokensForTokensTransfersOutput() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(tokenA);
        path[1] = address(tokenB);
        uint256[] memory expected = router.getAmountsOut(1_000 ether, path);
        address recipient = address(0xBEEF);

        uint256[] memory amounts =
            router.swapExactTokensForTokens(1_000 ether, expected[1], path, recipient, block.timestamp);

        assertEq(amounts[0], 1_000 ether);
        assertEq(amounts[1], expected[1]);
        assertEq(tokenB.balanceOf(recipient), expected[1]);
    }

    function testSwapExactTokensForTokensSupportsMultiHop() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        router.addLiquidity(
            address(tokenB), address(tokenC), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = _path3(address(tokenA), address(tokenB), address(tokenC));
        uint256[] memory expected = router.getAmountsOut(1_000 ether, path);
        address recipient = address(0xBEEF);

        uint256[] memory amounts =
            router.swapExactTokensForTokens(1_000 ether, expected[2], path, recipient, block.timestamp);

        assertEq(amounts[0], 1_000 ether);
        assertEq(amounts[1], expected[1]);
        assertEq(amounts[2], expected[2]);
        assertEq(tokenC.balanceOf(recipient), expected[2]);
    }

    function testSwapTokensForExactTokensTransfersRequestedOutput() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(tokenA);
        path[1] = address(tokenB);
        uint256 amountOut = 500 ether;
        uint256[] memory expected = router.getAmountsIn(amountOut, path);
        uint256 tokenABefore = tokenA.balanceOf(address(this));
        address recipient = address(0xBEEF);

        uint256[] memory amounts =
            router.swapTokensForExactTokens(amountOut, expected[0], path, recipient, block.timestamp);

        assertEq(amounts[0], expected[0]);
        assertEq(amounts[1], amountOut);
        assertEq(tokenABefore - tokenA.balanceOf(address(this)), expected[0]);
        assertEq(tokenB.balanceOf(recipient), amountOut);
    }

    function testSwapTokensForExactTokensEnforcesMaxInput() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(tokenA);
        path[1] = address(tokenB);
        uint256[] memory expected = router.getAmountsIn(500 ether, path);

        vm.expectRevert(bytes("TamaRouter: EXCESSIVE_INPUT_AMOUNT"));
        router.swapTokensForExactTokens(500 ether, expected[0] - 1, path, address(0xBEEF), block.timestamp);
    }

    function testAddLiquidityETHWrapsNativeValueAndMintsLp() public {
        (uint256 amountToken, uint256 amountETH, uint256 liquidity) = router.addLiquidityETH{value: 100 ether}(
            address(tokenA),200 ether, 200 ether, 100 ether, address(this), block.timestamp
        );

        address pairAddr = factory.getPair(address(tokenA), address(weth));
        UniswapV2PairIface pair = UniswapV2PairIface(pairAddr);

        assertTrue(pairAddr != address(0));
        assertEq(amountToken, 200 ether);
        assertEq(amountETH, 100 ether);
        assertGt(liquidity, 0);
        assertEq(pair.balanceOf(address(this)), liquidity);
        assertEq(tokenA.balanceOf(pairAddr), 200 ether);
        assertEq(weth.balanceOf(pairAddr), 100 ether);
    }

    function testSwapExactETHForTokensWrapsAndTransfersOutput() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA),100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(weth);
        path[1] = address(tokenA);
        uint256[] memory expected = router.getAmountsOut(1 ether, path);
        address recipient = address(0xBEEF);

        uint256[] memory amounts =
            router.swapExactETHForTokens{value: 1 ether}(expected[1], path, recipient, block.timestamp);

        assertEq(amounts[0], 1 ether);
        assertEq(amounts[1], expected[1]);
        assertEq(tokenA.balanceOf(recipient), expected[1]);
    }

    function testSwapExactTokensForETHUnwrapsAndTransfersNativeOutput() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA),100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = _path(address(tokenA), address(weth));
        uint256[] memory expected = router.getAmountsOut(1_000 ether, path);
        address recipient = address(0xBEEF);
        uint256 ethBefore = recipient.balance;

        uint256[] memory amounts =
            router.swapExactTokensForETH(1_000 ether, expected[1], path, recipient, block.timestamp);

        assertEq(amounts[0], 1_000 ether);
        assertEq(amounts[1], expected[1]);
        assertEq(recipient.balance - ethBefore, expected[1]);
    }

    function testSwapETHForExactTokensTransfersOutputAndRefundsUnusedETH() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA),100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = _path(address(weth), address(tokenA));
        uint256 amountOut = 1 ether;
        uint256[] memory expected = router.getAmountsIn(amountOut, path);
        uint256 ethBefore = address(this).balance;
        address recipient = address(0xBEEF);

        uint256[] memory amounts = router.swapETHForExactTokens{value: expected[0] + 1 ether}(
            amountOut, path, recipient, block.timestamp
        );

        assertEq(amounts[0], expected[0]);
        assertEq(amounts[1], amountOut);
        assertEq(tokenA.balanceOf(recipient), amountOut);
        assertEq(ethBefore - address(this).balance, expected[0]);
    }

    function testSwapTokensForExactETHUnwrapsAndTransfersNativeOutput() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA),100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = new address[](2);
        path[0] = address(tokenA);
        path[1] = address(weth);
        uint256 amountOut = 1 ether;
        uint256[] memory expected = router.getAmountsIn(amountOut, path);
        address recipient = address(0xBEEF);
        uint256 ethBefore = recipient.balance;

        uint256[] memory amounts =
            router.swapTokensForExactETH(amountOut, expected[0], path, recipient, block.timestamp);

        assertEq(amounts[0], expected[0]);
        assertEq(amounts[1], amountOut);
        assertEq(recipient.balance - ethBefore, amountOut);
    }

    function testAddLiquidityETHRefundsUnusedETH() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA),200_000 ether, 0, 0, address(this), block.timestamp
        );
        uint256 ethBefore = address(this).balance;

        (uint256 amountToken, uint256 amountETH,) = router.addLiquidityETH{value: 2 ether}(
            address(tokenA),2 ether, 0, 0, address(this), block.timestamp
        );

        assertEq(amountToken, 2 ether);
        assertEq(amountETH, 1 ether);
        assertEq(ethBefore - address(this).balance, 1 ether);
    }

    function testExactInputTokenSwapRevertsForInsufficientOutputAmount() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = _path(address(tokenA), address(tokenB));
        uint256[] memory expected = router.getAmountsOut(1_000 ether, path);

        vm.expectRevert(bytes("TamaRouter: INSUFFICIENT_OUTPUT_AMOUNT"));
        router.swapExactTokensForTokens(1_000 ether, expected[1] + 1, path, address(0xBEEF), block.timestamp);
    }

    function testExactInputETHSwapRevertsForInsufficientOutputAmount() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA),100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = _path(address(weth), address(tokenA));
        uint256[] memory expected = router.getAmountsOut(1 ether, path);

        vm.expectRevert(bytes("TamaRouter: INSUFFICIENT_OUTPUT_AMOUNT"));
        router.swapExactETHForTokens{value: 1 ether}(
            expected[1] + 1, path, address(0xBEEF), block.timestamp
        );
    }

    function testExactInputTokenForETHSwapRevertsForInsufficientOutputAmount() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA),100_000 ether, 0, 0, address(this), block.timestamp
        );
        address[] memory path = _path(address(tokenA), address(weth));
        uint256[] memory expected = router.getAmountsOut(1_000 ether, path);

        vm.expectRevert(bytes("TamaRouter: INSUFFICIENT_OUTPUT_AMOUNT"));
        router.swapExactTokensForETH(
            1_000 ether, expected[1] + 1, path, address(0xBEEF), block.timestamp
        );
    }

    function testSwapEntrypointsRejectExpiredDeadlines() public {
        address[] memory tokenPath = _path(address(tokenA), address(tokenB));
        address[] memory ethInPath = _path(address(weth), address(tokenA));
        address[] memory ethOutPath = _path(address(tokenA), address(weth));
        uint256 expired = block.timestamp - 1;

        vm.expectRevert(bytes("TamaRouter: EXPIRED"));
        router.swapExactTokensForTokens(1, 0, tokenPath, address(this), expired);
        vm.expectRevert(bytes("TamaRouter: EXPIRED"));
        router.swapTokensForExactTokens(1, 1, tokenPath, address(this), expired);
        vm.expectRevert(bytes("TamaRouter: EXPIRED"));
        router.swapExactETHForTokens{value: 1}(0, ethInPath, address(this), expired);
        vm.expectRevert(bytes("TamaRouter: EXPIRED"));
        router.swapETHForExactTokens{value: 1}(1, ethInPath, address(this), expired);
        vm.expectRevert(bytes("TamaRouter: EXPIRED"));
        router.swapExactTokensForETH(1, 0, ethOutPath, address(this), expired);
        vm.expectRevert(bytes("TamaRouter: EXPIRED"));
        router.swapTokensForExactETH(1, 1, ethOutPath, address(this), expired);
    }

    function testNativeSwapEntrypointsRejectShortPaths() public {
        address[] memory shortPath = new address[](1);
        shortPath[0] = address(weth);

        vm.expectRevert(bytes("TamaRouter: INVALID_PATH"));
        router.swapExactETHForTokens{value: 1}(0, shortPath, address(this), block.timestamp);
        vm.expectRevert(bytes("TamaRouter: INVALID_PATH"));
        router.swapETHForExactTokens{value: 1}(1, shortPath, address(this), block.timestamp);
        vm.expectRevert(bytes("TamaRouter: INVALID_PATH"));
        router.swapExactTokensForETH(1, 0, shortPath, address(this), block.timestamp);
        vm.expectRevert(bytes("TamaRouter: INVALID_PATH"));
        router.swapTokensForExactETH(1, 1, shortPath, address(this), block.timestamp);
    }

    function testRemoveLiquidityETHUnwrapsWethToNativeETH() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA),200_000 ether, 0, 0, address(this), block.timestamp
        );
        address pairAddr = factory.getPair(address(tokenA), address(weth));
        UniswapV2PairIface pair = UniswapV2PairIface(pairAddr);
        uint256 liquidity = pair.balanceOf(address(this)) / 2;
        pair.approve(address(router), liquidity);
        address recipient = address(0xBEEF);
        uint256 ethBefore = recipient.balance;

        (uint256 amountToken, uint256 amountETH) =
            router.removeLiquidityETH(address(tokenA),liquidity, 0, 0, recipient, block.timestamp);

        assertGt(amountToken, 0);
        assertGt(amountETH, 0);
        assertEq(tokenA.balanceOf(recipient), amountToken);
        assertEq(recipient.balance - ethBefore, amountETH);
    }

    function testEthOutSwapRequiresWrappedNativeWithdrawToIncreaseRouterBalance() public {
        // WETH is immutable, so the misbehaving wrapper must be bound at construction:
        // a router whose WETH.withdraw() mints nothing must still refuse to pay out ETH.
        FakeWETH fakeWeth = new FakeWETH();
        TamaRouter fakeRouter = new TamaRouter(address(factory), address(fakeWeth));
        fakeWeth.mint(address(this), 100_000 ether);
        fakeWeth.approve(address(fakeRouter), type(uint256).max);
        tokenA.approve(address(fakeRouter), type(uint256).max);
        fakeRouter.addLiquidity(
            address(tokenA), address(fakeWeth), 100_000 ether, 100_000 ether, 0, 0, address(this), block.timestamp
        );
        (bool ok,) = address(fakeRouter).call{value: 1 ether}("");
        assertTrue(ok);
        address[] memory path = _path(address(tokenA), address(fakeWeth));

        vm.expectRevert(bytes("TamaRouter: WETH_WITHDRAW_FAILED"));
        fakeRouter.swapExactTokensForETH(1 ether, 0, path, address(0xBEEF), block.timestamp);

        assertEq(address(fakeRouter).balance, 1 ether);
    }

    function testRemoveLiquidityBurnsLpAndReturnsTokens() public {
        router.addLiquidity(
            address(tokenA), address(tokenB), 100_000 ether, 200_000 ether, 0, 0, address(this), block.timestamp
        );
        address pairAddr = factory.getPair(address(tokenA), address(tokenB));
        UniswapV2PairIface pair = UniswapV2PairIface(pairAddr);
        uint256 liquidity = pair.balanceOf(address(this)) / 2;
        pair.approve(address(router), liquidity);
        address recipient = address(0xCAFE);

        (uint256 amountA, uint256 amountB) =
            router.removeLiquidity(address(tokenA), address(tokenB), liquidity, 0, 0, recipient, block.timestamp);

        assertGt(amountA, 0);
        assertGt(amountB, 0);
        assertEq(tokenA.balanceOf(recipient), amountA);
        assertEq(tokenB.balanceOf(recipient), amountB);
    }

    function testDeadlineIsEnforced() public {
        vm.expectRevert(bytes("TamaRouter: EXPIRED"));
        router.addLiquidity(address(tokenA), address(tokenB), 1, 1, 0, 0, address(this), block.timestamp - 1);
    }

    function testConstructorRejectsZeroWeth() public {
        vm.expectRevert(bytes("TamaRouter: ZERO_WETH"));
        new TamaRouter(address(factory), address(0));
    }

    function testReentrancyGuardBlocksReentrantSwap() public {
        router.addLiquidityETH{value: 100_000 ether}(
            address(tokenA), 100_000 ether, 0, 0, address(this), block.timestamp
        );
        ReentryAttacker attacker = new ReentryAttacker(router);
        address[] memory path = _path(address(weth), address(tokenA));
        uint256 amountOut = 1 ether;
        uint256[] memory expected = router.getAmountsIn(amountOut, path);

        // Outer swap succeeds; the refund callback's reentrant swap is rejected by the guard.
        attacker.attack{value: expected[0] + 1 ether}(amountOut, path);

        assertTrue(attacker.attempted());
        assertEq(attacker.reentryRevertReason(), "TamaRouter: REENTRANT");
        assertEq(tokenA.balanceOf(address(attacker)), amountOut);
    }

    function _path(address token0, address token1) internal pure returns (address[] memory path) {
        path = new address[](2);
        path[0] = token0;
        path[1] = token1;
    }

    function _path3(address token0, address token1, address token2) internal pure returns (address[] memory path) {
        path = new address[](3);
        path[0] = token0;
        path[1] = token1;
        path[2] = token2;
    }
}
