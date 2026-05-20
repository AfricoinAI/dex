// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {TamaRouter} from "../../src/TamaRouter.sol";
import {UniswapV2FactoryDeployer} from "../../src/generated/verity/UniswapV2FactoryDeployer.sol";
import {UniswapV2FactoryIface} from "../../src/generated/verity/UniswapV2FactoryIface.sol";
import {UniswapV2PairIface} from "../../src/generated/verity/UniswapV2PairIface.sol";
import {MockERC20} from "../verity/UniswapV2Helpers.sol";

contract TamaRouterTest is Test {
    UniswapV2FactoryIface internal factory;
    TamaRouter internal router;
    MockERC20 internal tokenA;
    MockERC20 internal tokenB;

    function setUp() public {
        factory = UniswapV2FactoryDeployer.deploy();
        router = new TamaRouter(address(factory));
        tokenA = new MockERC20();
        tokenB = new MockERC20();
        tokenA.mint(address(this), 1_000_000 ether);
        tokenB.mint(address(this), 1_000_000 ether);
        tokenA.approve(address(router), type(uint256).max);
        tokenB.approve(address(router), type(uint256).max);
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
}
