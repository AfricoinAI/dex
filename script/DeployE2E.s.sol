// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script} from "forge-std/Script.sol";
import {TamaRouter} from "../src/TamaRouter.sol";
import {TamaSwapFrontend} from "../src/TamaSwapFrontend.sol";
import {UniswapV2FactoryDeployer} from "../src/generated/verity/UniswapV2FactoryDeployer.sol";
import {E2EToken, E2EWETH} from "./E2ETokens.sol";

contract DeployE2E is Script {
    address internal constant CREATE2_DEPLOYER = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address internal constant GLOBAL_FACTORY = 0x00000060cc856A2b760b870290fAAD078c146258;
    address internal constant GLOBAL_ROUTER = 0x0000002Ec9919637129644E17039EE41d9bf9bce;
    address internal constant GLOBAL_FRONTEND = 0x0000002f0B0ce48CeC22156DdCe437d53D6F2E72;
    bytes32 internal constant FACTORY_SALT = 0x000000000000000000000000000000000000000079f16b35eec9000000f08c16;
    bytes32 internal constant ROUTER_SALT = 0x00000000000000000000000000000000000000006b423948f657000001dba44f;
    bytes32 internal constant FRONTEND_SALT = 0x0000000000000000000000000000000000000000d885dafdd6a20000007aa5b5;
    bytes32 internal constant WETH_SALT = keccak256("tama-uni-v2.local-weth");

    function run() external {
        uint256 privateKey = vm.envUint("PRIVATE_KEY");
        address deployer = vm.addr(privateKey);
        string memory output = vm.envOr("E2E_OUT", string("e2e/.tmp/deployment.json"));

        require(CREATE2_DEPLOYER.code.length != 0, "E2E_ARACHNID_MISSING");

        vm.startBroadcast(privateKey);
        address factory = _deployCreate2(FACTORY_SALT, factoryCreationCode(), GLOBAL_FACTORY);
        E2EWETH weth = E2EWETH(payable(_deployCreate2(WETH_SALT, type(E2EWETH).creationCode, wethAddress())));
        address router = _deployCreate2(ROUTER_SALT, routerCreationCode(factory), GLOBAL_ROUTER);
        TamaSwapFrontend frontend =
            TamaSwapFrontend(_deployCreate2(FRONTEND_SALT, type(TamaSwapFrontend).creationCode, GLOBAL_FRONTEND));
        E2EToken tokenA = new E2EToken("Test Token A", "TKA", 18);
        E2EToken tokenB = new E2EToken("Test Token B", "TKB", 6);
        tokenA.mint(deployer, 1_000_000 ether);
        tokenB.mint(deployer, 1_000_000 * 10 ** 6);
        vm.stopBroadcast();

        string memory root = "e2e";
        vm.serializeAddress(root, "account", deployer);
        vm.serializeAddress(root, "factory", factory);
        vm.serializeAddress(root, "weth", address(weth));
        vm.serializeAddress(root, "router", router);
        vm.serializeAddress(root, "frontend", address(frontend));
        vm.serializeAddress(root, "deploymentData", frontend.HTML_DATA());
        vm.serializeAddress(root, "deploymentCodeData", frontend.DEPLOYMENT_DATA());
        vm.serializeAddress(root, "tokenA", address(tokenA));
        string memory json = vm.serializeAddress(root, "tokenB", address(tokenB));
        vm.writeJson(json, output);
    }

    function factoryCreationCode() public pure returns (bytes memory) {
        return UniswapV2FactoryDeployer.creationCode();
    }

    function routerCreationCode(address factory) public pure returns (bytes memory) {
        return abi.encodePacked(type(TamaRouter).creationCode, abi.encode(factory));
    }

    function wethAddress() public pure returns (address) {
        return _create2Address(WETH_SALT, type(E2EWETH).creationCode);
    }

    function _deployCreate2(bytes32 salt, bytes memory initCode, address expected) internal returns (address deployed) {
        require(_create2Address(salt, initCode) == expected, "E2E_BAD_CREATE2_ADDRESS");
        if (expected.code.length != 0) return expected;

        (bool success, bytes memory returndata) = CREATE2_DEPLOYER.call(abi.encodePacked(salt, initCode));
        require(success, "E2E_CREATE2_CALL_FAILED");
        require(returndata.length == 20, "E2E_BAD_CREATE2_RETURN");

        assembly {
            deployed := shr(96, mload(add(returndata, 32)))
        }
        require(deployed == expected, "E2E_UNEXPECTED_CREATE2_ADDRESS");
        require(deployed.code.length != 0, "E2E_CREATE2_NO_CODE");
    }

    function _create2Address(bytes32 salt, bytes memory initCode) internal pure returns (address) {
        return address(
            uint160(uint256(keccak256(abi.encodePacked(bytes1(0xff), CREATE2_DEPLOYER, salt, keccak256(initCode)))))
        );
    }
}
