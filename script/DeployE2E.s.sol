// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script} from "forge-std/Script.sol";
import {TamaRouter} from "../src/TamaRouter.sol";
import {TamaSwapFrontend} from "../src/TamaSwapFrontend.sol";
import {E2EToken, E2EWETH} from "./E2ETokens.sol";

contract DeployE2E is Script {
    address internal constant CREATE2_DEPLOYER = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address internal constant GLOBAL_FACTORY = 0x00000021543ed46B665A74484c82B71E4eB61e34;
    address internal constant GLOBAL_ROUTER = 0x00000095D7941E2e3d65a0C14a77bEAf9F653Ab9;
    address internal constant GLOBAL_FRONTEND = 0x000000CA153CD3d1F62C3c817E254A4706046FF2;
    bytes32 internal constant FACTORY_SALT = 0xe7de01c00746d6ee6cacea2e58353be0f49b1826adaa8a7adaafaf5a235dbfcd;
    bytes32 internal constant ROUTER_SALT = 0x06282929ef89d7938a11484a36e4a7392bb25528a302f25d7ddfdac69e7bb51a;
    bytes32 internal constant FRONTEND_SALT = 0xa46c27ebaabd64d26a14c8848ad32af53481a6cc1bf650ba2cec3f49a8b6bbb2;
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

    function factoryCreationCode() public view returns (bytes memory) {
        bytes memory raw = bytes(vm.readFile("artifacts/bytecode/UniswapV2Factory.bin"));
        uint256 length = raw.length;
        if (length > 0 && raw[length - 1] == 0x0a) {
            length -= 1;
        }
        bytes memory trimmed = new bytes(length);
        for (uint256 i = 0; i < length; i++) {
            trimmed[i] = raw[i];
        }
        return vm.parseBytes(string.concat("0x", string(trimmed)));
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
