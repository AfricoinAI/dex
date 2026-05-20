// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script, console2} from "forge-std/Script.sol";

interface ICREATE3Factory {
    function deploy(bytes32 salt, bytes memory creationCode) external payable returns (address deployed);
    function getDeployed(address deployer, bytes32 salt) external view returns (address deployed);
}

contract DeployFactory is Script {
    address internal constant DEFAULT_CREATE3_FACTORY = 0x9fBB3DF7C40Da2e5A0dE984fFE2CCB7C47cd0ABf;
    bytes32 internal constant DEFAULT_SALT = keccak256("tama-uni-v2.factory");
    string internal constant FACTORY_BYTECODE_PATH = "artifacts/bytecode/UniswapV2Factory.bin";

    function run() external returns (address factory) {
        bytes32 salt = vm.envOr("FACTORY_SALT", DEFAULT_SALT);
        ICREATE3Factory create3Factory =
            ICREATE3Factory(vm.envOr("CREATE3_FACTORY", DEFAULT_CREATE3_FACTORY));

        vm.startBroadcast();
        factory = create3Factory.deploy(salt, factoryCreationCode());
        vm.stopBroadcast();

        console2.log("Factory deployed:", factory);
    }

    function predictFactoryAddress(address deployer, bytes32 salt) external view returns (address) {
        ICREATE3Factory create3Factory =
            ICREATE3Factory(vm.envOr("CREATE3_FACTORY", DEFAULT_CREATE3_FACTORY));
        return create3Factory.getDeployed(deployer, salt);
    }

    function factoryCreationCode() public view returns (bytes memory) {
        return vm.parseBytes(_trimTrailingNewline(vm.readFile(FACTORY_BYTECODE_PATH)));
    }

    function _trimTrailingNewline(string memory value) internal pure returns (string memory) {
        bytes memory raw = bytes(value);
        if (raw.length == 0 || raw[raw.length - 1] != 0x0a) {
            return value;
        }

        bytes memory trimmed = new bytes(raw.length - 1);
        for (uint256 i = 0; i < trimmed.length; i++) {
            trimmed[i] = raw[i];
        }
        return string(trimmed);
    }
}
