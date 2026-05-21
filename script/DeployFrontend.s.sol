// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script, console2} from "forge-std/Script.sol";
import {TamaSwapFrontend} from "../src/TamaSwapFrontend.sol";

contract DeployFrontend is Script {
    address internal constant CREATE2_DEPLOYER = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address internal constant FRONTEND = 0x000000b916D42E11D9ad4C0b3d83cF4b769A571d;
    bytes32 internal constant FRONTEND_SALT = 0x00000000000000000000000000000000000000003f70fcd3b2e00000009b0547;

    function run() external returns (TamaSwapFrontend frontend) {
        uint256 privateKey = vm.envUint("PRIVATE_KEY");

        require(CREATE2_DEPLOYER.code.length != 0, "ARACHNID_MISSING");

        vm.startBroadcast(privateKey);
        frontend = TamaSwapFrontend(_deployCreate2(FRONTEND_SALT, type(TamaSwapFrontend).creationCode, FRONTEND));
        vm.stopBroadcast();

        console2.log("Frontend data:", frontend.HTML_DATA());
        console2.log("Deployment data:", frontend.DEPLOYMENT_DATA());
        console2.log("Frontend:", address(frontend));
    }

    function _deployCreate2(bytes32 salt, bytes memory initCode, address expected) internal returns (address deployed) {
        require(_create2Address(salt, initCode) == expected, "BAD_CREATE2_ADDRESS");
        if (expected.code.length != 0) return expected;

        (bool success, bytes memory returndata) = CREATE2_DEPLOYER.call(abi.encodePacked(salt, initCode));
        require(success, "CREATE2_CALL_FAILED");
        require(returndata.length == 20, "BAD_CREATE2_RETURN");

        assembly {
            deployed := shr(96, mload(add(returndata, 32)))
        }
        require(deployed == expected, "UNEXPECTED_CREATE2_ADDRESS");
        require(deployed.code.length != 0, "CREATE2_NO_CODE");
    }

    function _create2Address(bytes32 salt, bytes memory initCode) internal pure returns (address) {
        return address(
            uint160(uint256(keccak256(abi.encodePacked(bytes1(0xff), CREATE2_DEPLOYER, salt, keccak256(initCode)))))
        );
    }
}
