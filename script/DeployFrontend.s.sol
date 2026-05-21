// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script, console2} from "forge-std/Script.sol";
import {TamaSwapFrontend, TamaSwapFrontendData} from "../src/TamaSwapFrontend.sol";

contract DeployFrontend is Script {
    function run() external returns (TamaSwapFrontend frontend) {
        uint256 privateKey = vm.envUint("PRIVATE_KEY");

        vm.startBroadcast(privateKey);
        TamaSwapFrontendData data = new TamaSwapFrontendData();
        frontend = new TamaSwapFrontend(address(data));
        vm.stopBroadcast();

        console2.log("Frontend data:", address(data));
        console2.log("Frontend:", address(frontend));
    }
}
