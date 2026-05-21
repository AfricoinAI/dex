// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script, console2} from "forge-std/Script.sol";
import {TamaSwapFrontend} from "../src/TamaSwapFrontend.sol";

contract DeployFrontend is Script {
    function run() external returns (TamaSwapFrontend frontend) {
        uint256 privateKey = vm.envUint("PRIVATE_KEY");

        vm.startBroadcast(privateKey);
        frontend = new TamaSwapFrontend();
        vm.stopBroadcast();

        console2.log("Frontend data:", frontend.HTML_DATA());
        console2.log("Deployment data:", frontend.DEPLOYMENT_DATA());
        console2.log("Frontend:", address(frontend));
    }
}
