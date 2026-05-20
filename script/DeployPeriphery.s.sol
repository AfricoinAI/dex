// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script, console2} from "forge-std/Script.sol";
import {TamaRouter} from "../src/TamaRouter.sol";
import {TamaSwapFrontend} from "../src/TamaSwapFrontend.sol";

contract DeployPeriphery is Script {
    function run() external returns (TamaRouter router, TamaSwapFrontend frontend) {
        address factory = vm.envAddress("FACTORY");

        vm.startBroadcast();
        router = new TamaRouter(factory);
        frontend = new TamaSwapFrontend(factory, address(router));
        vm.stopBroadcast();

        console2.log("Factory :", factory);
        console2.log("Router  :", address(router));
        console2.log("Frontend:", address(frontend));
    }
}
