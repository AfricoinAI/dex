// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script} from "forge-std/Script.sol";
import {TamaRouter} from "../src/TamaRouter.sol";
import {TamaSwapFrontend} from "../src/TamaSwapFrontend.sol";
import {UniswapV2FactoryDeployer} from "../src/generated/verity/UniswapV2FactoryDeployer.sol";

contract E2EToken {
    string public name;
    string public symbol;
    uint8 public immutable decimals = 18;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    constructor(string memory name_, string memory symbol_) {
        name = name_;
        symbol = symbol_;
    }

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
        emit Transfer(address(0), to, amount);
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "BALANCE");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        uint256 allowed = allowance[from][msg.sender];
        require(allowed >= amount, "ALLOWANCE");
        if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;
        require(balanceOf[from] >= amount, "BALANCE");
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        emit Transfer(from, to, amount);
        return true;
    }
}

contract DeployE2E is Script {
    function run() external {
        address deployer = vm.addr(vm.envUint("PRIVATE_KEY"));
        string memory output = vm.envOr("E2E_OUT", string("e2e/.tmp/deployment.json"));

        vm.startBroadcast();
        address factory = address(UniswapV2FactoryDeployer.deploy());
        TamaRouter router = new TamaRouter(factory);
        TamaSwapFrontend frontend = new TamaSwapFrontend(factory, address(router));
        E2EToken tokenA = new E2EToken("Test Token A", "TKA");
        E2EToken tokenB = new E2EToken("Test Token B", "TKB");
        tokenA.mint(deployer, 1_000_000 ether);
        tokenB.mint(deployer, 1_000_000 ether);
        vm.stopBroadcast();

        string memory root = "e2e";
        vm.serializeAddress(root, "account", deployer);
        vm.serializeAddress(root, "factory", factory);
        vm.serializeAddress(root, "router", address(router));
        vm.serializeAddress(root, "frontend", address(frontend));
        vm.serializeAddress(root, "tokenA", address(tokenA));
        string memory json = vm.serializeAddress(root, "tokenB", address(tokenB));
        vm.writeJson(json, output);
    }
}
