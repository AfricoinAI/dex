// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {UniswapV2FactoryDeployer} from "../../src/generated/verity/UniswapV2FactoryDeployer.sol";
import {UniswapV2FactoryIface} from "../../src/generated/verity/UniswapV2FactoryIface.sol";
import {UniswapV2PairIface} from "../../src/generated/verity/UniswapV2PairIface.sol";

contract MockERC20 {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    uint256 public totalSupply;

    event Transfer(address indexed from, address indexed to, uint256 value);

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
        emit Transfer(address(0), to, amount);
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
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
        if (allowed != type(uint256).max) {
            allowance[from][msg.sender] = allowed - amount;
        }
        require(balanceOf[from] >= amount, "BALANCE");
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        emit Transfer(from, to, amount);
        return true;
    }
}

contract NoReturnERC20 {
    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;

    event Transfer(address indexed from, address indexed to, uint256 value);

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
        emit Transfer(address(0), to, amount);
    }

    function transfer(address to, uint256 amount) external {
        require(balanceOf[msg.sender] >= amount, "BALANCE");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
    }
}

contract FalseReturnERC20 {
    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;

    event Transfer(address indexed from, address indexed to, uint256 value);

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
        emit Transfer(address(0), to, amount);
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "BALANCE");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
        return false;
    }
}

contract RevertingTransferERC20 {
    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;

    event Transfer(address indexed from, address indexed to, uint256 value);

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
        emit Transfer(address(0), to, amount);
    }

    function transfer(address, uint256) external pure returns (bool) {
        revert("TRANSFER_REVERTED");
    }
}

contract RevertingBalanceOfERC20 {
    function balanceOf(address) external pure returns (uint256) {
        revert("BALANCE_REVERTED");
    }
}

contract ShortReturnBalanceOfERC20 {
    mapping(address => uint256) internal balances;
    uint256 public totalSupply;

    event Transfer(address indexed from, address indexed to, uint256 value);

    function mint(address to, uint256 amount) external {
        balances[to] += amount;
        totalSupply += amount;
        emit Transfer(address(0), to, amount);
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balances[msg.sender] >= amount, "BALANCE");
        balances[msg.sender] -= amount;
        balances[to] += amount;
        emit Transfer(msg.sender, to, amount);
        return true;
    }

    fallback() external {
        bytes4 selector;
        assembly {
            selector := shr(224, calldataload(0))
        }
        if (selector == 0x70a08231) {
            assembly {
                mstore(0, 1)
                return(31, 1)
            }
        }
        revert("UNSUPPORTED");
    }
}

contract ReentrantTransferERC20 {
    enum Entrypoint {
        Mint,
        Burn,
        Swap,
        Skim,
        Sync
    }

    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;
    UniswapV2PairIface public pair;
    Entrypoint public entrypoint;
    bool public armed;
    bool public reentryRejected;
    string public revertReason;

    event Transfer(address indexed from, address indexed to, uint256 value);

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
        totalSupply += amount;
        emit Transfer(address(0), to, amount);
    }

    function configureReentry(UniswapV2PairIface pair_, Entrypoint entrypoint_) external {
        pair = pair_;
        entrypoint = entrypoint_;
        armed = true;
        reentryRejected = false;
        revertReason = "";
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "BALANCE");
        if (armed) {
            armed = false;
            _attemptReentry();
        }
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
        return true;
    }

    function _attemptReentry() internal {
        if (entrypoint == Entrypoint.Mint) {
            try pair.mint(address(this)) returns (uint256) {
                revert("MINT_REENTRY_ALLOWED");
            } catch Error(string memory reason) {
                reentryRejected = true;
                revertReason = reason;
            } catch {
                reentryRejected = true;
            }
        } else if (entrypoint == Entrypoint.Burn) {
            try pair.burn(address(this)) returns (uint256, uint256) {
                revert("BURN_REENTRY_ALLOWED");
            } catch Error(string memory reason) {
                reentryRejected = true;
                revertReason = reason;
            } catch {
                reentryRejected = true;
            }
        } else if (entrypoint == Entrypoint.Swap) {
            try pair.swap(0, 1, address(this), "") {
                revert("SWAP_REENTRY_ALLOWED");
            } catch Error(string memory reason) {
                reentryRejected = true;
                revertReason = reason;
            } catch {
                reentryRejected = true;
            }
        } else if (entrypoint == Entrypoint.Skim) {
            try pair.skim(address(this)) {
                revert("SKIM_REENTRY_ALLOWED");
            } catch Error(string memory reason) {
                reentryRejected = true;
                revertReason = reason;
            } catch {
                reentryRejected = true;
            }
        } else {
            try pair.sync() {
                revert("SYNC_REENTRY_ALLOWED");
            } catch Error(string memory reason) {
                reentryRejected = true;
                revertReason = reason;
            } catch {
                reentryRejected = true;
            }
        }
    }
}

contract FlashCallee {
    MockERC20 public token0;
    MockERC20 public token1;

    function uniswapV2Call(address, uint256 amount0Out, uint256 amount1Out, bytes calldata data) external {
        uint256 amount0In;
        uint256 amount1In;
        (token0, token1, amount0In, amount1In) = abi.decode(data, (MockERC20, MockERC20, uint256, uint256));
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "FLASH_TRANSFER0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "FLASH_TRANSFER1");
        amount0Out;
        amount1Out;
    }
}

contract TrackingFlashCallee {
    bool public called;
    address public lastSender;
    uint256 public lastAmount0Out;
    uint256 public lastAmount1Out;
    bytes public lastData;

    function uniswapV2Call(address sender, uint256 amount0Out, uint256 amount1Out, bytes calldata data) external {
        called = true;
        lastSender = sender;
        lastAmount0Out = amount0Out;
        lastAmount1Out = amount1Out;
        lastData = data;
        (MockERC20 payToken, uint256 payAmount) = abi.decode(data, (MockERC20, uint256));
        if (payAmount > 0) require(payToken.transfer(msg.sender, payAmount), "PAY");
    }
}

contract RevertingFlashCallee {
    function uniswapV2Call(address, uint256, uint256, bytes calldata) external pure {
        revert("FLASH_FAIL");
    }
}

abstract contract ReentrantCalleeBase {
    UniswapV2PairIface public pair;
    MockERC20 public token0;
    MockERC20 public token1;
    uint256 public amount0In;
    uint256 public amount1In;
    bool public reentryRejected;
    string public revertReason;

    constructor(
        UniswapV2PairIface pair_,
        MockERC20 token0_,
        MockERC20 token1_,
        uint256 amount0In_,
        uint256 amount1In_
    ) {
        pair = pair_;
        token0 = token0_;
        token1 = token1_;
        amount0In = amount0In_;
        amount1In = amount1In_;
    }

    function _payBackInputs() internal {
        if (amount0In > 0) require(token0.transfer(msg.sender, amount0In), "PAY0");
        if (amount1In > 0) require(token1.transfer(msg.sender, amount1In), "PAY1");
    }
}

contract MintReentrantCallee is ReentrantCalleeBase {
    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_, uint256 amount0In_, uint256 amount1In_)
        ReentrantCalleeBase(pair_, token0_, token1_, amount0In_, amount1In_)
    {}

    function uniswapV2Call(address, uint256, uint256, bytes calldata) external {
        try pair.mint(address(this)) returns (uint256) {
            revert("MINT_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            reentryRejected = true;
            revertReason = reason;
        } catch {
            reentryRejected = true;
        }
        _payBackInputs();
    }
}

contract BurnReentrantCallee is ReentrantCalleeBase {
    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_, uint256 amount0In_, uint256 amount1In_)
        ReentrantCalleeBase(pair_, token0_, token1_, amount0In_, amount1In_)
    {}

    function uniswapV2Call(address, uint256, uint256, bytes calldata) external {
        try pair.burn(address(this)) returns (uint256, uint256) {
            revert("BURN_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            reentryRejected = true;
            revertReason = reason;
        } catch {
            reentryRejected = true;
        }
        _payBackInputs();
    }
}

contract SwapReentrantCallee is ReentrantCalleeBase {
    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_, uint256 amount0In_, uint256 amount1In_)
        ReentrantCalleeBase(pair_, token0_, token1_, amount0In_, amount1In_)
    {}

    function uniswapV2Call(address, uint256, uint256, bytes calldata) external {
        try pair.swap(0, 1, address(this), "") {
            revert("SWAP_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            reentryRejected = true;
            revertReason = reason;
        } catch {
            reentryRejected = true;
        }
        _payBackInputs();
    }
}

contract SkimReentrantCallee is ReentrantCalleeBase {
    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_, uint256 amount0In_, uint256 amount1In_)
        ReentrantCalleeBase(pair_, token0_, token1_, amount0In_, amount1In_)
    {}

    function uniswapV2Call(address, uint256, uint256, bytes calldata) external {
        try pair.skim(address(this)) {
            revert("SKIM_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            reentryRejected = true;
            revertReason = reason;
        } catch {
            reentryRejected = true;
        }
        _payBackInputs();
    }
}

contract SyncReentrantCallee is ReentrantCalleeBase {
    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_, uint256 amount0In_, uint256 amount1In_)
        ReentrantCalleeBase(pair_, token0_, token1_, amount0In_, amount1In_)
    {}

    function uniswapV2Call(address, uint256, uint256, bytes calldata) external {
        try pair.sync() {
            revert("SYNC_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            reentryRejected = true;
            revertReason = reason;
        } catch {
            reentryRejected = true;
        }
        _payBackInputs();
    }
}

/// Tries every mutating entrypoint inside a single flash callback, recording
/// whether each attempt was rejected and with which revert reason. Used to
/// mirror `pair_flash_callback_reentry_attempts_revert_locked`, which states
/// that all five entrypoints reject with LOCKED during the callback.
contract AllEntrypointReentrantCallee is ReentrantCalleeBase {
    bool public mintRejected;
    string public mintRevertReason;
    bool public burnRejected;
    string public burnRevertReason;
    bool public swapRejected;
    string public swapRevertReason;
    bool public skimRejected;
    string public skimRevertReason;
    bool public syncRejected;
    string public syncRevertReason;

    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_, uint256 amount0In_, uint256 amount1In_)
        ReentrantCalleeBase(pair_, token0_, token1_, amount0In_, amount1In_)
    {}

    function uniswapV2Call(address, uint256, uint256, bytes calldata) external {
        try pair.mint(address(this)) returns (uint256) {
            revert("MINT_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            mintRejected = true;
            mintRevertReason = reason;
        } catch {
            mintRejected = true;
        }

        try pair.burn(address(this)) returns (uint256, uint256) {
            revert("BURN_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            burnRejected = true;
            burnRevertReason = reason;
        } catch {
            burnRejected = true;
        }

        try pair.swap(0, 1, address(this), "") {
            revert("SWAP_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            swapRejected = true;
            swapRevertReason = reason;
        } catch {
            swapRejected = true;
        }

        try pair.skim(address(this)) {
            revert("SKIM_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            skimRejected = true;
            skimRevertReason = reason;
        } catch {
            skimRejected = true;
        }

        try pair.sync() {
            revert("SYNC_REENTRY_ALLOWED");
        } catch Error(string memory reason) {
            syncRejected = true;
            syncRevertReason = reason;
        } catch {
            syncRejected = true;
        }

        reentryRejected = mintRejected && burnRejected && swapRejected && skimRejected && syncRejected;

        _payBackInputs();
    }
}

contract RevertingAllEntrypointReentrantCallee is ReentrantCalleeBase {
    constructor(UniswapV2PairIface pair_, MockERC20 token0_, MockERC20 token1_, uint256 amount0In_, uint256 amount1In_)
        ReentrantCalleeBase(pair_, token0_, token1_, amount0In_, amount1In_)
    {}

    function uniswapV2Call(address, uint256, uint256, bytes calldata) external {
        try pair.mint(address(this)) returns (uint256) {
            revert("MINT_REENTRY_ALLOWED");
        } catch {}

        try pair.burn(address(this)) returns (uint256, uint256) {
            revert("BURN_REENTRY_ALLOWED");
        } catch {}

        try pair.swap(0, 1, address(this), "") {
            revert("SWAP_REENTRY_ALLOWED");
        } catch {}

        try pair.skim(address(this)) {
            revert("SKIM_REENTRY_ALLOWED");
        } catch {}

        try pair.sync() {
            revert("SYNC_REENTRY_ALLOWED");
        } catch {}

        revert("CALLBACK_REVERT_AFTER_REENTRY");
    }
}

abstract contract PairFixture is Test {
    MockERC20 internal tokenA;
    MockERC20 internal tokenB;
    UniswapV2FactoryIface internal factory;
    UniswapV2PairIface internal pair;

    uint256 internal constant PAIR_FACTORY_SLOT = 0;
    uint256 internal constant PAIR_TOKEN0_SLOT = 1;
    uint256 internal constant PAIR_TOKEN1_SLOT = 2;
    uint256 internal constant PAIR_RESERVE0_SLOT = 3;
    uint256 internal constant PAIR_RESERVE1_SLOT = 4;
    uint256 internal constant PAIR_BLOCK_TIMESTAMP_LAST_SLOT = 5;
    uint256 internal constant PAIR_PRICE0_CUMULATIVE_LAST_SLOT = 6;
    uint256 internal constant PAIR_PRICE1_CUMULATIVE_LAST_SLOT = 7;
    uint256 internal constant PAIR_TOTAL_SUPPLY_SLOT = 8;
    uint256 internal constant PAIR_BALANCES_SLOT = 9;
    uint256 internal constant PAIR_ALLOWANCES_SLOT = 10;
    uint256 internal constant PAIR_UNLOCKED_SLOT = 11;
    uint256 internal constant MAX_UINT112 = 5192296858534827628530496329220095;

    event Approval(address indexed owner, address indexed spender, uint256 value);
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(address indexed sender, uint256 amount0, uint256 amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint256 reserve0, uint256 reserve1);
    event PairCreated(address indexed token0, address indexed token1, address pair, uint256 allPairsLength);

    function setUp() public virtual {
        tokenA = new MockERC20();
        tokenB = new MockERC20();
        factory = UniswapV2FactoryDeployer.deploy();
        pair = UniswapV2PairIface(factory.createPair(address(tokenA), address(tokenB)));
    }

    function seed(uint256 amountA, uint256 amountB) internal {
        tokenA.mint(address(pair), amountA);
        tokenB.mint(address(pair), amountB);
        pair.mint(address(this));
    }

    function sortedTokens() internal view returns (MockERC20 t0, MockERC20 t1) {
        return pair.token0() == address(tokenA) ? (tokenA, tokenB) : (tokenB, tokenA);
    }

    function sortedAmounts(uint256 amountA, uint256 amountB) internal view returns (uint256 amount0, uint256 amount1) {
        return pair.token0() == address(tokenA) ? (amountA, amountB) : (amountB, amountA);
    }

    function pairSlot(uint256 slot) internal pure returns (bytes32) {
        return bytes32(slot);
    }

    function lpBalanceSlot(address account) internal pure returns (bytes32) {
        return keccak256(abi.encode(account, PAIR_BALANCES_SLOT));
    }

    function lpAllowanceSlot(address owner, address spender) internal pure returns (bytes32) {
        return keccak256(abi.encode(spender, keccak256(abi.encode(owner, PAIR_ALLOWANCES_SLOT))));
    }

    function setLpBalance(address account, uint256 amount) internal {
        vm.store(address(pair), lpBalanceSlot(account), bytes32(amount));
    }

    function setLpAllowance(address owner, address spender, uint256 amount) internal {
        vm.store(address(pair), lpAllowanceSlot(owner, spender), bytes32(amount));
    }

    function getAmountIn(uint256 amountOut, uint256 reserveIn, uint256 reserveOut) internal pure returns (uint256) {
        return (reserveIn * amountOut * 1000) / ((reserveOut - amountOut) * 997) + 1;
    }

    function getAmountOut(uint256 amountIn, uint256 reserveIn, uint256 reserveOut) internal pure returns (uint256) {
        uint256 amountInWithFee = amountIn * 997;
        return (amountInWithFee * reserveOut) / (reserveIn * 1000 + amountInWithFee);
    }
}

abstract contract FactoryFixture is Test {
    MockERC20 internal tokenA;
    MockERC20 internal tokenB;
    UniswapV2FactoryIface internal factory;
    UniswapV2PairIface internal pair;

    uint256 internal constant FACTORY_PAIR_FOR_SLOT = 0;
    uint256 internal constant FACTORY_ALL_PAIRS_SLOT = 1;
    uint256 internal constant FACTORY_ALL_PAIRS_LENGTH_SLOT = 2;

    event PairCreated(address indexed token0, address indexed token1, address pair, uint256 allPairsLength);

    function setUp() public virtual {
        tokenA = new MockERC20();
        tokenB = new MockERC20();
        factory = UniswapV2FactoryDeployer.deploy();
        pair = UniswapV2PairIface(factory.createPair(address(tokenA), address(tokenB)));
    }

    function sortedAddresses(address x, address y) internal pure returns (address a0, address a1) {
        return x < y ? (x, y) : (y, x);
    }

    function factorySlot(uint256 slot) internal pure returns (bytes32) {
        return bytes32(slot);
    }

    function pairCreationCodeHex() internal view returns (string memory) {
        bytes memory raw = bytes(vm.readFile("artifacts/bytecode/UniswapV2Pair.bin"));
        uint256 length = raw.length;
        if (length > 0 && raw[length - 1] == 0x0a) {
            length -= 1;
        }
        bytes memory trimmed = new bytes(length);
        for (uint256 i = 0; i < length; i++) {
            trimmed[i] = raw[i];
        }
        return string.concat("0x", string(trimmed));
    }

    function expectedCreate2Pair(address token0, address token1) internal view returns (address) {
        bytes memory creationCode = vm.parseBytes(pairCreationCodeHex());
        bytes32 salt = keccak256(abi.encodePacked(token0, token1));
        return address(
            uint160(uint256(keccak256(abi.encodePacked(hex"ff", address(factory), salt, keccak256(creationCode)))))
        );
    }
}
