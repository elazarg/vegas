// SPDX-License-Identifier: MIT
pragma solidity ^0.8.37;

contract OddsEvensShort {
    enum Role { None, Odd, Even }
    
    uint256 constant public ACTION_Even_0 = 0;
    uint256 constant public ACTION_Odd_0 = 1;
    uint256 constant public ACTION_Odd_2 = 2;
    uint256 constant public ACTION_Even_4 = 3;
    uint256 constant public ACTION_Odd_3 = 4;
    uint256 constant public ACTION_Even_5 = 5;
    mapping(address => Role) public roles;
    address public address_Odd;
    address public address_Even;
    bool public done_Odd;
    bool public done_Even;
    bool public claimed_Odd;
    bool public claimed_Even;
    bool public Odd_c;
    bool public done_Odd_c;
    bytes32 public Odd_c_hidden;
    bool public done_Odd_c_hidden;
    bool public Even_c;
    bool public done_Even_c;
    bytes32 public Even_c_hidden;
    bool public done_Even_c_hidden;
    
    receive() external payable {
        revert("direct ETH not allowed");
    }
    
    uint256 constant public TIMEOUT = 86400;
    uint256 constant public NODE_COUNT = 6;
    uint256 public immutable deployedAt;
    
    /// Readiness time of each node: when its last predecessor resolved (0 = not ready).
    mapping(uint256 => uint256) public readyAt;
    /// Resolution time of each node: when it was played, or resolved without a value (0 = unresolved).
    mapping(uint256 => uint256) public resolvedAt;
    /// When a role quit: the deadline it missed (0 = active). Quitting is persistent.
    mapping(Role => uint256) public quitAt;
    /// Set when a role failed to join: play never starts and deposits are refunded.
    bool public aborted;
    /// Every node below this position is resolved.
    uint256 public settledPrefix;
    
    function _owner(uint256 i) internal pure returns (Role) {
        if (i == 0) return Role.Even;
        if (i == 1) return Role.Odd;
        if (i == 2) return Role.Odd;
        if (i == 3) return Role.Even;
        if (i == 4) return Role.Odd;
        return Role.Even;
    }
    
    function _predecessors(uint256 i) internal pure returns (uint256) {
        if (i == 0) return 0;
        if (i == 1) return 0;
        if (i == 2) return 3;
        if (i == 3) return 3;
        if (i == 4) return 15;
        return 31;
    }
    
    function _isJoin(uint256 i) internal pure returns (bool) {
        if (i == 0) return true;
        if (i == 1) return true;
        if (i == 2) return false;
        if (i == 3) return false;
        if (i == 4) return false;
        return false;
    }
    
    /// Resolve every node that can be resolved now. Anyone may call this.
    function settle() public {
        _settle();
    }
    
    function _settle() internal {
        uint256 prefix = settledPrefix;
        bool contiguous = true;
        for (uint256 i = prefix; i < NODE_COUNT; i++) {
            if (resolvedAt[i] == 0) _resolve(i);
            if (contiguous && resolvedAt[i] != 0) {
                prefix = i + 1;
            } else {
                contiguous = false;
            }
        }
        settledPrefix = prefix;
    }
    
    function _readiness(uint256 i) internal view returns (uint256) {
        uint256 ready = deployedAt;
        uint256 predecessors = _predecessors(i);
        for (uint256 j = 0; j < i; j++) {
            if ((predecessors >> j) & 1 == 1) {
                uint256 t = resolvedAt[j];
                if (t == 0) return 0;
                if (t > ready) ready = t;
            }
        }
        return ready;
    }
    
    function _resolve(uint256 i) internal {
        uint256 ready = readyAt[i];
        if (ready == 0) {
            ready = _readiness(i);
            if (ready == 0) return;
            readyAt[i] = ready;
        }
        if (aborted) {
            resolvedAt[i] = ready;
            return;
        }
        Role owner = _owner(i);
        uint256 quit = quitAt[owner];
        if (quit != 0) {
            resolvedAt[i] = quit > ready ? quit : ready;
            return;
        }
        if (block.timestamp > ready + TIMEOUT) {
            quitAt[owner] = ready + TIMEOUT;
            resolvedAt[i] = ready + TIMEOUT;
            if (_isJoin(i)) aborted = true;
        }
    }
    
    /// Settle, then require that node `i` is ready, unresolved, and owned by the caller's role.
    function _beginMove(uint256 i, Role role) internal {
        _settle();
        require(roles[msg.sender] == role, "bad role");
        require(readyAt[i] != 0, "not ready");
        require(resolvedAt[i] == 0, "not open");
    }
    
    function _endMove(uint256 i) internal {
        resolvedAt[i] = block.timestamp;
    }
    
    bytes32 private constant COMMIT_TAG = keccak256("VEGAS_COMMIT_V1");
    
    function _commitmentHash(Role role, address actor, bytes memory payload) internal view returns (bytes32) {
        return keccak256(abi.encode(
            COMMIT_TAG,
            address(this),
            role,
            actor,
            keccak256(payload)
        ));
    }
    
    function _checkReveal(bytes32 commitment, Role role, address actor, bytes memory payload) internal view {
        require(_commitmentHash(role, actor, payload) == commitment, "bad reveal");
    }
    
    constructor() {
        deployedAt = block.timestamp;
    }
    
    function move_Even_0() public payable {
        _beginMove(0, Role.None);
        require((!done_Even), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Even;
        address_Even = msg.sender;
        done_Even = true;
        _endMove(0);
    }
    
    function move_Odd_1() public payable {
        _beginMove(1, Role.None);
        require((!done_Odd), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Odd;
        address_Odd = msg.sender;
        done_Odd = true;
        _endMove(1);
    }
    
    function move_Odd_2(bytes32 _hidden_c) public {
        _beginMove(2, Role.Odd);
        Odd_c_hidden = _hidden_c;
        done_Odd_c_hidden = true;
        _endMove(2);
    }
    
    function move_Even_3(bytes32 _hidden_c) public {
        _beginMove(3, Role.Even);
        Even_c_hidden = _hidden_c;
        done_Even_c_hidden = true;
        _endMove(3);
    }
    
    function move_Odd_4(bool _c, uint256 _salt) public {
        _beginMove(4, Role.Odd);
        _checkReveal(Odd_c_hidden, Role.Odd, msg.sender, abi.encode(_c, _salt));
        Odd_c = _c;
        done_Odd_c = true;
        _endMove(4);
    }
    
    function move_Even_5(bool _c, uint256 _salt) public {
        _beginMove(5, Role.Even);
        _checkReveal(Even_c_hidden, Role.Even, msg.sender, abi.encode(_c, _salt));
        Even_c = _c;
        done_Even_c = true;
        _endMove(5);
    }
    
    function withdraw_Odd() public {
        _settle();
        require(roles[msg.sender] == Role.Odd, "bad role");
        require(!claimed_Odd, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_Odd ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = (((!done_Odd_c) || (!done_Even_c)) ? (done_Odd_c ? (int256(100) + (((done_Odd_c ? int256(0) : int256(100)) + (done_Even_c ? int256(0) : int256(100))) / ((((done_Odd_c ? int256(1) : int256(0)) + (done_Even_c ? int256(1) : int256(0))) > int256(0)) ? ((done_Odd_c ? int256(1) : int256(0)) + (done_Even_c ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((Even_c == Odd_c) ? int256(74) : int256(126)));
        }
        claimed_Odd = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_Odd).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Even() public {
        _settle();
        require(roles[msg.sender] == Role.Even, "bad role");
        require(!claimed_Even, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_Even ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = (((!done_Odd_c) || (!done_Even_c)) ? (done_Even_c ? (int256(100) + (((done_Odd_c ? int256(0) : int256(100)) + (done_Even_c ? int256(0) : int256(100))) / ((((done_Odd_c ? int256(1) : int256(0)) + (done_Even_c ? int256(1) : int256(0))) > int256(0)) ? ((done_Odd_c ? int256(1) : int256(0)) + (done_Even_c ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((Even_c == Odd_c) ? int256(126) : int256(74)));
        }
        claimed_Even = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_Even).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
