// SPDX-License-Identifier: MIT
pragma solidity ^0.8.37;

contract Prisoners {
    enum Role { None, A, B }
    
    uint256 constant public ACTION_A_0 = 0;
    uint256 constant public ACTION_B_1 = 1;
    uint256 constant public ACTION_A_3 = 2;
    uint256 constant public ACTION_B_5 = 3;
    uint256 constant public ACTION_A_4 = 4;
    uint256 constant public ACTION_B_6 = 5;
    mapping(address => Role) public roles;
    address public address_A;
    address public address_B;
    bool public done_A;
    bool public done_B;
    bool public claimed_A;
    bool public claimed_B;
    bool public A_c;
    bool public done_A_c;
    bytes32 public A_c_hidden;
    bool public done_A_c_hidden;
    bool public B_c;
    bool public done_B_c;
    bytes32 public B_c_hidden;
    bool public done_B_c_hidden;
    
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
        if (i == 0) return Role.A;
        if (i == 1) return Role.B;
        if (i == 2) return Role.A;
        if (i == 3) return Role.B;
        if (i == 4) return Role.A;
        return Role.B;
    }
    
    function _predecessors(uint256 i) internal pure returns (uint256) {
        if (i == 0) return 0;
        if (i == 1) return 1;
        if (i == 2) return 2;
        if (i == 3) return 2;
        if (i == 4) return 14;
        return 30;
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
    
    function move_A_0() public payable {
        _beginMove(0, Role.None);
        require((!done_A), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.A;
        address_A = msg.sender;
        done_A = true;
        _endMove(0);
    }
    
    function move_B_1() public payable {
        _beginMove(1, Role.None);
        require((!done_B), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.B;
        address_B = msg.sender;
        done_B = true;
        _endMove(1);
    }
    
    function move_A_2(bytes32 _hidden_c) public {
        _beginMove(2, Role.A);
        A_c_hidden = _hidden_c;
        done_A_c_hidden = true;
        _endMove(2);
    }
    
    function move_B_3(bytes32 _hidden_c) public {
        _beginMove(3, Role.B);
        B_c_hidden = _hidden_c;
        done_B_c_hidden = true;
        _endMove(3);
    }
    
    function move_A_4(bool _c, uint256 _salt) public {
        _beginMove(4, Role.A);
        _checkReveal(A_c_hidden, Role.A, msg.sender, abi.encode(_c, _salt));
        A_c = _c;
        done_A_c = true;
        _endMove(4);
    }
    
    function move_B_5(bool _c, uint256 _salt) public {
        _beginMove(5, Role.B);
        _checkReveal(B_c_hidden, Role.B, msg.sender, abi.encode(_c, _salt));
        B_c = _c;
        done_B_c = true;
        _endMove(5);
    }
    
    function withdraw_A() public {
        _settle();
        require(roles[msg.sender] == Role.A, "bad role");
        require(!claimed_A, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_A ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = (((!done_A_c) || (!done_B_c)) ? (done_A_c ? (int256(100) + (((done_A_c ? int256(0) : int256(100)) + (done_B_c ? int256(0) : int256(100))) / ((((done_A_c ? int256(1) : int256(0)) + (done_B_c ? int256(1) : int256(0))) > int256(0)) ? ((done_A_c ? int256(1) : int256(0)) + (done_B_c ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((A_c && B_c) ? int256(100) : ((A_c && (!B_c)) ? int256(0) : (((!A_c) && B_c) ? int256(200) : int256(90)))));
        }
        claimed_A = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_A).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B() public {
        _settle();
        require(roles[msg.sender] == Role.B, "bad role");
        require(!claimed_B, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_B ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = (((!done_A_c) || (!done_B_c)) ? (done_B_c ? (int256(100) + (((done_A_c ? int256(0) : int256(100)) + (done_B_c ? int256(0) : int256(100))) / ((((done_A_c ? int256(1) : int256(0)) + (done_B_c ? int256(1) : int256(0))) > int256(0)) ? ((done_A_c ? int256(1) : int256(0)) + (done_B_c ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((A_c && B_c) ? int256(100) : ((A_c && (!B_c)) ? int256(200) : (((!A_c) && B_c) ? int256(0) : int256(110)))));
        }
        claimed_B = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_B).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
