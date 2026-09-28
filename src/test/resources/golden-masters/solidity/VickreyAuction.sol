// SPDX-License-Identifier: MIT
pragma solidity ^0.8.37;

contract VickreyAuction {
    enum Role { None, Seller, B1, B2, B3 }
    
    uint256 constant public ACTION_B1_0 = 0;
    uint256 constant public ACTION_B2_0 = 1;
    uint256 constant public ACTION_B3_0 = 2;
    uint256 constant public ACTION_Seller_0 = 3;
    uint256 constant public ACTION_B1_2 = 4;
    uint256 constant public ACTION_B2_4 = 5;
    uint256 constant public ACTION_B3_6 = 6;
    uint256 constant public ACTION_B1_3 = 7;
    uint256 constant public ACTION_B2_5 = 8;
    uint256 constant public ACTION_B3_7 = 9;
    mapping(address => Role) public roles;
    address public address_Seller;
    address public address_B1;
    address public address_B2;
    address public address_B3;
    bool public done_Seller;
    bool public done_B1;
    bool public done_B2;
    bool public done_B3;
    bool public claimed_Seller;
    bool public claimed_B1;
    bool public claimed_B2;
    bool public claimed_B3;
    int256 public B1_b;
    bool public done_B1_b;
    bytes32 public B1_b_hidden;
    bool public done_B1_b_hidden;
    int256 public B2_b;
    bool public done_B2_b;
    bytes32 public B2_b_hidden;
    bool public done_B2_b_hidden;
    int256 public B3_b;
    bool public done_B3_b;
    bytes32 public B3_b_hidden;
    bool public done_B3_b_hidden;
    
    receive() external payable {
        revert("direct ETH not allowed");
    }
    
    uint256 constant public TIMEOUT = 86400;
    uint256 constant public NODE_COUNT = 10;
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
        if (i == 0) return Role.B1;
        if (i == 1) return Role.B2;
        if (i == 2) return Role.B3;
        if (i == 3) return Role.Seller;
        if (i == 4) return Role.B1;
        if (i == 5) return Role.B2;
        if (i == 6) return Role.B3;
        if (i == 7) return Role.B1;
        if (i == 8) return Role.B2;
        return Role.B3;
    }
    
    function _predecessors(uint256 i) internal pure returns (uint256) {
        if (i == 0) return 0;
        if (i == 1) return 0;
        if (i == 2) return 0;
        if (i == 3) return 0;
        if (i == 4) return 15;
        if (i == 5) return 15;
        if (i == 6) return 15;
        if (i == 7) return 127;
        if (i == 8) return 255;
        return 511;
    }
    
    function _isJoin(uint256 i) internal pure returns (bool) {
        if (i == 0) return true;
        if (i == 1) return true;
        if (i == 2) return true;
        if (i == 3) return true;
        if (i == 4) return false;
        if (i == 5) return false;
        if (i == 6) return false;
        if (i == 7) return false;
        if (i == 8) return false;
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
    
    function move_B1_0() public payable {
        _beginMove(0, Role.None);
        require((!done_B1), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.B1;
        address_B1 = msg.sender;
        done_B1 = true;
        _endMove(0);
    }
    
    function move_B2_1() public payable {
        _beginMove(1, Role.None);
        require((!done_B2), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.B2;
        address_B2 = msg.sender;
        done_B2 = true;
        _endMove(1);
    }
    
    function move_B3_2() public payable {
        _beginMove(2, Role.None);
        require((!done_B3), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.B3;
        address_B3 = msg.sender;
        done_B3 = true;
        _endMove(2);
    }
    
    function move_Seller_3() public payable {
        _beginMove(3, Role.None);
        require((!done_Seller), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Seller;
        address_Seller = msg.sender;
        done_Seller = true;
        _endMove(3);
    }
    
    function move_B1_4(bytes32 _hidden_b) public {
        _beginMove(4, Role.B1);
        B1_b_hidden = _hidden_b;
        done_B1_b_hidden = true;
        _endMove(4);
    }
    
    function move_B2_5(bytes32 _hidden_b) public {
        _beginMove(5, Role.B2);
        B2_b_hidden = _hidden_b;
        done_B2_b_hidden = true;
        _endMove(5);
    }
    
    function move_B3_6(bytes32 _hidden_b) public {
        _beginMove(6, Role.B3);
        B3_b_hidden = _hidden_b;
        done_B3_b_hidden = true;
        _endMove(6);
    }
    
    function move_B1_7(int256 _b, uint256 _salt) public {
        _beginMove(7, Role.B1);
        require(((_b >= 0) && (_b <= 2)), "domain");
        _checkReveal(B1_b_hidden, Role.B1, msg.sender, abi.encode(_b, _salt));
        B1_b = _b;
        done_B1_b = true;
        _endMove(7);
    }
    
    function move_B2_8(int256 _b, uint256 _salt) public {
        _beginMove(8, Role.B2);
        require(((_b >= 0) && (_b <= 2)), "domain");
        _checkReveal(B2_b_hidden, Role.B2, msg.sender, abi.encode(_b, _salt));
        B2_b = _b;
        done_B2_b = true;
        _endMove(8);
    }
    
    function move_B3_9(int256 _b, uint256 _salt) public {
        _beginMove(9, Role.B3);
        require(((_b >= 0) && (_b <= 2)), "domain");
        _checkReveal(B3_b_hidden, Role.B3, msg.sender, abi.encode(_b, _salt));
        B3_b = _b;
        done_B3_b = true;
        _endMove(9);
    }
    
    function withdraw_Seller() public {
        _settle();
        require(roles[msg.sender] == Role.Seller, "bad role");
        require(!claimed_Seller, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_Seller ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = ((((!done_B1_b) || (!done_B2_b)) || (!done_B3_b)) ? (true ? (int256(100) + (((((true ? int256(0) : int256(100)) + (done_B1_b ? int256(0) : int256(100))) + (done_B2_b ? int256(0) : int256(100))) + (done_B3_b ? int256(0) : int256(100))) / ((((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) > int256(0)) ? ((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : (int256(100) + ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B2_b >= B3_b) ? B2_b : B3_b) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B1_b >= B3_b) ? B1_b : B3_b) : ((B1_b >= B2_b) ? B1_b : B2_b)))));
        }
        claimed_Seller = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_Seller).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B1() public {
        _settle();
        require(roles[msg.sender] == Role.B1, "bad role");
        require(!claimed_B1, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_B1 ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = ((((!done_B1_b) || (!done_B2_b)) || (!done_B3_b)) ? (done_B1_b ? (int256(100) + (((((true ? int256(0) : int256(100)) + (done_B1_b ? int256(0) : int256(100))) + (done_B2_b ? int256(0) : int256(100))) + (done_B3_b ? int256(0) : int256(100))) / ((((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) > int256(0)) ? ((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? (int256(100) - ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B2_b >= B3_b) ? B2_b : B3_b) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B1_b >= B3_b) ? B1_b : B3_b) : ((B1_b >= B2_b) ? B1_b : B2_b)))) : int256(100)));
        }
        claimed_B1 = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_B1).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B2() public {
        _settle();
        require(roles[msg.sender] == Role.B2, "bad role");
        require(!claimed_B2, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_B2 ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = ((((!done_B1_b) || (!done_B2_b)) || (!done_B3_b)) ? (done_B2_b ? (int256(100) + (((((true ? int256(0) : int256(100)) + (done_B1_b ? int256(0) : int256(100))) + (done_B2_b ? int256(0) : int256(100))) + (done_B3_b ? int256(0) : int256(100))) / ((((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) > int256(0)) ? ((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? (int256(100) - ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B2_b >= B3_b) ? B2_b : B3_b) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B1_b >= B3_b) ? B1_b : B3_b) : ((B1_b >= B2_b) ? B1_b : B2_b)))) : int256(100)));
        }
        claimed_B2 = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_B2).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B3() public {
        _settle();
        require(roles[msg.sender] == Role.B3, "bad role");
        require(!claimed_B3, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_B3 ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = ((((!done_B1_b) || (!done_B2_b)) || (!done_B3_b)) ? (done_B3_b ? (int256(100) + (((((true ? int256(0) : int256(100)) + (done_B1_b ? int256(0) : int256(100))) + (done_B2_b ? int256(0) : int256(100))) + (done_B3_b ? int256(0) : int256(100))) / ((((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) > int256(0)) ? ((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((B3_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? (int256(100) - ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B2_b >= B3_b) ? B2_b : B3_b) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B1_b >= B3_b) ? B1_b : B3_b) : ((B1_b >= B2_b) ? B1_b : B2_b)))) : int256(100)));
        }
        claimed_B3 = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_B3).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
