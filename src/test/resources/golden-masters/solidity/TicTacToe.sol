// SPDX-License-Identifier: MIT
pragma solidity ^0.8.37;

contract TicTacToe {
    enum Role { None, X, O }
    
    uint256 constant public ACTION_X_0 = 0;
    uint256 constant public ACTION_O_1 = 1;
    uint256 constant public ACTION_X_2 = 2;
    uint256 constant public ACTION_O_3 = 3;
    uint256 constant public ACTION_X_4 = 4;
    uint256 constant public ACTION_O_5 = 5;
    uint256 constant public ACTION_X_6 = 6;
    uint256 constant public ACTION_O_7 = 7;
    uint256 constant public ACTION_X_8 = 8;
    uint256 constant public ACTION_O_9 = 9;
    mapping(address => Role) public roles;
    address public address_X;
    address public address_O;
    bool public done_X;
    bool public done_O;
    bool public claimed_X;
    bool public claimed_O;
    int256 public X_c1;
    bool public done_X_c1;
    int256 public O_c1;
    bool public done_O_c1;
    int256 public X_c2;
    bool public done_X_c2;
    int256 public O_c2;
    bool public done_O_c2;
    int256 public X_c3;
    bool public done_X_c3;
    int256 public O_c3;
    bool public done_O_c3;
    int256 public X_c4;
    bool public done_X_c4;
    int256 public O_c4;
    bool public done_O_c4;
    
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
        if (i == 0) return Role.X;
        if (i == 1) return Role.O;
        if (i == 2) return Role.X;
        if (i == 3) return Role.O;
        if (i == 4) return Role.X;
        if (i == 5) return Role.O;
        if (i == 6) return Role.X;
        if (i == 7) return Role.O;
        if (i == 8) return Role.X;
        return Role.O;
    }
    
    function _predecessors(uint256 i) internal pure returns (uint256) {
        if (i == 0) return 0;
        if (i == 1) return 1;
        if (i == 2) return 2;
        if (i == 3) return 4;
        if (i == 4) return 12;
        if (i == 5) return 28;
        if (i == 6) return 60;
        if (i == 7) return 124;
        if (i == 8) return 252;
        return 508;
    }
    
    function _isJoin(uint256 i) internal pure returns (bool) {
        if (i == 0) return true;
        if (i == 1) return true;
        if (i == 2) return false;
        if (i == 3) return false;
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
    
    function move_X_0() public payable {
        _beginMove(0, Role.None);
        require((!done_X), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.X;
        address_X = msg.sender;
        done_X = true;
        _endMove(0);
    }
    
    function move_O_1() public payable {
        _beginMove(1, Role.None);
        require((!done_O), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.O;
        address_O = msg.sender;
        done_O = true;
        _endMove(1);
    }
    
    function move_X_2(int256 _c1) public {
        _beginMove(2, Role.X);
        require(((_c1 >= 0) && (_c1 <= 8)), "domain");
        X_c1 = _c1;
        done_X_c1 = true;
        _endMove(2);
    }
    
    function move_O_3(int256 _c1) public {
        _beginMove(3, Role.O);
        require(((_c1 >= 0) && (_c1 <= 8)), "domain");
        require(((!done_X_c1) || (X_c1 != _c1)), "domain");
        O_c1 = _c1;
        done_O_c1 = true;
        _endMove(3);
    }
    
    function move_X_4(int256 _c2) public {
        _beginMove(4, Role.X);
        require(((_c2 >= 0) && (_c2 <= 8)), "domain");
        require(((!done_O_c1) || (((X_c1 != O_c1) && (X_c1 != _c2)) && (O_c1 != _c2))), "domain");
        X_c2 = _c2;
        done_X_c2 = true;
        _endMove(4);
    }
    
    function move_O_5(int256 _c2) public {
        _beginMove(5, Role.O);
        require(((_c2 >= 0) && (_c2 <= 8)), "domain");
        require((((!done_X_c1) || (!done_X_c2)) || ((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != _c2)) && (O_c1 != X_c2)) && (O_c1 != _c2)) && (X_c2 != _c2))), "domain");
        O_c2 = _c2;
        done_O_c2 = true;
        _endMove(5);
    }
    
    function move_X_6(int256 _c3) public {
        _beginMove(6, Role.X);
        require(((_c3 >= 0) && (_c3 <= 8)), "domain");
        require((((!done_O_c1) || (!done_O_c2)) || ((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != _c3)) && (O_c2 != _c3))), "domain");
        X_c3 = _c3;
        done_X_c3 = true;
        _endMove(6);
    }
    
    function move_O_7(int256 _c3) public {
        _beginMove(7, Role.O);
        require(((_c3 >= 0) && (_c3 <= 8)), "domain");
        require(((((!done_X_c1) || (!done_X_c2)) || (!done_X_c3)) || (((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != _c3)) && (O_c2 != X_c3)) && (O_c2 != _c3)) && (X_c3 != _c3))), "domain");
        O_c3 = _c3;
        done_O_c3 = true;
        _endMove(7);
    }
    
    function move_X_8(int256 _c4) public {
        _beginMove(8, Role.X);
        require(((_c4 >= 0) && (_c4 <= 8)), "domain");
        require(((((!done_O_c1) || (!done_O_c2)) || (!done_O_c3)) || (((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != _c4)) && (O_c3 != _c4))), "domain");
        X_c4 = _c4;
        done_X_c4 = true;
        _endMove(8);
    }
    
    function move_O_9(int256 _c4) public {
        _beginMove(9, Role.O);
        require(((_c4 >= 0) && (_c4 <= 8)), "domain");
        require((((((!done_X_c1) || (!done_X_c2)) || (!done_X_c3)) || (!done_X_c4)) || ((((((((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != X_c4)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != X_c4)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != X_c4)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != X_c4)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != X_c4)) && (X_c3 != _c4)) && (O_c3 != X_c4)) && (O_c3 != _c4)) && (X_c4 != _c4))), "domain");
        O_c4 = _c4;
        done_O_c4 = true;
        _endMove(9);
    }
    
    function withdraw_X() public {
        _settle();
        require(roles[msg.sender] == Role.X, "bad role");
        require(!claimed_X, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_X ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = ((!done_X_c1) ? (done_X_c1 ? (int256(100) + (((done_X_c1 ? int256(0) : int256(100)) + (true ? int256(0) : int256(100))) / ((((done_X_c1 ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) > int256(0)) ? ((done_X_c1 ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c1) ? (done_X_c1 ? (int256(100) + (((done_X_c1 ? int256(0) : int256(100)) + (done_O_c1 ? int256(0) : int256(100))) / ((((done_X_c1 ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) > int256(0)) ? ((done_X_c1 ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c2) ? ((done_X_c1 && done_X_c2) ? (int256(100) + ((((done_X_c1 && done_X_c2) ? int256(0) : int256(100)) + (done_O_c1 ? int256(0) : int256(100))) / (((((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) > int256(0)) ? (((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c2) ? ((done_X_c1 && done_X_c2) ? (int256(100) + ((((done_X_c1 && done_X_c2) ? int256(0) : int256(100)) + ((done_O_c1 && done_O_c2) ? int256(0) : int256(100))) / (((((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) > int256(0)) ? (((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c3) ? (((done_X_c1 && done_X_c2) && done_X_c3) ? (int256(100) + (((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(0) : int256(100)) + ((done_O_c1 && done_O_c2) ? int256(0) : int256(100))) / ((((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) > int256(0)) ? ((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c3) ? (((done_X_c1 && done_X_c2) && done_X_c3) ? (int256(100) + (((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(0) : int256(100)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(0) : int256(100))) / ((((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) > int256(0)) ? ((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c4) ? ((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? (int256(100) + ((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(0) : int256(100)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(0) : int256(100))) / (((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) > int256(0)) ? (((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c4) ? ((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? (int256(100) + ((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(0) : int256(100)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(0) : int256(100))) / (((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(1) : int256(0))) > int256(0)) ? (((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : int256(100)))))))));
        }
        claimed_X = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_X).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_O() public {
        _settle();
        require(roles[msg.sender] == Role.O, "bad role");
        require(!claimed_O, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_O ? int256(100) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = ((!done_X_c1) ? (true ? (int256(100) + (((done_X_c1 ? int256(0) : int256(100)) + (true ? int256(0) : int256(100))) / ((((done_X_c1 ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) > int256(0)) ? ((done_X_c1 ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c1) ? (done_O_c1 ? (int256(100) + (((done_X_c1 ? int256(0) : int256(100)) + (done_O_c1 ? int256(0) : int256(100))) / ((((done_X_c1 ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) > int256(0)) ? ((done_X_c1 ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c2) ? (done_O_c1 ? (int256(100) + ((((done_X_c1 && done_X_c2) ? int256(0) : int256(100)) + (done_O_c1 ? int256(0) : int256(100))) / (((((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) > int256(0)) ? (((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c2) ? ((done_O_c1 && done_O_c2) ? (int256(100) + ((((done_X_c1 && done_X_c2) ? int256(0) : int256(100)) + ((done_O_c1 && done_O_c2) ? int256(0) : int256(100))) / (((((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) > int256(0)) ? (((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c3) ? ((done_O_c1 && done_O_c2) ? (int256(100) + (((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(0) : int256(100)) + ((done_O_c1 && done_O_c2) ? int256(0) : int256(100))) / ((((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) > int256(0)) ? ((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c3) ? (((done_O_c1 && done_O_c2) && done_O_c3) ? (int256(100) + (((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(0) : int256(100)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(0) : int256(100))) / ((((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) > int256(0)) ? ((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c4) ? (((done_O_c1 && done_O_c2) && done_O_c3) ? (int256(100) + ((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(0) : int256(100)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(0) : int256(100))) / (((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) > int256(0)) ? (((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c4) ? ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? (int256(100) + ((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(0) : int256(100)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(0) : int256(100))) / (((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(1) : int256(0))) > int256(0)) ? (((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : int256(100)))))))));
        }
        claimed_O = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_O).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
