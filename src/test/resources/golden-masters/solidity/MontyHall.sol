// SPDX-License-Identifier: MIT
pragma solidity ^0.8.37;

contract MontyHall {
    enum Role { None, Host, Guest }
    
    uint256 constant public ACTION_Host_0 = 0;
    uint256 constant public ACTION_Guest_1 = 1;
    uint256 constant public ACTION_Host_2 = 2;
    uint256 constant public ACTION_Guest_3 = 3;
    uint256 constant public ACTION_Host_4 = 4;
    uint256 constant public ACTION_Guest_5 = 5;
    uint256 constant public ACTION_Host_6 = 6;
    mapping(address => Role) public roles;
    address public address_Host;
    address public address_Guest;
    bool public done_Host;
    bool public done_Guest;
    bool public claimed_Host;
    bool public claimed_Guest;
    int256 public Host_car;
    bool public done_Host_car;
    bytes32 public Host_car_hidden;
    bool public done_Host_car_hidden;
    int256 public Guest_d;
    bool public done_Guest_d;
    int256 public Host_goat;
    bool public done_Host_goat;
    bool public Guest_switch;
    bool public done_Guest_switch;
    
    receive() external payable {
        revert("direct ETH not allowed");
    }
    
    uint256 constant public TIMEOUT = 86400;
    uint256 constant public NODE_COUNT = 7;
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
        if (i == 0) return Role.Host;
        if (i == 1) return Role.Guest;
        if (i == 2) return Role.Host;
        if (i == 3) return Role.Guest;
        if (i == 4) return Role.Host;
        if (i == 5) return Role.Guest;
        return Role.Host;
    }
    
    function _predecessors(uint256 i) internal pure returns (uint256) {
        if (i == 0) return 0;
        if (i == 1) return 1;
        if (i == 2) return 2;
        if (i == 3) return 4;
        if (i == 4) return 8;
        if (i == 5) return 16;
        return 52;
    }
    
    function _isJoin(uint256 i) internal pure returns (bool) {
        if (i == 0) return true;
        if (i == 1) return true;
        if (i == 2) return false;
        if (i == 3) return false;
        if (i == 4) return false;
        if (i == 5) return false;
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
    
    function move_Host_0() public payable {
        _beginMove(0, Role.None);
        require((!done_Host), "already joined");
        require((msg.value == 20), "bad stake");
        roles[msg.sender] = Role.Host;
        address_Host = msg.sender;
        done_Host = true;
        _endMove(0);
    }
    
    function move_Guest_1() public payable {
        _beginMove(1, Role.None);
        require((!done_Guest), "already joined");
        require((msg.value == 20), "bad stake");
        roles[msg.sender] = Role.Guest;
        address_Guest = msg.sender;
        done_Guest = true;
        _endMove(1);
    }
    
    function move_Host_2(bytes32 _hidden_car) public {
        _beginMove(2, Role.Host);
        Host_car_hidden = _hidden_car;
        done_Host_car_hidden = true;
        _endMove(2);
    }
    
    function move_Guest_3(int256 _d) public {
        _beginMove(3, Role.Guest);
        require(((_d >= 0) && (_d <= 2)), "domain");
        Guest_d = _d;
        done_Guest_d = true;
        _endMove(3);
    }
    
    function move_Host_4(int256 _goat) public {
        _beginMove(4, Role.Host);
        require(((_goat >= 0) && (_goat <= 2)), "domain");
        require(((!done_Guest_d) || (_goat != Guest_d)), "domain");
        Host_goat = _goat;
        done_Host_goat = true;
        _endMove(4);
    }
    
    function move_Guest_5(bool _switch) public {
        _beginMove(5, Role.Guest);
        Guest_switch = _switch;
        done_Guest_switch = true;
        _endMove(5);
    }
    
    function move_Host_6(int256 _car, uint256 _salt) public {
        _beginMove(6, Role.Host);
        require(((_car >= 0) && (_car <= 2)), "domain");
        require((Host_goat != _car), "domain");
        _checkReveal(Host_car_hidden, Role.Host, msg.sender, abi.encode(_car, _salt));
        Host_car = _car;
        done_Host_car = true;
        _endMove(6);
    }
    
    function withdraw_Host() public {
        _settle();
        require(roles[msg.sender] == Role.Host, "bad role");
        require(!claimed_Host, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_Host ? int256(20) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = ((!done_Host_car) ? (done_Host_car ? (int256(20) + (((done_Host_car ? int256(0) : int256(20)) + (true ? int256(0) : int256(20))) / ((((done_Host_car ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) > int256(0)) ? ((done_Host_car ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Guest_d) ? (done_Host_car ? (int256(20) + (((done_Host_car ? int256(0) : int256(20)) + (done_Guest_d ? int256(0) : int256(20))) / ((((done_Host_car ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) > int256(0)) ? ((done_Host_car ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Host_goat) ? ((done_Host_car && done_Host_goat) ? (int256(20) + ((((done_Host_car && done_Host_goat) ? int256(0) : int256(20)) + (done_Guest_d ? int256(0) : int256(20))) / (((((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) > int256(0)) ? (((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Guest_switch) ? ((done_Host_car && done_Host_goat) ? (int256(20) + ((((done_Host_car && done_Host_goat) ? int256(0) : int256(20)) + ((done_Guest_d && done_Guest_switch) ? int256(0) : int256(20))) / (((((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + ((done_Guest_d && done_Guest_switch) ? int256(1) : int256(0))) > int256(0)) ? (((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + ((done_Guest_d && done_Guest_switch) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : (((Guest_d != Host_car) == Guest_switch) ? int256(0) : int256(40))))));
        }
        claimed_Host = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_Host).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Guest() public {
        _settle();
        require(roles[msg.sender] == Role.Guest, "bad role");
        require(!claimed_Guest, "already claimed");
        int256 payout;
        if (aborted) {
            payout = done_Guest ? int256(20) : int256(0);
        } else {
            require(settledPrefix == NODE_COUNT, "game not finished");
            payout = ((!done_Host_car) ? (true ? (int256(20) + (((done_Host_car ? int256(0) : int256(20)) + (true ? int256(0) : int256(20))) / ((((done_Host_car ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) > int256(0)) ? ((done_Host_car ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Guest_d) ? (done_Guest_d ? (int256(20) + (((done_Host_car ? int256(0) : int256(20)) + (done_Guest_d ? int256(0) : int256(20))) / ((((done_Host_car ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) > int256(0)) ? ((done_Host_car ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Host_goat) ? (done_Guest_d ? (int256(20) + ((((done_Host_car && done_Host_goat) ? int256(0) : int256(20)) + (done_Guest_d ? int256(0) : int256(20))) / (((((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) > int256(0)) ? (((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Guest_switch) ? ((done_Guest_d && done_Guest_switch) ? (int256(20) + ((((done_Host_car && done_Host_goat) ? int256(0) : int256(20)) + ((done_Guest_d && done_Guest_switch) ? int256(0) : int256(20))) / (((((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + ((done_Guest_d && done_Guest_switch) ? int256(1) : int256(0))) > int256(0)) ? (((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + ((done_Guest_d && done_Guest_switch) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : (((Guest_d != Host_car) == Guest_switch) ? int256(40) : int256(0))))));
        }
        claimed_Guest = true;
        if (payout > 0) {
            (bool ok, ) = payable(address_Guest).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
