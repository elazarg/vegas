// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

contract MontyHall {
    enum Role { None, Host, Guest }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
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
    
    mapping(Role => bool) private bailed;
    
    modifier action(Role role, uint256 actionId) {
        require((!actionDone[role][actionId]), "already done");
        actionDone[role][actionId] = true;
        _;
        actionTimestamp[role][actionId] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    modifier by(Role role) {
        require((roles[msg.sender] == role), "bad role");
        require(!bailed[role], "you bailed");
        _;
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
        lastTs = block.timestamp;
    }
    
    function move_Host_0() public payable by(Role.None) action(Role.Host, 0) {
        require((!done_Host), "already joined");
        require((msg.value == 20), "bad stake");
        roles[msg.sender] = Role.Host;
        address_Host = msg.sender;
        done_Host = true;
    }
    
    function move_Guest_1() public payable by(Role.None) action(Role.Guest, 1) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Host][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Host] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Host]) {
                require(actionDone[Role.Host][0], "dependency not satisfied");
            }
        }
        require((!done_Guest), "already joined");
        require((msg.value == 20), "bad stake");
        roles[msg.sender] = Role.Guest;
        address_Guest = msg.sender;
        done_Guest = true;
    }
    
    function move_Host_2(bytes32 _hidden_car) public by(Role.Host) action(Role.Host, 2) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Guest][1] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Guest] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Guest]) {
                require(actionDone[Role.Guest][1], "dependency not satisfied");
            }
        }
        Host_car_hidden = _hidden_car;
        done_Host_car_hidden = true;
    }
    
    function move_Guest_3(int256 _d) public by(Role.Guest) action(Role.Guest, 3) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Host][2] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Host] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Host]) {
                require(actionDone[Role.Host][2], "dependency not satisfied");
            }
        }
        require(((_d >= 0) && (_d <= 2)), "domain");
        Guest_d = _d;
        done_Guest_d = true;
    }
    
    function move_Host_4(int256 _goat) public by(Role.Host) action(Role.Host, 4) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Guest][3] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Guest] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Guest]) {
                require(actionDone[Role.Guest][3], "dependency not satisfied");
            }
        }
        require(((_goat >= 0) && (_goat <= 2)), "domain");
        require((_goat != Guest_d), "domain");
        Host_goat = _goat;
        done_Host_goat = true;
    }
    
    function move_Guest_5(bool _switch) public by(Role.Guest) action(Role.Guest, 5) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Host][4] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Host] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Host]) {
                require(actionDone[Role.Host][4], "dependency not satisfied");
            }
        }
        Guest_switch = _switch;
        done_Guest_switch = true;
    }
    
    function move_Host_6(int256 _car, uint256 _salt) public by(Role.Host) action(Role.Host, 6) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Host][2] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Host] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Host]) {
                require(actionDone[Role.Host][2], "dependency not satisfied");
            }
            if (!actionDone[Role.Host][4] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Host] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Host]) {
                require(actionDone[Role.Host][4], "dependency not satisfied");
            }
            if (!actionDone[Role.Guest][5] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Guest] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Guest]) {
                require(actionDone[Role.Guest][5], "dependency not satisfied");
            }
        }
        require(((_car >= 0) && (_car <= 2)), "domain");
        require((Host_goat != _car), "domain");
        _checkReveal(Host_car_hidden, Role.Host, msg.sender, abi.encode(_car, _salt));
        Host_car = _car;
        done_Host_car = true;
    }
    
    function withdraw_Host() public by(Role.Host) action(Role.Host, 7) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Host][6] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Host] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Host]) {
                require(actionDone[Role.Host][6], "dependency not satisfied");
            }
        }
        require((!claimed_Host), "already claimed");
        claimed_Host = true;
        int256 payout = ((!done_Host_car) ? (done_Host_car ? (int256(20) + (((done_Host_car ? int256(0) : int256(20)) + (true ? int256(0) : int256(20))) / ((((done_Host_car ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) > int256(0)) ? ((done_Host_car ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Guest_d) ? (done_Host_car ? (int256(20) + (((done_Host_car ? int256(0) : int256(20)) + (done_Guest_d ? int256(0) : int256(20))) / ((((done_Host_car ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) > int256(0)) ? ((done_Host_car ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Host_goat) ? ((done_Host_car && done_Host_goat) ? (int256(20) + ((((done_Host_car && done_Host_goat) ? int256(0) : int256(20)) + (done_Guest_d ? int256(0) : int256(20))) / (((((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) > int256(0)) ? (((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Guest_switch) ? ((done_Host_car && done_Host_goat) ? (int256(20) + ((((done_Host_car && done_Host_goat) ? int256(0) : int256(20)) + ((done_Guest_d && done_Guest_switch) ? int256(0) : int256(20))) / (((((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + ((done_Guest_d && done_Guest_switch) ? int256(1) : int256(0))) > int256(0)) ? (((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + ((done_Guest_d && done_Guest_switch) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : (((Guest_d != Host_car) == Guest_switch) ? int256(0) : int256(40))))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Host).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Guest() public by(Role.Guest) action(Role.Guest, 6) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Host][6] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Host] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Host]) {
                require(actionDone[Role.Host][6], "dependency not satisfied");
            }
        }
        require((!claimed_Guest), "already claimed");
        claimed_Guest = true;
        int256 payout = ((!done_Host_car) ? (true ? (int256(20) + (((done_Host_car ? int256(0) : int256(20)) + (true ? int256(0) : int256(20))) / ((((done_Host_car ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) > int256(0)) ? ((done_Host_car ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Guest_d) ? (done_Guest_d ? (int256(20) + (((done_Host_car ? int256(0) : int256(20)) + (done_Guest_d ? int256(0) : int256(20))) / ((((done_Host_car ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) > int256(0)) ? ((done_Host_car ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Host_goat) ? (done_Guest_d ? (int256(20) + ((((done_Host_car && done_Host_goat) ? int256(0) : int256(20)) + (done_Guest_d ? int256(0) : int256(20))) / (((((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) > int256(0)) ? (((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + (done_Guest_d ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_Guest_switch) ? ((done_Guest_d && done_Guest_switch) ? (int256(20) + ((((done_Host_car && done_Host_goat) ? int256(0) : int256(20)) + ((done_Guest_d && done_Guest_switch) ? int256(0) : int256(20))) / (((((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + ((done_Guest_d && done_Guest_switch) ? int256(1) : int256(0))) > int256(0)) ? (((done_Host_car && done_Host_goat) ? int256(1) : int256(0)) + ((done_Guest_d && done_Guest_switch) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : (((Guest_d != Host_car) == Guest_switch) ? int256(40) : int256(0))))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Guest).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
