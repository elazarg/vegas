pragma solidity ^0.8.31;

contract MontyHallChance {
    enum Role { None, Guest, Host }
    
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 public lastTs;
    uint256 constant public TIMEOUT = 86400;
    mapping(Role => bool) public bailed;
    uint256 constant public ACTION_Host_0 = 0;
    uint256 constant public ACTION_Guest_1 = 1;
    uint256 constant public ACTION_Host_2 = 2;
    uint256 constant public ACTION_Guest_3 = 3;
    uint256 constant public ACTION_Host_4 = 4;
    uint256 constant public ACTION_Guest_5 = 5;
    uint256 constant public ACTION_Host_6 = 6;
    mapping(address => Role) public roles;
    address public address_Guest;
    address public address_Host;
    bool public done_Guest;
    bool public done_Host;
    bool public claimed_Guest;
    bool public claimed_Host;
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
    
    constructor() {
        lastTs = block.timestamp;
    }
    
    function _check_timestamp(Role _role) internal {
        if ((_role == Role.None))
         {
            return;
        }
        if ((block.timestamp > (lastTs + _TIMEOUT)))
         {
            bailed[_role] = true;
            lastTs = block.timestamp;
        }
    }
    
    
    function move_Host_0() public payable {
        require((roles[msg.sender] == Role.Host), "bad role");
        _check_timestamp(Role.Host);
        require((!bailed[Role.Host]), "you bailed");
        require((!actionDone[Role.Host][0]), "already done");
        require((!done_Host), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Host;
        address_Host = msg.sender;
        done_Host = true;
        actionDone[Role.Host][0] = true;
        actionTimestamp[Role.Host][0] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Guest_1() public payable {
        require((roles[msg.sender] == Role.Guest), "bad role");
        _check_timestamp(Role.Guest);
        require((!bailed[Role.Guest]), "you bailed");
        require((!actionDone[Role.Guest][1]), "already done");
        _check_timestamp(Role.Host);
        if ((!bailed[Role.Host]))
         {
            require(actionDone[Role.Host][0], "dependency not satisfied");
        }
        require((!done_Guest), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Guest;
        address_Guest = msg.sender;
        done_Guest = true;
        actionDone[Role.Guest][1] = true;
        actionTimestamp[Role.Guest][1] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Host_2(bytes32 _hidden_car) public {
        require((roles[msg.sender] == Role.Host), "bad role");
        _check_timestamp(Role.Host);
        require((!bailed[Role.Host]), "you bailed");
        require((!actionDone[Role.Host][2]), "already done");
        _check_timestamp(Role.Guest);
        if ((!bailed[Role.Guest]))
         {
            require(actionDone[Role.Guest][1], "dependency not satisfied");
        }
        Host_car_hidden = _hidden_car;
        done_Host_car_hidden = true;
        actionDone[Role.Host][2] = true;
        actionTimestamp[Role.Host][2] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Guest_3(int256 _d) public {
        require((roles[msg.sender] == Role.Guest), "bad role");
        _check_timestamp(Role.Guest);
        require((!bailed[Role.Guest]), "you bailed");
        require((!actionDone[Role.Guest][3]), "already done");
        _check_timestamp(Role.Host);
        if ((!bailed[Role.Host]))
         {
            require(actionDone[Role.Host][2], "dependency not satisfied");
        }
        require((((_d == 0) || (_d == 1)) || (_d == 2)), "domain");
        Guest_d = _d;
        done_Guest_d = true;
        actionDone[Role.Guest][3] = true;
        actionTimestamp[Role.Guest][3] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Host_4(int256 _goat) public {
        require((roles[msg.sender] == Role.Host), "bad role");
        _check_timestamp(Role.Host);
        require((!bailed[Role.Host]), "you bailed");
        require((!actionDone[Role.Host][4]), "already done");
        _check_timestamp(Role.Host);
        if ((!bailed[Role.Host]))
         {
            require(actionDone[Role.Host][2], "dependency not satisfied");
        }
        _check_timestamp(Role.Guest);
        if ((!bailed[Role.Guest]))
         {
            require(actionDone[Role.Guest][3], "dependency not satisfied");
        }
        require((((_goat == 0) || (_goat == 1)) || (_goat == 2)), "domain");
        require(((_goat != Guest_d) && (_goat != Host_car)), "domain");
        Host_goat = _goat;
        done_Host_goat = true;
        actionDone[Role.Host][4] = true;
        actionTimestamp[Role.Host][4] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Guest_5(bool _switch) public {
        require((roles[msg.sender] == Role.Guest), "bad role");
        _check_timestamp(Role.Guest);
        require((!bailed[Role.Guest]), "you bailed");
        require((!actionDone[Role.Guest][5]), "already done");
        _check_timestamp(Role.Host);
        if ((!bailed[Role.Host]))
         {
            require(actionDone[Role.Host][4], "dependency not satisfied");
        }
        Guest_switch = _switch;
        done_Guest_switch = true;
        actionDone[Role.Guest][5] = true;
        actionTimestamp[Role.Guest][5] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Host_6(int256 _car, uint256 _salt) public {
        require((roles[msg.sender] == Role.Host), "bad role");
        _check_timestamp(Role.Host);
        require((!bailed[Role.Host]), "you bailed");
        require((!actionDone[Role.Host][6]), "already done");
        _check_timestamp(Role.Host);
        if ((!bailed[Role.Host]))
         {
            require(actionDone[Role.Host][2], "dependency not satisfied");
        }
        _check_timestamp(Role.Guest);
        if ((!bailed[Role.Guest]))
         {
            require(actionDone[Role.Guest][5], "dependency not satisfied");
        }
        require((((_car == 0) || (_car == 1)) || (_car == 2)), "domain");
        require((keccak256(abi.encodePacked(_car, _salt)) == Host_car_hidden), "reveal failed for car");
        Host_car = _car;
        done_Host_car = true;
        actionDone[Role.Host][6] = true;
        actionTimestamp[Role.Host][6] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function withdraw_Guest() public {
        require((!claimed_Guest), "already claimed");
        claimed_Guest = true;
        int256 payout = (((done_Host_car && done_Host_goat) && done_Guest_switch) ? (((Guest_d != Host_car) == Guest_switch) ? 120 : 80) : (((!done_Host_car) || (!done_Host_goat)) ? 200 : 0));
        if (payout > 0) {
            (bool ok, ) = payable(address_Guest).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Host() public {
        require((!claimed_Host), "already claimed");
        claimed_Host = true;
        int256 payout = (((done_Host_car && done_Host_goat) && done_Guest_switch) ? (((Guest_d != Host_car) == Guest_switch) ? 80 : 120) : (((!done_Host_car) || (!done_Host_goat)) ? 0 : 200));
        if (payout > 0) {
            (bool ok, ) = payable(address_Host).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
