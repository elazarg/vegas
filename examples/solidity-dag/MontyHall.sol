pragma solidity ^0.8.31;

contract MontyHall {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Host, Guest }

    uint256 public lastTs;

    mapping(uint256 => bool) public actionDone;

    mapping(uint256 => uint256) public actionTimestamp;

    uint256 constant public ACTION_Host_0 = 0;

    uint256 constant public ACTION_Guest_1 = 1;

    uint256 constant public ACTION_Host_2 = 2;

    uint256 constant public ACTION_Guest_3 = 3;

    uint256 constant public ACTION_Host_4 = 4;

    uint256 constant public ACTION_Guest_5 = 5;

    uint256 constant public ACTION_Host_6 = 6;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Host;

    address public address_Guest;

    bool public payoffs_distributed;

    bool public done_Host;

    bool public done_Guest;

    uint256 public Host_hidden_car;

    bool public done_Host_hidden_car;

    int256 public Host_car;

    bool public done_Host_car;

    int256 public Guest_d;

    bool public done_Guest_d;

    int256 public Host_goat;

    bool public done_Host_goat;

    bool public Guest_switch;

    bool public done_Guest_switch;

    modifier depends(uint256 actionId) {
        require(actionDone[actionId], "dependency not satisfied");
    }

    modifier notDone(uint256 actionId) {
        require((!actionDone[actionId]), "already done");
    }

    modifier by(Role r) {
        require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
        require(actionDone[6], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function move_Host_0() public payable by(Role.None) notDone(0) {
        require((!done_Host), "already joined");
        role[msg.sender] = Role.Host;
        address_Host = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Host = true;
        actionDone[0] = true;
        actionTimestamp[0] = block.timestamp;
    }

    function move_Guest_1() public payable by(Role.None) notDone(1) {
        require((!done_Guest), "already joined");
        role[msg.sender] = Role.Guest;
        address_Guest = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Guest = true;
        actionDone[1] = true;
        actionTimestamp[1] = block.timestamp;
    }

    function move_Host_2(uint256 _hidden_car) public by(Role.Host) notDone(2) {
        Host_hidden_car = _hidden_car;
        done_Host_hidden_car = true;
        actionDone[2] = true;
        actionTimestamp[2] = block.timestamp;
    }

    function move_Guest_3(int256 _d) public by(Role.Guest) notDone(3) {
        require((((_d == 0) || (_d == 1)) || (_d == 2)), "domain");
        Guest_d = _d;
        done_Guest_d = true;
        actionDone[3] = true;
        actionTimestamp[3] = block.timestamp;
    }

    function move_Guest_5(bool _switch) public by(Role.Guest) notDone(5) {
        Guest_switch = _switch;
        done_Guest_switch = true;
        actionDone[5] = true;
        actionTimestamp[5] = block.timestamp;
    }

    function move_Host_4(int256 _goat) public by(Role.Host) notDone(4) depends(3) {
        require((((_goat == 0) || (_goat == 1)) || (_goat == 2)), "domain");
        require((_goat != Guest_d), "where");
        Host_goat = _goat;
        done_Host_goat = true;
        actionDone[4] = true;
        actionTimestamp[4] = block.timestamp;
    }

    function move_Host_6(int256 _car, uint256 salt) public by(Role.Host) notDone(6) depends(4) depends(2) {
        require((keccak256(abi.encodePacked(_car, salt)) == bytes32(Host_hidden_car)), "bad reveal");
        require((((_car == 0) || (_car == 1)) || (_car == 2)), "domain");
        require((Host_goat != _car), "where");
        Host_car = _car;
        done_Host_car = true;
        actionDone[6] = true;
        actionTimestamp[6] = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Host] = ((done_Host_car && done_Guest_switch)) ? 0 : ((!done_Host_car)) ? (-100) : 0;
        balanceOf[address_Guest] = ((done_Host_car && done_Guest_switch)) ? (((Guest_d != Host_car) == Guest_switch)) ? 20 : (-20) : ((!done_Host_car)) ? 20 : (-100);
    }

    function withdraw() public {
        int256 bal = balanceOf[msg.sender];
        require((bal > 0), "no funds");
        balanceOf[msg.sender] = 0;
        (bool ok, ) = payable(msg.sender).call{value: uint256(bal)}("");
        require(ok, "ETH send failed");
    }

    receive() public payable {
        revert("direct ETH not allowed");
    }
}