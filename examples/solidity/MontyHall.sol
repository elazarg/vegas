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

    uint256 constant public ACTION_Host_3 = 3;

    uint256 constant public ACTION_Guest_4 = 4;

    uint256 constant public ACTION_Guest_5 = 5;

    uint256 constant public ACTION_Host_6 = 6;

    uint256 constant public ACTION_Host_7 = 7;

    uint256 constant public ACTION_Guest_8 = 8;

    uint256 constant public ACTION_Guest_9 = 9;

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

    uint256 public Guest_hidden_d;

    bool public done_Guest_hidden_d;

    int256 public Guest_d;

    bool public done_Guest_d;

    uint256 public Host_hidden_goat;

    bool public done_Host_hidden_goat;

    int256 public Host_goat;

    bool public done_Host_goat;

    uint256 public Guest_hidden_switch;

    bool public done_Guest_hidden_switch;

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
        require(actionDone[9], "game not over");
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

    function move_Guest_4(uint256 _hidden_d) public by(Role.Guest) notDone(4) {
        Guest_hidden_d = _hidden_d;
        done_Guest_hidden_d = true;
        actionDone[4] = true;
        actionTimestamp[4] = block.timestamp;
    }

    function move_Guest_8(uint256 _hidden_switch) public by(Role.Guest) notDone(8) {
        Guest_hidden_switch = _hidden_switch;
        done_Guest_hidden_switch = true;
        actionDone[8] = true;
        actionTimestamp[8] = block.timestamp;
    }

    function move_Guest_5(int256 _d, uint256 salt) public by(Role.Guest) notDone(5) depends(4) depends(8) {
        require((keccak256(abi.encodePacked(_d, salt)) == bytes32(Guest_hidden_d)), "bad reveal");
        require((((_d == 0) || (_d == 1)) || (_d == 2)), "domain");
        Guest_d = _d;
        done_Guest_d = true;
        actionDone[5] = true;
        actionTimestamp[5] = block.timestamp;
    }

    function move_Host_6(uint256 _hidden_goat) public by(Role.Host) notDone(6) depends(5) {
        Host_hidden_goat = _hidden_goat;
        done_Host_hidden_goat = true;
        actionDone[6] = true;
        actionTimestamp[6] = block.timestamp;
    }

    function move_Host_7(int256 _goat, uint256 salt) public by(Role.Host) notDone(7) depends(5) depends(6) depends(8) {
        require((keccak256(abi.encodePacked(_goat, salt)) == bytes32(Host_hidden_goat)), "bad reveal");
        require((((_goat == 0) || (_goat == 1)) || (_goat == 2)), "domain");
        require((_goat != Guest_d), "where");
        Host_goat = _goat;
        done_Host_goat = true;
        actionDone[7] = true;
        actionTimestamp[7] = block.timestamp;
    }

    function move_Guest_9(bool _switch, uint256 salt) public by(Role.Guest) notDone(9) depends(8) depends(4) depends(6) {
        require((keccak256(abi.encodePacked(_switch, salt)) == bytes32(Guest_hidden_switch)), "bad reveal");
        Guest_switch = _switch;
        done_Guest_switch = true;
        actionDone[9] = true;
        actionTimestamp[9] = block.timestamp;
    }

    function move_Host_3(int256 _car, uint256 salt) public by(Role.Host) notDone(3) depends(7) depends(2) {
        require((keccak256(abi.encodePacked(_car, salt)) == bytes32(Host_hidden_car)), "bad reveal");
        require((((_car == 0) || (_car == 1)) || (_car == 2)), "domain");
        require((Host_goat != _car), "where");
        Host_car = _car;
        done_Host_car = true;
        actionDone[3] = true;
        actionTimestamp[3] = block.timestamp;
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
