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

    uint256 constant public FINAL_ACTION = 9;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Host;

    address public address_Guest;

    bool public payoffs_distributed;

    bool public done_Host;

    bool public done_Guest;

    bytes32 public Host_hidden_car;

    bool public done_Host_hidden_car;

    int256 public Host_car;

    bool public done_Host_car;

    bytes32 public Guest_hidden_d;

    bool public done_Guest_hidden_d;

    int256 public Guest_d;

    bool public done_Guest_d;

    bytes32 public Host_hidden_goat;

    bool public done_Host_hidden_goat;

    int256 public Host_goat;

    bool public done_Host_goat;

    bytes32 public Guest_hidden_switch;

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
        require(actionDone[FINAL_ACTION], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function _checkReveal(bytes32 commitment, bytes preimage) internal pure {
        require((keccak256(preimage) == commitment), "bad reveal");
    }

    function _markActionDone(uint256 actionId) internal {
        actionDone[actionId] = true;
        actionTimestamp[actionId] = block.timestamp;
        lastTs = block.timestamp;
    }

    function move_Host_0() public payable by(Role.None) notDone(0) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_Host), "already joined");
        role[msg.sender] = Role.Host;
        address_Host = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Host = true;
        _markActionDone(0);
    }

    function move_Guest_1() public payable by(Role.None) notDone(1) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_Guest), "already joined");
        role[msg.sender] = Role.Guest;
        address_Guest = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Guest = true;
        _markActionDone(1);
    }

    function move_Host_2(bytes32 _hidden_car) public by(Role.Host) notDone(2) {
        Host_hidden_car = _hidden_car;
        done_Host_hidden_car = true;
        _markActionDone(2);
    }

    function move_Guest_4(bytes32 _hidden_d) public by(Role.Guest) notDone(4) {
        Guest_hidden_d = _hidden_d;
        done_Guest_hidden_d = true;
        _markActionDone(4);
    }

    function move_Guest_8(bytes32 _hidden_switch) public by(Role.Guest) notDone(8) {
        Guest_hidden_switch = _hidden_switch;
        done_Guest_hidden_switch = true;
        _markActionDone(8);
    }

    function move_Guest_5(int256 _d, uint256 salt) public by(Role.Guest) notDone(5) depends(4) depends(8) {
        _checkReveal(Guest_hidden_d, abi.encodePacked(_d, salt));
        require((((_d == 0) || (_d == 1)) || (_d == 2)), "domain");
        Guest_d = _d;
        done_Guest_d = true;
        _markActionDone(5);
    }

    function move_Host_6(bytes32 _hidden_goat) public by(Role.Host) notDone(6) depends(5) {
        Host_hidden_goat = _hidden_goat;
        done_Host_hidden_goat = true;
        _markActionDone(6);
    }

    function move_Host_7(int256 _goat, uint256 salt) public by(Role.Host) notDone(7) depends(5) depends(6) depends(8) {
        _checkReveal(Host_hidden_goat, abi.encodePacked(_goat, salt));
        require((((_goat == 0) || (_goat == 1)) || (_goat == 2)), "domain");
        require((_goat != Guest_d), "where");
        Host_goat = _goat;
        done_Host_goat = true;
        _markActionDone(7);
    }

    function move_Guest_9(bool _switch, uint256 salt) public by(Role.Guest) notDone(9) depends(8) depends(4) depends(6) {
        _checkReveal(Guest_hidden_switch, abi.encodePacked(_switch, salt));
        Guest_switch = _switch;
        done_Guest_switch = true;
        _markActionDone(9);
    }

    function move_Host_3(int256 _car, uint256 salt) public by(Role.Host) notDone(3) depends(7) depends(2) {
        _checkReveal(Host_hidden_car, abi.encodePacked(_car, salt));
        require((((_car == 0) || (_car == 1)) || (_car == 2)), "domain");
        require((Host_goat != _car), "where");
        Host_car = _car;
        done_Host_car = true;
        _markActionDone(3);
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
