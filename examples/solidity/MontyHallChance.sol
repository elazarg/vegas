pragma solidity ^0.8.31;

contract MontyHallChance {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Guest, Host }

    uint256 constant public PHASE_TIME = uint256(500);

    uint256 public phase;

    uint256 public lastTs;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Guest;

    address public address_Host;

    bool public payoffs_distributed;

    bool public done_Host;

    bool public done_Phase0_Host;

    bool public done_Guest;

    bool public done_Phase1_Guest;

    uint256 public Host_hidden_car;

    bool public done_Host_hidden_car;

    int256 public Host_car;

    bool public done_Host_car;

    bool public done_Phase2_Host;

    int256 public Guest_d;

    bool public done_Guest_d;

    bool public done_Phase3_Guest;

    int256 public Host_goat;

    bool public done_Host_goat;

    bool public done_Phase4_Host;

    bool public Guest_switch;

    bool public done_Guest_switch;

    bool public done_Phase5_Guest;

    bool public done_Phase6_Host;

    modifier at_phase(uint256 _phase) {
        require((phase == _phase), "wrong phase");
    }

    modifier by(Role r) {
        require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
        require((phase == 7), "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function keccak(bool x, uint256 salt) public pure returns (bytes32 out) {
        return keccak256(abi.encodePacked(x, salt));
    }

    function join_Host() public payable by(Role.None) at_phase(0) {
        require((!done_Host), "already joined");
        role[msg.sender] = Role.Host;
        address_Host = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Host = true;
        done_Phase0_Host = true;
    }

    function __nextPhase_Phase0() public {
        require((phase == 0), "wrong phase");
        require(done_Phase0_Host, "Host not done");
        emit Broadcast_Phase0();
        phase = 1;
        lastTs = block.timestamp;
    }

    function join_Guest() public payable by(Role.None) at_phase(1) {
        require((!done_Guest), "already joined");
        role[msg.sender] = Role.Guest;
        address_Guest = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Guest = true;
        done_Phase1_Guest = true;
    }

    function __nextPhase_Phase1() public {
        require((phase == 1), "wrong phase");
        require(done_Phase1_Guest, "Guest not done");
        emit Broadcast_Phase1();
        phase = 2;
        lastTs = block.timestamp;
    }

    function yield_Phase2_Host(uint256 _hidden_car) public by(Role.Host) at_phase(2) {
        require((!done_Phase2_Host), "done");
        Host_hidden_car = _hidden_car;
        done_Host_hidden_car = true;
        done_Phase2_Host = true;
    }

    function __nextPhase_Phase2() public {
        require((phase == 2), "wrong phase");
        require(done_Phase2_Host, "Host not done");
        emit Broadcast_Phase2();
        phase = 3;
        lastTs = block.timestamp;
    }

    function yield_Phase3_Guest(int256 _d) public by(Role.Guest) at_phase(3) {
        require((!done_Phase3_Guest), "done");
        require((((_d == 0) || (_d == 1)) || (_d == 2)), "domain");
        Guest_d = _d;
        done_Guest_d = true;
        done_Phase3_Guest = true;
    }

    function __nextPhase_Phase3() public {
        require((phase == 3), "wrong phase");
        require(done_Phase3_Guest, "Guest not done");
        emit Broadcast_Phase3();
        phase = 4;
        lastTs = block.timestamp;
    }

    function yield_Phase4_Host(int256 _goat) public by(Role.Host) at_phase(4) {
        require((!done_Phase4_Host), "done");
        require((((_goat == 0) || (_goat == 1)) || (_goat == 2)), "domain");
        require(((_goat != Guest_d) && (_goat != Host_hidden_car)), "where");
        Host_goat = _goat;
        done_Host_goat = true;
        done_Phase4_Host = true;
    }

    function __nextPhase_Phase4() public {
        require((phase == 4), "wrong phase");
        require(done_Phase4_Host, "Host not done");
        emit Broadcast_Phase4();
        phase = 5;
        lastTs = block.timestamp;
    }

    function yield_Phase5_Guest(bool _switch) public by(Role.Guest) at_phase(5) {
        require((!done_Phase5_Guest), "done");
        Guest_switch = _switch;
        done_Guest_switch = true;
        done_Phase5_Guest = true;
    }

    function __nextPhase_Phase5() public {
        require((phase == 5), "wrong phase");
        require(done_Phase5_Guest, "Guest not done");
        emit Broadcast_Phase5();
        phase = 6;
        lastTs = block.timestamp;
    }

    function reveal_Phase6_Host(int256 _car, uint256 salt) public by(Role.Host) at_phase(6) {
        require((!done_Phase6_Host), "done");
        require((keccak256(abi.encodePacked(_car, salt)) == bytes32(Host_hidden_car)), "bad reveal");
        require((((_car == 0) || (_car == 1)) || (_car == 2)), "domain");
        Host_car = _car;
        done_Host_car = true;
        done_Phase6_Host = true;
    }

    function __nextPhase_Phase6() public {
        require((phase == 6), "wrong phase");
        require(done_Phase6_Host, "Host not done");
        emit Broadcast_Phase6();
        phase = 7;
        lastTs = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Guest] = (((done_Host_car && done_Host_goat) && done_Guest_switch)) ? (((Guest_d != Host_car) == Guest_switch)) ? 20 : (-20) : (((!done_Host_car) || (!done_Host_goat))) ? 20 : (-100);
        balanceOf[address_Host] = (((done_Host_car && done_Host_goat) && done_Guest_switch)) ? 0 : (((!done_Host_car) || (!done_Host_goat))) ? (-100) : 0;
    }

    function withdraw() public {
        int256 bal = balanceOf[msg.sender];
        require((bal > 0), "no funds");
        balanceOf[msg.sender] = 0;
        (bool ok, ) = payable(msg.sender).call{value: uint256(bal)}("");
        require(ok, "ETH send failed");
    }

    event Broadcast_Phase0();

    event Broadcast_Phase1();

    event Broadcast_Phase2();

    event Broadcast_Phase3();

    event Broadcast_Phase4();

    event Broadcast_Phase5();

    event Broadcast_Phase6();

    receive() public payable {
        revert("direct ETH not allowed");
    }
}