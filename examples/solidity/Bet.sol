pragma solidity ^0.8.31;

contract Bet {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Gambler, Race }

    uint256 public lastTs;

    mapping(uint256 => bool) public actionDone;

    mapping(uint256 => uint256) public actionTimestamp;

    uint256 constant public ACTION_Race_0 = 0;

    uint256 constant public ACTION_Gambler_1 = 1;

    uint256 constant public ACTION_Gambler_2 = 2;

    uint256 constant public ACTION_Race_3 = 3;

    uint256 constant public ACTION_Race_4 = 4;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Gambler;

    address public address_Race;

    bool public payoffs_distributed;

    bool public done_Race;

    bool public done_Gambler;

    uint256 public Gambler_hidden_bet;

    bool public done_Gambler_hidden_bet;

    int256 public Gambler_bet;

    bool public done_Gambler_bet;

    uint256 public Race_hidden_winner;

    bool public done_Race_hidden_winner;

    int256 public Race_winner;

    bool public done_Race_winner;

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
        require(actionDone[4], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function move_Race_0() public payable by(Role.None) notDone(0) {
        require((!done_Race), "already joined");
        role[msg.sender] = Role.Race;
        address_Race = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Race = true;
        actionDone[0] = true;
        actionTimestamp[0] = block.timestamp;
    }

    function move_Gambler_1(uint256 _hidden_bet) public payable by(Role.None) notDone(1) {
        require((!done_Gambler), "already joined");
        role[msg.sender] = Role.Gambler;
        address_Gambler = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Gambler = true;
        Gambler_hidden_bet = _hidden_bet;
        done_Gambler_hidden_bet = true;
        actionDone[1] = true;
        actionTimestamp[1] = block.timestamp;
    }

    function move_Race_3(uint256 _hidden_winner) public by(Role.Race) notDone(3) {
        Race_hidden_winner = _hidden_winner;
        done_Race_hidden_winner = true;
        actionDone[3] = true;
        actionTimestamp[3] = block.timestamp;
    }

    function move_Gambler_2(int256 _bet, uint256 salt) public by(Role.Gambler) notDone(2) depends(1) depends(3) {
        require((keccak256(abi.encodePacked(_bet, salt)) == bytes32(Gambler_hidden_bet)), "bad reveal");
        require((((_bet == 1) || (_bet == 2)) || (_bet == 3)), "domain");
        Gambler_bet = _bet;
        done_Gambler_bet = true;
        actionDone[2] = true;
        actionTimestamp[2] = block.timestamp;
    }

    function move_Race_4(int256 _winner, uint256 salt) public by(Role.Race) notDone(4) depends(3) depends(1) {
        require((keccak256(abi.encodePacked(_winner, salt)) == bytes32(Race_hidden_winner)), "bad reveal");
        require((((_winner == 1) || (_winner == 2)) || (_winner == 3)), "domain");
        Race_winner = _winner;
        done_Race_winner = true;
        actionDone[4] = true;
        actionTimestamp[4] = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Gambler] = (((!done_Race_winner) || (Race_winner == Gambler_bet))) ? 100 : 0;
        balanceOf[address_Race] = (((!done_Race_winner) || (Race_winner == Gambler_bet))) ? 0 : 100;
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
