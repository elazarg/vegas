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

    uint256 constant public FINAL_ACTION = 4;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Gambler;

    address public address_Race;

    bool public payoffs_distributed;

    bool public done_Race;

    bool public done_Gambler;

    bytes32 public Gambler_hidden_bet;

    bool public done_Gambler_hidden_bet;

    int256 public Gambler_bet;

    bool public done_Gambler_bet;

    bytes32 public Race_hidden_winner;

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

    function move_Race_0() public payable by(Role.None) notDone(0) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_Race), "already joined");
        role[msg.sender] = Role.Race;
        address_Race = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Race = true;
        _markActionDone(0);
    }

    function move_Gambler_1(bytes32 _hidden_bet) public payable by(Role.None) notDone(1) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_Gambler), "already joined");
        role[msg.sender] = Role.Gambler;
        address_Gambler = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Gambler = true;
        Gambler_hidden_bet = _hidden_bet;
        done_Gambler_hidden_bet = true;
        _markActionDone(1);
    }

    function move_Race_3(bytes32 _hidden_winner) public by(Role.Race) notDone(3) {
        Race_hidden_winner = _hidden_winner;
        done_Race_hidden_winner = true;
        _markActionDone(3);
    }

    function move_Gambler_2(int256 _bet, uint256 salt) public by(Role.Gambler) notDone(2) depends(1) depends(3) {
        _checkReveal(Gambler_hidden_bet, abi.encodePacked(_bet, salt));
        require((((_bet == 1) || (_bet == 2)) || (_bet == 3)), "domain");
        Gambler_bet = _bet;
        done_Gambler_bet = true;
        _markActionDone(2);
    }

    function move_Race_4(int256 _winner, uint256 salt) public by(Role.Race) notDone(4) depends(3) depends(1) {
        _checkReveal(Race_hidden_winner, abi.encodePacked(_winner, salt));
        require((((_winner == 1) || (_winner == 2)) || (_winner == 3)), "domain");
        Race_winner = _winner;
        done_Race_winner = true;
        _markActionDone(4);
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
