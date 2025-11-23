pragma solidity ^0.8.31;

contract OddsEvensShort {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Odd, Even }

    uint256 public lastTs;

    mapping(uint256 => bool) public actionDone;

    mapping(uint256 => uint256) public actionTimestamp;

    uint256 constant public ACTION_Even_0 = 0;

    uint256 constant public ACTION_Odd_0 = 1;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Odd;

    address public address_Even;

    bool public payoffs_distributed;

    bool public done_Odd;

    uint256 public Odd_hidden_c;

    bool public done_Odd_hidden_c;

    bool public Odd_c;

    bool public done_Odd_c;

    bool public done_Even;

    uint256 public Even_hidden_c;

    bool public done_Even_hidden_c;

    bool public Even_c;

    bool public done_Even_c;

    bool public done_Odd;

    bool public done_Even;

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
        require(actionDone[1], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function move_Odd_0(uint256 _hidden_c) public payable by(Role.None) notDone(1) {
        require((!done_Odd), "already joined");
        role[msg.sender] = Role.Odd;
        address_Odd = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Odd = true;
        Odd_hidden_c = _hidden_c;
        done_Odd_hidden_c = true;
        actionDone[1] = true;
        actionTimestamp[1] = block.timestamp;
    }

    function move_Even_0(uint256 _hidden_c) public payable by(Role.None) notDone(0) {
        require((!done_Even), "already joined");
        role[msg.sender] = Role.Even;
        address_Even = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Even = true;
        Even_hidden_c = _hidden_c;
        done_Even_hidden_c = true;
        actionDone[0] = true;
        actionTimestamp[0] = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Odd] = ((done_Even_c && done_Odd_c)) ? ((Even_c == Odd_c)) ? (-10) : 10 : (((!done_Even_c) && done_Odd_c)) ? 10 : (-100);
        balanceOf[address_Even] = ((done_Even_c && done_Odd_c)) ? ((Even_c == Odd_c)) ? 10 : (-10) : (((!done_Even_c) && done_Odd_c)) ? (-100) : (-100);
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
