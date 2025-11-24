pragma solidity ^0.8.31;

contract OddsEvens {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Odd, Even }

    uint256 public lastTs;

    mapping(uint256 => bool) public actionDone;

    mapping(uint256 => uint256) public actionTimestamp;

    uint256 constant public ACTION_Even_0 = 0;

    uint256 constant public ACTION_Odd_1 = 1;

    uint256 constant public ACTION_Odd_2 = 2;

    uint256 constant public ACTION_Odd_3 = 3;

    uint256 constant public ACTION_Even_4 = 4;

    uint256 constant public ACTION_Even_5 = 5;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Odd;

    address public address_Even;

    bool public payoffs_distributed;

    bool public done_Odd;

    bool public done_Even;

    uint256 public Odd_hidden_c;

    bool public done_Odd_hidden_c;

    bool public Odd_c;

    bool public done_Odd_c;

    uint256 public Even_hidden_c;

    bool public done_Even_hidden_c;

    bool public Even_c;

    bool public done_Even_c;

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
        require(actionDone[5], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function move_Odd_1() public payable by(Role.None) notDone(1) {
        require((!done_Odd), "already joined");
        role[msg.sender] = Role.Odd;
        address_Odd = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Odd = true;
        actionDone[1] = true;
        actionTimestamp[1] = block.timestamp;
    }

    function move_Even_0() public payable by(Role.None) notDone(0) {
        require((!done_Even), "already joined");
        role[msg.sender] = Role.Even;
        address_Even = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Even = true;
        actionDone[0] = true;
        actionTimestamp[0] = block.timestamp;
    }

    function move_Odd_2(uint256 _hidden_c) public by(Role.Odd) notDone(2) {
        Odd_hidden_c = _hidden_c;
        done_Odd_hidden_c = true;
        actionDone[2] = true;
        actionTimestamp[2] = block.timestamp;
    }

    function move_Even_4(uint256 _hidden_c) public by(Role.Even) notDone(4) {
        Even_hidden_c = _hidden_c;
        done_Even_hidden_c = true;
        actionDone[4] = true;
        actionTimestamp[4] = block.timestamp;
    }

    function move_Odd_3(bool _c, uint256 salt) public by(Role.Odd) notDone(3) depends(2) depends(4) {
        require((keccak256(abi.encodePacked(_c, salt)) == bytes32(Odd_hidden_c)), "bad reveal");
        Odd_c = _c;
        done_Odd_c = true;
        actionDone[3] = true;
        actionTimestamp[3] = block.timestamp;
    }

    function move_Even_5(bool _c, uint256 salt) public by(Role.Even) notDone(5) depends(4) depends(2) {
        require((keccak256(abi.encodePacked(_c, salt)) == bytes32(Even_hidden_c)), "bad reveal");
        Even_c = _c;
        done_Even_c = true;
        actionDone[5] = true;
        actionTimestamp[5] = block.timestamp;
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
