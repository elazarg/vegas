pragma solidity ^0.8.31;

contract Prisoners {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, A, B }

    uint256 public lastTs;

    mapping(uint256 => bool) public actionDone;

    mapping(uint256 => uint256) public actionTimestamp;

    uint256 constant public ACTION_A_0 = 0;

    uint256 constant public ACTION_B_1 = 1;

    uint256 constant public ACTION_A_2 = 2;

    uint256 constant public ACTION_B_2 = 3;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_A;

    address public address_B;

    bool public payoffs_distributed;

    bool public done_A;

    bool public done_B;

    uint256 public A_hidden_c;

    bool public done_A_hidden_c;

    bool public A_c;

    bool public done_A_c;

    uint256 public B_hidden_c;

    bool public done_B_hidden_c;

    bool public B_c;

    bool public done_B_c;

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
        require(actionDone[3], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function move_A_0() public payable by(Role.None) notDone(0) {
        require((!done_A), "already joined");
        role[msg.sender] = Role.A;
        address_A = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_A = true;
        actionDone[0] = true;
        actionTimestamp[0] = block.timestamp;
    }

    function move_B_1() public payable by(Role.None) notDone(1) {
        require((!done_B), "already joined");
        role[msg.sender] = Role.B;
        address_B = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_B = true;
        actionDone[1] = true;
        actionTimestamp[1] = block.timestamp;
    }

    function move_A_2(uint256 _hidden_c) public by(Role.A) notDone(2) {
        A_hidden_c = _hidden_c;
        done_A_hidden_c = true;
        actionDone[2] = true;
        actionTimestamp[2] = block.timestamp;
    }

    function move_B_2(uint256 _hidden_c) public by(Role.B) notDone(3) {
        B_hidden_c = _hidden_c;
        done_B_hidden_c = true;
        actionDone[3] = true;
        actionTimestamp[3] = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_A] = ((done_A_c && done_B_c)) ? ((A_c && B_c)) ? (-2) : ((A_c && (!B_c))) ? 0 : (((!A_c) && B_c)) ? (-3) : (-1) : ((!done_A_c)) ? (-100) : 10;
        balanceOf[address_B] = ((done_A_c && done_B_c)) ? ((A_c && B_c)) ? (-2) : ((A_c && (!B_c))) ? (-3) : (((!A_c) && B_c)) ? 0 : (-1) : ((!done_A_c)) ? 10 : (-100);
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