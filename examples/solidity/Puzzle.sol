pragma solidity ^0.8.31;

contract Puzzle {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Q, A }

    uint256 public lastTs;

    mapping(uint256 => bool) public actionDone;

    mapping(uint256 => uint256) public actionTimestamp;

    uint256 constant public ACTION_Q_0 = 0;

    uint256 constant public ACTION_A_1 = 1;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Q;

    address public address_A;

    bool public payoffs_distributed;

    bool public done_Q;

    bool public done_A;

    int256 public Q_x;

    bool public done_Q_x;

    int256 public A_p;

    bool public done_A_p;

    int256 public A_q;

    bool public done_A_q;

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

    function move_Q_0(int256 _x) public payable by(Role.None) notDone(0) {
        require((!done_Q), "already joined");
        role[msg.sender] = Role.Q;
        address_Q = msg.sender;
        require((msg.value == 50), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Q = true;
        Q_x = _x;
        done_Q_x = true;
        actionDone[0] = true;
        actionTimestamp[0] = block.timestamp;
    }

    function move_A_1(int256 _p, int256 _q) public by(Role.None) notDone(1) depends(0) {
        require((!done_A), "already joined");
        role[msg.sender] = Role.A;
        address_A = msg.sender;
        done_A = true;
        require(((((_p * _q) == Q_x) && (_p != 1)) && (_q != 1)), "where");
        A_p = _p;
        done_A_p = true;
        A_q = _q;
        done_A_q = true;
        actionDone[1] = true;
        actionTimestamp[1] = block.timestamp;
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Q] = 0;
        balanceOf[address_A] = 50;
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
