pragma solidity ^0.8.31;

contract TicTacToe {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, X, O }

    uint256 public lastTs;

    mapping(uint256 => bool) public actionDone;

    mapping(uint256 => uint256) public actionTimestamp;

    uint256 constant public ACTION_X_0 = 0;

    uint256 constant public ACTION_O_1 = 1;

    uint256 constant public ACTION_X_2 = 2;

    uint256 constant public ACTION_O_3 = 3;

    uint256 constant public ACTION_X_4 = 4;

    uint256 constant public ACTION_O_5 = 5;

    uint256 constant public ACTION_X_6 = 6;

    uint256 constant public ACTION_O_7 = 7;

    uint256 constant public ACTION_X_8 = 8;

    uint256 constant public ACTION_O_9 = 9;

    uint256 constant public FINAL_ACTION = 9;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_X;

    address public address_O;

    bool public payoffs_distributed;

    bool public done_X;

    bool public done_O;

    int256 public X_c1;

    bool public done_X_c1;

    int256 public O_c1;

    bool public done_O_c1;

    int256 public X_c2;

    bool public done_X_c2;

    int256 public O_c2;

    bool public done_O_c2;

    int256 public X_c3;

    bool public done_X_c3;

    int256 public O_c3;

    bool public done_O_c3;

    int256 public X_c4;

    bool public done_X_c4;

    int256 public O_c4;

    bool public done_O_c4;

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

    function move_X_0() public payable by(Role.None) notDone(0) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_X), "already joined");
        role[msg.sender] = Role.X;
        address_X = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_X = true;
        _markActionDone(0);
    }

    function move_O_1() public payable by(Role.None) notDone(1) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_O), "already joined");
        role[msg.sender] = Role.O;
        address_O = msg.sender;
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_O = true;
        _markActionDone(1);
    }

    function move_X_2(int256 _c1) public by(Role.X) notDone(2) {
        require((((_c1 == 0) || (_c1 == 1)) || (_c1 == 4)), "domain");
        X_c1 = _c1;
        done_X_c1 = true;
        _markActionDone(2);
    }

    function move_O_3(int256 _c1) public by(Role.O) notDone(3) depends(2) {
        require((((((_c1 == 1) || (_c1 == 3)) || (_c1 == 4)) || (_c1 == 5)) || (_c1 == 9)), "domain");
        require((X_c1 != _c1), "where");
        O_c1 = _c1;
        done_O_c1 = true;
        _markActionDone(3);
    }

    function move_X_4(int256 _c2) public by(Role.X) notDone(4) depends(2) depends(3) {
        require((((((((((_c2 == 0) || (_c2 == 1)) || (_c2 == 2)) || (_c2 == 3)) || (_c2 == 4)) || (_c2 == 5)) || (_c2 == 6)) || (_c2 == 7)) || (_c2 == 8)), "domain");
        require((((X_c1 != O_c1) && (X_c1 != _c2)) && (O_c1 != _c2)), "where");
        X_c2 = _c2;
        done_X_c2 = true;
        _markActionDone(4);
    }

    function move_O_5(int256 _c2) public by(Role.O) notDone(5) depends(2) depends(3) depends(4) {
        require((((((((((_c2 == 0) || (_c2 == 1)) || (_c2 == 2)) || (_c2 == 3)) || (_c2 == 4)) || (_c2 == 5)) || (_c2 == 6)) || (_c2 == 7)) || (_c2 == 8)), "domain");
        require(((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != _c2)) && (O_c1 != X_c2)) && (O_c1 != _c2)) && (X_c2 != _c2)), "where");
        O_c2 = _c2;
        done_O_c2 = true;
        _markActionDone(5);
    }

    function move_X_6(int256 _c3) public by(Role.X) notDone(6) depends(2) depends(3) depends(4) depends(5) {
        require((((((((((_c3 == 0) || (_c3 == 1)) || (_c3 == 2)) || (_c3 == 3)) || (_c3 == 4)) || (_c3 == 5)) || (_c3 == 6)) || (_c3 == 7)) || (_c3 == 8)), "domain");
        require(((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != _c3)) && (O_c2 != _c3)), "where");
        X_c3 = _c3;
        done_X_c3 = true;
        _markActionDone(6);
    }

    function move_O_7(int256 _c3) public by(Role.O) notDone(7) depends(2) depends(3) depends(4) depends(5) depends(6) {
        require((((((((((_c3 == 0) || (_c3 == 1)) || (_c3 == 2)) || (_c3 == 3)) || (_c3 == 4)) || (_c3 == 5)) || (_c3 == 6)) || (_c3 == 7)) || (_c3 == 8)), "domain");
        require((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != _c3)) && (O_c2 != X_c3)) && (O_c2 != _c3)) && (X_c3 != _c3)), "where");
        O_c3 = _c3;
        done_O_c3 = true;
        _markActionDone(7);
    }

    function move_X_8(int256 _c4) public by(Role.X) notDone(8) depends(2) depends(3) depends(4) depends(5) depends(6) depends(7) {
        require((((((((((_c4 == 0) || (_c4 == 1)) || (_c4 == 2)) || (_c4 == 3)) || (_c4 == 4)) || (_c4 == 5)) || (_c4 == 6)) || (_c4 == 7)) || (_c4 == 8)), "domain");
        require((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != _c4)) && (O_c3 != _c4)), "where");
        X_c4 = _c4;
        done_X_c4 = true;
        _markActionDone(8);
    }

    function move_O_9(int256 _c4) public by(Role.O) notDone(9) depends(2) depends(3) depends(4) depends(5) depends(6) depends(7) depends(8) {
        require((((((((((_c4 == 0) || (_c4 == 1)) || (_c4 == 2)) || (_c4 == 3)) || (_c4 == 4)) || (_c4 == 5)) || (_c4 == 6)) || (_c4 == 7)) || (_c4 == 8)), "domain");
        require(((((((((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != X_c4)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != X_c4)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != X_c4)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != X_c4)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != X_c4)) && (X_c3 != _c4)) && (O_c3 != X_c4)) && (O_c3 != _c4)) && (X_c4 != _c4)), "where");
        O_c4 = _c4;
        done_O_c4 = true;
        _markActionDone(9);
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_X] = 0;
        balanceOf[address_O] = 0;
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
