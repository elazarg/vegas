pragma solidity ^0.8.31;

contract Simple {
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

    uint256 constant public ACTION_B_3 = 3;

    uint256 constant public ACTION_A_4 = 4;

    uint256 constant public FINAL_ACTION = 4;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_A;

    address public address_B;

    bool public payoffs_distributed;

    bool public done_A;

    bool public done_B;

    bytes32 public A_hidden_c;

    bool public done_A_hidden_c;

    bool public A_c;

    bool public done_A_c;

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

    function move_A_0() public payable by(Role.None) notDone(0) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_A), "already joined");
        role[msg.sender] = Role.A;
        address_A = msg.sender;
        require((msg.value == 1), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_A = true;
        _markActionDone(0);
    }

    function move_B_1() public payable by(Role.None) notDone(1) depends(0) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_B), "already joined");
        role[msg.sender] = Role.B;
        address_B = msg.sender;
        require((msg.value == 1), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_B = true;
        _markActionDone(1);
    }

    function move_A_2(bytes32 _hidden_c) public by(Role.A) notDone(2) depends(1) {
        A_hidden_c = _hidden_c;
        done_A_hidden_c = true;
        _markActionDone(2);
    }

    function move_B_3(bool _c) public by(Role.B) notDone(3) depends(2) {
        B_c = _c;
        done_B_c = true;
        _markActionDone(3);
    }

    function move_A_4(bool _c, uint256 salt) public by(Role.A) notDone(4) depends(3) depends(2) {
        _checkReveal(A_hidden_c, abi.encodePacked(_c, salt));
        A_c = _c;
        done_A_c = true;
        _markActionDone(4);
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_A] = (((A_c != B_c) || (!done_B_c))) ? 1 : (-1);
        balanceOf[address_B] = (((A_c == B_c) || (!done_A_c))) ? 1 : (-1);
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
