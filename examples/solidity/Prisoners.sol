pragma solidity ^0.8.31;

contract Prisoners {
    enum Role { None, A, B }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(uint256 => uint256) public actionTimestamp;
    uint256 constant public ACTION_A_0 = 0;
    uint256 constant public ACTION_B_1 = 1;
    uint256 constant public ACTION_A_3 = 2;
    uint256 constant public ACTION_A_4 = 3;
    uint256 constant public ACTION_B_5 = 4;
    uint256 constant public ACTION_B_6 = 5;
    uint256 constant public FINAL_ACTION = 5;
    mapping(address => Role) public roles;
    mapping(address => int256) public balanceOf;
    address public address_A;
    address public address_B;
    bool public done_A;
    bool public done_B;
    bool public payoffs_distributed;
    bool public A_c;
    bool public done_A_c;
    bytes32 public A_c_hidden;
    bool public done_A_c_hidden;
    bool public B_c;
    bool public done_B_c;
    bytes32 public B_c_hidden;
    bool public done_B_c_hidden;
    
    receive() public payable {
        revert("direct ETH not allowed");
    }
    
    uint256 constant public TIMEOUT = 86400;
    
    mapping(Role => bool) private bailed;
    
    function _check_timestamp(Role role) private {
        if (role == Role.None) {
            return;
        }
        if (block.timestamp > lastTs + TIMEOUT) {
            bailed[role] = true;
            lastTs = block.timestamp;
        }
    }
    
    modifier depends(Role role, uint256 actionId) {
        _check_timestamp(role);
        if (!bailed[role]) {
            require(actionDone[role][actionId], "dependency not satisfied");
        }
        _;
    }
    
    modifier action(Role role, uint256 actionId) {
        require((!actionDone[role][actionId]), "already done");
        _;
        actionDone[role][actionId] = true;
        actionTimestamp[role][actionId] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    modifier by(Role role) {
        require((roles[msg.sender] == role), "bad role");
        _check_timestamp(role);
        require(!bailed[role], "you bailed");
        _;
    }
    
    modifier at_final_phase() {
        require(actionDone[FINAL_ACTION], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
        _;
    }
    
    function _checkReveal(bytes32 commitment, bytes memory preimage) internal pure {
        require((keccak256(preimage) == commitment), "bad reveal");
    }
    
    constructor() {
        lastTs = block.timestamp;
    }
    
    function move_A_0() public payable by(Role.None) action(Role.A, 0) {
        require((!done_A), "already joined");
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        roles[msg.sender] = Role.A;
        address_A = msg.sender;
        done_A = true;
    }
    
    function move_B_1() public payable by(Role.None) action(Role.B, 1) depends(Role.A, 0) {
        require((!done_B), "already joined");
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        roles[msg.sender] = Role.B;
        address_B = msg.sender;
        done_B = true;
    }
    
    function move_A_2(bytes32 _hidden_c) public by(Role.A) action(Role.A, 3) depends(Role.B, 1) {
        A_c_hidden = _hidden_c;
        done_A_c_hidden = true;
    }
    
    function move_B_4(bytes32 _hidden_c) public by(Role.B) action(Role.B, 5) depends(Role.B, 1) {
        B_c_hidden = _hidden_c;
        done_B_c_hidden = true;
    }
    
    function move_A_3(bool _c, uint256 _salt) public by(Role.A) action(Role.A, 4) depends(Role.B, 1) depends(Role.A, 3) depends(Role.B, 5) {
        require((keccak256(abi.encodePacked(_c, _salt)) == A_c_hidden), "reveal failed for c");
        A_c = _c;
        done_A_c = true;
    }
    
    function move_B_5(bool _c, uint256 _salt) public by(Role.B) action(Role.B, 6) depends(Role.B, 1) depends(Role.A, 3) depends(Role.B, 5) {
        require((keccak256(abi.encodePacked(_c, _salt)) == B_c_hidden), "reveal failed for c");
        B_c = _c;
        done_B_c = true;
    }
    
    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_A] = ((done_A_c && done_B_c) ? ((A_c && B_c) ? (-2) : ((A_c && (!B_c)) ? 0 : (((!A_c) && B_c) ? (-3) : (-1)))) : ((!done_A_c) ? (-100) : 10));
        balanceOf[address_B] = ((done_A_c && done_B_c) ? ((A_c && B_c) ? (-2) : ((A_c && (!B_c)) ? (-3) : (((!A_c) && B_c) ? 0 : (-1)))) : ((!done_A_c) ? 10 : (-100)));
    }
    
    function withdraw() public {
        int256 bal = balanceOf[msg.sender];
        require((bal > 0), "no funds");
        balanceOf[msg.sender] = 0;
        (bool ok, ) = payable(msg.sender).call{value: uint256(bal)}("");
        require(ok, "ETH send failed");
    }
}
