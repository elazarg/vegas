pragma solidity ^0.8.31;

contract Simple {
    enum Role { None, A, B }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 constant public ACTION_A_0 = 0;
    uint256 constant public ACTION_B_1 = 1;
    uint256 constant public ACTION_A_2 = 2;
    uint256 constant public ACTION_B_3 = 3;
    uint256 constant public ACTION_A_4 = 4;
    mapping(address => Role) public roles;
    address public address_A;
    address public address_B;
    bool public done_A;
    bool public done_B;
    bool public claimed_A;
    bool public claimed_B;
    bool public A_c;
    bool public done_A_c;
    bytes32 public A_c_hidden;
    bool public done_A_c_hidden;
    bool public B_c;
    bool public done_B_c;
    
    receive() external payable {
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
    
    function _checkReveal(bytes32 commitment, bytes memory preimage) internal pure {
        require((keccak256(preimage) == commitment), "bad reveal");
    }
    
    constructor() {
        lastTs = block.timestamp;
    }
    
    function move_A_0() public payable by(Role.None) action(Role.A, 0) {
        require((!done_A), "already joined");
        require((msg.value == 1), "bad stake");
        roles[msg.sender] = Role.A;
        address_A = msg.sender;
        done_A = true;
    }
    
    function move_B_1() public payable by(Role.None) action(Role.B, 1) depends(Role.A, 0) {
        require((!done_B), "already joined");
        require((msg.value == 1), "bad stake");
        roles[msg.sender] = Role.B;
        address_B = msg.sender;
        done_B = true;
    }
    
    function move_A_2(bytes32 _hidden_c) public by(Role.A) action(Role.A, 2) depends(Role.B, 1) {
        A_c_hidden = _hidden_c;
        done_A_c_hidden = true;
    }
    
    function move_B_3(bool _c) public by(Role.B) action(Role.B, 3) depends(Role.A, 2) {
        B_c = _c;
        done_B_c = true;
    }
    
    function move_A_4(bool _c, uint256 _salt) public by(Role.A) action(Role.A, 4) depends(Role.A, 2) depends(Role.B, 3) {
        require((keccak256(abi.encodePacked(_c, _salt)) == A_c_hidden), "reveal failed for c");
        A_c = _c;
        done_A_c = true;
    }
    
    function withdraw_A() public by(Role.A) action(Role.A, 5) depends(Role.A, 4) {
        require((!claimed_A), "already claimed");
        claimed_A = true;
        int256 payout = (((A_c != B_c) || (!done_B_c)) ? 1 : (-1));
        if (payout > 0) {
            (bool ok, ) = payable(address_A).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B() public by(Role.B) action(Role.B, 6) depends(Role.A, 4) {
        require((!claimed_B), "already claimed");
        claimed_B = true;
        int256 payout = (((A_c == B_c) || (!done_A_c)) ? 1 : (-1));
        if (payout > 0) {
            (bool ok, ) = payable(address_B).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
