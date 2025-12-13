pragma solidity ^0.8.31;

contract Prisoners {
    enum Role { None, A, B }
    
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 public lastTs;
    uint256 constant public TIMEOUT = 86400;
    mapping(Role => bool) public bailed;
    uint256 constant public ACTION_A_0 = 0;
    uint256 constant public ACTION_B_1 = 1;
    uint256 constant public ACTION_A_3 = 2;
    uint256 constant public ACTION_A_4 = 3;
    uint256 constant public ACTION_B_5 = 4;
    uint256 constant public ACTION_B_6 = 5;
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
    bytes32 public B_c_hidden;
    bool public done_B_c_hidden;
    
    receive() external payable {
        revert("direct ETH not allowed");
    }
    
    constructor() {
        lastTs = block.timestamp;
    }
    
    function _check_timestamp(Role _role) internal {
        if ((_role == Role.None))
         {
            return;
        }
        if ((block.timestamp > (lastTs + _TIMEOUT)))
         {
            bailed[_role] = true;
            lastTs = block.timestamp;
        }
    }
    

    modifier by(Role role) {
        require((roles[msg.sender] == _role), "bad role");
        _check_timestamp(_role);
        require((!bailed[_role]), "you bailed");
        _;
    }

    modifier action(Role role, uint256 actionId) {
        require((!actionDone[_role][_actionId]), "already done");
        actionDone[_role][_actionId] = true;
        _;
        actionTimestamp[_role][_actionId] = block.timestamp;
        lastTs = block.timestamp;
    }

    modifier depends(Role role, uint256 actionId) {
        _check_timestamp(_role);
        if ((!bailed[_role]))
         {
            require(actionDone[_role][_actionId], "dependency not satisfied");
        }
        _;
    }
    

    function move_A_0() public payable by(Role.A) action(Role.A, 0) {
        require((!done_A), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.A;
        address_A = msg.sender;
        done_A = true;
    }
    
    function move_B_1() public payable by(Role.B) action(Role.B, 1) depends(Role.A, 0) {
        require((!done_B), "already joined");
        require((msg.value == 100), "bad stake");
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
    
    function withdraw_A() public {
        require((!claimed_A), "already claimed");
        claimed_A = true;
        int256 payout = ((done_A_c && done_B_c) ? ((A_c && B_c) ? 100 : ((A_c && (!B_c)) ? 0 : (((!A_c) && B_c) ? 200 : 90))) : ((!done_A_c) ? 0 : 200));
        if (payout > 0) {
            (bool ok, ) = payable(address_A).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B() public {
        require((!claimed_B), "already claimed");
        claimed_B = true;
        int256 payout = ((done_A_c && done_B_c) ? ((A_c && B_c) ? 100 : ((A_c && (!B_c)) ? 200 : (((!A_c) && B_c) ? 0 : 110))) : ((!done_A_c) ? 200 : 0));
        if (payout > 0) {
            (bool ok, ) = payable(address_B).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
