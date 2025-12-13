pragma solidity ^0.8.31;

contract Trivial1 {
    enum Role { None, A }
    
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 public lastTs;
    uint256 constant public TIMEOUT = 86400;
    mapping(Role => bool) public bailed;
    uint256 constant public ACTION_A_0 = 0;
    mapping(address => Role) public roles;
    address public address_A;
    bool public done_A;
    bool public claimed_A;
    
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
        require((msg.value == 10), "bad stake");
        roles[msg.sender] = Role.A;
        address_A = msg.sender;
        done_A = true;
    }
    
    function withdraw_A() public {
        require((!claimed_A), "already claimed");
        claimed_A = true;
        int256 payout = 10;
        if (payout > 0) {
            (bool ok, ) = payable(address_A).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
