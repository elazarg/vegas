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
    
    
    function move_A_0() public payable {
        require((roles[msg.sender] == Role.A), "bad role");
        _check_timestamp(Role.A);
        require((!bailed[Role.A]), "you bailed");
        require((!actionDone[Role.A][0]), "already done");
        require((!done_A), "already joined");
        require((msg.value == 10), "bad stake");
        roles[msg.sender] = Role.A;
        address_A = msg.sender;
        done_A = true;
        actionDone[Role.A][0] = true;
        actionTimestamp[Role.A][0] = block.timestamp;
        lastTs = block.timestamp;
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
