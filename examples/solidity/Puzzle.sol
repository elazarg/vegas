pragma solidity ^0.8.31;

contract Puzzle {
    enum Role { None, Q, A }
    
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 public lastTs;
    uint256 constant public TIMEOUT = 86400;
    mapping(Role => bool) public bailed;
    uint256 constant public ACTION_Q_0 = 0;
    uint256 constant public ACTION_A_1 = 1;
    mapping(address => Role) public roles;
    address public address_Q;
    address public address_A;
    bool public done_Q;
    bool public done_A;
    bool public claimed_Q;
    bool public claimed_A;
    int256 public Q_x;
    bool public done_Q_x;
    int256 public A_p;
    bool public done_A_p;
    int256 public A_q;
    bool public done_A_q;
    
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
    

    function move_Q_0(int256 _x) public payable by(Role.Q) action(Role.Q, 0) {
        require((!done_Q), "already joined");
        require((msg.value == 50), "bad stake");
        roles[msg.sender] = Role.Q;
        address_Q = msg.sender;
        done_Q = true;
        Q_x = _x;
        done_Q_x = true;
    }
    
    function move_A_1(int256 _p, int256 _q) public by(Role.A) action(Role.A, 1) depends(Role.Q, 0) {
        require(((((_p * _q) == Q_x) && (_p != 1)) && (_q != 1)), "domain");
        require((!done_A), "already joined");
        roles[msg.sender] = Role.A;
        address_A = msg.sender;
        done_A = true;
        A_p = _p;
        done_A_p = true;
        A_q = _q;
        done_A_q = true;
    }
    
    function withdraw_Q() public {
        require((!claimed_Q), "already claimed");
        claimed_Q = true;
        int256 payout = 0;
        if (payout > 0) {
            (bool ok, ) = payable(address_Q).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_A() public {
        require((!claimed_A), "already claimed");
        claimed_A = true;
        int256 payout = 100;
        if (payout > 0) {
            (bool ok, ) = payable(address_A).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
