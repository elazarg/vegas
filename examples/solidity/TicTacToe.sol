pragma solidity ^0.8.31;

contract TicTacToe {
    enum Role { None, X, O }
    
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 public lastTs;
    uint256 constant public TIMEOUT = 86400;
    mapping(Role => bool) public bailed;
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
    mapping(address => Role) public roles;
    address public address_X;
    address public address_O;
    bool public done_X;
    bool public done_O;
    bool public claimed_X;
    bool public claimed_O;
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
    
    
    function move_X_0() public payable {
        require((roles[msg.sender] == Role.X), "bad role");
        _check_timestamp(Role.X);
        require((!bailed[Role.X]), "you bailed");
        require((!actionDone[Role.X][0]), "already done");
        require((!done_X), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.X;
        address_X = msg.sender;
        done_X = true;
        actionDone[Role.X][0] = true;
        actionTimestamp[Role.X][0] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_O_1() public payable {
        require((roles[msg.sender] == Role.O), "bad role");
        _check_timestamp(Role.O);
        require((!bailed[Role.O]), "you bailed");
        require((!actionDone[Role.O][1]), "already done");
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][0], "dependency not satisfied");
        }
        require((!done_O), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.O;
        address_O = msg.sender;
        done_O = true;
        actionDone[Role.O][1] = true;
        actionTimestamp[Role.O][1] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_X_2(int256 _c1) public {
        require((roles[msg.sender] == Role.X), "bad role");
        _check_timestamp(Role.X);
        require((!bailed[Role.X]), "you bailed");
        require((!actionDone[Role.X][2]), "already done");
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][1], "dependency not satisfied");
        }
        require((((_c1 == 0) || (_c1 == 1)) || (_c1 == 4)), "domain");
        X_c1 = _c1;
        done_X_c1 = true;
        actionDone[Role.X][2] = true;
        actionTimestamp[Role.X][2] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_O_3(int256 _c1) public {
        require((roles[msg.sender] == Role.O), "bad role");
        _check_timestamp(Role.O);
        require((!bailed[Role.O]), "you bailed");
        require((!actionDone[Role.O][3]), "already done");
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][2], "dependency not satisfied");
        }
        require((((((_c1 == 1) || (_c1 == 3)) || (_c1 == 4)) || (_c1 == 5)) || (_c1 == 9)), "domain");
        require((X_c1 != _c1), "domain");
        O_c1 = _c1;
        done_O_c1 = true;
        actionDone[Role.O][3] = true;
        actionTimestamp[Role.O][3] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_X_4(int256 _c2) public {
        require((roles[msg.sender] == Role.X), "bad role");
        _check_timestamp(Role.X);
        require((!bailed[Role.X]), "you bailed");
        require((!actionDone[Role.X][4]), "already done");
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][2], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][3], "dependency not satisfied");
        }
        require((((((((((_c2 == 0) || (_c2 == 1)) || (_c2 == 2)) || (_c2 == 3)) || (_c2 == 4)) || (_c2 == 5)) || (_c2 == 6)) || (_c2 == 7)) || (_c2 == 8)), "domain");
        require((((X_c1 != O_c1) && (X_c1 != _c2)) && (O_c1 != _c2)), "domain");
        X_c2 = _c2;
        done_X_c2 = true;
        actionDone[Role.X][4] = true;
        actionTimestamp[Role.X][4] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_O_5(int256 _c2) public {
        require((roles[msg.sender] == Role.O), "bad role");
        _check_timestamp(Role.O);
        require((!bailed[Role.O]), "you bailed");
        require((!actionDone[Role.O][5]), "already done");
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][2], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][3], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][4], "dependency not satisfied");
        }
        require((((((((((_c2 == 0) || (_c2 == 1)) || (_c2 == 2)) || (_c2 == 3)) || (_c2 == 4)) || (_c2 == 5)) || (_c2 == 6)) || (_c2 == 7)) || (_c2 == 8)), "domain");
        require(((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != _c2)) && (O_c1 != X_c2)) && (O_c1 != _c2)) && (X_c2 != _c2)), "domain");
        O_c2 = _c2;
        done_O_c2 = true;
        actionDone[Role.O][5] = true;
        actionTimestamp[Role.O][5] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_X_6(int256 _c3) public {
        require((roles[msg.sender] == Role.X), "bad role");
        _check_timestamp(Role.X);
        require((!bailed[Role.X]), "you bailed");
        require((!actionDone[Role.X][6]), "already done");
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][2], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][3], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][4], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][5], "dependency not satisfied");
        }
        require((((((((((_c3 == 0) || (_c3 == 1)) || (_c3 == 2)) || (_c3 == 3)) || (_c3 == 4)) || (_c3 == 5)) || (_c3 == 6)) || (_c3 == 7)) || (_c3 == 8)), "domain");
        require(((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != _c3)) && (O_c2 != _c3)), "domain");
        X_c3 = _c3;
        done_X_c3 = true;
        actionDone[Role.X][6] = true;
        actionTimestamp[Role.X][6] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_O_7(int256 _c3) public {
        require((roles[msg.sender] == Role.O), "bad role");
        _check_timestamp(Role.O);
        require((!bailed[Role.O]), "you bailed");
        require((!actionDone[Role.O][7]), "already done");
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][2], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][3], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][4], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][5], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][6], "dependency not satisfied");
        }
        require((((((((((_c3 == 0) || (_c3 == 1)) || (_c3 == 2)) || (_c3 == 3)) || (_c3 == 4)) || (_c3 == 5)) || (_c3 == 6)) || (_c3 == 7)) || (_c3 == 8)), "domain");
        require((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != _c3)) && (O_c2 != X_c3)) && (O_c2 != _c3)) && (X_c3 != _c3)), "domain");
        O_c3 = _c3;
        done_O_c3 = true;
        actionDone[Role.O][7] = true;
        actionTimestamp[Role.O][7] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_X_8(int256 _c4) public {
        require((roles[msg.sender] == Role.X), "bad role");
        _check_timestamp(Role.X);
        require((!bailed[Role.X]), "you bailed");
        require((!actionDone[Role.X][8]), "already done");
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][2], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][3], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][4], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][5], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][6], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][7], "dependency not satisfied");
        }
        require((((((((((_c4 == 0) || (_c4 == 1)) || (_c4 == 2)) || (_c4 == 3)) || (_c4 == 4)) || (_c4 == 5)) || (_c4 == 6)) || (_c4 == 7)) || (_c4 == 8)), "domain");
        require((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != _c4)) && (O_c3 != _c4)), "domain");
        X_c4 = _c4;
        done_X_c4 = true;
        actionDone[Role.X][8] = true;
        actionTimestamp[Role.X][8] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_O_9(int256 _c4) public {
        require((roles[msg.sender] == Role.O), "bad role");
        _check_timestamp(Role.O);
        require((!bailed[Role.O]), "you bailed");
        require((!actionDone[Role.O][9]), "already done");
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][2], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][3], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][4], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][5], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][6], "dependency not satisfied");
        }
        _check_timestamp(Role.O);
        if ((!bailed[Role.O]))
         {
            require(actionDone[Role.O][7], "dependency not satisfied");
        }
        _check_timestamp(Role.X);
        if ((!bailed[Role.X]))
         {
            require(actionDone[Role.X][8], "dependency not satisfied");
        }
        require((((((((((_c4 == 0) || (_c4 == 1)) || (_c4 == 2)) || (_c4 == 3)) || (_c4 == 4)) || (_c4 == 5)) || (_c4 == 6)) || (_c4 == 7)) || (_c4 == 8)), "domain");
        require(((((((((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != X_c4)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != X_c4)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != X_c4)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != X_c4)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != X_c4)) && (X_c3 != _c4)) && (O_c3 != X_c4)) && (O_c3 != _c4)) && (X_c4 != _c4)), "domain");
        O_c4 = _c4;
        done_O_c4 = true;
        actionDone[Role.O][9] = true;
        actionTimestamp[Role.O][9] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function withdraw_X() public {
        require((!claimed_X), "already claimed");
        claimed_X = true;
        int256 payout = 100;
        if (payout > 0) {
            (bool ok, ) = payable(address_X).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_O() public {
        require((!claimed_O), "already claimed");
        claimed_O = true;
        int256 payout = 100;
        if (payout > 0) {
            (bool ok, ) = payable(address_O).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
