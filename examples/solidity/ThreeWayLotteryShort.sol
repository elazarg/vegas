pragma solidity ^0.8.31;

contract ThreeWayLotteryShort {
    enum Role { None, Issuer, Alice, Bob }
    
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 public lastTs;
    uint256 constant public TIMEOUT = 86400;
    mapping(Role => bool) public bailed;
    uint256 constant public ACTION_Issuer_1 = 0;
    uint256 constant public ACTION_Issuer_2 = 1;
    uint256 constant public ACTION_Alice_3 = 2;
    uint256 constant public ACTION_Alice_4 = 3;
    uint256 constant public ACTION_Bob_5 = 4;
    uint256 constant public ACTION_Bob_6 = 5;
    mapping(address => Role) public roles;
    address public address_Issuer;
    address public address_Alice;
    address public address_Bob;
    bool public done_Issuer;
    bool public done_Alice;
    bool public done_Bob;
    bool public claimed_Issuer;
    bool public claimed_Alice;
    bool public claimed_Bob;
    int256 public Issuer_c;
    bool public done_Issuer_c;
    bytes32 public Issuer_c_hidden;
    bool public done_Issuer_c_hidden;
    int256 public Alice_c;
    bool public done_Alice_c;
    bytes32 public Alice_c_hidden;
    bool public done_Alice_c_hidden;
    int256 public Bob_c;
    bool public done_Bob_c;
    bytes32 public Bob_c_hidden;
    bool public done_Bob_c_hidden;
    
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
    
    
    function move_Issuer_0(bytes32 _hidden_c) public payable {
        require((roles[msg.sender] == Role.Issuer), "bad role");
        _check_timestamp(Role.Issuer);
        require((!bailed[Role.Issuer]), "you bailed");
        require((!actionDone[Role.Issuer][1]), "already done");
        require((!done_Issuer), "already joined");
        require((msg.value == 12), "bad stake");
        roles[msg.sender] = Role.Issuer;
        address_Issuer = msg.sender;
        done_Issuer = true;
        Issuer_c_hidden = _hidden_c;
        done_Issuer_c_hidden = true;
        actionDone[Role.Issuer][1] = true;
        actionTimestamp[Role.Issuer][1] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Alice_2(bytes32 _hidden_c) public payable {
        require((roles[msg.sender] == Role.Alice), "bad role");
        _check_timestamp(Role.Alice);
        require((!bailed[Role.Alice]), "you bailed");
        require((!actionDone[Role.Alice][3]), "already done");
        require((!done_Alice), "already joined");
        require((msg.value == 12), "bad stake");
        roles[msg.sender] = Role.Alice;
        address_Alice = msg.sender;
        done_Alice = true;
        Alice_c_hidden = _hidden_c;
        done_Alice_c_hidden = true;
        actionDone[Role.Alice][3] = true;
        actionTimestamp[Role.Alice][3] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Bob_4(bytes32 _hidden_c) public payable {
        require((roles[msg.sender] == Role.Bob), "bad role");
        _check_timestamp(Role.Bob);
        require((!bailed[Role.Bob]), "you bailed");
        require((!actionDone[Role.Bob][5]), "already done");
        require((!done_Bob), "already joined");
        require((msg.value == 12), "bad stake");
        roles[msg.sender] = Role.Bob;
        address_Bob = msg.sender;
        done_Bob = true;
        Bob_c_hidden = _hidden_c;
        done_Bob_c_hidden = true;
        actionDone[Role.Bob][5] = true;
        actionTimestamp[Role.Bob][5] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Issuer_1(int256 _c, uint256 _salt) public {
        require((roles[msg.sender] == Role.Issuer), "bad role");
        _check_timestamp(Role.Issuer);
        require((!bailed[Role.Issuer]), "you bailed");
        require((!actionDone[Role.Issuer][2]), "already done");
        _check_timestamp(Role.Issuer);
        if ((!bailed[Role.Issuer]))
         {
            require(actionDone[Role.Issuer][1], "dependency not satisfied");
        }
        _check_timestamp(Role.Alice);
        if ((!bailed[Role.Alice]))
         {
            require(actionDone[Role.Alice][3], "dependency not satisfied");
        }
        _check_timestamp(Role.Bob);
        if ((!bailed[Role.Bob]))
         {
            require(actionDone[Role.Bob][5], "dependency not satisfied");
        }
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        require((keccak256(abi.encodePacked(_c, _salt)) == Issuer_c_hidden), "reveal failed for c");
        Issuer_c = _c;
        done_Issuer_c = true;
        actionDone[Role.Issuer][2] = true;
        actionTimestamp[Role.Issuer][2] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Alice_3(int256 _c, uint256 _salt) public {
        require((roles[msg.sender] == Role.Alice), "bad role");
        _check_timestamp(Role.Alice);
        require((!bailed[Role.Alice]), "you bailed");
        require((!actionDone[Role.Alice][4]), "already done");
        _check_timestamp(Role.Issuer);
        if ((!bailed[Role.Issuer]))
         {
            require(actionDone[Role.Issuer][1], "dependency not satisfied");
        }
        _check_timestamp(Role.Alice);
        if ((!bailed[Role.Alice]))
         {
            require(actionDone[Role.Alice][3], "dependency not satisfied");
        }
        _check_timestamp(Role.Bob);
        if ((!bailed[Role.Bob]))
         {
            require(actionDone[Role.Bob][5], "dependency not satisfied");
        }
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        require((keccak256(abi.encodePacked(_c, _salt)) == Alice_c_hidden), "reveal failed for c");
        Alice_c = _c;
        done_Alice_c = true;
        actionDone[Role.Alice][4] = true;
        actionTimestamp[Role.Alice][4] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Bob_5(int256 _c, uint256 _salt) public {
        require((roles[msg.sender] == Role.Bob), "bad role");
        _check_timestamp(Role.Bob);
        require((!bailed[Role.Bob]), "you bailed");
        require((!actionDone[Role.Bob][6]), "already done");
        _check_timestamp(Role.Issuer);
        if ((!bailed[Role.Issuer]))
         {
            require(actionDone[Role.Issuer][1], "dependency not satisfied");
        }
        _check_timestamp(Role.Alice);
        if ((!bailed[Role.Alice]))
         {
            require(actionDone[Role.Alice][3], "dependency not satisfied");
        }
        _check_timestamp(Role.Bob);
        if ((!bailed[Role.Bob]))
         {
            require(actionDone[Role.Bob][5], "dependency not satisfied");
        }
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        require((keccak256(abi.encodePacked(_c, _salt)) == Bob_c_hidden), "reveal failed for c");
        Bob_c = _c;
        done_Bob_c = true;
        actionDone[Role.Bob][6] = true;
        actionTimestamp[Role.Bob][6] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function withdraw_Bob() public {
        require((!claimed_Bob), "already claimed");
        claimed_Bob = true;
        int256 payout = (((done_Alice_c && done_Bob_c) && done_Issuer_c) ? (((((Issuer_c + Alice_c) + Bob_c) % 3) == 0) ? 6 : (((((Issuer_c + Alice_c) + Bob_c) % 3) == 1) ? 24 : 6)) : (((!done_Alice_c) && (!done_Bob_c)) ? 1 : (((!done_Alice_c) && (!done_Issuer_c)) ? 34 : (((!done_Bob_c) && (!done_Issuer_c)) ? 1 : ((!done_Alice_c) ? 17 : ((!done_Bob_c) ? 2 : ((!done_Issuer_c) ? 17 : 12)))))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Bob).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Issuer() public {
        require((!claimed_Issuer), "already claimed");
        claimed_Issuer = true;
        int256 payout = (((done_Alice_c && done_Bob_c) && done_Issuer_c) ? (((((Issuer_c + Alice_c) + Bob_c) % 3) == 0) ? 6 : (((((Issuer_c + Alice_c) + Bob_c) % 3) == 1) ? 6 : 24)) : (((!done_Alice_c) && (!done_Bob_c)) ? 34 : (((!done_Alice_c) && (!done_Issuer_c)) ? 1 : (((!done_Bob_c) && (!done_Issuer_c)) ? 1 : ((!done_Alice_c) ? 17 : ((!done_Bob_c) ? 17 : ((!done_Issuer_c) ? 2 : 12)))))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Issuer).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Alice() public {
        require((!claimed_Alice), "already claimed");
        claimed_Alice = true;
        int256 payout = (((done_Alice_c && done_Bob_c) && done_Issuer_c) ? (((((Issuer_c + Alice_c) + Bob_c) % 3) == 0) ? 24 : (((((Issuer_c + Alice_c) + Bob_c) % 3) == 1) ? 6 : 6)) : (((!done_Alice_c) && (!done_Bob_c)) ? 1 : (((!done_Alice_c) && (!done_Issuer_c)) ? 1 : (((!done_Bob_c) && (!done_Issuer_c)) ? 34 : ((!done_Alice_c) ? 2 : ((!done_Bob_c) ? 17 : ((!done_Issuer_c) ? 17 : 12)))))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Alice).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
