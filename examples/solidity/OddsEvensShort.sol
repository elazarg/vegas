pragma solidity ^0.8.31;

contract OddsEvensShort {
    enum Role { None, Odd, Even }
    
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 public lastTs;
    uint256 constant public TIMEOUT = 86400;
    mapping(Role => bool) public bailed;
    uint256 constant public ACTION_Odd_1 = 0;
    uint256 constant public ACTION_Odd_2 = 1;
    uint256 constant public ACTION_Even_3 = 2;
    uint256 constant public ACTION_Even_4 = 3;
    mapping(address => Role) public roles;
    address public address_Odd;
    address public address_Even;
    bool public done_Odd;
    bool public done_Even;
    bool public claimed_Odd;
    bool public claimed_Even;
    bool public Odd_c;
    bool public done_Odd_c;
    bytes32 public Odd_c_hidden;
    bool public done_Odd_c_hidden;
    bool public Even_c;
    bool public done_Even_c;
    bytes32 public Even_c_hidden;
    bool public done_Even_c_hidden;
    
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
    
    
    function move_Odd_0(bytes32 _hidden_c) public payable {
        require((roles[msg.sender] == Role.Odd), "bad role");
        _check_timestamp(Role.Odd);
        require((!bailed[Role.Odd]), "you bailed");
        require((!actionDone[Role.Odd][1]), "already done");
        require((!done_Odd), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Odd;
        address_Odd = msg.sender;
        done_Odd = true;
        Odd_c_hidden = _hidden_c;
        done_Odd_c_hidden = true;
        actionDone[Role.Odd][1] = true;
        actionTimestamp[Role.Odd][1] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Even_2(bytes32 _hidden_c) public payable {
        require((roles[msg.sender] == Role.Even), "bad role");
        _check_timestamp(Role.Even);
        require((!bailed[Role.Even]), "you bailed");
        require((!actionDone[Role.Even][3]), "already done");
        require((!done_Even), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Even;
        address_Even = msg.sender;
        done_Even = true;
        Even_c_hidden = _hidden_c;
        done_Even_c_hidden = true;
        actionDone[Role.Even][3] = true;
        actionTimestamp[Role.Even][3] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Odd_1(bool _c, uint256 _salt) public {
        require((roles[msg.sender] == Role.Odd), "bad role");
        _check_timestamp(Role.Odd);
        require((!bailed[Role.Odd]), "you bailed");
        require((!actionDone[Role.Odd][2]), "already done");
        _check_timestamp(Role.Odd);
        if ((!bailed[Role.Odd]))
         {
            require(actionDone[Role.Odd][1], "dependency not satisfied");
        }
        _check_timestamp(Role.Even);
        if ((!bailed[Role.Even]))
         {
            require(actionDone[Role.Even][3], "dependency not satisfied");
        }
        require((keccak256(abi.encodePacked(_c, _salt)) == Odd_c_hidden), "reveal failed for c");
        Odd_c = _c;
        done_Odd_c = true;
        actionDone[Role.Odd][2] = true;
        actionTimestamp[Role.Odd][2] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function move_Even_3(bool _c, uint256 _salt) public {
        require((roles[msg.sender] == Role.Even), "bad role");
        _check_timestamp(Role.Even);
        require((!bailed[Role.Even]), "you bailed");
        require((!actionDone[Role.Even][4]), "already done");
        _check_timestamp(Role.Odd);
        if ((!bailed[Role.Odd]))
         {
            require(actionDone[Role.Odd][1], "dependency not satisfied");
        }
        _check_timestamp(Role.Even);
        if ((!bailed[Role.Even]))
         {
            require(actionDone[Role.Even][3], "dependency not satisfied");
        }
        require((keccak256(abi.encodePacked(_c, _salt)) == Even_c_hidden), "reveal failed for c");
        Even_c = _c;
        done_Even_c = true;
        actionDone[Role.Even][4] = true;
        actionTimestamp[Role.Even][4] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    function withdraw_Even() public {
        require((!claimed_Even), "already claimed");
        claimed_Even = true;
        int256 payout = ((done_Even_c && done_Odd_c) ? ((Even_c == Odd_c) ? 126 : 74) : (((!done_Even_c) && done_Odd_c) ? 20 : ((done_Even_c && (!done_Odd_c)) ? 180 : 100)));
        if (payout > 0) {
            (bool ok, ) = payable(address_Even).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Odd() public {
        require((!claimed_Odd), "already claimed");
        claimed_Odd = true;
        int256 payout = ((done_Even_c && done_Odd_c) ? ((Even_c == Odd_c) ? 74 : 126) : (((!done_Even_c) && done_Odd_c) ? 180 : ((done_Even_c && (!done_Odd_c)) ? 20 : 100)));
        if (payout > 0) {
            (bool ok, ) = payable(address_Odd).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
