pragma solidity ^0.8.31;

contract OddsEvensShort {
    enum Role { None, Odd, Even }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
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
        actionDone[role][actionId] = true;
        _;
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
    
    function move_Odd_0(bytes32 _hidden_c) public payable by(Role.None) action(Role.Odd, 1) {
        require((!done_Odd), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Odd;
        address_Odd = msg.sender;
        done_Odd = true;
        Odd_c_hidden = _hidden_c;
        done_Odd_c_hidden = true;
    }
    
    function move_Even_2(bytes32 _hidden_c) public payable by(Role.None) action(Role.Even, 3) {
        require((!done_Even), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Even;
        address_Even = msg.sender;
        done_Even = true;
        Even_c_hidden = _hidden_c;
        done_Even_c_hidden = true;
    }
    
    function move_Odd_1(bool _c, uint256 _salt) public by(Role.Odd) action(Role.Odd, 2) depends(Role.Odd, 1) depends(Role.Even, 3) {
        require((keccak256(abi.encodePacked(_c, _salt)) == Odd_c_hidden), "reveal failed for c");
        Odd_c = _c;
        done_Odd_c = true;
    }
    
    function move_Even_3(bool _c, uint256 _salt) public by(Role.Even) action(Role.Even, 4) depends(Role.Odd, 1) depends(Role.Even, 3) {
        require((keccak256(abi.encodePacked(_c, _salt)) == Even_c_hidden), "reveal failed for c");
        Even_c = _c;
        done_Even_c = true;
    }
    
    function withdraw_Even() public by(Role.Even) action(Role.Even, 4) depends(Role.Odd, 2) depends(Role.Even, 4) {
        require((!claimed_Even), "already claimed");
        claimed_Even = true;
        int256 payout = ((done_Even_c && done_Odd_c) ? ((Even_c == Odd_c) ? 126 : 74) : (((!done_Even_c) && done_Odd_c) ? 20 : ((done_Even_c && (!done_Odd_c)) ? 180 : 100)));
        if (payout > 0) {
            (bool ok, ) = payable(address_Even).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Odd() public by(Role.Odd) action(Role.Odd, 5) depends(Role.Odd, 2) depends(Role.Even, 4) {
        require((!claimed_Odd), "already claimed");
        claimed_Odd = true;
        int256 payout = ((done_Even_c && done_Odd_c) ? ((Even_c == Odd_c) ? 74 : 126) : (((!done_Even_c) && done_Odd_c) ? 180 : ((done_Even_c && (!done_Odd_c)) ? 20 : 100)));
        if (payout > 0) {
            (bool ok, ) = payable(address_Odd).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
