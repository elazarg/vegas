pragma solidity ^0.8.31;

contract ThreeWayLotteryBuggy {
    enum Role { None, Issuer, Alice, Bob }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 constant public ACTION_Issuer_0 = 0;
    uint256 constant public ACTION_Alice_1 = 1;
    uint256 constant public ACTION_Bob_2 = 2;
    uint256 constant public ACTION_Issuer_4 = 3;
    uint256 constant public ACTION_Issuer_5 = 4;
    uint256 constant public ACTION_Alice_6 = 5;
    uint256 constant public ACTION_Alice_7 = 6;
    uint256 constant public ACTION_Bob_8 = 7;
    uint256 constant public ACTION_Bob_9 = 8;
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
    
    function move_Issuer_0() public payable by(Role.None) action(Role.Issuer, 0) {
        require((!done_Issuer), "already joined");
        require((msg.value == 10), "bad stake");
        roles[msg.sender] = Role.Issuer;
        address_Issuer = msg.sender;
        done_Issuer = true;
    }
    
    function move_Alice_1() public payable by(Role.None) action(Role.Alice, 1) depends(Role.Issuer, 0) {
        require((!done_Alice), "already joined");
        require((msg.value == 10), "bad stake");
        roles[msg.sender] = Role.Alice;
        address_Alice = msg.sender;
        done_Alice = true;
    }
    
    function move_Bob_2() public payable by(Role.None) action(Role.Bob, 2) depends(Role.Alice, 1) {
        require((!done_Bob), "already joined");
        require((msg.value == 10), "bad stake");
        roles[msg.sender] = Role.Bob;
        address_Bob = msg.sender;
        done_Bob = true;
    }
    
    function move_Issuer_3(bytes32 _hidden_c) public by(Role.Issuer) action(Role.Issuer, 4) depends(Role.Bob, 2) {
        Issuer_c_hidden = _hidden_c;
        done_Issuer_c_hidden = true;
    }
    
    function move_Alice_5(bytes32 _hidden_c) public by(Role.Alice) action(Role.Alice, 6) depends(Role.Bob, 2) {
        Alice_c_hidden = _hidden_c;
        done_Alice_c_hidden = true;
    }
    
    function move_Bob_7(bytes32 _hidden_c) public by(Role.Bob) action(Role.Bob, 8) depends(Role.Bob, 2) {
        Bob_c_hidden = _hidden_c;
        done_Bob_c_hidden = true;
    }
    
    function move_Issuer_4(int256 _c, uint256 _salt) public by(Role.Issuer) action(Role.Issuer, 5) depends(Role.Bob, 2) depends(Role.Issuer, 4) depends(Role.Alice, 6) depends(Role.Bob, 8) {
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        require((keccak256(abi.encodePacked(_c, _salt)) == Issuer_c_hidden), "reveal failed for c");
        Issuer_c = _c;
        done_Issuer_c = true;
    }
    
    function move_Alice_6(int256 _c, uint256 _salt) public by(Role.Alice) action(Role.Alice, 7) depends(Role.Bob, 2) depends(Role.Issuer, 4) depends(Role.Alice, 6) depends(Role.Bob, 8) {
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        require((keccak256(abi.encodePacked(_c, _salt)) == Alice_c_hidden), "reveal failed for c");
        Alice_c = _c;
        done_Alice_c = true;
    }
    
    function move_Bob_8(int256 _c, uint256 _salt) public by(Role.Bob) action(Role.Bob, 9) depends(Role.Bob, 2) depends(Role.Issuer, 4) depends(Role.Alice, 6) depends(Role.Bob, 8) {
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        require((keccak256(abi.encodePacked(_c, _salt)) == Bob_c_hidden), "reveal failed for c");
        Bob_c = _c;
        done_Bob_c = true;
    }
    
    function withdraw_Bob() public by(Role.Bob) action(Role.Bob, 9) depends(Role.Issuer, 5) depends(Role.Alice, 7) depends(Role.Bob, 9) {
        require((!claimed_Bob), "already claimed");
        claimed_Bob = true;
        int256 payout = (((!done_Alice_c) || (!done_Bob_c)) ? (-10) : ((!done_Issuer_c) ? (-10) : ((Alice_c == Bob_c) ? (-10) : ((((((Alice_c + Bob_c) + Issuer_c) / 2) * 2) == ((Alice_c + Bob_c) + Issuer_c)) ? (-10) : 20))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Bob).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Issuer() public by(Role.Issuer) action(Role.Issuer, 10) depends(Role.Issuer, 5) depends(Role.Alice, 7) depends(Role.Bob, 9) {
        require((!claimed_Issuer), "already claimed");
        claimed_Issuer = true;
        int256 payout = (((!done_Alice_c) || (!done_Bob_c)) ? 20 : ((!done_Issuer_c) ? (-10) : ((Alice_c == Bob_c) ? 20 : ((((((Alice_c + Bob_c) + Issuer_c) / 2) * 2) == ((Alice_c + Bob_c) + Issuer_c)) ? (-10) : (-10)))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Issuer).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Alice() public by(Role.Alice) action(Role.Alice, 11) depends(Role.Issuer, 5) depends(Role.Alice, 7) depends(Role.Bob, 9) {
        require((!claimed_Alice), "already claimed");
        claimed_Alice = true;
        int256 payout = (((!done_Alice_c) || (!done_Bob_c)) ? (-10) : ((!done_Issuer_c) ? 20 : ((Alice_c == Bob_c) ? (-10) : ((((((Alice_c + Bob_c) + Issuer_c) / 2) * 2) == ((Alice_c + Bob_c) + Issuer_c)) ? 20 : (-10)))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Alice).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
