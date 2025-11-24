pragma solidity ^0.8.31;

contract ThreeWayLotteryShort {
    constructor() {
        lastTs = block.timestamp;
    }

    enum Role { None, Issuer, Alice, Bob }

    uint256 public lastTs;

    mapping(uint256 => bool) public actionDone;

    mapping(uint256 => uint256) public actionTimestamp;

    uint256 constant public ACTION_Issuer_0 = 0;

    uint256 constant public ACTION_Issuer_1 = 1;

    uint256 constant public ACTION_Alice_2 = 2;

    uint256 constant public ACTION_Alice_3 = 3;

    uint256 constant public ACTION_Bob_4 = 4;

    uint256 constant public ACTION_Bob_5 = 5;

    uint256 constant public FINAL_ACTION = 5;

    mapping(address => Role) public role;

    mapping(address => int256) public balanceOf;

    address public address_Issuer;

    address public address_Alice;

    address public address_Bob;

    bool public payoffs_distributed;

    bool public done_Issuer;

    bool public done_Alice;

    bool public done_Bob;

    bytes32 public Issuer_hidden_c;

    bool public done_Issuer_hidden_c;

    int256 public Issuer_c;

    bool public done_Issuer_c;

    bytes32 public Alice_hidden_c;

    bool public done_Alice_hidden_c;

    int256 public Alice_c;

    bool public done_Alice_c;

    bytes32 public Bob_hidden_c;

    bool public done_Bob_hidden_c;

    int256 public Bob_c;

    bool public done_Bob_c;

    modifier depends(uint256 actionId) {
        require(actionDone[actionId], "dependency not satisfied");
    }

    modifier notDone(uint256 actionId) {
        require((!actionDone[actionId]), "already done");
    }

    modifier by(Role r) {
        require((role[msg.sender] == r), "bad role");
    }

    modifier at_final_phase() {
        require(actionDone[FINAL_ACTION], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
    }

    function _checkReveal(bytes32 commitment, bytes preimage) internal pure {
        require((keccak256(preimage) == commitment), "bad reveal");
    }

    function _markActionDone(uint256 actionId) internal {
        actionDone[actionId] = true;
        actionTimestamp[actionId] = block.timestamp;
        lastTs = block.timestamp;
    }

    function move_Issuer_0(bytes32 _hidden_c) public payable by(Role.None) notDone(0) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_Issuer), "already joined");
        role[msg.sender] = Role.Issuer;
        address_Issuer = msg.sender;
        require((msg.value == 10), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Issuer = true;
        Issuer_hidden_c = _hidden_c;
        done_Issuer_hidden_c = true;
        _markActionDone(0);
    }

    function move_Alice_2(bytes32 _hidden_c) public payable by(Role.None) notDone(2) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_Alice), "already joined");
        role[msg.sender] = Role.Alice;
        address_Alice = msg.sender;
        require((msg.value == 10), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Alice = true;
        Alice_hidden_c = _hidden_c;
        done_Alice_hidden_c = true;
        _markActionDone(2);
    }

    function move_Bob_4(bytes32 _hidden_c) public payable by(Role.None) notDone(4) {
        require((role[msg.sender] == Role.None), "already has a role");
        require((!done_Bob), "already joined");
        role[msg.sender] = Role.Bob;
        address_Bob = msg.sender;
        require((msg.value == 10), "bad stake");
        balanceOf[msg.sender] = msg.value;
        done_Bob = true;
        Bob_hidden_c = _hidden_c;
        done_Bob_hidden_c = true;
        _markActionDone(4);
    }

    function move_Issuer_1(int256 _c, uint256 salt) public by(Role.Issuer) notDone(1) depends(0) depends(2) depends(4) {
        _checkReveal(Issuer_hidden_c, abi.encodePacked(_c, salt));
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        Issuer_c = _c;
        done_Issuer_c = true;
        _markActionDone(1);
    }

    function move_Alice_3(int256 _c, uint256 salt) public by(Role.Alice) notDone(3) depends(2) depends(0) depends(4) {
        _checkReveal(Alice_hidden_c, abi.encodePacked(_c, salt));
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        Alice_c = _c;
        done_Alice_c = true;
        _markActionDone(3);
    }

    function move_Bob_5(int256 _c, uint256 salt) public by(Role.Bob) notDone(5) depends(4) depends(0) depends(2) {
        _checkReveal(Bob_hidden_c, abi.encodePacked(_c, salt));
        require((((_c == 1) || (_c == 2)) || (_c == 3)), "domain");
        Bob_c = _c;
        done_Bob_c = true;
        _markActionDone(5);
    }

    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Issuer] = (((!done_Alice_c) || (!done_Bob_c))) ? 20 : ((!done_Issuer_c)) ? (-10) : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? (-10) : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? (-10) : 20;
        balanceOf[address_Alice] = (((!done_Alice_c) || (!done_Bob_c))) ? (-10) : ((!done_Issuer_c)) ? 20 : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? 20 : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? (-10) : (-10);
        balanceOf[address_Bob] = (((!done_Alice_c) || (!done_Bob_c))) ? (-10) : ((!done_Issuer_c)) ? (-10) : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == ((Issuer_c + Alice_c) + Bob_c))) ? (-10) : ((((((Issuer_c + Alice_c) + Bob_c) / 3) * 3) == (((Issuer_c + Alice_c) + Bob_c) - 1))) ? 20 : (-10);
    }

    function withdraw() public {
        int256 bal = balanceOf[msg.sender];
        require((bal > 0), "no funds");
        balanceOf[msg.sender] = 0;
        (bool ok, ) = payable(msg.sender).call{value: uint256(bal)}("");
        require(ok, "ETH send failed");
    }

    receive() public payable {
        revert("direct ETH not allowed");
    }
}
