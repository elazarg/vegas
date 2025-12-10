pragma solidity ^0.8.31;

contract Bet {
    enum Role { None, Gambler, Race }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(uint256 => uint256) public actionTimestamp;
    uint256 constant public ACTION_Race_0 = 0;
    uint256 constant public ACTION_Gambler_1 = 1;
    uint256 constant public ACTION_Race_2 = 2;
    uint256 constant public FINAL_ACTION = 2;
    mapping(address => Role) public roles;
    mapping(address => int256) public balanceOf;
    address public address_Gambler;
    address public address_Race;
    bool public done_Gambler;
    bool public done_Race;
    bool public payoffs_distributed;
    int256 public Gambler_bet;
    bool public done_Gambler_bet;
    int256 public Race_winner;
    bool public done_Race_winner;
    
    receive() public payable {
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
    
    modifier at_final_phase() {
        require(actionDone[FINAL_ACTION], "game not over");
        require((!payoffs_distributed), "payoffs already sent");
        _;
    }
    
    function _checkReveal(bytes32 commitment, bytes memory preimage) internal pure {
        require((keccak256(preimage) == commitment), "bad reveal");
    }
    
    constructor() {
        lastTs = block.timestamp;
    }
    
    function move_Race_0() public payable by(Role.None) action(Role.Race, 0) {
        require((!done_Race), "already joined");
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        roles[msg.sender] = Role.Race;
        address_Race = msg.sender;
        done_Race = true;
    }
    
    function move_Gambler_1(int256 _bet) public payable by(Role.None) action(Role.Gambler, 1) depends(Role.Race, 0) {
        require((((_bet == 1) || (_bet == 2)) || (_bet == 3)), "domain");
        require((!done_Gambler), "already joined");
        require((msg.value == 100), "bad stake");
        balanceOf[msg.sender] = msg.value;
        roles[msg.sender] = Role.Gambler;
        address_Gambler = msg.sender;
        done_Gambler = true;
        Gambler_bet = _bet;
        done_Gambler_bet = true;
    }
    
    function move_Race_2(int256 _winner) public by(Role.Race) action(Role.Race, 2) depends(Role.Gambler, 1) {
        require((((_winner == 1) || (_winner == 2)) || (_winner == 3)), "domain");
        Race_winner = _winner;
        done_Race_winner = true;
    }
    
    function distributePayoffs() public at_final_phase {
        payoffs_distributed = true;
        balanceOf[address_Gambler] = (((!done_Race_winner) || (Race_winner == Gambler_bet)) ? 100 : 0);
        balanceOf[address_Race] = (((!done_Race_winner) || (Race_winner == Gambler_bet)) ? 0 : 100);
    }
    
    function withdraw() public {
        int256 bal = balanceOf[msg.sender];
        require((bal > 0), "no funds");
        balanceOf[msg.sender] = 0;
        (bool ok, ) = payable(msg.sender).call{value: uint256(bal)}("");
        require(ok, "ETH send failed");
    }
}
