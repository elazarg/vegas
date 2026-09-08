// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

contract OddsEvensShort {
    enum Role { None, Odd, Even }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 constant public ACTION_Even_0 = 0;
    uint256 constant public ACTION_Odd_0 = 1;
    uint256 constant public ACTION_Odd_2 = 2;
    uint256 constant public ACTION_Odd_3 = 3;
    uint256 constant public ACTION_Even_4 = 4;
    uint256 constant public ACTION_Even_5 = 5;
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
    
    modifier action(Role role, uint256 actionId) {
        require((!actionDone[role][actionId]), "already done");
        actionDone[role][actionId] = true;
        _;
        actionTimestamp[role][actionId] = block.timestamp;
        lastTs = block.timestamp;
    }
    
    modifier by(Role role) {
        require((roles[msg.sender] == role), "bad role");
        require(!bailed[role], "you bailed");
        _;
    }
    
    bytes32 private constant COMMIT_TAG = keccak256("VEGAS_COMMIT_V1");
    
    function _commitmentHash(Role role, address actor, bytes memory payload) internal view returns (bytes32) {
        return keccak256(abi.encode(
            COMMIT_TAG,
            address(this),
            role,
            actor,
            keccak256(payload)
        ));
    }
    
    function _checkReveal(bytes32 commitment, Role role, address actor, bytes memory payload) internal view {
        require(_commitmentHash(role, actor, payload) == commitment, "bad reveal");
    }
    
    
    constructor() {
        lastTs = block.timestamp;
    }
    
    function move_Odd_1() public payable by(Role.None) action(Role.Odd, 0) {
        require((!done_Odd), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Odd;
        address_Odd = msg.sender;
        done_Odd = true;
    }
    
    function move_Even_0() public payable by(Role.None) action(Role.Even, 0) {
        require((!done_Even), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Even;
        address_Even = msg.sender;
        done_Even = true;
    }
    
    function move_Odd_2(bytes32 _hidden_c) public by(Role.Odd) action(Role.Odd, 2) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Even][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Even] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Even]) {
                require(actionDone[Role.Even][0], "dependency not satisfied");
            }
            if (!actionDone[Role.Odd][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Odd] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Odd]) {
                require(actionDone[Role.Odd][0], "dependency not satisfied");
            }
        }
        Odd_c_hidden = _hidden_c;
        done_Odd_c_hidden = true;
    }
    
    function move_Even_4(bytes32 _hidden_c) public by(Role.Even) action(Role.Even, 4) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Even][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Even] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Even]) {
                require(actionDone[Role.Even][0], "dependency not satisfied");
            }
            if (!actionDone[Role.Odd][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Odd] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Odd]) {
                require(actionDone[Role.Odd][0], "dependency not satisfied");
            }
        }
        Even_c_hidden = _hidden_c;
        done_Even_c_hidden = true;
    }
    
    function move_Odd_3(bool _c, uint256 _salt) public by(Role.Odd) action(Role.Odd, 3) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Even][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Even] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Even]) {
                require(actionDone[Role.Even][0], "dependency not satisfied");
            }
            if (!actionDone[Role.Odd][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Odd] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Odd]) {
                require(actionDone[Role.Odd][0], "dependency not satisfied");
            }
            if (!actionDone[Role.Odd][2] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Odd] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Odd]) {
                require(actionDone[Role.Odd][2], "dependency not satisfied");
            }
            if (!actionDone[Role.Even][4] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Even] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Even]) {
                require(actionDone[Role.Even][4], "dependency not satisfied");
            }
        }
        _checkReveal(Odd_c_hidden, Role.Odd, msg.sender, abi.encode(_c, _salt));
        Odd_c = _c;
        done_Odd_c = true;
    }
    
    function move_Even_5(bool _c, uint256 _salt) public by(Role.Even) action(Role.Even, 5) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Even][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Even] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Even]) {
                require(actionDone[Role.Even][0], "dependency not satisfied");
            }
            if (!actionDone[Role.Odd][0] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Odd] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Odd]) {
                require(actionDone[Role.Odd][0], "dependency not satisfied");
            }
            if (!actionDone[Role.Odd][2] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Odd] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Odd]) {
                require(actionDone[Role.Odd][2], "dependency not satisfied");
            }
            if (!actionDone[Role.Even][4] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Even] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Even]) {
                require(actionDone[Role.Even][4], "dependency not satisfied");
            }
        }
        _checkReveal(Even_c_hidden, Role.Even, msg.sender, abi.encode(_c, _salt));
        Even_c = _c;
        done_Even_c = true;
    }
    
    function withdraw_Odd() public by(Role.Odd) action(Role.Odd, 4) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Odd][3] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Odd] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Odd]) {
                require(actionDone[Role.Odd][3], "dependency not satisfied");
            }
            if (!actionDone[Role.Even][5] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Even] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Even]) {
                require(actionDone[Role.Even][5], "dependency not satisfied");
            }
        }
        require((!claimed_Odd), "already claimed");
        claimed_Odd = true;
        int256 payout = (((!done_Odd_c) || (!done_Even_c)) ? (done_Odd_c ? (int256(100) + (((done_Odd_c ? int256(0) : int256(100)) + (done_Even_c ? int256(0) : int256(100))) / ((((done_Odd_c ? int256(1) : int256(0)) + (done_Even_c ? int256(1) : int256(0))) > int256(0)) ? ((done_Odd_c ? int256(1) : int256(0)) + (done_Even_c ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((Even_c == Odd_c) ? int256(74) : int256(126)));
        if (payout > 0) {
            (bool ok, ) = payable(address_Odd).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_Even() public by(Role.Even) action(Role.Even, 6) {
        {
            uint256 vegasDependencyOrigin = lastTs;
            if (!actionDone[Role.Odd][3] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Odd] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Odd]) {
                require(actionDone[Role.Odd][3], "dependency not satisfied");
            }
            if (!actionDone[Role.Even][5] && block.timestamp > vegasDependencyOrigin + TIMEOUT) {
                bailed[Role.Even] = true;
                lastTs = block.timestamp;
            }
            if (!bailed[Role.Even]) {
                require(actionDone[Role.Even][5], "dependency not satisfied");
            }
        }
        require((!claimed_Even), "already claimed");
        claimed_Even = true;
        int256 payout = (((!done_Odd_c) || (!done_Even_c)) ? (done_Even_c ? (int256(100) + (((done_Odd_c ? int256(0) : int256(100)) + (done_Even_c ? int256(0) : int256(100))) / ((((done_Odd_c ? int256(1) : int256(0)) + (done_Even_c ? int256(1) : int256(0))) > int256(0)) ? ((done_Odd_c ? int256(1) : int256(0)) + (done_Even_c ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((Even_c == Odd_c) ? int256(126) : int256(74)));
        if (payout > 0) {
            (bool ok, ) = payable(address_Even).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
