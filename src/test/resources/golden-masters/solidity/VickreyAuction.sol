// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

contract VickreyAuction {
    enum Role { None, Seller, B1, B2, B3 }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
    uint256 constant public ACTION_B1_0 = 0;
    uint256 constant public ACTION_B2_0 = 1;
    uint256 constant public ACTION_B3_0 = 2;
    uint256 constant public ACTION_Seller_0 = 3;
    uint256 constant public ACTION_B1_2 = 4;
    uint256 constant public ACTION_B1_3 = 5;
    uint256 constant public ACTION_B2_4 = 6;
    uint256 constant public ACTION_B2_5 = 7;
    uint256 constant public ACTION_B3_6 = 8;
    uint256 constant public ACTION_B3_7 = 9;
    mapping(address => Role) public roles;
    address public address_Seller;
    address public address_B1;
    address public address_B2;
    address public address_B3;
    bool public done_Seller;
    bool public done_B1;
    bool public done_B2;
    bool public done_B3;
    bool public claimed_Seller;
    bool public claimed_B1;
    bool public claimed_B2;
    bool public claimed_B3;
    int256 public B1_b;
    bool public done_B1_b;
    bytes32 public B1_b_hidden;
    bool public done_B1_b_hidden;
    int256 public B2_b;
    bool public done_B2_b;
    bytes32 public B2_b_hidden;
    bool public done_B2_b_hidden;
    int256 public B3_b;
    bool public done_B3_b;
    bytes32 public B3_b_hidden;
    bool public done_B3_b_hidden;
    
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
    
    function move_Seller_3() public payable by(Role.None) action(Role.Seller, 0) {
        require((!done_Seller), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.Seller;
        address_Seller = msg.sender;
        done_Seller = true;
    }
    
    function move_B1_0() public payable by(Role.None) action(Role.B1, 0) {
        require((!done_B1), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.B1;
        address_B1 = msg.sender;
        done_B1 = true;
    }
    
    function move_B2_1() public payable by(Role.None) action(Role.B2, 0) {
        require((!done_B2), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.B2;
        address_B2 = msg.sender;
        done_B2 = true;
    }
    
    function move_B3_2() public payable by(Role.None) action(Role.B3, 0) {
        require((!done_B3), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.B3;
        address_B3 = msg.sender;
        done_B3 = true;
    }
    
    function move_B1_4(bytes32 _hidden_b) public by(Role.B1) action(Role.B1, 2) depends(Role.B1, 0) depends(Role.B2, 0) depends(Role.B3, 0) depends(Role.Seller, 0) {
        B1_b_hidden = _hidden_b;
        done_B1_b_hidden = true;
    }
    
    function move_B2_6(bytes32 _hidden_b) public by(Role.B2) action(Role.B2, 4) depends(Role.B1, 0) depends(Role.B2, 0) depends(Role.B3, 0) depends(Role.Seller, 0) {
        B2_b_hidden = _hidden_b;
        done_B2_b_hidden = true;
    }
    
    function move_B3_8(bytes32 _hidden_b) public by(Role.B3) action(Role.B3, 6) depends(Role.B1, 0) depends(Role.B2, 0) depends(Role.B3, 0) depends(Role.Seller, 0) {
        B3_b_hidden = _hidden_b;
        done_B3_b_hidden = true;
    }
    
    function move_B1_5(int256 _b, uint256 _salt) public by(Role.B1) action(Role.B1, 3) depends(Role.B1, 0) depends(Role.B2, 0) depends(Role.B3, 0) depends(Role.Seller, 0) depends(Role.B1, 2) depends(Role.B2, 4) depends(Role.B3, 6) {
        require((((_b == 0) || (_b == 1)) || (_b == 2)), "domain");
        _checkReveal(B1_b_hidden, Role.B1, msg.sender, abi.encode(_b, _salt));
        B1_b = _b;
        done_B1_b = true;
    }
    
    function move_B2_7(int256 _b, uint256 _salt) public by(Role.B2) action(Role.B2, 5) depends(Role.B1, 0) depends(Role.B2, 0) depends(Role.B3, 0) depends(Role.Seller, 0) depends(Role.B1, 2) depends(Role.B2, 4) depends(Role.B3, 6) {
        require((((_b == 0) || (_b == 1)) || (_b == 2)), "domain");
        _checkReveal(B2_b_hidden, Role.B2, msg.sender, abi.encode(_b, _salt));
        B2_b = _b;
        done_B2_b = true;
    }
    
    function move_B3_9(int256 _b, uint256 _salt) public by(Role.B3) action(Role.B3, 7) depends(Role.B1, 0) depends(Role.B2, 0) depends(Role.B3, 0) depends(Role.Seller, 0) depends(Role.B1, 2) depends(Role.B2, 4) depends(Role.B3, 6) {
        require((((_b == 0) || (_b == 1)) || (_b == 2)), "domain");
        _checkReveal(B3_b_hidden, Role.B3, msg.sender, abi.encode(_b, _salt));
        B3_b = _b;
        done_B3_b = true;
    }
    
    function withdraw_Seller() public by(Role.Seller) action(Role.Seller, 1) depends(Role.B1, 3) depends(Role.B2, 5) depends(Role.B3, 7) {
        require((!claimed_Seller), "already claimed");
        claimed_Seller = true;
        int256 payout = ((((!done_B1_b) || (!done_B2_b)) || (!done_B3_b)) ? (true ? (int256(100) + (((((true ? int256(0) : int256(100)) + (done_B1_b ? int256(0) : int256(100))) + (done_B2_b ? int256(0) : int256(100))) + (done_B3_b ? int256(0) : int256(100))) / ((((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) > int256(0)) ? ((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : (int256(100) + ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B2_b >= B3_b) ? B2_b : B3_b) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B1_b >= B3_b) ? B1_b : B3_b) : ((B1_b >= B2_b) ? B1_b : B2_b)))));
        if (payout > 0) {
            (bool ok, ) = payable(address_Seller).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B1() public by(Role.B1) action(Role.B1, 4) depends(Role.B1, 3) depends(Role.B2, 5) depends(Role.B3, 7) {
        require((!claimed_B1), "already claimed");
        claimed_B1 = true;
        int256 payout = ((((!done_B1_b) || (!done_B2_b)) || (!done_B3_b)) ? (done_B1_b ? (int256(100) + (((((true ? int256(0) : int256(100)) + (done_B1_b ? int256(0) : int256(100))) + (done_B2_b ? int256(0) : int256(100))) + (done_B3_b ? int256(0) : int256(100))) / ((((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) > int256(0)) ? ((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? (int256(100) - ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B2_b >= B3_b) ? B2_b : B3_b) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B1_b >= B3_b) ? B1_b : B3_b) : ((B1_b >= B2_b) ? B1_b : B2_b)))) : int256(100)));
        if (payout > 0) {
            (bool ok, ) = payable(address_B1).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B2() public by(Role.B2) action(Role.B2, 6) depends(Role.B1, 3) depends(Role.B2, 5) depends(Role.B3, 7) {
        require((!claimed_B2), "already claimed");
        claimed_B2 = true;
        int256 payout = ((((!done_B1_b) || (!done_B2_b)) || (!done_B3_b)) ? (done_B2_b ? (int256(100) + (((((true ? int256(0) : int256(100)) + (done_B1_b ? int256(0) : int256(100))) + (done_B2_b ? int256(0) : int256(100))) + (done_B3_b ? int256(0) : int256(100))) / ((((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) > int256(0)) ? ((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? (int256(100) - ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B2_b >= B3_b) ? B2_b : B3_b) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B1_b >= B3_b) ? B1_b : B3_b) : ((B1_b >= B2_b) ? B1_b : B2_b)))) : int256(100)));
        if (payout > 0) {
            (bool ok, ) = payable(address_B2).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_B3() public by(Role.B3) action(Role.B3, 8) depends(Role.B1, 3) depends(Role.B2, 5) depends(Role.B3, 7) {
        require((!claimed_B3), "already claimed");
        claimed_B3 = true;
        int256 payout = ((((!done_B1_b) || (!done_B2_b)) || (!done_B3_b)) ? (done_B3_b ? (int256(100) + (((((true ? int256(0) : int256(100)) + (done_B1_b ? int256(0) : int256(100))) + (done_B2_b ? int256(0) : int256(100))) + (done_B3_b ? int256(0) : int256(100))) / ((((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) > int256(0)) ? ((((true ? int256(1) : int256(0)) + (done_B1_b ? int256(1) : int256(0))) + (done_B2_b ? int256(1) : int256(0))) + (done_B3_b ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((B3_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? (int256(100) - ((B1_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B2_b >= B3_b) ? B2_b : B3_b) : ((B2_b == ((((B1_b >= B2_b) ? B1_b : B2_b) >= B3_b) ? ((B1_b >= B2_b) ? B1_b : B2_b) : B3_b)) ? ((B1_b >= B3_b) ? B1_b : B3_b) : ((B1_b >= B2_b) ? B1_b : B2_b)))) : int256(100)));
        if (payout > 0) {
            (bool ok, ) = payable(address_B3).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
