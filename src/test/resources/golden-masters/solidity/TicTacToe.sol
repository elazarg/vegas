pragma solidity ^0.8.31;

contract TicTacToe {
    enum Role { None, X, O }
    
    uint256 public lastTs;
    mapping(Role => mapping(uint256 => bool)) public actionDone;
    mapping(Role => mapping(uint256 => uint256)) public actionTimestamp;
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
    
    function move_X_0() public payable by(Role.None) action(Role.X, 0) {
        require((!done_X), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.X;
        address_X = msg.sender;
        done_X = true;
    }
    
    function move_O_1() public payable by(Role.None) action(Role.O, 1) depends(Role.X, 0) {
        require((!done_O), "already joined");
        require((msg.value == 100), "bad stake");
        roles[msg.sender] = Role.O;
        address_O = msg.sender;
        done_O = true;
    }
    
    function move_X_2(int256 _c1) public by(Role.X) action(Role.X, 2) depends(Role.O, 1) {
        require((((_c1 == 0) || (_c1 == 1)) || (_c1 == 4)), "domain");
        X_c1 = _c1;
        done_X_c1 = true;
    }
    
    function move_O_3(int256 _c1) public by(Role.O) action(Role.O, 3) depends(Role.X, 2) {
        require((((((_c1 == 1) || (_c1 == 3)) || (_c1 == 4)) || (_c1 == 5)) || (_c1 == 9)), "domain");
        require((X_c1 != _c1), "domain");
        O_c1 = _c1;
        done_O_c1 = true;
    }
    
    function move_X_4(int256 _c2) public by(Role.X) action(Role.X, 4) depends(Role.X, 2) depends(Role.O, 3) {
        require((((((((((_c2 == 0) || (_c2 == 1)) || (_c2 == 2)) || (_c2 == 3)) || (_c2 == 4)) || (_c2 == 5)) || (_c2 == 6)) || (_c2 == 7)) || (_c2 == 8)), "domain");
        require((((X_c1 != O_c1) && (X_c1 != _c2)) && (O_c1 != _c2)), "domain");
        X_c2 = _c2;
        done_X_c2 = true;
    }
    
    function move_O_5(int256 _c2) public by(Role.O) action(Role.O, 5) depends(Role.X, 2) depends(Role.O, 3) depends(Role.X, 4) {
        require((((((((((_c2 == 0) || (_c2 == 1)) || (_c2 == 2)) || (_c2 == 3)) || (_c2 == 4)) || (_c2 == 5)) || (_c2 == 6)) || (_c2 == 7)) || (_c2 == 8)), "domain");
        require(((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != _c2)) && (O_c1 != X_c2)) && (O_c1 != _c2)) && (X_c2 != _c2)), "domain");
        O_c2 = _c2;
        done_O_c2 = true;
    }
    
    function move_X_6(int256 _c3) public by(Role.X) action(Role.X, 6) depends(Role.X, 2) depends(Role.O, 3) depends(Role.X, 4) depends(Role.O, 5) {
        require((((((((((_c3 == 0) || (_c3 == 1)) || (_c3 == 2)) || (_c3 == 3)) || (_c3 == 4)) || (_c3 == 5)) || (_c3 == 6)) || (_c3 == 7)) || (_c3 == 8)), "domain");
        require(((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != _c3)) && (O_c2 != _c3)), "domain");
        X_c3 = _c3;
        done_X_c3 = true;
    }
    
    function move_O_7(int256 _c3) public by(Role.O) action(Role.O, 7) depends(Role.X, 2) depends(Role.O, 3) depends(Role.X, 4) depends(Role.O, 5) depends(Role.X, 6) {
        require((((((((((_c3 == 0) || (_c3 == 1)) || (_c3 == 2)) || (_c3 == 3)) || (_c3 == 4)) || (_c3 == 5)) || (_c3 == 6)) || (_c3 == 7)) || (_c3 == 8)), "domain");
        require((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != _c3)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != _c3)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != _c3)) && (O_c2 != X_c3)) && (O_c2 != _c3)) && (X_c3 != _c3)), "domain");
        O_c3 = _c3;
        done_O_c3 = true;
    }
    
    function move_X_8(int256 _c4) public by(Role.X) action(Role.X, 8) depends(Role.X, 2) depends(Role.O, 3) depends(Role.X, 4) depends(Role.O, 5) depends(Role.X, 6) depends(Role.O, 7) {
        require((((((((((_c4 == 0) || (_c4 == 1)) || (_c4 == 2)) || (_c4 == 3)) || (_c4 == 4)) || (_c4 == 5)) || (_c4 == 6)) || (_c4 == 7)) || (_c4 == 8)), "domain");
        require((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != _c4)) && (O_c3 != _c4)), "domain");
        X_c4 = _c4;
        done_X_c4 = true;
    }
    
    function move_O_9(int256 _c4) public by(Role.O) action(Role.O, 9) depends(Role.X, 2) depends(Role.O, 3) depends(Role.X, 4) depends(Role.O, 5) depends(Role.X, 6) depends(Role.O, 7) depends(Role.X, 8) {
        require((((((((((_c4 == 0) || (_c4 == 1)) || (_c4 == 2)) || (_c4 == 3)) || (_c4 == 4)) || (_c4 == 5)) || (_c4 == 6)) || (_c4 == 7)) || (_c4 == 8)), "domain");
        require(((((((((((((((((((((((((((((X_c1 != O_c1) && (X_c1 != X_c2)) && (X_c1 != O_c2)) && (X_c1 != X_c3)) && (X_c1 != O_c3)) && (X_c1 != X_c4)) && (X_c1 != _c4)) && (O_c1 != X_c2)) && (O_c1 != O_c2)) && (O_c1 != X_c3)) && (O_c1 != O_c3)) && (O_c1 != X_c4)) && (O_c1 != _c4)) && (X_c2 != O_c2)) && (X_c2 != X_c3)) && (X_c2 != O_c3)) && (X_c2 != X_c4)) && (X_c2 != _c4)) && (O_c2 != X_c3)) && (O_c2 != O_c3)) && (O_c2 != X_c4)) && (O_c2 != _c4)) && (X_c3 != O_c3)) && (X_c3 != X_c4)) && (X_c3 != _c4)) && (O_c3 != X_c4)) && (O_c3 != _c4)) && (X_c4 != _c4)), "domain");
        O_c4 = _c4;
        done_O_c4 = true;
    }
    
    function withdraw_X() public by(Role.X) action(Role.X, 9) depends(Role.O, 9) {
        require((!claimed_X), "already claimed");
        claimed_X = true;
        int256 payout = ((!done_X_c1) ? (done_X_c1 ? (int256(100) + (((done_X_c1 ? int256(0) : int256(100)) + (true ? int256(0) : int256(100))) / ((((done_X_c1 ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) > int256(0)) ? ((done_X_c1 ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c1) ? (done_X_c1 ? (int256(100) + (((done_X_c1 ? int256(0) : int256(100)) + (done_O_c1 ? int256(0) : int256(100))) / ((((done_X_c1 ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) > int256(0)) ? ((done_X_c1 ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c2) ? ((done_X_c1 && done_X_c2) ? (int256(100) + ((((done_X_c1 && done_X_c2) ? int256(0) : int256(100)) + (done_O_c1 ? int256(0) : int256(100))) / (((((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) > int256(0)) ? (((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c2) ? ((done_X_c1 && done_X_c2) ? (int256(100) + ((((done_X_c1 && done_X_c2) ? int256(0) : int256(100)) + ((done_O_c1 && done_O_c2) ? int256(0) : int256(100))) / (((((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) > int256(0)) ? (((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c3) ? (((done_X_c1 && done_X_c2) && done_X_c3) ? (int256(100) + (((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(0) : int256(100)) + ((done_O_c1 && done_O_c2) ? int256(0) : int256(100))) / ((((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) > int256(0)) ? ((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c3) ? (((done_X_c1 && done_X_c2) && done_X_c3) ? (int256(100) + (((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(0) : int256(100)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(0) : int256(100))) / ((((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) > int256(0)) ? ((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c4) ? ((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? (int256(100) + ((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(0) : int256(100)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(0) : int256(100))) / (((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) > int256(0)) ? (((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c4) ? ((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? (int256(100) + ((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(0) : int256(100)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(0) : int256(100))) / (((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(1) : int256(0))) > int256(0)) ? (((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : int256(100)))))))));
        if (payout > 0) {
            (bool ok, ) = payable(address_X).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
    
    function withdraw_O() public by(Role.O) action(Role.O, 10) depends(Role.O, 9) {
        require((!claimed_O), "already claimed");
        claimed_O = true;
        int256 payout = ((!done_X_c1) ? (true ? (int256(100) + (((done_X_c1 ? int256(0) : int256(100)) + (true ? int256(0) : int256(100))) / ((((done_X_c1 ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) > int256(0)) ? ((done_X_c1 ? int256(1) : int256(0)) + (true ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c1) ? (done_O_c1 ? (int256(100) + (((done_X_c1 ? int256(0) : int256(100)) + (done_O_c1 ? int256(0) : int256(100))) / ((((done_X_c1 ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) > int256(0)) ? ((done_X_c1 ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c2) ? (done_O_c1 ? (int256(100) + ((((done_X_c1 && done_X_c2) ? int256(0) : int256(100)) + (done_O_c1 ? int256(0) : int256(100))) / (((((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) > int256(0)) ? (((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + (done_O_c1 ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c2) ? ((done_O_c1 && done_O_c2) ? (int256(100) + ((((done_X_c1 && done_X_c2) ? int256(0) : int256(100)) + ((done_O_c1 && done_O_c2) ? int256(0) : int256(100))) / (((((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) > int256(0)) ? (((done_X_c1 && done_X_c2) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c3) ? ((done_O_c1 && done_O_c2) ? (int256(100) + (((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(0) : int256(100)) + ((done_O_c1 && done_O_c2) ? int256(0) : int256(100))) / ((((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) > int256(0)) ? ((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + ((done_O_c1 && done_O_c2) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c3) ? (((done_O_c1 && done_O_c2) && done_O_c3) ? (int256(100) + (((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(0) : int256(100)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(0) : int256(100))) / ((((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) > int256(0)) ? ((((done_X_c1 && done_X_c2) && done_X_c3) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_X_c4) ? (((done_O_c1 && done_O_c2) && done_O_c3) ? (int256(100) + ((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(0) : int256(100)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(0) : int256(100))) / (((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) > int256(0)) ? (((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + (((done_O_c1 && done_O_c2) && done_O_c3) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : ((!done_O_c4) ? ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? (int256(100) + ((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(0) : int256(100)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(0) : int256(100))) / (((((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(1) : int256(0))) > int256(0)) ? (((((done_X_c1 && done_X_c2) && done_X_c3) && done_X_c4) ? int256(1) : int256(0)) + ((((done_O_c1 && done_O_c2) && done_O_c3) && done_O_c4) ? int256(1) : int256(0))) : int256(1)))) : int256(0)) : int256(100)))))))));
        if (payout > 0) {
            (bool ok, ) = payable(address_O).call{value: uint256(payout)}("");
            require(ok, "ETH send failed");
        }
    }
}
