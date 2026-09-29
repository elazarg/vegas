// SPDX-License-Identifier: MIT
pragma solidity ^0.8.37;

/// The request of Chainlink VRF v2.5 (`VRFV2PlusClient.RandomWordsRequest`).
struct RandomWordsRequest {
    bytes32 keyHash;
    uint256 subId;
    uint16 requestConfirmations;
    uint32 callbackGasLimit;
    uint32 numWords;
    bytes extraArgs;
}

/// The part of the VRF v2.5 coordinator this adapter uses.
interface IVrfCoordinatorV2Plus {
    function requestRandomWords(RandomWordsRequest calldata req) external returns (uint256 requestId);
}

/// An `IVegasBeacon` backed by Chainlink VRF v2.5.
///
/// A Vegas draw asks for the first round after its readiness time plus the
/// contract's beacon delay; call that time `t`. Here the round for `t` is a VRF
/// request that anyone may make once `t` has passed, fulfilled by the
/// coordinator's callback. The requester cannot choose the output (the VRF
/// proof fixes it), and the request postdates `t`, when the block that made
/// the draw ready is final. Each `t` is requested and fulfilled once, so
/// retrying cannot pick among outputs.
///
/// Trust: the VRF operator computes each output before publishing it, so it
/// could bias a draw by withholding an output it dislikes; it is trusted not
/// to, and to stay live (a round nobody requests, or that is never fulfilled,
/// stalls the draw). A threshold beacon such as drand removes the single
/// party who sees a round early. The subscription must list this contract as
/// a consumer and stay funded.
contract VrfBeacon {
    IVrfCoordinatorV2Plus public immutable coordinator;
    bytes32 public immutable keyHash;
    uint256 public immutable subId;
    uint16 public constant REQUEST_CONFIRMATIONS = 3;
    uint32 public constant CALLBACK_GAS_LIMIT = 100000;

    /// Request id of the round for each readiness time (0 = not requested).
    mapping(uint256 => uint256) public requestOf;
    /// Readiness time plus one for each request id (0 = unknown request).
    mapping(uint256 => uint256) private timePlusOneOf;
    /// Output and fulfilment time of the round for each readiness time.
    mapping(uint256 => bytes32) private valueOf;
    mapping(uint256 => uint256) private roundTimeOf;

    constructor(IVrfCoordinatorV2Plus coordinator_, bytes32 keyHash_, uint256 subId_) {
        coordinator = coordinator_;
        keyHash = keyHash_;
        subId = subId_;
    }

    /// Request the round for readiness time `t`; anyone may call once `t` has passed.
    function request(uint256 t) external returns (uint256 requestId) {
        require(block.timestamp > t, "too early");
        require(requestOf[t] == 0, "already requested");
        requestId = coordinator.requestRandomWords(RandomWordsRequest({
            keyHash: keyHash,
            subId: subId,
            requestConfirmations: REQUEST_CONFIRMATIONS,
            callbackGasLimit: CALLBACK_GAS_LIMIT,
            numWords: 1,
            // VRFV2PlusClient.ExtraArgsV1({nativePayment: false})
            extraArgs: abi.encodeWithSelector(bytes4(keccak256("VRF ExtraArgsV1")), false)
        }));
        requestOf[t] = requestId;
        timePlusOneOf[requestId] = t + 1;
    }

    /// The coordinator's callback (the name VRF v2.5 consumers implement).
    function rawFulfillRandomWords(uint256 requestId, uint256[] calldata randomWords) external {
        require(msg.sender == address(coordinator), "only coordinator");
        uint256 timePlusOne = timePlusOneOf[requestId];
        require(timePlusOne != 0, "unknown request");
        uint256 t = timePlusOne - 1;
        require(roundTimeOf[t] == 0, "already fulfilled");
        // Zero means "not published" to a Vegas contract; a zero word (probability
        // 2^-256) is mapped to one.
        valueOf[t] = randomWords[0] == 0 ? bytes32(uint256(1)) : bytes32(randomWords[0]);
        roundTimeOf[t] = block.timestamp;
    }

    /// `IVegasBeacon`: the output of the round for time `t`, and its time; zero while unfulfilled.
    function randomnessAfter(uint256 t) external view returns (bytes32 value, uint256 roundTime) {
        return (valueOf[t], roundTimeOf[t]);
    }
}
