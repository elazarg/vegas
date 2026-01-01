# @version 0.4.0

enum Role:
    None
    A
    B

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
ACTION_A_0: constant(uint256) = 0
ACTION_B_1: constant(uint256) = 1
ACTION_A_3: constant(uint256) = 2
ACTION_A_4: constant(uint256) = 3
ACTION_B_5: constant(uint256) = 4
ACTION_B_6: constant(uint256) = 5
roles: HashMap[address, Role]
address_A: address
address_B: address
done_A: bool
done_B: bool
claimed_A: bool
claimed_B: bool
A_c: bool
done_A_c: bool
A_c_hidden: bytes32
done_A_c_hidden: bool
B_c: bool
done_B_c: bool
B_c_hidden: bytes32
done_B_c_hidden: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]
COMMIT_TAG: immutable(bytes32)

@deploy
def __init__():
    COMMIT_TAG = keccak256("VEGAS_COMMIT_V1")
    self.lastTs = block.timestamp

@external
@payable
def move_A_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.A][0], "already done"
    assert (not self.done_A), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.A
    self.address_A = msg.sender
    self.done_A = True
    self.actionDone[Role.A][0] = True
    self.actionTimestamp[Role.A][0] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_B_1():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.B][1], "already done"
    self._check_timestamp(Role.A)
    if not self.bailed[Role.A]:
        assert self.actionDone[Role.A][0], "dependency not satisfied"
    assert (not self.done_B), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.B
    self.address_B = msg.sender
    self.done_B = True
    self.actionDone[Role.B][1] = True
    self.actionTimestamp[Role.B][1] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_A_2(_hidden_c: bytes32):
    assert self.roles[msg.sender] == Role.A, "bad role"
    self._check_timestamp(Role.A)
    assert not self.bailed[Role.A], "you bailed"
    assert not self.actionDone[Role.A][3], "already done"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][1], "dependency not satisfied"
    self.A_c_hidden = _hidden_c
    self.done_A_c_hidden = True
    self.actionDone[Role.A][3] = True
    self.actionTimestamp[Role.A][3] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_B_4(_hidden_c: bytes32):
    assert self.roles[msg.sender] == Role.B, "bad role"
    self._check_timestamp(Role.B)
    assert not self.bailed[Role.B], "you bailed"
    assert not self.actionDone[Role.B][5], "already done"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][1], "dependency not satisfied"
    self.B_c_hidden = _hidden_c
    self.done_B_c_hidden = True
    self.actionDone[Role.B][5] = True
    self.actionTimestamp[Role.B][5] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_A_3(_c: bool, _salt: uint256):
    assert self.roles[msg.sender] == Role.A, "bad role"
    self._check_timestamp(Role.A)
    assert not self.bailed[Role.A], "you bailed"
    assert not self.actionDone[Role.A][4], "already done"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][1], "dependency not satisfied"
    self._check_timestamp(Role.A)
    if not self.bailed[Role.A]:
        assert self.actionDone[Role.A][3], "dependency not satisfied"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][5], "dependency not satisfied"
    self._checkReveal(self.A_c_hidden, Role.A, msg.sender, _abi_encode(_c, _salt))
    self.A_c = _c
    self.done_A_c = True
    self.actionDone[Role.A][4] = True
    self.actionTimestamp[Role.A][4] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_B_5(_c: bool, _salt: uint256):
    assert self.roles[msg.sender] == Role.B, "bad role"
    self._check_timestamp(Role.B)
    assert not self.bailed[Role.B], "you bailed"
    assert not self.actionDone[Role.B][6], "already done"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][1], "dependency not satisfied"
    self._check_timestamp(Role.A)
    if not self.bailed[Role.A]:
        assert self.actionDone[Role.A][3], "dependency not satisfied"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][5], "dependency not satisfied"
    self._checkReveal(self.B_c_hidden, Role.B, msg.sender, _abi_encode(_c, _salt))
    self.B_c = _c
    self.done_B_c = True
    self.actionDone[Role.B][6] = True
    self.actionTimestamp[Role.B][6] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_A():
    assert self.roles[msg.sender] == Role.A, "bad role"
    self._check_timestamp(Role.A)
    assert not self.bailed[Role.A], "you bailed"
    assert not self.actionDone[Role.A][5], "already done"
    self._check_timestamp(Role.A)
    if not self.bailed[Role.A]:
        assert self.actionDone[Role.A][4], "dependency not satisfied"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][6], "dependency not satisfied"
    assert (not self.claimed_A), "already claimed"
    self.claimed_A = True
    payout: int256 = 100 if (self.A_c and self.B_c) else 0 if (self.A_c and (not self.B_c)) else 200 if ((not self.A_c) and self.B_c) else 90 if (self.done_A_c and self.done_B_c) else 0 if (not self.done_A_c) else 200
    if payout > 0:
        success: bool = raw_call(self.address_A, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.A][5] = True
    self.actionTimestamp[Role.A][5] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_B():
    assert self.roles[msg.sender] == Role.B, "bad role"
    self._check_timestamp(Role.B)
    assert not self.bailed[Role.B], "you bailed"
    assert not self.actionDone[Role.B][7], "already done"
    self._check_timestamp(Role.A)
    if not self.bailed[Role.A]:
        assert self.actionDone[Role.A][4], "dependency not satisfied"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][6], "dependency not satisfied"
    assert (not self.claimed_B), "already claimed"
    self.claimed_B = True
    payout: int256 = 100 if (self.A_c and self.B_c) else 200 if (self.A_c and (not self.B_c)) else 0 if ((not self.A_c) and self.B_c) else 110 if (self.done_A_c and self.done_B_c) else 200 if (not self.done_A_c) else 0
    if payout > 0:
        success: bool = raw_call(self.address_B, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.B][7] = True
    self.actionTimestamp[Role.B][7] = block.timestamp
    self.lastTs = block.timestamp

@payable
@external
def __default__():
    assert False, "direct ETH not allowed"

@internal
def _check_timestamp(role: Role):
    if role == Role.None:
        return
    if block.timestamp > self.lastTs + TIMEOUT:
        self.bailed[role] = True
        self.lastTs = block.timestamp

@internal
@view
def _checkReveal(commitment: bytes32, role: Role, actor: address, payload: Bytes[256]):
    expected: bytes32 = keccak256(_abi_encode(COMMIT_TAG, self, role, actor, keccak256(payload)))
    assert expected == commitment, "bad reveal"

