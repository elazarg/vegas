# @version 0.4.0

enum Role:
    None
    Odd
    Even

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
ACTION_Odd_1: constant(uint256) = 0
ACTION_Odd_2: constant(uint256) = 1
ACTION_Even_3: constant(uint256) = 2
ACTION_Even_4: constant(uint256) = 3
roles: HashMap[address, Role]
address_Odd: address
address_Even: address
done_Odd: bool
done_Even: bool
claimed_Odd: bool
claimed_Even: bool
Odd_c: bool
done_Odd_c: bool
Odd_c_hidden: bytes32
done_Odd_c_hidden: bool
Even_c: bool
done_Even_c: bool
Even_c_hidden: bytes32
done_Even_c_hidden: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp

@external
@payable
def move_Odd_0(_hidden_c: bytes32):
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Odd][1], "already done"
    assert (not self.done_Odd), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.Odd
    self.address_Odd = msg.sender
    self.done_Odd = True
    self.Odd_c_hidden = _hidden_c
    self.done_Odd_c_hidden = True
    self.actionDone[Role.Odd][1] = True
    self.actionTimestamp[Role.Odd][1] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_Even_2(_hidden_c: bytes32):
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Even][3], "already done"
    assert (not self.done_Even), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.Even
    self.address_Even = msg.sender
    self.done_Even = True
    self.Even_c_hidden = _hidden_c
    self.done_Even_c_hidden = True
    self.actionDone[Role.Even][3] = True
    self.actionTimestamp[Role.Even][3] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Odd_1(_c: bool, _salt: uint256):
    assert self.roles[msg.sender] == Role.Odd, "bad role"
    self._check_timestamp(Role.Odd)
    assert not self.bailed[Role.Odd], "you bailed"
    assert not self.actionDone[Role.Odd][2], "already done"
    self._check_timestamp(Role.Odd)
    if not self.bailed[Role.Odd]:
        assert self.actionDone[Role.Odd][1], "dependency not satisfied"
    self._check_timestamp(Role.Even)
    if not self.bailed[Role.Even]:
        assert self.actionDone[Role.Even][3], "dependency not satisfied"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.Odd_c_hidden), "reveal failed for c"
    self.Odd_c = _c
    self.done_Odd_c = True
    self.actionDone[Role.Odd][2] = True
    self.actionTimestamp[Role.Odd][2] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Even_3(_c: bool, _salt: uint256):
    assert self.roles[msg.sender] == Role.Even, "bad role"
    self._check_timestamp(Role.Even)
    assert not self.bailed[Role.Even], "you bailed"
    assert not self.actionDone[Role.Even][4], "already done"
    self._check_timestamp(Role.Odd)
    if not self.bailed[Role.Odd]:
        assert self.actionDone[Role.Odd][1], "dependency not satisfied"
    self._check_timestamp(Role.Even)
    if not self.bailed[Role.Even]:
        assert self.actionDone[Role.Even][3], "dependency not satisfied"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.Even_c_hidden), "reveal failed for c"
    self.Even_c = _c
    self.done_Even_c = True
    self.actionDone[Role.Even][4] = True
    self.actionTimestamp[Role.Even][4] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Even():
    assert self.roles[msg.sender] == Role.Even, "bad role"
    self._check_timestamp(Role.Even)
    assert not self.bailed[Role.Even], "you bailed"
    assert not self.actionDone[Role.Even][4], "already done"
    self._check_timestamp(Role.Odd)
    if not self.bailed[Role.Odd]:
        assert self.actionDone[Role.Odd][2], "dependency not satisfied"
    self._check_timestamp(Role.Even)
    if not self.bailed[Role.Even]:
        assert self.actionDone[Role.Even][4], "dependency not satisfied"
    assert (not self.claimed_Even), "already claimed"
    self.claimed_Even = True
    payout: int256 = 126 if (self.Even_c == self.Odd_c) else 74 if (self.done_Even_c and self.done_Odd_c) else 20 if ((not self.done_Even_c) and self.done_Odd_c) else 180 if (self.done_Even_c and (not self.done_Odd_c)) else 100
    if payout > 0:
        success: bool = raw_call(self.address_Even, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.Even][4] = True
    self.actionTimestamp[Role.Even][4] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Odd():
    assert self.roles[msg.sender] == Role.Odd, "bad role"
    self._check_timestamp(Role.Odd)
    assert not self.bailed[Role.Odd], "you bailed"
    assert not self.actionDone[Role.Odd][5], "already done"
    self._check_timestamp(Role.Odd)
    if not self.bailed[Role.Odd]:
        assert self.actionDone[Role.Odd][2], "dependency not satisfied"
    self._check_timestamp(Role.Even)
    if not self.bailed[Role.Even]:
        assert self.actionDone[Role.Even][4], "dependency not satisfied"
    assert (not self.claimed_Odd), "already claimed"
    self.claimed_Odd = True
    payout: int256 = 74 if (self.Even_c == self.Odd_c) else 126 if (self.done_Even_c and self.done_Odd_c) else 180 if ((not self.done_Even_c) and self.done_Odd_c) else 20 if (self.done_Even_c and (not self.done_Odd_c)) else 100
    if payout > 0:
        success: bool = raw_call(self.address_Odd, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.Odd][5] = True
    self.actionTimestamp[Role.Odd][5] = block.timestamp
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

