# @version 0.4.0

enum Role:
    None
    X
    O

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
ACTION_X_0: constant(uint256) = 0
ACTION_O_1: constant(uint256) = 1
ACTION_X_2: constant(uint256) = 2
ACTION_O_3: constant(uint256) = 3
ACTION_X_4: constant(uint256) = 4
ACTION_O_5: constant(uint256) = 5
ACTION_X_6: constant(uint256) = 6
ACTION_O_7: constant(uint256) = 7
ACTION_X_8: constant(uint256) = 8
ACTION_O_9: constant(uint256) = 9
roles: HashMap[address, Role]
address_X: address
address_O: address
done_X: bool
done_O: bool
claimed_X: bool
claimed_O: bool
X_c1: int256
done_X_c1: bool
O_c1: int256
done_O_c1: bool
X_c2: int256
done_X_c2: bool
O_c2: int256
done_O_c2: bool
X_c3: int256
done_X_c3: bool
O_c3: int256
done_O_c3: bool
X_c4: int256
done_X_c4: bool
O_c4: int256
done_O_c4: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp

@external
@payable
def move_X_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.X][0], "already done"
    assert (not self.done_X), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.X
    self.address_X = msg.sender
    self.done_X = True
    self.actionDone[Role.X][0] = True
    self.actionTimestamp[Role.X][0] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_O_1():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.O][1], "already done"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][0], "dependency not satisfied"
    assert (not self.done_O), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.O
    self.address_O = msg.sender
    self.done_O = True
    self.actionDone[Role.O][1] = True
    self.actionTimestamp[Role.O][1] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_X_2(_c1: int256):
    assert self.roles[msg.sender] == Role.X, "bad role"
    self._check_timestamp(Role.X)
    assert not self.bailed[Role.X], "you bailed"
    assert not self.actionDone[Role.X][2], "already done"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][1], "dependency not satisfied"
    assert (((_c1 == 0) or (_c1 == 1)) or (_c1 == 4)), "domain"
    self.X_c1 = _c1
    self.done_X_c1 = True
    self.actionDone[Role.X][2] = True
    self.actionTimestamp[Role.X][2] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_O_3(_c1: int256):
    assert self.roles[msg.sender] == Role.O, "bad role"
    self._check_timestamp(Role.O)
    assert not self.bailed[Role.O], "you bailed"
    assert not self.actionDone[Role.O][3], "already done"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][2], "dependency not satisfied"
    assert (((((_c1 == 1) or (_c1 == 3)) or (_c1 == 4)) or (_c1 == 5)) or (_c1 == 9)), "domain"
    assert (self.X_c1 != _c1), "domain"
    self.O_c1 = _c1
    self.done_O_c1 = True
    self.actionDone[Role.O][3] = True
    self.actionTimestamp[Role.O][3] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_X_4(_c2: int256):
    assert self.roles[msg.sender] == Role.X, "bad role"
    self._check_timestamp(Role.X)
    assert not self.bailed[Role.X], "you bailed"
    assert not self.actionDone[Role.X][4], "already done"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][2], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][3], "dependency not satisfied"
    assert (((((((((_c2 == 0) or (_c2 == 1)) or (_c2 == 2)) or (_c2 == 3)) or (_c2 == 4)) or (_c2 == 5)) or (_c2 == 6)) or (_c2 == 7)) or (_c2 == 8)), "domain"
    assert (((self.X_c1 != self.O_c1) and (self.X_c1 != _c2)) and (self.O_c1 != _c2)), "domain"
    self.X_c2 = _c2
    self.done_X_c2 = True
    self.actionDone[Role.X][4] = True
    self.actionTimestamp[Role.X][4] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_O_5(_c2: int256):
    assert self.roles[msg.sender] == Role.O, "bad role"
    self._check_timestamp(Role.O)
    assert not self.bailed[Role.O], "you bailed"
    assert not self.actionDone[Role.O][5], "already done"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][2], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][3], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][4], "dependency not satisfied"
    assert (((((((((_c2 == 0) or (_c2 == 1)) or (_c2 == 2)) or (_c2 == 3)) or (_c2 == 4)) or (_c2 == 5)) or (_c2 == 6)) or (_c2 == 7)) or (_c2 == 8)), "domain"
    assert ((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != _c2)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != _c2)) and (self.X_c2 != _c2)), "domain"
    self.O_c2 = _c2
    self.done_O_c2 = True
    self.actionDone[Role.O][5] = True
    self.actionTimestamp[Role.O][5] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_X_6(_c3: int256):
    assert self.roles[msg.sender] == Role.X, "bad role"
    self._check_timestamp(Role.X)
    assert not self.bailed[Role.X], "you bailed"
    assert not self.actionDone[Role.X][6], "already done"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][2], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][3], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][4], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][5], "dependency not satisfied"
    assert (((((((((_c3 == 0) or (_c3 == 1)) or (_c3 == 2)) or (_c3 == 3)) or (_c3 == 4)) or (_c3 == 5)) or (_c3 == 6)) or (_c3 == 7)) or (_c3 == 8)), "domain"
    assert ((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != _c3)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != _c3)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != _c3)) and (self.O_c2 != _c3)), "domain"
    self.X_c3 = _c3
    self.done_X_c3 = True
    self.actionDone[Role.X][6] = True
    self.actionTimestamp[Role.X][6] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_O_7(_c3: int256):
    assert self.roles[msg.sender] == Role.O, "bad role"
    self._check_timestamp(Role.O)
    assert not self.bailed[Role.O], "you bailed"
    assert not self.actionDone[Role.O][7], "already done"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][2], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][3], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][4], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][5], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][6], "dependency not satisfied"
    assert (((((((((_c3 == 0) or (_c3 == 1)) or (_c3 == 2)) or (_c3 == 3)) or (_c3 == 4)) or (_c3 == 5)) or (_c3 == 6)) or (_c3 == 7)) or (_c3 == 8)), "domain"
    assert (((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != _c3)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != _c3)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != _c3)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != _c3)) and (self.X_c3 != _c3)), "domain"
    self.O_c3 = _c3
    self.done_O_c3 = True
    self.actionDone[Role.O][7] = True
    self.actionTimestamp[Role.O][7] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_X_8(_c4: int256):
    assert self.roles[msg.sender] == Role.X, "bad role"
    self._check_timestamp(Role.X)
    assert not self.bailed[Role.X], "you bailed"
    assert not self.actionDone[Role.X][8], "already done"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][2], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][3], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][4], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][5], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][6], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][7], "dependency not satisfied"
    assert (((((((((_c4 == 0) or (_c4 == 1)) or (_c4 == 2)) or (_c4 == 3)) or (_c4 == 4)) or (_c4 == 5)) or (_c4 == 6)) or (_c4 == 7)) or (_c4 == 8)), "domain"
    assert (((((((((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != self.O_c3)) and (self.X_c1 != _c4)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != self.O_c3)) and (self.O_c1 != _c4)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != self.O_c3)) and (self.X_c2 != _c4)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != self.O_c3)) and (self.O_c2 != _c4)) and (self.X_c3 != self.O_c3)) and (self.X_c3 != _c4)) and (self.O_c3 != _c4)), "domain"
    self.X_c4 = _c4
    self.done_X_c4 = True
    self.actionDone[Role.X][8] = True
    self.actionTimestamp[Role.X][8] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_O_9(_c4: int256):
    assert self.roles[msg.sender] == Role.O, "bad role"
    self._check_timestamp(Role.O)
    assert not self.bailed[Role.O], "you bailed"
    assert not self.actionDone[Role.O][9], "already done"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][2], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][3], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][4], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][5], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][6], "dependency not satisfied"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][7], "dependency not satisfied"
    self._check_timestamp(Role.X)
    if not self.bailed[Role.X]:
        assert self.actionDone[Role.X][8], "dependency not satisfied"
    assert (((((((((_c4 == 0) or (_c4 == 1)) or (_c4 == 2)) or (_c4 == 3)) or (_c4 == 4)) or (_c4 == 5)) or (_c4 == 6)) or (_c4 == 7)) or (_c4 == 8)), "domain"
    assert ((((((((((((((((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != self.O_c3)) and (self.X_c1 != self.X_c4)) and (self.X_c1 != _c4)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != self.O_c3)) and (self.O_c1 != self.X_c4)) and (self.O_c1 != _c4)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != self.O_c3)) and (self.X_c2 != self.X_c4)) and (self.X_c2 != _c4)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != self.O_c3)) and (self.O_c2 != self.X_c4)) and (self.O_c2 != _c4)) and (self.X_c3 != self.O_c3)) and (self.X_c3 != self.X_c4)) and (self.X_c3 != _c4)) and (self.O_c3 != self.X_c4)) and (self.O_c3 != _c4)) and (self.X_c4 != _c4)), "domain"
    self.O_c4 = _c4
    self.done_O_c4 = True
    self.actionDone[Role.O][9] = True
    self.actionTimestamp[Role.O][9] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_X():
    assert self.roles[msg.sender] == Role.X, "bad role"
    self._check_timestamp(Role.X)
    assert not self.bailed[Role.X], "you bailed"
    assert not self.actionDone[Role.X][10], "already done"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][9], "dependency not satisfied"
    assert (not self.claimed_X), "already claimed"
    self.claimed_X = True
    payout: int256 = 100
    if payout > 0:
        success: bool = raw_call(self.address_X, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.X][10] = True
    self.actionTimestamp[Role.X][10] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_O():
    assert self.roles[msg.sender] == Role.O, "bad role"
    self._check_timestamp(Role.O)
    assert not self.bailed[Role.O], "you bailed"
    assert not self.actionDone[Role.O][11], "already done"
    self._check_timestamp(Role.O)
    if not self.bailed[Role.O]:
        assert self.actionDone[Role.O][9], "dependency not satisfied"
    assert (not self.claimed_O), "already claimed"
    self.claimed_O = True
    payout: int256 = 100
    if payout > 0:
        success: bool = raw_call(self.address_O, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.O][11] = True
    self.actionTimestamp[Role.O][11] = block.timestamp
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

