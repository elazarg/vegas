# @version 0.4.0

enum Role:
    None
    Host
    Guest

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
ACTION_Host_0: constant(uint256) = 0
ACTION_Guest_1: constant(uint256) = 1
ACTION_Host_2: constant(uint256) = 2
ACTION_Guest_3: constant(uint256) = 3
ACTION_Host_4: constant(uint256) = 4
ACTION_Guest_5: constant(uint256) = 5
ACTION_Host_6: constant(uint256) = 6
roles: HashMap[address, Role]
address_Host: address
address_Guest: address
done_Host: bool
done_Guest: bool
claimed_Host: bool
claimed_Guest: bool
Host_car: int256
done_Host_car: bool
Host_car_hidden: bytes32
done_Host_car_hidden: bool
Guest_d: int256
done_Guest_d: bool
Host_goat: int256
done_Host_goat: bool
Guest_switch: bool
done_Guest_switch: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]
COMMIT_TAG: immutable(bytes32)

@deploy
def __init__():
    COMMIT_TAG = keccak256("VEGAS_COMMIT_V1")
    self.lastTs = block.timestamp

@external
@payable
def move_Host_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Host][0], "already done"
    assert (not self.done_Host), "already joined"
    assert (msg.value == 20), "bad stake"
    self.roles[msg.sender] = Role.Host
    self.address_Host = msg.sender
    self.done_Host = True
    self.actionDone[Role.Host][0] = True
    self.actionTimestamp[Role.Host][0] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_Guest_1():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Guest][1], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][0], "dependency not satisfied"
    assert (not self.done_Guest), "already joined"
    assert (msg.value == 20), "bad stake"
    self.roles[msg.sender] = Role.Guest
    self.address_Guest = msg.sender
    self.done_Guest = True
    self.actionDone[Role.Guest][1] = True
    self.actionTimestamp[Role.Guest][1] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Host_2(_hidden_car: bytes32):
    assert self.roles[msg.sender] == Role.Host, "bad role"
    self._check_timestamp(Role.Host)
    assert not self.bailed[Role.Host], "you bailed"
    assert not self.actionDone[Role.Host][2], "already done"
    self._check_timestamp(Role.Guest)
    if not self.bailed[Role.Guest]:
        assert self.actionDone[Role.Guest][1], "dependency not satisfied"
    self.Host_car_hidden = _hidden_car
    self.done_Host_car_hidden = True
    self.actionDone[Role.Host][2] = True
    self.actionTimestamp[Role.Host][2] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Guest_3(_d: int256):
    assert self.roles[msg.sender] == Role.Guest, "bad role"
    self._check_timestamp(Role.Guest)
    assert not self.bailed[Role.Guest], "you bailed"
    assert not self.actionDone[Role.Guest][3], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][2], "dependency not satisfied"
    assert (((_d == 0) or (_d == 1)) or (_d == 2)), "domain"
    self.Guest_d = _d
    self.done_Guest_d = True
    self.actionDone[Role.Guest][3] = True
    self.actionTimestamp[Role.Guest][3] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Host_4(_goat: int256):
    assert self.roles[msg.sender] == Role.Host, "bad role"
    self._check_timestamp(Role.Host)
    assert not self.bailed[Role.Host], "you bailed"
    assert not self.actionDone[Role.Host][4], "already done"
    self._check_timestamp(Role.Guest)
    if not self.bailed[Role.Guest]:
        assert self.actionDone[Role.Guest][3], "dependency not satisfied"
    assert (((_goat == 0) or (_goat == 1)) or (_goat == 2)), "domain"
    assert (_goat != self.Guest_d), "domain"
    self.Host_goat = _goat
    self.done_Host_goat = True
    self.actionDone[Role.Host][4] = True
    self.actionTimestamp[Role.Host][4] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Guest_5(_switch: bool):
    assert self.roles[msg.sender] == Role.Guest, "bad role"
    self._check_timestamp(Role.Guest)
    assert not self.bailed[Role.Guest], "you bailed"
    assert not self.actionDone[Role.Guest][5], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][4], "dependency not satisfied"
    self.Guest_switch = _switch
    self.done_Guest_switch = True
    self.actionDone[Role.Guest][5] = True
    self.actionTimestamp[Role.Guest][5] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Host_6(_car: int256, _salt: uint256):
    assert self.roles[msg.sender] == Role.Host, "bad role"
    self._check_timestamp(Role.Host)
    assert not self.bailed[Role.Host], "you bailed"
    assert not self.actionDone[Role.Host][6], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][2], "dependency not satisfied"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][4], "dependency not satisfied"
    self._check_timestamp(Role.Guest)
    if not self.bailed[Role.Guest]:
        assert self.actionDone[Role.Guest][5], "dependency not satisfied"
    assert (((_car == 0) or (_car == 1)) or (_car == 2)), "domain"
    assert (self.Host_goat != _car), "domain"
    self._checkReveal(self.Host_car_hidden, Role.Host, msg.sender, _abi_encode(_car, _salt))
    self.Host_car = _car
    self.done_Host_car = True
    self.actionDone[Role.Host][6] = True
    self.actionTimestamp[Role.Host][6] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Host():
    assert self.roles[msg.sender] == Role.Host, "bad role"
    self._check_timestamp(Role.Host)
    assert not self.bailed[Role.Host], "you bailed"
    assert not self.actionDone[Role.Host][7], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][6], "dependency not satisfied"
    assert (not self.claimed_Host), "already claimed"
    self.claimed_Host = True
    payout: int256 = (20 + ((0 if self.done_Host_car else 20 + 0 if True else 20) / (1 if self.done_Host_car else 0 + 1 if True else 0) if ((1 if self.done_Host_car else 0 + 1 if True else 0) > 0) else 1)) if self.done_Host_car else 0 if (not self.done_Host_car) else (20 + ((0 if self.done_Host_car else 20 + 0 if self.done_Guest_d else 20) / (1 if self.done_Host_car else 0 + 1 if self.done_Guest_d else 0) if ((1 if self.done_Host_car else 0 + 1 if self.done_Guest_d else 0) > 0) else 1)) if self.done_Host_car else 0 if (not self.done_Guest_d) else (20 + ((0 if (self.done_Host_car and self.done_Host_goat) else 20 + 0 if self.done_Guest_d else 20) / (1 if (self.done_Host_car and self.done_Host_goat) else 0 + 1 if self.done_Guest_d else 0) if ((1 if (self.done_Host_car and self.done_Host_goat) else 0 + 1 if self.done_Guest_d else 0) > 0) else 1)) if (self.done_Host_car and self.done_Host_goat) else 0 if (not self.done_Host_goat) else (20 + ((0 if (self.done_Host_car and self.done_Host_goat) else 20 + 0 if (self.done_Guest_d and self.done_Guest_switch) else 20) / (1 if (self.done_Host_car and self.done_Host_goat) else 0 + 1 if (self.done_Guest_d and self.done_Guest_switch) else 0) if ((1 if (self.done_Host_car and self.done_Host_goat) else 0 + 1 if (self.done_Guest_d and self.done_Guest_switch) else 0) > 0) else 1)) if (self.done_Host_car and self.done_Host_goat) else 0 if (not self.done_Guest_switch) else 0 if ((self.Guest_d != self.Host_car) == self.Guest_switch) else 40
    if payout > 0:
        success: bool = raw_call(self.address_Host, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.Host][7] = True
    self.actionTimestamp[Role.Host][7] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Guest():
    assert self.roles[msg.sender] == Role.Guest, "bad role"
    self._check_timestamp(Role.Guest)
    assert not self.bailed[Role.Guest], "you bailed"
    assert not self.actionDone[Role.Guest][6], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][6], "dependency not satisfied"
    assert (not self.claimed_Guest), "already claimed"
    self.claimed_Guest = True
    payout: int256 = (20 + ((0 if self.done_Host_car else 20 + 0 if True else 20) / (1 if self.done_Host_car else 0 + 1 if True else 0) if ((1 if self.done_Host_car else 0 + 1 if True else 0) > 0) else 1)) if True else 0 if (not self.done_Host_car) else (20 + ((0 if self.done_Host_car else 20 + 0 if self.done_Guest_d else 20) / (1 if self.done_Host_car else 0 + 1 if self.done_Guest_d else 0) if ((1 if self.done_Host_car else 0 + 1 if self.done_Guest_d else 0) > 0) else 1)) if self.done_Guest_d else 0 if (not self.done_Guest_d) else (20 + ((0 if (self.done_Host_car and self.done_Host_goat) else 20 + 0 if self.done_Guest_d else 20) / (1 if (self.done_Host_car and self.done_Host_goat) else 0 + 1 if self.done_Guest_d else 0) if ((1 if (self.done_Host_car and self.done_Host_goat) else 0 + 1 if self.done_Guest_d else 0) > 0) else 1)) if self.done_Guest_d else 0 if (not self.done_Host_goat) else (20 + ((0 if (self.done_Host_car and self.done_Host_goat) else 20 + 0 if (self.done_Guest_d and self.done_Guest_switch) else 20) / (1 if (self.done_Host_car and self.done_Host_goat) else 0 + 1 if (self.done_Guest_d and self.done_Guest_switch) else 0) if ((1 if (self.done_Host_car and self.done_Host_goat) else 0 + 1 if (self.done_Guest_d and self.done_Guest_switch) else 0) > 0) else 1)) if (self.done_Guest_d and self.done_Guest_switch) else 0 if (not self.done_Guest_switch) else 40 if ((self.Guest_d != self.Host_car) == self.Guest_switch) else 0
    if payout > 0:
        success: bool = raw_call(self.address_Guest, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.Guest][6] = True
    self.actionTimestamp[Role.Guest][6] = block.timestamp
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

