# @version 0.4.0

enum Role:
    None
    Q
    A

actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
lastTs: uint256
TIMEOUT: constant(uint256) = 86400
bailed: HashMap[Role, bool]
ACTION_Q_0: constant(uint256) = 0
ACTION_A_1: constant(uint256) = 1
roles: HashMap[address, Role]
address_Q: address
address_A: address
done_Q: bool
done_A: bool
claimed_Q: bool
claimed_A: bool
Q_x: int256
done_Q_x: bool
A_p: int256
done_A_p: bool
A_q: int256
done_A_q: bool

@external
def __init__():
    self.lastTs = block.timestamp

@internal
def _check_timestamp(role: Role):
    if (_role == Role.None):
        return
    if (block.timestamp > (self.lastTs + _TIMEOUT)):
        self.bailed[_role] = True
        self.lastTs = block.timestamp


@external
@payable
def move_Q_0(_x: int256):
    assert (self.roles[msg.sender] == Role.Q), "bad role"
    _check_timestamp(Role.Q)
    assert (not self.bailed[Role.Q]), "you bailed"
    assert (not self.actionDone[Role.Q][0]), "already done"
    assert (not self.done_Q), "already joined"
    assert (msg.value == 50), "bad stake"
    self.roles[msg.sender] = Role.Q
    self.address_Q = msg.sender
    self.done_Q = True
    self.Q_x = _x
    self.done_Q_x = True
    self.actionDone[Role.Q][0] = True
    self.actionTimestamp[Role.Q][0] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_A_1(_p: int256, _q: int256):
    assert (self.roles[msg.sender] == Role.A), "bad role"
    _check_timestamp(Role.A)
    assert (not self.bailed[Role.A]), "you bailed"
    assert (not self.actionDone[Role.A][1]), "already done"
    _check_timestamp(Role.Q)
    if (not self.bailed[Role.Q]):
        assert self.actionDone[Role.Q][0], "dependency not satisfied"
    assert ((((_p * _q) == self.Q_x) and (_p != 1)) and (_q != 1)), "domain"
    assert (not self.done_A), "already joined"
    self.roles[msg.sender] = Role.A
    self.address_A = msg.sender
    self.done_A = True
    self.A_p = _p
    self.done_A_p = True
    self.A_q = _q
    self.done_A_q = True
    self.actionDone[Role.A][1] = True
    self.actionTimestamp[Role.A][1] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Q():
    assert (not self.claimed_Q), "already claimed"
    self.claimed_Q = True
    payout: int256 = 0
    if payout > 0:
        success: bool = raw_call(self.address_Q, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_A():
    assert (not self.claimed_A), "already claimed"
    self.claimed_A = True
    payout: int256 = 100
    if payout > 0:
        success: bool = raw_call(self.address_A, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@payable
@external
def __default__():
    assert False, "direct ETH not allowed"

