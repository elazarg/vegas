# @version 0.4.0

enum Role:
    None
    A

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
ACTION_A_0: constant(uint256) = 0
roles: HashMap[address, Role]
address_A: address
done_A: bool
claimed_A: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp

@external
@payable
def move_A_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.A][0], "already done"
    assert (not self.done_A), "already joined"
    assert (msg.value == 10), "bad stake"
    self.roles[msg.sender] = Role.A
    self.address_A = msg.sender
    self.done_A = True
    self.actionDone[Role.A][0] = True
    self.actionTimestamp[Role.A][0] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_A():
    assert self.roles[msg.sender] == Role.A, "bad role"
    self._check_timestamp(Role.A)
    assert not self.bailed[Role.A], "you bailed"
    assert not self.actionDone[Role.A][1], "already done"
    self._check_timestamp(Role.A)
    if not self.bailed[Role.A]:
        assert self.actionDone[Role.A][0], "dependency not satisfied"
    assert (not self.claimed_A), "already claimed"
    self.claimed_A = True
    payout: int256 = 10
    if payout > 0:
        success: bool = raw_call(self.address_A, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.A][1] = True
    self.actionTimestamp[Role.A][1] = block.timestamp
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

