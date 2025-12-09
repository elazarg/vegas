# @version 0.4.0

enum Role:
    None
    Q
    A

ACTION_Q_0: constant(uint256) = 0
ACTION_A_1: constant(uint256) = 1
FINAL_ACTION: constant(uint256) = 1

lastTs: uint256
actionDone: HashMap[uint256, bool]
actionTimestamp: HashMap[uint256, uint256]
role: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_Q: address
address_A: address
payoffs_distributed: bool
done_Q: bool
done_A: bool
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
@view
def _checkReveal(commitment: bytes32, preimage: Bytes[128]):
    assert keccak256(preimage) == commitment, "bad reveal"

@internal
def _markActionDone(actionId: uint256):
    self.actionDone[actionId] = True
    self.actionTimestamp[actionId] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_Q_0(_x: int256):
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[0], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Q, "already joined"
    self.role[msg.sender] = Role.Q
    self.address_Q = msg.sender
    assert msg.value == 50, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Q = True
    self.Q_x = _x
    self.done_Q_x = True
    self._markActionDone(0)

@external
def move_A_1(_p: int256, _q: int256):
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[1], "already done"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_A, "already joined"
    self.role[msg.sender] = Role.A
    self.address_A = msg.sender
    self.done_A = True
    assert (((_p * _q) == self.Q_x) and (_p != 1)) and (_q != 1), "where"
    self.A_p = _p
    self.done_A_p = True
    self.A_q = _q
    self.done_A_q = True
    self._markActionDone(1)

@external
def distributePayoffs():
    assert self.actionDone[FINAL_ACTION], "game not over"
    assert not self.payoffs_distributed, "payoffs already sent"
    self.payoffs_distributed = True
    self.balanceOf[self.address_Q] = 0
    self.balanceOf[self.address_A] = 50

@external
def withdraw():
    bal: int256 = self.balanceOf[msg.sender]
    assert bal > 0, "no funds"
    self.balanceOf[msg.sender] = 0
    ok: bool = raw_call(msg.sender, b"", value=convert(bal, uint256), max_outsize=0, gas=100000)
    assert ok, "ETH send failed"

@payable
@external
def __default__():
    assert False, "direct ETH not allowed"
