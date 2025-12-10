# @version 0.4.0

enum Role:
    None
    Q
    A

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[uint256, uint256]
ACTION_Q_0: constant(uint256) = 0
ACTION_A_1: constant(uint256) = 1
FINAL_ACTION: constant(uint256) = 1
roles: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_Q: address
address_A: address
done_Q: bool
done_A: bool
payoffs_distributed: bool
Q_x: int256
done_Q_x: bool
A_p: int256
done_A_p: bool
A_q: int256
done_A_q: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp
    

@external
@payable
def move_Q_0(_x: int256):
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Q][0], "already done"
    assert (not self.done_Q), "already joined"
    assert (msg.value == 50), "bad stake"
    self.balanceOf[msg.sender] = msg.value
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
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.A][1], "already done"
    self._check_timestamp(Role.Q)
    if not self.bailed[Role.Q]:
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
    success: bool = raw_call(msg.sender, b"", value=convert(bal, uint256), revert_on_failure=False)
    assert success, "ETH send failed"
    

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
    
    

