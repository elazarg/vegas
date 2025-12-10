# @version 0.4.0

enum Role:
    None
    A
    B

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[uint256, uint256]
ACTION_A_0: constant(uint256) = 0
ACTION_B_1: constant(uint256) = 1
ACTION_A_2: constant(uint256) = 2
ACTION_B_3: constant(uint256) = 3
ACTION_A_4: constant(uint256) = 4
FINAL_ACTION: constant(uint256) = 4
roles: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_A: address
address_B: address
done_A: bool
done_B: bool
payoffs_distributed: bool
A_c: bool
done_A_c: bool
A_c_hidden: bytes32
done_A_c_hidden: bool
B_c: bool
done_B_c: bool
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
    assert (msg.value == 1), "bad stake"
    self.balanceOf[msg.sender] = msg.value
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
    assert (msg.value == 1), "bad stake"
    self.balanceOf[msg.sender] = msg.value
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
    assert not self.actionDone[Role.A][2], "already done"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][1], "dependency not satisfied"
    self.A_c_hidden = _hidden_c
    self.done_A_c_hidden = True
    self.actionDone[Role.A][2] = True
    self.actionTimestamp[Role.A][2] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def move_B_3(_c: bool):
    assert self.roles[msg.sender] == Role.B, "bad role"
    self._check_timestamp(Role.B)
    assert not self.bailed[Role.B], "you bailed"
    assert not self.actionDone[Role.B][3], "already done"
    self._check_timestamp(Role.A)
    if not self.bailed[Role.A]:
        assert self.actionDone[Role.A][2], "dependency not satisfied"
    self.B_c = _c
    self.done_B_c = True
    self.actionDone[Role.B][3] = True
    self.actionTimestamp[Role.B][3] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def move_A_4(_c: bool, _salt: uint256):
    assert self.roles[msg.sender] == Role.A, "bad role"
    self._check_timestamp(Role.A)
    assert not self.bailed[Role.A], "you bailed"
    assert not self.actionDone[Role.A][4], "already done"
    self._check_timestamp(Role.A)
    if not self.bailed[Role.A]:
        assert self.actionDone[Role.A][2], "dependency not satisfied"
    self._check_timestamp(Role.B)
    if not self.bailed[Role.B]:
        assert self.actionDone[Role.B][3], "dependency not satisfied"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.A_c_hidden), "reveal failed for c"
    self.A_c = _c
    self.done_A_c = True
    self.actionDone[Role.A][4] = True
    self.actionTimestamp[Role.A][4] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def distributePayoffs():
    assert self.actionDone[FINAL_ACTION], "game not over"
    assert not self.payoffs_distributed, "payoffs already sent"
    self.payoffs_distributed = True
    self.balanceOf[self.address_A] = 1 if ((self.A_c != self.B_c) or (not self.done_B_c)) else (-1)
    self.balanceOf[self.address_B] = 1 if ((self.A_c == self.B_c) or (not self.done_A_c)) else (-1)
    

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
    
    

