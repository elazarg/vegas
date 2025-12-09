# @version 0.4.0

enum Role:
    None
    A
    B

ACTION_A_0: constant(uint256) = 0
ACTION_B_1: constant(uint256) = 1
ACTION_A_2: constant(uint256) = 2
ACTION_B_3: constant(uint256) = 3
ACTION_A_4: constant(uint256) = 4
FINAL_ACTION: constant(uint256) = 4

lastTs: uint256
actionDone: HashMap[uint256, bool]
actionTimestamp: HashMap[uint256, uint256]
role: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_A: address
address_B: address
payoffs_distributed: bool
done_A: bool
done_B: bool
A_hidden_c: bytes32
done_A_hidden_c: bool
A_c: bool
done_A_c: bool
B_c: bool
done_B_c: bool

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
def move_A_0():
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[0], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_A, "already joined"
    self.role[msg.sender] = Role.A
    self.address_A = msg.sender
    assert msg.value == 1, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_A = True
    self._markActionDone(0)

@external
@payable
def move_B_1():
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[1], "already done"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_B, "already joined"
    self.role[msg.sender] = Role.B
    self.address_B = msg.sender
    assert msg.value == 1, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_B = True
    self._markActionDone(1)

@external
def move_A_2(_hidden_c: bytes32):
    assert self.role[msg.sender] == Role.A, "bad role"
    assert not self.actionDone[2], "already done"
    assert self.actionDone[1], "dependency not satisfied"
    self.A_hidden_c = _hidden_c
    self.done_A_hidden_c = True
    self._markActionDone(2)

@external
def move_B_3(_c: bool):
    assert self.role[msg.sender] == Role.B, "bad role"
    assert not self.actionDone[3], "already done"
    assert self.actionDone[2], "dependency not satisfied"
    self.B_c = _c
    self.done_B_c = True
    self._markActionDone(3)

@external
def move_A_4(_c: bool, salt: uint256):
    assert self.role[msg.sender] == Role.A, "bad role"
    assert not self.actionDone[4], "already done"
    assert self.actionDone[3], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    self._checkReveal(self.A_hidden_c, abi_encode(_c, salt, output_type=Bytes[128]))
    self.A_c = _c
    self.done_A_c = True
    self._markActionDone(4)

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
    ok: bool = raw_call(msg.sender, b"", value=convert(bal, uint256), max_outsize=0, gas=100000)
    assert ok, "ETH send failed"

@payable
@external
def __default__():
    assert False, "direct ETH not allowed"
