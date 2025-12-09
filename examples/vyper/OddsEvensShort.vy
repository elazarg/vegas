# @version 0.4.0

enum Role:
    None
    Odd
    Even

ACTION_Odd_0: constant(uint256) = 0
ACTION_Odd_1: constant(uint256) = 1
ACTION_Even_2: constant(uint256) = 2
ACTION_Even_3: constant(uint256) = 3
FINAL_ACTION: constant(uint256) = 3

lastTs: uint256
actionDone: HashMap[uint256, bool]
actionTimestamp: HashMap[uint256, uint256]
role: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_Odd: address
address_Even: address
payoffs_distributed: bool
done_Odd: bool
done_Even: bool
Odd_hidden_c: bytes32
done_Odd_hidden_c: bool
Odd_c: bool
done_Odd_c: bool
Even_hidden_c: bytes32
done_Even_hidden_c: bool
Even_c: bool
done_Even_c: bool

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
def move_Odd_0(_hidden_c: bytes32):
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[0], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Odd, "already joined"
    self.role[msg.sender] = Role.Odd
    self.address_Odd = msg.sender
    assert msg.value == 100, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Odd = True
    self.Odd_hidden_c = _hidden_c
    self.done_Odd_hidden_c = True
    self._markActionDone(0)

@external
@payable
def move_Even_2(_hidden_c: bytes32):
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[2], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Even, "already joined"
    self.role[msg.sender] = Role.Even
    self.address_Even = msg.sender
    assert msg.value == 100, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Even = True
    self.Even_hidden_c = _hidden_c
    self.done_Even_hidden_c = True
    self._markActionDone(2)

@external
def move_Odd_1(_c: bool, salt: uint256):
    assert self.role[msg.sender] == Role.Odd, "bad role"
    assert not self.actionDone[1], "already done"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    self._checkReveal(self.Odd_hidden_c, abi_encode(_c, salt, output_type=Bytes[128]))
    self.Odd_c = _c
    self.done_Odd_c = True
    self._markActionDone(1)

@external
def move_Even_3(_c: bool, salt: uint256):
    assert self.role[msg.sender] == Role.Even, "bad role"
    assert not self.actionDone[3], "already done"
    assert self.actionDone[2], "dependency not satisfied"
    assert self.actionDone[0], "dependency not satisfied"
    self._checkReveal(self.Even_hidden_c, abi_encode(_c, salt, output_type=Bytes[128]))
    self.Even_c = _c
    self.done_Even_c = True
    self._markActionDone(3)

@external
def distributePayoffs():
    assert self.actionDone[FINAL_ACTION], "game not over"
    assert not self.payoffs_distributed, "payoffs already sent"
    self.payoffs_distributed = True
    self.balanceOf[self.address_Odd] = (-10) if (self.Even_c == self.Odd_c) else 10 if (self.done_Even_c and self.done_Odd_c) else 10 if ((not self.done_Even_c) and self.done_Odd_c) else (-100)
    self.balanceOf[self.address_Even] = 10 if (self.Even_c == self.Odd_c) else (-10) if (self.done_Even_c and self.done_Odd_c) else (-100) if ((not self.done_Even_c) and self.done_Odd_c) else (-100)

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
