# @version 0.4.0

enum Role:
    None
    X
    O

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
FINAL_ACTION: constant(uint256) = 9

lastTs: uint256
actionDone: HashMap[uint256, bool]
actionTimestamp: HashMap[uint256, uint256]
role: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_X: address
address_O: address
payoffs_distributed: bool
done_X: bool
done_O: bool
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
def move_X_0():
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[0], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_X, "already joined"
    self.role[msg.sender] = Role.X
    self.address_X = msg.sender
    assert msg.value == 100, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_X = True
    self._markActionDone(0)

@external
@payable
def move_O_1():
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[1], "already done"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_O, "already joined"
    self.role[msg.sender] = Role.O
    self.address_O = msg.sender
    assert msg.value == 100, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_O = True
    self._markActionDone(1)

@external
def move_X_2(_c1: int256):
    assert self.role[msg.sender] == Role.X, "bad role"
    assert not self.actionDone[2], "already done"
    assert self.actionDone[1], "dependency not satisfied"
    assert ((_c1 == 0) or (_c1 == 1)) or (_c1 == 4), "domain"
    self.X_c1 = _c1
    self.done_X_c1 = True
    self._markActionDone(2)

@external
def move_O_3(_c1: int256):
    assert self.role[msg.sender] == Role.O, "bad role"
    assert not self.actionDone[3], "already done"
    assert self.actionDone[2], "dependency not satisfied"
    assert ((((_c1 == 1) or (_c1 == 3)) or (_c1 == 4)) or (_c1 == 5)) or (_c1 == 9), "domain"
    assert self.X_c1 != _c1, "where"
    self.O_c1 = _c1
    self.done_O_c1 = True
    self._markActionDone(3)

@external
def move_X_4(_c2: int256):
    assert self.role[msg.sender] == Role.X, "bad role"
    assert not self.actionDone[4], "already done"
    assert self.actionDone[3], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    assert ((((((((_c2 == 0) or (_c2 == 1)) or (_c2 == 2)) or (_c2 == 3)) or (_c2 == 4)) or (_c2 == 5)) or (_c2 == 6)) or (_c2 == 7)) or (_c2 == 8), "domain"
    assert ((self.X_c1 != self.O_c1) and (self.X_c1 != _c2)) and (self.O_c1 != _c2), "where"
    self.X_c2 = _c2
    self.done_X_c2 = True
    self._markActionDone(4)

@external
def move_O_5(_c2: int256):
    assert self.role[msg.sender] == Role.O, "bad role"
    assert not self.actionDone[5], "already done"
    assert self.actionDone[4], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    assert self.actionDone[3], "dependency not satisfied"
    assert ((((((((_c2 == 0) or (_c2 == 1)) or (_c2 == 2)) or (_c2 == 3)) or (_c2 == 4)) or (_c2 == 5)) or (_c2 == 6)) or (_c2 == 7)) or (_c2 == 8), "domain"
    assert (((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != _c2)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != _c2)) and (self.X_c2 != _c2), "where"
    self.O_c2 = _c2
    self.done_O_c2 = True
    self._markActionDone(5)

@external
def move_X_6(_c3: int256):
    assert self.role[msg.sender] == Role.X, "bad role"
    assert not self.actionDone[6], "already done"
    assert self.actionDone[5], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    assert self.actionDone[3], "dependency not satisfied"
    assert self.actionDone[4], "dependency not satisfied"
    assert ((((((((_c3 == 0) or (_c3 == 1)) or (_c3 == 2)) or (_c3 == 3)) or (_c3 == 4)) or (_c3 == 5)) or (_c3 == 6)) or (_c3 == 7)) or (_c3 == 8), "domain"
    assert (((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != _c3)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != _c3)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != _c3)) and (self.O_c2 != _c3), "where"
    self.X_c3 = _c3
    self.done_X_c3 = True
    self._markActionDone(6)

@external
def move_O_7(_c3: int256):
    assert self.role[msg.sender] == Role.O, "bad role"
    assert not self.actionDone[7], "already done"
    assert self.actionDone[6], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    assert self.actionDone[3], "dependency not satisfied"
    assert self.actionDone[4], "dependency not satisfied"
    assert self.actionDone[5], "dependency not satisfied"
    assert ((((((((_c3 == 0) or (_c3 == 1)) or (_c3 == 2)) or (_c3 == 3)) or (_c3 == 4)) or (_c3 == 5)) or (_c3 == 6)) or (_c3 == 7)) or (_c3 == 8), "domain"
    assert ((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != _c3)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != _c3)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != _c3)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != _c3)) and (self.X_c3 != _c3), "where"
    self.O_c3 = _c3
    self.done_O_c3 = True
    self._markActionDone(7)

@external
def move_X_8(_c4: int256):
    assert self.role[msg.sender] == Role.X, "bad role"
    assert not self.actionDone[8], "already done"
    assert self.actionDone[7], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    assert self.actionDone[3], "dependency not satisfied"
    assert self.actionDone[4], "dependency not satisfied"
    assert self.actionDone[5], "dependency not satisfied"
    assert self.actionDone[6], "dependency not satisfied"
    assert ((((((((_c4 == 0) or (_c4 == 1)) or (_c4 == 2)) or (_c4 == 3)) or (_c4 == 4)) or (_c4 == 5)) or (_c4 == 6)) or (_c4 == 7)) or (_c4 == 8), "domain"
    assert ((((((((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != self.O_c3)) and (self.X_c1 != _c4)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != self.O_c3)) and (self.O_c1 != _c4)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != self.O_c3)) and (self.X_c2 != _c4)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != self.O_c3)) and (self.O_c2 != _c4)) and (self.X_c3 != self.O_c3)) and (self.X_c3 != _c4)) and (self.O_c3 != _c4), "where"
    self.X_c4 = _c4
    self.done_X_c4 = True
    self._markActionDone(8)

@external
def move_O_9(_c4: int256):
    assert self.role[msg.sender] == Role.O, "bad role"
    assert not self.actionDone[9], "already done"
    assert self.actionDone[8], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    assert self.actionDone[3], "dependency not satisfied"
    assert self.actionDone[4], "dependency not satisfied"
    assert self.actionDone[5], "dependency not satisfied"
    assert self.actionDone[6], "dependency not satisfied"
    assert self.actionDone[7], "dependency not satisfied"
    assert ((((((((_c4 == 0) or (_c4 == 1)) or (_c4 == 2)) or (_c4 == 3)) or (_c4 == 4)) or (_c4 == 5)) or (_c4 == 6)) or (_c4 == 7)) or (_c4 == 8), "domain"
    assert (((((((((((((((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != self.O_c3)) and (self.X_c1 != self.X_c4)) and (self.X_c1 != _c4)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != self.O_c3)) and (self.O_c1 != self.X_c4)) and (self.O_c1 != _c4)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != self.O_c3)) and (self.X_c2 != self.X_c4)) and (self.X_c2 != _c4)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != self.O_c3)) and (self.O_c2 != self.X_c4)) and (self.O_c2 != _c4)) and (self.X_c3 != self.O_c3)) and (self.X_c3 != self.X_c4)) and (self.X_c3 != _c4)) and (self.O_c3 != self.X_c4)) and (self.O_c3 != _c4)) and (self.X_c4 != _c4), "where"
    self.O_c4 = _c4
    self.done_O_c4 = True
    self._markActionDone(9)

@external
def distributePayoffs():
    assert self.actionDone[FINAL_ACTION], "game not over"
    assert not self.payoffs_distributed, "payoffs already sent"
    self.payoffs_distributed = True
    self.balanceOf[self.address_X] = 0
    self.balanceOf[self.address_O] = 0

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
