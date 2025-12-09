# @version 0.4.0

enum Role:
    None
    Issuer
    Alice
    Bob

ACTION_Issuer_0: constant(uint256) = 0
ACTION_Issuer_1: constant(uint256) = 1
ACTION_Alice_2: constant(uint256) = 2
ACTION_Alice_3: constant(uint256) = 3
ACTION_Bob_4: constant(uint256) = 4
ACTION_Bob_5: constant(uint256) = 5
FINAL_ACTION: constant(uint256) = 5

lastTs: uint256
actionDone: HashMap[uint256, bool]
actionTimestamp: HashMap[uint256, uint256]
role: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_Issuer: address
address_Alice: address
address_Bob: address
payoffs_distributed: bool
done_Issuer: bool
done_Alice: bool
done_Bob: bool
Issuer_hidden_c: bytes32
done_Issuer_hidden_c: bool
Issuer_c: int256
done_Issuer_c: bool
Alice_hidden_c: bytes32
done_Alice_hidden_c: bool
Alice_c: int256
done_Alice_c: bool
Bob_hidden_c: bytes32
done_Bob_hidden_c: bool
Bob_c: int256
done_Bob_c: bool

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
def move_Issuer_0(_hidden_c: bytes32):
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[0], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Issuer, "already joined"
    self.role[msg.sender] = Role.Issuer
    self.address_Issuer = msg.sender
    assert msg.value == 10, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Issuer = True
    self.Issuer_hidden_c = _hidden_c
    self.done_Issuer_hidden_c = True
    self._markActionDone(0)

@external
@payable
def move_Alice_2(_hidden_c: bytes32):
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[2], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Alice, "already joined"
    self.role[msg.sender] = Role.Alice
    self.address_Alice = msg.sender
    assert msg.value == 10, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Alice = True
    self.Alice_hidden_c = _hidden_c
    self.done_Alice_hidden_c = True
    self._markActionDone(2)

@external
@payable
def move_Bob_4(_hidden_c: bytes32):
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[4], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Bob, "already joined"
    self.role[msg.sender] = Role.Bob
    self.address_Bob = msg.sender
    assert msg.value == 10, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Bob = True
    self.Bob_hidden_c = _hidden_c
    self.done_Bob_hidden_c = True
    self._markActionDone(4)

@external
def move_Issuer_1(_c: int256, salt: uint256):
    assert self.role[msg.sender] == Role.Issuer, "bad role"
    assert not self.actionDone[1], "already done"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    assert self.actionDone[4], "dependency not satisfied"
    self._checkReveal(self.Issuer_hidden_c, abi_encode(_c, salt, output_type=Bytes[128]))
    assert ((_c == 1) or (_c == 2)) or (_c == 3), "domain"
    self.Issuer_c = _c
    self.done_Issuer_c = True
    self._markActionDone(1)

@external
def move_Alice_3(_c: int256, salt: uint256):
    assert self.role[msg.sender] == Role.Alice, "bad role"
    assert not self.actionDone[3], "already done"
    assert self.actionDone[2], "dependency not satisfied"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.actionDone[4], "dependency not satisfied"
    self._checkReveal(self.Alice_hidden_c, abi_encode(_c, salt, output_type=Bytes[128]))
    assert ((_c == 1) or (_c == 2)) or (_c == 3), "domain"
    self.Alice_c = _c
    self.done_Alice_c = True
    self._markActionDone(3)

@external
def move_Bob_5(_c: int256, salt: uint256):
    assert self.role[msg.sender] == Role.Bob, "bad role"
    assert not self.actionDone[5], "already done"
    assert self.actionDone[4], "dependency not satisfied"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    self._checkReveal(self.Bob_hidden_c, abi_encode(_c, salt, output_type=Bytes[128]))
    assert ((_c == 1) or (_c == 2)) or (_c == 3), "domain"
    self.Bob_c = _c
    self.done_Bob_c = True
    self._markActionDone(5)

@external
def distributePayoffs():
    assert self.actionDone[FINAL_ACTION], "game not over"
    assert not self.payoffs_distributed, "payoffs already sent"
    self.payoffs_distributed = True
    self.balanceOf[self.address_Issuer] = 20 if ((not self.done_Alice_c) or (not self.done_Bob_c)) else (-10) if (not self.done_Issuer_c) else (-10) if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == ((self.Issuer_c + self.Alice_c) + self.Bob_c)) else (-10) if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == (((self.Issuer_c + self.Alice_c) + self.Bob_c) - 1)) else 20
    self.balanceOf[self.address_Alice] = (-10) if ((not self.done_Alice_c) or (not self.done_Bob_c)) else 20 if (not self.done_Issuer_c) else 20 if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == ((self.Issuer_c + self.Alice_c) + self.Bob_c)) else (-10) if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == (((self.Issuer_c + self.Alice_c) + self.Bob_c) - 1)) else (-10)
    self.balanceOf[self.address_Bob] = (-10) if ((not self.done_Alice_c) or (not self.done_Bob_c)) else (-10) if (not self.done_Issuer_c) else (-10) if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == ((self.Issuer_c + self.Alice_c) + self.Bob_c)) else 20 if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == (((self.Issuer_c + self.Alice_c) + self.Bob_c) - 1)) else (-10)

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
