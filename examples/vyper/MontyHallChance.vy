# @version 0.4.0

enum Role:
    None
    Guest
    Host

ACTION_Host_0: constant(uint256) = 0
ACTION_Guest_1: constant(uint256) = 1
ACTION_Host_2: constant(uint256) = 2
ACTION_Guest_3: constant(uint256) = 3
ACTION_Host_4: constant(uint256) = 4
ACTION_Guest_5: constant(uint256) = 5
ACTION_Host_6: constant(uint256) = 6
FINAL_ACTION: constant(uint256) = 6

lastTs: uint256
actionDone: HashMap[uint256, bool]
actionTimestamp: HashMap[uint256, uint256]
role: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_Guest: address
address_Host: address
payoffs_distributed: bool
done_Host: bool
done_Guest: bool
Host_hidden_car: bytes32
done_Host_hidden_car: bool
Host_car: int256
done_Host_car: bool
Guest_d: int256
done_Guest_d: bool
Host_goat: int256
done_Host_goat: bool
Guest_switch: bool
done_Guest_switch: bool

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
def move_Host_0():
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[0], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Host, "already joined"
    self.role[msg.sender] = Role.Host
    self.address_Host = msg.sender
    assert msg.value == 100, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Host = True
    self._markActionDone(0)

@external
@payable
def move_Guest_1():
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[1], "already done"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Guest, "already joined"
    self.role[msg.sender] = Role.Guest
    self.address_Guest = msg.sender
    assert msg.value == 100, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Guest = True
    self._markActionDone(1)

@external
def move_Host_2(_hidden_car: bytes32):
    assert self.role[msg.sender] == Role.Host, "bad role"
    assert not self.actionDone[2], "already done"
    assert self.actionDone[1], "dependency not satisfied"
    self.Host_hidden_car = _hidden_car
    self.done_Host_hidden_car = True
    self._markActionDone(2)

@external
def move_Guest_3(_d: int256):
    assert self.role[msg.sender] == Role.Guest, "bad role"
    assert not self.actionDone[3], "already done"
    assert self.actionDone[2], "dependency not satisfied"
    assert ((_d == 0) or (_d == 1)) or (_d == 2), "domain"
    self.Guest_d = _d
    self.done_Guest_d = True
    self._markActionDone(3)

@external
def move_Host_4(_goat: int256):
    assert self.role[msg.sender] == Role.Host, "bad role"
    assert not self.actionDone[4], "already done"
    assert self.actionDone[3], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    assert ((_goat == 0) or (_goat == 1)) or (_goat == 2), "domain"
    assert (_goat != self.Guest_d) and (_goat != self.Host_car), "where"
    self.Host_goat = _goat
    self.done_Host_goat = True
    self._markActionDone(4)

@external
def move_Guest_5(_switch: bool):
    assert self.role[msg.sender] == Role.Guest, "bad role"
    assert not self.actionDone[5], "already done"
    assert self.actionDone[4], "dependency not satisfied"
    self.Guest_switch = _switch
    self.done_Guest_switch = True
    self._markActionDone(5)

@external
def move_Host_6(_car: int256, salt: uint256):
    assert self.role[msg.sender] == Role.Host, "bad role"
    assert not self.actionDone[6], "already done"
    assert self.actionDone[5], "dependency not satisfied"
    assert self.actionDone[2], "dependency not satisfied"
    self._checkReveal(self.Host_hidden_car, abi_encode(_car, salt, output_type=Bytes[128]))
    assert ((_car == 0) or (_car == 1)) or (_car == 2), "domain"
    self.Host_car = _car
    self.done_Host_car = True
    self._markActionDone(6)

@external
def distributePayoffs():
    assert self.actionDone[FINAL_ACTION], "game not over"
    assert not self.payoffs_distributed, "payoffs already sent"
    self.payoffs_distributed = True
    self.balanceOf[self.address_Guest] = 20 if ((self.Guest_d != self.Host_car) == self.Guest_switch) else (-20) if ((self.done_Host_car and self.done_Host_goat) and self.done_Guest_switch) else 20 if ((not self.done_Host_car) or (not self.done_Host_goat)) else (-100)
    self.balanceOf[self.address_Host] = 0 if ((self.done_Host_car and self.done_Host_goat) and self.done_Guest_switch) else (-100) if ((not self.done_Host_car) or (not self.done_Host_goat)) else 0

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
