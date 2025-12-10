# @version 0.4.0

enum Role:
    None
    Guest
    Host

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[uint256, uint256]
ACTION_Host_0: constant(uint256) = 0
ACTION_Guest_1: constant(uint256) = 1
ACTION_Host_2: constant(uint256) = 2
ACTION_Guest_3: constant(uint256) = 3
ACTION_Host_4: constant(uint256) = 4
ACTION_Guest_5: constant(uint256) = 5
ACTION_Host_6: constant(uint256) = 6
FINAL_ACTION: constant(uint256) = 6
roles: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_Guest: address
address_Host: address
done_Guest: bool
done_Host: bool
payoffs_distributed: bool
Host_car: int256
done_Host_car: bool
Host_car_hidden: bytes32
done_Host_car_hidden: bool
Guest_d: int256
done_Guest_d: bool
Host_goat: int256
done_Host_goat: bool
Guest_switch: bool
done_Guest_switch: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp
    

@external
@payable
def move_Host_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Host][0], "already done"
    assert (not self.done_Host), "already joined"
    assert (msg.value == 100), "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.roles[msg.sender] = Role.Host
    self.address_Host = msg.sender
    self.done_Host = True
    self.actionDone[Role.Host][0] = True
    self.actionTimestamp[Role.Host][0] = block.timestamp
    self.lastTs = block.timestamp
    

@external
@payable
def move_Guest_1():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Guest][1], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][0], "dependency not satisfied"
    assert (not self.done_Guest), "already joined"
    assert (msg.value == 100), "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.roles[msg.sender] = Role.Guest
    self.address_Guest = msg.sender
    self.done_Guest = True
    self.actionDone[Role.Guest][1] = True
    self.actionTimestamp[Role.Guest][1] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def move_Host_2(_hidden_car: bytes32):
    assert self.roles[msg.sender] == Role.Host, "bad role"
    self._check_timestamp(Role.Host)
    assert not self.bailed[Role.Host], "you bailed"
    assert not self.actionDone[Role.Host][2], "already done"
    self._check_timestamp(Role.Guest)
    if not self.bailed[Role.Guest]:
        assert self.actionDone[Role.Guest][1], "dependency not satisfied"
    self.Host_car_hidden = _hidden_car
    self.done_Host_car_hidden = True
    self.actionDone[Role.Host][2] = True
    self.actionTimestamp[Role.Host][2] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def move_Guest_3(_d: int256):
    assert self.roles[msg.sender] == Role.Guest, "bad role"
    self._check_timestamp(Role.Guest)
    assert not self.bailed[Role.Guest], "you bailed"
    assert not self.actionDone[Role.Guest][3], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][2], "dependency not satisfied"
    assert (((_d == 0) or (_d == 1)) or (_d == 2)), "domain"
    self.Guest_d = _d
    self.done_Guest_d = True
    self.actionDone[Role.Guest][3] = True
    self.actionTimestamp[Role.Guest][3] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def move_Host_4(_goat: int256):
    assert self.roles[msg.sender] == Role.Host, "bad role"
    self._check_timestamp(Role.Host)
    assert not self.bailed[Role.Host], "you bailed"
    assert not self.actionDone[Role.Host][4], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][2], "dependency not satisfied"
    self._check_timestamp(Role.Guest)
    if not self.bailed[Role.Guest]:
        assert self.actionDone[Role.Guest][3], "dependency not satisfied"
    assert (((_goat == 0) or (_goat == 1)) or (_goat == 2)), "domain"
    assert ((_goat != self.Guest_d) and (_goat != self.Host_car)), "domain"
    self.Host_goat = _goat
    self.done_Host_goat = True
    self.actionDone[Role.Host][4] = True
    self.actionTimestamp[Role.Host][4] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def move_Guest_5(_switch: bool):
    assert self.roles[msg.sender] == Role.Guest, "bad role"
    self._check_timestamp(Role.Guest)
    assert not self.bailed[Role.Guest], "you bailed"
    assert not self.actionDone[Role.Guest][5], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][4], "dependency not satisfied"
    self.Guest_switch = _switch
    self.done_Guest_switch = True
    self.actionDone[Role.Guest][5] = True
    self.actionTimestamp[Role.Guest][5] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def move_Host_6(_car: int256, _salt: uint256):
    assert self.roles[msg.sender] == Role.Host, "bad role"
    self._check_timestamp(Role.Host)
    assert not self.bailed[Role.Host], "you bailed"
    assert not self.actionDone[Role.Host][6], "already done"
    self._check_timestamp(Role.Host)
    if not self.bailed[Role.Host]:
        assert self.actionDone[Role.Host][2], "dependency not satisfied"
    self._check_timestamp(Role.Guest)
    if not self.bailed[Role.Guest]:
        assert self.actionDone[Role.Guest][5], "dependency not satisfied"
    assert (((_car == 0) or (_car == 1)) or (_car == 2)), "domain"
    assert (keccak256(concat(convert(car, bytes32), convert(salt, bytes32))) == self.Host_car_hidden), "reveal failed for car"
    self.Host_car = _car
    self.done_Host_car = True
    self.actionDone[Role.Host][6] = True
    self.actionTimestamp[Role.Host][6] = block.timestamp
    self.lastTs = block.timestamp
    

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
    
    

