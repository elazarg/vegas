# @version 0.4.0

enum Role:
    None
    Gambler
    Race

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[uint256, uint256]
ACTION_Race_0: constant(uint256) = 0
ACTION_Gambler_1: constant(uint256) = 1
ACTION_Race_2: constant(uint256) = 2
FINAL_ACTION: constant(uint256) = 2
roles: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_Gambler: address
address_Race: address
done_Gambler: bool
done_Race: bool
payoffs_distributed: bool
Gambler_bet: int256
done_Gambler_bet: bool
Race_winner: int256
done_Race_winner: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp
    

@external
@payable
def move_Race_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Race][0], "already done"
    assert (not self.done_Race), "already joined"
    assert (msg.value == 100), "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.roles[msg.sender] = Role.Race
    self.address_Race = msg.sender
    self.done_Race = True
    self.actionDone[Role.Race][0] = True
    self.actionTimestamp[Role.Race][0] = block.timestamp
    self.lastTs = block.timestamp
    

@external
@payable
def move_Gambler_1(_bet: int256):
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Gambler][1], "already done"
    self._check_timestamp(Role.Race)
    if not self.bailed[Role.Race]:
        assert self.actionDone[Role.Race][0], "dependency not satisfied"
    assert (((_bet == 1) or (_bet == 2)) or (_bet == 3)), "domain"
    assert (not self.done_Gambler), "already joined"
    assert (msg.value == 100), "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.roles[msg.sender] = Role.Gambler
    self.address_Gambler = msg.sender
    self.done_Gambler = True
    self.Gambler_bet = _bet
    self.done_Gambler_bet = True
    self.actionDone[Role.Gambler][1] = True
    self.actionTimestamp[Role.Gambler][1] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def move_Race_2(_winner: int256):
    assert self.roles[msg.sender] == Role.Race, "bad role"
    self._check_timestamp(Role.Race)
    assert not self.bailed[Role.Race], "you bailed"
    assert not self.actionDone[Role.Race][2], "already done"
    self._check_timestamp(Role.Gambler)
    if not self.bailed[Role.Gambler]:
        assert self.actionDone[Role.Gambler][1], "dependency not satisfied"
    assert (((_winner == 1) or (_winner == 2)) or (_winner == 3)), "domain"
    self.Race_winner = _winner
    self.done_Race_winner = True
    self.actionDone[Role.Race][2] = True
    self.actionTimestamp[Role.Race][2] = block.timestamp
    self.lastTs = block.timestamp
    

@external
def distributePayoffs():
    assert self.actionDone[FINAL_ACTION], "game not over"
    assert not self.payoffs_distributed, "payoffs already sent"
    self.payoffs_distributed = True
    self.balanceOf[self.address_Gambler] = 100 if ((not self.done_Race_winner) or (self.Race_winner == self.Gambler_bet)) else 0
    self.balanceOf[self.address_Race] = 0 if ((not self.done_Race_winner) or (self.Race_winner == self.Gambler_bet)) else 100
    

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
    
    

