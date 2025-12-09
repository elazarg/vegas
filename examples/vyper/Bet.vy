# @version 0.4.0

enum Role:
    None
    Gambler
    Race

ACTION_Race_0: constant(uint256) = 0
ACTION_Gambler_1: constant(uint256) = 1
ACTION_Race_2: constant(uint256) = 2
FINAL_ACTION: constant(uint256) = 2

lastTs: uint256
actionDone: HashMap[uint256, bool]
actionTimestamp: HashMap[uint256, uint256]
role: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_Gambler: address
address_Race: address
payoffs_distributed: bool
done_Race: bool
done_Gambler: bool
Gambler_bet: int256
done_Gambler_bet: bool
Race_winner: int256
done_Race_winner: bool

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
def move_Race_0():
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[0], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Race, "already joined"
    self.role[msg.sender] = Role.Race
    self.address_Race = msg.sender
    assert msg.value == 100, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Race = True
    self._markActionDone(0)

@external
@payable
def move_Gambler_1(_bet: int256):
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[1], "already done"
    assert self.actionDone[0], "dependency not satisfied"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_Gambler, "already joined"
    self.role[msg.sender] = Role.Gambler
    self.address_Gambler = msg.sender
    assert msg.value == 100, "bad stake"
    self.balanceOf[msg.sender] = msg.value
    self.done_Gambler = True
    assert ((_bet == 1) or (_bet == 2)) or (_bet == 3), "domain"
    self.Gambler_bet = _bet
    self.done_Gambler_bet = True
    self._markActionDone(1)

@external
def move_Race_2(_winner: int256):
    assert self.role[msg.sender] == Role.Race, "bad role"
    assert not self.actionDone[2], "already done"
    assert self.actionDone[1], "dependency not satisfied"
    assert ((_winner == 1) or (_winner == 2)) or (_winner == 3), "domain"
    self.Race_winner = _winner
    self.done_Race_winner = True
    self._markActionDone(2)

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
    ok: bool = raw_call(msg.sender, b"", value=convert(bal, uint256), max_outsize=0, gas=100000)
    assert ok, "ETH send failed"

@payable
@external
def __default__():
    assert False, "direct ETH not allowed"
