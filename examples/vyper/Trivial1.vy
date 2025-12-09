# @version 0.4.0

enum Role:
    None
    A

ACTION_A_0: constant(uint256) = 0
FINAL_ACTION: constant(uint256) = 0

lastTs: uint256
actionDone: HashMap[uint256, bool]
actionTimestamp: HashMap[uint256, uint256]
role: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_A: address
payoffs_distributed: bool
done_A: bool

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
def move_A_0():
    assert self.role[msg.sender] == Role.None, "bad role"
    assert not self.actionDone[0], "already done"
    assert self.role[msg.sender] == Role.None, "already has a role"
    assert not self.done_A, "already joined"
    self.role[msg.sender] = Role.A
    self.address_A = msg.sender
    self.done_A = True
    self._markActionDone(0)

@external
def distributePayoffs():
    assert self.actionDone[FINAL_ACTION], "game not over"
    assert not self.payoffs_distributed, "payoffs already sent"
    self.payoffs_distributed = True
    self.balanceOf[self.address_A] = 0

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
