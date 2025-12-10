# @version 0.4.0

enum Role:
    None
    A

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[uint256, uint256]
ACTION_A_0: constant(uint256) = 0
FINAL_ACTION: constant(uint256) = 0
roles: HashMap[address, Role]
balanceOf: HashMap[address, int256]
address_A: address
done_A: bool
payoffs_distributed: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp
    

@external
def move_A_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.A][0], "already done"
    assert (not self.done_A), "already joined"
    self.roles[msg.sender] = Role.A
    self.address_A = msg.sender
    self.done_A = True
    self.actionDone[Role.A][0] = True
    self.actionTimestamp[Role.A][0] = block.timestamp
    self.lastTs = block.timestamp
    

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
    
    

