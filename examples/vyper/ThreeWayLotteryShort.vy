# @version 0.4.0

enum Role:
    None
    Issuer
    Alice
    Bob

actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
lastTs: uint256
TIMEOUT: constant(uint256) = 86400
bailed: HashMap[Role, bool]
ACTION_Issuer_1: constant(uint256) = 0
ACTION_Issuer_2: constant(uint256) = 1
ACTION_Alice_3: constant(uint256) = 2
ACTION_Alice_4: constant(uint256) = 3
ACTION_Bob_5: constant(uint256) = 4
ACTION_Bob_6: constant(uint256) = 5
roles: HashMap[address, Role]
address_Issuer: address
address_Alice: address
address_Bob: address
done_Issuer: bool
done_Alice: bool
done_Bob: bool
claimed_Issuer: bool
claimed_Alice: bool
claimed_Bob: bool
Issuer_c: int256
done_Issuer_c: bool
Issuer_c_hidden: bytes32
done_Issuer_c_hidden: bool
Alice_c: int256
done_Alice_c: bool
Alice_c_hidden: bytes32
done_Alice_c_hidden: bool
Bob_c: int256
done_Bob_c: bool
Bob_c_hidden: bytes32
done_Bob_c_hidden: bool

@external
def __init__():
    self.lastTs = block.timestamp

@internal
def _check_timestamp(role: Role):
    if (_role == Role.None):
        return
    if (block.timestamp > (self.lastTs + _TIMEOUT)):
        self.bailed[_role] = True
        self.lastTs = block.timestamp


@external
@payable
def move_Issuer_0(_hidden_c: bytes32):
    assert (self.roles[msg.sender] == Role.Issuer), "bad role"
    _check_timestamp(Role.Issuer)
    assert (not self.bailed[Role.Issuer]), "you bailed"
    assert (not self.actionDone[Role.Issuer][1]), "already done"
    self.actionDone[Role.Issuer][1] = True
    assert (not self.done_Issuer), "already joined"
    assert (msg.value == 12), "bad stake"
    self.roles[msg.sender] = Role.Issuer
    self.address_Issuer = msg.sender
    self.done_Issuer = True
    self.Issuer_c_hidden = _hidden_c
    self.done_Issuer_c_hidden = True
    self.actionTimestamp[Role.Issuer][1] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_Alice_2(_hidden_c: bytes32):
    assert (self.roles[msg.sender] == Role.Alice), "bad role"
    _check_timestamp(Role.Alice)
    assert (not self.bailed[Role.Alice]), "you bailed"
    assert (not self.actionDone[Role.Alice][3]), "already done"
    self.actionDone[Role.Alice][3] = True
    assert (not self.done_Alice), "already joined"
    assert (msg.value == 12), "bad stake"
    self.roles[msg.sender] = Role.Alice
    self.address_Alice = msg.sender
    self.done_Alice = True
    self.Alice_c_hidden = _hidden_c
    self.done_Alice_c_hidden = True
    self.actionTimestamp[Role.Alice][3] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_Bob_4(_hidden_c: bytes32):
    assert (self.roles[msg.sender] == Role.Bob), "bad role"
    _check_timestamp(Role.Bob)
    assert (not self.bailed[Role.Bob]), "you bailed"
    assert (not self.actionDone[Role.Bob][5]), "already done"
    self.actionDone[Role.Bob][5] = True
    assert (not self.done_Bob), "already joined"
    assert (msg.value == 12), "bad stake"
    self.roles[msg.sender] = Role.Bob
    self.address_Bob = msg.sender
    self.done_Bob = True
    self.Bob_c_hidden = _hidden_c
    self.done_Bob_c_hidden = True
    self.actionTimestamp[Role.Bob][5] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Issuer_1(_c: int256, _salt: uint256):
    assert (self.roles[msg.sender] == Role.Issuer), "bad role"
    _check_timestamp(Role.Issuer)
    assert (not self.bailed[Role.Issuer]), "you bailed"
    assert (not self.actionDone[Role.Issuer][2]), "already done"
    self.actionDone[Role.Issuer][2] = True
    _check_timestamp(Role.Issuer)
    if (not self.bailed[Role.Issuer]):
        assert self.actionDone[Role.Issuer][1], "dependency not satisfied"
    _check_timestamp(Role.Alice)
    if (not self.bailed[Role.Alice]):
        assert self.actionDone[Role.Alice][3], "dependency not satisfied"
    _check_timestamp(Role.Bob)
    if (not self.bailed[Role.Bob]):
        assert self.actionDone[Role.Bob][5], "dependency not satisfied"
    assert (((_c == 1) or (_c == 2)) or (_c == 3)), "domain"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.Issuer_c_hidden), "reveal failed for c"
    self.Issuer_c = _c
    self.done_Issuer_c = True
    self.actionTimestamp[Role.Issuer][2] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Alice_3(_c: int256, _salt: uint256):
    assert (self.roles[msg.sender] == Role.Alice), "bad role"
    _check_timestamp(Role.Alice)
    assert (not self.bailed[Role.Alice]), "you bailed"
    assert (not self.actionDone[Role.Alice][4]), "already done"
    self.actionDone[Role.Alice][4] = True
    _check_timestamp(Role.Issuer)
    if (not self.bailed[Role.Issuer]):
        assert self.actionDone[Role.Issuer][1], "dependency not satisfied"
    _check_timestamp(Role.Alice)
    if (not self.bailed[Role.Alice]):
        assert self.actionDone[Role.Alice][3], "dependency not satisfied"
    _check_timestamp(Role.Bob)
    if (not self.bailed[Role.Bob]):
        assert self.actionDone[Role.Bob][5], "dependency not satisfied"
    assert (((_c == 1) or (_c == 2)) or (_c == 3)), "domain"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.Alice_c_hidden), "reveal failed for c"
    self.Alice_c = _c
    self.done_Alice_c = True
    self.actionTimestamp[Role.Alice][4] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Bob_5(_c: int256, _salt: uint256):
    assert (self.roles[msg.sender] == Role.Bob), "bad role"
    _check_timestamp(Role.Bob)
    assert (not self.bailed[Role.Bob]), "you bailed"
    assert (not self.actionDone[Role.Bob][6]), "already done"
    self.actionDone[Role.Bob][6] = True
    _check_timestamp(Role.Issuer)
    if (not self.bailed[Role.Issuer]):
        assert self.actionDone[Role.Issuer][1], "dependency not satisfied"
    _check_timestamp(Role.Alice)
    if (not self.bailed[Role.Alice]):
        assert self.actionDone[Role.Alice][3], "dependency not satisfied"
    _check_timestamp(Role.Bob)
    if (not self.bailed[Role.Bob]):
        assert self.actionDone[Role.Bob][5], "dependency not satisfied"
    assert (((_c == 1) or (_c == 2)) or (_c == 3)), "domain"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.Bob_c_hidden), "reveal failed for c"
    self.Bob_c = _c
    self.done_Bob_c = True
    self.actionTimestamp[Role.Bob][6] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Bob():
    assert (not self.claimed_Bob), "already claimed"
    self.claimed_Bob = True
    payout: int256 = 6 if ((((self.Issuer_c + self.Alice_c) + self.Bob_c) % 3) == 0) else 24 if ((((self.Issuer_c + self.Alice_c) + self.Bob_c) % 3) == 1) else 6 if ((self.done_Alice_c and self.done_Bob_c) and self.done_Issuer_c) else 1 if ((not self.done_Alice_c) and (not self.done_Bob_c)) else 34 if ((not self.done_Alice_c) and (not self.done_Issuer_c)) else 1 if ((not self.done_Bob_c) and (not self.done_Issuer_c)) else 17 if (not self.done_Alice_c) else 2 if (not self.done_Bob_c) else 17 if (not self.done_Issuer_c) else 12
    if payout > 0:
        success: bool = raw_call(self.address_Bob, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_Issuer():
    assert (not self.claimed_Issuer), "already claimed"
    self.claimed_Issuer = True
    payout: int256 = 6 if ((((self.Issuer_c + self.Alice_c) + self.Bob_c) % 3) == 0) else 6 if ((((self.Issuer_c + self.Alice_c) + self.Bob_c) % 3) == 1) else 24 if ((self.done_Alice_c and self.done_Bob_c) and self.done_Issuer_c) else 34 if ((not self.done_Alice_c) and (not self.done_Bob_c)) else 1 if ((not self.done_Alice_c) and (not self.done_Issuer_c)) else 1 if ((not self.done_Bob_c) and (not self.done_Issuer_c)) else 17 if (not self.done_Alice_c) else 17 if (not self.done_Bob_c) else 2 if (not self.done_Issuer_c) else 12
    if payout > 0:
        success: bool = raw_call(self.address_Issuer, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_Alice():
    assert (not self.claimed_Alice), "already claimed"
    self.claimed_Alice = True
    payout: int256 = 24 if ((((self.Issuer_c + self.Alice_c) + self.Bob_c) % 3) == 0) else 6 if ((((self.Issuer_c + self.Alice_c) + self.Bob_c) % 3) == 1) else 6 if ((self.done_Alice_c and self.done_Bob_c) and self.done_Issuer_c) else 1 if ((not self.done_Alice_c) and (not self.done_Bob_c)) else 1 if ((not self.done_Alice_c) and (not self.done_Issuer_c)) else 34 if ((not self.done_Bob_c) and (not self.done_Issuer_c)) else 2 if (not self.done_Alice_c) else 17 if (not self.done_Bob_c) else 17 if (not self.done_Issuer_c) else 12
    if payout > 0:
        success: bool = raw_call(self.address_Alice, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@payable
@external
def __default__():
    assert False, "direct ETH not allowed"

