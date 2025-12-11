# @version 0.4.0

enum Role:
    None
    Issuer
    Alice
    Bob

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
ACTION_Issuer_0: constant(uint256) = 0
ACTION_Alice_1: constant(uint256) = 1
ACTION_Bob_2: constant(uint256) = 2
ACTION_Issuer_4: constant(uint256) = 3
ACTION_Issuer_5: constant(uint256) = 4
ACTION_Alice_6: constant(uint256) = 5
ACTION_Alice_7: constant(uint256) = 6
ACTION_Bob_8: constant(uint256) = 7
ACTION_Bob_9: constant(uint256) = 8
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
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp

@external
@payable
def move_Issuer_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Issuer][0], "already done"
    assert (not self.done_Issuer), "already joined"
    assert (msg.value == 10), "bad stake"
    self.roles[msg.sender] = Role.Issuer
    self.address_Issuer = msg.sender
    self.done_Issuer = True
    self.actionDone[Role.Issuer][0] = True
    self.actionTimestamp[Role.Issuer][0] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_Alice_1():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Alice][1], "already done"
    self._check_timestamp(Role.Issuer)
    if not self.bailed[Role.Issuer]:
        assert self.actionDone[Role.Issuer][0], "dependency not satisfied"
    assert (not self.done_Alice), "already joined"
    assert (msg.value == 10), "bad stake"
    self.roles[msg.sender] = Role.Alice
    self.address_Alice = msg.sender
    self.done_Alice = True
    self.actionDone[Role.Alice][1] = True
    self.actionTimestamp[Role.Alice][1] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_Bob_2():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Bob][2], "already done"
    self._check_timestamp(Role.Alice)
    if not self.bailed[Role.Alice]:
        assert self.actionDone[Role.Alice][1], "dependency not satisfied"
    assert (not self.done_Bob), "already joined"
    assert (msg.value == 10), "bad stake"
    self.roles[msg.sender] = Role.Bob
    self.address_Bob = msg.sender
    self.done_Bob = True
    self.actionDone[Role.Bob][2] = True
    self.actionTimestamp[Role.Bob][2] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Issuer_3(_hidden_c: bytes32):
    assert self.roles[msg.sender] == Role.Issuer, "bad role"
    self._check_timestamp(Role.Issuer)
    assert not self.bailed[Role.Issuer], "you bailed"
    assert not self.actionDone[Role.Issuer][4], "already done"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][2], "dependency not satisfied"
    self.Issuer_c_hidden = _hidden_c
    self.done_Issuer_c_hidden = True
    self.actionDone[Role.Issuer][4] = True
    self.actionTimestamp[Role.Issuer][4] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Alice_5(_hidden_c: bytes32):
    assert self.roles[msg.sender] == Role.Alice, "bad role"
    self._check_timestamp(Role.Alice)
    assert not self.bailed[Role.Alice], "you bailed"
    assert not self.actionDone[Role.Alice][6], "already done"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][2], "dependency not satisfied"
    self.Alice_c_hidden = _hidden_c
    self.done_Alice_c_hidden = True
    self.actionDone[Role.Alice][6] = True
    self.actionTimestamp[Role.Alice][6] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Bob_7(_hidden_c: bytes32):
    assert self.roles[msg.sender] == Role.Bob, "bad role"
    self._check_timestamp(Role.Bob)
    assert not self.bailed[Role.Bob], "you bailed"
    assert not self.actionDone[Role.Bob][8], "already done"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][2], "dependency not satisfied"
    self.Bob_c_hidden = _hidden_c
    self.done_Bob_c_hidden = True
    self.actionDone[Role.Bob][8] = True
    self.actionTimestamp[Role.Bob][8] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Issuer_4(_c: int256, _salt: uint256):
    assert self.roles[msg.sender] == Role.Issuer, "bad role"
    self._check_timestamp(Role.Issuer)
    assert not self.bailed[Role.Issuer], "you bailed"
    assert not self.actionDone[Role.Issuer][5], "already done"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][2], "dependency not satisfied"
    self._check_timestamp(Role.Issuer)
    if not self.bailed[Role.Issuer]:
        assert self.actionDone[Role.Issuer][4], "dependency not satisfied"
    self._check_timestamp(Role.Alice)
    if not self.bailed[Role.Alice]:
        assert self.actionDone[Role.Alice][6], "dependency not satisfied"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][8], "dependency not satisfied"
    assert (((_c == 1) or (_c == 2)) or (_c == 3)), "domain"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.Issuer_c_hidden), "reveal failed for c"
    self.Issuer_c = _c
    self.done_Issuer_c = True
    self.actionDone[Role.Issuer][5] = True
    self.actionTimestamp[Role.Issuer][5] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Alice_6(_c: int256, _salt: uint256):
    assert self.roles[msg.sender] == Role.Alice, "bad role"
    self._check_timestamp(Role.Alice)
    assert not self.bailed[Role.Alice], "you bailed"
    assert not self.actionDone[Role.Alice][7], "already done"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][2], "dependency not satisfied"
    self._check_timestamp(Role.Issuer)
    if not self.bailed[Role.Issuer]:
        assert self.actionDone[Role.Issuer][4], "dependency not satisfied"
    self._check_timestamp(Role.Alice)
    if not self.bailed[Role.Alice]:
        assert self.actionDone[Role.Alice][6], "dependency not satisfied"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][8], "dependency not satisfied"
    assert (((_c == 1) or (_c == 2)) or (_c == 3)), "domain"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.Alice_c_hidden), "reveal failed for c"
    self.Alice_c = _c
    self.done_Alice_c = True
    self.actionDone[Role.Alice][7] = True
    self.actionTimestamp[Role.Alice][7] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_Bob_8(_c: int256, _salt: uint256):
    assert self.roles[msg.sender] == Role.Bob, "bad role"
    self._check_timestamp(Role.Bob)
    assert not self.bailed[Role.Bob], "you bailed"
    assert not self.actionDone[Role.Bob][9], "already done"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][2], "dependency not satisfied"
    self._check_timestamp(Role.Issuer)
    if not self.bailed[Role.Issuer]:
        assert self.actionDone[Role.Issuer][4], "dependency not satisfied"
    self._check_timestamp(Role.Alice)
    if not self.bailed[Role.Alice]:
        assert self.actionDone[Role.Alice][6], "dependency not satisfied"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][8], "dependency not satisfied"
    assert (((_c == 1) or (_c == 2)) or (_c == 3)), "domain"
    assert (keccak256(concat(convert(c, bytes32), convert(salt, bytes32))) == self.Bob_c_hidden), "reveal failed for c"
    self.Bob_c = _c
    self.done_Bob_c = True
    self.actionDone[Role.Bob][9] = True
    self.actionTimestamp[Role.Bob][9] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Bob():
    assert self.roles[msg.sender] == Role.Bob, "bad role"
    self._check_timestamp(Role.Bob)
    assert not self.bailed[Role.Bob], "you bailed"
    assert not self.actionDone[Role.Bob][9], "already done"
    self._check_timestamp(Role.Issuer)
    if not self.bailed[Role.Issuer]:
        assert self.actionDone[Role.Issuer][5], "dependency not satisfied"
    self._check_timestamp(Role.Alice)
    if not self.bailed[Role.Alice]:
        assert self.actionDone[Role.Alice][7], "dependency not satisfied"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][9], "dependency not satisfied"
    assert (not self.claimed_Bob), "already claimed"
    self.claimed_Bob = True
    payout: int256 = 0 if ((not self.done_Alice_c) or (not self.done_Bob_c)) else 0 if (not self.done_Issuer_c) else 0 if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == ((self.Issuer_c + self.Alice_c) + self.Bob_c)) else 30 if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == (((self.Issuer_c + self.Alice_c) + self.Bob_c) - 1)) else 0
    if payout > 0:
        success: bool = raw_call(self.address_Bob, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.Bob][9] = True
    self.actionTimestamp[Role.Bob][9] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Issuer():
    assert self.roles[msg.sender] == Role.Issuer, "bad role"
    self._check_timestamp(Role.Issuer)
    assert not self.bailed[Role.Issuer], "you bailed"
    assert not self.actionDone[Role.Issuer][10], "already done"
    self._check_timestamp(Role.Issuer)
    if not self.bailed[Role.Issuer]:
        assert self.actionDone[Role.Issuer][5], "dependency not satisfied"
    self._check_timestamp(Role.Alice)
    if not self.bailed[Role.Alice]:
        assert self.actionDone[Role.Alice][7], "dependency not satisfied"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][9], "dependency not satisfied"
    assert (not self.claimed_Issuer), "already claimed"
    self.claimed_Issuer = True
    payout: int256 = 30 if ((not self.done_Alice_c) or (not self.done_Bob_c)) else 0 if (not self.done_Issuer_c) else 0 if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == ((self.Issuer_c + self.Alice_c) + self.Bob_c)) else 0 if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == (((self.Issuer_c + self.Alice_c) + self.Bob_c) - 1)) else 30
    if payout > 0:
        success: bool = raw_call(self.address_Issuer, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.Issuer][10] = True
    self.actionTimestamp[Role.Issuer][10] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Alice():
    assert self.roles[msg.sender] == Role.Alice, "bad role"
    self._check_timestamp(Role.Alice)
    assert not self.bailed[Role.Alice], "you bailed"
    assert not self.actionDone[Role.Alice][11], "already done"
    self._check_timestamp(Role.Issuer)
    if not self.bailed[Role.Issuer]:
        assert self.actionDone[Role.Issuer][5], "dependency not satisfied"
    self._check_timestamp(Role.Alice)
    if not self.bailed[Role.Alice]:
        assert self.actionDone[Role.Alice][7], "dependency not satisfied"
    self._check_timestamp(Role.Bob)
    if not self.bailed[Role.Bob]:
        assert self.actionDone[Role.Bob][9], "dependency not satisfied"
    assert (not self.claimed_Alice), "already claimed"
    self.claimed_Alice = True
    payout: int256 = 0 if ((not self.done_Alice_c) or (not self.done_Bob_c)) else 30 if (not self.done_Issuer_c) else 30 if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == ((self.Issuer_c + self.Alice_c) + self.Bob_c)) else 0 if (((((self.Issuer_c + self.Alice_c) + self.Bob_c) / 3) * 3) == (((self.Issuer_c + self.Alice_c) + self.Bob_c) - 1)) else 0
    if payout > 0:
        success: bool = raw_call(self.address_Alice, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.Alice][11] = True
    self.actionTimestamp[Role.Alice][11] = block.timestamp
    self.lastTs = block.timestamp

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

