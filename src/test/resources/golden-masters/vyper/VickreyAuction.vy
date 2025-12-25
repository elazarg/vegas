# @version 0.4.0

enum Role:
    None
    Seller
    B1
    B2
    B3

lastTs: uint256
actionDone: HashMap[Role, HashMap[uint256, bool]]
actionTimestamp: HashMap[Role, HashMap[uint256, uint256]]
ACTION_B1_0: constant(uint256) = 0
ACTION_B2_0: constant(uint256) = 1
ACTION_B3_0: constant(uint256) = 2
ACTION_Seller_0: constant(uint256) = 3
ACTION_B1_1: constant(uint256) = 4
ACTION_B2_2: constant(uint256) = 5
ACTION_B3_3: constant(uint256) = 6
ACTION_B1_4: constant(uint256) = 7
ACTION_B2_5: constant(uint256) = 8
ACTION_B3_6: constant(uint256) = 9
roles: HashMap[address, Role]
address_Seller: address
address_B1: address
address_B2: address
address_B3: address
done_Seller: bool
done_B1: bool
done_B2: bool
done_B3: bool
claimed_Seller: bool
claimed_B1: bool
claimed_B2: bool
claimed_B3: bool
B1_b: int256
done_B1_b: bool
B1_b_hidden: bytes32
done_B1_b_hidden: bool
B2_b: int256
done_B2_b: bool
B2_b_hidden: bytes32
done_B2_b_hidden: bool
B3_b: int256
done_B3_b: bool
B3_b_hidden: bytes32
done_B3_b_hidden: bool
TIMEOUT: constant(uint256) = 86400  # 24 hours in seconds
bailed: HashMap[Role, bool]

@external
def __init__():
    self.lastTs = block.timestamp

@external
@payable
def move_Seller_3():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.Seller][0], "already done"
    assert (not self.done_Seller), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.Seller
    self.address_Seller = msg.sender
    self.done_Seller = True
    self.actionDone[Role.Seller][0] = True
    self.actionTimestamp[Role.Seller][0] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_B1_0():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.B1][0], "already done"
    assert (not self.done_B1), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.B1
    self.address_B1 = msg.sender
    self.done_B1 = True
    self.actionDone[Role.B1][0] = True
    self.actionTimestamp[Role.B1][0] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_B2_1():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.B2][0], "already done"
    assert (not self.done_B2), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.B2
    self.address_B2 = msg.sender
    self.done_B2 = True
    self.actionDone[Role.B2][0] = True
    self.actionTimestamp[Role.B2][0] = block.timestamp
    self.lastTs = block.timestamp

@external
@payable
def move_B3_2():
    assert self.roles[msg.sender] == Role.None, "bad role"
    self._check_timestamp(Role.None)
    assert not self.bailed[Role.None], "you bailed"
    assert not self.actionDone[Role.B3][0], "already done"
    assert (not self.done_B3), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.B3
    self.address_B3 = msg.sender
    self.done_B3 = True
    self.actionDone[Role.B3][0] = True
    self.actionTimestamp[Role.B3][0] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_B1_4(_hidden_b: bytes32):
    assert self.roles[msg.sender] == Role.B1, "bad role"
    self._check_timestamp(Role.B1)
    assert not self.bailed[Role.B1], "you bailed"
    assert not self.actionDone[Role.B1][1], "already done"
    self._check_timestamp(Role.B1)
    if not self.bailed[Role.B1]:
        assert self.actionDone[Role.B1][0], "dependency not satisfied"
    self._check_timestamp(Role.B2)
    if not self.bailed[Role.B2]:
        assert self.actionDone[Role.B2][0], "dependency not satisfied"
    self._check_timestamp(Role.B3)
    if not self.bailed[Role.B3]:
        assert self.actionDone[Role.B3][0], "dependency not satisfied"
    self._check_timestamp(Role.Seller)
    if not self.bailed[Role.Seller]:
        assert self.actionDone[Role.Seller][0], "dependency not satisfied"
    self.B1_b_hidden = _hidden_b
    self.done_B1_b_hidden = True
    self.actionDone[Role.B1][1] = True
    self.actionTimestamp[Role.B1][1] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_B2_5(_hidden_b: bytes32):
    assert self.roles[msg.sender] == Role.B2, "bad role"
    self._check_timestamp(Role.B2)
    assert not self.bailed[Role.B2], "you bailed"
    assert not self.actionDone[Role.B2][2], "already done"
    self._check_timestamp(Role.B1)
    if not self.bailed[Role.B1]:
        assert self.actionDone[Role.B1][1], "dependency not satisfied"
    self.B2_b_hidden = _hidden_b
    self.done_B2_b_hidden = True
    self.actionDone[Role.B2][2] = True
    self.actionTimestamp[Role.B2][2] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_B3_6(_hidden_b: bytes32):
    assert self.roles[msg.sender] == Role.B3, "bad role"
    self._check_timestamp(Role.B3)
    assert not self.bailed[Role.B3], "you bailed"
    assert not self.actionDone[Role.B3][3], "already done"
    self._check_timestamp(Role.B2)
    if not self.bailed[Role.B2]:
        assert self.actionDone[Role.B2][2], "dependency not satisfied"
    self.B3_b_hidden = _hidden_b
    self.done_B3_b_hidden = True
    self.actionDone[Role.B3][3] = True
    self.actionTimestamp[Role.B3][3] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_B1_7(_b: int256, _salt: uint256):
    assert self.roles[msg.sender] == Role.B1, "bad role"
    self._check_timestamp(Role.B1)
    assert not self.bailed[Role.B1], "you bailed"
    assert not self.actionDone[Role.B1][4], "already done"
    self._check_timestamp(Role.B1)
    if not self.bailed[Role.B1]:
        assert self.actionDone[Role.B1][1], "dependency not satisfied"
    self._check_timestamp(Role.B3)
    if not self.bailed[Role.B3]:
        assert self.actionDone[Role.B3][3], "dependency not satisfied"
    assert (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((_b == 0) or (_b == 1)) or (_b == 2)) or (_b == 3)) or (_b == 4)) or (_b == 5)) or (_b == 6)) or (_b == 7)) or (_b == 8)) or (_b == 9)) or (_b == 10)) or (_b == 11)) or (_b == 12)) or (_b == 13)) or (_b == 14)) or (_b == 15)) or (_b == 16)) or (_b == 17)) or (_b == 18)) or (_b == 19)) or (_b == 20)) or (_b == 21)) or (_b == 22)) or (_b == 23)) or (_b == 24)) or (_b == 25)) or (_b == 26)) or (_b == 27)) or (_b == 28)) or (_b == 29)) or (_b == 30)) or (_b == 31)) or (_b == 32)) or (_b == 33)) or (_b == 34)) or (_b == 35)) or (_b == 36)) or (_b == 37)) or (_b == 38)) or (_b == 39)) or (_b == 40)) or (_b == 41)) or (_b == 42)) or (_b == 43)) or (_b == 44)) or (_b == 45)) or (_b == 46)) or (_b == 47)) or (_b == 48)) or (_b == 49)) or (_b == 50)) or (_b == 51)) or (_b == 52)) or (_b == 53)) or (_b == 54)) or (_b == 55)) or (_b == 56)) or (_b == 57)) or (_b == 58)) or (_b == 59)) or (_b == 60)) or (_b == 61)) or (_b == 62)) or (_b == 63)) or (_b == 64)) or (_b == 65)) or (_b == 66)) or (_b == 67)) or (_b == 68)) or (_b == 69)) or (_b == 70)) or (_b == 71)) or (_b == 72)) or (_b == 73)) or (_b == 74)) or (_b == 75)) or (_b == 76)) or (_b == 77)) or (_b == 78)) or (_b == 79)) or (_b == 80)) or (_b == 81)) or (_b == 82)) or (_b == 83)) or (_b == 84)) or (_b == 85)) or (_b == 86)) or (_b == 87)) or (_b == 88)) or (_b == 89)) or (_b == 90)) or (_b == 91)) or (_b == 92)) or (_b == 93)) or (_b == 94)) or (_b == 95)) or (_b == 96)) or (_b == 97)) or (_b == 98)) or (_b == 99)) or (_b == 100)), "domain"
    assert (keccak256(concat(convert(b, bytes32), convert(salt, bytes32))) == self.B1_b_hidden), "reveal failed for b"
    self.B1_b = _b
    self.done_B1_b = True
    self.actionDone[Role.B1][4] = True
    self.actionTimestamp[Role.B1][4] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_B2_8(_b: int256, _salt: uint256):
    assert self.roles[msg.sender] == Role.B2, "bad role"
    self._check_timestamp(Role.B2)
    assert not self.bailed[Role.B2], "you bailed"
    assert not self.actionDone[Role.B2][5], "already done"
    self._check_timestamp(Role.B2)
    if not self.bailed[Role.B2]:
        assert self.actionDone[Role.B2][2], "dependency not satisfied"
    self._check_timestamp(Role.B1)
    if not self.bailed[Role.B1]:
        assert self.actionDone[Role.B1][4], "dependency not satisfied"
    assert (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((_b == 0) or (_b == 1)) or (_b == 2)) or (_b == 3)) or (_b == 4)) or (_b == 5)) or (_b == 6)) or (_b == 7)) or (_b == 8)) or (_b == 9)) or (_b == 10)) or (_b == 11)) or (_b == 12)) or (_b == 13)) or (_b == 14)) or (_b == 15)) or (_b == 16)) or (_b == 17)) or (_b == 18)) or (_b == 19)) or (_b == 20)) or (_b == 21)) or (_b == 22)) or (_b == 23)) or (_b == 24)) or (_b == 25)) or (_b == 26)) or (_b == 27)) or (_b == 28)) or (_b == 29)) or (_b == 30)) or (_b == 31)) or (_b == 32)) or (_b == 33)) or (_b == 34)) or (_b == 35)) or (_b == 36)) or (_b == 37)) or (_b == 38)) or (_b == 39)) or (_b == 40)) or (_b == 41)) or (_b == 42)) or (_b == 43)) or (_b == 44)) or (_b == 45)) or (_b == 46)) or (_b == 47)) or (_b == 48)) or (_b == 49)) or (_b == 50)) or (_b == 51)) or (_b == 52)) or (_b == 53)) or (_b == 54)) or (_b == 55)) or (_b == 56)) or (_b == 57)) or (_b == 58)) or (_b == 59)) or (_b == 60)) or (_b == 61)) or (_b == 62)) or (_b == 63)) or (_b == 64)) or (_b == 65)) or (_b == 66)) or (_b == 67)) or (_b == 68)) or (_b == 69)) or (_b == 70)) or (_b == 71)) or (_b == 72)) or (_b == 73)) or (_b == 74)) or (_b == 75)) or (_b == 76)) or (_b == 77)) or (_b == 78)) or (_b == 79)) or (_b == 80)) or (_b == 81)) or (_b == 82)) or (_b == 83)) or (_b == 84)) or (_b == 85)) or (_b == 86)) or (_b == 87)) or (_b == 88)) or (_b == 89)) or (_b == 90)) or (_b == 91)) or (_b == 92)) or (_b == 93)) or (_b == 94)) or (_b == 95)) or (_b == 96)) or (_b == 97)) or (_b == 98)) or (_b == 99)) or (_b == 100)), "domain"
    assert (keccak256(concat(convert(b, bytes32), convert(salt, bytes32))) == self.B2_b_hidden), "reveal failed for b"
    self.B2_b = _b
    self.done_B2_b = True
    self.actionDone[Role.B2][5] = True
    self.actionTimestamp[Role.B2][5] = block.timestamp
    self.lastTs = block.timestamp

@external
def move_B3_9(_b: int256, _salt: uint256):
    assert self.roles[msg.sender] == Role.B3, "bad role"
    self._check_timestamp(Role.B3)
    assert not self.bailed[Role.B3], "you bailed"
    assert not self.actionDone[Role.B3][6], "already done"
    self._check_timestamp(Role.B3)
    if not self.bailed[Role.B3]:
        assert self.actionDone[Role.B3][3], "dependency not satisfied"
    self._check_timestamp(Role.B2)
    if not self.bailed[Role.B2]:
        assert self.actionDone[Role.B2][5], "dependency not satisfied"
    assert (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((_b == 0) or (_b == 1)) or (_b == 2)) or (_b == 3)) or (_b == 4)) or (_b == 5)) or (_b == 6)) or (_b == 7)) or (_b == 8)) or (_b == 9)) or (_b == 10)) or (_b == 11)) or (_b == 12)) or (_b == 13)) or (_b == 14)) or (_b == 15)) or (_b == 16)) or (_b == 17)) or (_b == 18)) or (_b == 19)) or (_b == 20)) or (_b == 21)) or (_b == 22)) or (_b == 23)) or (_b == 24)) or (_b == 25)) or (_b == 26)) or (_b == 27)) or (_b == 28)) or (_b == 29)) or (_b == 30)) or (_b == 31)) or (_b == 32)) or (_b == 33)) or (_b == 34)) or (_b == 35)) or (_b == 36)) or (_b == 37)) or (_b == 38)) or (_b == 39)) or (_b == 40)) or (_b == 41)) or (_b == 42)) or (_b == 43)) or (_b == 44)) or (_b == 45)) or (_b == 46)) or (_b == 47)) or (_b == 48)) or (_b == 49)) or (_b == 50)) or (_b == 51)) or (_b == 52)) or (_b == 53)) or (_b == 54)) or (_b == 55)) or (_b == 56)) or (_b == 57)) or (_b == 58)) or (_b == 59)) or (_b == 60)) or (_b == 61)) or (_b == 62)) or (_b == 63)) or (_b == 64)) or (_b == 65)) or (_b == 66)) or (_b == 67)) or (_b == 68)) or (_b == 69)) or (_b == 70)) or (_b == 71)) or (_b == 72)) or (_b == 73)) or (_b == 74)) or (_b == 75)) or (_b == 76)) or (_b == 77)) or (_b == 78)) or (_b == 79)) or (_b == 80)) or (_b == 81)) or (_b == 82)) or (_b == 83)) or (_b == 84)) or (_b == 85)) or (_b == 86)) or (_b == 87)) or (_b == 88)) or (_b == 89)) or (_b == 90)) or (_b == 91)) or (_b == 92)) or (_b == 93)) or (_b == 94)) or (_b == 95)) or (_b == 96)) or (_b == 97)) or (_b == 98)) or (_b == 99)) or (_b == 100)), "domain"
    assert (keccak256(concat(convert(b, bytes32), convert(salt, bytes32))) == self.B3_b_hidden), "reveal failed for b"
    self.B3_b = _b
    self.done_B3_b = True
    self.actionDone[Role.B3][6] = True
    self.actionTimestamp[Role.B3][6] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_B2():
    assert self.roles[msg.sender] == Role.B2, "bad role"
    self._check_timestamp(Role.B2)
    assert not self.bailed[Role.B2], "you bailed"
    assert not self.actionDone[Role.B2][10], "already done"
    self._check_timestamp(Role.B3)
    if not self.bailed[Role.B3]:
        assert self.actionDone[Role.B3][6], "dependency not satisfied"
    assert (not self.claimed_B2), "already claimed"
    self.claimed_B2 = True
    payout: int256 = 100 if (not self.done_B1_b) else 0 if (not self.done_B2_b) else 100 if (not self.done_B3_b) else (100 - self.B2_b if (self.B2_b >= self.B3_b) else self.B3_b if (self.B1_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else self.B1_b if (self.B1_b >= self.B3_b) else self.B3_b if (self.B2_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if (self.B2_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else 100
    if payout > 0:
        success: bool = raw_call(self.address_B2, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.B2][10] = True
    self.actionTimestamp[Role.B2][10] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_B3():
    assert self.roles[msg.sender] == Role.B3, "bad role"
    self._check_timestamp(Role.B3)
    assert not self.bailed[Role.B3], "you bailed"
    assert not self.actionDone[Role.B3][11], "already done"
    self._check_timestamp(Role.B3)
    if not self.bailed[Role.B3]:
        assert self.actionDone[Role.B3][6], "dependency not satisfied"
    assert (not self.claimed_B3), "already claimed"
    self.claimed_B3 = True
    payout: int256 = 100 if (not self.done_B1_b) else 100 if (not self.done_B2_b) else 0 if (not self.done_B3_b) else (100 - self.B2_b if (self.B2_b >= self.B3_b) else self.B3_b if (self.B1_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else self.B1_b if (self.B1_b >= self.B3_b) else self.B3_b if (self.B2_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if (self.B3_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else 100
    if payout > 0:
        success: bool = raw_call(self.address_B3, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.B3][11] = True
    self.actionTimestamp[Role.B3][11] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_Seller():
    assert self.roles[msg.sender] == Role.Seller, "bad role"
    self._check_timestamp(Role.Seller)
    assert not self.bailed[Role.Seller], "you bailed"
    assert not self.actionDone[Role.Seller][12], "already done"
    self._check_timestamp(Role.B3)
    if not self.bailed[Role.B3]:
        assert self.actionDone[Role.B3][6], "dependency not satisfied"
    assert (not self.claimed_Seller), "already claimed"
    self.claimed_Seller = True
    payout: int256 = 200 if (not self.done_B1_b) else 200 if (not self.done_B2_b) else 200 if (not self.done_B3_b) else (100 + self.B2_b if (self.B2_b >= self.B3_b) else self.B3_b if (self.B1_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else self.B1_b if (self.B1_b >= self.B3_b) else self.B3_b if (self.B2_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b)
    if payout > 0:
        success: bool = raw_call(self.address_Seller, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.Seller][12] = True
    self.actionTimestamp[Role.Seller][12] = block.timestamp
    self.lastTs = block.timestamp

@external
def withdraw_B1():
    assert self.roles[msg.sender] == Role.B1, "bad role"
    self._check_timestamp(Role.B1)
    assert not self.bailed[Role.B1], "you bailed"
    assert not self.actionDone[Role.B1][13], "already done"
    self._check_timestamp(Role.B3)
    if not self.bailed[Role.B3]:
        assert self.actionDone[Role.B3][6], "dependency not satisfied"
    assert (not self.claimed_B1), "already claimed"
    self.claimed_B1 = True
    payout: int256 = 0 if (not self.done_B1_b) else 100 if (not self.done_B2_b) else 100 if (not self.done_B3_b) else (100 - self.B2_b if (self.B2_b >= self.B3_b) else self.B3_b if (self.B1_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else self.B1_b if (self.B1_b >= self.B3_b) else self.B3_b if (self.B2_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if (self.B1_b == self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b if (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b >= self.B3_b) else self.B3_b) else 100
    if payout > 0:
        success: bool = raw_call(self.address_B1, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"
    self.actionDone[Role.B1][13] = True
    self.actionTimestamp[Role.B1][13] = block.timestamp
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

