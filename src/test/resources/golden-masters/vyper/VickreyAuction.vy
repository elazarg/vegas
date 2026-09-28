#pragma version ^0.4.3

flag Role:
    Seller
    B1
    B2
    B3

ACTION_B1_0: public(constant(uint256)) = 0
ACTION_B2_0: public(constant(uint256)) = 1
ACTION_B3_0: public(constant(uint256)) = 2
ACTION_Seller_0: public(constant(uint256)) = 3
ACTION_B1_2: public(constant(uint256)) = 4
ACTION_B2_4: public(constant(uint256)) = 5
ACTION_B3_6: public(constant(uint256)) = 6
ACTION_B1_3: public(constant(uint256)) = 7
ACTION_B2_5: public(constant(uint256)) = 8
ACTION_B3_7: public(constant(uint256)) = 9
roles: public(HashMap[address, Role])
address_Seller: public(address)
address_B1: public(address)
address_B2: public(address)
address_B3: public(address)
done_Seller: public(bool)
done_B1: public(bool)
done_B2: public(bool)
done_B3: public(bool)
claimed_Seller: public(bool)
claimed_B1: public(bool)
claimed_B2: public(bool)
claimed_B3: public(bool)
B1_b: public(int256)
done_B1_b: public(bool)
B1_b_hidden: public(bytes32)
done_B1_b_hidden: public(bool)
B2_b: public(int256)
done_B2_b: public(bool)
B2_b_hidden: public(bytes32)
done_B2_b_hidden: public(bool)
B3_b: public(int256)
done_B3_b: public(bool)
B3_b_hidden: public(bytes32)
done_B3_b_hidden: public(bool)
TIMEOUT: public(constant(uint256)) = 86400
NODE_COUNT: public(constant(uint256)) = 10
deployedAt: public(immutable(uint256))
COMMIT_TAG: immutable(bytes32)
# Readiness time of each node: when its last predecessor resolved (0 = not ready).
readyAt: public(HashMap[uint256, uint256])
# Resolution time of each node: when it was played, or resolved without a value (0 = unresolved).
resolvedAt: public(HashMap[uint256, uint256])
# When a role quit: the deadline it missed (0 = active). Quitting is persistent.
quitAt: public(HashMap[Role, uint256])
# Set when a role failed to join: play never starts and deposits are refunded.
aborted: public(bool)
# Every node below this position is resolved.
settledPrefix: public(uint256)

@deploy
def __init__():
    deployedAt = block.timestamp
    COMMIT_TAG = keccak256("VEGAS_COMMIT_V1")

@internal
@view
def _owner(i: uint256) -> Role:
    if i == 0:
        return Role.B1
    if i == 1:
        return Role.B2
    if i == 2:
        return Role.B3
    if i == 3:
        return Role.Seller
    if i == 4:
        return Role.B1
    if i == 5:
        return Role.B2
    if i == 6:
        return Role.B3
    if i == 7:
        return Role.B1
    if i == 8:
        return Role.B2
    return Role.B3

@internal
@view
def _predecessors(i: uint256) -> uint256:
    if i == 0:
        return 0
    if i == 1:
        return 0
    if i == 2:
        return 0
    if i == 3:
        return 0
    if i == 4:
        return 15
    if i == 5:
        return 15
    if i == 6:
        return 15
    if i == 7:
        return 127
    if i == 8:
        return 255
    return 511

@internal
@view
def _isJoin(i: uint256) -> bool:
    if i == 0:
        return True
    if i == 1:
        return True
    if i == 2:
        return True
    if i == 3:
        return True
    if i == 4:
        return False
    if i == 5:
        return False
    if i == 6:
        return False
    if i == 7:
        return False
    if i == 8:
        return False
    return False

# Resolve every node that can be resolved now. Anyone may call this.
@external
def settle():
    self._settle()

@internal
def _settle():
    start: uint256 = self.settledPrefix
    prefix: uint256 = start
    contiguous: bool = True
    for i: uint256 in range(start, NODE_COUNT, bound=NODE_COUNT):
        if self.resolvedAt[i] == 0:
            self._resolve(i)
        if contiguous and self.resolvedAt[i] != 0:
            prefix = i + 1
        else:
            contiguous = False
    self.settledPrefix = prefix

@internal
@view
def _readiness(i: uint256) -> uint256:
    ready: uint256 = deployedAt
    predecessors: uint256 = self._predecessors(i)
    for j: uint256 in range(NODE_COUNT):
        if j >= i:
            break
        if (predecessors >> j) & 1 == 1:
            t: uint256 = self.resolvedAt[j]
            if t == 0:
                return 0
            if t > ready:
                ready = t
    return ready

@internal
def _resolve(i: uint256):
    ready: uint256 = self.readyAt[i]
    if ready == 0:
        ready = self._readiness(i)
        if ready == 0:
            return
        self.readyAt[i] = ready
    if self.aborted:
        self.resolvedAt[i] = ready
        return
    owner: Role = self._owner(i)
    quit: uint256 = self.quitAt[owner]
    if quit != 0:
        self.resolvedAt[i] = max(quit, ready)
        return
    if block.timestamp > ready + TIMEOUT:
        self.quitAt[owner] = ready + TIMEOUT
        self.resolvedAt[i] = ready + TIMEOUT
        if self._isJoin(i):
            self.aborted = True

# Settle, then require that node i is ready, unresolved, and owned by the caller's role.
@internal
def _beginMove(i: uint256, role: Role):
    self._settle()
    assert self.roles[msg.sender] == role, "bad role"
    assert self.readyAt[i] != 0, "not ready"
    assert self.resolvedAt[i] == 0, "not open"

@internal
def _endMove(i: uint256):
    self.resolvedAt[i] = block.timestamp

@external
@payable
def move_B1_0():
    self._beginMove(0, empty(Role))
    assert (not self.done_B1), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.B1
    self.address_B1 = msg.sender
    self.done_B1 = True
    self._endMove(0)

@external
@payable
def move_B2_1():
    self._beginMove(1, empty(Role))
    assert (not self.done_B2), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.B2
    self.address_B2 = msg.sender
    self.done_B2 = True
    self._endMove(1)

@external
@payable
def move_B3_2():
    self._beginMove(2, empty(Role))
    assert (not self.done_B3), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.B3
    self.address_B3 = msg.sender
    self.done_B3 = True
    self._endMove(2)

@external
@payable
def move_Seller_3():
    self._beginMove(3, empty(Role))
    assert (not self.done_Seller), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.Seller
    self.address_Seller = msg.sender
    self.done_Seller = True
    self._endMove(3)

@external
def move_B1_4(_hidden_b: bytes32):
    self._beginMove(4, Role.B1)
    self.B1_b_hidden = _hidden_b
    self.done_B1_b_hidden = True
    self._endMove(4)

@external
def move_B2_5(_hidden_b: bytes32):
    self._beginMove(5, Role.B2)
    self.B2_b_hidden = _hidden_b
    self.done_B2_b_hidden = True
    self._endMove(5)

@external
def move_B3_6(_hidden_b: bytes32):
    self._beginMove(6, Role.B3)
    self.B3_b_hidden = _hidden_b
    self.done_B3_b_hidden = True
    self._endMove(6)

@external
def move_B1_7(_b: int256, _salt: uint256):
    self._beginMove(7, Role.B1)
    assert ((_b >= 0) and (_b <= 2)), "domain"
    self._checkReveal(self.B1_b_hidden, Role.B1, msg.sender, abi_encode(_b, _salt))
    self.B1_b = _b
    self.done_B1_b = True
    self._endMove(7)

@external
def move_B2_8(_b: int256, _salt: uint256):
    self._beginMove(8, Role.B2)
    assert ((_b >= 0) and (_b <= 2)), "domain"
    self._checkReveal(self.B2_b_hidden, Role.B2, msg.sender, abi_encode(_b, _salt))
    self.B2_b = _b
    self.done_B2_b = True
    self._endMove(8)

@external
def move_B3_9(_b: int256, _salt: uint256):
    self._beginMove(9, Role.B3)
    assert ((_b >= 0) and (_b <= 2)), "domain"
    self._checkReveal(self.B3_b_hidden, Role.B3, msg.sender, abi_encode(_b, _salt))
    self.B3_b = _b
    self.done_B3_b = True
    self._endMove(9)

@external
def withdraw_Seller():
    self._settle()
    assert self.roles[msg.sender] == Role.Seller, "bad role"
    assert not self.claimed_Seller, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 100 if self.done_Seller else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((100 + (((((0 if True else 100) + (0 if self.done_B1_b else 100)) + (0 if self.done_B2_b else 100)) + (0 if self.done_B3_b else 100)) // (((((1 if True else 0) + (1 if self.done_B1_b else 0)) + (1 if self.done_B2_b else 0)) + (1 if self.done_B3_b else 0)) if (((((1 if True else 0) + (1 if self.done_B1_b else 0)) + (1 if self.done_B2_b else 0)) + (1 if self.done_B3_b else 0)) > 0) else 1))) if True else 0) if (((not self.done_B1_b) or (not self.done_B2_b)) or (not self.done_B3_b)) else (100 + ((self.B2_b if (self.B2_b >= self.B3_b) else self.B3_b) if (self.B1_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else ((self.B1_b if (self.B1_b >= self.B3_b) else self.B3_b) if (self.B2_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b)))))
    self.claimed_Seller = True
    if payout > 0:
        success: bool = raw_call(self.address_Seller, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_B1():
    self._settle()
    assert self.roles[msg.sender] == Role.B1, "bad role"
    assert not self.claimed_B1, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 100 if self.done_B1 else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((100 + (((((0 if True else 100) + (0 if self.done_B1_b else 100)) + (0 if self.done_B2_b else 100)) + (0 if self.done_B3_b else 100)) // (((((1 if True else 0) + (1 if self.done_B1_b else 0)) + (1 if self.done_B2_b else 0)) + (1 if self.done_B3_b else 0)) if (((((1 if True else 0) + (1 if self.done_B1_b else 0)) + (1 if self.done_B2_b else 0)) + (1 if self.done_B3_b else 0)) > 0) else 1))) if self.done_B1_b else 0) if (((not self.done_B1_b) or (not self.done_B2_b)) or (not self.done_B3_b)) else ((100 - ((self.B2_b if (self.B2_b >= self.B3_b) else self.B3_b) if (self.B1_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else ((self.B1_b if (self.B1_b >= self.B3_b) else self.B3_b) if (self.B2_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b)))) if (self.B1_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else 100))
    self.claimed_B1 = True
    if payout > 0:
        success: bool = raw_call(self.address_B1, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_B2():
    self._settle()
    assert self.roles[msg.sender] == Role.B2, "bad role"
    assert not self.claimed_B2, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 100 if self.done_B2 else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((100 + (((((0 if True else 100) + (0 if self.done_B1_b else 100)) + (0 if self.done_B2_b else 100)) + (0 if self.done_B3_b else 100)) // (((((1 if True else 0) + (1 if self.done_B1_b else 0)) + (1 if self.done_B2_b else 0)) + (1 if self.done_B3_b else 0)) if (((((1 if True else 0) + (1 if self.done_B1_b else 0)) + (1 if self.done_B2_b else 0)) + (1 if self.done_B3_b else 0)) > 0) else 1))) if self.done_B2_b else 0) if (((not self.done_B1_b) or (not self.done_B2_b)) or (not self.done_B3_b)) else ((100 - ((self.B2_b if (self.B2_b >= self.B3_b) else self.B3_b) if (self.B1_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else ((self.B1_b if (self.B1_b >= self.B3_b) else self.B3_b) if (self.B2_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b)))) if (self.B2_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else 100))
    self.claimed_B2 = True
    if payout > 0:
        success: bool = raw_call(self.address_B2, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_B3():
    self._settle()
    assert self.roles[msg.sender] == Role.B3, "bad role"
    assert not self.claimed_B3, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 100 if self.done_B3 else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((100 + (((((0 if True else 100) + (0 if self.done_B1_b else 100)) + (0 if self.done_B2_b else 100)) + (0 if self.done_B3_b else 100)) // (((((1 if True else 0) + (1 if self.done_B1_b else 0)) + (1 if self.done_B2_b else 0)) + (1 if self.done_B3_b else 0)) if (((((1 if True else 0) + (1 if self.done_B1_b else 0)) + (1 if self.done_B2_b else 0)) + (1 if self.done_B3_b else 0)) > 0) else 1))) if self.done_B3_b else 0) if (((not self.done_B1_b) or (not self.done_B2_b)) or (not self.done_B3_b)) else ((100 - ((self.B2_b if (self.B2_b >= self.B3_b) else self.B3_b) if (self.B1_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else ((self.B1_b if (self.B1_b >= self.B3_b) else self.B3_b) if (self.B2_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else (self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b)))) if (self.B3_b == ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) if ((self.B1_b if (self.B1_b >= self.B2_b) else self.B2_b) >= self.B3_b) else self.B3_b)) else 100))
    self.claimed_B3 = True
    if payout > 0:
        success: bool = raw_call(self.address_B3, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@payable
@external
def __default__():
    assert False, "direct ETH not allowed"

@internal
@view
def _checkReveal(commitment: bytes32, role: Role, actor: address, payload: Bytes[256]):
    expected: bytes32 = keccak256(abi_encode(COMMIT_TAG, self, role, actor, keccak256(payload)))
    assert expected == commitment, "bad reveal"

