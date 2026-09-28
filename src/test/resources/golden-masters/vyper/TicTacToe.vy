#pragma version ^0.4.3

flag Role:
    X
    O

ACTION_X_0: public(constant(uint256)) = 0
ACTION_O_1: public(constant(uint256)) = 1
ACTION_X_2: public(constant(uint256)) = 2
ACTION_O_3: public(constant(uint256)) = 3
ACTION_X_4: public(constant(uint256)) = 4
ACTION_O_5: public(constant(uint256)) = 5
ACTION_X_6: public(constant(uint256)) = 6
ACTION_O_7: public(constant(uint256)) = 7
ACTION_X_8: public(constant(uint256)) = 8
ACTION_O_9: public(constant(uint256)) = 9
roles: public(HashMap[address, Role])
address_X: public(address)
address_O: public(address)
done_X: public(bool)
done_O: public(bool)
claimed_X: public(bool)
claimed_O: public(bool)
X_c1: public(int256)
done_X_c1: public(bool)
O_c1: public(int256)
done_O_c1: public(bool)
X_c2: public(int256)
done_X_c2: public(bool)
O_c2: public(int256)
done_O_c2: public(bool)
X_c3: public(int256)
done_X_c3: public(bool)
O_c3: public(int256)
done_O_c3: public(bool)
X_c4: public(int256)
done_X_c4: public(bool)
O_c4: public(int256)
done_O_c4: public(bool)
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
        return Role.X
    if i == 1:
        return Role.O
    if i == 2:
        return Role.X
    if i == 3:
        return Role.O
    if i == 4:
        return Role.X
    if i == 5:
        return Role.O
    if i == 6:
        return Role.X
    if i == 7:
        return Role.O
    if i == 8:
        return Role.X
    return Role.O

@internal
@view
def _predecessors(i: uint256) -> uint256:
    if i == 0:
        return 0
    if i == 1:
        return 1
    if i == 2:
        return 2
    if i == 3:
        return 4
    if i == 4:
        return 12
    if i == 5:
        return 28
    if i == 6:
        return 60
    if i == 7:
        return 124
    if i == 8:
        return 252
    return 508

@internal
@view
def _isJoin(i: uint256) -> bool:
    if i == 0:
        return True
    if i == 1:
        return True
    if i == 2:
        return False
    if i == 3:
        return False
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
def move_X_0():
    self._beginMove(0, empty(Role))
    assert (not self.done_X), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.X
    self.address_X = msg.sender
    self.done_X = True
    self._endMove(0)

@external
@payable
def move_O_1():
    self._beginMove(1, empty(Role))
    assert (not self.done_O), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.O
    self.address_O = msg.sender
    self.done_O = True
    self._endMove(1)

@external
def move_X_2(_c1: int256):
    self._beginMove(2, Role.X)
    assert ((_c1 >= 0) and (_c1 <= 8)), "domain"
    self.X_c1 = _c1
    self.done_X_c1 = True
    self._endMove(2)

@external
def move_O_3(_c1: int256):
    self._beginMove(3, Role.O)
    assert ((_c1 >= 0) and (_c1 <= 8)), "domain"
    assert ((not self.done_X_c1) or (self.X_c1 != _c1)), "domain"
    self.O_c1 = _c1
    self.done_O_c1 = True
    self._endMove(3)

@external
def move_X_4(_c2: int256):
    self._beginMove(4, Role.X)
    assert ((_c2 >= 0) and (_c2 <= 8)), "domain"
    assert ((not self.done_O_c1) or (((self.X_c1 != self.O_c1) and (self.X_c1 != _c2)) and (self.O_c1 != _c2))), "domain"
    self.X_c2 = _c2
    self.done_X_c2 = True
    self._endMove(4)

@external
def move_O_5(_c2: int256):
    self._beginMove(5, Role.O)
    assert ((_c2 >= 0) and (_c2 <= 8)), "domain"
    assert (((not self.done_X_c1) or (not self.done_X_c2)) or ((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != _c2)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != _c2)) and (self.X_c2 != _c2))), "domain"
    self.O_c2 = _c2
    self.done_O_c2 = True
    self._endMove(5)

@external
def move_X_6(_c3: int256):
    self._beginMove(6, Role.X)
    assert ((_c3 >= 0) and (_c3 <= 8)), "domain"
    assert (((not self.done_O_c1) or (not self.done_O_c2)) or ((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != _c3)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != _c3)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != _c3)) and (self.O_c2 != _c3))), "domain"
    self.X_c3 = _c3
    self.done_X_c3 = True
    self._endMove(6)

@external
def move_O_7(_c3: int256):
    self._beginMove(7, Role.O)
    assert ((_c3 >= 0) and (_c3 <= 8)), "domain"
    assert ((((not self.done_X_c1) or (not self.done_X_c2)) or (not self.done_X_c3)) or (((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != _c3)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != _c3)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != _c3)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != _c3)) and (self.X_c3 != _c3))), "domain"
    self.O_c3 = _c3
    self.done_O_c3 = True
    self._endMove(7)

@external
def move_X_8(_c4: int256):
    self._beginMove(8, Role.X)
    assert ((_c4 >= 0) and (_c4 <= 8)), "domain"
    assert ((((not self.done_O_c1) or (not self.done_O_c2)) or (not self.done_O_c3)) or (((((((((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != self.O_c3)) and (self.X_c1 != _c4)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != self.O_c3)) and (self.O_c1 != _c4)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != self.O_c3)) and (self.X_c2 != _c4)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != self.O_c3)) and (self.O_c2 != _c4)) and (self.X_c3 != self.O_c3)) and (self.X_c3 != _c4)) and (self.O_c3 != _c4))), "domain"
    self.X_c4 = _c4
    self.done_X_c4 = True
    self._endMove(8)

@external
def move_O_9(_c4: int256):
    self._beginMove(9, Role.O)
    assert ((_c4 >= 0) and (_c4 <= 8)), "domain"
    assert (((((not self.done_X_c1) or (not self.done_X_c2)) or (not self.done_X_c3)) or (not self.done_X_c4)) or ((((((((((((((((((((((((((((self.X_c1 != self.O_c1) and (self.X_c1 != self.X_c2)) and (self.X_c1 != self.O_c2)) and (self.X_c1 != self.X_c3)) and (self.X_c1 != self.O_c3)) and (self.X_c1 != self.X_c4)) and (self.X_c1 != _c4)) and (self.O_c1 != self.X_c2)) and (self.O_c1 != self.O_c2)) and (self.O_c1 != self.X_c3)) and (self.O_c1 != self.O_c3)) and (self.O_c1 != self.X_c4)) and (self.O_c1 != _c4)) and (self.X_c2 != self.O_c2)) and (self.X_c2 != self.X_c3)) and (self.X_c2 != self.O_c3)) and (self.X_c2 != self.X_c4)) and (self.X_c2 != _c4)) and (self.O_c2 != self.X_c3)) and (self.O_c2 != self.O_c3)) and (self.O_c2 != self.X_c4)) and (self.O_c2 != _c4)) and (self.X_c3 != self.O_c3)) and (self.X_c3 != self.X_c4)) and (self.X_c3 != _c4)) and (self.O_c3 != self.X_c4)) and (self.O_c3 != _c4)) and (self.X_c4 != _c4))), "domain"
    self.O_c4 = _c4
    self.done_O_c4 = True
    self._endMove(9)

@external
def withdraw_X():
    self._settle()
    assert self.roles[msg.sender] == Role.X, "bad role"
    assert not self.claimed_X, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 100 if self.done_X else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((100 + (((0 if self.done_X_c1 else 100) + (0 if True else 100)) // (((1 if self.done_X_c1 else 0) + (1 if True else 0)) if (((1 if self.done_X_c1 else 0) + (1 if True else 0)) > 0) else 1))) if self.done_X_c1 else 0) if (not self.done_X_c1) else (((100 + (((0 if self.done_X_c1 else 100) + (0 if self.done_O_c1 else 100)) // (((1 if self.done_X_c1 else 0) + (1 if self.done_O_c1 else 0)) if (((1 if self.done_X_c1 else 0) + (1 if self.done_O_c1 else 0)) > 0) else 1))) if self.done_X_c1 else 0) if (not self.done_O_c1) else (((100 + (((0 if (self.done_X_c1 and self.done_X_c2) else 100) + (0 if self.done_O_c1 else 100)) // (((1 if (self.done_X_c1 and self.done_X_c2) else 0) + (1 if self.done_O_c1 else 0)) if (((1 if (self.done_X_c1 and self.done_X_c2) else 0) + (1 if self.done_O_c1 else 0)) > 0) else 1))) if (self.done_X_c1 and self.done_X_c2) else 0) if (not self.done_X_c2) else (((100 + (((0 if (self.done_X_c1 and self.done_X_c2) else 100) + (0 if (self.done_O_c1 and self.done_O_c2) else 100)) // (((1 if (self.done_X_c1 and self.done_X_c2) else 0) + (1 if (self.done_O_c1 and self.done_O_c2) else 0)) if (((1 if (self.done_X_c1 and self.done_X_c2) else 0) + (1 if (self.done_O_c1 and self.done_O_c2) else 0)) > 0) else 1))) if (self.done_X_c1 and self.done_X_c2) else 0) if (not self.done_O_c2) else (((100 + (((0 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 100) + (0 if (self.done_O_c1 and self.done_O_c2) else 100)) // (((1 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) + (1 if (self.done_O_c1 and self.done_O_c2) else 0)) if (((1 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) + (1 if (self.done_O_c1 and self.done_O_c2) else 0)) > 0) else 1))) if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) if (not self.done_X_c3) else (((100 + (((0 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 100) + (0 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 100)) // (((1 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) + (1 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0)) if (((1 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) + (1 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0)) > 0) else 1))) if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) if (not self.done_O_c3) else (((100 + (((0 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 100) + (0 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 100)) // (((1 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) + (1 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0)) if (((1 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) + (1 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0)) > 0) else 1))) if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) if (not self.done_X_c4) else (((100 + (((0 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 100) + (0 if (((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) and self.done_O_c4) else 100)) // (((1 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) + (1 if (((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) and self.done_O_c4) else 0)) if (((1 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) + (1 if (((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) and self.done_O_c4) else 0)) > 0) else 1))) if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) if (not self.done_O_c4) else 100))))))))
    self.claimed_X = True
    if payout > 0:
        success: bool = raw_call(self.address_X, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_O():
    self._settle()
    assert self.roles[msg.sender] == Role.O, "bad role"
    assert not self.claimed_O, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 100 if self.done_O else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((100 + (((0 if self.done_X_c1 else 100) + (0 if True else 100)) // (((1 if self.done_X_c1 else 0) + (1 if True else 0)) if (((1 if self.done_X_c1 else 0) + (1 if True else 0)) > 0) else 1))) if True else 0) if (not self.done_X_c1) else (((100 + (((0 if self.done_X_c1 else 100) + (0 if self.done_O_c1 else 100)) // (((1 if self.done_X_c1 else 0) + (1 if self.done_O_c1 else 0)) if (((1 if self.done_X_c1 else 0) + (1 if self.done_O_c1 else 0)) > 0) else 1))) if self.done_O_c1 else 0) if (not self.done_O_c1) else (((100 + (((0 if (self.done_X_c1 and self.done_X_c2) else 100) + (0 if self.done_O_c1 else 100)) // (((1 if (self.done_X_c1 and self.done_X_c2) else 0) + (1 if self.done_O_c1 else 0)) if (((1 if (self.done_X_c1 and self.done_X_c2) else 0) + (1 if self.done_O_c1 else 0)) > 0) else 1))) if self.done_O_c1 else 0) if (not self.done_X_c2) else (((100 + (((0 if (self.done_X_c1 and self.done_X_c2) else 100) + (0 if (self.done_O_c1 and self.done_O_c2) else 100)) // (((1 if (self.done_X_c1 and self.done_X_c2) else 0) + (1 if (self.done_O_c1 and self.done_O_c2) else 0)) if (((1 if (self.done_X_c1 and self.done_X_c2) else 0) + (1 if (self.done_O_c1 and self.done_O_c2) else 0)) > 0) else 1))) if (self.done_O_c1 and self.done_O_c2) else 0) if (not self.done_O_c2) else (((100 + (((0 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 100) + (0 if (self.done_O_c1 and self.done_O_c2) else 100)) // (((1 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) + (1 if (self.done_O_c1 and self.done_O_c2) else 0)) if (((1 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) + (1 if (self.done_O_c1 and self.done_O_c2) else 0)) > 0) else 1))) if (self.done_O_c1 and self.done_O_c2) else 0) if (not self.done_X_c3) else (((100 + (((0 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 100) + (0 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 100)) // (((1 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) + (1 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0)) if (((1 if ((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) else 0) + (1 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0)) > 0) else 1))) if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0) if (not self.done_O_c3) else (((100 + (((0 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 100) + (0 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 100)) // (((1 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) + (1 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0)) if (((1 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) + (1 if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0)) > 0) else 1))) if ((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) else 0) if (not self.done_X_c4) else (((100 + (((0 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 100) + (0 if (((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) and self.done_O_c4) else 100)) // (((1 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) + (1 if (((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) and self.done_O_c4) else 0)) if (((1 if (((self.done_X_c1 and self.done_X_c2) and self.done_X_c3) and self.done_X_c4) else 0) + (1 if (((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) and self.done_O_c4) else 0)) > 0) else 1))) if (((self.done_O_c1 and self.done_O_c2) and self.done_O_c3) and self.done_O_c4) else 0) if (not self.done_O_c4) else 100))))))))
    self.claimed_O = True
    if payout > 0:
        success: bool = raw_call(self.address_O, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@payable
@external
def __default__():
    assert False, "direct ETH not allowed"

