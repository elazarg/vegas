#pragma version ^0.4.3

flag Role:
    Odd
    Even

ACTION_Even_0: public(constant(uint256)) = 0
ACTION_Odd_0: public(constant(uint256)) = 1
ACTION_Odd_2: public(constant(uint256)) = 2
ACTION_Even_4: public(constant(uint256)) = 3
ACTION_Odd_3: public(constant(uint256)) = 4
ACTION_Even_5: public(constant(uint256)) = 5
roles: public(HashMap[address, Role])
address_Odd: public(address)
address_Even: public(address)
done_Odd: public(bool)
done_Even: public(bool)
claimed_Odd: public(bool)
claimed_Even: public(bool)
Odd_c: public(bool)
done_Odd_c: public(bool)
Odd_c_hidden: public(bytes32)
done_Odd_c_hidden: public(bool)
Even_c: public(bool)
done_Even_c: public(bool)
Even_c_hidden: public(bytes32)
done_Even_c_hidden: public(bool)
TIMEOUT: public(constant(uint256)) = 86400
NODE_COUNT: public(constant(uint256)) = 6
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
        return Role.Even
    if i == 1:
        return Role.Odd
    if i == 2:
        return Role.Odd
    if i == 3:
        return Role.Even
    if i == 4:
        return Role.Odd
    return Role.Even

@internal
@view
def _predecessors(i: uint256) -> uint256:
    if i == 0:
        return 0
    if i == 1:
        return 0
    if i == 2:
        return 3
    if i == 3:
        return 3
    if i == 4:
        return 15
    return 31

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
def move_Even_0():
    self._beginMove(0, empty(Role))
    assert (not self.done_Even), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.Even
    self.address_Even = msg.sender
    self.done_Even = True
    self._endMove(0)

@external
@payable
def move_Odd_1():
    self._beginMove(1, empty(Role))
    assert (not self.done_Odd), "already joined"
    assert (msg.value == 100), "bad stake"
    self.roles[msg.sender] = Role.Odd
    self.address_Odd = msg.sender
    self.done_Odd = True
    self._endMove(1)

@external
def move_Odd_2(_hidden_c: bytes32):
    self._beginMove(2, Role.Odd)
    self.Odd_c_hidden = _hidden_c
    self.done_Odd_c_hidden = True
    self._endMove(2)

@external
def move_Even_3(_hidden_c: bytes32):
    self._beginMove(3, Role.Even)
    self.Even_c_hidden = _hidden_c
    self.done_Even_c_hidden = True
    self._endMove(3)

@external
def move_Odd_4(_c: bool, _salt: uint256):
    self._beginMove(4, Role.Odd)
    self._checkReveal(self.Odd_c_hidden, Role.Odd, msg.sender, abi_encode(_c, _salt))
    self.Odd_c = _c
    self.done_Odd_c = True
    self._endMove(4)

@external
def move_Even_5(_c: bool, _salt: uint256):
    self._beginMove(5, Role.Even)
    self._checkReveal(self.Even_c_hidden, Role.Even, msg.sender, abi_encode(_c, _salt))
    self.Even_c = _c
    self.done_Even_c = True
    self._endMove(5)

@external
def withdraw_Odd():
    self._settle()
    assert self.roles[msg.sender] == Role.Odd, "bad role"
    assert not self.claimed_Odd, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 100 if self.done_Odd else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((100 + (((0 if self.done_Odd_c else 100) + (0 if self.done_Even_c else 100)) // (((1 if self.done_Odd_c else 0) + (1 if self.done_Even_c else 0)) if (((1 if self.done_Odd_c else 0) + (1 if self.done_Even_c else 0)) > 0) else 1))) if self.done_Odd_c else 0) if ((not self.done_Odd_c) or (not self.done_Even_c)) else (74 if (self.Even_c == self.Odd_c) else 126))
    self.claimed_Odd = True
    if payout > 0:
        success: bool = raw_call(self.address_Odd, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_Even():
    self._settle()
    assert self.roles[msg.sender] == Role.Even, "bad role"
    assert not self.claimed_Even, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 100 if self.done_Even else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((100 + (((0 if self.done_Odd_c else 100) + (0 if self.done_Even_c else 100)) // (((1 if self.done_Odd_c else 0) + (1 if self.done_Even_c else 0)) if (((1 if self.done_Odd_c else 0) + (1 if self.done_Even_c else 0)) > 0) else 1))) if self.done_Even_c else 0) if ((not self.done_Odd_c) or (not self.done_Even_c)) else (126 if (self.Even_c == self.Odd_c) else 74))
    self.claimed_Even = True
    if payout > 0:
        success: bool = raw_call(self.address_Even, b"", value=convert(payout, uint256), revert_on_failure=False)
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

