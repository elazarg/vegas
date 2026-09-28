#pragma version ^0.4.3

flag Role:
    Host
    Guest

ACTION_Host_0: public(constant(uint256)) = 0
ACTION_Guest_1: public(constant(uint256)) = 1
ACTION_Host_2: public(constant(uint256)) = 2
ACTION_Guest_3: public(constant(uint256)) = 3
ACTION_Host_4: public(constant(uint256)) = 4
ACTION_Guest_5: public(constant(uint256)) = 5
ACTION_Host_6: public(constant(uint256)) = 6
roles: public(HashMap[address, Role])
address_Host: public(address)
address_Guest: public(address)
done_Host: public(bool)
done_Guest: public(bool)
claimed_Host: public(bool)
claimed_Guest: public(bool)
Host_car: public(int256)
done_Host_car: public(bool)
Host_car_hidden: public(bytes32)
done_Host_car_hidden: public(bool)
Guest_d: public(int256)
done_Guest_d: public(bool)
Host_goat: public(int256)
done_Host_goat: public(bool)
Guest_switch: public(bool)
done_Guest_switch: public(bool)
TIMEOUT: public(constant(uint256)) = 86400
NODE_COUNT: public(constant(uint256)) = 7
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
        return Role.Host
    if i == 1:
        return Role.Guest
    if i == 2:
        return Role.Host
    if i == 3:
        return Role.Guest
    if i == 4:
        return Role.Host
    if i == 5:
        return Role.Guest
    return Role.Host

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
        return 8
    if i == 5:
        return 16
    return 52

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
def move_Host_0():
    self._beginMove(0, empty(Role))
    assert (not self.done_Host), "already joined"
    assert (msg.value == 20), "bad stake"
    self.roles[msg.sender] = Role.Host
    self.address_Host = msg.sender
    self.done_Host = True
    self._endMove(0)

@external
@payable
def move_Guest_1():
    self._beginMove(1, empty(Role))
    assert (not self.done_Guest), "already joined"
    assert (msg.value == 20), "bad stake"
    self.roles[msg.sender] = Role.Guest
    self.address_Guest = msg.sender
    self.done_Guest = True
    self._endMove(1)

@external
def move_Host_2(_hidden_car: bytes32):
    self._beginMove(2, Role.Host)
    self.Host_car_hidden = _hidden_car
    self.done_Host_car_hidden = True
    self._endMove(2)

@external
def move_Guest_3(_d: int256):
    self._beginMove(3, Role.Guest)
    assert ((_d >= 0) and (_d <= 2)), "domain"
    self.Guest_d = _d
    self.done_Guest_d = True
    self._endMove(3)

@external
def move_Host_4(_goat: int256):
    self._beginMove(4, Role.Host)
    assert ((_goat >= 0) and (_goat <= 2)), "domain"
    assert ((not self.done_Guest_d) or (_goat != self.Guest_d)), "domain"
    self.Host_goat = _goat
    self.done_Host_goat = True
    self._endMove(4)

@external
def move_Guest_5(_switch: bool):
    self._beginMove(5, Role.Guest)
    self.Guest_switch = _switch
    self.done_Guest_switch = True
    self._endMove(5)

@external
def move_Host_6(_car: int256, _salt: uint256):
    self._beginMove(6, Role.Host)
    assert ((_car >= 0) and (_car <= 2)), "domain"
    assert (self.Host_goat != _car), "domain"
    self._checkReveal(self.Host_car_hidden, Role.Host, msg.sender, abi_encode(_car, _salt))
    self.Host_car = _car
    self.done_Host_car = True
    self._endMove(6)

@external
def withdraw_Host():
    self._settle()
    assert self.roles[msg.sender] == Role.Host, "bad role"
    assert not self.claimed_Host, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 20 if self.done_Host else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((20 + (((0 if self.done_Host_car else 20) + (0 if True else 20)) // (((1 if self.done_Host_car else 0) + (1 if True else 0)) if (((1 if self.done_Host_car else 0) + (1 if True else 0)) > 0) else 1))) if self.done_Host_car else 0) if (not self.done_Host_car) else (((20 + (((0 if self.done_Host_car else 20) + (0 if self.done_Guest_d else 20)) // (((1 if self.done_Host_car else 0) + (1 if self.done_Guest_d else 0)) if (((1 if self.done_Host_car else 0) + (1 if self.done_Guest_d else 0)) > 0) else 1))) if self.done_Host_car else 0) if (not self.done_Guest_d) else (((20 + (((0 if (self.done_Host_car and self.done_Host_goat) else 20) + (0 if self.done_Guest_d else 20)) // (((1 if (self.done_Host_car and self.done_Host_goat) else 0) + (1 if self.done_Guest_d else 0)) if (((1 if (self.done_Host_car and self.done_Host_goat) else 0) + (1 if self.done_Guest_d else 0)) > 0) else 1))) if (self.done_Host_car and self.done_Host_goat) else 0) if (not self.done_Host_goat) else (((20 + (((0 if (self.done_Host_car and self.done_Host_goat) else 20) + (0 if (self.done_Guest_d and self.done_Guest_switch) else 20)) // (((1 if (self.done_Host_car and self.done_Host_goat) else 0) + (1 if (self.done_Guest_d and self.done_Guest_switch) else 0)) if (((1 if (self.done_Host_car and self.done_Host_goat) else 0) + (1 if (self.done_Guest_d and self.done_Guest_switch) else 0)) > 0) else 1))) if (self.done_Host_car and self.done_Host_goat) else 0) if (not self.done_Guest_switch) else (0 if ((self.Guest_d != self.Host_car) == self.Guest_switch) else 40)))))
    self.claimed_Host = True
    if payout > 0:
        success: bool = raw_call(self.address_Host, b"", value=convert(payout, uint256), revert_on_failure=False)
        assert success, "ETH send failed"

@external
def withdraw_Guest():
    self._settle()
    assert self.roles[msg.sender] == Role.Guest, "bad role"
    assert not self.claimed_Guest, "already claimed"
    payout: int256 = 0
    if self.aborted:
        payout = 20 if self.done_Guest else 0
    else:
        assert self.settledPrefix == NODE_COUNT, "game not finished"
        payout = (((20 + (((0 if self.done_Host_car else 20) + (0 if True else 20)) // (((1 if self.done_Host_car else 0) + (1 if True else 0)) if (((1 if self.done_Host_car else 0) + (1 if True else 0)) > 0) else 1))) if True else 0) if (not self.done_Host_car) else (((20 + (((0 if self.done_Host_car else 20) + (0 if self.done_Guest_d else 20)) // (((1 if self.done_Host_car else 0) + (1 if self.done_Guest_d else 0)) if (((1 if self.done_Host_car else 0) + (1 if self.done_Guest_d else 0)) > 0) else 1))) if self.done_Guest_d else 0) if (not self.done_Guest_d) else (((20 + (((0 if (self.done_Host_car and self.done_Host_goat) else 20) + (0 if self.done_Guest_d else 20)) // (((1 if (self.done_Host_car and self.done_Host_goat) else 0) + (1 if self.done_Guest_d else 0)) if (((1 if (self.done_Host_car and self.done_Host_goat) else 0) + (1 if self.done_Guest_d else 0)) > 0) else 1))) if self.done_Guest_d else 0) if (not self.done_Host_goat) else (((20 + (((0 if (self.done_Host_car and self.done_Host_goat) else 20) + (0 if (self.done_Guest_d and self.done_Guest_switch) else 20)) // (((1 if (self.done_Host_car and self.done_Host_goat) else 0) + (1 if (self.done_Guest_d and self.done_Guest_switch) else 0)) if (((1 if (self.done_Host_car and self.done_Host_goat) else 0) + (1 if (self.done_Guest_d and self.done_Guest_switch) else 0)) > 0) else 1))) if (self.done_Guest_d and self.done_Guest_switch) else 0) if (not self.done_Guest_switch) else (40 if ((self.Guest_d != self.Host_car) == self.Guest_switch) else 0)))))
    self.claimed_Guest = True
    if payout > 0:
        success: bool = raw_call(self.address_Guest, b"", value=convert(payout, uint256), revert_on_failure=False)
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

