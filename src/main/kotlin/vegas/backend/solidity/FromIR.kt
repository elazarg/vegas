package vegas.backend.solidity

import vegas.RoleId
import vegas.VarId
import vegas.FieldRef
import vegas.ir.*

val NO_ROLE = RoleId("None")

/**
 * Defines the context in which an IR expression is being translated.
 * - WHERE_CLAUSE: Reading from function inputs and current storage.
 * - PAYOFF: Reading from final, post-game storage.
 */
private enum class ExprContext { WHERE_CLAUSE, PAYOFF }

fun genSolidityFromIR(g: GameIR): String {
    val solAst = irToSolidity(expandCommitReveal(g))
    return renderSolidityContract(solAst)
}

/**
 * Main entry: translate IR to a SolidityContract AST.
 */
fun irToSolidity(g: GameIR): SolidityContract {
    val history = ParamHistory(g)
    val finalPhase = g.phases.size

    // ---- Constructor: set lastTs = block.timestamp
    val ctor = Constructor(
        body = listOf(
            // lastTs = block.timestamp;
            Statement.Assign(
                lhs = SolExpr.Var(LAST_TS_VAR),
                rhs = SolExpr.Member(SolExpr.Var("block"), "timestamp")
            )
        )
    )

    // ---- Role enum (None + all roles)
    val roleEnum = EnumDecl(
        name = ROLE_ENUM,
        values = (listOf(NO_ROLE) + g.roles + g.chanceRoles).map { it.name }
    )

    // ---- Storage (timing, role/balance, per-field state, payoff state)
    val storage = buildGameStorage(g)

    // ---- Modifiers
    val modifiers = mutableListOf(
        // modifier at_phase(uint _phase) { require(phase == _phase); /* timers removed */ _; }
        ModifierDecl(
            name = "at_phase",
            params = listOf(Param(SolType.Uint256, "_phase")),
            body = listOf(
                require(v(PHASE_VAR) eq v("_phase"), "wrong phase")
                // (Timer logic removed to match goldens)
            )
        ),
        // modifier by(Role r) { require(role[msg.sender] == r, "bad role"); _; }
        ModifierDecl(
            name = "by",
            params = listOf(Param(SolType.EnumType(ROLE_ENUM), "r")),
            body = listOf(
                require(index(ROLE_MAPPING, msgSender) eq v("r"), "bad role")
            )
        ),
        // modifier at_final_phase() { require(phase == FINAL_PHASE && !payoffs_distributed); _; }
        ModifierDecl(
            name = "at_final_phase",
            params = emptyList(),
            body = listOf(
                require(v(PHASE_VAR) eq int(finalPhase), "game not over"),
                require(not(v("payoffs_distributed")), "payoffs already sent")
            )
        )
    )

    // ---- Functions
    val functions = buildList {
        // keccak helper (bool variant per goldens; can be extended)
        add(
            FunctionDecl(
                name = "keccak",
                params = listOf(Param(SolType.Bool, "x"), Param(SolType.Uint256, "salt")),
                visibility = Visibility.PUBLIC,
                stateMutability = StateMutability.PURE,
                modifiers = emptyList(),
                returns = listOf(Param(SolType.Bytes32, "out")),
                body = listOf(
                    ret(SolExpr.Keccak256(SolExpr.AbiEncodePacked(listOf(v("x"), v("salt")))))
                )
            )
        )

        // Phase blocks
        g.phases.forEachIndexed { phaseIdx, phase ->
            addAll(buildPhaseFunctions(g, phaseIdx, phase, history))
        }

        // Payoff distribution function
        add(buildPayoffFunction(g, history, finalPhase))

        // withdraw()
        add(buildWithdraw())
    }

    // ---- Events (one per phase “broadcast”)
    val events = g.phases.indices.map { i -> EventDecl(broadcastEvent(i)) }

    // ---- Fallback (reject stray ETH)
    val fallback = FallbackDecl(
        visibility = Visibility.PUBLIC, // rendered as `external`
        stateMutability = StateMutability.PAYABLE,
        body = listOf(Statement.Revert("direct ETH not allowed"))
    )

    return SolidityContract(
        name = g.name,
        constructor = ctor,
        enums = listOf(roleEnum),
        storage = storage,
        modifiers = modifiers,
        functions = functions,
        events = events,
        fallback = fallback
    )
}

/* ============================== Helpers =============================== */

private fun by(roleId: RoleId): ModifierCall = ModifierCall("by", listOf(role(roleId.name)))

/**
 * Tracks where each (role,param) first appears (commit) and where it is revealed.
 */
private class ParamHistory(g: GameIR) {
    private data class Occ(val phase: Int, val visible: Boolean)

    private val occ = mutableMapOf<FieldRef, MutableList<Occ>>()

    init {
        g.phases.forEachIndexed { p, phase ->
            phase.actions.forEach { (role, sig) ->
                sig.parameters.forEach { prm ->
                    occ.getOrPut(FieldRef(role, prm.name)) { mutableListOf() }
                        .add(Occ(p, prm.visible))
                }
            }
        }
    }

    /** Was the first time this param was defined a visible one? */
    fun wasDefinedVisible(role: RoleId, param: VarId): Boolean {
        val first = occ[FieldRef(role, param)]?.minByOrNull { it.phase }
        return first?.visible == true
    }

    /** Is this param hidden *in this phase* and revealed in a *future* phase? */
    private fun isRevealedLater(role: RoleId, param: VarId, phase: Int): Boolean {
        val xs = occ[FieldRef(role, param)] ?: return false
        val here = xs.find { it.phase == phase } ?: return false
        return !here.visible && xs.any { it.phase > phase && it.visible }
    }

    /** Does this signature contain *any* param that is hidden now but revealed *later*? */
    fun needsCommitReveal(role: RoleId, sig: Signature, phase: Int): Boolean {
        return sig.parameters.any { p -> isRevealedLater(role, p.name, phase) }
    }

    /** Is this param being revealed *in this phase*? (i.e., visible now, but was hidden first) */
    fun isReveal(role: RoleId, param: VarId, phase: Int): Boolean {
        val xs = occ[FieldRef(role, param)] ?: return false
        val first = xs.minByOrNull { it.phase } ?: return false
        val here = xs.find { it.phase == phase } ?: return false
        // It's a reveal if it's visible now, but its first definition was hidden
        return here.visible && !first.visible && phase > first.phase
    }
}

/** Build persistent storage for every param, done-flags, role addresses, and payoff state. */
private fun buildGameStorage(g: GameIR): List<StorageDecl> = buildList {
    // ---- Timing ----
    add(
        StorageDecl(
            type = SolType.Uint256,
            visibility = Visibility.PUBLIC,
            name = PHASE_TIME_CONST,
            constant = true,
            value = uint(500) // (per golden)
        )
    )
    add(StorageDecl(SolType.Uint256, Visibility.PUBLIC, PHASE_VAR))
    add(StorageDecl(SolType.Uint256, Visibility.PUBLIC, LAST_TS_VAR))

    // ---- Roles and Balances ----
    add(
        StorageDecl(
            type = SolType.Mapping(SolType.Address, SolType.EnumType(ROLE_ENUM)),
            visibility = Visibility.PUBLIC,
            name = ROLE_MAPPING
        )
    )
    add(
        StorageDecl(
            type = SolType.Mapping(SolType.Address, SolType.Int256),
            visibility = Visibility.PUBLIC,
            name = BALANCE_MAPPING
        )
    )
    // Add storage for player addresses
    g.roles.forEach { role ->
        add(StorageDecl(SolType.Address, Visibility.PUBLIC, roleAddr(role)))
    }
    g.chanceRoles.forEach { role ->
        add(StorageDecl(SolType.Address, Visibility.PUBLIC, roleAddr(role)))
    }
    // Add flag to ensure payoffs are only sent once
    add(StorageDecl(SolType.Bool, Visibility.PUBLIC, "payoffs_distributed"))


    // ---- Game State Storage ----
    val definedFields = mutableSetOf<FieldRef>()
    g.phases.forEachIndexed { phaseIdx, phase ->
        phase.actions.forEach { (role, sig) ->
            // Per-role “joined” flag (for first join)
            if (sig.join != null) {
                add(StorageDecl(SolType.Bool, Visibility.PUBLIC, roleDone(role)))
            }
            // For each parameter, create storage + done flags
            sig.parameters.forEach { p ->
                val field = FieldRef(role, p.name)
                // Storage for the value (hidden or visible)
                if (!definedFields.contains(field)) {
                    // This is the first time we see this field.
                    // If it's hidden, we need *both* hidden and visible slots.
                    // If it's visible, we just need visible slot.
                    if (!p.visible) {
                        add(StorageDecl(SolType.Uint256, Visibility.PUBLIC, storageParam(role, p.name, true)))
                        add(StorageDecl(SolType.Bool, Visibility.PUBLIC, doneFlag(role, p.name, true)))
                        add(StorageDecl(translateType(p.type), Visibility.PUBLIC, storageParam(role, p.name, false)))
                        add(StorageDecl(SolType.Bool, Visibility.PUBLIC, doneFlag(role, p.name, false)))
                    } else {
                        add(StorageDecl(translateType(p.type), Visibility.PUBLIC, storageParam(role, p.name, false)))
                        add(StorageDecl(SolType.Bool, Visibility.PUBLIC, doneFlag(role, p.name, false)))
                    }
                    definedFields.add(field)
                }
            }
            // Per-phase action-taken marker
            add(StorageDecl(SolType.Bool, Visibility.PUBLIC, phaseDone(role, phaseIdx)))
        }
    }
}

/** Per-phase functions: joins / yields / reveal + ONE Broadcast/nextPhase pair. */
private fun buildPhaseFunctions(
    g: GameIR,
    phaseIdx: Int,
    phase: Phase,
    history: ParamHistory
): List<FunctionDecl> = buildList {

    // 1. Generate all role-specific functions for this phase
    phase.actions.forEach { (role, sig) ->
        // Is this *this* signature a reveal phase for at least one param?
        val isReveal = sig.parameters.any { p -> history.isReveal(role, p.name, phaseIdx) }
        // Is this *this* signature a commit phase?
        val needsCR = history.needsCommitReveal(role, sig, phaseIdx)

        // Determine the correct function name
        val funcName = if (sig.join != null) {
            joinFunc(role)
        } else if (isReveal) {
            revealFunc(role, phaseIdx)
        } else {
            yieldFunc(role, phaseIdx)
        }

        when {
            // Case 1: A 'reveal' phase
            isReveal -> add(buildReveal(role, sig, phaseIdx, funcName, g, history))

            // Case 2: A 'commit' phase
            needsCR -> add(buildCommit(role, sig, phaseIdx, funcName, g, history))

            // --- From here, we know !isReveal AND !needsCR ---

            // Case 3: It's a JOIN phase (and not a commit/reveal)
            sig.join != null -> {
                if (sig.parameters.isEmpty()) {
                    // Case 3a: Simple join (no params)
                    add(buildSimpleJoin(role, sig, phaseIdx, g, history))
                } else {
                    // Case 3b: Join with visible params
                    add(buildJoinVisible(role, sig, phaseIdx, g, history))
                }
            }

            // Case 4: It's a YIELD phase (sig.join == null) (and not a commit/reveal)
            else -> {
                add(buildYield(role, sig, phaseIdx, funcName, g, history))
            }
        }
    }

    // 2. AFTER all role functions, add ONE phase-advancing function
    add(buildNextPhase(phaseIdx, phase))
}


/** join with no parameters (just stake + role assignment) */
private fun buildSimpleJoin(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    val deposit = sig.join?.deposit?.v ?: 0
    return FunctionDecl(
        name = joinFunc(role),
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE else StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(NO_ROLE),
            atPhase(phaseIdx)
        ),
        body = buildList {
            addAll(buildJoinLogic(role, sig)) // Refactored
            // Add translated 'where' clause
            addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))
            // add(assign(v(roleDone(role)), bool(true))) // <-- Moved to helper
            add(assign(v(phaseDone(role, phaseIdx)), bool(true)))
        }
    )
}

/** join with visible parameters (no commit) */
private fun buildJoinVisible(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    val deposit = sig.join?.deposit?.v ?: 0
    val inputs = sig.parameters.map { Param(translateType(it.type), inputParam(it.name, false)) }
    return FunctionDecl(
        name = joinFunc(role),
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE else StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(NO_ROLE),
            atPhase(phaseIdx)
        ),
        body = buildList {
            addAll(buildJoinLogic(role, sig)) // Refactored
            addAll(translateDomainGuards(sig.parameters))           // visible domain guards
            addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))
            addAll(translateAssignments(role, sig.parameters))      // store + done flags
            // add(assign(v(roleDone(role)), bool(true))) // <-- Moved to helper
            add(assign(v(phaseDone(role, phaseIdx)), bool(true)))
        }
    )
}

/** yield with visible params */
private fun buildYield(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    funcName: String,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    val inputs = sig.parameters.map { Param(translateType(it.type), inputParam(it.name, false)) }
    return FunctionDecl(
        name = funcName,
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(role),
            atPhase(phaseIdx)
        ),
        body = buildList {
            add(require(not(v(phaseDone(role, phaseIdx))), "done"))
            addAll(translateDomainGuards(sig.parameters))
            addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))
            addAll(translateAssignments(role, sig.parameters))
            add(assign(v(phaseDone(role, phaseIdx)), bool(true)))
        }
    )
}

/** commit phase: dynamically builds inputs and assignments from signature */
private fun buildCommit(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    funcName: String,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    // Only params that are hidden *now*
    val hiddenParams = sig.parameters.filter { !it.visible }

    val inputs = hiddenParams.map { p ->
        // All hidden inputs are passed as uint256 (hashes)
        Param(SolType.Uint256, inputParam(p.name, hidden = true))
    }

    val body = buildList {
        add(require(not(v(phaseDone(role, phaseIdx))), "done"))

        // Add translated 'where' clause (can read from inputs)
        addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))

        // Assign all hidden params from inputs to storage
        hiddenParams.forEach { p ->
            val pName = p.name
            add(
                assign(
                    v(storageParam(role, pName, hidden = true)), // e.g., Alice_car_hidden
                    v(inputParam(pName, hidden = true))       // e.g., _hidden_car
                )
            )
            add(
                assign(
                    v(doneFlag(role, pName, hidden = true)),     // e.g., Alice_car_hidden_done
                    bool(true)
                )
            )
        }
        add(assign(v(phaseDone(role, phaseIdx)), bool(true)))
    }.toMutableList()

    // Check for join (e.g. MontyHall)
    val deposit = sig.join?.deposit?.v ?: 0
    val byRole = if (sig.join != null) NO_ROLE else role
    val joinModifiers = listOf(
        by(byRole),
        atPhase(phaseIdx)
    )
    if (sig.join != null) {
        // Prepend all join logic
        body.addAll(0, buildJoinLogic(role, sig))
    }


    return FunctionDecl(
        name = funcName,
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = if (deposit > 0) StateMutability.PAYABLE else StateMutability.NONPAYABLE,
        modifiers = joinModifiers,
        body = body
    )
}

/** reveal phase: dynamically build inputs, checks, and assignments */
private fun buildReveal(
    role: RoleId,
    sig: Signature,
    phaseIdx: Int,
    funcName: String,
    g: GameIR,
    history: ParamHistory
): FunctionDecl {
    // These are the clear-text parameters being revealed *in this phase*
    val clearParams = sig.parameters.filter { it.visible }

    val inputs = buildList {
        clearParams.forEach { p ->
            add(Param(translateType(p.type), inputParam(p.name, hidden = false)))
        }
        // Add salt (assuming one salt for all reveals in this phase)
        // TODO: This could be more robust, e.g., per-param salts
        add(Param(SolType.Uint256, "salt"))
    }

    val body = buildList {
        add(require(not(v(phaseDone(role, phaseIdx))), "done"))

        // Verify commitment(s)
        clearParams.forEach { p ->
            // Check this is *actually* a reveal (was hidden before)
            if (history.isReveal(role, p.name, phaseIdx)) {
                val computed = SolExpr.Keccak256(
                    SolExpr.AbiEncodePacked(
                        listOf(
                            v(inputParam(p.name, false)), // _param_car
                            v("salt")
                        )
                    )
                )
                val stored = v(storageParam(role, p.name, hidden = true)) // Alice_car_hidden
                add(require(computed eq SolExpr.Cast(SolType.Bytes32, stored), "bad reveal"))
            }
        }

        // Check domain guards on clear-text values
        addAll(translateDomainGuards(clearParams))
        // Check 'where' clause on clear-text values
        addAll(translateWhere(sig.requires.condition, g, history, role, phaseIdx))

        // Assign clear-text values to visible storage
        addAll(translateAssignments(role, clearParams))
        add(assign(v(phaseDone(role, phaseIdx)), bool(true)))
    }
    return FunctionDecl(
        name = funcName,
        params = inputs,
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(
            by(role),
            atPhase(phaseIdx)
        ),
        body = body
    )
}

private fun atPhase(phaseIdx: Int): ModifierCall = ModifierCall("at_phase", listOf(int(phaseIdx)))

/** Single phase-advancing function, called after all role actions in a phase are done. */
private fun buildNextPhase(phaseIdx: Int, phase: Phase): FunctionDecl {
    val guards = phase.roles().map { role ->
        require(v(phaseDone(role, phaseIdx)), "${role.name} not done")
    }

    return FunctionDecl(
        name = nextPhaseFunc(phaseIdx),
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = emptyList(), // No 'at_phase' modifier, it checks its own phase
        body = listOf(
            require(v(PHASE_VAR) eq int(phaseIdx), "wrong phase")
        ) + guards + listOf( // Add all role-done guards
            Statement.Emit(broadcastEvent(phaseIdx), emptyList()),
            assign(v(PHASE_VAR), int(phaseIdx + 1)),
            assign(v(LAST_TS_VAR), SolExpr.Member(SolExpr.Var("block"), "timestamp"))
        )
    )
}

/** Function to calculate and assign payoffs to balances based on final state. */
private fun buildPayoffFunction(g: GameIR, history: ParamHistory, finalPhase: Int): FunctionDecl {
    val body = buildList<Statement> {
        // Mark payoffs as distributed (effects-first)
        add(assign(v("payoffs_distributed"), bool(true)))

        // Calculate and assign payoffs to each role's balance
        (g.roles + g.chanceRoles).forEach { role ->
            val payoffExpr = g.payoffs[role] ?: return@forEach // Skip roles with no payoff

            val solPayoff = translateIrExpr(
                payoffExpr,
                g,
                history,
                role, // 'currentRole' doesn't matter much for payoff context
                finalPhase,
                ExprContext.PAYOFF
            )

            val roleAddr = v(roleAddr(role))
            // Assume payoffs are absolute, not deltas
            add(assign(index(BALANCE_MAPPING, roleAddr), solPayoff))
        }
    }

    return FunctionDecl(
        name = "distributePayoffs",
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = listOf(ModifierCall("at_final_phase", emptyList())),
        body = body
    )
}


/** Withdraw function (matches golden) */
private fun buildWithdraw(): FunctionDecl {
    val bal = "bal"
    return FunctionDecl(
        name = "withdraw",
        params = emptyList(),
        visibility = Visibility.PUBLIC,
        stateMutability = StateMutability.NONPAYABLE,
        modifiers = emptyList(),
        body = listOf(
            // int256 bal = balanceOf[msg.sender];
            Statement.VarDecl(SolType.Int256, bal, index(BALANCE_MAPPING, msgSender)),
            // require(bal > 0, "no funds");
            require(v(bal) gt int(0), "no funds"),
            // Effects-first: balanceOf[msg.sender] = 0;
            assign(index(BALANCE_MAPPING, msgSender), int(0)),
            // Interaction: (bool ok, ) = payable(msg.sender).call{value: bal}("");
            Statement.Raw("(bool ok, ) = payable(msg.sender).call{value: uint256($bal)}(\"\");"),
            require(v("ok"), "ETH send failed")
        )
    )
}

/**
 * Helper function to generate the common "join" logic.
 * This includes role assignment, address saving, deposit handling, and 'done' flag.
 */
private fun buildJoinLogic(role: RoleId, sig: Signature): List<Statement> {
    val deposit = sig.join?.deposit?.v ?: 0
    val statements = mutableListOf<Statement>()

    statements.add(require(not(v(roleDone(role))), "already joined"))
    statements.add(assign(index(ROLE_MAPPING, msgSender), role(role.name)))
    statements.add(assign(v(roleAddr(role)), msgSender)) // Save address

    if (deposit > 0) {
        statements.add(requireDeposit(deposit))
        statements.add(setBalance())
    }

    statements.add(assign(v(roleDone(role)), bool(true))) // Mark as joined

    return statements
}

private fun role(byRole: String): SolExpr.EnumValue = enumVal(ROLE_ENUM, byRole)

/* ====================== IR→Solidity translation atoms ====================== */

private fun translateType(t: Type): SolType = when (t) {
    is Type.IntType -> SolType.Int256
    is Type.BoolType -> SolType.Bool
    is Type.SetType -> SolType.Int256 // Enums/sets are represented as integers
}

/**
 * Translates a vegas.ir.Expr into a vegas.backend.solidity.SolExpr.
 * This is the core logic engine that replaces the 'translateWhere' stub.
 */
private fun translateIrExpr(
    expr: Expr,
    g: GameIR,
    history: ParamHistory,
    currentRole: RoleId,
    phaseIdx: Int,
    context: ExprContext
): SolExpr {
    when (expr) {
        // Literals
        is Expr.IntVal -> return int(expr.v)
        is Expr.BoolVal -> return bool(expr.v)

        // Field Access
        is Expr.Field -> {
            val (role, param) = expr.field
            val sig = g.phases.getOrNull(phaseIdx)?.actions?.get((currentRole))

            // Is this field an input to the CURRENT function?
            val paramDef = sig?.parameters?.find { it.name == param }
            val isInput = paramDef != null && context == ExprContext.WHERE_CLAUSE

            if (isInput) {
                // Read from function input (e.g., "_param_car" or "_hidden_car")
                return v(inputParam(param, !paramDef.visible))
            } else {
                // Read from storage (e.g., "Alice_car_visible")
                // For payoffs, always read visible.
                // For 'where', we must know if it's been revealed yet.
                val readVisible = history.wasDefinedVisible(role, param) ||
                        context == ExprContext.PAYOFF ||
                        // Check if it was revealed in a *previous* phase
                        (0 until phaseIdx).any { p -> history.isReveal(role, param, p) }

                return v(storageParam(role, param, hidden = !readVisible))
            }
        }

        // 'isDefined' check
        is Expr.IsDefined -> {
            val (role, param) = expr.field
            // Check if the *visible* param done flag is set
            // (Assuming isDefined always refers to the public, revealed value)
            return v(doneFlag(role, param, hidden = false))
        }

        // --- Arithmetic ---
        is Expr.Add -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) +
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Sub -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) -
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Mul -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) *
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Div -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) /
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Neg -> return neg(translateIrExpr(expr.x, g, history, currentRole, phaseIdx, context))

        // --- Comparison ---
        is Expr.Eq -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) eq
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Ne -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) ne
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Lt -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) lt
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Le -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) le
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Gt -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) gt
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Ge -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) ge
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        // --- Boolean ---
        is Expr.And -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) and
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Or -> return translateIrExpr(expr.l, g, history, currentRole, phaseIdx, context) or
                translateIrExpr(expr.r, g, history, currentRole, phaseIdx, context)

        is Expr.Not -> return not(translateIrExpr(expr.x, g, history, currentRole, phaseIdx, context))

        // --- Ternary ---
        is Expr.Ite -> return SolExpr.Ternary(
            condition = translateIrExpr(expr.c, g, history, currentRole, phaseIdx, context),
            ifTrue = translateIrExpr(expr.t, g, history, currentRole, phaseIdx, context),
            ifFalse = translateIrExpr(expr.e, g, history, currentRole, phaseIdx, context)
        )
    }
}


/** Translates the IR 'where' condition into Solidity 'require' statements. */
private fun translateWhere(
    expr: Expr,
    g: GameIR,
    history: ParamHistory,
    role: RoleId,
    phaseIdx: Int
): List<Statement.Require> {
    if (expr == Expr.BoolVal(true)) return emptyList() // Don't emit 'require(true)'

    val solCondition = translateIrExpr(
        expr, g, history, role, phaseIdx, ExprContext.WHERE_CLAUSE
    )
    return listOf(require(solCondition, "where"))
}

/** Generates 'require' statements for domain validation (e.g., `x in {1, 2, 3}`) */
private fun translateDomainGuards(params: List<Parameter>): List<Statement.Require> =
    params.filter { it.visible }.mapNotNull { p ->
        when (val t = p.type) {
            is Type.SetType -> {
                if (t.values.isEmpty()) null
                else {
                    val x = v(inputParam(p.name, false))
                    val cond = t.values.map { x eq int(it) }.reduce<SolExpr, SolExpr> { a, b -> a or b }
                    require(cond, "domain")
                }
            }

            else -> null
        }
    }

/** Generates assignment statements to store visible parameters and set their done flags. */
private fun translateAssignments(role: RoleId, params: List<Parameter>): List<Statement.Assign> =
    params.filter { it.visible }.flatMap { p ->
        val storage = v(storageParam(role, p.name, false))
        val input = v(inputParam(p.name, false))
        val done = v(doneFlag(role, p.name, false))
        listOf(assign(storage, input), assign(done, bool(true)))
    }
