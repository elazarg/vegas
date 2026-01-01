package vegas.frontend

import vegas.RoleId
import vegas.VarId
import vegas.FieldRef

sealed class Ast

interface Step

data class Role(val id: RoleId) : Ast() {
    override fun toString(): String = id.toString()
    val name = id.name

    companion object {
        @JvmStatic
        fun of(name: String) = Role(RoleId(name))
    }
}

sealed class Ext : Ast() {
    data class Bind(val kind: Kind, val qs: List<Query>, val handler: Outcome? = null, val ext: Ext) : Ext(), Step
    data class BindSingle(val kind: Kind, val q: Query, val handler: Outcome? = null, val ext: Ext) : Ext(), Step
    data class Value(val outcome: Outcome) : Ext()
}

data class Query(val role: Role, val params: List<VarDec>, val deposit: Exp.Const.Num, val where: Exp, val handler: Outcome? = null) : Ast()

sealed class Exp : Ast() {
    data class Call(val target: Var, val args: List<Exp>) : Exp()
    data class UnOp(val op: String, val operand: Exp) : Exp()
    data class BinOp(val op: String, val left: Exp, val right: Exp) : Exp()

    data class Var(val id: VarId) : Exp() {
        override fun toString(): String = id.toString()
        companion object {
            @JvmStatic
            fun of(name: String) = Var(VarId(name))
        }
    }

    data class Field(val fieldRef: FieldRef) : Exp() {
        companion object {
            @JvmStatic
            fun of(role: Role, param: Var) = Field(FieldRef(role.id, param.id))
        }
    }
    data class Cond(val cond: Exp, val ifTrue: Exp, val ifFalse: Exp) : Exp()

    sealed class Const : Exp() {
        object UNDEFINED : Const()
        data class Num(val n: Int) : Const()
        data class Bool(val truth: Boolean) : Const()
        data class Address(val n: Int) : Const()
    }

    data class Let(val dec: VarDec, val init: Exp, val exp: Exp) : Exp()
}

sealed class Outcome : Ast() {
    data class Cond(val cond: Exp, val ifTrue: Outcome, val ifFalse: Outcome) : Outcome()
    // Idea: not a simple Var -> Exp mapping, but a `lambda (Var : RoleSet) . Exp` mapping
    // (the trivial case where RoleSet is a singleton van have Var -> Exp as a syntactic sugar)
    // This sounds like dependent types, but no complex type checking is involved.

    data class Value(val ts: Map<Role, Exp>) : Outcome()
    data class Let(val dec: VarDec, val init: Exp, val outcome: Outcome) : Outcome()

    // Group failure handlers for simultaneous steps
    object Split : Outcome()
    object Burn : Outcome()
    object Null : Outcome()
}

data class VarDec(val v: Exp.Var, val type: TypeExp)

data class MacroDec(
    val name: VarId,
    val params: List<MacroParam>,
    val resultType: TypeExp,
    val body: Exp
) : Ast()

data class MacroParam(
    val name: VarId,
    val type: TypeExp
) : Ast()

enum class Kind { JOIN, YIELD, REVEAL, COMMIT, JOIN_CHANCE }

sealed class TypeExp : Ast() {
    object INT : TypeExp(), IntClass
    object BOOL : TypeExp()
    object ADDRESS : TypeExp()
    object EMPTY : TypeExp()

    // Hidden is an internal type created for commit fields - not user-facing syntax
    data class Hidden(val type: TypeExp) : TypeExp()

    data class TypeId(val name: String) : TypeExp() {
        override fun toString(): String = name
    }

    interface IntClass
    data class Subset(val values: Set<Exp.Const.Num>) : TypeExp(), IntClass
    data class Range(val min: Exp.Const.Num, val max: Exp.Const.Num) : TypeExp(), IntClass
    data class Opt(val type: TypeExp) : TypeExp()
}

data class GameAst(
    val name: String,
    val desc: String,
    val types: Map<TypeExp.TypeId, TypeExp>,
    val macros: List<MacroDec>,
    val game: Ext
) : Ast()

internal fun findRoleIds(ext: Ext): Set<RoleId> = when (ext) {
    is Ext.Bind -> (if (ext.kind == Kind.JOIN) ext.qs.map { it.role.id }.toSet() else setOf()) + findRoleIds(ext.ext)
    is Ext.BindSingle -> (if (ext.kind == Kind.JOIN) setOf(ext.q.role.id) else setOf()) + findRoleIds(ext.ext)
    is Ext.Value -> setOf()
}

internal fun findChanceRoleIds(ext: Ext): Set<RoleId> = when (ext) {
    is Ext.Bind -> (if (ext.kind == Kind.JOIN_CHANCE) ext.qs.map { it.role.id }.toSet() else setOf()) + findChanceRoleIds(
        ext.ext
    )

    is Ext.BindSingle -> (if (ext.kind == Kind.JOIN_CHANCE) setOf(ext.q.role.id) else setOf()) + findChanceRoleIds(
        ext.ext
    )

    is Ext.Value -> setOf()
}

// Free *names* in an Exp, given a set of bound variables.
// Includes:
//   - free variable names (Exp.Var not in `bound`)
//   - call targets (Exp.Call.target.id) if not bound
internal fun Exp.freeVars(bound: Set<VarId> = emptySet()): Set<VarId> {
    val acc = mutableSetOf<VarId>()

    fun go(e: Exp, b: MutableSet<VarId>) {
        when (e) {
            is Exp.Var -> {
                if (e.id !in b) acc.add(e.id)
            }

            is Exp.Call -> {
                // Call target (function/macro name) counts as a free name if not bound
                if (e.target.id !in b) acc.add(e.target.id)
                e.args.forEach { go(it, b) }
            }

            is Exp.Field -> {
                // FieldRef contains a VarId for the field name, but that’s in field namespace;
                // we don’t treat it as a free *variable* name for macros.
                // Nothing to do.
            }

            is Exp.UnOp -> go(e.operand, b)

            is Exp.BinOp -> {
                go(e.left, b); go(e.right, b)
            }

            is Exp.Cond -> {
                go(e.cond, b); go(e.ifTrue, b); go(e.ifFalse, b)
            }

            is Exp.Let -> {
                // let! dec.v.id = init in exp
                go(e.init, b)
                // shadowing: introduce bound name for the body
                val b2 = HashSet(b)
                b2.add(e.dec.v.id)
                go(e.exp, b2)
            }

            is Exp.Const.Num,
            is Exp.Const.Bool,
            is Exp.Const.Address,
            Exp.Const.UNDEFINED -> {
                // no names here
            }
        }
    }

    go(this, bound.toMutableSet())
    return acc
}
