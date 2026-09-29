/**
 * # VegasCore elaboration
 *
 * Emits, for a Vegas game, the VegasCore `SourceProgram` over `simpleExpr`
 * that has the same event structure, so that Lean checks the correspondence
 * of `docs/DESIGN.md` section 0 instead of taking it on trust.
 *
 * The emitted program is exact in its structure: the sequence of draws,
 * commitments and disclosures (a linearization of the event graph), each
 * cell's kind, owner and payload type, and which cells every guard and every
 * payoff reads, and through which kind of cell. Type-checking it in Lean
 * establishes what the core demands of that structure: names are fresh,
 * every commitment is resolved exactly once before the end, a guard reads only
 * public data, publications and its own author's commitments, all in scope
 * where it is declared, and payoffs read only public cells.
 *
 * The emitted code is not the program's: `simpleExpr` has no integer
 * subtraction, multiplication or comparison, so guards and payoffs are
 * replaced by placeholders that read exactly the same cells. Value semantics
 * is therefore not checked, and neither is money (deposits, `burn`), which the
 * core does not have.
 *
 * A game outside the core's fragment is refused with [UnsupportedCoreElaboration]
 * naming the construct; see [generateCoreSourceProgram].
 */
package vegas.backend.vegascore

import vegas.FieldRef
import vegas.RoleId
import vegas.ir.Dist
import vegas.ir.EntropySource
import vegas.ir.Expr
import vegas.ir.GameIR
import vegas.ir.NodeId
import vegas.ir.Type
import vegas.ir.Visibility
import vegas.ir.fieldsRead

/** The game uses a construct the core has no counterpart for. */
class UnsupportedCoreElaboration(message: String) : RuntimeException(message)

/** The imports and opens a file of elaborated programs starts with. */
const val CORE_PRELUDE = """import Vegas.Source.Basic
import Vegas.Expr.Simple

open Vegas Vegas.SourceProgram
"""

/**
 * The Lean declarations, in namespace [namespace], of the VegasCore program
 * corresponding to [ir]: an inductive `Player`, the initial `context` of
 * private inputs, and `program`, a `SourceProgram Player simpleExpr context` with
 * no outstanding commitment.
 *
 * Refused, with the reason, when the game uses:
 * - a `random` role (a trusted chance actor; core chance has no controller);
 * - a draw conditioned by `where`, or without a finite declared law;
 * - a private draw its owner could act before (core private inputs are
 *   drawn by the setup, before play);
 * - an action without parameters, or a guard on a join;
 * - a guard reading another role's value that is not yet public at the
 *   guard's commitment (a core guard reads only what is in scope there).
 */
fun generateCoreSourceProgram(ir: GameIR, namespace: String): String =
    CoreElaborator(ir).emit(namespace)

private enum class CellKind { PRIVATE_INPUT, COMMITMENT, PUBLICATION, PUBLIC_DATA }

private data class Cell(val id: Int, val field: FieldRef, val kind: CellKind, val type: Type)

/** A source context, most recent cell first, as in VegasCore. */
private class Context(val cells: List<Cell> = emptyList()) {
    fun push(cell: Cell) = Context(listOf(cell) + cells)

    fun path(cell: Cell): String = hasVar(cells.indexOf(cell).also { require(it >= 0) })

    /** The cell holding [field]'s published value, if it is public by now. */
    fun public(field: FieldRef): Cell? = cells.firstOrNull {
        it.field == field && (it.kind == CellKind.PUBLICATION || it.kind == CellKind.PUBLIC_DATA)
    }

    fun commitment(field: FieldRef): Cell? =
        cells.firstOrNull { it.field == field && it.kind == CellKind.COMMITMENT }

    fun privateInput(field: FieldRef): Cell? =
        cells.firstOrNull { it.field == field && it.kind == CellKind.PRIVATE_INPUT }

    /** `SourcePublicCtx`: the public cells, in order. */
    fun publicCells(): List<Cell> =
        cells.filter { it.kind == CellKind.PUBLICATION || it.kind == CellKind.PUBLIC_DATA }
}

private class CoreElaborator(private val ir: GameIR) {
    private val dag = ir.dag
    private var nextId = 0
    private fun freshId() = nextId++

    private fun unsupported(reason: String): Nothing = throw UnsupportedCoreElaboration(reason)

    fun emit(namespace: String): String {
        val order = dag.topo()
        val (initial, draws) = privateInputs(order)
        var ctx = initial
        val steps = mutableListOf<String>()
        val guards = guardReadsByCommitment(order)

        for (id in order) {
            if (id in draws) continue
            val meta = dag.meta(id)
            val sample = meta.sample
            if (sample != null && sample.source is EntropySource.RoleSubmit) {
                unsupported("random role '${meta.struct.owner}' is a trusted chance actor; core chance has no controller")
            }
            if (meta.spec.params.isEmpty()) {
                if (meta.spec.join == null) unsupported("action $id has no parameters, so no core event")
                if (!isTrue(meta.spec.guardExpr)) unsupported("the join $id has a guard, which binds no value")
                continue
            }
            if (sample != null) {
                if (!isTrue(meta.spec.guardExpr)) unsupported("draw $id is conditioned by 'where'; core laws are unconditioned")
                val param = meta.spec.params.singleOrNull()
                    ?: unsupported("draw $id binds several values; a core draw binds one")
                val dist = sample.dist ?: unsupported("draw $id has no finite declared law")
                val cell = Cell(freshId(), FieldRef(meta.struct.owner, param.name), CellKind.PUBLIC_DATA, param.type)
                steps += ".sample (payload := ${leanType(param.type)}) ${cell.id} (by decide) " +
                    "(.weighted ${leanLaw(dist, param.type)})"
                ctx = ctx.push(cell)
                continue
            }
            val owner = meta.struct.owner
            val published = mutableListOf<Cell>()
            for (param in meta.spec.params) {
                val field = FieldRef(owner, param.name)
                when (meta.struct.visibility.getValue(field)) {
                    Visibility.COMMIT, Visibility.PUBLIC -> {
                        val cell = Cell(freshId(), field, CellKind.COMMITMENT, param.type)
                        steps += ".commit (payload := ${leanType(param.type)}) ${cell.id} ${player(owner)} (by decide) " +
                            guard(ctx, owner, cell, guards[field].orEmpty())
                        ctx = ctx.push(cell)
                        if (meta.struct.visibility.getValue(field) == Visibility.PUBLIC) published += cell
                    }
                    Visibility.REVEAL -> {
                        val source = ctx.commitment(field) ?: unsupported("$field is revealed without a commitment")
                        val (step, next) = reveal(ctx, source)
                        steps += step
                        ctx = next
                    }
                }
            }
            // A public move is a commitment whose disclosure follows at once.
            for (cell in published) {
                val (step, next) = reveal(ctx, cell)
                steps += step
                ctx = next
            }
        }
        steps += ".ret ${payoffs(ctx)}"

        return buildString {
            appendLine("namespace $namespace")
            appendLine()
            appendLine("inductive Player where")
            appendLine("  " + ir.roles.sortedBy { it.name }.joinToString(" ") { "| «${it.name}»" })
            appendLine("  deriving DecidableEq")
            appendLine()
            appendLine("abbrev context : SourceCtx Player simpleExpr :=")
            appendLine("  [" + initial.cells.joinToString(", ") { "(${it.id}, ${cellType(it)})" } + "]")
            appendLine()
            appendLine("def program : SourceProgram Player simpleExpr context ∅ :=")
            appendLine("  " + steps.joinToString(" <|\n  "))
            appendLine()
            appendLine("end $namespace")
        }
    }

    /**
     * Private draws become the setup's private inputs. That is faithful only
     * when the owner learns nothing earlier than it would in the game: every
     * move of the owner must follow the draw.
     */
    private fun privateInputs(order: List<NodeId>): Pair<Context, Set<NodeId>> {
        val draws = order.filter { dag.isPrivateDraw(it) }
        var ctx = Context()
        for (draw in draws) {
            val owner = dag.owner(draw)
            val early = order.firstOrNull {
                dag.owner(it) == owner && it != draw && dag.spec(it).join == null &&
                    !dag.isPrivateDraw(it) && !dag.reaches(draw, it)
            }
            if (early != null) {
                unsupported("private draw $draw comes after $owner can move ($early); core private inputs precede play")
            }
            for (param in dag.params(draw)) {
                ctx = ctx.push(Cell(freshId(), FieldRef(owner, param.name), CellKind.PRIVATE_INPUT, param.type))
            }
        }
        return ctx to draws.toSet()
    }

    /**
     * The cells each commitment's guard reads. A core guard is declared at one
     * commitment, its subject, and is checked at the reveal that publishes the
     * last of its inputs. A Vegas guard constrains its node's owner, so its
     * subject is the owner's latest commitment among the node's values and
     * the owner's fields it reads. For a guard Vegas checks at a reveal
     * (`reveal Host(car) where Host.goat != Host.car`) that is the commitment
     * to `goat`, reading the earlier commitment to `car`, and the core checks
     * it when `car` is revealed, as Vegas does.
     */
    private fun guardReadsByCommitment(order: List<NodeId>): Map<FieldRef, Set<FieldRef>> {
        val committedAt = mutableMapOf<FieldRef, Int>()
        for (id in order) {
            for ((field, visibility) in dag.visibilityOf(id)) {
                if (visibility != Visibility.REVEAL) committedAt.putIfAbsent(field, committedAt.size)
            }
        }
        val reads = mutableMapOf<FieldRef, Set<FieldRef>>()
        for (id in order) {
            val meta = dag.meta(id)
            if (meta.sample != null || isTrue(meta.spec.guardExpr) || meta.spec.params.isEmpty()) continue
            val owner = meta.struct.owner
            val read = meta.spec.guardExpr.fieldsRead()
            val subject = (meta.spec.params.map { FieldRef(owner, it.name) } + read.filter { it.owner == owner })
                .filter { it in committedAt }
                .maxBy { committedAt.getValue(it) }
            reads[subject] = reads[subject].orEmpty() + read
        }
        return reads
    }

    private fun guard(ctx: Context, author: RoleId, subject: Cell, readFields: Set<FieldRef>): String {
        val schema = (readFields - subject.field).map { field ->
            val (read, cell) = guardRead(ctx, field, subject)
            Triple(field, read, cell)
        }
        val schemaIds = schema.map { (_, _, cell) -> cell.id }
        val code = schema.foldIndexed(".eq (.var ${subject.id} .here) (.var ${subject.id} .here)") { i, acc, (_, _, cell) ->
            val v = ".var ${cell.id} ${hasVar(i + 1)}"
            ".andBool ($acc) (.eq ($v) ($v))"
        }
        val reads = if (schema.isEmpty()) "fun h => nomatch h" else
            "fun h => match h with " + schema.mapIndexed { i, (_, read, _) -> "| ${hasVar(i)} => $read" }.joinToString(" ")
        val schemaList = schema.joinToString(", ") { (_, _, cell) -> "(${cell.id}, ${leanType(cell.type)})" }
        check(schemaIds.distinct().size == schemaIds.size)
        return "{ schema := [$schemaList], schemaNames := by decide, subjectFresh := by decide, " +
            "code := $code, reads := $reads }"
    }

    /**
     * How a guard reads [field], as `SourceGuardRead`: its publication if it is
     * public, else its commitment. The commitment may be another role's; Lean
     * then rejects the read, as the core forbids it.
     */
    private fun guardRead(ctx: Context, field: FieldRef, subject: Cell): Pair<String, Cell> {
        ctx.public(field)?.let { cell ->
            val constructor = if (cell.kind == CellKind.PUBLIC_DATA) ".publicData" else ".publication"
            return "$constructor ${ctx.path(cell)}" to cell
        }
        ctx.commitment(field)?.let { cell -> return ".commitment ${ctx.path(cell)}" to cell }
        if (ctx.privateInput(field) != null) unsupported("the guard on ${subject.field} reads the private input $field")
        unsupported("the guard on ${subject.field} reads $field, which is not yet in scope at the commitment")
    }

    private fun reveal(ctx: Context, source: Cell): Pair<String, Context> {
        val cell = Cell(freshId(), source.field, CellKind.PUBLICATION, source.type)
        val step = ".reveal (payload := ${leanType(source.type)}) ${cell.id} ${player(source.field.owner)} ${source.id} " +
            "(by decide) ${ctx.path(source)} (by decide)"
        return step to ctx.push(cell)
    }

    /** `ret` with each role's payoff: a placeholder reading the same public cells. */
    private fun payoffs(ctx: Context): String {
        val public = ctx.publicCells()
        val entries = ir.roles.sortedBy { it.name }.map { role ->
            val expr = ir.payoffs[role]
            val reads = expr?.fieldsRead().orEmpty().map { field ->
                ctx.public(field) ?: unsupported("the payoff of $role reads $field, which is never published")
            }
            val code = reads.fold(".constInt 0") { acc, cell ->
                val v = ".var ${cell.id} ${hasVar(public.indexOf(cell))}"
                ".ite (.eq ($v) ($v)) ($acc) (.constInt 0)"
            }
            "(${player(role)}, $code)"
        }
        return "[" + entries.joinToString(", ") + "]"
    }

    private fun player(role: RoleId) = ".«${role.name}»"

    private fun cellType(cell: Cell): String = when (cell.kind) {
        CellKind.PRIVATE_INPUT -> ".privateInput ${player(cell.field.owner)} ${leanType(cell.type)}"
        CellKind.COMMITMENT -> ".commitment ${player(cell.field.owner)} ${leanType(cell.type)}"
        CellKind.PUBLICATION -> ".publication ${leanType(cell.type)}"
        CellKind.PUBLIC_DATA -> ".publicData ${leanType(cell.type)}"
    }
}

private fun isTrue(e: Expr) = e is Expr.Const.BoolVal && e.v

/** `HasVar` evidence for the cell [index] positions from the head. */
private fun hasVar(index: Int): String =
    (0 until index).fold(".here") { acc, _ -> "(.there $acc)" }

private fun leanType(type: Type): String = when (type) {
    Type.BoolType -> ".bool"
    Type.IntType -> ".int"
    is Type.RangeType -> "(.range (${type.min}) ${type.max - type.min})"
}

private fun leanValue(value: Expr.Const, type: Type): String = when (type) {
    Type.BoolType -> (value as Expr.Const.BoolVal).v.toString()
    Type.IntType -> "(${(value as Expr.Const.IntVal).v} : Int)"
    is Type.RangeType -> "⟨${(value as Expr.Const.IntVal).v}, by decide⟩"
}

/** A `RationalLaw` literal; its normalization is checked by Lean. */
private fun leanLaw(dist: Dist, type: Type): String {
    val entries = dist.support.joinToString(", ") { (v, w) ->
        "(${leanValue(v, type)}, (${w.numerator} / ${w.denominator} : ℚ≥0))"
    }
    return "⟨[$entries], by norm_num⟩"
}
