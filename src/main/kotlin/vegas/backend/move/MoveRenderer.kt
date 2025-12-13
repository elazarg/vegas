package vegas.backend.move

class MoveRenderer {
    private val sb = StringBuilder()
    private var indentLevel = 0

    fun render(pkg: MovePackage): String {
        pkg.modules.forEach { renderModule(it) }
        return sb.toString()
    }

    private fun renderModule(module: MoveModule) {
        line("module ${module.name}::${module.name} {")
        indent {
            // Imports
            module.imports.sortedBy { it.module }.forEach { imp ->
                val alias = if (imp.alias != null) " as ${imp.alias}" else ""
                line("use ${imp.address}::${imp.module}$alias;")
            }
            if (module.imports.isNotEmpty()) line()

            // Constants
            module.constants.forEach { c ->
                line("const ${c.name}: ${renderType(c.type)} = ${renderExpr(c.value)};")
            }
            if (module.constants.isNotEmpty()) line()

            // Structs
            module.structs.forEach { struct ->
                val abilities = if (struct.abilities.isNotEmpty()) " has ${struct.abilities.joinToString(", ")}" else ""
                val typeParams = if (struct.typeParams.isNotEmpty()) "<${struct.typeParams.joinToString(", ")}>" else ""
                line("public struct ${struct.name}$typeParams$abilities {")
                indent {
                    struct.fields.forEach { f ->
                        line("${f.name}: ${renderType(f.type)},")
                    }
                }
                line("}")
                line()
            }

            // Functions
            module.functions.forEach { func ->
                renderFunction(func)
                line()
            }
        }
        line("}")
    }

    private fun renderFunction(func: MoveFunction) {
        val vis = when (func.visibility) {
            MoveVisibility.PRIVATE -> "" // default
            MoveVisibility.PUBLIC -> "public "
            MoveVisibility.PUBLIC_ENTRY -> "public entry "
            MoveVisibility.PUBLIC_FRIEND -> "public(friend) "
        }

        val typeParams = if (func.typeParams.isNotEmpty()) "<${func.typeParams.joinToString(", ")}>" else ""

        val params = func.params.joinToString(", ") { "${it.name}: ${renderType(it.type)}" }

        val ret = if (func.returnType != null) ": ${renderType(func.returnType)}" else ""

        line("${vis}fun ${func.name}$typeParams($params)$ret {")
        indent {
            func.body.forEach { stmt ->
                renderStmt(stmt)
            }
        }
        line("}")
    }

    private fun renderStmt(stmt: MoveStmt) {
        when (stmt) {
            is MoveStmt.Let -> {
                val typeAnn = if (stmt.type != null) ": ${renderType(stmt.type)}" else ""
                line("let ${stmt.name}$typeAnn = ${renderExpr(stmt.expr)};")
            }
            is MoveStmt.Assign -> {
                line("${renderExpr(stmt.lhs)} = ${renderExpr(stmt.rhs)};")
            }
            is MoveStmt.Mutate -> {
                line("*${renderExpr(stmt.lhs)} = ${renderExpr(stmt.rhs)};")
            }
            is MoveStmt.Return -> {
                if (stmt.expr != null) {
                    line("return ${renderExpr(stmt.expr)};")
                } else {
                    line("return")
                }
            }
            is MoveStmt.ExprStmt -> {
                line("${renderExpr(stmt.expr)};")
            }
            is MoveStmt.Assert -> {
                line("assert!(${renderExpr(stmt.cond)}, ${stmt.code});")
            }
            is MoveStmt.If -> {
                line("if (${renderExpr(stmt.cond)}) {")
                indent {
                    stmt.thenBlock.forEach { renderStmt(it) }
                }
                if (stmt.elseBlock != null) {
                    line("} else {")
                    indent {
                        stmt.elseBlock.forEach { renderStmt(it) }
                    }
                    line("}")
                } else {
                    line("};")
                }
            }
            is MoveStmt.Emit -> {
                 val fields = stmt.args.joinToString(", ") { "${it.field}: ${renderExpr(it.value)}" }
                 line("event::emit(${renderType(stmt.type)} { $fields });")
            }
            is MoveStmt.Comment -> {
                line("// ${stmt.text}")
            }
        }
    }

    private fun renderExpr(expr: MoveExpr): String {
        return when (expr) {
            is MoveExpr.BoolLit -> expr.value.toString()
            is MoveExpr.U64Lit -> "${expr.value}"
            is MoveExpr.AddressLit -> expr.value
            is MoveExpr.StringLit -> "b\"${expr.value}\""
            is MoveExpr.ByteStringLit -> "x\"${expr.value}\""
            is MoveExpr.Var -> expr.name
            is MoveExpr.Call -> {
                val typeArgs = if (expr.typeArgs.isNotEmpty()) "<${expr.typeArgs.joinToString(", ") { renderType(it) }}>" else ""
                val args = expr.args.joinToString(", ") { renderExpr(it) }
                val prefix = if (expr.module != null) "${expr.module}::" else ""
                "$prefix${expr.func}$typeArgs($args)"
            }
            is MoveExpr.FieldAccess -> "${renderExpr(expr.base)}.${expr.field}"
            is MoveExpr.BinOp -> "(${renderExpr(expr.lhs)} ${expr.op.symbol} ${renderExpr(expr.rhs)})"
            is MoveExpr.UnaryOp -> "${expr.op.symbol}${renderExpr(expr.arg)}"
            is MoveExpr.StructInit -> {
                val fields = expr.fields.joinToString(", ") { "${it.field}: ${renderExpr(it.value)}" }
                "${renderType(expr.type)} { $fields }"
            }
            is MoveExpr.Vector -> {
                val items = expr.items.joinToString(", ") { renderExpr(it) }
                "vector[$items]"
            }
            is MoveExpr.Deref -> "*${renderExpr(expr.expr)}"
            is MoveExpr.Borrow -> if (expr.mut) "&mut ${renderExpr(expr.expr)}" else "&${renderExpr(expr.expr)}"
            is MoveExpr.Cast -> "(${renderExpr(expr.expr)} as ${renderType(expr.type)})"
            is MoveExpr.IfElse -> "if (${renderExpr(expr.cond)}) ${renderExpr(expr.ifTrue)} else ${renderExpr(expr.ifFalse)}"
        }
    }

    private fun renderType(type: MoveType): String {
        return when(type) {
            MoveType.Bool -> "bool"
            MoveType.U8 -> "u8"
            MoveType.U64 -> "u64"
            MoveType.U128 -> "u128"
            MoveType.Address -> "address"
            is MoveType.Struct -> {
                val args = if (type.typeArgs.isEmpty()) "" else "<${type.typeArgs.joinToString(", ") { renderType(it) }}>"
                val prefix = if (type.module != null) "${type.module}::" else ""
                "$prefix${type.name}$args"
            }
            is MoveType.Vector -> "vector<${renderType(type.param)}>"
            is MoveType.Ref -> if (type.mut) "&mut ${renderType(type.param)}" else "&${renderType(type.param)}"
            is MoveType.TypeParam -> type.name
        }
    }

    private fun line(s: String = "") {
        sb.append("    ".repeat(indentLevel)).append(s).append("\n")
    }

    private fun indent(block: () -> Unit) {
        indentLevel++
        block()
        indentLevel--
    }
}
