package vegas.backend.solana

class AnchorRustGenerator {

    fun generate(program: SolanaProgram): String {
        val sb = StringBuilder()

        // 1. Header & Imports
        sb.appendLine("use anchor_lang::prelude::*;")
        sb.appendLine()
        sb.appendLine("declare_id!(\"Fg6PaFpoGXkYsidMpWTK6W2BeZ7FEfcYkg476zPFsLnS\"); // Placeholder ID")
        sb.appendLine()

        // 2. Program Module
        sb.appendLine("#[program]")
        sb.appendLine("pub mod ${program.name.lowercase()} {")
        sb.appendLine("    use super::*;")
        sb.appendLine()

        // Instructions
        for (instr in program.instructions) {
            generateInstructionParams(sb, instr)
        }
        sb.appendLine("}")
        sb.appendLine()

        // 3. Instruction Context Structs
        for (instr in program.instructions) {
            generateContextStruct(sb, instr)
        }

        // 4. State Structs (Accounts)
        generateAccountStruct(sb, program.stateStruct)
        for (struct in program.additionalStructs) {
            generateStruct(sb, struct)
        }

        // 5. Errors
        if (program.errors.isNotEmpty()) {
            generateErrors(sb, program.errors)
        }

        return sb.toString()
    }

    private fun generateInstructionParams(sb: StringBuilder, instr: SolanaInstruction) {
        sb.appendLine("    pub fn ${instr.name}(ctx: Context<${instr.name.capitalize()}>, ${instr.params.joinToString(", ") { "${it.name}: ${generateAnchorType(it.type)}" }}) -> Result<()> {")
        // Account Bindings
        for (acc in instr.accounts) {
            // Special handling for system_program which is not usually bound as variable but accessed via ctx
            if (acc.name == "system_program") continue

            val mut = if (acc.isMut) "&mut " else "&"
            sb.appendLine("        let ${acc.name} = ${mut}ctx.accounts.${acc.name};")
        }
        generateBody(sb, instr.body, "        ")
        sb.appendLine("        Ok(())")
        sb.appendLine("    }")
        sb.appendLine()
    }

    private fun String.capitalize(): String = replaceFirstChar { it.uppercase() }

    private fun generateContextStruct(sb: StringBuilder, instr: SolanaInstruction) {
        sb.appendLine("#[derive(Accounts)]")
        if (instr.params.isNotEmpty()) {
             sb.append("#[instruction(")
             sb.append(instr.params.joinToString(", ") { "${it.name}: ${generateAnchorType(it.type)}" })
             sb.appendLine(")]")
        }
        sb.appendLine("pub struct ${instr.name.capitalize()}<'info> {")
        for (account in instr.accounts) {
            // Add #[account(mut)] if needed and not present in constraints
            val explicitMut = account.constraints.any { it.contains("mut") }
            if (account.isMut && !explicitMut) {
                sb.appendLine("    #[account(mut)]")
            }

            for (constraint in account.constraints) {
                sb.appendLine("    $constraint")
            }
            sb.appendLine("    pub ${account.name}: ${account.type},")
        }
        sb.appendLine("}")
        sb.appendLine()
    }

    private fun generateAccountStruct(sb: StringBuilder, struct: SolanaAccountStruct) {
        sb.appendLine("#[account]")
        sb.appendLine("#[derive(InitSpace)]")
        sb.appendLine("pub struct ${struct.name} {")
        for (field in struct.fields) {
            sb.appendLine("    pub ${field.name}: ${generateAnchorType(field.type)},")
        }
        sb.appendLine("}")
        sb.appendLine()
    }

    private fun generateStruct(sb: StringBuilder, struct: SolanaStruct) {
        sb.appendLine("#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy, InitSpace)]")
        sb.appendLine("pub struct ${struct.name} {")
        for (field in struct.fields) {
            sb.appendLine("    pub ${field.name}: ${generateAnchorType(field.type)},")
        }
        sb.appendLine("}")
        sb.appendLine()
    }

    private fun generateErrors(sb: StringBuilder, errors: List<SolanaError>) {
        sb.appendLine("#[error_code]")
        sb.appendLine("pub enum ErrorCode {")
        for (error in errors) {
            sb.appendLine("    #[msg(\"${error.msg}\")]")
            sb.appendLine("    ${error.name},")
        }
        sb.appendLine("}")
        sb.appendLine()
    }

    private fun generateBody(sb: StringBuilder, stmts: List<SolanaStmt>, indent: String) {
        for (stmt in stmts) {
            generateStmt(sb, stmt, indent)
        }
    }

    private fun generateStmt(sb: StringBuilder, stmt: SolanaStmt, indent: String) {
        when (stmt) {
            is SolanaStmt.Let -> {
                val typeStr = if (stmt.type != null) ": ${generateAnchorType(stmt.type)}" else ""
                sb.appendLine("$indent let ${stmt.name}$typeStr = ${generateAnchorExpr(stmt.value)};")
            }
            is SolanaStmt.Assign -> {
                sb.appendLine("$indent ${generateAnchorExpr(stmt.target)} = ${generateAnchorExpr(stmt.value)};")
            }
            is SolanaStmt.Require -> {
                sb.appendLine("$indent require!(${generateAnchorExpr(stmt.condition)}, ErrorCode::${stmt.error.name});")
            }
            is SolanaStmt.If -> {
                sb.appendLine("$indent if ${generateAnchorExpr(stmt.condition)} {")
                generateBody(sb, stmt.thenBranch, "$indent    ")
                if (stmt.elseBranch.isNotEmpty()) {
                    sb.appendLine("$indent } else {")
                    generateBody(sb, stmt.elseBranch, "$indent    ")
                }
                sb.appendLine("$indent }")
            }
            is SolanaStmt.ExprStmt -> {
                sb.appendLine("$indent ${generateAnchorExpr(stmt.expr)};")
            }
            is SolanaStmt.TransferSol -> {
                sb.appendLine("$indent anchor_lang::system_program::transfer(")
                sb.appendLine("$indent    anchor_lang::context::CpiContext::new(")
                sb.appendLine("$indent        ctx.accounts.system_program.to_account_info(),")
                sb.appendLine("$indent        anchor_lang::system_program::Transfer {")
                sb.appendLine("$indent            from: ctx.accounts.${stmt.from}.to_account_info(),")
                sb.appendLine("$indent            to: ctx.accounts.${stmt.to}.to_account_info(),")
                sb.appendLine("$indent        },")
                sb.appendLine("$indent    ),")
                sb.appendLine("$indent    ${generateAnchorExpr(stmt.amount)},")
                sb.appendLine("$indent )?;")
            }
            is SolanaStmt.Code -> {
                stmt.text.lines().forEach { line ->
                    sb.appendLine("$indent $line")
                }
            }
            is SolanaStmt.Comment -> {
                sb.appendLine("$indent // ${stmt.text}")
            }
        }
    }
}

fun generateAnchorRust(program: SolanaProgram): String {
    return AnchorRustGenerator().generate(program)
}

fun generateAnchorExpr(expr: SolanaExpr): String {
    return when (expr) {
        is SolanaExpr.IntLit -> "${expr.v}"
        is SolanaExpr.BoolLit -> "${expr.v}"
        is SolanaExpr.BytesLit -> "&[${expr.bytes.joinToString(", ")}]"
        is SolanaExpr.StringLit -> "\"${expr.v}\""
        is SolanaExpr.Var -> expr.name
        is SolanaExpr.FieldAccess -> "${generateAnchorExpr(expr.target)}.${expr.field}"
        is SolanaExpr.Index -> "${generateAnchorExpr(expr.target)}[${generateAnchorExpr(expr.index)} as usize]"
        is SolanaExpr.Binary -> "(${generateAnchorExpr(expr.l)} ${expr.op.symbol} ${generateAnchorExpr(expr.r)})"
        is SolanaExpr.Unary -> "${expr.op.symbol}(${generateAnchorExpr(expr.expr)})"
        is SolanaExpr.ClockTimestamp -> "Clock::get()?.unix_timestamp"
        is SolanaExpr.PubkeyDefault -> "Pubkey::default()"
        is SolanaExpr.Call -> "${expr.func}(${expr.args.joinToString(", ") { generateAnchorExpr(it) }})"
        is SolanaExpr.MethodCall -> "${generateAnchorExpr(expr.target)}.${expr.method}(${expr.args.joinToString(", ") { generateAnchorExpr(it) }})"
        is SolanaExpr.If -> "if ${generateAnchorExpr(expr.condition)} { ${generateAnchorExpr(expr.thenExpr)} } else { ${generateAnchorExpr(expr.elseExpr)} }"
        is SolanaExpr.Raw -> expr.text
    }.toString()
}

fun generateAnchorType(type: SolanaType): String {
    return when (type) {
        SolanaType.U8 -> "u8"
        SolanaType.U64 -> "u64"
        SolanaType.I64 -> "i64"
        SolanaType.Bool -> "bool"
        SolanaType.Pubkey -> "Pubkey"
        is SolanaType.Array -> "[${generateAnchorType(type.inner)}; ${type.size}]"
        is SolanaType.Vec -> "Vec<${generateAnchorType(type.inner)}>"
        SolanaType.String -> "String"
        is SolanaType.Custom -> type.name
    }.toString()
}
