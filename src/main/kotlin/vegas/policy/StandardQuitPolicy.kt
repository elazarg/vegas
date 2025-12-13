package vegas.policy

import vegas.ir.ActionId
import vegas.FieldRef
import vegas.RoleId
import vegas.VarId
import vegas.ir.ActionDag
import vegas.ir.Expr
import vegas.backend.evm.*
import vegas.backend.evm.EvmExpr.*
import vegas.backend.evm.EvmStmt.*
import vegas.backend.evm.EvmType.*

class StandardQuitPolicy : EvmQuitPolicy {

    override fun getQuitDelta(
        role: RoleId,
        pendingActions: List<ActionId>,
        dag: ActionDag
    ): Map<FieldRef, Expr.Const> {
        val delta = mutableMapOf<FieldRef, Expr.Const>()
        for (actionId in pendingActions) {
            val spec = dag.spec(actionId)
            for (param in spec.params) {
                val field = FieldRef(role, param.name)
                delta[field] = Expr.Const.Quit
            }
        }
        return delta
    }

    override fun resolveRead(value: Expr.Const?, field: FieldRef): Expr.Const? {
        return value
    }

    override fun storage(): List<EvmStorageSlot> {
        return listOf(
            EvmStorageSlot("lastTs", Uint256),
            EvmStorageSlot("TIMEOUT", Uint256, IntLit(86400), isImmutable = true),
            EvmStorageSlot("bailed", Mapping(EnumType("Role"), Bool))
        )
    }

    override fun helpers(): List<EvmFunction> {
        return listOf(
            EvmFunction(
                name = "_check_timestamp",
                inputs = listOf(EvmParam(VarId("role"), EnumType("Role"))),
                body = listOf(
                    // if (role == Role.None) return;
                    EvmStmt.If(
                        Binary(BinaryOp.EQ, Var(VarId("role")), EnumValue("Role", "None")),
                        listOf(Return())
                    ),
                    // if (block.timestamp > lastTs + TIMEOUT) { bailed[role] = true; lastTs = block.timestamp; }
                    EvmStmt.If(
                        Binary(BinaryOp.GT, BuiltIn.Timestamp, Binary(BinaryOp.ADD, Member(BuiltIn.Self, "lastTs"), Var(VarId("TIMEOUT")))),
                        listOf(
                            Assign(Index(Member(BuiltIn.Self, "bailed"), Var(VarId("role"))), BoolLit(true)),
                            Assign(Member(BuiltIn.Self, "lastTs"), BuiltIn.Timestamp)
                        )
                    )
                )
            )
        )
    }

    override fun preActionLogic(role: RoleId, actionId: ActionId, dependencies: List<ActionId>): List<EvmStmt> {
        val stmts = mutableListOf<EvmStmt>()
        val roleEnum = EnumValue("Role", role.name)
        val actIdx = IntLit(actionId.second)

        // 1. Check Invoker (replaced 'by' modifier)
        // require(roles[msg.sender] == role, "bad role")
        stmts.add(Require(
            Binary(BinaryOp.EQ, Index(Member(BuiltIn.Self, "roles"), BuiltIn.MsgSender), roleEnum),
            "bad role"
        ))

        // _check_timestamp(role)
        stmts.add(ExprStmt(Call("_check_timestamp", listOf(roleEnum))))

        // require(!bailed[role], "you bailed")
        stmts.add(Require(
            Unary(UnaryOp.NOT, Index(Member(BuiltIn.Self, "bailed"), roleEnum)),
            "you bailed"
        ))

        // 2. Check Not Done (replaced 'action' modifier part 1)
        // require(!actionDone[role][id], "already done")
        stmts.add(Require(
            Unary(UnaryOp.NOT, Index(Index(Member(BuiltIn.Self, "actionDone"), roleEnum), actIdx)),
            "already done"
        ))

        // 3. Check Dependencies (replaced 'depends' modifier)
        for (dep in dependencies) {
            val depRole = EnumValue("Role", dep.first.name)
            val depIdx = IntLit(dep.second)

            // _check_timestamp(depRole)
            stmts.add(ExprStmt(Call("_check_timestamp", listOf(depRole))))

            // if (!bailed[depRole]) { require(actionDone[depRole][depIdx], "dependency not satisfied") }
            stmts.add(EvmStmt.If(
                Unary(UnaryOp.NOT, Index(Member(BuiltIn.Self, "bailed"), depRole)),
                listOf(
                    Require(
                        Index(Index(Member(BuiltIn.Self, "actionDone"), depRole), depIdx),
                        "dependency not satisfied"
                    )
                )
            ))
        }

        return stmts
    }

    override fun postActionLogic(role: RoleId, actionId: ActionId): List<EvmStmt> {
        val stmts = mutableListOf<EvmStmt>()
        val roleEnum = EnumValue("Role", role.name)
        val actIdx = IntLit(actionId.second)

        // actionDone[role][id] = true
        stmts.add(Assign(
            Index(Index(Member(BuiltIn.Self, "actionDone"), roleEnum), actIdx),
            BoolLit(true)
        ))

        // actionTimestamp[role][id] = block.timestamp
        stmts.add(Assign(
            Index(Index(Member(BuiltIn.Self, "actionTimestamp"), roleEnum), actIdx),
            BuiltIn.Timestamp
        ))

        // lastTs = block.timestamp
        stmts.add(Assign(Member(BuiltIn.Self, "lastTs"), BuiltIn.Timestamp))

        return stmts
    }
}
