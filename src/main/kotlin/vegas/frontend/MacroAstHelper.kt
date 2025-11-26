package vegas.frontend

import vegas.VarId

/**
 * Helper functions for constructing macro AST nodes from Java code.
 * Needed because value class parameters make constructors inaccessible from Java.
 */
object MacroAstHelper {
    @JvmStatic
    fun createMacroDec(
        name: String,
        params: List<MacroParam>,
        resultType: TypeExp,
        body: Exp
    ): MacroDec {
        return MacroDec(VarId(name), params, resultType, body)
    }

    @JvmStatic
    fun createMacroParam(name: String, type: TypeExp): MacroParam {
        return MacroParam(VarId(name), type)
    }
}
