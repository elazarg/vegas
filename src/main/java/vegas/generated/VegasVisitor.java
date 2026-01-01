// Generated from Vegas.g4 by ANTLR 4.13.2
package vegas.generated;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link VegasParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface VegasVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link VegasParser#program}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProgram(VegasParser.ProgramContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#gameDec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGameDec(VegasParser.GameDecContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#gameId}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGameId(VegasParser.GameIdContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#typeDec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeDec(VegasParser.TypeDecContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#macroDec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMacroDec(VegasParser.MacroDecContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#paramDec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParamDec(VegasParser.ParamDecContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SubsetTypeExp}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSubsetTypeExp(VegasParser.SubsetTypeExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code RangeTypeExp}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRangeTypeExp(VegasParser.RangeTypeExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IdTypeExp}
	 * labeled alternative in {@link VegasParser#typeExp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdTypeExp(VegasParser.IdTypeExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ReceiveExt}
	 * labeled alternative in {@link VegasParser#ext}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitReceiveExt(VegasParser.ReceiveExtContext ctx);
	/**
	 * Visit a parse tree produced by the {@code WithdrawExt}
	 * labeled alternative in {@link VegasParser#ext}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitWithdrawExt(VegasParser.WithdrawExtContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#query}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitQuery(VegasParser.QueryContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IfQueryHandler}
	 * labeled alternative in {@link VegasParser#queryHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfQueryHandler(VegasParser.IfQueryHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code LetQueryHandler}
	 * labeled alternative in {@link VegasParser#queryHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLetQueryHandler(VegasParser.LetQueryHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ParenQueryHandler}
	 * labeled alternative in {@link VegasParser#queryHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenQueryHandler(VegasParser.ParenQueryHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code OutcomeQueryHandler}
	 * labeled alternative in {@link VegasParser#queryHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOutcomeQueryHandler(VegasParser.OutcomeQueryHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SplitQueryHandler}
	 * labeled alternative in {@link VegasParser#queryHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSplitQueryHandler(VegasParser.SplitQueryHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BurnQueryHandler}
	 * labeled alternative in {@link VegasParser#queryHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBurnQueryHandler(VegasParser.BurnQueryHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code NullQueryHandler}
	 * labeled alternative in {@link VegasParser#queryHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNullQueryHandler(VegasParser.NullQueryHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code SplitHandler}
	 * labeled alternative in {@link VegasParser#groupHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitSplitHandler(VegasParser.SplitHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BurnHandler}
	 * labeled alternative in {@link VegasParser#groupHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBurnHandler(VegasParser.BurnHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code NullHandler}
	 * labeled alternative in {@link VegasParser#groupHandler}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNullHandler(VegasParser.NullHandlerContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IfOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfOutcome(VegasParser.IfOutcomeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code LetOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLetOutcome(VegasParser.LetOutcomeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ParenOutcome}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenOutcome(VegasParser.ParenOutcomeContext ctx);
	/**
	 * Visit a parse tree produced by the {@code OutcomeExp}
	 * labeled alternative in {@link VegasParser#outcome}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOutcomeExp(VegasParser.OutcomeExpContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#item}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitItem(VegasParser.ItemContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpEqExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpEqExp(VegasParser.BinOpEqExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code UndefExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUndefExp(VegasParser.UndefExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpAddExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpAddExp(VegasParser.BinOpAddExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpCompExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpCompExp(VegasParser.BinOpCompExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code UnOpExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnOpExp(VegasParser.UnOpExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code MemberExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitMemberExp(VegasParser.MemberExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IdExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIdExp(VegasParser.IdExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code CallExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCallExp(VegasParser.CallExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code IfExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIfExp(VegasParser.IfExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpBoolExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpBoolExp(VegasParser.BinOpBoolExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code ParenExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitParenExp(VegasParser.ParenExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BoolLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolLiteralExp(VegasParser.BoolLiteralExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code LetExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLetExp(VegasParser.LetExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code AddressLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAddressLiteralExp(VegasParser.AddressLiteralExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code BinOpMultExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinOpMultExp(VegasParser.BinOpMultExpContext ctx);
	/**
	 * Visit a parse tree produced by the {@code NumLiteralExp}
	 * labeled alternative in {@link VegasParser#exp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNumLiteralExp(VegasParser.NumLiteralExpContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#varDec}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarDec(VegasParser.VarDecContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#typeId}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTypeId(VegasParser.TypeIdContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#varId}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVarId(VegasParser.VarIdContext ctx);
	/**
	 * Visit a parse tree produced by {@link VegasParser#roleId}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRoleId(VegasParser.RoleIdContext ctx);
}