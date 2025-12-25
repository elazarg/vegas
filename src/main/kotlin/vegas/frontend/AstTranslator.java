package vegas.frontend;

import vegas.generated.VegasBaseVisitor;
import vegas.generated.VegasParser.*;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.ParserRuleContext;

import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.net.URI;
import java.util.Objects;

import static java.util.stream.Collectors.*;

class AstTranslator extends VegasBaseVisitor<Ast> {

    private final URI uri; // document being translated

    public AstTranslator(URI uri) {
        this.uri = Objects.requireNonNull(uri);
    }
    /* ---------- Span helpers ---------- */

    private static int oneBasedCol(Token t) {
        // ANTLR charPositionInLine is 0-based; convert to 1-based.
        return t.getCharPositionInLine() + 1;
    }

    private static int endColInclusive(Token stop) {
        // Best effort: end column as (startCol + token text length - 1)
        // If text is null (rare), fall back to startCol.
        String txt = stop.getText();
        int len = (txt != null && !txt.isEmpty()) ? txt.length() : 1;
        return oneBasedCol(stop) + Math.max(len - 1, 0);
    }

    private Span spanOf(ParserRuleContext ctx) {
        Token s = ctx.getStart();
        Token e = ctx.getStop();
        if (e == null) {
            // Some rules may not have a stop (error nodes); approximate as single-point span.
            return new Span(uri, s.getLine(), oneBasedCol(s), s.getLine(), oneBasedCol(s));
        }
        return new Span(uri, s.getLine(), oneBasedCol(s), e.getLine(), endColInclusive(e));
    }

    private <T extends Ast> T withSpan(T node, ParserRuleContext ctx) {
        SourceLoc.INSTANCE.set(node, spanOf(ctx));
        return node;
    }

    @Override
    public GameAst visitProgram(ProgramContext ctx) {
        GameDecContext gameDec = ctx.gameDec();
        String gameName = gameDec.name.getText();

        // For now, only 'main' is supported
        if (!gameName.equals("main")) {
            throw new RuntimeException("Only 'game main()' is supported; found 'game " + gameName + "()' at line " + gameDec.getStart().getLine());
        }

        return new GameAst("", "", map(ctx.typeDec()), macros(ctx.macroDec()), ext(gameDec.ext()));
    }

    private Map<TypeExp.TypeId, TypeExp> map(List<TypeDecContext> ctxs) {
        return ctxs.stream().collect(toMap(ctx -> visitTypeId(ctx.typeId()), this::makeType));
    }

    private TypeExp makeType(TypeDecContext ctx) {
        return (TypeExp) withSpan(ctx.typeExp().accept(this), ctx);
    }

    private List<MacroDec> macros(List<MacroDecContext> ctxs) {
        return ctxs.stream().map(this::visitMacroDec).collect(toList());
    }

    public MacroDec visitMacroDec(MacroDecContext ctx) {
        return withSpan(MacroAstHelper.createMacroDec(
            ctx.name.getText(),
            list(ctx.params, this::visitParamDec),
            (TypeExp) ctx.resultType.accept(this),
            exp(ctx.body)
        ), ctx);
    }

    public MacroParam visitParamDec(ParamDecContext ctx) {
        TypeExp paramType = (TypeExp) ctx.type.accept(this);
        return withSpan(MacroAstHelper.createMacroParam(
            ctx.name.getText(),
            paramType
        ), ctx);
    }

    @Override
    public TypeExp.Subset visitSubsetTypeExp(SubsetTypeExpContext ctx) {
        return new TypeExp.Subset(ctx.vals.stream().map(this::num).collect(toSet()));
    }

    @Override
    public TypeExp.Range visitRangeTypeExp(RangeTypeExpContext ctx) {
        return new TypeExp.Range(num(ctx.start), num(ctx.end));
    }

    @Override
    public TypeExp.TypeId visitIdTypeExp(IdTypeExpContext t) {
        return withSpan(new TypeExp.TypeId(t.getText()), t);
    }

    @Override
    public TypeExp.TypeId visitTypeId(TypeIdContext t) {
        return withSpan(new TypeExp.TypeId(t.getText()), t);
    }

    private Exp.Const.Num num(Token v) {
        String text = v == null ? "0" : v.getText();
        return new Exp.Const.Num(Integer.parseInt(text));
    }

    private Role role(RoleIdContext roleId) {
        return withSpan(Role.of(roleId.getText()), roleId);
    }

    private Exp exp(ExpContext ctx) {
        if (ctx == null) return null; // Safety check
        Ast node = ctx.accept(this);
        if (node == null) throw new RuntimeException("Syntax error in expression at line " + ctx.getStart().getLine());
        return (Exp) withSpan(node, ctx);
    }

    private Ext ext(ExtContext ctx) {
        if (ctx == null) return null; // Safety check
        Ast node = ctx.accept(this);
        if (node == null) throw new RuntimeException("Syntax error in protocol (ext) at line " + ctx.getStart().getLine());
        return (Ext) withSpan(node, ctx);
    }

    @Override
    public Ext visitReceiveExt(ReceiveExtContext ctx) {
        Ext ext = ext(ctx.ext());
        Kind kind = toKind(ctx.kind);
        if (ctx.query().size() == 1)
            return new Ext.BindSingle(kind, query(ctx.query().getFirst()), ext);
        else
            return new Ext.Bind(kind, list(ctx.query(), this::query), ext);
    }

    private Query query(QueryContext ctx) {
        return withSpan(new Query(role(ctx.roleId()), list(ctx.decls, this::vardec), num(ctx.deposit), where(ctx.cond), handler(ctx.handler)), ctx);
    }

    private Outcome handler(OutcomeContext handler) {
        return handler != null ? outcome(handler) : null;
    }

    private Exp where(ExpContext cond) {
        return cond != null ? exp(cond) : new Exp.Const.Bool(true);
    }

    @Override
    public Ext.Value visitWithdrawExt(WithdrawExtContext ctx) {
        return new Ext.Value(outcome(ctx.outcome()));
    }

    @Override
    public Exp.UnOp visitUndefExp(UndefExpContext ctx) {
        Exp exp = exp(ctx.exp());
        return ctx.op.getText().equals("==")
                ? new Exp.UnOp("isUndefined", exp)
                : new Exp.UnOp("isDefined", exp);
    }

    @Override
    public Exp.UnOp visitUnOpExp(UnOpExpContext ctx) {
        return new Exp.UnOp(ctx.op.getText(), exp(ctx.exp()));
    }

    @Override
    public Exp visitIdExp(IdExpContext ctx) {
        String name = ctx.name.getText();
        switch (name) {
            case "true":
            case "false":
                assert false;
        }
        return var(ctx);
    }

    @Override
    public Exp.Const.Bool visitBoolLiteralExp(BoolLiteralExpContext ctx) {
        return new Exp.Const.Bool(Boolean.parseBoolean(ctx.getText()));
    }

    @Override
    public Exp.Field visitMemberExp(MemberExpContext ctx) {
        return Exp.Field.of(role(ctx.role), var(ctx.field));
    }

    @Override
    public Exp.Call visitCallExp(CallExpContext ctx) {
        return new Exp.Call(Exp.Var.of(ctx.callee.getText()), list(ctx.args, this::exp));
    }

    @Override
    public Exp.Cond visitIfExp(IfExpContext ctx) {
        return new Exp.Cond(exp(ctx.cond), exp(ctx.ifTrue), exp(ctx.ifFalse));
    }

    @Override
    public Exp.Let visitLetExp(LetExpContext ctx) {
        return new Exp.Let(vardec(ctx.dec), exp(ctx.init), exp(ctx.body));
    }

    @Override
    public Exp.BinOp visitBinOpEqExp(BinOpEqExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }

    @Override
    public Exp.BinOp visitBinOpAddExp(BinOpAddExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }

    @Override
    public Exp.BinOp visitBinOpCompExp(BinOpCompExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }

    @Override
    public Exp.BinOp visitBinOpBoolExp(BinOpBoolExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }

    @Override
    public Exp.BinOp visitBinOpMultExp(BinOpMultExpContext ctx) {
        return binop(ctx.op, ctx.left, ctx.right);
    }

    private Exp.BinOp binop(Token op, ExpContext left, ExpContext right) {
        return new Exp.BinOp(op.getText(), exp(left), exp(right));
    }

    @Override
    public Exp visitParenExp(ParenExpContext ctx) {
        return exp(ctx.exp());
    }

    @Override
    public Outcome visitParenOutcome(ParenOutcomeContext ctx) {
        return outcome(ctx.outcome());
    }
    @Override
    public Exp.Const.Address visitAddressLiteralExp(AddressLiteralExpContext ctx) {
        return new Exp.Const.Address(Integer.parseInt(ctx.ADDRESS().getText().substring(2), 16));
    }

    @Override
    public Exp.Const.Num visitNumLiteralExp(NumLiteralExpContext ctx) {
        return num(ctx.INT().getSymbol());
    }

    private Exp.Var var(IdExpContext v) {
        return withSpan(Exp.Var.of(v.getText()), v);
    }

    private Exp.Var var(VarIdContext v) {
        return withSpan(Exp.Var.of(v.getText()), v);
    }

    @Override
    public Outcome visitOutcomeExp(OutcomeExpContext ctx) {
        Map<Role, Exp> m = ctx.items.stream().collect(toMap(e -> role(e.role), e -> exp(e.exp())));
        return new Outcome.Value(m);
    }

    @Override
    public Outcome visitIfOutcome(IfOutcomeContext ctx) {
        return new Outcome.Cond(exp(ctx.cond), outcome(ctx.ifTrue), outcome(ctx.ifFalse));
    }

    @Override
    public Outcome visitLetOutcome(LetOutcomeContext ctx) {
        return new Outcome.Let(vardec(ctx.dec), exp(ctx.init), outcome(ctx.outcome()));
    }

    private Outcome outcome(OutcomeContext ctx) {
        if (ctx == null) return null;
        Ast node = ctx.accept(this);
        if (node == null) throw new RuntimeException("Syntax error in outcome at line " + ctx.getStart().getLine());
        return (Outcome) withSpan(node, ctx);
    }

    private <T1, T2> List<T2> list(List<T1> iterable, Function<T1, T2> f) {
        return iterable.stream().map(f).collect(toList());
    }

    private Kind toKind(Token kind) {
        return switch (kind.getText()) {
            case "join" -> Kind.JOIN;
            case "yield" -> Kind.YIELD;
            case "reveal" -> Kind.REVEAL;
            case "random" -> Kind.JOIN_CHANCE;
            default -> throw new AssertionError();
        };
    }

    private VarDec vardec(VarDecContext ctx) {
        TypeExp type = type(ctx);
        return new VarDec(var(ctx.varId()), (ctx.hidden != null) ? withSpan(new TypeExp.Hidden(type), ctx.typeExp()) : type);
    }

    private TypeExp type(VarDecContext ctx) {
        return switch (ctx.type.getText()) {
            case "bool" -> TypeExp.BOOL.INSTANCE;
            case "int" -> TypeExp.INT.INSTANCE;
            default -> withSpan(new TypeExp.TypeId(ctx.type.getText()), ctx.typeExp());
        };
    }
}
