// Generated from Vegas.g4 by ANTLR 4.13.2
package vegas.generated;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue", "this-escape"})
public class VegasParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, T__18=19, T__19=20, T__20=21, T__21=22, T__22=23, T__23=24, 
		T__24=25, T__25=26, T__26=27, T__27=28, T__28=29, T__29=30, T__30=31, 
		T__31=32, T__32=33, T__33=34, T__34=35, T__35=36, T__36=37, T__37=38, 
		T__38=39, T__39=40, T__40=41, T__41=42, T__42=43, T__43=44, T__44=45, 
		T__45=46, T__46=47, T__47=48, T__48=49, T__49=50, T__50=51, T__51=52, 
		T__52=53, T__53=54, ROLE_ID=55, LOWER_ID=56, INT=57, ADDRESS=58, STRING=59, 
		BlockComment=60, LineComment=61, WS=62;
	public static final int
		RULE_program = 0, RULE_gameDec = 1, RULE_gameId = 2, RULE_typeDec = 3, 
		RULE_macroDec = 4, RULE_paramDec = 5, RULE_typeExp = 6, RULE_ext = 7, 
		RULE_query = 8, RULE_randomQuery = 9, RULE_queryHandler = 10, RULE_groupHandler = 11, 
		RULE_outcome = 12, RULE_exitItem = 13, RULE_utilityItem = 14, RULE_item = 15, 
		RULE_exp = 16, RULE_varDec = 17, RULE_distExp = 18, RULE_distVal = 19, 
		RULE_weightedItem = 20, RULE_typeId = 21, RULE_varId = 22, RULE_roleId = 23;
	private static String[] makeRuleNames() {
		return new String[] {
			"program", "gameDec", "gameId", "typeDec", "macroDec", "paramDec", "typeExp", 
			"ext", "query", "randomQuery", "queryHandler", "groupHandler", "outcome", 
			"exitItem", "utilityItem", "item", "exp", "varDec", "distExp", "distVal", 
			"weightedItem", "typeId", "varId", "roleId"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'game'", "'('", "')'", "'{'", "'}'", "'type'", "'='", "'macro'", 
			"','", "':'", "';'", "'..'", "'join'", "'yield'", "'reveal'", "'commit'", 
			"'or'", "'random'", "'sample'", "'withdraw'", "'exit'", "'utility'", 
			"'$'", "'where'", "'||'", "'?'", "'let'", "'in'", "'split'", "'burn'", 
			"'null'", "'->'", "'-'", "'.'", "'!'", "'*'", "'/'", "'%'", "'+'", "'!='", 
			"'=='", "'<'", "'<='", "'>='", "'>'", "'<->'", "'<-!->'", "'&&'", "'true'", 
			"'false'", "'let!'", "'~'", "'uniform'", "'weighted'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, "ROLE_ID", "LOWER_ID", "INT", 
			"ADDRESS", "STRING", "BlockComment", "LineComment", "WS"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Vegas.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public VegasParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ProgramContext extends ParserRuleContext {
		public GameDecContext gameDec() {
			return getRuleContext(GameDecContext.class,0);
		}
		public TerminalNode EOF() { return getToken(VegasParser.EOF, 0); }
		public List<TypeDecContext> typeDec() {
			return getRuleContexts(TypeDecContext.class);
		}
		public TypeDecContext typeDec(int i) {
			return getRuleContext(TypeDecContext.class,i);
		}
		public List<MacroDecContext> macroDec() {
			return getRuleContexts(MacroDecContext.class);
		}
		public MacroDecContext macroDec(int i) {
			return getRuleContext(MacroDecContext.class,i);
		}
		public ProgramContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_program; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitProgram(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ProgramContext program() throws RecognitionException {
		ProgramContext _localctx = new ProgramContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_program);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(52);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__5 || _la==T__7) {
				{
				setState(50);
				_errHandler.sync(this);
				switch (_input.LA(1)) {
				case T__5:
					{
					setState(48);
					typeDec();
					}
					break;
				case T__7:
					{
					setState(49);
					macroDec();
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				}
				setState(54);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(55);
			gameDec();
			setState(56);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class GameDecContext extends ParserRuleContext {
		public GameIdContext name;
		public ExtContext ext() {
			return getRuleContext(ExtContext.class,0);
		}
		public GameIdContext gameId() {
			return getRuleContext(GameIdContext.class,0);
		}
		public GameDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_gameDec; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitGameDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GameDecContext gameDec() throws RecognitionException {
		GameDecContext _localctx = new GameDecContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_gameDec);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(58);
			match(T__0);
			setState(59);
			((GameDecContext)_localctx).name = gameId();
			setState(60);
			match(T__1);
			setState(61);
			match(T__2);
			setState(62);
			match(T__3);
			setState(63);
			ext();
			setState(64);
			match(T__4);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class GameIdContext extends ParserRuleContext {
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public GameIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_gameId; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitGameId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GameIdContext gameId() throws RecognitionException {
		GameIdContext _localctx = new GameIdContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_gameId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(66);
			varId();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class TypeDecContext extends ParserRuleContext {
		public TypeIdContext name;
		public TypeExpContext typeExp() {
			return getRuleContext(TypeExpContext.class,0);
		}
		public TypeIdContext typeId() {
			return getRuleContext(TypeIdContext.class,0);
		}
		public TypeDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeDec; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitTypeDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeDecContext typeDec() throws RecognitionException {
		TypeDecContext _localctx = new TypeDecContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_typeDec);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(68);
			match(T__5);
			setState(69);
			((TypeDecContext)_localctx).name = typeId();
			setState(70);
			match(T__6);
			setState(71);
			typeExp();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class MacroDecContext extends ParserRuleContext {
		public VarIdContext name;
		public ParamDecContext paramDec;
		public List<ParamDecContext> params = new ArrayList<ParamDecContext>();
		public TypeExpContext resultType;
		public ExpContext body;
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public TypeExpContext typeExp() {
			return getRuleContext(TypeExpContext.class,0);
		}
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public List<ParamDecContext> paramDec() {
			return getRuleContexts(ParamDecContext.class);
		}
		public ParamDecContext paramDec(int i) {
			return getRuleContext(ParamDecContext.class,i);
		}
		public MacroDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_macroDec; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitMacroDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final MacroDecContext macroDec() throws RecognitionException {
		MacroDecContext _localctx = new MacroDecContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_macroDec);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(73);
			match(T__7);
			setState(74);
			((MacroDecContext)_localctx).name = varId();
			setState(75);
			match(T__1);
			setState(84);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==LOWER_ID) {
				{
				setState(76);
				((MacroDecContext)_localctx).paramDec = paramDec();
				((MacroDecContext)_localctx).params.add(((MacroDecContext)_localctx).paramDec);
				setState(81);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(77);
					match(T__8);
					setState(78);
					((MacroDecContext)_localctx).paramDec = paramDec();
					((MacroDecContext)_localctx).params.add(((MacroDecContext)_localctx).paramDec);
					}
					}
					setState(83);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(86);
			match(T__2);
			setState(87);
			match(T__9);
			setState(88);
			((MacroDecContext)_localctx).resultType = typeExp();
			setState(89);
			match(T__6);
			setState(90);
			((MacroDecContext)_localctx).body = exp(0);
			setState(92);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__10) {
				{
				setState(91);
				match(T__10);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ParamDecContext extends ParserRuleContext {
		public VarIdContext name;
		public TypeExpContext type;
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public TypeExpContext typeExp() {
			return getRuleContext(TypeExpContext.class,0);
		}
		public ParamDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_paramDec; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitParamDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ParamDecContext paramDec() throws RecognitionException {
		ParamDecContext _localctx = new ParamDecContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_paramDec);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(94);
			((ParamDecContext)_localctx).name = varId();
			setState(95);
			match(T__9);
			setState(96);
			((ParamDecContext)_localctx).type = typeExp();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class TypeExpContext extends ParserRuleContext {
		public TypeExpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeExp; }
	 
		public TypeExpContext() { }
		public void copyFrom(TypeExpContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IdTypeExpContext extends TypeExpContext {
		public TypeIdContext name;
		public TypeIdContext typeId() {
			return getRuleContext(TypeIdContext.class,0);
		}
		public IdTypeExpContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIdTypeExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class SubsetTypeExpContext extends TypeExpContext {
		public Token INT;
		public List<Token> vals = new ArrayList<Token>();
		public List<TerminalNode> INT() { return getTokens(VegasParser.INT); }
		public TerminalNode INT(int i) {
			return getToken(VegasParser.INT, i);
		}
		public SubsetTypeExpContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitSubsetTypeExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class RangeTypeExpContext extends TypeExpContext {
		public Token start;
		public Token end;
		public List<TerminalNode> INT() { return getTokens(VegasParser.INT); }
		public TerminalNode INT(int i) {
			return getToken(VegasParser.INT, i);
		}
		public RangeTypeExpContext(TypeExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitRangeTypeExp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeExpContext typeExp() throws RecognitionException {
		TypeExpContext _localctx = new TypeExpContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_typeExp);
		int _la;
		try {
			setState(114);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				_localctx = new SubsetTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(98);
				match(T__3);
				setState(99);
				((SubsetTypeExpContext)_localctx).INT = match(INT);
				((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
				setState(104);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(100);
					match(T__8);
					setState(101);
					((SubsetTypeExpContext)_localctx).INT = match(INT);
					((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
					}
					}
					setState(106);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(107);
				match(T__4);
				}
				break;
			case 2:
				_localctx = new RangeTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(108);
				match(T__3);
				setState(109);
				((RangeTypeExpContext)_localctx).start = match(INT);
				setState(110);
				match(T__11);
				setState(111);
				((RangeTypeExpContext)_localctx).end = match(INT);
				setState(112);
				match(T__4);
				}
				break;
			case 3:
				_localctx = new IdTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(113);
				((IdTypeExpContext)_localctx).name = typeId();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ExtContext extends ParserRuleContext {
		public ExtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ext; }
	 
		public ExtContext() { }
		public void copyFrom(ExtContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class RandomExtContext extends ExtContext {
		public ExtContext ext() {
			return getRuleContext(ExtContext.class,0);
		}
		public List<RandomQueryContext> randomQuery() {
			return getRuleContexts(RandomQueryContext.class);
		}
		public RandomQueryContext randomQuery(int i) {
			return getRuleContext(RandomQueryContext.class,i);
		}
		public RandomExtContext(ExtContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitRandomExt(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ReceiveExtContext extends ExtContext {
		public Token kind;
		public GroupHandlerContext handler;
		public ExtContext ext() {
			return getRuleContext(ExtContext.class,0);
		}
		public List<QueryContext> query() {
			return getRuleContexts(QueryContext.class);
		}
		public QueryContext query(int i) {
			return getRuleContext(QueryContext.class,i);
		}
		public GroupHandlerContext groupHandler() {
			return getRuleContext(GroupHandlerContext.class,0);
		}
		public ReceiveExtContext(ExtContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitReceiveExt(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class WithdrawExtContext extends ExtContext {
		public ExitItemContext exitItem;
		public List<ExitItemContext> exits = new ArrayList<ExitItemContext>();
		public UtilityItemContext utilityItem;
		public List<UtilityItemContext> utilities = new ArrayList<UtilityItemContext>();
		public OutcomeContext outcome() {
			return getRuleContext(OutcomeContext.class,0);
		}
		public List<ExitItemContext> exitItem() {
			return getRuleContexts(ExitItemContext.class);
		}
		public ExitItemContext exitItem(int i) {
			return getRuleContext(ExitItemContext.class,i);
		}
		public List<UtilityItemContext> utilityItem() {
			return getRuleContexts(UtilityItemContext.class);
		}
		public UtilityItemContext utilityItem(int i) {
			return getRuleContext(UtilityItemContext.class,i);
		}
		public WithdrawExtContext(ExtContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitWithdrawExt(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class SampleExtContext extends ExtContext {
		public RoleIdContext owner;
		public VarDecContext varDec;
		public List<VarDecContext> bindings = new ArrayList<VarDecContext>();
		public ExtContext ext() {
			return getRuleContext(ExtContext.class,0);
		}
		public List<VarDecContext> varDec() {
			return getRuleContexts(VarDecContext.class);
		}
		public VarDecContext varDec(int i) {
			return getRuleContext(VarDecContext.class,i);
		}
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public SampleExtContext(ExtContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitSampleExt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExtContext ext() throws RecognitionException {
		ExtContext _localctx = new ExtContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_ext);
		int _la;
		try {
			setState(179);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__12:
			case T__13:
			case T__14:
			case T__15:
				_localctx = new ReceiveExtContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(116);
				((ReceiveExtContext)_localctx).kind = _input.LT(1);
				_la = _input.LA(1);
				if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 122880L) != 0)) ) {
					((ReceiveExtContext)_localctx).kind = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(119);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__16) {
					{
					setState(117);
					match(T__16);
					setState(118);
					((ReceiveExtContext)_localctx).handler = groupHandler();
					}
				}

				setState(122); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(121);
					query();
					}
					}
					setState(124); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ROLE_ID );
				setState(126);
				match(T__10);
				setState(127);
				ext();
				}
				break;
			case T__17:
				_localctx = new RandomExtContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(129);
				match(T__17);
				setState(131); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(130);
					randomQuery();
					}
					}
					setState(133); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ROLE_ID );
				setState(135);
				match(T__10);
				setState(136);
				ext();
				}
				break;
			case T__18:
				_localctx = new SampleExtContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(138);
				match(T__18);
				setState(140);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==ROLE_ID) {
					{
					setState(139);
					((SampleExtContext)_localctx).owner = roleId();
					}
				}

				setState(142);
				match(T__1);
				setState(143);
				((SampleExtContext)_localctx).varDec = varDec();
				((SampleExtContext)_localctx).bindings.add(((SampleExtContext)_localctx).varDec);
				setState(148);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(144);
					match(T__8);
					setState(145);
					((SampleExtContext)_localctx).varDec = varDec();
					((SampleExtContext)_localctx).bindings.add(((SampleExtContext)_localctx).varDec);
					}
					}
					setState(150);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(151);
				match(T__2);
				setState(152);
				match(T__10);
				setState(153);
				ext();
				}
				break;
			case T__19:
				_localctx = new WithdrawExtContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(155);
				match(T__19);
				setState(156);
				outcome();
				setState(166);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__20) {
					{
					setState(157);
					match(T__20);
					setState(158);
					match(T__3);
					setState(160); 
					_errHandler.sync(this);
					_la = _input.LA(1);
					do {
						{
						{
						setState(159);
						((WithdrawExtContext)_localctx).exitItem = exitItem();
						((WithdrawExtContext)_localctx).exits.add(((WithdrawExtContext)_localctx).exitItem);
						}
						}
						setState(162); 
						_errHandler.sync(this);
						_la = _input.LA(1);
					} while ( _la==ROLE_ID );
					setState(164);
					match(T__4);
					}
				}

				setState(177);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__21) {
					{
					setState(168);
					match(T__21);
					setState(169);
					match(T__3);
					setState(171); 
					_errHandler.sync(this);
					_la = _input.LA(1);
					do {
						{
						{
						setState(170);
						((WithdrawExtContext)_localctx).utilityItem = utilityItem();
						((WithdrawExtContext)_localctx).utilities.add(((WithdrawExtContext)_localctx).utilityItem);
						}
						}
						setState(173); 
						_errHandler.sync(this);
						_la = _input.LA(1);
					} while ( _la==ROLE_ID );
					setState(175);
					match(T__4);
					}
				}

				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class QueryContext extends ParserRuleContext {
		public RoleIdContext role;
		public VarDecContext varDec;
		public List<VarDecContext> decls = new ArrayList<VarDecContext>();
		public Token deposit;
		public ExpContext cond;
		public QueryHandlerContext handler;
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public TerminalNode INT() { return getToken(VegasParser.INT, 0); }
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public QueryHandlerContext queryHandler() {
			return getRuleContext(QueryHandlerContext.class,0);
		}
		public List<VarDecContext> varDec() {
			return getRuleContexts(VarDecContext.class);
		}
		public VarDecContext varDec(int i) {
			return getRuleContext(VarDecContext.class,i);
		}
		public QueryContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_query; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitQuery(this);
			else return visitor.visitChildren(this);
		}
	}

	public final QueryContext query() throws RecognitionException {
		QueryContext _localctx = new QueryContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_query);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(181);
			((QueryContext)_localctx).role = roleId();
			setState(194);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__1) {
				{
				setState(182);
				match(T__1);
				setState(191);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==LOWER_ID) {
					{
					setState(183);
					((QueryContext)_localctx).varDec = varDec();
					((QueryContext)_localctx).decls.add(((QueryContext)_localctx).varDec);
					setState(188);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__8) {
						{
						{
						setState(184);
						match(T__8);
						setState(185);
						((QueryContext)_localctx).varDec = varDec();
						((QueryContext)_localctx).decls.add(((QueryContext)_localctx).varDec);
						}
						}
						setState(190);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(193);
				match(T__2);
				}
			}

			setState(198);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__22) {
				{
				setState(196);
				match(T__22);
				setState(197);
				((QueryContext)_localctx).deposit = match(INT);
				}
			}

			setState(202);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__23) {
				{
				setState(200);
				match(T__23);
				setState(201);
				((QueryContext)_localctx).cond = exp(0);
				}
			}

			setState(206);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__24) {
				{
				setState(204);
				match(T__24);
				setState(205);
				((QueryContext)_localctx).handler = queryHandler();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class RandomQueryContext extends ParserRuleContext {
		public RoleIdContext role;
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public RandomQueryContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_randomQuery; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitRandomQuery(this);
			else return visitor.visitChildren(this);
		}
	}

	public final RandomQueryContext randomQuery() throws RecognitionException {
		RandomQueryContext _localctx = new RandomQueryContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_randomQuery);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(208);
			((RandomQueryContext)_localctx).role = roleId();
			setState(211);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__1) {
				{
				setState(209);
				match(T__1);
				setState(210);
				match(T__2);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class QueryHandlerContext extends ParserRuleContext {
		public QueryHandlerContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_queryHandler; }
	 
		public QueryHandlerContext() { }
		public void copyFrom(QueryHandlerContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ParenQueryHandlerContext extends QueryHandlerContext {
		public QueryHandlerContext queryHandler() {
			return getRuleContext(QueryHandlerContext.class,0);
		}
		public ParenQueryHandlerContext(QueryHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitParenQueryHandler(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class OutcomeQueryHandlerContext extends QueryHandlerContext {
		public ItemContext item;
		public List<ItemContext> items = new ArrayList<ItemContext>();
		public List<ItemContext> item() {
			return getRuleContexts(ItemContext.class);
		}
		public ItemContext item(int i) {
			return getRuleContext(ItemContext.class,i);
		}
		public OutcomeQueryHandlerContext(QueryHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitOutcomeQueryHandler(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BurnQueryHandlerContext extends QueryHandlerContext {
		public BurnQueryHandlerContext(QueryHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBurnQueryHandler(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class SplitQueryHandlerContext extends QueryHandlerContext {
		public SplitQueryHandlerContext(QueryHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitSplitQueryHandler(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class NullQueryHandlerContext extends QueryHandlerContext {
		public NullQueryHandlerContext(QueryHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitNullQueryHandler(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IfQueryHandlerContext extends QueryHandlerContext {
		public ExpContext cond;
		public QueryHandlerContext ifTrue;
		public QueryHandlerContext ifFalse;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public List<QueryHandlerContext> queryHandler() {
			return getRuleContexts(QueryHandlerContext.class);
		}
		public QueryHandlerContext queryHandler(int i) {
			return getRuleContext(QueryHandlerContext.class,i);
		}
		public IfQueryHandlerContext(QueryHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIfQueryHandler(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class LetQueryHandlerContext extends QueryHandlerContext {
		public VarDecContext dec;
		public ExpContext init;
		public QueryHandlerContext body;
		public VarDecContext varDec() {
			return getRuleContext(VarDecContext.class,0);
		}
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public QueryHandlerContext queryHandler() {
			return getRuleContext(QueryHandlerContext.class,0);
		}
		public LetQueryHandlerContext(QueryHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitLetQueryHandler(this);
			else return visitor.visitChildren(this);
		}
	}

	public final QueryHandlerContext queryHandler() throws RecognitionException {
		QueryHandlerContext _localctx = new QueryHandlerContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_queryHandler);
		int _la;
		try {
			setState(241);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,25,_ctx) ) {
			case 1:
				_localctx = new IfQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(213);
				((IfQueryHandlerContext)_localctx).cond = exp(0);
				setState(214);
				match(T__25);
				setState(215);
				((IfQueryHandlerContext)_localctx).ifTrue = queryHandler();
				setState(216);
				match(T__9);
				setState(217);
				((IfQueryHandlerContext)_localctx).ifFalse = queryHandler();
				}
				break;
			case 2:
				_localctx = new LetQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(219);
				match(T__26);
				setState(220);
				((LetQueryHandlerContext)_localctx).dec = varDec();
				setState(221);
				match(T__6);
				setState(222);
				((LetQueryHandlerContext)_localctx).init = exp(0);
				setState(223);
				match(T__27);
				setState(224);
				((LetQueryHandlerContext)_localctx).body = queryHandler();
				}
				break;
			case 3:
				_localctx = new ParenQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(226);
				match(T__1);
				setState(227);
				queryHandler();
				setState(228);
				match(T__2);
				}
				break;
			case 4:
				_localctx = new OutcomeQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(230);
				match(T__3);
				setState(232); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(231);
					((OutcomeQueryHandlerContext)_localctx).item = item();
					((OutcomeQueryHandlerContext)_localctx).items.add(((OutcomeQueryHandlerContext)_localctx).item);
					}
					}
					setState(234); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__29 || _la==ROLE_ID );
				setState(236);
				match(T__4);
				}
				break;
			case 5:
				_localctx = new SplitQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(238);
				match(T__28);
				}
				break;
			case 6:
				_localctx = new BurnQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(239);
				match(T__29);
				}
				break;
			case 7:
				_localctx = new NullQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 7);
				{
				setState(240);
				match(T__30);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class GroupHandlerContext extends ParserRuleContext {
		public GroupHandlerContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_groupHandler; }
	 
		public GroupHandlerContext() { }
		public void copyFrom(GroupHandlerContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class SplitHandlerContext extends GroupHandlerContext {
		public SplitHandlerContext(GroupHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitSplitHandler(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class NullHandlerContext extends GroupHandlerContext {
		public NullHandlerContext(GroupHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitNullHandler(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BurnHandlerContext extends GroupHandlerContext {
		public BurnHandlerContext(GroupHandlerContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBurnHandler(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GroupHandlerContext groupHandler() throws RecognitionException {
		GroupHandlerContext _localctx = new GroupHandlerContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_groupHandler);
		try {
			setState(246);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__28:
				_localctx = new SplitHandlerContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(243);
				match(T__28);
				}
				break;
			case T__29:
				_localctx = new BurnHandlerContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(244);
				match(T__29);
				}
				break;
			case T__30:
				_localctx = new NullHandlerContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(245);
				match(T__30);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class OutcomeContext extends ParserRuleContext {
		public OutcomeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_outcome; }
	 
		public OutcomeContext() { }
		public void copyFrom(OutcomeContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class OutcomeExpContext extends OutcomeContext {
		public ItemContext item;
		public List<ItemContext> items = new ArrayList<ItemContext>();
		public List<ItemContext> item() {
			return getRuleContexts(ItemContext.class);
		}
		public ItemContext item(int i) {
			return getRuleContext(ItemContext.class,i);
		}
		public OutcomeExpContext(OutcomeContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitOutcomeExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IfOutcomeContext extends OutcomeContext {
		public ExpContext cond;
		public OutcomeContext ifTrue;
		public OutcomeContext ifFalse;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public List<OutcomeContext> outcome() {
			return getRuleContexts(OutcomeContext.class);
		}
		public OutcomeContext outcome(int i) {
			return getRuleContext(OutcomeContext.class,i);
		}
		public IfOutcomeContext(OutcomeContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIfOutcome(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class LetOutcomeContext extends OutcomeContext {
		public VarDecContext dec;
		public ExpContext init;
		public OutcomeContext body;
		public VarDecContext varDec() {
			return getRuleContext(VarDecContext.class,0);
		}
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public OutcomeContext outcome() {
			return getRuleContext(OutcomeContext.class,0);
		}
		public LetOutcomeContext(OutcomeContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitLetOutcome(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ParenOutcomeContext extends OutcomeContext {
		public OutcomeContext outcome() {
			return getRuleContext(OutcomeContext.class,0);
		}
		public ParenOutcomeContext(OutcomeContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitParenOutcome(this);
			else return visitor.visitChildren(this);
		}
	}

	public final OutcomeContext outcome() throws RecognitionException {
		OutcomeContext _localctx = new OutcomeContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_outcome);
		int _la;
		try {
			setState(273);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,28,_ctx) ) {
			case 1:
				_localctx = new IfOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(248);
				((IfOutcomeContext)_localctx).cond = exp(0);
				setState(249);
				match(T__25);
				setState(250);
				((IfOutcomeContext)_localctx).ifTrue = outcome();
				setState(251);
				match(T__9);
				setState(252);
				((IfOutcomeContext)_localctx).ifFalse = outcome();
				}
				break;
			case 2:
				_localctx = new LetOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(254);
				match(T__26);
				setState(255);
				((LetOutcomeContext)_localctx).dec = varDec();
				setState(256);
				match(T__6);
				setState(257);
				((LetOutcomeContext)_localctx).init = exp(0);
				setState(258);
				match(T__27);
				setState(259);
				((LetOutcomeContext)_localctx).body = outcome();
				}
				break;
			case 3:
				_localctx = new ParenOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(261);
				match(T__1);
				setState(262);
				outcome();
				setState(263);
				match(T__2);
				}
				break;
			case 4:
				_localctx = new OutcomeExpContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(265);
				match(T__3);
				setState(267); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(266);
					((OutcomeExpContext)_localctx).item = item();
					((OutcomeExpContext)_localctx).items.add(((OutcomeExpContext)_localctx).item);
					}
					}
					setState(269); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==T__29 || _la==ROLE_ID );
				setState(271);
				match(T__4);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ExitItemContext extends ParserRuleContext {
		public RoleIdContext role;
		public Token neg;
		public Token amount;
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public TerminalNode INT() { return getToken(VegasParser.INT, 0); }
		public ExitItemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_exitItem; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitExitItem(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExitItemContext exitItem() throws RecognitionException {
		ExitItemContext _localctx = new ExitItemContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_exitItem);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(275);
			((ExitItemContext)_localctx).role = roleId();
			setState(276);
			match(T__31);
			setState(278);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__32) {
				{
				setState(277);
				((ExitItemContext)_localctx).neg = match(T__32);
				}
			}

			setState(280);
			((ExitItemContext)_localctx).amount = match(INT);
			setState(282);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__10) {
				{
				setState(281);
				match(T__10);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class UtilityItemContext extends ParserRuleContext {
		public RoleIdContext role;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public UtilityItemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_utilityItem; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitUtilityItem(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UtilityItemContext utilityItem() throws RecognitionException {
		UtilityItemContext _localctx = new UtilityItemContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_utilityItem);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(284);
			((UtilityItemContext)_localctx).role = roleId();
			setState(285);
			match(T__31);
			setState(286);
			exp(0);
			setState(288);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__10) {
				{
				setState(287);
				match(T__10);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ItemContext extends ParserRuleContext {
		public ItemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_item; }
	 
		public ItemContext() { }
		public void copyFrom(ItemContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BurnItemContext extends ItemContext {
		public ExpContext amount;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public BurnItemContext(ItemContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBurnItem(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class RoleItemContext extends ItemContext {
		public RoleIdContext role;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public RoleItemContext(ItemContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitRoleItem(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ItemContext item() throws RecognitionException {
		ItemContext _localctx = new ItemContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_item);
		int _la;
		try {
			setState(301);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ROLE_ID:
				_localctx = new RoleItemContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(290);
				((RoleItemContext)_localctx).role = roleId();
				setState(291);
				match(T__31);
				setState(292);
				exp(0);
				setState(294);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__10) {
					{
					setState(293);
					match(T__10);
					}
				}

				}
				break;
			case T__29:
				_localctx = new BurnItemContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(296);
				match(T__29);
				setState(297);
				((BurnItemContext)_localctx).amount = exp(0);
				setState(299);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__10) {
					{
					setState(298);
					match(T__10);
					}
				}

				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ExpContext extends ParserRuleContext {
		public ExpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_exp; }
	 
		public ExpContext() { }
		public void copyFrom(ExpContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpEqExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpEqExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpEqExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class UndefExpContext extends ExpContext {
		public Token op;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public UndefExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitUndefExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpAddExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpAddExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpAddExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpCompExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpCompExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpCompExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class UnOpExpContext extends ExpContext {
		public Token op;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public UnOpExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitUnOpExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class MemberExpContext extends ExpContext {
		public RoleIdContext role;
		public VarIdContext field;
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public MemberExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitMemberExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IdExpContext extends ExpContext {
		public VarIdContext name;
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public IdExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIdExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class CallExpContext extends ExpContext {
		public VarIdContext callee;
		public ExpContext exp;
		public List<ExpContext> args = new ArrayList<ExpContext>();
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public CallExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitCallExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IfExpContext extends ExpContext {
		public ExpContext cond;
		public ExpContext ifTrue;
		public ExpContext ifFalse;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public IfExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitIfExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpBoolExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpBoolExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpBoolExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ParenExpContext extends ExpContext {
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public ParenExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitParenExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BoolLiteralExpContext extends ExpContext {
		public BoolLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBoolLiteralExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class LetExpContext extends ExpContext {
		public VarDecContext dec;
		public ExpContext init;
		public ExpContext body;
		public VarDecContext varDec() {
			return getRuleContext(VarDecContext.class,0);
		}
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public LetExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitLetExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class AddressLiteralExpContext extends ExpContext {
		public TerminalNode ADDRESS() { return getToken(VegasParser.ADDRESS, 0); }
		public AddressLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitAddressLiteralExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BinOpMultExpContext extends ExpContext {
		public ExpContext left;
		public Token op;
		public ExpContext right;
		public List<ExpContext> exp() {
			return getRuleContexts(ExpContext.class);
		}
		public ExpContext exp(int i) {
			return getRuleContext(ExpContext.class,i);
		}
		public BinOpMultExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBinOpMultExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class NumLiteralExpContext extends ExpContext {
		public TerminalNode INT() { return getToken(VegasParser.INT, 0); }
		public NumLiteralExpContext(ExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitNumLiteralExp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExpContext exp() throws RecognitionException {
		return exp(0);
	}

	private ExpContext exp(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ExpContext _localctx = new ExpContext(_ctx, _parentState);
		ExpContext _prevctx = _localctx;
		int _startState = 32;
		enterRecursionRule(_localctx, 32, RULE_exp, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(339);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,37,_ctx) ) {
			case 1:
				{
				_localctx = new ParenExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(304);
				match(T__1);
				setState(305);
				exp(0);
				setState(306);
				match(T__2);
				}
				break;
			case 2:
				{
				_localctx = new MemberExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(308);
				((MemberExpContext)_localctx).role = roleId();
				setState(309);
				match(T__33);
				setState(310);
				((MemberExpContext)_localctx).field = varId();
				}
				break;
			case 3:
				{
				_localctx = new CallExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(312);
				((CallExpContext)_localctx).callee = varId();
				setState(313);
				match(T__1);
				setState(322);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 544372647908081668L) != 0)) {
					{
					setState(314);
					((CallExpContext)_localctx).exp = exp(0);
					((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
					setState(319);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__8) {
						{
						{
						setState(315);
						match(T__8);
						setState(316);
						((CallExpContext)_localctx).exp = exp(0);
						((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
						}
						}
						setState(321);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(324);
				match(T__2);
				}
				break;
			case 4:
				{
				_localctx = new UnOpExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(326);
				((UnOpExpContext)_localctx).op = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__32 || _la==T__34) ) {
					((UnOpExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(327);
				exp(13);
				}
				break;
			case 5:
				{
				_localctx = new BoolLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(328);
				_la = _input.LA(1);
				if ( !(_la==T__48 || _la==T__49) ) {
				_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				}
				break;
			case 6:
				{
				_localctx = new IdExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(329);
				((IdExpContext)_localctx).name = varId();
				}
				break;
			case 7:
				{
				_localctx = new NumLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(330);
				match(INT);
				}
				break;
			case 8:
				{
				_localctx = new AddressLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(331);
				match(ADDRESS);
				}
				break;
			case 9:
				{
				_localctx = new LetExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(332);
				match(T__50);
				setState(333);
				((LetExpContext)_localctx).dec = varDec();
				setState(334);
				match(T__6);
				setState(335);
				((LetExpContext)_localctx).init = exp(0);
				setState(336);
				match(T__27);
				setState(337);
				((LetExpContext)_localctx).body = exp(1);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(367);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,39,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(365);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,38,_ctx) ) {
					case 1:
						{
						_localctx = new BinOpMultExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpMultExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(341);
						if (!(precpred(_ctx, 12))) throw new FailedPredicateException(this, "precpred(_ctx, 12)");
						setState(342);
						((BinOpMultExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 481036337152L) != 0)) ) {
							((BinOpMultExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(343);
						((BinOpMultExpContext)_localctx).right = exp(13);
						}
						break;
					case 2:
						{
						_localctx = new BinOpAddExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpAddExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(344);
						if (!(precpred(_ctx, 11))) throw new FailedPredicateException(this, "precpred(_ctx, 11)");
						setState(345);
						((BinOpAddExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__32 || _la==T__38) ) {
							((BinOpAddExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(346);
						((BinOpAddExpContext)_localctx).right = exp(12);
						}
						break;
					case 3:
						{
						_localctx = new BinOpCompExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpCompExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(347);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(348);
						((BinOpCompExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 65970697666560L) != 0)) ) {
							((BinOpCompExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(349);
						((BinOpCompExpContext)_localctx).right = exp(10);
						}
						break;
					case 4:
						{
						_localctx = new BinOpEqExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpEqExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(350);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(351);
						((BinOpEqExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 214404767416320L) != 0)) ) {
							((BinOpEqExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(352);
						((BinOpEqExpContext)_localctx).right = exp(9);
						}
						break;
					case 5:
						{
						_localctx = new BinOpBoolExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpBoolExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(353);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(354);
						((BinOpBoolExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__24 || _la==T__47) ) {
							((BinOpBoolExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(355);
						((BinOpBoolExpContext)_localctx).right = exp(8);
						}
						break;
					case 6:
						{
						_localctx = new IfExpContext(new ExpContext(_parentctx, _parentState));
						((IfExpContext)_localctx).cond = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(356);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(357);
						match(T__25);
						setState(358);
						((IfExpContext)_localctx).ifTrue = exp(0);
						setState(359);
						match(T__9);
						setState(360);
						((IfExpContext)_localctx).ifFalse = exp(6);
						}
						break;
					case 7:
						{
						_localctx = new UndefExpContext(new ExpContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(362);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(363);
						((UndefExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__39 || _la==T__40) ) {
							((UndefExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(364);
						match(T__30);
						}
						break;
					}
					} 
				}
				setState(369);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,39,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class VarDecContext extends ParserRuleContext {
		public VarIdContext name;
		public TypeExpContext type;
		public DistExpContext dist;
		public VarIdContext varId() {
			return getRuleContext(VarIdContext.class,0);
		}
		public TypeExpContext typeExp() {
			return getRuleContext(TypeExpContext.class,0);
		}
		public DistExpContext distExp() {
			return getRuleContext(DistExpContext.class,0);
		}
		public VarDecContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varDec; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitVarDec(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarDecContext varDec() throws RecognitionException {
		VarDecContext _localctx = new VarDecContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_varDec);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(370);
			((VarDecContext)_localctx).name = varId();
			setState(371);
			match(T__9);
			setState(372);
			((VarDecContext)_localctx).type = typeExp();
			setState(375);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__51) {
				{
				setState(373);
				match(T__51);
				setState(374);
				((VarDecContext)_localctx).dist = distExp();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class DistExpContext extends ParserRuleContext {
		public DistExpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_distExp; }
	 
		public DistExpContext() { }
		public void copyFrom(DistExpContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class WeightedDistExpContext extends DistExpContext {
		public WeightedItemContext weightedItem;
		public List<WeightedItemContext> items = new ArrayList<WeightedItemContext>();
		public List<WeightedItemContext> weightedItem() {
			return getRuleContexts(WeightedItemContext.class);
		}
		public WeightedItemContext weightedItem(int i) {
			return getRuleContext(WeightedItemContext.class,i);
		}
		public WeightedDistExpContext(DistExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitWeightedDistExp(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class UniformDistExpContext extends DistExpContext {
		public DistValContext distVal;
		public List<DistValContext> vals = new ArrayList<DistValContext>();
		public List<DistValContext> distVal() {
			return getRuleContexts(DistValContext.class);
		}
		public DistValContext distVal(int i) {
			return getRuleContext(DistValContext.class,i);
		}
		public UniformDistExpContext(DistExpContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitUniformDistExp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DistExpContext distExp() throws RecognitionException {
		DistExpContext _localctx = new DistExpContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_distExp);
		int _la;
		try {
			setState(401);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__52:
				_localctx = new UniformDistExpContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(377);
				match(T__52);
				setState(378);
				match(T__3);
				setState(379);
				((UniformDistExpContext)_localctx).distVal = distVal();
				((UniformDistExpContext)_localctx).vals.add(((UniformDistExpContext)_localctx).distVal);
				setState(384);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(380);
					match(T__8);
					setState(381);
					((UniformDistExpContext)_localctx).distVal = distVal();
					((UniformDistExpContext)_localctx).vals.add(((UniformDistExpContext)_localctx).distVal);
					}
					}
					setState(386);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(387);
				match(T__4);
				}
				break;
			case T__53:
				_localctx = new WeightedDistExpContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(389);
				match(T__53);
				setState(390);
				match(T__3);
				setState(391);
				((WeightedDistExpContext)_localctx).weightedItem = weightedItem();
				((WeightedDistExpContext)_localctx).items.add(((WeightedDistExpContext)_localctx).weightedItem);
				setState(396);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(392);
					match(T__8);
					setState(393);
					((WeightedDistExpContext)_localctx).weightedItem = weightedItem();
					((WeightedDistExpContext)_localctx).items.add(((WeightedDistExpContext)_localctx).weightedItem);
					}
					}
					setState(398);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(399);
				match(T__4);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class DistValContext extends ParserRuleContext {
		public DistValContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_distVal; }
	 
		public DistValContext() { }
		public void copyFrom(DistValContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class NumDistValContext extends DistValContext {
		public TerminalNode INT() { return getToken(VegasParser.INT, 0); }
		public NumDistValContext(DistValContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitNumDistVal(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class BoolDistValContext extends DistValContext {
		public BoolDistValContext(DistValContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitBoolDistVal(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DistValContext distVal() throws RecognitionException {
		DistValContext _localctx = new DistValContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_distVal);
		int _la;
		try {
			setState(405);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case INT:
				_localctx = new NumDistValContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(403);
				match(INT);
				}
				break;
			case T__48:
			case T__49:
				_localctx = new BoolDistValContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(404);
				_la = _input.LA(1);
				if ( !(_la==T__48 || _la==T__49) ) {
				_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class WeightedItemContext extends ParserRuleContext {
		public DistValContext value;
		public Token weight;
		public DistValContext distVal() {
			return getRuleContext(DistValContext.class,0);
		}
		public TerminalNode INT() { return getToken(VegasParser.INT, 0); }
		public WeightedItemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_weightedItem; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitWeightedItem(this);
			else return visitor.visitChildren(this);
		}
	}

	public final WeightedItemContext weightedItem() throws RecognitionException {
		WeightedItemContext _localctx = new WeightedItemContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_weightedItem);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(407);
			((WeightedItemContext)_localctx).value = distVal();
			setState(408);
			match(T__9);
			setState(409);
			((WeightedItemContext)_localctx).weight = match(INT);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class TypeIdContext extends ParserRuleContext {
		public TerminalNode LOWER_ID() { return getToken(VegasParser.LOWER_ID, 0); }
		public TypeIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeId; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitTypeId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeIdContext typeId() throws RecognitionException {
		TypeIdContext _localctx = new TypeIdContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_typeId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(411);
			match(LOWER_ID);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class VarIdContext extends ParserRuleContext {
		public TerminalNode LOWER_ID() { return getToken(VegasParser.LOWER_ID, 0); }
		public VarIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_varId; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitVarId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VarIdContext varId() throws RecognitionException {
		VarIdContext _localctx = new VarIdContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_varId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(413);
			match(LOWER_ID);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class RoleIdContext extends ParserRuleContext {
		public TerminalNode ROLE_ID() { return getToken(VegasParser.ROLE_ID, 0); }
		public RoleIdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_roleId; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitRoleId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final RoleIdContext roleId() throws RecognitionException {
		RoleIdContext _localctx = new RoleIdContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_roleId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(415);
			match(ROLE_ID);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 16:
			return exp_sempred((ExpContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean exp_sempred(ExpContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 12);
		case 1:
			return precpred(_ctx, 11);
		case 2:
			return precpred(_ctx, 9);
		case 3:
			return precpred(_ctx, 8);
		case 4:
			return precpred(_ctx, 7);
		case 5:
			return precpred(_ctx, 6);
		case 6:
			return precpred(_ctx, 10);
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u0001>\u01a2\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"+
		"\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"+
		"\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"+
		"\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b\u0002"+
		"\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002\u000f\u0007\u000f"+
		"\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002\u0012\u0007\u0012"+
		"\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014\u0002\u0015\u0007\u0015"+
		"\u0002\u0016\u0007\u0016\u0002\u0017\u0007\u0017\u0001\u0000\u0001\u0000"+
		"\u0005\u00003\b\u0000\n\u0000\f\u00006\t\u0000\u0001\u0000\u0001\u0000"+
		"\u0001\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0002\u0001\u0002\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0005\u0004P\b\u0004"+
		"\n\u0004\f\u0004S\t\u0004\u0003\u0004U\b\u0004\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0003\u0004]\b\u0004"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0005\u0006g\b\u0006\n\u0006\f\u0006j\t\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0003\u0006s\b\u0006\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0003\u0007x\b\u0007\u0001\u0007\u0004\u0007{\b\u0007\u000b\u0007\f\u0007"+
		"|\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0004\u0007"+
		"\u0084\b\u0007\u000b\u0007\f\u0007\u0085\u0001\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0003\u0007\u008d\b\u0007\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0005\u0007\u0093\b\u0007\n\u0007\f\u0007"+
		"\u0096\t\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0004\u0007\u00a1\b\u0007"+
		"\u000b\u0007\f\u0007\u00a2\u0001\u0007\u0001\u0007\u0003\u0007\u00a7\b"+
		"\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0004\u0007\u00ac\b\u0007\u000b"+
		"\u0007\f\u0007\u00ad\u0001\u0007\u0001\u0007\u0003\u0007\u00b2\b\u0007"+
		"\u0003\u0007\u00b4\b\u0007\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0005"+
		"\b\u00bb\b\b\n\b\f\b\u00be\t\b\u0003\b\u00c0\b\b\u0001\b\u0003\b\u00c3"+
		"\b\b\u0001\b\u0001\b\u0003\b\u00c7\b\b\u0001\b\u0001\b\u0003\b\u00cb\b"+
		"\b\u0001\b\u0001\b\u0003\b\u00cf\b\b\u0001\t\u0001\t\u0001\t\u0003\t\u00d4"+
		"\b\t\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001"+
		"\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001\n\u0001"+
		"\n\u0001\n\u0004\n\u00e9\b\n\u000b\n\f\n\u00ea\u0001\n\u0001\n\u0001\n"+
		"\u0001\n\u0001\n\u0003\n\u00f2\b\n\u0001\u000b\u0001\u000b\u0001\u000b"+
		"\u0003\u000b\u00f7\b\u000b\u0001\f\u0001\f\u0001\f\u0001\f\u0001\f\u0001"+
		"\f\u0001\f\u0001\f\u0001\f\u0001\f\u0001\f\u0001\f\u0001\f\u0001\f\u0001"+
		"\f\u0001\f\u0001\f\u0001\f\u0001\f\u0004\f\u010c\b\f\u000b\f\f\f\u010d"+
		"\u0001\f\u0001\f\u0003\f\u0112\b\f\u0001\r\u0001\r\u0001\r\u0003\r\u0117"+
		"\b\r\u0001\r\u0001\r\u0003\r\u011b\b\r\u0001\u000e\u0001\u000e\u0001\u000e"+
		"\u0001\u000e\u0003\u000e\u0121\b\u000e\u0001\u000f\u0001\u000f\u0001\u000f"+
		"\u0001\u000f\u0003\u000f\u0127\b\u000f\u0001\u000f\u0001\u000f\u0001\u000f"+
		"\u0003\u000f\u012c\b\u000f\u0003\u000f\u012e\b\u000f\u0001\u0010\u0001"+
		"\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001"+
		"\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001"+
		"\u0010\u0005\u0010\u013e\b\u0010\n\u0010\f\u0010\u0141\t\u0010\u0003\u0010"+
		"\u0143\b\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010"+
		"\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010"+
		"\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0003\u0010\u0154\b\u0010"+
		"\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010"+
		"\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010"+
		"\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010"+
		"\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010"+
		"\u0005\u0010\u016e\b\u0010\n\u0010\f\u0010\u0171\t\u0010\u0001\u0011\u0001"+
		"\u0011\u0001\u0011\u0001\u0011\u0001\u0011\u0003\u0011\u0178\b\u0011\u0001"+
		"\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0005\u0012\u017f"+
		"\b\u0012\n\u0012\f\u0012\u0182\t\u0012\u0001\u0012\u0001\u0012\u0001\u0012"+
		"\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0005\u0012\u018b\b\u0012"+
		"\n\u0012\f\u0012\u018e\t\u0012\u0001\u0012\u0001\u0012\u0003\u0012\u0192"+
		"\b\u0012\u0001\u0013\u0001\u0013\u0003\u0013\u0196\b\u0013\u0001\u0014"+
		"\u0001\u0014\u0001\u0014\u0001\u0014\u0001\u0015\u0001\u0015\u0001\u0016"+
		"\u0001\u0016\u0001\u0017\u0001\u0017\u0001\u0017\u0000\u0001 \u0018\u0000"+
		"\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014\u0016\u0018\u001a\u001c"+
		"\u001e \"$&(*,.\u0000\t\u0001\u0000\r\u0010\u0002\u0000!!##\u0001\u0000"+
		"12\u0001\u0000$&\u0002\u0000!!\'\'\u0001\u0000*-\u0002\u0000()./\u0002"+
		"\u0000\u0019\u001900\u0001\u0000()\u01cd\u00004\u0001\u0000\u0000\u0000"+
		"\u0002:\u0001\u0000\u0000\u0000\u0004B\u0001\u0000\u0000\u0000\u0006D"+
		"\u0001\u0000\u0000\u0000\bI\u0001\u0000\u0000\u0000\n^\u0001\u0000\u0000"+
		"\u0000\fr\u0001\u0000\u0000\u0000\u000e\u00b3\u0001\u0000\u0000\u0000"+
		"\u0010\u00b5\u0001\u0000\u0000\u0000\u0012\u00d0\u0001\u0000\u0000\u0000"+
		"\u0014\u00f1\u0001\u0000\u0000\u0000\u0016\u00f6\u0001\u0000\u0000\u0000"+
		"\u0018\u0111\u0001\u0000\u0000\u0000\u001a\u0113\u0001\u0000\u0000\u0000"+
		"\u001c\u011c\u0001\u0000\u0000\u0000\u001e\u012d\u0001\u0000\u0000\u0000"+
		" \u0153\u0001\u0000\u0000\u0000\"\u0172\u0001\u0000\u0000\u0000$\u0191"+
		"\u0001\u0000\u0000\u0000&\u0195\u0001\u0000\u0000\u0000(\u0197\u0001\u0000"+
		"\u0000\u0000*\u019b\u0001\u0000\u0000\u0000,\u019d\u0001\u0000\u0000\u0000"+
		".\u019f\u0001\u0000\u0000\u000003\u0003\u0006\u0003\u000013\u0003\b\u0004"+
		"\u000020\u0001\u0000\u0000\u000021\u0001\u0000\u0000\u000036\u0001\u0000"+
		"\u0000\u000042\u0001\u0000\u0000\u000045\u0001\u0000\u0000\u000057\u0001"+
		"\u0000\u0000\u000064\u0001\u0000\u0000\u000078\u0003\u0002\u0001\u0000"+
		"89\u0005\u0000\u0000\u00019\u0001\u0001\u0000\u0000\u0000:;\u0005\u0001"+
		"\u0000\u0000;<\u0003\u0004\u0002\u0000<=\u0005\u0002\u0000\u0000=>\u0005"+
		"\u0003\u0000\u0000>?\u0005\u0004\u0000\u0000?@\u0003\u000e\u0007\u0000"+
		"@A\u0005\u0005\u0000\u0000A\u0003\u0001\u0000\u0000\u0000BC\u0003,\u0016"+
		"\u0000C\u0005\u0001\u0000\u0000\u0000DE\u0005\u0006\u0000\u0000EF\u0003"+
		"*\u0015\u0000FG\u0005\u0007\u0000\u0000GH\u0003\f\u0006\u0000H\u0007\u0001"+
		"\u0000\u0000\u0000IJ\u0005\b\u0000\u0000JK\u0003,\u0016\u0000KT\u0005"+
		"\u0002\u0000\u0000LQ\u0003\n\u0005\u0000MN\u0005\t\u0000\u0000NP\u0003"+
		"\n\u0005\u0000OM\u0001\u0000\u0000\u0000PS\u0001\u0000\u0000\u0000QO\u0001"+
		"\u0000\u0000\u0000QR\u0001\u0000\u0000\u0000RU\u0001\u0000\u0000\u0000"+
		"SQ\u0001\u0000\u0000\u0000TL\u0001\u0000\u0000\u0000TU\u0001\u0000\u0000"+
		"\u0000UV\u0001\u0000\u0000\u0000VW\u0005\u0003\u0000\u0000WX\u0005\n\u0000"+
		"\u0000XY\u0003\f\u0006\u0000YZ\u0005\u0007\u0000\u0000Z\\\u0003 \u0010"+
		"\u0000[]\u0005\u000b\u0000\u0000\\[\u0001\u0000\u0000\u0000\\]\u0001\u0000"+
		"\u0000\u0000]\t\u0001\u0000\u0000\u0000^_\u0003,\u0016\u0000_`\u0005\n"+
		"\u0000\u0000`a\u0003\f\u0006\u0000a\u000b\u0001\u0000\u0000\u0000bc\u0005"+
		"\u0004\u0000\u0000ch\u00059\u0000\u0000de\u0005\t\u0000\u0000eg\u0005"+
		"9\u0000\u0000fd\u0001\u0000\u0000\u0000gj\u0001\u0000\u0000\u0000hf\u0001"+
		"\u0000\u0000\u0000hi\u0001\u0000\u0000\u0000ik\u0001\u0000\u0000\u0000"+
		"jh\u0001\u0000\u0000\u0000ks\u0005\u0005\u0000\u0000lm\u0005\u0004\u0000"+
		"\u0000mn\u00059\u0000\u0000no\u0005\f\u0000\u0000op\u00059\u0000\u0000"+
		"ps\u0005\u0005\u0000\u0000qs\u0003*\u0015\u0000rb\u0001\u0000\u0000\u0000"+
		"rl\u0001\u0000\u0000\u0000rq\u0001\u0000\u0000\u0000s\r\u0001\u0000\u0000"+
		"\u0000tw\u0007\u0000\u0000\u0000uv\u0005\u0011\u0000\u0000vx\u0003\u0016"+
		"\u000b\u0000wu\u0001\u0000\u0000\u0000wx\u0001\u0000\u0000\u0000xz\u0001"+
		"\u0000\u0000\u0000y{\u0003\u0010\b\u0000zy\u0001\u0000\u0000\u0000{|\u0001"+
		"\u0000\u0000\u0000|z\u0001\u0000\u0000\u0000|}\u0001\u0000\u0000\u0000"+
		"}~\u0001\u0000\u0000\u0000~\u007f\u0005\u000b\u0000\u0000\u007f\u0080"+
		"\u0003\u000e\u0007\u0000\u0080\u00b4\u0001\u0000\u0000\u0000\u0081\u0083"+
		"\u0005\u0012\u0000\u0000\u0082\u0084\u0003\u0012\t\u0000\u0083\u0082\u0001"+
		"\u0000\u0000\u0000\u0084\u0085\u0001\u0000\u0000\u0000\u0085\u0083\u0001"+
		"\u0000\u0000\u0000\u0085\u0086\u0001\u0000\u0000\u0000\u0086\u0087\u0001"+
		"\u0000\u0000\u0000\u0087\u0088\u0005\u000b\u0000\u0000\u0088\u0089\u0003"+
		"\u000e\u0007\u0000\u0089\u00b4\u0001\u0000\u0000\u0000\u008a\u008c\u0005"+
		"\u0013\u0000\u0000\u008b\u008d\u0003.\u0017\u0000\u008c\u008b\u0001\u0000"+
		"\u0000\u0000\u008c\u008d\u0001\u0000\u0000\u0000\u008d\u008e\u0001\u0000"+
		"\u0000\u0000\u008e\u008f\u0005\u0002\u0000\u0000\u008f\u0094\u0003\"\u0011"+
		"\u0000\u0090\u0091\u0005\t\u0000\u0000\u0091\u0093\u0003\"\u0011\u0000"+
		"\u0092\u0090\u0001\u0000\u0000\u0000\u0093\u0096\u0001\u0000\u0000\u0000"+
		"\u0094\u0092\u0001\u0000\u0000\u0000\u0094\u0095\u0001\u0000\u0000\u0000"+
		"\u0095\u0097\u0001\u0000\u0000\u0000\u0096\u0094\u0001\u0000\u0000\u0000"+
		"\u0097\u0098\u0005\u0003\u0000\u0000\u0098\u0099\u0005\u000b\u0000\u0000"+
		"\u0099\u009a\u0003\u000e\u0007\u0000\u009a\u00b4\u0001\u0000\u0000\u0000"+
		"\u009b\u009c\u0005\u0014\u0000\u0000\u009c\u00a6\u0003\u0018\f\u0000\u009d"+
		"\u009e\u0005\u0015\u0000\u0000\u009e\u00a0\u0005\u0004\u0000\u0000\u009f"+
		"\u00a1\u0003\u001a\r\u0000\u00a0\u009f\u0001\u0000\u0000\u0000\u00a1\u00a2"+
		"\u0001\u0000\u0000\u0000\u00a2\u00a0\u0001\u0000\u0000\u0000\u00a2\u00a3"+
		"\u0001\u0000\u0000\u0000\u00a3\u00a4\u0001\u0000\u0000\u0000\u00a4\u00a5"+
		"\u0005\u0005\u0000\u0000\u00a5\u00a7\u0001\u0000\u0000\u0000\u00a6\u009d"+
		"\u0001\u0000\u0000\u0000\u00a6\u00a7\u0001\u0000\u0000\u0000\u00a7\u00b1"+
		"\u0001\u0000\u0000\u0000\u00a8\u00a9\u0005\u0016\u0000\u0000\u00a9\u00ab"+
		"\u0005\u0004\u0000\u0000\u00aa\u00ac\u0003\u001c\u000e\u0000\u00ab\u00aa"+
		"\u0001\u0000\u0000\u0000\u00ac\u00ad\u0001\u0000\u0000\u0000\u00ad\u00ab"+
		"\u0001\u0000\u0000\u0000\u00ad\u00ae\u0001\u0000\u0000\u0000\u00ae\u00af"+
		"\u0001\u0000\u0000\u0000\u00af\u00b0\u0005\u0005\u0000\u0000\u00b0\u00b2"+
		"\u0001\u0000\u0000\u0000\u00b1\u00a8\u0001\u0000\u0000\u0000\u00b1\u00b2"+
		"\u0001\u0000\u0000\u0000\u00b2\u00b4\u0001\u0000\u0000\u0000\u00b3t\u0001"+
		"\u0000\u0000\u0000\u00b3\u0081\u0001\u0000\u0000\u0000\u00b3\u008a\u0001"+
		"\u0000\u0000\u0000\u00b3\u009b\u0001\u0000\u0000\u0000\u00b4\u000f\u0001"+
		"\u0000\u0000\u0000\u00b5\u00c2\u0003.\u0017\u0000\u00b6\u00bf\u0005\u0002"+
		"\u0000\u0000\u00b7\u00bc\u0003\"\u0011\u0000\u00b8\u00b9\u0005\t\u0000"+
		"\u0000\u00b9\u00bb\u0003\"\u0011\u0000\u00ba\u00b8\u0001\u0000\u0000\u0000"+
		"\u00bb\u00be\u0001\u0000\u0000\u0000\u00bc\u00ba\u0001\u0000\u0000\u0000"+
		"\u00bc\u00bd\u0001\u0000\u0000\u0000\u00bd\u00c0\u0001\u0000\u0000\u0000"+
		"\u00be\u00bc\u0001\u0000\u0000\u0000\u00bf\u00b7\u0001\u0000\u0000\u0000"+
		"\u00bf\u00c0\u0001\u0000\u0000\u0000\u00c0\u00c1\u0001\u0000\u0000\u0000"+
		"\u00c1\u00c3\u0005\u0003\u0000\u0000\u00c2\u00b6\u0001\u0000\u0000\u0000"+
		"\u00c2\u00c3\u0001\u0000\u0000\u0000\u00c3\u00c6\u0001\u0000\u0000\u0000"+
		"\u00c4\u00c5\u0005\u0017\u0000\u0000\u00c5\u00c7\u00059\u0000\u0000\u00c6"+
		"\u00c4\u0001\u0000\u0000\u0000\u00c6\u00c7\u0001\u0000\u0000\u0000\u00c7"+
		"\u00ca\u0001\u0000\u0000\u0000\u00c8\u00c9\u0005\u0018\u0000\u0000\u00c9"+
		"\u00cb\u0003 \u0010\u0000\u00ca\u00c8\u0001\u0000\u0000\u0000\u00ca\u00cb"+
		"\u0001\u0000\u0000\u0000\u00cb\u00ce\u0001\u0000\u0000\u0000\u00cc\u00cd"+
		"\u0005\u0019\u0000\u0000\u00cd\u00cf\u0003\u0014\n\u0000\u00ce\u00cc\u0001"+
		"\u0000\u0000\u0000\u00ce\u00cf\u0001\u0000\u0000\u0000\u00cf\u0011\u0001"+
		"\u0000\u0000\u0000\u00d0\u00d3\u0003.\u0017\u0000\u00d1\u00d2\u0005\u0002"+
		"\u0000\u0000\u00d2\u00d4\u0005\u0003\u0000\u0000\u00d3\u00d1\u0001\u0000"+
		"\u0000\u0000\u00d3\u00d4\u0001\u0000\u0000\u0000\u00d4\u0013\u0001\u0000"+
		"\u0000\u0000\u00d5\u00d6\u0003 \u0010\u0000\u00d6\u00d7\u0005\u001a\u0000"+
		"\u0000\u00d7\u00d8\u0003\u0014\n\u0000\u00d8\u00d9\u0005\n\u0000\u0000"+
		"\u00d9\u00da\u0003\u0014\n\u0000\u00da\u00f2\u0001\u0000\u0000\u0000\u00db"+
		"\u00dc\u0005\u001b\u0000\u0000\u00dc\u00dd\u0003\"\u0011\u0000\u00dd\u00de"+
		"\u0005\u0007\u0000\u0000\u00de\u00df\u0003 \u0010\u0000\u00df\u00e0\u0005"+
		"\u001c\u0000\u0000\u00e0\u00e1\u0003\u0014\n\u0000\u00e1\u00f2\u0001\u0000"+
		"\u0000\u0000\u00e2\u00e3\u0005\u0002\u0000\u0000\u00e3\u00e4\u0003\u0014"+
		"\n\u0000\u00e4\u00e5\u0005\u0003\u0000\u0000\u00e5\u00f2\u0001\u0000\u0000"+
		"\u0000\u00e6\u00e8\u0005\u0004\u0000\u0000\u00e7\u00e9\u0003\u001e\u000f"+
		"\u0000\u00e8\u00e7\u0001\u0000\u0000\u0000\u00e9\u00ea\u0001\u0000\u0000"+
		"\u0000\u00ea\u00e8\u0001\u0000\u0000\u0000\u00ea\u00eb\u0001\u0000\u0000"+
		"\u0000\u00eb\u00ec\u0001\u0000\u0000\u0000\u00ec\u00ed\u0005\u0005\u0000"+
		"\u0000\u00ed\u00f2\u0001\u0000\u0000\u0000\u00ee\u00f2\u0005\u001d\u0000"+
		"\u0000\u00ef\u00f2\u0005\u001e\u0000\u0000\u00f0\u00f2\u0005\u001f\u0000"+
		"\u0000\u00f1\u00d5\u0001\u0000\u0000\u0000\u00f1\u00db\u0001\u0000\u0000"+
		"\u0000\u00f1\u00e2\u0001\u0000\u0000\u0000\u00f1\u00e6\u0001\u0000\u0000"+
		"\u0000\u00f1\u00ee\u0001\u0000\u0000\u0000\u00f1\u00ef\u0001\u0000\u0000"+
		"\u0000\u00f1\u00f0\u0001\u0000\u0000\u0000\u00f2\u0015\u0001\u0000\u0000"+
		"\u0000\u00f3\u00f7\u0005\u001d\u0000\u0000\u00f4\u00f7\u0005\u001e\u0000"+
		"\u0000\u00f5\u00f7\u0005\u001f\u0000\u0000\u00f6\u00f3\u0001\u0000\u0000"+
		"\u0000\u00f6\u00f4\u0001\u0000\u0000\u0000\u00f6\u00f5\u0001\u0000\u0000"+
		"\u0000\u00f7\u0017\u0001\u0000\u0000\u0000\u00f8\u00f9\u0003 \u0010\u0000"+
		"\u00f9\u00fa\u0005\u001a\u0000\u0000\u00fa\u00fb\u0003\u0018\f\u0000\u00fb"+
		"\u00fc\u0005\n\u0000\u0000\u00fc\u00fd\u0003\u0018\f\u0000\u00fd\u0112"+
		"\u0001\u0000\u0000\u0000\u00fe\u00ff\u0005\u001b\u0000\u0000\u00ff\u0100"+
		"\u0003\"\u0011\u0000\u0100\u0101\u0005\u0007\u0000\u0000\u0101\u0102\u0003"+
		" \u0010\u0000\u0102\u0103\u0005\u001c\u0000\u0000\u0103\u0104\u0003\u0018"+
		"\f\u0000\u0104\u0112\u0001\u0000\u0000\u0000\u0105\u0106\u0005\u0002\u0000"+
		"\u0000\u0106\u0107\u0003\u0018\f\u0000\u0107\u0108\u0005\u0003\u0000\u0000"+
		"\u0108\u0112\u0001\u0000\u0000\u0000\u0109\u010b\u0005\u0004\u0000\u0000"+
		"\u010a\u010c\u0003\u001e\u000f\u0000\u010b\u010a\u0001\u0000\u0000\u0000"+
		"\u010c\u010d\u0001\u0000\u0000\u0000\u010d\u010b\u0001\u0000\u0000\u0000"+
		"\u010d\u010e\u0001\u0000\u0000\u0000\u010e\u010f\u0001\u0000\u0000\u0000"+
		"\u010f\u0110\u0005\u0005\u0000\u0000\u0110\u0112\u0001\u0000\u0000\u0000"+
		"\u0111\u00f8\u0001\u0000\u0000\u0000\u0111\u00fe\u0001\u0000\u0000\u0000"+
		"\u0111\u0105\u0001\u0000\u0000\u0000\u0111\u0109\u0001\u0000\u0000\u0000"+
		"\u0112\u0019\u0001\u0000\u0000\u0000\u0113\u0114\u0003.\u0017\u0000\u0114"+
		"\u0116\u0005 \u0000\u0000\u0115\u0117\u0005!\u0000\u0000\u0116\u0115\u0001"+
		"\u0000\u0000\u0000\u0116\u0117\u0001\u0000\u0000\u0000\u0117\u0118\u0001"+
		"\u0000\u0000\u0000\u0118\u011a\u00059\u0000\u0000\u0119\u011b\u0005\u000b"+
		"\u0000\u0000\u011a\u0119\u0001\u0000\u0000\u0000\u011a\u011b\u0001\u0000"+
		"\u0000\u0000\u011b\u001b\u0001\u0000\u0000\u0000\u011c\u011d\u0003.\u0017"+
		"\u0000\u011d\u011e\u0005 \u0000\u0000\u011e\u0120\u0003 \u0010\u0000\u011f"+
		"\u0121\u0005\u000b\u0000\u0000\u0120\u011f\u0001\u0000\u0000\u0000\u0120"+
		"\u0121\u0001\u0000\u0000\u0000\u0121\u001d\u0001\u0000\u0000\u0000\u0122"+
		"\u0123\u0003.\u0017\u0000\u0123\u0124\u0005 \u0000\u0000\u0124\u0126\u0003"+
		" \u0010\u0000\u0125\u0127\u0005\u000b\u0000\u0000\u0126\u0125\u0001\u0000"+
		"\u0000\u0000\u0126\u0127\u0001\u0000\u0000\u0000\u0127\u012e\u0001\u0000"+
		"\u0000\u0000\u0128\u0129\u0005\u001e\u0000\u0000\u0129\u012b\u0003 \u0010"+
		"\u0000\u012a\u012c\u0005\u000b\u0000\u0000\u012b\u012a\u0001\u0000\u0000"+
		"\u0000\u012b\u012c\u0001\u0000\u0000\u0000\u012c\u012e\u0001\u0000\u0000"+
		"\u0000\u012d\u0122\u0001\u0000\u0000\u0000\u012d\u0128\u0001\u0000\u0000"+
		"\u0000\u012e\u001f\u0001\u0000\u0000\u0000\u012f\u0130\u0006\u0010\uffff"+
		"\uffff\u0000\u0130\u0131\u0005\u0002\u0000\u0000\u0131\u0132\u0003 \u0010"+
		"\u0000\u0132\u0133\u0005\u0003\u0000\u0000\u0133\u0154\u0001\u0000\u0000"+
		"\u0000\u0134\u0135\u0003.\u0017\u0000\u0135\u0136\u0005\"\u0000\u0000"+
		"\u0136\u0137\u0003,\u0016\u0000\u0137\u0154\u0001\u0000\u0000\u0000\u0138"+
		"\u0139\u0003,\u0016\u0000\u0139\u0142\u0005\u0002\u0000\u0000\u013a\u013f"+
		"\u0003 \u0010\u0000\u013b\u013c\u0005\t\u0000\u0000\u013c\u013e\u0003"+
		" \u0010\u0000\u013d\u013b\u0001\u0000\u0000\u0000\u013e\u0141\u0001\u0000"+
		"\u0000\u0000\u013f\u013d\u0001\u0000\u0000\u0000\u013f\u0140\u0001\u0000"+
		"\u0000\u0000\u0140\u0143\u0001\u0000\u0000\u0000\u0141\u013f\u0001\u0000"+
		"\u0000\u0000\u0142\u013a\u0001\u0000\u0000\u0000\u0142\u0143\u0001\u0000"+
		"\u0000\u0000\u0143\u0144\u0001\u0000\u0000\u0000\u0144\u0145\u0005\u0003"+
		"\u0000\u0000\u0145\u0154\u0001\u0000\u0000\u0000\u0146\u0147\u0007\u0001"+
		"\u0000\u0000\u0147\u0154\u0003 \u0010\r\u0148\u0154\u0007\u0002\u0000"+
		"\u0000\u0149\u0154\u0003,\u0016\u0000\u014a\u0154\u00059\u0000\u0000\u014b"+
		"\u0154\u0005:\u0000\u0000\u014c\u014d\u00053\u0000\u0000\u014d\u014e\u0003"+
		"\"\u0011\u0000\u014e\u014f\u0005\u0007\u0000\u0000\u014f\u0150\u0003 "+
		"\u0010\u0000\u0150\u0151\u0005\u001c\u0000\u0000\u0151\u0152\u0003 \u0010"+
		"\u0001\u0152\u0154\u0001\u0000\u0000\u0000\u0153\u012f\u0001\u0000\u0000"+
		"\u0000\u0153\u0134\u0001\u0000\u0000\u0000\u0153\u0138\u0001\u0000\u0000"+
		"\u0000\u0153\u0146\u0001\u0000\u0000\u0000\u0153\u0148\u0001\u0000\u0000"+
		"\u0000\u0153\u0149\u0001\u0000\u0000\u0000\u0153\u014a\u0001\u0000\u0000"+
		"\u0000\u0153\u014b\u0001\u0000\u0000\u0000\u0153\u014c\u0001\u0000\u0000"+
		"\u0000\u0154\u016f\u0001\u0000\u0000\u0000\u0155\u0156\n\f\u0000\u0000"+
		"\u0156\u0157\u0007\u0003\u0000\u0000\u0157\u016e\u0003 \u0010\r\u0158"+
		"\u0159\n\u000b\u0000\u0000\u0159\u015a\u0007\u0004\u0000\u0000\u015a\u016e"+
		"\u0003 \u0010\f\u015b\u015c\n\t\u0000\u0000\u015c\u015d\u0007\u0005\u0000"+
		"\u0000\u015d\u016e\u0003 \u0010\n\u015e\u015f\n\b\u0000\u0000\u015f\u0160"+
		"\u0007\u0006\u0000\u0000\u0160\u016e\u0003 \u0010\t\u0161\u0162\n\u0007"+
		"\u0000\u0000\u0162\u0163\u0007\u0007\u0000\u0000\u0163\u016e\u0003 \u0010"+
		"\b\u0164\u0165\n\u0006\u0000\u0000\u0165\u0166\u0005\u001a\u0000\u0000"+
		"\u0166\u0167\u0003 \u0010\u0000\u0167\u0168\u0005\n\u0000\u0000\u0168"+
		"\u0169\u0003 \u0010\u0006\u0169\u016e\u0001\u0000\u0000\u0000\u016a\u016b"+
		"\n\n\u0000\u0000\u016b\u016c\u0007\b\u0000\u0000\u016c\u016e\u0005\u001f"+
		"\u0000\u0000\u016d\u0155\u0001\u0000\u0000\u0000\u016d\u0158\u0001\u0000"+
		"\u0000\u0000\u016d\u015b\u0001\u0000\u0000\u0000\u016d\u015e\u0001\u0000"+
		"\u0000\u0000\u016d\u0161\u0001\u0000\u0000\u0000\u016d\u0164\u0001\u0000"+
		"\u0000\u0000\u016d\u016a\u0001\u0000\u0000\u0000\u016e\u0171\u0001\u0000"+
		"\u0000\u0000\u016f\u016d\u0001\u0000\u0000\u0000\u016f\u0170\u0001\u0000"+
		"\u0000\u0000\u0170!\u0001\u0000\u0000\u0000\u0171\u016f\u0001\u0000\u0000"+
		"\u0000\u0172\u0173\u0003,\u0016\u0000\u0173\u0174\u0005\n\u0000\u0000"+
		"\u0174\u0177\u0003\f\u0006\u0000\u0175\u0176\u00054\u0000\u0000\u0176"+
		"\u0178\u0003$\u0012\u0000\u0177\u0175\u0001\u0000\u0000\u0000\u0177\u0178"+
		"\u0001\u0000\u0000\u0000\u0178#\u0001\u0000\u0000\u0000\u0179\u017a\u0005"+
		"5\u0000\u0000\u017a\u017b\u0005\u0004\u0000\u0000\u017b\u0180\u0003&\u0013"+
		"\u0000\u017c\u017d\u0005\t\u0000\u0000\u017d\u017f\u0003&\u0013\u0000"+
		"\u017e\u017c\u0001\u0000\u0000\u0000\u017f\u0182\u0001\u0000\u0000\u0000"+
		"\u0180\u017e\u0001\u0000\u0000\u0000\u0180\u0181\u0001\u0000\u0000\u0000"+
		"\u0181\u0183\u0001\u0000\u0000\u0000\u0182\u0180\u0001\u0000\u0000\u0000"+
		"\u0183\u0184\u0005\u0005\u0000\u0000\u0184\u0192\u0001\u0000\u0000\u0000"+
		"\u0185\u0186\u00056\u0000\u0000\u0186\u0187\u0005\u0004\u0000\u0000\u0187"+
		"\u018c\u0003(\u0014\u0000\u0188\u0189\u0005\t\u0000\u0000\u0189\u018b"+
		"\u0003(\u0014\u0000\u018a\u0188\u0001\u0000\u0000\u0000\u018b\u018e\u0001"+
		"\u0000\u0000\u0000\u018c\u018a\u0001\u0000\u0000\u0000\u018c\u018d\u0001"+
		"\u0000\u0000\u0000\u018d\u018f\u0001\u0000\u0000\u0000\u018e\u018c\u0001"+
		"\u0000\u0000\u0000\u018f\u0190\u0005\u0005\u0000\u0000\u0190\u0192\u0001"+
		"\u0000\u0000\u0000\u0191\u0179\u0001\u0000\u0000\u0000\u0191\u0185\u0001"+
		"\u0000\u0000\u0000\u0192%\u0001\u0000\u0000\u0000\u0193\u0196\u00059\u0000"+
		"\u0000\u0194\u0196\u0007\u0002\u0000\u0000\u0195\u0193\u0001\u0000\u0000"+
		"\u0000\u0195\u0194\u0001\u0000\u0000\u0000\u0196\'\u0001\u0000\u0000\u0000"+
		"\u0197\u0198\u0003&\u0013\u0000\u0198\u0199\u0005\n\u0000\u0000\u0199"+
		"\u019a\u00059\u0000\u0000\u019a)\u0001\u0000\u0000\u0000\u019b\u019c\u0005"+
		"8\u0000\u0000\u019c+\u0001\u0000\u0000\u0000\u019d\u019e\u00058\u0000"+
		"\u0000\u019e-\u0001\u0000\u0000\u0000\u019f\u01a0\u00057\u0000\u0000\u01a0"+
		"/\u0001\u0000\u0000\u0000-24QT\\hrw|\u0085\u008c\u0094\u00a2\u00a6\u00ad"+
		"\u00b1\u00b3\u00bc\u00bf\u00c2\u00c6\u00ca\u00ce\u00d3\u00ea\u00f1\u00f6"+
		"\u010d\u0111\u0116\u011a\u0120\u0126\u012b\u012d\u013f\u0142\u0153\u016d"+
		"\u016f\u0177\u0180\u018c\u0191\u0195";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}