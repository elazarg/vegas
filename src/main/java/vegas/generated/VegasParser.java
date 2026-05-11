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
		T__45=46, T__46=47, T__47=48, T__48=49, T__49=50, T__50=51, ROLE_ID=52, 
		LOWER_ID=53, INT=54, ADDRESS=55, STRING=56, BlockComment=57, LineComment=58, 
		WS=59;
	public static final int
		RULE_program = 0, RULE_gameDec = 1, RULE_gameId = 2, RULE_typeDec = 3, 
		RULE_macroDec = 4, RULE_paramDec = 5, RULE_typeExp = 6, RULE_ext = 7, 
		RULE_query = 8, RULE_queryHandler = 9, RULE_groupHandler = 10, RULE_outcome = 11, 
		RULE_item = 12, RULE_exp = 13, RULE_varDec = 14, RULE_distExp = 15, RULE_distVal = 16, 
		RULE_weightedItem = 17, RULE_typeId = 18, RULE_varId = 19, RULE_roleId = 20;
	private static String[] makeRuleNames() {
		return new String[] {
			"program", "gameDec", "gameId", "typeDec", "macroDec", "paramDec", "typeExp", 
			"ext", "query", "queryHandler", "groupHandler", "outcome", "item", "exp", 
			"varDec", "distExp", "distVal", "weightedItem", "typeId", "varId", "roleId"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'game'", "'('", "')'", "'{'", "'}'", "'type'", "'='", "'macro'", 
			"','", "':'", "';'", "'..'", "'join'", "'yield'", "'reveal'", "'commit'", 
			"'random'", "'or'", "'withdraw'", "'$'", "'where'", "'||'", "'?'", "'let'", 
			"'in'", "'split'", "'burn'", "'null'", "'->'", "'.'", "'-'", "'!'", "'*'", 
			"'/'", "'%'", "'+'", "'!='", "'=='", "'<'", "'<='", "'>='", "'>'", "'<->'", 
			"'<-!->'", "'&&'", "'true'", "'false'", "'let!'", "'~'", "'uniform'", 
			"'weighted'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, "ROLE_ID", "LOWER_ID", "INT", "ADDRESS", "STRING", 
			"BlockComment", "LineComment", "WS"
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
			setState(46);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__5 || _la==T__7) {
				{
				setState(44);
				_errHandler.sync(this);
				switch (_input.LA(1)) {
				case T__5:
					{
					setState(42);
					typeDec();
					}
					break;
				case T__7:
					{
					setState(43);
					macroDec();
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				}
				setState(48);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(49);
			gameDec();
			setState(50);
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
			setState(52);
			match(T__0);
			setState(53);
			((GameDecContext)_localctx).name = gameId();
			setState(54);
			match(T__1);
			setState(55);
			match(T__2);
			setState(56);
			match(T__3);
			setState(57);
			ext();
			setState(58);
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
			setState(60);
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
			setState(62);
			match(T__5);
			setState(63);
			((TypeDecContext)_localctx).name = typeId();
			setState(64);
			match(T__6);
			setState(65);
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
			setState(67);
			match(T__7);
			setState(68);
			((MacroDecContext)_localctx).name = varId();
			setState(69);
			match(T__1);
			setState(78);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==LOWER_ID) {
				{
				setState(70);
				((MacroDecContext)_localctx).paramDec = paramDec();
				((MacroDecContext)_localctx).params.add(((MacroDecContext)_localctx).paramDec);
				setState(75);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(71);
					match(T__8);
					setState(72);
					((MacroDecContext)_localctx).paramDec = paramDec();
					((MacroDecContext)_localctx).params.add(((MacroDecContext)_localctx).paramDec);
					}
					}
					setState(77);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(80);
			match(T__2);
			setState(81);
			match(T__9);
			setState(82);
			((MacroDecContext)_localctx).resultType = typeExp();
			setState(83);
			match(T__6);
			setState(84);
			((MacroDecContext)_localctx).body = exp(0);
			setState(86);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__10) {
				{
				setState(85);
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
			setState(88);
			((ParamDecContext)_localctx).name = varId();
			setState(89);
			match(T__9);
			setState(90);
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
			setState(108);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				_localctx = new SubsetTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(92);
				match(T__3);
				setState(93);
				((SubsetTypeExpContext)_localctx).INT = match(INT);
				((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
				setState(98);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(94);
					match(T__8);
					setState(95);
					((SubsetTypeExpContext)_localctx).INT = match(INT);
					((SubsetTypeExpContext)_localctx).vals.add(((SubsetTypeExpContext)_localctx).INT);
					}
					}
					setState(100);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(101);
				match(T__4);
				}
				break;
			case 2:
				_localctx = new RangeTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(102);
				match(T__3);
				setState(103);
				((RangeTypeExpContext)_localctx).start = match(INT);
				setState(104);
				match(T__11);
				setState(105);
				((RangeTypeExpContext)_localctx).end = match(INT);
				setState(106);
				match(T__4);
				}
				break;
			case 3:
				_localctx = new IdTypeExpContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(107);
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
		public OutcomeContext outcome() {
			return getRuleContext(OutcomeContext.class,0);
		}
		public WithdrawExtContext(ExtContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitWithdrawExt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExtContext ext() throws RecognitionException {
		ExtContext _localctx = new ExtContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_ext);
		int _la;
		try {
			setState(125);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__12:
			case T__13:
			case T__14:
			case T__15:
			case T__16:
				_localctx = new ReceiveExtContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(110);
				((ReceiveExtContext)_localctx).kind = _input.LT(1);
				_la = _input.LA(1);
				if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 253952L) != 0)) ) {
					((ReceiveExtContext)_localctx).kind = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(113);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__17) {
					{
					setState(111);
					match(T__17);
					setState(112);
					((ReceiveExtContext)_localctx).handler = groupHandler();
					}
				}

				setState(116); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(115);
					query();
					}
					}
					setState(118); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ROLE_ID );
				setState(120);
				match(T__10);
				setState(121);
				ext();
				}
				break;
			case T__18:
				_localctx = new WithdrawExtContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(123);
				match(T__18);
				setState(124);
				outcome();
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
			setState(127);
			((QueryContext)_localctx).role = roleId();
			setState(140);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__1) {
				{
				setState(128);
				match(T__1);
				setState(137);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==LOWER_ID) {
					{
					setState(129);
					((QueryContext)_localctx).varDec = varDec();
					((QueryContext)_localctx).decls.add(((QueryContext)_localctx).varDec);
					setState(134);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__8) {
						{
						{
						setState(130);
						match(T__8);
						setState(131);
						((QueryContext)_localctx).varDec = varDec();
						((QueryContext)_localctx).decls.add(((QueryContext)_localctx).varDec);
						}
						}
						setState(136);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(139);
				match(T__2);
				}
			}

			setState(144);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__19) {
				{
				setState(142);
				match(T__19);
				setState(143);
				((QueryContext)_localctx).deposit = match(INT);
				}
			}

			setState(148);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__20) {
				{
				setState(146);
				match(T__20);
				setState(147);
				((QueryContext)_localctx).cond = exp(0);
				}
			}

			setState(152);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__21) {
				{
				setState(150);
				match(T__21);
				setState(151);
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
		enterRule(_localctx, 18, RULE_queryHandler);
		int _la;
		try {
			setState(182);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,17,_ctx) ) {
			case 1:
				_localctx = new IfQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(154);
				((IfQueryHandlerContext)_localctx).cond = exp(0);
				setState(155);
				match(T__22);
				setState(156);
				((IfQueryHandlerContext)_localctx).ifTrue = queryHandler();
				setState(157);
				match(T__9);
				setState(158);
				((IfQueryHandlerContext)_localctx).ifFalse = queryHandler();
				}
				break;
			case 2:
				_localctx = new LetQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(160);
				match(T__23);
				setState(161);
				((LetQueryHandlerContext)_localctx).dec = varDec();
				setState(162);
				match(T__6);
				setState(163);
				((LetQueryHandlerContext)_localctx).init = exp(0);
				setState(164);
				match(T__24);
				setState(165);
				((LetQueryHandlerContext)_localctx).body = queryHandler();
				}
				break;
			case 3:
				_localctx = new ParenQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(167);
				match(T__1);
				setState(168);
				queryHandler();
				setState(169);
				match(T__2);
				}
				break;
			case 4:
				_localctx = new OutcomeQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(171);
				match(T__3);
				setState(173); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(172);
					((OutcomeQueryHandlerContext)_localctx).item = item();
					((OutcomeQueryHandlerContext)_localctx).items.add(((OutcomeQueryHandlerContext)_localctx).item);
					}
					}
					setState(175); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ROLE_ID );
				setState(177);
				match(T__4);
				}
				break;
			case 5:
				_localctx = new SplitQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(179);
				match(T__25);
				}
				break;
			case 6:
				_localctx = new BurnQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(180);
				match(T__26);
				}
				break;
			case 7:
				_localctx = new NullQueryHandlerContext(_localctx);
				enterOuterAlt(_localctx, 7);
				{
				setState(181);
				match(T__27);
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
		enterRule(_localctx, 20, RULE_groupHandler);
		try {
			setState(187);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__25:
				_localctx = new SplitHandlerContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(184);
				match(T__25);
				}
				break;
			case T__26:
				_localctx = new BurnHandlerContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(185);
				match(T__26);
				}
				break;
			case T__27:
				_localctx = new NullHandlerContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(186);
				match(T__27);
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
		enterRule(_localctx, 22, RULE_outcome);
		int _la;
		try {
			setState(214);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,20,_ctx) ) {
			case 1:
				_localctx = new IfOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(189);
				((IfOutcomeContext)_localctx).cond = exp(0);
				setState(190);
				match(T__22);
				setState(191);
				((IfOutcomeContext)_localctx).ifTrue = outcome();
				setState(192);
				match(T__9);
				setState(193);
				((IfOutcomeContext)_localctx).ifFalse = outcome();
				}
				break;
			case 2:
				_localctx = new LetOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(195);
				match(T__23);
				setState(196);
				((LetOutcomeContext)_localctx).dec = varDec();
				setState(197);
				match(T__6);
				setState(198);
				((LetOutcomeContext)_localctx).init = exp(0);
				setState(199);
				match(T__24);
				setState(200);
				((LetOutcomeContext)_localctx).body = outcome();
				}
				break;
			case 3:
				_localctx = new ParenOutcomeContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(202);
				match(T__1);
				setState(203);
				outcome();
				setState(204);
				match(T__2);
				}
				break;
			case 4:
				_localctx = new OutcomeExpContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(206);
				match(T__3);
				setState(208); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(207);
					((OutcomeExpContext)_localctx).item = item();
					((OutcomeExpContext)_localctx).items.add(((OutcomeExpContext)_localctx).item);
					}
					}
					setState(210); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ROLE_ID );
				setState(212);
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
	public static class ItemContext extends ParserRuleContext {
		public RoleIdContext role;
		public ExpContext exp() {
			return getRuleContext(ExpContext.class,0);
		}
		public RoleIdContext roleId() {
			return getRuleContext(RoleIdContext.class,0);
		}
		public ItemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_item; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VegasVisitor ) return ((VegasVisitor<? extends T>)visitor).visitItem(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ItemContext item() throws RecognitionException {
		ItemContext _localctx = new ItemContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_item);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(216);
			((ItemContext)_localctx).role = roleId();
			setState(217);
			match(T__28);
			setState(218);
			exp(0);
			setState(220);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__10) {
				{
				setState(219);
				match(T__10);
				}
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
		int _startState = 26;
		enterRecursionRule(_localctx, 26, RULE_exp, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(258);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,24,_ctx) ) {
			case 1:
				{
				_localctx = new ParenExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(223);
				match(T__1);
				setState(224);
				exp(0);
				setState(225);
				match(T__2);
				}
				break;
			case 2:
				{
				_localctx = new MemberExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(227);
				((MemberExpContext)_localctx).role = roleId();
				setState(228);
				match(T__29);
				setState(229);
				((MemberExpContext)_localctx).field = varId();
				}
				break;
			case 3:
				{
				_localctx = new CallExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(231);
				((CallExpContext)_localctx).callee = varId();
				setState(232);
				match(T__1);
				setState(241);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & 68046582062252036L) != 0)) {
					{
					setState(233);
					((CallExpContext)_localctx).exp = exp(0);
					((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
					setState(238);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__8) {
						{
						{
						setState(234);
						match(T__8);
						setState(235);
						((CallExpContext)_localctx).exp = exp(0);
						((CallExpContext)_localctx).args.add(((CallExpContext)_localctx).exp);
						}
						}
						setState(240);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(243);
				match(T__2);
				}
				break;
			case 4:
				{
				_localctx = new UnOpExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(245);
				((UnOpExpContext)_localctx).op = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==T__30 || _la==T__31) ) {
					((UnOpExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(246);
				exp(13);
				}
				break;
			case 5:
				{
				_localctx = new BoolLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(247);
				_la = _input.LA(1);
				if ( !(_la==T__45 || _la==T__46) ) {
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
				setState(248);
				((IdExpContext)_localctx).name = varId();
				}
				break;
			case 7:
				{
				_localctx = new NumLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(249);
				match(INT);
				}
				break;
			case 8:
				{
				_localctx = new AddressLiteralExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(250);
				match(ADDRESS);
				}
				break;
			case 9:
				{
				_localctx = new LetExpContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(251);
				match(T__47);
				setState(252);
				((LetExpContext)_localctx).dec = varDec();
				setState(253);
				match(T__6);
				setState(254);
				((LetExpContext)_localctx).init = exp(0);
				setState(255);
				match(T__24);
				setState(256);
				((LetExpContext)_localctx).body = exp(1);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(286);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,26,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(284);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,25,_ctx) ) {
					case 1:
						{
						_localctx = new BinOpMultExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpMultExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(260);
						if (!(precpred(_ctx, 12))) throw new FailedPredicateException(this, "precpred(_ctx, 12)");
						setState(261);
						((BinOpMultExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 60129542144L) != 0)) ) {
							((BinOpMultExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(262);
						((BinOpMultExpContext)_localctx).right = exp(13);
						}
						break;
					case 2:
						{
						_localctx = new BinOpAddExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpAddExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(263);
						if (!(precpred(_ctx, 11))) throw new FailedPredicateException(this, "precpred(_ctx, 11)");
						setState(264);
						((BinOpAddExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__30 || _la==T__35) ) {
							((BinOpAddExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(265);
						((BinOpAddExpContext)_localctx).right = exp(12);
						}
						break;
					case 3:
						{
						_localctx = new BinOpCompExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpCompExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(266);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(267);
						((BinOpCompExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 8246337208320L) != 0)) ) {
							((BinOpCompExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(268);
						((BinOpCompExpContext)_localctx).right = exp(10);
						}
						break;
					case 4:
						{
						_localctx = new BinOpEqExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpEqExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(269);
						if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
						setState(270);
						((BinOpEqExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 26800595927040L) != 0)) ) {
							((BinOpEqExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(271);
						((BinOpEqExpContext)_localctx).right = exp(9);
						}
						break;
					case 5:
						{
						_localctx = new BinOpBoolExpContext(new ExpContext(_parentctx, _parentState));
						((BinOpBoolExpContext)_localctx).left = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(272);
						if (!(precpred(_ctx, 7))) throw new FailedPredicateException(this, "precpred(_ctx, 7)");
						setState(273);
						((BinOpBoolExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__21 || _la==T__44) ) {
							((BinOpBoolExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(274);
						((BinOpBoolExpContext)_localctx).right = exp(8);
						}
						break;
					case 6:
						{
						_localctx = new IfExpContext(new ExpContext(_parentctx, _parentState));
						((IfExpContext)_localctx).cond = _prevctx;
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(275);
						if (!(precpred(_ctx, 6))) throw new FailedPredicateException(this, "precpred(_ctx, 6)");
						setState(276);
						match(T__22);
						setState(277);
						((IfExpContext)_localctx).ifTrue = exp(0);
						setState(278);
						match(T__9);
						setState(279);
						((IfExpContext)_localctx).ifFalse = exp(6);
						}
						break;
					case 7:
						{
						_localctx = new UndefExpContext(new ExpContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_exp);
						setState(281);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(282);
						((UndefExpContext)_localctx).op = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__36 || _la==T__37) ) {
							((UndefExpContext)_localctx).op = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(283);
						match(T__27);
						}
						break;
					}
					} 
				}
				setState(288);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,26,_ctx);
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
		enterRule(_localctx, 28, RULE_varDec);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(289);
			((VarDecContext)_localctx).name = varId();
			setState(290);
			match(T__9);
			setState(291);
			((VarDecContext)_localctx).type = typeExp();
			setState(294);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__48) {
				{
				setState(292);
				match(T__48);
				setState(293);
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
		enterRule(_localctx, 30, RULE_distExp);
		int _la;
		try {
			setState(320);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__49:
				_localctx = new UniformDistExpContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(296);
				match(T__49);
				setState(297);
				match(T__3);
				setState(298);
				((UniformDistExpContext)_localctx).distVal = distVal();
				((UniformDistExpContext)_localctx).vals.add(((UniformDistExpContext)_localctx).distVal);
				setState(303);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(299);
					match(T__8);
					setState(300);
					((UniformDistExpContext)_localctx).distVal = distVal();
					((UniformDistExpContext)_localctx).vals.add(((UniformDistExpContext)_localctx).distVal);
					}
					}
					setState(305);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(306);
				match(T__4);
				}
				break;
			case T__50:
				_localctx = new WeightedDistExpContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(308);
				match(T__50);
				setState(309);
				match(T__3);
				setState(310);
				((WeightedDistExpContext)_localctx).weightedItem = weightedItem();
				((WeightedDistExpContext)_localctx).items.add(((WeightedDistExpContext)_localctx).weightedItem);
				setState(315);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__8) {
					{
					{
					setState(311);
					match(T__8);
					setState(312);
					((WeightedDistExpContext)_localctx).weightedItem = weightedItem();
					((WeightedDistExpContext)_localctx).items.add(((WeightedDistExpContext)_localctx).weightedItem);
					}
					}
					setState(317);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(318);
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
		enterRule(_localctx, 32, RULE_distVal);
		int _la;
		try {
			setState(324);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case INT:
				_localctx = new NumDistValContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(322);
				match(INT);
				}
				break;
			case T__45:
			case T__46:
				_localctx = new BoolDistValContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(323);
				_la = _input.LA(1);
				if ( !(_la==T__45 || _la==T__46) ) {
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
		enterRule(_localctx, 34, RULE_weightedItem);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(326);
			((WeightedItemContext)_localctx).value = distVal();
			setState(327);
			match(T__9);
			setState(328);
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
		enterRule(_localctx, 36, RULE_typeId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(330);
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
		enterRule(_localctx, 38, RULE_varId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(332);
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
		enterRule(_localctx, 40, RULE_roleId);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(334);
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
		case 13:
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
		"\u0004\u0001;\u0151\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"+
		"\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"+
		"\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"+
		"\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b\u0002"+
		"\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002\u000f\u0007\u000f"+
		"\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002\u0012\u0007\u0012"+
		"\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014\u0001\u0000\u0001\u0000"+
		"\u0005\u0000-\b\u0000\n\u0000\f\u00000\t\u0000\u0001\u0000\u0001\u0000"+
		"\u0001\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0002\u0001\u0002\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0005\u0004J\b\u0004"+
		"\n\u0004\f\u0004M\t\u0004\u0003\u0004O\b\u0004\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0003\u0004W\b\u0004"+
		"\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0005\u0006a\b\u0006\n\u0006\f\u0006d\t\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0003\u0006m\b\u0006\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0003\u0007r\b\u0007\u0001\u0007\u0004\u0007u\b\u0007\u000b\u0007\f\u0007"+
		"v\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0003\u0007"+
		"~\b\u0007\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0005\b\u0085\b\b\n"+
		"\b\f\b\u0088\t\b\u0003\b\u008a\b\b\u0001\b\u0003\b\u008d\b\b\u0001\b\u0001"+
		"\b\u0003\b\u0091\b\b\u0001\b\u0001\b\u0003\b\u0095\b\b\u0001\b\u0001\b"+
		"\u0003\b\u0099\b\b\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001"+
		"\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001"+
		"\t\u0001\t\u0001\t\u0001\t\u0004\t\u00ae\b\t\u000b\t\f\t\u00af\u0001\t"+
		"\u0001\t\u0001\t\u0001\t\u0001\t\u0003\t\u00b7\b\t\u0001\n\u0001\n\u0001"+
		"\n\u0003\n\u00bc\b\n\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001"+
		"\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001"+
		"\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001"+
		"\u000b\u0001\u000b\u0001\u000b\u0004\u000b\u00d1\b\u000b\u000b\u000b\f"+
		"\u000b\u00d2\u0001\u000b\u0001\u000b\u0003\u000b\u00d7\b\u000b\u0001\f"+
		"\u0001\f\u0001\f\u0001\f\u0003\f\u00dd\b\f\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0005\r\u00ed\b\r\n\r\f\r\u00f0\t\r\u0003\r\u00f2\b\r\u0001"+
		"\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0003\r\u0103\b\r\u0001\r\u0001"+
		"\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001\r\u0001"+
		"\r\u0001\r\u0001\r\u0001\r\u0001\r\u0005\r\u011d\b\r\n\r\f\r\u0120\t\r"+
		"\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0001\u000e\u0003\u000e"+
		"\u0127\b\u000e\u0001\u000f\u0001\u000f\u0001\u000f\u0001\u000f\u0001\u000f"+
		"\u0005\u000f\u012e\b\u000f\n\u000f\f\u000f\u0131\t\u000f\u0001\u000f\u0001"+
		"\u000f\u0001\u000f\u0001\u000f\u0001\u000f\u0001\u000f\u0001\u000f\u0005"+
		"\u000f\u013a\b\u000f\n\u000f\f\u000f\u013d\t\u000f\u0001\u000f\u0001\u000f"+
		"\u0003\u000f\u0141\b\u000f\u0001\u0010\u0001\u0010\u0003\u0010\u0145\b"+
		"\u0010\u0001\u0011\u0001\u0011\u0001\u0011\u0001\u0011\u0001\u0012\u0001"+
		"\u0012\u0001\u0013\u0001\u0013\u0001\u0014\u0001\u0014\u0001\u0014\u0000"+
		"\u0001\u001a\u0015\u0000\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014"+
		"\u0016\u0018\u001a\u001c\u001e \"$&(\u0000\t\u0001\u0000\r\u0011\u0001"+
		"\u0000\u001f \u0001\u0000./\u0001\u0000!#\u0002\u0000\u001f\u001f$$\u0001"+
		"\u0000\'*\u0002\u0000%&+,\u0002\u0000\u0016\u0016--\u0001\u0000%&\u0170"+
		"\u0000.\u0001\u0000\u0000\u0000\u00024\u0001\u0000\u0000\u0000\u0004<"+
		"\u0001\u0000\u0000\u0000\u0006>\u0001\u0000\u0000\u0000\bC\u0001\u0000"+
		"\u0000\u0000\nX\u0001\u0000\u0000\u0000\fl\u0001\u0000\u0000\u0000\u000e"+
		"}\u0001\u0000\u0000\u0000\u0010\u007f\u0001\u0000\u0000\u0000\u0012\u00b6"+
		"\u0001\u0000\u0000\u0000\u0014\u00bb\u0001\u0000\u0000\u0000\u0016\u00d6"+
		"\u0001\u0000\u0000\u0000\u0018\u00d8\u0001\u0000\u0000\u0000\u001a\u0102"+
		"\u0001\u0000\u0000\u0000\u001c\u0121\u0001\u0000\u0000\u0000\u001e\u0140"+
		"\u0001\u0000\u0000\u0000 \u0144\u0001\u0000\u0000\u0000\"\u0146\u0001"+
		"\u0000\u0000\u0000$\u014a\u0001\u0000\u0000\u0000&\u014c\u0001\u0000\u0000"+
		"\u0000(\u014e\u0001\u0000\u0000\u0000*-\u0003\u0006\u0003\u0000+-\u0003"+
		"\b\u0004\u0000,*\u0001\u0000\u0000\u0000,+\u0001\u0000\u0000\u0000-0\u0001"+
		"\u0000\u0000\u0000.,\u0001\u0000\u0000\u0000./\u0001\u0000\u0000\u0000"+
		"/1\u0001\u0000\u0000\u00000.\u0001\u0000\u0000\u000012\u0003\u0002\u0001"+
		"\u000023\u0005\u0000\u0000\u00013\u0001\u0001\u0000\u0000\u000045\u0005"+
		"\u0001\u0000\u000056\u0003\u0004\u0002\u000067\u0005\u0002\u0000\u0000"+
		"78\u0005\u0003\u0000\u000089\u0005\u0004\u0000\u00009:\u0003\u000e\u0007"+
		"\u0000:;\u0005\u0005\u0000\u0000;\u0003\u0001\u0000\u0000\u0000<=\u0003"+
		"&\u0013\u0000=\u0005\u0001\u0000\u0000\u0000>?\u0005\u0006\u0000\u0000"+
		"?@\u0003$\u0012\u0000@A\u0005\u0007\u0000\u0000AB\u0003\f\u0006\u0000"+
		"B\u0007\u0001\u0000\u0000\u0000CD\u0005\b\u0000\u0000DE\u0003&\u0013\u0000"+
		"EN\u0005\u0002\u0000\u0000FK\u0003\n\u0005\u0000GH\u0005\t\u0000\u0000"+
		"HJ\u0003\n\u0005\u0000IG\u0001\u0000\u0000\u0000JM\u0001\u0000\u0000\u0000"+
		"KI\u0001\u0000\u0000\u0000KL\u0001\u0000\u0000\u0000LO\u0001\u0000\u0000"+
		"\u0000MK\u0001\u0000\u0000\u0000NF\u0001\u0000\u0000\u0000NO\u0001\u0000"+
		"\u0000\u0000OP\u0001\u0000\u0000\u0000PQ\u0005\u0003\u0000\u0000QR\u0005"+
		"\n\u0000\u0000RS\u0003\f\u0006\u0000ST\u0005\u0007\u0000\u0000TV\u0003"+
		"\u001a\r\u0000UW\u0005\u000b\u0000\u0000VU\u0001\u0000\u0000\u0000VW\u0001"+
		"\u0000\u0000\u0000W\t\u0001\u0000\u0000\u0000XY\u0003&\u0013\u0000YZ\u0005"+
		"\n\u0000\u0000Z[\u0003\f\u0006\u0000[\u000b\u0001\u0000\u0000\u0000\\"+
		"]\u0005\u0004\u0000\u0000]b\u00056\u0000\u0000^_\u0005\t\u0000\u0000_"+
		"a\u00056\u0000\u0000`^\u0001\u0000\u0000\u0000ad\u0001\u0000\u0000\u0000"+
		"b`\u0001\u0000\u0000\u0000bc\u0001\u0000\u0000\u0000ce\u0001\u0000\u0000"+
		"\u0000db\u0001\u0000\u0000\u0000em\u0005\u0005\u0000\u0000fg\u0005\u0004"+
		"\u0000\u0000gh\u00056\u0000\u0000hi\u0005\f\u0000\u0000ij\u00056\u0000"+
		"\u0000jm\u0005\u0005\u0000\u0000km\u0003$\u0012\u0000l\\\u0001\u0000\u0000"+
		"\u0000lf\u0001\u0000\u0000\u0000lk\u0001\u0000\u0000\u0000m\r\u0001\u0000"+
		"\u0000\u0000nq\u0007\u0000\u0000\u0000op\u0005\u0012\u0000\u0000pr\u0003"+
		"\u0014\n\u0000qo\u0001\u0000\u0000\u0000qr\u0001\u0000\u0000\u0000rt\u0001"+
		"\u0000\u0000\u0000su\u0003\u0010\b\u0000ts\u0001\u0000\u0000\u0000uv\u0001"+
		"\u0000\u0000\u0000vt\u0001\u0000\u0000\u0000vw\u0001\u0000\u0000\u0000"+
		"wx\u0001\u0000\u0000\u0000xy\u0005\u000b\u0000\u0000yz\u0003\u000e\u0007"+
		"\u0000z~\u0001\u0000\u0000\u0000{|\u0005\u0013\u0000\u0000|~\u0003\u0016"+
		"\u000b\u0000}n\u0001\u0000\u0000\u0000}{\u0001\u0000\u0000\u0000~\u000f"+
		"\u0001\u0000\u0000\u0000\u007f\u008c\u0003(\u0014\u0000\u0080\u0089\u0005"+
		"\u0002\u0000\u0000\u0081\u0086\u0003\u001c\u000e\u0000\u0082\u0083\u0005"+
		"\t\u0000\u0000\u0083\u0085\u0003\u001c\u000e\u0000\u0084\u0082\u0001\u0000"+
		"\u0000\u0000\u0085\u0088\u0001\u0000\u0000\u0000\u0086\u0084\u0001\u0000"+
		"\u0000\u0000\u0086\u0087\u0001\u0000\u0000\u0000\u0087\u008a\u0001\u0000"+
		"\u0000\u0000\u0088\u0086\u0001\u0000\u0000\u0000\u0089\u0081\u0001\u0000"+
		"\u0000\u0000\u0089\u008a\u0001\u0000\u0000\u0000\u008a\u008b\u0001\u0000"+
		"\u0000\u0000\u008b\u008d\u0005\u0003\u0000\u0000\u008c\u0080\u0001\u0000"+
		"\u0000\u0000\u008c\u008d\u0001\u0000\u0000\u0000\u008d\u0090\u0001\u0000"+
		"\u0000\u0000\u008e\u008f\u0005\u0014\u0000\u0000\u008f\u0091\u00056\u0000"+
		"\u0000\u0090\u008e\u0001\u0000\u0000\u0000\u0090\u0091\u0001\u0000\u0000"+
		"\u0000\u0091\u0094\u0001\u0000\u0000\u0000\u0092\u0093\u0005\u0015\u0000"+
		"\u0000\u0093\u0095\u0003\u001a\r\u0000\u0094\u0092\u0001\u0000\u0000\u0000"+
		"\u0094\u0095\u0001\u0000\u0000\u0000\u0095\u0098\u0001\u0000\u0000\u0000"+
		"\u0096\u0097\u0005\u0016\u0000\u0000\u0097\u0099\u0003\u0012\t\u0000\u0098"+
		"\u0096\u0001\u0000\u0000\u0000\u0098\u0099\u0001\u0000\u0000\u0000\u0099"+
		"\u0011\u0001\u0000\u0000\u0000\u009a\u009b\u0003\u001a\r\u0000\u009b\u009c"+
		"\u0005\u0017\u0000\u0000\u009c\u009d\u0003\u0012\t\u0000\u009d\u009e\u0005"+
		"\n\u0000\u0000\u009e\u009f\u0003\u0012\t\u0000\u009f\u00b7\u0001\u0000"+
		"\u0000\u0000\u00a0\u00a1\u0005\u0018\u0000\u0000\u00a1\u00a2\u0003\u001c"+
		"\u000e\u0000\u00a2\u00a3\u0005\u0007\u0000\u0000\u00a3\u00a4\u0003\u001a"+
		"\r\u0000\u00a4\u00a5\u0005\u0019\u0000\u0000\u00a5\u00a6\u0003\u0012\t"+
		"\u0000\u00a6\u00b7\u0001\u0000\u0000\u0000\u00a7\u00a8\u0005\u0002\u0000"+
		"\u0000\u00a8\u00a9\u0003\u0012\t\u0000\u00a9\u00aa\u0005\u0003\u0000\u0000"+
		"\u00aa\u00b7\u0001\u0000\u0000\u0000\u00ab\u00ad\u0005\u0004\u0000\u0000"+
		"\u00ac\u00ae\u0003\u0018\f\u0000\u00ad\u00ac\u0001\u0000\u0000\u0000\u00ae"+
		"\u00af\u0001\u0000\u0000\u0000\u00af\u00ad\u0001\u0000\u0000\u0000\u00af"+
		"\u00b0\u0001\u0000\u0000\u0000\u00b0\u00b1\u0001\u0000\u0000\u0000\u00b1"+
		"\u00b2\u0005\u0005\u0000\u0000\u00b2\u00b7\u0001\u0000\u0000\u0000\u00b3"+
		"\u00b7\u0005\u001a\u0000\u0000\u00b4\u00b7\u0005\u001b\u0000\u0000\u00b5"+
		"\u00b7\u0005\u001c\u0000\u0000\u00b6\u009a\u0001\u0000\u0000\u0000\u00b6"+
		"\u00a0\u0001\u0000\u0000\u0000\u00b6\u00a7\u0001\u0000\u0000\u0000\u00b6"+
		"\u00ab\u0001\u0000\u0000\u0000\u00b6\u00b3\u0001\u0000\u0000\u0000\u00b6"+
		"\u00b4\u0001\u0000\u0000\u0000\u00b6\u00b5\u0001\u0000\u0000\u0000\u00b7"+
		"\u0013\u0001\u0000\u0000\u0000\u00b8\u00bc\u0005\u001a\u0000\u0000\u00b9"+
		"\u00bc\u0005\u001b\u0000\u0000\u00ba\u00bc\u0005\u001c\u0000\u0000\u00bb"+
		"\u00b8\u0001\u0000\u0000\u0000\u00bb\u00b9\u0001\u0000\u0000\u0000\u00bb"+
		"\u00ba\u0001\u0000\u0000\u0000\u00bc\u0015\u0001\u0000\u0000\u0000\u00bd"+
		"\u00be\u0003\u001a\r\u0000\u00be\u00bf\u0005\u0017\u0000\u0000\u00bf\u00c0"+
		"\u0003\u0016\u000b\u0000\u00c0\u00c1\u0005\n\u0000\u0000\u00c1\u00c2\u0003"+
		"\u0016\u000b\u0000\u00c2\u00d7\u0001\u0000\u0000\u0000\u00c3\u00c4\u0005"+
		"\u0018\u0000\u0000\u00c4\u00c5\u0003\u001c\u000e\u0000\u00c5\u00c6\u0005"+
		"\u0007\u0000\u0000\u00c6\u00c7\u0003\u001a\r\u0000\u00c7\u00c8\u0005\u0019"+
		"\u0000\u0000\u00c8\u00c9\u0003\u0016\u000b\u0000\u00c9\u00d7\u0001\u0000"+
		"\u0000\u0000\u00ca\u00cb\u0005\u0002\u0000\u0000\u00cb\u00cc\u0003\u0016"+
		"\u000b\u0000\u00cc\u00cd\u0005\u0003\u0000\u0000\u00cd\u00d7\u0001\u0000"+
		"\u0000\u0000\u00ce\u00d0\u0005\u0004\u0000\u0000\u00cf\u00d1\u0003\u0018"+
		"\f\u0000\u00d0\u00cf\u0001\u0000\u0000\u0000\u00d1\u00d2\u0001\u0000\u0000"+
		"\u0000\u00d2\u00d0\u0001\u0000\u0000\u0000\u00d2\u00d3\u0001\u0000\u0000"+
		"\u0000\u00d3\u00d4\u0001\u0000\u0000\u0000\u00d4\u00d5\u0005\u0005\u0000"+
		"\u0000\u00d5\u00d7\u0001\u0000\u0000\u0000\u00d6\u00bd\u0001\u0000\u0000"+
		"\u0000\u00d6\u00c3\u0001\u0000\u0000\u0000\u00d6\u00ca\u0001\u0000\u0000"+
		"\u0000\u00d6\u00ce\u0001\u0000\u0000\u0000\u00d7\u0017\u0001\u0000\u0000"+
		"\u0000\u00d8\u00d9\u0003(\u0014\u0000\u00d9\u00da\u0005\u001d\u0000\u0000"+
		"\u00da\u00dc\u0003\u001a\r\u0000\u00db\u00dd\u0005\u000b\u0000\u0000\u00dc"+
		"\u00db\u0001\u0000\u0000\u0000\u00dc\u00dd\u0001\u0000\u0000\u0000\u00dd"+
		"\u0019\u0001\u0000\u0000\u0000\u00de\u00df\u0006\r\uffff\uffff\u0000\u00df"+
		"\u00e0\u0005\u0002\u0000\u0000\u00e0\u00e1\u0003\u001a\r\u0000\u00e1\u00e2"+
		"\u0005\u0003\u0000\u0000\u00e2\u0103\u0001\u0000\u0000\u0000\u00e3\u00e4"+
		"\u0003(\u0014\u0000\u00e4\u00e5\u0005\u001e\u0000\u0000\u00e5\u00e6\u0003"+
		"&\u0013\u0000\u00e6\u0103\u0001\u0000\u0000\u0000\u00e7\u00e8\u0003&\u0013"+
		"\u0000\u00e8\u00f1\u0005\u0002\u0000\u0000\u00e9\u00ee\u0003\u001a\r\u0000"+
		"\u00ea\u00eb\u0005\t\u0000\u0000\u00eb\u00ed\u0003\u001a\r\u0000\u00ec"+
		"\u00ea\u0001\u0000\u0000\u0000\u00ed\u00f0\u0001\u0000\u0000\u0000\u00ee"+
		"\u00ec\u0001\u0000\u0000\u0000\u00ee\u00ef\u0001\u0000\u0000\u0000\u00ef"+
		"\u00f2\u0001\u0000\u0000\u0000\u00f0\u00ee\u0001\u0000\u0000\u0000\u00f1"+
		"\u00e9\u0001\u0000\u0000\u0000\u00f1\u00f2\u0001\u0000\u0000\u0000\u00f2"+
		"\u00f3\u0001\u0000\u0000\u0000\u00f3\u00f4\u0005\u0003\u0000\u0000\u00f4"+
		"\u0103\u0001\u0000\u0000\u0000\u00f5\u00f6\u0007\u0001\u0000\u0000\u00f6"+
		"\u0103\u0003\u001a\r\r\u00f7\u0103\u0007\u0002\u0000\u0000\u00f8\u0103"+
		"\u0003&\u0013\u0000\u00f9\u0103\u00056\u0000\u0000\u00fa\u0103\u00057"+
		"\u0000\u0000\u00fb\u00fc\u00050\u0000\u0000\u00fc\u00fd\u0003\u001c\u000e"+
		"\u0000\u00fd\u00fe\u0005\u0007\u0000\u0000\u00fe\u00ff\u0003\u001a\r\u0000"+
		"\u00ff\u0100\u0005\u0019\u0000\u0000\u0100\u0101\u0003\u001a\r\u0001\u0101"+
		"\u0103\u0001\u0000\u0000\u0000\u0102\u00de\u0001\u0000\u0000\u0000\u0102"+
		"\u00e3\u0001\u0000\u0000\u0000\u0102\u00e7\u0001\u0000\u0000\u0000\u0102"+
		"\u00f5\u0001\u0000\u0000\u0000\u0102\u00f7\u0001\u0000\u0000\u0000\u0102"+
		"\u00f8\u0001\u0000\u0000\u0000\u0102\u00f9\u0001\u0000\u0000\u0000\u0102"+
		"\u00fa\u0001\u0000\u0000\u0000\u0102\u00fb\u0001\u0000\u0000\u0000\u0103"+
		"\u011e\u0001\u0000\u0000\u0000\u0104\u0105\n\f\u0000\u0000\u0105\u0106"+
		"\u0007\u0003\u0000\u0000\u0106\u011d\u0003\u001a\r\r\u0107\u0108\n\u000b"+
		"\u0000\u0000\u0108\u0109\u0007\u0004\u0000\u0000\u0109\u011d\u0003\u001a"+
		"\r\f\u010a\u010b\n\t\u0000\u0000\u010b\u010c\u0007\u0005\u0000\u0000\u010c"+
		"\u011d\u0003\u001a\r\n\u010d\u010e\n\b\u0000\u0000\u010e\u010f\u0007\u0006"+
		"\u0000\u0000\u010f\u011d\u0003\u001a\r\t\u0110\u0111\n\u0007\u0000\u0000"+
		"\u0111\u0112\u0007\u0007\u0000\u0000\u0112\u011d\u0003\u001a\r\b\u0113"+
		"\u0114\n\u0006\u0000\u0000\u0114\u0115\u0005\u0017\u0000\u0000\u0115\u0116"+
		"\u0003\u001a\r\u0000\u0116\u0117\u0005\n\u0000\u0000\u0117\u0118\u0003"+
		"\u001a\r\u0006\u0118\u011d\u0001\u0000\u0000\u0000\u0119\u011a\n\n\u0000"+
		"\u0000\u011a\u011b\u0007\b\u0000\u0000\u011b\u011d\u0005\u001c\u0000\u0000"+
		"\u011c\u0104\u0001\u0000\u0000\u0000\u011c\u0107\u0001\u0000\u0000\u0000"+
		"\u011c\u010a\u0001\u0000\u0000\u0000\u011c\u010d\u0001\u0000\u0000\u0000"+
		"\u011c\u0110\u0001\u0000\u0000\u0000\u011c\u0113\u0001\u0000\u0000\u0000"+
		"\u011c\u0119\u0001\u0000\u0000\u0000\u011d\u0120\u0001\u0000\u0000\u0000"+
		"\u011e\u011c\u0001\u0000\u0000\u0000\u011e\u011f\u0001\u0000\u0000\u0000"+
		"\u011f\u001b\u0001\u0000\u0000\u0000\u0120\u011e\u0001\u0000\u0000\u0000"+
		"\u0121\u0122\u0003&\u0013\u0000\u0122\u0123\u0005\n\u0000\u0000\u0123"+
		"\u0126\u0003\f\u0006\u0000\u0124\u0125\u00051\u0000\u0000\u0125\u0127"+
		"\u0003\u001e\u000f\u0000\u0126\u0124\u0001\u0000\u0000\u0000\u0126\u0127"+
		"\u0001\u0000\u0000\u0000\u0127\u001d\u0001\u0000\u0000\u0000\u0128\u0129"+
		"\u00052\u0000\u0000\u0129\u012a\u0005\u0004\u0000\u0000\u012a\u012f\u0003"+
		" \u0010\u0000\u012b\u012c\u0005\t\u0000\u0000\u012c\u012e\u0003 \u0010"+
		"\u0000\u012d\u012b\u0001\u0000\u0000\u0000\u012e\u0131\u0001\u0000\u0000"+
		"\u0000\u012f\u012d\u0001\u0000\u0000\u0000\u012f\u0130\u0001\u0000\u0000"+
		"\u0000\u0130\u0132\u0001\u0000\u0000\u0000\u0131\u012f\u0001\u0000\u0000"+
		"\u0000\u0132\u0133\u0005\u0005\u0000\u0000\u0133\u0141\u0001\u0000\u0000"+
		"\u0000\u0134\u0135\u00053\u0000\u0000\u0135\u0136\u0005\u0004\u0000\u0000"+
		"\u0136\u013b\u0003\"\u0011\u0000\u0137\u0138\u0005\t\u0000\u0000\u0138"+
		"\u013a\u0003\"\u0011\u0000\u0139\u0137\u0001\u0000\u0000\u0000\u013a\u013d"+
		"\u0001\u0000\u0000\u0000\u013b\u0139\u0001\u0000\u0000\u0000\u013b\u013c"+
		"\u0001\u0000\u0000\u0000\u013c\u013e\u0001\u0000\u0000\u0000\u013d\u013b"+
		"\u0001\u0000\u0000\u0000\u013e\u013f\u0005\u0005\u0000\u0000\u013f\u0141"+
		"\u0001\u0000\u0000\u0000\u0140\u0128\u0001\u0000\u0000\u0000\u0140\u0134"+
		"\u0001\u0000\u0000\u0000\u0141\u001f\u0001\u0000\u0000\u0000\u0142\u0145"+
		"\u00056\u0000\u0000\u0143\u0145\u0007\u0002\u0000\u0000\u0144\u0142\u0001"+
		"\u0000\u0000\u0000\u0144\u0143\u0001\u0000\u0000\u0000\u0145!\u0001\u0000"+
		"\u0000\u0000\u0146\u0147\u0003 \u0010\u0000\u0147\u0148\u0005\n\u0000"+
		"\u0000\u0148\u0149\u00056\u0000\u0000\u0149#\u0001\u0000\u0000\u0000\u014a"+
		"\u014b\u00055\u0000\u0000\u014b%\u0001\u0000\u0000\u0000\u014c\u014d\u0005"+
		"5\u0000\u0000\u014d\'\u0001\u0000\u0000\u0000\u014e\u014f\u00054\u0000"+
		"\u0000\u014f)\u0001\u0000\u0000\u0000 ,.KNVblqv}\u0086\u0089\u008c\u0090"+
		"\u0094\u0098\u00af\u00b6\u00bb\u00d2\u00d6\u00dc\u00ee\u00f1\u0102\u011c"+
		"\u011e\u0126\u012f\u013b\u0140\u0144";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}