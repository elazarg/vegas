grammar Vegas;

program : (typeDec | macroDec)* gameDec EOF ;

gameDec : 'game' name=gameId '(' ')' '{' ext '}' ;

gameId : varId ;

typeDec : 'type' name=typeId '=' typeExp ;

macroDec
    : 'macro' name=varId
      '(' (params+=paramDec (',' params+=paramDec)*)? ')'
      ':' resultType=typeExp
      '=' body=exp
      ';'?
    ;

paramDec
    : name=varId ':' type=typeExp
    ;

typeExp
    : '{' vals+=INT (',' vals+=INT)* '}'  # SubsetTypeExp
    | '{' start=INT '..' end=INT '}'      # RangeTypeExp
    | name=typeId                         # IdTypeExp
    ;

ext : kind=('join' | 'yield' | 'reveal' | 'commit' | 'random') ('or' handler=groupHandler)? query+ ';' ext  # ReceiveExt
    | 'withdraw' outcome                                                                                    # WithdrawExt
    ;

// Per-query handlers: only brace-wrapped outcomes (not split/burn keywords)
query : role=roleId ('(' (decls+=varDec (',' decls+=varDec)*)? ')')? ('$' deposit=INT)? ('where' cond=exp)? ('||' handler=queryHandler)? ;

// Query handlers: outcomes for individual query timeouts
queryHandler
    : <assoc=right> cond=exp '?' ifTrue=queryHandler ':' ifFalse=queryHandler # IfQueryHandler
    | 'let' dec=varDec '=' init=exp 'in' body=queryHandler                    # LetQueryHandler
    | '(' queryHandler ')'                                                     # ParenQueryHandler
    | '{' items+=item+ '}'                                                     # OutcomeQueryHandler
    | 'split'                                                                  # SplitQueryHandler
    | 'burn'                                                                   # BurnQueryHandler
    | 'null'                                                                   # NullQueryHandler
    ;

// Group handlers: split, burn, or null for multi-party steps
groupHandler
    : 'split'  # SplitHandler
    | 'burn'   # BurnHandler
    | 'null'   # NullHandler
    ;

outcome
    : <assoc=right> cond=exp '?' ifTrue=outcome ':' ifFalse=outcome # IfOutcome
    | 'let' dec=varDec '=' init=exp 'in' body=outcome               # LetOutcome
    | '(' outcome ')'                                               # ParenOutcome
    | '{' items+=item+ '}'                                          # OutcomeExp
    ;

item : (role=roleId '->' exp ';'?) ;

exp
    : '(' exp ')'                                            # ParenExp
    | role=roleId '.' field=varId                            # MemberExp
    | callee=varId '(' (args+=exp (',' args+=exp)*)?  ')'    # CallExp
    | op=('-' | '!') exp                                     # UnOpExp
    | left=exp op=('*' | '/' | '%') right=exp                # BinOpMultExp
    | left=exp op=('+' | '-') right=exp                      # BinOpAddExp
    | exp op=('!='|'==') 'null'                              # UndefExp
    | left=exp op=('<' | '<=' | '>=' | '>') right=exp        # BinOpCompExp
    | left=exp op=('==' | '!=' | '<->' | '<-!->') right=exp  # BinOpEqExp
    | left=exp op=('&&' | '||') right=exp                    # BinOpBoolExp
    | <assoc=right> cond=exp '?' ifTrue=exp ':' ifFalse=exp  # IfExp
    | ('true'|'false')                                       # BoolLiteralExp
    | name=varId                                             # IdExp
    | INT                                                    # NumLiteralExp
    | ADDRESS                                                # AddressLiteralExp
    | 'let!' dec=varDec '=' init=exp 'in' body=exp           # LetExp
    ;

varDec : name=varId ':' type=typeExp;

typeId: LOWER_ID ;
varId : LOWER_ID;
roleId: ROLE_ID;

// LEXER
ROLE_ID: [A-Z][a-zA-Z_0-9]*;
LOWER_ID: [a-z][a-zA-Z_0-9]*;
INT: ([1-9][0-9]* | [0]) ;
ADDRESS: '0x'([1-9a-fA-F][0-9a-fA-F]* | [0]) ;
STRING: '"' ( ~('"'|'\\') )* '"' ;
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\n]* -> skip ;
WS : [ \t\r\n]+ -> skip;
