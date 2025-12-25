## 1. What a Vegas game looks like

Vegas programs are written as `game` blocks. A `game` either:

* reaches a terminal `withdraw { ... }` (the only money-moving construct), or
* transfers control to another `game` (structurally, by inlining; there is no runtime call stack).

A minimal example:

```kotlin
game TakeAll[A | pool$2]() {
  withdraw { A -> 2 }
}

game main() {
  join Alice() $1 Bob() $1;           // instance locks a single pool P
  yield Bob(ok: bool) || TakeAll();   // if Bob quits here, go to TakeAll[Alice]
  withdraw { Alice -> 0; Bob -> 2 }   // normal outcome: Bob takes all
}
```

Intuition:

* The instance locks a single pool `P`.
* The program proceeds until it reaches a terminal `withdraw`.
* At certain points (join/yield/reveal), a role may **Quit**; `||` specifies what happens in that case.

`main()` is the entrypoint game. For now, `main` has no parameters; later it may, but that is out of scope here.

---

## 2. Core execution and money model

### 2.1 One locked global pool; one terminal allocation

A game instance locks a single global pool `P` when roles join. During gameplay there are **no transfers**. Money moves only once, at the end:

```kotlin
withdraw { Role1 -> a1; Role2 -> a2; ... }
```

### 2.2 Conservation

**Defined here:** terminal withdrawals must allocate the pool exactly.

* The sum of all payouts in `withdraw { ... }` must be **exactly** `P`.
* There is no implicit burn and no implicit “dust”.

A dedicated burn/sink mechanism may be added later (see Future directions).

---

## 3. Quit semantics and timeouts

### 3.1 Quit is a strategic role action

At the language level, **Quit is a move made by the role**. Whether the real-world cause is strategic abandonment, a timeout, or a connectivity failure is irrelevant to the game-theoretic model in this document.

### 3.2 Backend timeouts are an implementation mechanism

Backends may implement Quit via:

* explicit on-chain quit actions, and/or
* timeout-triggered forced transitions after a deadline.

The language and analysis treat these as the same: the role has Quit available at that point.

---

## 4. Handlers: specifying what happens on Quit

Vegas supports Quit handlers only at **single-actor** sites in this design.

### 4.1 `||` selects the Quit continuation

A handler is written with `||`:

```kotlin
yield Bob(ok: bool) || TakeAll();
```

Meaning:

* If Bob provides `ok`, continue normally.
* If Bob Quits instead, take the handler branch (`TakeAll()` here).

This is not exception handling and not a “time player”. It is simply “what happens if the role chooses Quit at this point”.

### 4.2 Supported handler sites

**Defined here:** handlers are supported only for the following *single-actor* constructs:

1. **join** (role fails to join / effectively quits during setup)

```kotlin
join Alice() $1 || Refund();
```

2. **yield** (role fails to provide an input)

```kotlin
yield Alice(x: int) || Catch();
```

3. **reveal** (role fails to reveal a committed value)

```kotlin
reveal Alice(x) || Catch();
```

### 4.3 Availability rule (scope discipline)

**Defined here:** the handler is typechecked in the environment **before** the attempted action.

So:

* Values that would have been produced by the attempted action are **not in scope** in the handler.

Example:

```kotlin
yield Alice(x:int) || { /* x is NOT available here */ ... }
```

This makes Quit branches well-defined and prevents recovery code from depending on missing inputs/secrets.

### 4.4 Recipient ambiguity rule

Handlers often redistribute the outcome among remaining roles.

**Defined here:** whenever it is ambiguous which roles are meant to receive payouts, roles must be passed explicitly. Vegas does not infer recipients “by symmetry” or “by remaining players” in this design.

---

## 5. Subgames and composition

### 5.1 Subgames are structural (inlined)

Calling a subgame is not a runtime call. Semantics are defined by **inlining** into one whole-program control flow. There is no return value; control flow ends when a terminal `withdraw` is reached.

This design relies on hygienic inlining (renaming to avoid collisions) as a compiler responsibility.

---

## 6. Scale-typed global pools

This section defines how a game can be written once and instantiated at many stake sizes without rewriting logic.

### 6.1 Coefficients and a global scale `k`

Numeric literals in payouts are **coefficients**. At instantiation time the instance chooses a global scale `k > 0`, and a literal `n` denotes `n·k` units.

### 6.2 Pool weight annotation `pool$W`

A game may annotate the required weight of the global pool:

```kotlin
game TakeAll[A | pool$2]() {
  withdraw { A -> 2 }
}
```

Meaning:

* The instance pool satisfies `P = 2·k` for some `k > 0`.
* The withdrawal allocates exactly `P`.

### 6.3 Compiler obligations

**Defined here:** the compiler/backend must ensure:

* `k > 0`,
* the locked pool `P` is exactly `W·k` where `W` is the declared pool weight,
* every terminal `withdraw` sums exactly to `P` (conservation).

In the integer-only setting of this design, this is equivalent to: `P` divisible by `W`, with `k = P/W`.

---

## 7. Multiple leavers: what is covered vs deferred

### 7.1 Covered: sequential Quit at single-actor sites

Multiple Quits over time are expressible when they occur at distinct single-actor sites, because each site can have its own handler.

### 7.2 Deferred: simultaneous actions and staged multi-party failures

**Not defined here:** Quit handlers for multi-actor “simultaneous” constructs, including commit–reveal protocols where multiple parties may fail at different stages (commit vs reveal).

Reason: once multiple roles can fail within a single conceptual step, a handler must refer to (a) which subset failed and (b) how recipients are chosen among the remaining roles—both require additional surface design (e.g., explicit subset matching and/or symmetry annotations).

**Parser/validator rule (recommended):**

* The grammar may accept `||` on simultaneous constructs, but the validator must reject it with a clear error (“handlers currently supported only for single-actor join/yield/reveal; please desugar/unroll”).

---

## 8. Future directions (non-binding)

These are explicitly not part of the defined design, but are expected extensions:

1. **Burn/sink support**
   A dedicated `BURN` recipient (or equivalent) to explicitly destroy value while preserving “withdraw sums exactly to P” as a structural invariant.

2. **Simultaneous handlers**
   A handler form for multi-actor steps that deliberately provides no access to missing committed/hidden values and can transition to a subgame with fewer participants.

3. **Symmetry annotations / inference**
   A way to mark subgames as symmetric under permutation of certain roles, allowing safe inference of recipient mapping in otherwise ambiguous handlers.

---

## 9. Summary

This design defines a compact, compiler-checkable core:

* A single locked global pool `P`.
* A single terminal `withdraw` that must allocate exactly `P`.
* Quit as a role move; timeouts are backend mechanics.
* `||` handlers for Quit at **single-actor** join/yield/reveal sites, with a strict availability rule.
* Scale-typed pools (`pool$W`) so games are written in coefficients and instantiated via a positive scale `k`.
* No simultaneous-action recovery in this design; it is explicitly deferred.

The result is implementable, analyzable, and avoids ambiguous “who failed / who gets paid” cases until the language has the machinery to express them precisely.

----

Possible grammar file:
```
grammar Vegas;

// Top-level program consists of types, macros, and game definitions.
// 'main' is just a game convention, not a distinct grammar rule.
program : (typeDec | macroDec | gameDec)* EOF ;

// -------------------------------------------------------------------------
// Declarations
// -------------------------------------------------------------------------

typeDec : 'type' name=typeId '=' typeExp ;

macroDec
    : 'macro' name=varId
      '(' (params+=paramDec (',' params+=paramDec)*)? ')'
      ':' resultType=typeExp
      '=' body=exp
      ';'?
    ;

// Functional Game Definition
// Example: game Split[A, B | pool$2](amount: int) { ... }
// Example: game main() { ... }
gameDec
    : 'game' name=(varId | roleId)
      // Optional Configuration Block: Roles and Pool Weight
      ('[' (roles+=roleId (',' roles+=roleId)*)? ('|' 'pool' '$' weight=INT)? ']')?
      // Explicit Parameters (State)
      '(' (params+=paramDec (',' params+=paramDec)*)? ')'
      '{' ext '}'
    ;

paramDec
    : name=varId ':' type=typeExp
    ;

varDec 
    : name=varId ':' hidden='hidden'? type=typeExp
    ;

// -------------------------------------------------------------------------
// Control Flow & Actions (Extensions)
// -------------------------------------------------------------------------

ext 
    : kind=('join' | 'yield' | 'reveal' | 'random') query+ ';' ext   # ReceiveExt
    | 'withdraw' outcome                                             # WithdrawExt
    | tail=gameCall                                                  # TailCallExt
    ;

// A query (action) with optional recovery handler
// Example: yield Alice(x: int) || Refund(10);
query 
    : role=roleId ('(' (decls+=varDec (',' decls+=varDec)*)? ')')? 
      ('$' deposit=INT)? 
      ('where' cond=exp)? 
      ('||' recovery=gameCall)? 
    ;

// Game Transition / Call
// distinct from exp-level calls to allow UpperCase game names (e.g., Refund)
gameCall 
    : callee=(varId | roleId) '(' (args+=exp (',' args+=exp)*)? ')' 
    ;

// -------------------------------------------------------------------------
// Expressions & Types
// -------------------------------------------------------------------------

outcome
    : <assoc=right> cond=exp '?' ifTrue=outcome ':' ifFalse=outcome  # IfOutcome
    | 'let' dec=varDec '=' init=exp 'in' body=outcome                # LetOutcome
    | '(' outcome ')'                                                # ParenOutcome
    | '{' items+=item+ '}'                                           # OutcomeExp
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

typeExp
    : '{' vals+=INT (',' vals+=INT)* '}'   # SubsetTypeExp
    | '{' start=INT '..' end=INT '}'       # RangeTypeExp
    | name=typeId                          # IdTypeExp
    ;

// -------------------------------------------------------------------------
// Lexer
// -------------------------------------------------------------------------

typeId: LOWER_ID ;
varId : LOWER_ID ;
roleId: ROLE_ID ;

ROLE_ID: [A-Z][a-zA-Z_0-9]*;
LOWER_ID: [a-z][a-zA-Z_0-9]*;
INT: ([1-9][0-9]* | [0]) ;
ADDRESS: '0x'([1-9a-fA-F][0-9a-fA-F]* | [0]) ;
STRING: '"' ( ~('"'|'\\') )* '"' ;

BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\n]* -> skip ;
WS : [ \t\r\n]+ -> skip;
```

