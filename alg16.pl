


%LEXICAL ANALYSIS:
lexer(Tokens) -->
    white_space,
    (   ( ":=",     !, {Token = tokAssgn}
        ; ";",      !, {Token = tokSColon}
        ; "+",      !, {Token = tokPlus}
        ; "-",      !, {Token = tokMinus}
        ; "*",      !, {Token = tokTimes}
        ; "<",      !, {Token = tokLt}
        ; "<=",     !, {Token = tokLeq}
        ; ">",      !, {Token = tokGt}
        ; ">=",     !, {Token = tokGeq}
        ; "=",      !, {Token = tokEq}
        ; "<>",     !, {Token = tokNeq}
        ; ":=",     !, {Token = tokAssgn}
        ; ",",      !, {Token = tokComma}
        ; "(",      !, {Token = tokLParen}
        ; ")",      !, {Token = tokRParen}
        ; digit(FirstDigit), !, number(FirstDigit,N), {Token = tokNumber(N)}
        ; letter(FirstLetter), !, identifier(FirstLetter, Id),
            {member((Id, Token), [(and, tokAnd),
                                 (begin, tokBegin),
                                 (call, tokCall),
                                 (div, tokDiv),
                                 (do, tokDo),
                                 (done, tokDone),
                                 (else, tokElse),
                                 (end, tokEnd),
                                 (fi, tokFi),
                                 (if, tokIf),
                                 (local, tokLocal),
                                 (mod, tokMod),
                                 (not, tokNot),
                                 (or, tokOr),
                                 (procedure, tokProcedure),
                                 (program, tokProgram),
                                 (read, tokRead),
                                 (return, tokReturn),
                                 (then, tokThen),
                                 (value, tokValue),
                                 (while, tokWhile),
                                 (write, tokWrite)]),
            !
            ; Token = tokId(Id)
          }
        ; [_], {Token = tokenUnknow}
      ),
      !, {Tokens = [Token | TokList] },
      lexer(TokList)
; [], {Tokens = []}
).

comment -->
    "*)", !.
comment -->
    [_], comment, !.

white_space -->
    [Char], {code_type(Char, space)}, !, white_space.
white_space -->
    "(*", comment, white_space, !.
white_space -->
    [].

digit(D) -->
    [D], {code_type(D, digit)}.

digits([H|T]) --> digit(H), !, digits(T).
digits([]) --> [].

number(FirstDigit, X) -->
    digits(Ds), {number_chars(X, [FirstDigit|Ds])}.

letter(X) -->
    [X], {code_type(X, alpha)}.

alphanum([H|T]) -->
    [H], {code_type(H, alnum)}, !,  alphanum(T).
alphanum([]) -->
    [].

identifier(FirstLetter, Id) -->
    alphanum(As),
    {atom_codes(Id, [FirstLetter|As])}.


%SYNTAX ANALYSIS:

:-op(990, xfy, ';;').
:-op(900, xfy, :=).
:-op(820, xfy, and).
:-op(840, xfy, or).
:-op(700, xfy, <=).
:-op(700, xfy, <>).

program(AST) -->
    [tokProgram], [TokId], block(Block), {TokId = tokId(Id), AST = program(Id, Block)}.

block(Block) -->
    declarations(Declarations), [tokBegin], complexInstr(ComplexInstr), [tokEnd],
    {Block = block(Declarations, ComplexInstr)}.

declarations(Declarations) -->
    declaration(Declaration), !, declarations(Other),
    {append(Declaration, Other, Declarations)}.
declarations([]) -->
    [].

declaration(Vars) -->
    declarator(Vars), !.
declaration(Procedure) -->
    procedure(Procedure).

declarator(Vars) -->
    [tokLocal], variables(Vars).

variables([Var|Others]) -->
    variable(Var), [tokComma], !, variables(Others).
variables([Var]) -->
    variable(Var).

variable(var(Var)) -->
    [TokId], {TokId = tokId(Var)}.

procedure(Procedure) -->
    [tokProcedure], [ProcName], [tokLParen], formalArgs(FormalArgs), [tokRParen], block(Block),
    {ProcName = tokId(Name), Procedure = procedure(Name, FormalArgs, Block)}.

formalArgs(FormalArgs) -->
    formalArgsSequence(FormalArgs), !.
formalArgs([]) -->
    [].

formalArgsSequence([arg(Arg)|Args]) -->
    formalArg(Arg), [tokComma], !, formalArgsSequence(Args).
formalArgsSequence([]) -->
    [].

formalArg(by_val(Var)) -->
    [tokValue], !, variable(Var).
formalArg(Arg) -->
    variable(Arg).

complexInstr(CmpInstr) -->
    instr(Instr), [tokSColon], !, complexInstr(Instrs),
    {CmpInstr = (Instr ';;' Instrs) }.
complexInstr(Instr) -->
    instr(Instr).

instr(Instr) -->
    ( variable(Var), !, [tokAssgn], arith_expr(Ar_Expr),
      {Instr = (Var := Ar_Expr)}
    ; [tokIf], logicExpr(L_Expr), [tokThen], complexInstr(ThenPart), [tokFi], !,
      {Instr = if(L_Expr, ThenPart, emptyInstr)}
    ; [tokIf], logicExpr(L_Expr), [tokThen], complexInstr(ThenPart), [tokElse], complexInstr(ElsePart), [tokFi],
      {Instr = if(L_Expr, ThenPart, ElsePart)}
    ; [tokWhile], !, logicExpr(L_Expr), [tokDo], complexInstr(Body), [tokDone],
      {Instr = while(L_Expr, Body)}
    ; [tokCall], !, procCall(Proc),
      {Instr = Proc}
    ; [tokReturn], !, arith_expr(Expr),
      {Instr = return(Expr)}
    ; [tokRead], !, variable(Var),
      {Instr = read(Var)}
    ; [tokWrite], arith_expr(Expr),
      {Instr = write(Expr)}
    ).

arith_expr(Expr) -->
    summand(Summand), arith_expr(Summand, Expr).

arith_expr(Acc, Expr) -->
    additive_op(Op), !, summand(Summand),
    {Acc1 =.. [Op, Acc, Summand]}, arith_expr(Acc1, Expr).
arith_expr(Acc, Acc) -->
    [].

additive_op(+) -->
    [tokPlus], !.
additive_op(-) -->
    [tokMinus].

summand(Expr) -->
    factor(Factor), summand(Factor, Expr).

summand(Acc, Expr) -->
    multiplicative_op(Op), !, factor(Factor),
    {Acc1 =.. [Op, Acc, Factor]}, summand(Acc1, Expr).
summand(Acc, Acc) -->
    [].

multiplicative_op(*) -->
    [tokTimes], !.
multiplicative_op(div) -->
    [tokDiv], !.
multiplicative_op(mod) -->
    [tokMod], !.

factor(Expr) -->
    ( [tokMinus], !, simple_expr(SExpr), {Expr = -SExpr}
    ; simple_expr(Expr)).

simple_expr(Expr) -->
    [tokLParen], !, arith_expr(Expr), [tokRParen].
simple_expr(Expr) -->
    atom_expr(Expr).

atom_expr(X) -->
    ( variable(X), !
    ; procCall(X), !
    ; [tokNumber(Y)], {X = const(Y)}
    ).

procCall(X) -->
    [ProcName], {ProcName = tokId(Name)}, [tokLParen], realArgs(Args), [tokRParen],
    {X = callProc(Name, Args)}.



%TESTING: reading code from file
test(Filename, Program) :-
    open(Filename, read, Str),
    readProgram(Str, Program),
    write(Program), nl,
    close(Str).

readProgram(In, []) :-
    at_end_of_stream(In), !.
readProgram(In, [Char|Prog]) :-
    get_code(In, Char),
    readProgram(In, Prog).
