


%LEXICAL ANALYSIS:
lexer(Tokens) -->
    white_space,
    (   ( ":=",     !, {Token = tokAssgn}
        ; ";",      !, {Token = tokSColon}
        ; "+",      !, {Token = tokPlus}
        ; "-",      !, {Token = tokMinus}
        ; "*",      !, {Token = tokTimes}
        ; "<>",     !, {Token = tokNeq}
        ; "<=",     !, {Token = tokLeq}
        ; "<",      !, {Token = tokLt}
        ; ">=",     !, {Token = tokGeq}
        ; ">",      !, {Token = tokGt}
        ; "=",      !, {Token = tokEq}
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
    [H], {code_type(H, alnum) ; H = '_'}, !,  alphanum(T).
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
    [tokProgram], [TokId], block(Block), {TokId = tokId(Id), AST = program(Id, _, Block)}.

block(Block) -->
    declarations(Decs), [tokBegin], complexInstr(ComplexInstr), [tokEnd],
    {Block = block(Decs, ComplexInstr)}.

declarations(Declarations) -->
    declaration(Declaration), !, declarations(Other),
    {append(Declaration, Other, Declarations)}.
declarations([]) -->
    [].

declaration(Vars) -->
    declarator(Vars), !.
declaration([Procedure]) -->
    procedure(Procedure).

declarator(Vars) -->
    [tokLocal], variables(Vars).

variables([Var|Others]) -->
    variable(Var), [tokComma], !, variables(Others).
variables([Var]) -->
    variable(Var).

variable(var(Var, _)) -->
    [TokId], {TokId = tokId(Var)}.

procedure(Procedure) -->
    [tokProcedure], [ProcName], [tokLParen], formalArgs(FormalArgs), [tokRParen], block(Block),
    {ProcName = tokId(Name), Procedure = procedure(Name, FormalArgs, Block)}.

formalArgs(FormalArgs) -->
    formalArgsSequence(FormalArgs), !.
formalArgs([]) -->
    [].

formalArgsSequence([Arg|Args]) -->
    formalArg(Arg), [tokComma], !, formalArgsSequence(Args).
formalArgsSequence([Arg]) -->
    formalArg(Arg), !.
formalArgsSequence([]) -->
    [].

formalArg(by_val(Var)) -->
    [tokValue], !, variable(Var).
formalArg(arg(Arg)) -->
    variable(Arg).

complexInstr(CmpInstr) -->
    instr(Instr), [tokSColon], !, complexInstr(Instrs),
    {CmpInstr = (Instr ';;' Instrs) }.
complexInstr(Instr) -->
    instr(Instr).

instr(Instr) -->
    (
    [tokIf], !, logicExpr(L_Expr), [tokThen], complexInstr(ThenPart),
        ( [tokFi], !, {Instr = if(L_Expr, ThenPart, emptyInstr)}
        ; [tokThen], complexInstr(ElsePart), {Instr = if(L_Expr, ThenPart, ElsePart)})
    ; [tokWhile], !, logicExpr(L_Expr), [tokDo], complexInstr(Body), [tokDone],
      {Instr = while(L_Expr, Body)}
    ; [tokCall], !, procCall(Proc),
      {Instr = Proc}
    ; [tokReturn], !, arith_expr(Expr),
      {Instr = return(Expr)}
    ; [tokRead], !, variable(Var),
      {Instr = read(Var)}
    ; [tokWrite], !, arith_expr(Expr),
      {Instr = write(Expr)}
    ; variable(Var),  [tokAssgn], arith_expr(Ar_Expr),
      {Instr = (Var := Ar_Expr)}
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
    ( procCall(X), !
    ; variable(X), !
    ; [tokNumber(Y)], {X = const(Y)}
    ).

procCall(X) -->
    [ProcName], {ProcName = tokId(Name)}, [tokLParen], realArgs(Args), [tokRParen],
    {X = call(Name, _, Args)}.

realArgs([Arg|Args]) -->
    realArg(Arg), [tokComma], !, realArgs(Args).
realArgs([Arg]) -->
    realArg(Arg), !.
realArgs([]) -->
    [].

realArg(Arg) -->
    arith_expr(Arg).

logicExpr(Bool) -->
    disjunct(Disjunct), logicExpr(Disjunct, Bool).

logicExpr(Acc, Bool) -->
    [tokOr], !, disjunct(Disjunct),
    {Acc1 =.. [or, Acc, Disjunct]},
    logicExpr(Acc1, Bool).
logicExpr(Acc, Acc) -->
    [].

disjunct(Disjunct) -->
    conjunct(Conjunct), disjunct(Conjunct, Disjunct).

disjunct(Acc, Disjunct) -->
    [tokAnd], !, conjunct(Conjunct),
    {Acc1 =.. [and, Acc, Conjunct]},
    disjunct(Acc1, Disjunct).
disjunct(Acc, Acc) -->
    [].

conjunct(Conjunct) -->
    ( [tokNot], !, relExpr(Expr), {Conjunct = not(Expr)}
    ; relExpr(Conjunct) ).

relExpr(Expr) -->
    ( arith_expr(LExpr), !, rel_op(Op), arith_expr(RExpr),
      {Expr =.. [Op, LExpr, RExpr]}
    ; [tokLParen], logicExpr(Expr), [tokRParen] ).

rel_op(<>) -->
    [tokNeq], !.
rel_op(<) -->
    [tokLt], !.
rel_op(<=) -->
    [tokLeq], !.
rel_op(>) -->
    [tokGt], !.
rel_op(>=) -->
    [tokGeq], !.
rel_op(=) -->
    [tokEq], !.

%VALIDATING SEMANTICS - NAMESPACES OF VARIABLES AND PROCEDURES
vArithExpr(Expr, Gamma) :-
    (OP = + ; OP = -; OP = *; OP = div; OP = mod),
    Expr =.. [OP, L, R], !,
    vArithExpr(L, Gamma),
    vArithExpr(R, Gamma).
vArithExpr(var(X, Path), Gamma) :-
    findVar(X, Gamma, Path). %HERE
vArithExpr(call(X, Path, Args), Gamma) :-
    length(Args, CountArgs),
    findCall(X, CountArgs, Gamma, Path), %HERE
    vArgs(Args, Gamma).
vArithExpr(const(_), _).

vLogicExpr(Expr, Gamma) :-
    (OP = and; OP = or; OP = not),
    Expr =.. [OP, L, R], !,
    vLogicExpr(L, Gamma),
    vLogicExpr(R, Gamma).
vLogicExpr(Expr, Gamma) :-
    (OP = <>; OP = <=; OP = <; OP = >; OP = >=; OP = (=)),
    Expr =.. [OP, L, R], !,
    vArithExpr(L, Gamma),
    vArithExpr(R, Gamma).

vArgs([], _).
vArgs([H|T], Gamma) :-
    vArithExpr(H, Gamma),
    vArgs(T, Gamma).

vInstr(if(Condition, Then, Else), Gamma) :-
    !,vLogicExpr(Condition, Gamma),
    vInstrs(Then, Gamma),
    vInstrs(Else, Gamma).
vInstr(while(Condition, Instrs), Gamma) :-
    !,vLogicExpr(Condition, Gamma),
    vInstrs(Instrs, Gamma).
vInstr(call(Name, Path, Args), Gamma) :-
    !,length(Args, CountArgs),
    findCall(Name, CountArgs, Gamma, Path), %HERE
    vArgs(Args, Gamma).
vInstr(return(Expr), Gamma) :-
    !,vArithExpr(Expr, Gamma).
vInstr(write(Expr), Gamma) :-
    !,vArithExpr(Expr, Gamma).
vInstr(read(var(X, Path)), Gamma) :-
    !,findVar(X, Gamma, Path). %HERE
vInstr(var(X, Path) := Expr, Gamma) :-
    !,findVar(X, Gamma, Path),
    vArithExpr(Expr, Gamma).
vInstr(emptyInstr, _).

vInstrs(Instr ';;' Instrs, Gamma) :-
    !, vInstr(Instr, Gamma),
    vInstrs(Instrs, Gamma).
vInstrs(Instr, Gamma) :-
    vInstr(Instr, Gamma).

vProcds([], Gamma, Gamma).
vProcds([procedure(Name, Args,block(Decs, Instrs))| T], Gamma, NewGamma) :-
    length(Args, CountArgs),
    countVars(Decs, CountVars),
    append(Args, [rec(Name, CountArgs, CountVars)|Gamma], TmpGamma),
    vBlock(block(Decs, Instrs), TmpGamma),
    vProcds(T, [proc(Name, CountArgs, CountVars)|Gamma], NewGamma).

vBlock(block(Decs, Instrs), Gamma) :-
    vDecs(Decs, Gamma, NewGamma),
    vInstrs(Instrs, NewGamma).

vDecs([], Gamma, Gamma).
vDecs([procedure(Name, Args, Block) | T], Gamma, NewGamma) :-
    !,length(Args, CountArgs),
    Block =.. [block, Decs, _],
    countVars(Decs, CountVars),
    append(Args, [rec(Name, CountArgs, CountVars) | Gamma], TmpGamma),
    vBlock(Block, TmpGamma),
    vDecs(T, [proc(Name, CountArgs, CountVars)|Gamma], NewGamma).
vDecs([var(X, _) | T], Gamma, NewGamma) :-
    vDecs(T, [var(X, _) | Gamma], NewGamma).

vProgram(program(_, CountVars, Block)) :-
    Block =.. [block, Decs, _],
    countVars(Decs, CountVars),
    vBlock(Block, []).

findVar(X, [var(X, _) | T], Nr) :- !, findVarNumber(T, 1, Nr).
findVar(X, [var(_, _) | T], Path) :-
    !, findVar(X, T, Path).
findVar(X, [arg(var(X, _))| T], arg(Nr)) :-
     !, findArgNumber(T, 1, Nr).
findVar(X, [arg(var(_, _))|T], Path) :-
    !, findVar(X, T, Path).
findVar(X, [proc(_,_,_) | T], Path) :-
    !,findVar(X, T, Path).
findVar(X, [rec(_,_,_) | T], up(Path)) :-
    !,findVar(X, T, Path).

findVarNumber([], Acc, Acc) :- !.
findVarNumber([arg(_)|_],Acc, Acc) :- !.
findVarNumber([rec(_,_,_) | _], Acc, Acc) :- !.
findVarNumber([_|T], Acc, Nr) :-
    !, NewAcc is Acc+1,
    findVarNumber(T, NewAcc, Nr).

findArgNumber([], Acc, Acc) :- !.
findArgNumber([rec(_,_,_) | _], Acc, Acc) :- !.
findArgNumber([_|T], Acc, Nr) :-
    !, NewAcc is Acc+1,
    findArgNumber(T, NewAcc, Nr).

findCall(X, CountArgs, [proc(X, CountArgs, CountVars) | _], proc(X, CountArgs, CountVars)) :- !.
findCall(X, CountArgs, [rec(X, CountArgs, CountVars)| _], rec(X, CountArgs, CountVars)) :- !.
findCall(X, CountArgs, [rec(_,_,_)| T], upcall(Path)) :-
    !,findCall(X, CountArgs, T, Path).
findCall(X, CountArgs, [_|T], Path) :-
    findCall(X, CountArgs, T, Path).

%how many variables has procedure?
countVars([], Acc, Acc).
countVars([var(_,_) | T], Acc, CVars) :-
    !, NewAcc is Acc+1,
    countVars(T, NewAcc, CVars).
countVars([_|T], Acc, CVars) :-
    countVars(T, Acc, CVars).
countVars(DecList, CVars) :-
    countVars(DecList, 0, CVars).

%TRANSLATING - FIRST STAGE:

tProc(procedure(Name, _, block(Decs, Instrs)), Code, ProcMap, [(Name, X) | ProcMap]) :-
    tInstrs(Instrs, InstrsCode, [(Name, X) | ProcMap]),
    tDecs(Decs, DecsCode, [(Name, X) | ProcMap]),
    append([label(X) | InstrsCode], DecsCode, Code).



tInstrs(Instr ';;' OtherInstrs, Code, ProcMap) :-
    !, tInstr(Instr, Code1, ProcMap),
    append(Code1, Code2, Code),
    tInstrs(OtherInstrs, Code2, ProcMap).
tInstrs(Instr, Code, ProcMap) :-
    tInstr(Instr, Code, ProcMap).

tInstr(emptyInstr, [], _) :- !.
tInstr(if(Condition, ThenPart, ElsePart), Code, ProcMap) :-
    !, tLogicExpr(Condition, Code1, ProcMap),
    tInstrs(ThenPart, CodeThen, ProcMap),
    tInstrs(ElsePart, CodeElse, ProcMap),
    append(Code1, [branchz(X) | CodeThen], TmpCode),
    append(TmpCode, [label(X) | CodeElse], Code).
tInstr(while(Condition, Instrs), Code, ProcMap) :-
    !, tLogicExpr(Condition, CodeCondition, ProcMap),
    tInstrs(Instrs, CodeInstrs, ProcMap),
    append([label(X)], CodeCondition, TmpCode),
    append(TmpCode, [branchz(End)|CodeInstrs], CodeTmp2),
    Code = [jump(X), label(End) | CodeTmp2].
tInstr(call(Name, Path, Args), Code, ProcMap) :-
    !, tCall(call(Name, Path, Args), ProcMap, Code).
tInstr(return(Expr), Code, ProcMap) :-
    !, tArithExpr(Expr, ExprCode, ProcMap),
    ReturnCode = [
                  swapd,
                  const(0xFFFF),
                  swapa,
                  swapd,
                  store,
                  const(0xFFFD),
                  swapa,
                  load,
                  swapd,
                  const(1),
                  add,
                  swapa,
                  load,
                  swapd,
                  swapa,
                  const(0xFFFE),
                  swapa,
                  swapd,
                  store,
                  const(2),
                  add,
                  swapa,
                  load,
                  swapa,
                  const(0xFFFD),
                  swapa,
                  store,
                  swapd,
                  swapa,
                  load,
                  swapd,
                  const(0xFFFF),
                  swapa,
                  load,
                  swapd,
                  store,
                  swapd,
                  push,
                  const(0xFFFF),
                  swapa,
                  load,
                  jump],
    append(ExprCode, ReturnCode, Code).
tInstr(write(Expr), Code, ProcMap) :-
    !, tArithExpr(Expr, ExprCode, ProcMap),
    append(ExprCode, [swapd, const(2), syscall], Code).


tArithExpr(Expr, Code, ProcMap) :-
    ( OP = +, INSTR = add
    ; OP = -, INSTR = sub
    ; OP = *, INSTR = mult
    ; OP = div, INSTR = div),
    Expr =.. [OP, L, R], !,
    tArithExpr(L, CL, ProcMap),
    tArithExpr(R, CR, ProcMap),
    append(CL, [push | CR], TmpC),
    append(TmpC, [swapd, top, INSTR], Code).
tArithExpr(const(X), [const(X)], _).

tCall(upcall(X), Addr, SLCode, Code) :-
    !, append(SLCode, [swapd, const(0x003), add, swapa, load], NewSLCode),
    tCall(X, Addr, NewSLCode, Code).
tCall(proc(_, ArgsCount, VarCount), Addr, SLCode, Code) :-
    CodeTmp = [const(X),
             push,
             const(0xFFFE),
             swapa,
             load,
             swapd,
             const(ArgsCount),
             swapd,
             sub,
             push,
             const(0xFFFD),
             swapa,
             load,
             push,
             const(0xFFFD),
             swapa,
             load],
    append(CodeTmp, SLCode, CodeTmp2),
    CodeTmp3 = [push,
                const(0xFFFE),
                swapa,
                load,
                swapd,
                const(0xFFFD),
                swapa,
                const(0x0003),
                swapd,
                sub,
                store,
                const(0xFFFE),
                swapa,
                load,
                swapd,
                const(VarCount),
                add,
                store,
                jump(Addr),
                label(X)
               ],
    append(CodeTmp2, CodeTmp3, Code).

tCall(call(Name, Path, Args), ProcMap, Code) :-
    tArgs(Args, ArgsCode),
    findAddr(ProcMap, Name, Addr),
    tCall(Path, Addr, [], CallCode),
    append(ArgsCode, CallCode, Code).

tArgs(_, [argsCode]).

findAddr([(Name, Addr) | _ ], Name, Addr) :- !.
findAddr([_ | T], Name, Addr) :-
    findAddr(T, Name, Addr).



%TESTING: reading code from file
test(Filename, AST) :-
    open(Filename, read, Str),
    readProgram(Str, Program),
    phrase(lexer(TokList), Program),
    phrase(program(AST), TokList),
    vProgram(AST),
    close(Str).

readProgram(In, []) :-
    at_end_of_stream(In), !.
readProgram(In, [Char|Prog]) :-
    get_code(In, Char),
    readProgram(In, Prog).

writeCode([]).
writeCode([H|T]) :-
    write(H), nl, writeCode(T).
