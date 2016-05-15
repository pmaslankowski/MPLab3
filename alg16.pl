%Kompilator języka Algol 16
%Autor: Piotr Maślankowski
%Zaimplementowana wersja języka: bez przekazywania parametrów przez nazwę.
% (tzn. kompilator obsługuje zagnieżdżone procedury)



%Informacja:
%Parser i lekser na podstawie parsera języka While zamieszczonego na KNO

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
    [H], {code_type(H, alnum), ! ; char_code('_', H), ! ; char_code('''', H), !},  alphanum(T).
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

appInstr(I1 ';;' I2, Instr2, I1 ';;' X) :-
  !, appInstr(I2, Instr2, X).
appInstr(Instr1, Instr2, Instr1 ';;' Instr2) :- !.

program(AST) -->
    [tokProgram], [TokId], startblock(Block), {TokId = tokId(Id), AST = program(Id, _, Block)}.

startblock(Block) -->
    declarations(Decs), [tokBegin], complexInstr(ComplexInstr), [tokEnd],
    {Block = block(Decs, ComplexInstr)}.

block(Block) -->
    declarations(Decs), [tokBegin], complexInstr(ComplexInstrTmp), [tokEnd],
    {appInstr(ComplexInstrTmp, return(const(0)), ComplexInstr), Block = block(Decs, ComplexInstr)}.

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

formalArg(arg(Var)) -->
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
        ; [tokElse], complexInstr(ElsePart), {Instr = if(L_Expr, ThenPart, ElsePart)}, [tokFi])
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
    ( arith_expr(LExpr), rel_op(Op), !, arith_expr(RExpr),
      {Expr =.. [Op, LExpr, RExpr]}
    ; [tokLParen], !, logicExpr(Expr), [tokRParen] ).
relExpr(Expr) -->
  arith_expr(LExpr), [tokLeq], !, arith_expr(RExpr),
  {Expr = not(LExpr > RExpr)}.
relExpr(Expr) -->
  arith_expr(LExpr), [tokGeq], !, arith_expr(RExpr),
  {Expr = not(LExpr < RExpr)}.

rel_op(<>) -->
    [tokNeq], !.
rel_op(<) -->
    [tokLt], !.
rel_op(>) -->
    [tokGt], !.
rel_op(=) -->
    [tokEq], !.


%Validating namespaces:

vArithExpr(Expr, Gamma) :-
    (OP = + ; OP = -; OP = *; OP = div; OP = mod),
    Expr =.. [OP, L, R], !,
    vArithExpr(L, Gamma),
    vArithExpr(R, Gamma).
vArithExpr(Expr, Gamma) :-
    Expr =.. [-, X], !,
    vArithExpr(X, Gamma).
vArithExpr(var(X, Path), Gamma) :-
    findVar(X, Gamma, Path).
vArithExpr(call(X, Path, Args), Gamma) :-
    length(Args, CountArgs),
    findCall(X, CountArgs, Gamma, Path),
    vArgs(Args, Gamma).
vArithExpr(const(_), _).

vLogicExpr(Expr, Gamma) :-
    (OP = and; OP = or),
    Expr =.. [OP, L, R], !,
    vLogicExpr(L, Gamma),
    vLogicExpr(R, Gamma).
vLogicExpr(not(X), Gamma) :-
  !, vLogicExpr(X, Gamma).
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
    findCall(Name, CountArgs, Gamma, Path),
    vArgs(Args, Gamma).
vInstr(return(Expr), Gamma) :-
    !,vArithExpr(Expr, Gamma).
vInstr(write(Expr), Gamma) :-
    !,vArithExpr(Expr, Gamma).
vInstr(read(var(X, Path)), Gamma) :-
    !,findVar(X, Gamma, Path).
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
    reverse(Args, RArgs),
    append(RArgs, [rec(Name, CountArgs, CountVars)|Gamma], TmpGamma),
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
    reverse(Args, RArgs),
    append(RArgs, [rec(Name, CountArgs, CountVars) | Gamma], TmpGamma),
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
findVarNumber([proc(_,_,_) | T], Acc, Nr) :-
    !,findVarNumber(T, Acc, Nr).
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

%Translating to extended assembler - we added const(Value) and label(Name) instructions.
%We introduce 4th register - at 0xFFFF
%We hold stack pointer at 0xFFFE and frame pointer at 0xFFFD


%Activation record:
%   Arguments...
%   Return pointer    <- Frame pointer points here.
%   Old stack pointer
%   Old frame pointer
%   Static link
%   Local variables...
%Stack is in the end of memory

%ProcMap contains addresses of all visible functions
tProgram(program(_, VarCount, block(Decs, Instrs)), Code) :-
    tDecs(Decs, DecsCode, [], ProcMap),
    tInstrs(Instrs, InstrsCode, ProcMap),
    StartSP is 0xFFFE - 5 - VarCount - 1,
    append([const(0xFFFE), %creating AR of program
            swapa,
            const(StartSP),
            store,
            const(0xFFFD),
            swapa,
            const(0xFFFC),
            store,
            const(0xFFF9),
            swapa,
            const(0xFFFC),
            store,
            const(Start), jump | DecsCode], [label(Start) | InstrsCode], TmpCode),
    append(TmpCode, [const(0), syscall], Code).

tProc(procedure(Name, _, block(Decs, Instrs)), Code, ProcMap, [(Name, X) | ProcMap]) :-
    tDecs(Decs, DecsCode, [(Name, X) | ProcMap], TmpProcMap),
    tInstrs(Instrs, InstrsCode, TmpProcMap),
    append([label(X) | InstrsCode], DecsCode, Code).

tDecs([], CodeAcc, CodeAcc, ProcMap, ProcMap).
tDecs([procedure(Name, _, block(Decs, Instrs)) | T], CodeAcc, Code, ProcMap, NewProcMap) :-
    !, tProc(procedure(Name, _, block(Decs, Instrs)), ProcCode, ProcMap, [(Name, X) | _]),
    append(CodeAcc, ProcCode, NewAccCode),
    tDecs(T, NewAccCode, Code, [(Name, X) | ProcMap], NewProcMap).
tDecs([_|T], CodeAcc, Code, ProcMap, NewProcMap) :-
    tDecs(T, CodeAcc, Code, ProcMap, NewProcMap).
tDecs(Decs, Code, ProcMap, NewProcMap) :-
  tDecs(Decs, [], Code, ProcMap, NewProcMap).

tInstrs(return(X) ';;' _, Code, ProcMap) :-
  !, tInstr(return(X), Code, ProcMap).
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
    append(CodeThen, [const(Y), jump], CodeThen2),
    append(CodeElse, [label(Y)], CodeElse2),
    append(Code1, [const(0xFFFE),
                   swapa,
                   load,
                   swapd,
                   const(1),
                   swapd,
                   add,
                   store,
                   swapa,
                   load,
                   swapa,
                   const(X),
                   swapa,
                   branchz | CodeThen2], TmpCode),
    append(TmpCode, [label(X) | CodeElse2], Code).
tInstr(while(Condition, Instrs), Code, ProcMap) :-
    !, tLogicExpr(Condition, CodeCondition, ProcMap),
    tInstrs(Instrs, CodeInstrs, ProcMap),
    append([label(X)], CodeCondition, TmpCode),
    append(CodeInstrs, [const(X), jump, label(End)], InstrsCode),
    append(TmpCode, [const(0xFFFE),
                     swapa,
                     load,
                     swapd,
                     const(1),
                     swapd,
                     add,
                     store,
                     swapa,
                     load,
                     swapa,
                     const(End),
                     swapa,
                     branchz|InstrsCode], Code).
tInstr(call(Name, Path, Args), Code, ProcMap) :-
    !, tCall(call(Name, Path, Args), ProcMap, TmpCode),
    append(TmpCode, [ const(0xFFFE),
                      swapa,
                      load,
                      swapd,
                      const(1),
                      add,
                      store], Code).
tInstr(return(Expr), Code, ProcMap) :-
    !, tArithExpr(Expr, ExprCode, ProcMap),
    ReturnCode = [const(0xFFFE), %get the result from stack
                  swapa,
                  load,
                  swapd,
                  const(1),
                  swapd,
                  add,
                  store,
                  swapa,
                  load,
                  swapd,           %result->DR
                  const(0xFFFF),
                  swapa,
                  swapd,
                  store,          %wynik -> 3R
                  const(0xFFFD),
                  swapa,
                  load,
                  swapd,
                  const(1),
                  swapd,
                  sub,
                  swapa,
                  load,
                  swapd,
                  swapa,
                  const(0xFFFE),
                  swapa,
                  swapd,
                  store,        %SP := OSP
                  const(0xFFFD),
                  swapa,
                  load,
                  swapd,
                  const(2),
                  swapd,
                  sub,
                  swapa,
                  load,
                  swapa,
                  const(0xFFFD),
                  swapa,
                  swapd,
                  load,
                  swapd,
                  store, % FP := OFP
                  swapd,
                  swapa,
                  load,
                  swapd,
                  const(0xFFFF),
                  swapa,
                  load,
                  swapd,
                  store,      %RP -> 3R
                  const(0xFFFE), %start of pushing result
                  swapa,
                  load,
                  swapa,
                  swapd,
                  store,
                  const(1),
                  swapd,
                  swapa,
                  sub,
                  store, %push end
                  const(0xFFFF),
                  swapa,
                  load,
                  jump],   %jump to RP
    append(ExprCode, ReturnCode, Code).
tInstr(write(Expr), Code, ProcMap) :-
    !, tArithExpr(Expr, ExprCode, ProcMap),
    append(ExprCode, [const(0xFFFE),
                      swapa,
                      load,
                      swapd,
                      const(1),
                      add,
                      store,
                      swapa,
                      load,
                      swapd,
                      const(2),
                      syscall], Code).
tInstr(read(var(_, Path)), Code, _) :-
    !, getVarAddr(Path, CodeAddr),
    append(CodeAddr, [swapa, const(1), syscall, store], Code).
tInstr(var(_, Path) := Expr, Code, ProcMap) :-
    !, tArithExpr(Expr, ExprCode, ProcMap),
    getVarAddr(Path, CodeAddr),
    append(ExprCode, CodeAddr, TmpCode),
    append(TmpCode, [ swapa,
                      const(0xFFFF),
                      swapa,
                      store, %addr to 4R
                      const(0xFFFE),
                      swapa,
                      load,
                      swapd,
                      const(1),
                      swapd,
                      add,
                      store,
                      swapa,
                      load, %get result from stack
                      swapd,
                      const(0xFFFF),
                      swapa,
                      load,
                      swapa,
                      swapd,
                      store], Code).

tArithExpr(call(_, Path, Args), Code, ProcMap) :-
    !, tCall(call(_, Path, Args), ProcMap, Code).
tArithExpr(Expr, Code, ProcMap) :-
    ( OP = +, INSTR = add
    ; OP = -, INSTR = sub
    ; OP = *, INSTR = mult
    ; OP = div, INSTR = div),
    Expr =.. [OP, L, R], !,
    tArithExpr(L, CL, ProcMap),
    tArithExpr(R, CR, ProcMap),
    append(CL, CR, TmpC), %push end
    append(TmpC, [const(0xFFFE),
                  swapa,
                  load,
                  swapd,
                  const(1),
                  swapd,
                  add,
                  store,
                  swapa,
                  load,
                  swapa,
                  add,
                  swapa,
                  swapd,
                  load,
                  INSTR,
                  store], Code).
tArithExpr(Expr, Code, ProcMap) :-
  Expr =.. [-, X], !,
  tArithExpr(X, XCode, ProcMap),
  append(XCode, [const(0xFFFE),
                 swapa,
                 load,
                 swapd,
                 const(1),
                 swapd,
                 add,
                 swapa,
                 load,
                 swapd,
                 const(0xFFFF),
                 swapd,
                 mult,
                 store], Code).
tArithExpr(Expr, Code, ProcMap) :-
  Expr =.. [mod, L, R], !,
  tArithExpr(L, CL, ProcMap),
  tArithExpr(R, CR, ProcMap),
  append(CL, CR, TmpC),
  append(TmpC, [const(0xFFFE),
                swapa,
                load,
                swapd,
                const(1),
                swapd,
                add,
                store,
                swapa,
                load,
                swapa,
                add,
                swapa,
                swapd,
                load,
                div,
                const(0xfff0),
                swapd,
                shift,
                store], Code).

tArithExpr(const(X), Code, _) :-
    !, Code = [
            const(X),
            swapd, %push start
            const(0xFFFE),
            swapa,
            load,
            swapa,
            swapd,
            store,
            const(1),
            swapd,
            swapa,
            sub,
            store]. %push end
tArithExpr(var(_, Path), Code, _) :-
    !,getVarAddr(Path, VarCode),
    append(VarCode, [swapa,
                     load,
                     swapd, %push start
                     const(0xFFFE),
                     swapa,
                     load,
                     swapa,
                     swapd,
                     store,
                     const(1),
                     swapd,
                     swapa,
                     sub,
                     store %push end
                     ], Code).


parseLogicExpr(not(X), nand(XParsed, XParsed)) :-
    !, parseLogicExpr(X, XParsed).
parseLogicExpr(L or R, nand(nand(LExpr, LExpr), nand(RExpr, RExpr))) :-
    !, parseLogicExpr(L, LExpr),
    parseLogicExpr(R, RExpr).
parseLogicExpr(L and R, nand(nand(LExpr, RExpr), nand(LExpr, RExpr))) :-
    !, parseLogicExpr(L, LExpr),
    parseLogicExpr(R, RExpr).
parseLogicExpr(X, X) :- !.

tLogicExpr(Expr, Code, ProcMap) :-
    parseLogicExpr(Expr, PExpr),
    tLogicExpr_(PExpr, Code, ProcMap).

tLogicExpr_(nand(L, R), Code, ProcMap) :-
    !, tLogicExpr_(L, LCode, ProcMap),
    tLogicExpr_(R, RCode, ProcMap),
    append(LCode, RCode, TmpCode),
    append(TmpCode, [const(0xFFFE),
                  swapa,
                  load,
                  swapd,
                  const(1),
                  swapd,
                  add,
                  store,
                  swapa,
                  load,
                  swapa,
                  add,
                  swapa,
                  swapd,
                  load,
                  nand,
                  store], Code).
tLogicExpr_(Expr, Code, ProcMap) :-
    Expr =.. [Op, L, R],
    tArithExpr(L, LCode, ProcMap),
    tArithExpr(R, RCode, ProcMap),
    append(LCode, RCode, TmpCode),
    append(TmpCode, [const(0xFFFE),
                     swapa,
                     load,
                     swapd,
                     const(1),
                     swapd,
                     add,
                     store,
                     swapa,
                     load,
                     swapa,
                     add,
                     swapa,
                     swapd,
                     load], TmpCode1),
    ( Op = <, !, NextCode = [swapa,
                             const(0xFFFF),
                             swapa,
                             store,
                             swapa,
                             const(1),
                             swapd,
                             swapa,
                             shift,
                             const(0xFFFF),
                             swapa,
                             swapd,
                             load,
                             sub,
                             swapa,
                             const(TrueLab),
                             swapa,
                             swapd,
                             const(0xFFFF),
                             swapd,
                             shift,
                             branchn]
    ; Op = >, !, NextCode = [swapd,
                             swapa,
                             const(0xFFFF),
                             swapa,
                             store,
                             swapa,
                             const(1),
                             swapd,
                             swapa,
                             shift,
                             const(0xFFFF),
                             swapa,
                             swapd,
                             load,
                             sub,
                             swapa,
                             const(TrueLab),
                             swapa,
                             swapd,
                             const(0xFFFF),
                             swapd,
                             shift,
                             branchn]
    ; Op = =, !, NextCode = [sub, swapa, const(TrueLab), swapa, branchz]
    ; Op = <>, !, NextCode = [sub, swapa, const(TrueLab), swapa, branchn, swapd, const(0xFFFF), mult, branchn]
    ),
    append(TmpCode1, NextCode, TmpCode2),
    append(TmpCode2,[const(0xFFFE),
                     swapa,
                     load,
                     swapd,
                     const(1),
                     swapd,
                     add,
                     swapa,
                     const(0),
                     store,
                     const(EndLab),
                     jump,
                     label(TrueLab),
                     const(0xFFFE),
                     swapa,
                     load,
                     swapd,
                     const(1),
                     swapd,
                     add,
                     swapa,
                     const(0xFFFF),
                     store,
                     label(EndLab) ], Code).

getVarAddr(X, Acc, Code) :-
    integer(X), !,
    Offset is X + 3,
    append(Acc, [swapd, const(Offset), swapd, sub], Code).
getVarAddr(arg(X), Acc, Code) :-
  !, append(Acc, [swapd, const(X), swapd, add], Code).
getVarAddr(up(X), Acc, Code) :-
    append(Acc, [swapd, const(3), swapd, sub, swapa, load], NewAcc),
    getVarAddr(X, NewAcc, Code).
getVarAddr(X, Code) :-
    append([const(0xFFFD), swapa, load], Code1, Code),
    getVarAddr(X, [], Code1).


tCall(upcall(X), Addr, SLCode, Code) :-
    !, append(SLCode, [swapd, const(3), swapd, sub, swapa, load], NewSLCode),
    tCall(X, Addr, NewSLCode, Code).
tCall(Something, Addr, SLCode, Code) :-
    (Something = proc(_, ArgsCount, VarCount) ; Something = rec(_, ArgsCount, VarCount)), !,
    ArgsCount2 is ArgsCount + 1,
    CodeTmp = [const(X),
             swapd, %push start
             const(0xFFFE),
             swapa,
             load,
             swapa,
             swapd,
             store,
             const(1),
             swapd,
             swapa,
             sub,
             store, %push end
             const(0xFFFE),
             swapa,
             load,
             swapd,
             const(ArgsCount2),
             swapd,
             add,
             swapd, %push start
             const(0xFFFE),
             swapa,
             load,
             swapa,
             swapd,
             store,
             const(1),
             swapd,
             swapa,
             sub,
             store, %push end,
             const(0xFFFD),
             swapa,
             load,
             swapd, %push start
             const(0xFFFE),
             swapa,
             load,
             swapa,
             swapd,
             store,
             const(1),
             swapd,
             swapa,
             sub,
             store, %push end,
             const(0xFFFD),
             swapa,
             load,
             swapd,
             const(3),
             swapd,
             sub,
             swapa,
             load],
    append(CodeTmp, SLCode, CodeTmp2),
    CodeTmp3 = [swapd, %push start
                const(0xFFFE),
                swapa,
                load,
                swapa,
                swapd,
                store,
                const(1),
                swapd,
                swapa,
                sub,
                store, %push end,
                const(0xFFFE),
                swapa,
                load,
                swapd,
                const(0xFFFD),
                swapa,
                const(4),
                swapd,
                add,
                store,
                const(0xFFFE),
                swapa,
                load,
                swapd,
                const(VarCount),
                swapd,
                sub,
                store,
                const(Addr),
                jump,
                label(X)
               ],
    append(CodeTmp2, CodeTmp3, Code).

tCall(call(Name, Path, Args), ProcMap, Code) :-
    tArgs(Args, ArgsCode, ProcMap),
    findAddr(ProcMap, Name, Addr),
    write(ProcMap),
    tCall(Path, Addr, [], CallCode),
    append(ArgsCode, CallCode, Code).

tArgs([], Acc, Acc, _).
tArgs([H|T], Acc, ArgsCode, ProcMap) :-
    tArithExpr(H, ArgCode, ProcMap),
    append(ArgCode, Acc, NewAcc),
    tArgs(T, NewAcc, ArgsCode, ProcMap).
tArgs(Args, Code, ProcMap) :-
  tArgs(Args, [], Code, ProcMap).

findAddr([(Name, Addr) | _ ], Name, Addr) :- !.
findAddr([_ | T], Name, Addr) :-
    findAddr(T, Name, Addr).


%FINAL TRANSLATION:
translate([const(Val) | T], X, 0, CurrWord, OrderCount, AssemblyCode) :-
    !, append([CurrWord | X], OtherAsm, AssemblyCode),
    length(X, XLen),
    NewOrderCount is OrderCount + 1 + XLen,
    translate(T, [Val], 1, 9, NewOrderCount, OtherAsm). %CONST CODE = 9
translate([const(Val) | T], X, Nr, CurrWord, OrderCount, AssemblyCode) :-
    !, NewNr is (Nr + 1) mod 4,
    NewCurrWord is 16 * CurrWord + 9, %CONST CODE = 9
    append(X, [Val], NewX),
    translate(T, NewX, NewNr, NewCurrWord, OrderCount, AssemblyCode).
translate([label(Val), NextOrder | T], X, Nr, CurrWord, OrderCount, AssemblyCode) :- %what if next order is label or val?
    !, addNOPs(Nr, CurrWord, CurrWord_),
    length(X, XLen),
    NewOrderCount is OrderCount + 1 + XLen,
    Val = NewOrderCount,
    translate([NextOrder | T], X, 0, CurrWord_, OrderCount, AssemblyCode).
translate([label(Val)], X, Nr, CurrWord, OrderCount, AssemblyCode) :-
    !, addNOPs(Nr, CurrWord, CurrWord_),
    AssemblyCode = [CurrWord_ | X],
    length(X, XLen),
    NewOrderCount is OrderCount + 1 + XLen,
    Val = NewOrderCount.
translate([Order | T], X, 0, CurrWord, OrderCount, AssemblyCode) :-
    !, append([CurrWord | X], OtherAsm, AssemblyCode),
    length(X, XL),
    NewOrderCount is OrderCount + 1 + XL,
    member((Order, TOrder), [(nop, 0),
                                 (syscall, 1),
                                 (load, 2),
                                 (store, 3),
                                 (swapa, 4),
                                 (swapd, 5),
                                 (branchz, 6),
                                 (branchn, 7),
                                 (jump, 8),
                                 (const, 9),
                                 (add, 0xA),
                                 (sub, 0xB),
                                 (mult, 0xC),
                                 (div, 0xD),
                                 (shift, 0xE),
                                 (nand, 0xF)]), !,
    translate(T, [], 1, TOrder, NewOrderCount, OtherAsm).
translate([Order | T], X, Nr, CurrWord, OrderCount, AssemblyCode) :-
    !, NewNr is (Nr + 1) mod 4,
    member((Order, TOrder), [(nop, 0),
                                 (syscall, 1),
                                 (load, 2),
                                 (store, 3),
                                 (swapa, 4),
                                 (swapd, 5),
                                 (branchz, 6),
                                 (branchn, 7),
                                 (jump, 8),
                                 (const, 9),
                                 (add, 0xA),
                                 (sub, 0xB),
                                 (mult, 0xC),
                                 (div, 0xD),
                                 (shift, 0xE),
                                 (nand, 0xF)]), !,
    NewCurrWord is CurrWord * 16 + TOrder,
    translate(T, X, NewNr, NewCurrWord, OrderCount, AssemblyCode).
translate([], X, Nr, CurrWord, _, AssemblyCode) :-
    !, addNOPs(Nr, CurrWord, CurrWord_),
    AssemblyCode = [CurrWord_ | X].
translate(Code, AssemblyCode) :-
    translate(Code, [], 0, 0, -1, [0 | AssemblyCode]).

addNOPs(0, CurrWord, CurrWord) :- !.
addNOPs(Nr, CurrWord, Res) :-
    NewCurrWord is CurrWord * 16,
    NewNr is (Nr + 1) mod 4,
    addNOPs(NewNr, NewCurrWord, Res).


%TESTING: reading code from file
test(Filename, MachineCode) :-
    open(Filename, read, Str),
    readProgram(Str, Program),
    phrase(lexer(TokList), Program),
    %writeCode(TokList),
    phrase(program(AST), TokList),
    vProgram(AST),
    tProgram(AST, Code),
    write(AST),
    writeCode(Code), nl, nl, nl,
    translate(Code, MachineCode),
    %writeCode(MachineCode),
    close(Str).

readProgram(In, []) :-
    at_end_of_stream(In), !.
readProgram(In, [Char|Prog]) :-
    get_code(In, Char),
    readProgram(In, Prog).

writeCode([]).
writeCode([H|T]) :-
    write(H), nl, writeCode(T).

writeToFileAux([], _).
writeToFileAux([H|T], Stream) :-
  write(Stream, H),
  nl(Stream),
  writeToFileAux(T, Stream).
writeToFile(L, Filename) :-
  open(Filename, write, Stream),
  writeToFileAux(L, Stream),
  close(Stream).
