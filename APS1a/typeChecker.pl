inContext([(Var, Type)|_], Var, Type).
inContext([(_, _) | RemainingContext], Var, Type):-  inContext(RemainingContext, Var, Type).

extractFromRef(ref(T), T).
% extract arg names

extract([], []).
extract([arg(ident(Id), Type)| RemainingArgs], [(Id, Type) | RemainingNames]) :- print("ag"),extract(RemainingArgs, RemainingNames).
extract([argp(ident(Id), Type)| RemainingArgs], [(Id, ref(Type)) | RemainingNames]) :-print("ap"), extract(RemainingArgs, RemainingNames).
% args

typeArgs([],[]).
typeArgs([arg(_, Type)| RemainingArgs], [Type| RemainingType]) :- typeArgs(RemainingArgs, RemainingType).
typeArgs([argp(_, Type)| RemainingArgs], [ref(Type)| RemainingType]) :- typeArgs(RemainingArgs, RemainingType).

% checking types

listTypes(_,[],[]).
listTypes(Context, [Expr| Exprs], [Type| Types]) :-expr(Context, Expr, Type), listTypes(Context, Exprs, Types).

listTypes2(_,[],[]).
listTypes2(Context, [Expr| Exprs], [Type| Types]) :-exprp(Context, Expr, Type), listTypes2(Context, Exprs, Types).

% checking expressions

expr(_,num(N), int) :- integer(N).
expr(Context, ident(Var), Type):- inContext(Context, Var, Type); inContext(Context, Var, ref(Type)) .

expr(_, true, bool).
expr(_, false, bool).

expr(Context, not(Expr), bool) :-expr(Context, Expr, bool).

expr(Context, and(ExprOne, ExprTwo), bool) :- expr(Context, ExprOne, bool), expr(Context, ExprTwo, bool).

expr(Context, or(ExprOne, ExprTwo), bool) :- expr(Context, ExprOne, bool), expr(Context, ExprTwo, bool).

expr(Context, eq(ExprOne, ExprTwo), bool) :- expr(Context, ExprOne, int), expr(Context, ExprTwo, int).

expr(Context, lt(ExprOne, ExprTwo), bool) :- expr(Context, ExprOne, int), expr(Context, ExprTwo, int).

expr(Context, add(ExprOne, ExprTwo), int) :- expr(Context, ExprOne, int), expr(Context, ExprTwo, int).
expr(Context, sub(ExprOne, ExprTwo), int) :- expr(Context, ExprOne, int), expr(Context, ExprTwo, int).
expr(Context, mul(ExprOne, ExprTwo), int) :- expr(Context, ExprOne, int), expr(Context, ExprTwo, int).
expr(Context, div(ExprOne, ExprTwo), int) :- expr(Context, ExprOne, int), expr(Context, ExprTwo, int).


expr(Context, anonymousFun(VarsAndTypes, Expr), composedType(TypesIn, ReturnType)):-
    typeArgs(VarsAndTypes, TypesIn),
    extract(VarsAndTypes, TypesArgs),
    append(TypesArgs, Context,VarsAndTypesInContext ),
    expr(VarsAndTypesInContext, Expr, ReturnType).

expr(Context, app(E, Expr), ReturnType):-

        listTypes(Context, Expr, TypesIn),

        expr(Context, E,composedType(TypesIn, ReturnType)).

expr(Context, if(Cond, Cons, Alt), Type):- 
        expr(Context,Cond, bool), expr(Context, Cons, Type), expr(Context, Alt, Type).

exprp(Context, adr(Id), Type):- expr(Context, Id, Type).
exprp(Context, E, Type):-expr(Context,E,Type).

% dec 
dec(Context, const(ident(Id), Type, Expr), [(Id, Type)| Context]):- expr(Context, Expr, Type).

dec(Context, var(ident(Id), Type), [(Id,ref(Type)) | Context]).

dec(Context, fun(ident(Id), ReturnType, ArgsAndTypes, Expr), [(Id, composedType(Type, ReturnType))| Context]):- 
    typeArgs(ArgsAndTypes, Type),
    extract(ArgsAndTypes, ListNamesAndTypes),
    append(ListNamesAndTypes, Context, ExtendedContext), 
    expr(ExtendedContext, Expr, ReturnType ).

dec(Context, funrec(ident(Id), ReturnType, ArgsAndTypes, Expr), [(Id, composedType(Type, ReturnType))| Context]):- 
    typeArgs(ArgsAndTypes, Type), 
    extract(ArgsAndTypes, ListNamesAndTypes),
    append(ListNamesAndTypes, Context, ExtendedContext), 
    expr([(Id, composedType(Type, ReturnType))| ExtendedContext], Expr, ReturnType).

dec(Context, proc(ident(Id), ArgsAndTypes, block(CS)), [(Id, composedType(Type, void))| Context]):- 
    typeArgs(ArgsAndTypes, Type),
    extract(ArgsAndTypes, ListNamesAndTypes),
    
    append(ListNamesAndTypes, Context, ExtendedContext), 
 
    cmds(ExtendedContext, CS, void).

dec(Context, procrec(ident(Id), ArgsAndTypes, block(CS)), [(Id, composedType(Type, void))| Context]):- 
    typeArgs(ArgsAndTypes, Type),
     
    extract(ArgsAndTypes, ListNamesAndTypes),
    append(ListNamesAndTypes, Context, ExtendedContext), 
    cmds([(Id, composedType(Type, void))| ExtendedContext], CS, void).

% stat

% stat (contexte, echo, void); T = ref(Type), T(E) = Type
stat(Context, echo(Expr), void) :- expr(Context, Expr, int).
stat(Context, set(ident(Id), Expr), void) :-expr(Context, ident(Id), T), extractFromRef(T, R), expr(Context, Expr, R).
stat(Context, ifImp(Expr, block(C), block(S)), void) :- expr(Context, Expr, bool), cmds(Context, C, void), cmds(Context,S, void).
stat(Context, while(Expr, block(C)), void ) :- expr(Context, Expr,bool), cmds(Context,C, void).
stat(Context, call(ident(Id), Exprs), void) :-  listTypes2(Context, Exprs, Types), inContext(Context, Id, composedType(Types, void)).
% cmds (contexte, commandes, void)
cmds(Context, [Dec|Cmd], void) :- dec(Context, Dec, NewContext), cmds(NewContext, Cmd, void).
cmds(Context, [Stat|Cmd], void) :- stat(Context, Stat, void), cmds(Context, Cmd, void).
cmds(_, [], void).

% prog (programme, void)
block(block(CS), void) :- cmds([], CS, void).

main_stdin :-
	read(user_input,T),
    block(T,R),
	print(R).
