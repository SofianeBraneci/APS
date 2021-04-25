inContext([(Var, Type)|_], Var, Type).
inContext([(_, _) | RemainingContext], Var, Type):-  inContext(RemainingContext, Var, Type).


% extract arg names

extract([], []).
extract([arg(ident(Id), Type)| RemainingArgs], [(Id, Type) | RemainingNames]) :- extract(RemainingArgs, RemainingNames).

% args

typeArgs([],[]).
typeArgs([arg(_, Type)| RemainingArgs], [Type| RemainingType]) :- typeArgs(RemainingArgs, RemainingType).


% checking types

listTypes(_,[],[]).
listTypes(Context, [Expr| Exprs], [Type| Types]) :-print(Expr),expr(Context, Expr, Type), listTypes(Context, Exprs, Types).


% checking expressions

expr(_,num(N), int) :- integer(N).
expr(Context, ident(Var), Type):- inContext(Context, Var, Type).
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


expr(Context, anonymousFun(VarsAndTypes, Expr), composedTypes(TypesIn, ReturnType)):-
    typeArgs(VarsAndTypes, TypesIn),
    append(VarsAndTypes, Context,VarsAndTypesInContext ),
    expr(VarsAndTypesInContext, Expr, ReturnType).

expr(Context, app(ident(Id), Expr), ReturnType):- 
        listTypes(Context, Expr, TypesIn),
        print(Context),
        expr(Context, ident(Id),composedTypes(TypesIn, ReturnType)).

expr(Context, if(Cond, Cons, Alt), Type):- 
        expr(Context,Cond, bool), expr(Context, Cons, Type), expr(Context, Alt, Type).

% dec 
dec(Context, const(ident(Id), Type, Expr), [(Id, Type)| Context]):- expr(Context, Expr, Type).


dec(Context, fun(ident(Id), ReturnType, ArgsAndTypes, Expr), [(Id, composedTypes(Type, ReturnType))| Context]):- 
    typeArgs(ArgsAndTypes, Type),
    extract(ArgsAndTypes, ListNamesAndTypes),
    append(ListNamesAndTypes, Context, ExtendedContext), 
    expr(ExtendedContext, Expr, ReturnType ).

dec(Context, funrec(ident(Id), ReturnType, ArgsAndTypes, Expr), [(Id, composedTypes(Type, ReturnType))| Context]):- 
    typeArgs(ArgsAndTypes, Type), 
    extract(ArgsAndTypes, ListNamesAndTypes),
    append(ListNamesAndTypes, Context, ExtendedContext), 
    expr([(Id, composedTypes(Type, ReturnType))| ExtendedContext], Expr, ReturnType).

% stat

% stat (contexte, echo, void)
stat(Context, echo(Expr), void) :- expr(Context, Expr, int).
% cmds (contexte, commandes, void)
cmds(Context, [Dec|Cmd], void) :- dec(Context, Dec, NewContext), cmds(NewContext, Cmd, void).
cmds(Context, [Stat|Cmd], void) :- stat(Context, Stat, void), cmds(Context, Cmd, void).
cmds(_, [], void).

% prog (programme, void)
prog(prog(CS), void) :- cmds([], CS, void).

main_stdin :-
	read(user_input,T),
    prog(T,R),
	print(R).
