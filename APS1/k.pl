% contains(contexte, var, type)
contains([(X1, T1)], X1, T1).
contains([arg(ident(X1),T1)],X1,T1).
contains([(_, _)|Ctx], X2, T2) :- contains(Ctx, X2, T2).


argsTypesList([],[]).
argsTypesList([arg(_|T1)|Args],[T1|Argtypes]) :- argsTypesList(Args,Argtypes).


typesList(_,[],[]).
typesList(G,[E1|Er],[T1|Tr]) :- expr(G,E1,T1), typesList(G,Er,Tr).

% expr(contexte, expression, type)
expr(_, num(N), int) :- integer(N).
expr(G, ident(X), T) :- contains(G, X, T).
expr(_, true, bool).
expr(_, false, bool).

expr(G, not(E1),bool) :- expr(G,E1,bool).
expr(G, and(E1,E2),bool) :- expr(G,E1,bool), expr(G,E2,bool).
expr(G, or(E1, E2), bool) :- expr(G, E1, bool), expr(G, E2, bool).

expr(G,eq(E1,E2),bool) :- expr(G,E1,int), expr(G,E2,int).
expr(G, lt(E1, E2), bool) :- expr(G, E1, int), expr(G, E2, int).

expr(G, add(E1, E2), int) :- expr(G, E1, int), expr(G, E2, int).
expr(G, sub(E1, E2), int) :- expr(G, E1, int), expr(G, E2, int).
expr(G, mul(E1, E2), int) :- expr(G, E1, int), expr(G, E2, int).
expr(G, div(E1, E2), int) :- expr(G, E1, int), expr(G, E2, int).

expr(G, anonymousFun(XsTs, E), composedType(Ts, Tr)) :-
	argsTypesList(XsTs, Ts),
	append(XsTs, G, XsTsG),
	expr(XsTsG, E, Tr).

expr(G,app(ident(F),Es),T) :- typesList(G,Es,Ts), expr(G,ident(F),composedType(Ts,T)).

expr(G,if(E1,E2,E3),T) :- expr(G,E1,bool), expr(G,E2,T), expr(G,E3,T).


%def (ctx,declaration,ctx)
def(G, const(ident(X), T, E), [(X, T)|G]) :- expr(G, E, T).

def(G,fun(ident(Id),ReturnType,Args,Ex),[(Id,composedType(Ts,ReturnType))|G]) :- 
	argsTypesList(Args,Ts),
	append(Args, G, ArgsG),
	expr(ArgsG, Ex, ReturnType).

def(G, funRec(ident(X), Tr, XsTs, E), [(X, composedType(Ts, Tr))|G]) :-
	argsTypesList(XsTs, Ts),
	append(XsTs, G, XsTsG),
	expr([(X, composedType(Ts, Tr))|XsTsG], E, Tr).

% stat (contexte, echo, void)
stat(G, echo(E), void) :- expr(G, E, int).

% cmds (contexte, commandes, void)
cmds(G, [Def|CS], void) :- def(G, Def, Ctx), cmds(Ctx, CS, void).
cmds(G, [Stat|CS], void) :- stat(G, Stat, void), cmds(G, CS, void).
cmds(_, [], void).

% prog (programme, void)
prog(prog(CS), void) :- cmds([], CS, void).

main_stdin :-
	read(user_input, T),
	prog(T, R),
	print(R).