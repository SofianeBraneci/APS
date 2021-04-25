inContext([(Var, Value)|_], Var, Value).
inContext([(_, _) | RemainingContext], Var, Value):-  inContext(RemainingContext, Var, Value).
 

% extract arg names

extract([], []).
extract([arg(Id, _)| RemainingArgs], [(Id, _ )| RemainingNames]) :- extract(RemainingArgs, RemainingNames).
extract([argp(Id, _)| RemainingArgs], [(Id, _ )| RemainingNames]) :- extract(RemainingArgs, RemainingNames).

% eval evalPrams

evalPrams(_,[],[]).
evalPrams(Env, [E | Exprs], [Value| Values]):- expr(Env, E, Value), evalPrams(Env, Exprs, Values).

% lier les valeurs au ids
link([], [], []).
link([(X, _) | Exprs],[Value|Values], [(X, Value)| ExprValue]) :- link(Exprs, Values, ExprValue).


values(_, _, [], []).
values(Env, Mem, [Expr| Exprs], [Value| Values]):- expr(Env, Mem, Expr, Value), values(Env, Mem, Exprs, Values).

values2(_, _, [], []).
values2(Env, Mem, [Expr| Exprs], [Value| Values]):- exprp(Env, Mem, Expr, Value), values2(Env, Mem, Exprs, Values).


alloc([], 0, [(0, any)]).
alloc([(N, V)|Mem], N1, [(N1, any)|[(N, V)|Mem]]) :- N1 is N+1.

change([(Adr,_)| Mem], Adr, Value, [(Adr, Value)| Mem]).
change([C|Mem], Adr, Value, [C|Mem2]):- change(Mem, Adr, Value, Mem2).

restriction(Mem, N,Mem) :- length(Mem, N).
restriction([_|Mem], N, Mem1):- restriction(Mem, N, Mem1).

expr(_, _,true, 1).
expr(_, _,false, 0).
expr(_,_,num(N), R):- R is integer(N).

expr(Env, _,   Id, Value):- inContext(Env, Id, Value), not(Value = addr(_)).
expr(Env, Mem, Id, Value):- inContext(Env, Id, addr(A)), inContext(Mem, A, Value). 

expr(Env, Mem, not(Expr), 1):- expr(Env, Mem,Expr,0).
expr(Env, Mem, not(Expr), 0) :- expr(Env, Mem,Expr, 1).

expr(Env, Mem, and(ExprOne, _), 0):- expr(Env, Mem,ExprOne, 0).
expr(Env, Mem, and(ExprOne, ExprTwo), V) :-  expr(Env, Mem,ExprOne, 1), expr(Env, Mem,ExprTwo,V).

expr(Env, Mem, or(ExprOne, _), 1):- expr(Env, Mem, ExprOne, 1).
expr(Env, Mem, or(ExprOne,ExprTwo), V):- expr(Env, Mem, ExprOne, 0), expr(Env, Mem,ExprTwo, V).

expr(Env, Mem, eq(ExprOne,ExprTwo), 1):- expr(Env, Mem, ExprOne,V), expr(Env, Mem, ExprTwo,V).
expr(Env, Mem, eq(ExprOne,ExprTwo), 0):- expr(Env, Mem, ExprOne,V1), expr(Env, Mem, ExprTwo,V2), not(V1 = V2).

expr(Env, Mem, lt(ExprOne,ExprTwo), 1):-expr(Env, Mem, ExprOne,V1), expr(Env, Mem, ExprTwo,V2), V1 < V2.
expr(Env, Mem, lt(ExprOne,ExprTwo), 0):-expr(Env, Mem, ExprOne,V1), expr(Env, Mem, ExprTwo,V2),not( V1 < V2).

expr(Env, Mem, add(ExprOne,ExprTwo), R) :- expr(Env, Mem, ExprOne,V1), expr(Env, Mem, ExprTwo,V2), R is  V1 + V2.
expr(Env, Mem, sub(ExprOne,ExprTwo), R):- expr(Env, Mem, ExprOne,V1), expr(Env, Mem, ExprTwo,V2), R is V1 - V2.
expr(Env, Mem, mul(ExprOne,ExprTwo), R):- expr(Env, Mem, ExprOne,V1), expr(Env, Mem, ExprTwo,V2), R is V1 * V2.
expr(Env, Mem, div(ExprOne,ExprTwo), R):- expr(Env, Mem, ExprOne,V1), expr(Env, Mem, ExprTwo,V2), R is V1 // V2.

expr(Env, Mem, if(Condition, Consq, _), V):- expr(Env, Mem, Condition, 1), expr(Env, Mem, Consq,V).
expr(Env, Mem, if(Condition, _, Alt), V):- expr(Env, Mem, Condition, 0), expr(Env, Mem, Alt, V).

expr(Env, _ , anonymousFun(ArgsAndTypes, Expr), closure(Expr, Args, Env)):-print(Env), extract(ArgsAndTypes, Args).  


expr(Env,Mem, app(Expr, ListExpr), V):- (inContext(Env,Expr, closure(_,_,_))-> expr(Env, Mem,appt(Expr, Mem ,ListExpr), V); expr(Env, Mem,appr(Expr, ListExpr), V) ).

expr(Env, Mem, appt(E, ListExpr), V):-
	expr(Env, Mem, E, closure(Ef, Xs, Envf)), 
	values(Env, Mem, ListExpr, Values),
	link(Xs, Values, LinkedValues),
	append(LinkedValues, Envf, EnvfValues),
	expr(EnvfValues, Mem, Ef, V).


expr(Env, Mem, appr(E, ListExpr), V):-
	expr(Env, Mem, E, closure_rec(Xf, Ef, Xs, Envf)), 
	values(Env, Mem, ListExpr, Values),
	link(Xs, Values, LinkedValues),
	append(LinkedValues, Envf, EnvfValues),
	expr( [(Xf, closure_rec(Xf, Ef, Xs, Envf))|EnvfValues], Mem, Ef, V).

exprp(Env, _, adr(Id), A):-  expr(Env, _, Id, A).
exprp(Env,Mem, E, V):- expr(Env, Mem,E, V).

% stats (env, memory, outstream, stat, memory', outstream').

stat(Env, Mem, O, echo(E), Mem, [N|O]):-  expr(Env, Mem, E, N), print(N).

stat(Env, Mem, O, set(Id, E), Mem1, O):- inContext(Env, Id, addr(A)),exprp(Env,Mem,E, V), print(V) ,change(Mem, A, V, Mem1),print(Mem1).

stat(Env, Mem, O, ifImp(Condition, block(C),_), Mem1, O1):- 
	expr(Env,Mem, Condition, 1), block(Env,Mem, O, block(C), Mem1, O1).

stat(Env, Mem, O, ifImp(Condition,_, block(S)), Mem1, O1):- 
	expr(Env,Mem, Condition, 0), block(Env,Mem, O, block(S), Mem1, O1).


stat(Env, Mem, O, while(Condition, block(CS)), Mem2, O3):-
	expr(Env, Mem, Condition, 1),
	block(Env, Mem, O, block(CS), Mem1, O2),
	stat(Env, Mem1, O2, while(Condition, block(CS)), Mem2, O3).

stat(Env, Mem, O, while(Condition,_), Mem, O):- expr(Env, Mem, Condition, 0).

stat(Env, Mem, O, call(Expr, Args), Mem1, O1):- (inContext(Env, Expr, closure_p(_,_,_))->stat(Env,Mem, O, callp(Expr, Args), Mem1, O1); stat(Env,Mem, O, callpr(Expr, Args), Mem1, O1)).

stat(Env, Mem, O, callp(Expr, Args), Mem1, O1):-
	inContext(Env, Expr, closure_p(P, Xs, Envp)),
	values2(Env, Mem, Args, Values), 
	link(Xs, Values, LinkedValues),
	append(LinkedValues, Envp, EvpValues),
	block(EvpValues, Mem, O, P, Mem1, O1).


stat(Env, Mem, O, callpr(Expr, Args), Mem1, O1):-
	inContext(Env, Expr, closure_pr(Xp,P, Xs, Envp)),
	values2(Env, Mem, Args, Values), 
	link(Xs, Values, LinkedValues),
	append(LinkedValues, Envp, EvpValues),
	block([(Xp, closure_pr(Xp, P, Xs, Envp))| EvpValues], Mem, O, P, Mem1, O1).


% dec(Env, Memory, instruction, Env', Memory')

dec(Env, Mem, const(Id, _, Expr), [(Id, V)| Env], Mem):- expr(Env, Mem,Expr, V).

dec(Env, Mem, var(Id, _), [(Id, addr(A))| Env], Mem1):- alloc(Mem, A, Mem1).

dec(Env, Mem, fun(Id, _, ListArgs, Expr), [(Id, closure(Expr, Args, Env))| Env], Mem):- extract(ListArgs, Args).

dec(Env, Mem, funrec(Id, _ , ListArgs, Expr), [(Id, closure_rec(Id, Expr, Args, Env)) |Env], Mem) :- extract(ListArgs, Args).



dec(Env, Mem, proc(Id, ListArgs, P), [(Id, closure_p(P, Args, Env))| Env], Mem):- extract(ListArgs, Args), print(Args).

dec(Env, Mem, procrec(Id, ListArgs, P), [(Id, closure_pr(Id, P, Args, Env)) |Env], Mem):- extract(ListArgs, Args).


% cmds (environnement, mémoire, sortie, commandes, environnement', mémoire, sortie')
cmds(Env, Mem, O, [Dec|CS], Env2, Mem2, O1) :-
	dec(Env, Mem, Dec, Env1, Mem1),
	cmds(Env1, Mem1, O, CS, Env2, Mem2, O1).

cmds(Env, Mem, O, [Stat|CS], Env1, Mem2, O2) :-
	stat(Env, Mem, O, Stat, Mem1, O1),
	cmds(Env, Mem1, O1, CS, Env1, Mem2, O2).

cmds(Env, Mem, O, [], Env, Mem, O).

% block (environnement, mémoire, sortie, programme, mémoire', sortie')
block(Env, Mem, O, block(CS), Mem2, O1) :-
	length(Mem, N),
	cmds(Env, Mem, O, CS, _, Mem1, O1),
	restriction(Mem1, N, Mem2).

% prog(programme, mémoire, sortie)
block(block(CS), Mem, O) :- cmds([], [], [], CS, _, Mem, O).

main_stdin :-
	read(user_input, T),
	block(T, _, O),
	print(O),
	nl.