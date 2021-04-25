
open Ast
  
let rec print_expr e =
  match e with
  | CBool(b) ->    Printf.printf "%b" b
  | Num(n) ->      Printf.printf "num(%d)" n
  | Add(e1, e2) -> (Printf.printf "add(";
                   print_expr e1; 
                   Printf.printf ",";
                   print_expr e2;
                   Printf.printf ")")
  | Sub(e1, e2) -> (Printf.printf "sub(";
                   print_expr e1; 
                   Printf.printf ",";
                   print_expr e2;
                   Printf.printf ")")
  | Mul(e1, e2) -> (Printf.printf "mul(";
                   print_expr e1; 
                   Printf.printf ",";
                   print_expr e2;
                   Printf.printf ")")
  | Not(e) ->      (Printf.printf "not(";
                   print_expr e;
                   Printf.printf ")")
  | And(e1, e2) -> (Printf.printf "and(";
                   print_expr e1; 
                   Printf.printf ",";
                   print_expr e2;
                   Printf.printf ")")
  | Or(e1, e2) ->  (Printf.printf "or(";
                   print_expr e1; 
                   Printf.printf ",";
                   print_expr e2;
                   Printf.printf ")")
  | If(cond, cons, alt) -> 
                  (Printf.printf "if(";
                  print_expr cond;
                  Printf.printf ",";
                  print_expr cons;
                  Printf.printf ",";
                  print_expr alt;
                  Printf.printf ")")
  | Div(e1, e2) -> 
                 ( Printf.printf "div(";
                  print_expr e1; 
                  Printf.printf ",";
                  print_expr e2;
                  Printf.printf ")")
  | Lt(e1, e2) -> 
              ( Printf.printf "lt(";
                print_expr e1; 
                Printf.printf ",";
                print_expr e2;
                Printf.printf ")")
  | Eq (e1, e2) ->
            (Printf.printf "eq(";
              print_expr e1; 
              Printf.printf ",";
              print_expr e2;
              Printf.printf ")")
  | Ident(s) ->   Printf.printf "ident(%s)" s
  | App(e, le) -> 
              (Printf.printf "app(";
              print_expr e;
              Printf.printf ",";
              Printf.printf "[";
              print_exprs le;
              Printf.printf "])")
  | AnonymousFun(args, e) -> 
              (Printf.printf "anonymousFun(";
              Printf.printf "[";
              print_args args;
              Printf.printf "]," ;
              print_expr e;
              Printf.printf ")")
and print_exprs es = 
match es with
| [] -> ()
| [e] -> print_expr e;
| e :: t -> print_expr e;Printf.printf ","; print_exprs t;
and print_arg arg = 
match arg with
  |Arg(s, t) ->
          (Printf.printf "arg(";
          Printf.printf "ident(%s),"s;
          print_type t;
          Printf.printf ")")
and print_args args = 
match args with
| [] -> ()
| [arg] ->      print_arg arg
| h :: tl ->    
        (print_arg h; 
        Printf.printf ",";
        print_args tl)

and print_type t =
match t with
| Int ->        Printf.printf "int"
| Bool ->       Printf.printf "bool"
| ComposedType (types, ty) -> 
                (Printf.printf "composedType([";
                print_types types;
                Printf.printf "],";
                print_type ty;
                Printf.printf ")")
and print_types types = 
match types with 
  | [] -> ()
  | [t] ->     print_type t;
  | h :: tl -> 
               (print_type h; 
               Printf.printf ",";
               print_types tl)

and print_stat stat = 
 match stat with 
 | Echo(e) -> 
              (Printf.printf "echo(";
              print_expr e;
              Printf.printf ")";
              )
 |Set(ident, e) -> (
              Printf.printf "set(";
              Printf.printf "ident(%s)," ident;
              print_expr e;
              Printf.printf ")";
              )
| IfImp(e, block1, block2) -> 
              (Printf.printf "ifImp(";
              print_expr e;
              Printf.printf ",block([";
              print_block block1;
              Printf.printf "]),block([";
              print_block block2;
              Printf.printf "]))";
              )
 | While(e, block) ->
              (Printf.printf "while(";
              print_expr e;
              Printf.printf ",block([";
              print_block block;
              Printf.printf "]))";
              )
 | Call(ident, exps) ->
              (Printf.printf "call(";
              Printf.printf "ident(%s),[" ident; 
              print_exprs exps;
              Printf.printf "])";)
and print_def def = 
match def with 
| Const(ident, t, e) -> 
              (Printf.printf "const(";
              Printf.printf "ident(%s)," ident;
              print_type t;
              Printf.printf ",";
              print_expr e; 
              Printf.printf ")")
| Fun(ident, t, args, e) -> 
              (Printf.printf "fun(";
              Printf.printf "ident(%s)," ident;
              print_type t;
              Printf.printf ",[";
              print_args args;
              Printf.printf "],";
              print_expr e;
              Printf.printf ")")

| FunRec(ident, t, args, e) -> 
              (Printf.printf "funrec(";
              Printf.printf "ident(%s)," ident;
              print_type t;
              Printf.printf ",[";
              print_args args;
              Printf.printf "],";
              print_expr e;
              Printf.printf ")")
| Var(ident, t) ->(
              Printf.printf "var(ident(%s)," ident;
              print_type t;
              Printf.printf ")";)
| Proc(ident, args, block) ->(
              Printf.printf "proc(ident(%s)," ident;
              Printf.printf "[";
              print_args args;
              Printf.printf "],block([";
              print_block block;
              Printf.printf "]))";)
| ProcRec(ident, args, block) ->
              (Printf.printf "procrec(ident(%s)," ident;
              Printf.printf "["; 
              print_args args; 
              Printf.printf "],block(["; 
              print_block block;
              Printf.printf "]))")
and print_cmds cmd = 
match cmd with
| Stat(stat) -> 
              print_stat stat;
| Def(def) -> print_def def
                                  
and print_block  prog =
match prog with
| [] -> ()
| [cmd] -> print_cmds cmd;
| cmd :: cmds -> 
              (print_cmds cmd;
              Printf.printf ",";
            print_block cmds;)
;;
let fname = Sys.argv.(1) in
let ic = open_in fname in
  try
    let lexbuf = Lexing.from_channel ic in
    let prog = Parser.block Lexer.token lexbuf in
      Printf.printf "block([";
      print_block prog;
      print_string "])\n"
  with Lexer.Eof ->
    exit 0
      
