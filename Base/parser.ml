type token =
  | LPAR
  | RPAR
  | LBRACKET
  | RBRACKET
  | SEMICOLON
  | COLON
  | COMMA
  | STAR
  | ARROW
  | CONST
  | FUN
  | REC
  | ECHO
  | BOOL
  | INT
  | CBOOL of (bool)
  | EQ
  | LT
  | ADD
  | SUB
  | MUL
  | DIV
  | IF
  | AND
  | OR
  | NUM of (int)
  | IDENT of (string)
  | NOT

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"


open Ast

# 39 "parser.ml"
let yytransl_const = [|
  257 (* LPAR *);
  258 (* RPAR *);
  259 (* LBRACKET *);
  260 (* RBRACKET *);
  261 (* SEMICOLON *);
  262 (* COLON *);
  263 (* COMMA *);
  264 (* STAR *);
  265 (* ARROW *);
  266 (* CONST *);
  267 (* FUN *);
  268 (* REC *);
  269 (* ECHO *);
  270 (* BOOL *);
  271 (* INT *);
  273 (* EQ *);
  274 (* LT *);
  275 (* ADD *);
  276 (* SUB *);
  277 (* MUL *);
  278 (* DIV *);
  279 (* IF *);
  280 (* AND *);
  281 (* OR *);
  284 (* NOT *);
    0|]

let yytransl_block = [|
  272 (* CBOOL *);
  282 (* NUM *);
  283 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\003\000\004\000\004\000\004\000\005\000\
\005\000\005\000\006\000\006\000\008\000\008\000\007\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\010\000\010\000\
\000\000"

let yylen = "\002\000\
\003\000\001\000\003\000\004\000\004\000\009\000\010\000\001\000\
\001\000\005\000\001\000\003\000\001\000\003\000\003\000\001\000\
\001\000\003\000\003\000\003\000\003\000\002\000\003\000\003\000\
\003\000\003\000\008\000\001\000\004\000\004\000\001\000\002\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\033\000\000\000\000\000\000\000\000\000\
\002\000\000\000\000\000\000\000\000\000\000\000\001\000\000\000\
\000\000\009\000\008\000\000\000\000\000\000\000\000\000\000\000\
\017\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\016\000\028\000\000\000\000\000\003\000\000\000\
\000\000\005\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\022\000\004\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\024\000\025\000\018\000\019\000\
\020\000\021\000\000\000\023\000\026\000\012\000\000\000\000\000\
\000\000\032\000\029\000\015\000\014\000\030\000\000\000\010\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\006\000\
\000\000\007\000\027\000"

let yydgoto = "\002\000\
\004\000\008\000\009\000\010\000\040\000\041\000\047\000\048\000\
\064\000\065\000"

let yysindex = "\001\000\
\002\255\000\000\037\255\000\000\236\254\254\254\007\255\020\255\
\000\000\016\255\017\255\255\254\017\255\043\255\000\000\037\255\
\017\255\000\000\000\000\043\255\017\255\025\255\043\255\003\255\
\000\000\043\255\043\255\043\255\043\255\043\255\043\255\028\255\
\043\255\043\255\000\000\000\000\043\255\031\255\000\000\026\255\
\036\255\000\000\046\255\003\255\043\255\047\255\045\255\051\255\
\043\255\043\255\043\255\043\255\043\255\043\255\043\255\043\255\
\043\255\000\000\000\000\017\255\017\255\003\255\053\255\043\255\
\056\255\017\255\003\255\043\255\000\000\000\000\000\000\000\000\
\000\000\000\000\070\255\000\000\000\000\000\000\072\255\071\255\
\076\255\000\000\000\000\000\000\000\000\000\000\043\255\000\000\
\078\255\043\255\080\255\043\255\081\255\043\255\082\255\000\000\
\083\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\073\255\
\000\000\000\000\000\000\000\000\000\000\000\000\084\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\085\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\070\000\000\000\000\000\246\255\029\000\000\000\216\255\
\242\255\026\000"

let yytablesize = 90
let yytable = "\038\000\
\020\000\001\000\022\000\063\000\003\000\042\000\011\000\014\000\
\045\000\012\000\043\000\049\000\050\000\051\000\052\000\053\000\
\054\000\017\000\056\000\057\000\016\000\080\000\058\000\015\000\
\013\000\021\000\085\000\044\000\055\000\046\000\018\000\019\000\
\059\000\060\000\069\000\070\000\071\000\072\000\073\000\074\000\
\075\000\076\000\077\000\023\000\061\000\024\000\005\000\006\000\
\062\000\007\000\079\000\067\000\066\000\086\000\068\000\084\000\
\081\000\083\000\025\000\026\000\027\000\028\000\029\000\030\000\
\031\000\032\000\033\000\034\000\035\000\036\000\037\000\087\000\
\091\000\088\000\089\000\093\000\090\000\095\000\092\000\097\000\
\094\000\011\000\096\000\098\000\099\000\039\000\031\000\013\000\
\078\000\082\000"

let yycheck = "\014\000\
\011\000\001\000\013\000\044\000\003\001\020\000\027\001\001\001\
\023\000\012\001\021\000\026\000\027\000\028\000\029\000\030\000\
\031\000\001\001\033\000\034\000\005\001\062\000\037\000\004\001\
\027\001\027\001\067\000\003\001\001\001\027\001\014\001\015\001\
\002\001\008\001\049\000\050\000\051\000\052\000\053\000\054\000\
\055\000\056\000\057\000\001\001\009\001\003\001\010\001\011\001\
\003\001\013\001\061\000\007\001\006\001\068\000\004\001\066\000\
\004\001\002\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\024\001\025\001\026\001\027\001\028\001\002\001\
\087\000\002\001\004\001\090\000\001\001\092\000\001\001\094\000\
\001\001\009\001\002\001\002\001\002\001\016\000\002\001\004\001\
\060\000\064\000"

let yynames_const = "\
  LPAR\000\
  RPAR\000\
  LBRACKET\000\
  RBRACKET\000\
  SEMICOLON\000\
  COLON\000\
  COMMA\000\
  STAR\000\
  ARROW\000\
  CONST\000\
  FUN\000\
  REC\000\
  ECHO\000\
  BOOL\000\
  INT\000\
  EQ\000\
  LT\000\
  ADD\000\
  SUB\000\
  MUL\000\
  DIV\000\
  IF\000\
  AND\000\
  OR\000\
  NOT\000\
  "

let yynames_block = "\
  CBOOL\000\
  NUM\000\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.cmd list) in
    Obj.repr(
# 35 "parser.mly"
                              (_2)
# 211 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stat) in
    Obj.repr(
# 38 "parser.mly"
               ([Stat(_1)])
# 218 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.def) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 39 "parser.mly"
                          (Def(_1) :: _3)
# 226 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 42 "parser.mly"
                           (Echo(_3))
# 233 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.apstype) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 44 "parser.mly"
                               (Const(_2, _3, _4))
# 242 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 6 : Ast.apstype) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : Ast.arg list) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 45 "parser.mly"
                                                              (Fun(_2, _3, _5, _8))
# 252 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : Ast.apstype) in
    let _6 = (Parsing.peek_val __caml_parser_env 4 : Ast.arg list) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 46 "parser.mly"
                                                                  (FunRec(_3, _4, _6, _9))
# 262 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    Obj.repr(
# 49 "parser.mly"
             (Int)
# 268 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "parser.mly"
              (Bool)
# 274 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.apstype list) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.apstype) in
    Obj.repr(
# 51 "parser.mly"
                                          (ComposedType(_2, _4))
# 282 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 54 "parser.mly"
                       ([_1])
# 289 "parser.ml"
               : Ast.apstype list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.apstype) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype list) in
    Obj.repr(
# 55 "parser.mly"
                                 (_1 :: _3)
# 297 "parser.ml"
               : Ast.apstype list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 59 "parser.mly"
          ([_1])
# 304 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg list) in
    Obj.repr(
# 60 "parser.mly"
                      (_1::_3)
# 312 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 62 "parser.mly"
                          (Arg(_1, _3))
# 320 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 65 "parser.mly"
          (Num(_1))
# 327 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 66 "parser.mly"
            (CBool( _1))
# 334 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 67 "parser.mly"
                     (Add(_2, _3))
# 342 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 68 "parser.mly"
                     (Sub(_2, _3))
# 350 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 69 "parser.mly"
                     (Mul(_2, _3))
# 358 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 70 "parser.mly"
                     (Div(_2, _3))
# 366 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 71 "parser.mly"
                     (Not(_2))
# 373 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 72 "parser.mly"
                     (And(_2, _3))
# 381 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 73 "parser.mly"
                     (Eq(_2, _3))
# 389 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 74 "parser.mly"
                     (Lt(_2, _3))
# 397 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 75 "parser.mly"
                     (Or(_2, _3))
# 405 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 76 "parser.mly"
                                             (If(_3, _5, _7))
# 414 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 77 "parser.mly"
            (Ident(_1))
# 421 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr list) in
    Obj.repr(
# 78 "parser.mly"
                           (App(_2, _3))
# 429 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 79 "parser.mly"
                                  (AnonymousFun(_2, _4))
# 437 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 82 "parser.mly"
           ([_1])
# 444 "parser.ml"
               : Ast.expr list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr list) in
    Obj.repr(
# 83 "parser.mly"
                  (_1::_2)
# 452 "parser.ml"
               : Ast.expr list))
(* Entry prog *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let prog (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.prog)
