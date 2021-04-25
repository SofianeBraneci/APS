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
  | WHILE
  | CALL
  | SET
  | IFIMP
  | VAR
  | PROC

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"


open Ast

# 45 "parser.ml"
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
  285 (* WHILE *);
  286 (* CALL *);
  287 (* SET *);
  288 (* IFIMP *);
  289 (* VAR *);
  290 (* PROC *);
    0|]

let yytransl_block = [|
  272 (* CBOOL *);
  282 (* NUM *);
  283 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\003\000\003\000\003\000\003\000\
\003\000\004\000\004\000\004\000\004\000\004\000\004\000\005\000\
\005\000\005\000\006\000\006\000\008\000\008\000\007\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\009\000\009\000\009\000\009\000\009\000\009\000\010\000\010\000\
\000\000"

let yylen = "\002\000\
\003\000\001\000\003\000\003\000\004\000\003\000\006\000\005\000\
\003\000\004\000\009\000\010\000\003\000\006\000\007\000\001\000\
\001\000\005\000\001\000\003\000\001\000\003\000\003\000\001\000\
\001\000\003\000\003\000\003\000\003\000\002\000\003\000\003\000\
\003\000\003\000\008\000\001\000\004\000\006\000\001\000\002\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\041\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\000\000\000\000\017\000\
\016\000\000\000\000\000\000\000\000\000\000\000\025\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\024\000\036\000\000\000\000\000\000\000\000\000\009\000\006\000\
\000\000\013\000\000\000\000\000\003\000\004\000\000\000\000\000\
\010\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\030\000\005\000\000\000\040\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\032\000\
\033\000\026\000\027\000\028\000\029\000\000\000\031\000\034\000\
\008\000\000\000\000\000\000\000\020\000\000\000\000\000\000\000\
\037\000\023\000\022\000\000\000\000\000\007\000\000\000\014\000\
\018\000\000\000\000\000\000\000\000\000\015\000\000\000\000\000\
\038\000\000\000\000\000\011\000\000\000\012\000\035\000"

let yydgoto = "\002\000\
\004\000\014\000\015\000\016\000\063\000\064\000\070\000\071\000\
\054\000\055\000"

let yysindex = "\001\000\
\009\255\000\000\082\255\000\000\242\254\007\255\014\255\034\255\
\011\255\012\255\039\255\015\255\017\255\047\255\070\255\073\255\
\035\255\052\255\035\255\045\255\045\255\045\255\045\255\045\255\
\035\255\054\255\079\255\000\000\082\255\082\255\035\255\000\000\
\000\000\045\255\035\255\080\255\045\255\058\255\000\000\045\255\
\045\255\045\255\045\255\045\255\045\255\085\255\045\255\045\255\
\000\000\000\000\045\255\086\255\087\255\045\255\000\000\000\000\
\088\255\000\000\084\255\058\255\000\000\000\000\083\255\089\255\
\000\000\091\255\058\255\045\255\093\255\094\255\096\255\045\255\
\045\255\045\255\045\255\045\255\045\255\045\255\045\255\045\255\
\000\000\000\000\009\255\000\000\009\255\058\255\098\255\035\255\
\035\255\058\255\100\255\103\255\035\255\058\255\105\255\000\000\
\000\000\000\000\000\000\000\000\000\000\106\255\000\000\000\000\
\000\000\009\255\113\255\009\255\000\000\107\255\114\255\118\255\
\000\000\000\000\000\000\045\255\045\255\000\000\009\255\000\000\
\000\000\119\255\045\255\120\255\122\255\000\000\045\255\123\255\
\000\000\045\255\124\255\000\000\125\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\117\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\072\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\115\255\000\000\
\000\000\000\000\000\000\000\000\000\000\126\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\180\255\232\255\000\000\000\000\247\255\040\000\000\000\207\255\
\236\255\235\255"

let yytablesize = 130
let yytable = "\052\000\
\053\000\001\000\056\000\057\000\061\000\062\000\105\000\034\000\
\106\000\036\000\087\000\003\000\017\000\065\000\020\000\058\000\
\068\000\091\000\018\000\072\000\073\000\074\000\075\000\076\000\
\077\000\066\000\079\000\080\000\026\000\118\000\081\000\120\000\
\084\000\019\000\021\000\031\000\107\000\022\000\023\000\024\000\
\111\000\025\000\126\000\027\000\115\000\037\000\092\000\038\000\
\032\000\033\000\028\000\096\000\097\000\098\000\099\000\100\000\
\101\000\102\000\103\000\104\000\039\000\040\000\041\000\042\000\
\043\000\044\000\045\000\046\000\047\000\048\000\049\000\050\000\
\051\000\039\000\029\000\039\000\039\000\030\000\035\000\110\000\
\059\000\060\000\067\000\114\000\069\000\078\000\086\000\082\000\
\083\000\085\000\088\000\005\000\006\000\090\000\007\000\124\000\
\125\000\089\000\093\000\095\000\094\000\108\000\128\000\112\000\
\113\000\116\000\131\000\117\000\121\000\133\000\008\000\009\000\
\010\000\011\000\012\000\013\000\119\000\122\000\123\000\127\000\
\002\000\129\000\130\000\019\000\132\000\134\000\135\000\109\000\
\000\000\021\000"

let yycheck = "\020\000\
\021\000\001\000\023\000\024\000\029\000\030\000\083\000\017\000\
\085\000\019\000\060\000\003\001\027\001\034\000\001\001\025\000\
\037\000\067\000\012\001\040\000\041\000\042\000\043\000\044\000\
\045\000\035\000\047\000\048\000\012\001\106\000\051\000\108\000\
\054\000\027\001\001\001\001\001\086\000\027\001\027\001\001\001\
\090\000\027\001\119\000\027\001\094\000\001\001\068\000\003\001\
\014\001\015\001\004\001\072\000\073\000\074\000\075\000\076\000\
\077\000\078\000\079\000\080\000\016\001\017\001\018\001\019\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\027\001\
\028\001\002\001\005\001\004\001\005\001\005\001\027\001\089\000\
\027\001\003\001\003\001\093\000\027\001\001\001\003\001\002\001\
\002\001\002\001\008\001\010\001\011\001\003\001\013\001\116\000\
\117\000\009\001\006\001\004\001\007\001\004\001\123\000\004\001\
\002\001\001\001\127\000\002\001\002\001\130\000\029\001\030\001\
\031\001\032\001\033\001\034\001\004\001\004\001\001\001\001\001\
\004\001\002\001\001\001\009\001\002\001\002\001\002\001\088\000\
\255\255\004\001"

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
  WHILE\000\
  CALL\000\
  SET\000\
  IFIMP\000\
  VAR\000\
  PROC\000\
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
# 36 "parser.mly"
                               (_2)
# 253 "parser.ml"
               : Ast.block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stat) in
    Obj.repr(
# 40 "parser.mly"
            ([Stat(_1)])
# 260 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 41 "parser.mly"
                             (Stat(_1) :: _3)
# 268 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.def) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 42 "parser.mly"
                          (Def(_1) :: _3)
# 276 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 45 "parser.mly"
                             (Echo(_3))
# 283 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 46 "parser.mly"
                      (Set(_2, _3))
# 291 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.block) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 47 "parser.mly"
                                        (IfImp(_3, _5, _6))
# 300 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 48 "parser.mly"
                                  (While(_3, _5))
# 308 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr list) in
    Obj.repr(
# 49 "parser.mly"
                        (Call(_2, _3))
# 316 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.apstype) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 51 "parser.mly"
                               (Const(_2, _3, _4))
# 325 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 6 : Ast.apstype) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : Ast.arg list) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 52 "parser.mly"
                                                              (Fun(_2, _3, _5, _8))
# 335 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : Ast.apstype) in
    let _6 = (Parsing.peek_val __caml_parser_env 4 : Ast.arg list) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 53 "parser.mly"
                                                                  (FunRec(_3, _4, _6, _9))
# 345 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 54 "parser.mly"
                        (Var(_2, _3))
# 353 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 55 "parser.mly"
                                              (Proc(_2, _4, _6))
# 362 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 56 "parser.mly"
                                                  (ProcRec(_3, _5, _7))
# 371 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
             (Int)
# 377 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    Obj.repr(
# 60 "parser.mly"
              (Bool)
# 383 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.apstype list) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.apstype) in
    Obj.repr(
# 61 "parser.mly"
                                          (ComposedType(_2, _4))
# 391 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 64 "parser.mly"
                       ([_1])
# 398 "parser.ml"
               : Ast.apstype list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.apstype) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype list) in
    Obj.repr(
# 65 "parser.mly"
                                 (_1 :: _3)
# 406 "parser.ml"
               : Ast.apstype list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 69 "parser.mly"
          ([_1])
# 413 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg list) in
    Obj.repr(
# 70 "parser.mly"
                      (_1::_3)
# 421 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 72 "parser.mly"
                          (Arg(_1, _3))
# 429 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 75 "parser.mly"
          (Num(_1))
# 436 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 76 "parser.mly"
            (CBool( _1))
# 443 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 77 "parser.mly"
                     (Add(_2, _3))
# 451 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 78 "parser.mly"
                     (Sub(_2, _3))
# 459 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 79 "parser.mly"
                     (Mul(_2, _3))
# 467 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 80 "parser.mly"
                     (Div(_2, _3))
# 475 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 81 "parser.mly"
                     (Not(_2))
# 482 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 82 "parser.mly"
                     (And(_2, _3))
# 490 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 83 "parser.mly"
                     (Eq(_2, _3))
# 498 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 84 "parser.mly"
                     (Lt(_2, _3))
# 506 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 85 "parser.mly"
                     (Or(_2, _3))
# 514 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 86 "parser.mly"
                                             (If(_3, _5, _7))
# 523 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 87 "parser.mly"
            (Ident(_1))
# 530 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr list) in
    Obj.repr(
# 88 "parser.mly"
                           (App(_2, _3))
# 538 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ast.arg list) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 89 "parser.mly"
                                             (AnonymousFun(_2, _5))
# 546 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 92 "parser.mly"
           ([_1])
# 553 "parser.ml"
               : Ast.expr list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr list) in
    Obj.repr(
# 93 "parser.mly"
                  (_1::_2)
# 561 "parser.ml"
               : Ast.expr list))
(* Entry block *)
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
let block (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.block)
