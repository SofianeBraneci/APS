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
  | VARADR
  | REF
  | ADR

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"


open Ast

# 48 "parser.ml"
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
  291 (* VARADR *);
  292 (* REF *);
  293 (* ADR *);
    0|]

let yytransl_block = [|
  272 (* CBOOL *);
  282 (* NUM *);
  283 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\003\000\003\000\003\000\003\000\
\003\000\004\000\004\000\004\000\004\000\004\000\004\000\005\000\
\005\000\005\000\005\000\006\000\006\000\008\000\008\000\007\000\
\010\000\010\000\009\000\009\000\011\000\011\000\011\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\011\000\011\000\012\000\012\000\013\000\013\000\014\000\
\014\000\000\000"

let yylen = "\002\000\
\003\000\001\000\003\000\003\000\004\000\003\000\006\000\005\000\
\003\000\004\000\009\000\010\000\003\000\006\000\007\000\001\000\
\001\000\002\000\005\000\001\000\003\000\001\000\003\000\003\000\
\001\000\003\000\004\000\003\000\001\000\001\000\003\000\003\000\
\003\000\003\000\002\000\003\000\003\000\003\000\003\000\008\000\
\001\000\004\000\006\000\001\000\002\000\001\000\004\000\001\000\
\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\050\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\001\000\000\000\000\000\000\000\017\000\
\016\000\000\000\000\000\000\000\000\000\000\000\000\000\030\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\029\000\041\000\000\000\000\000\000\000\000\000\046\000\
\000\000\009\000\006\000\000\000\013\000\000\000\000\000\003\000\
\004\000\000\000\000\000\018\000\010\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\035\000\005\000\000\000\000\000\
\049\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\037\000\038\000\031\000\032\000\033\000\034\000\000\000\036\000\
\039\000\008\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\021\000\000\000\000\000\000\000\045\000\042\000\024\000\
\023\000\000\000\000\000\047\000\007\000\000\000\028\000\000\000\
\026\000\014\000\019\000\000\000\000\000\000\000\000\000\015\000\
\027\000\000\000\000\000\043\000\000\000\000\000\011\000\000\000\
\012\000\040\000"

let yydgoto = "\002\000\
\004\000\014\000\015\000\016\000\066\000\067\000\074\000\075\000\
\094\000\095\000\056\000\101\000\057\000\058\000"

let yysindex = "\008\000\
\007\255\000\000\150\255\000\000\243\254\000\255\032\255\038\255\
\017\255\019\255\046\255\021\255\018\255\045\255\049\255\050\255\
\005\255\023\255\005\255\121\255\121\255\149\255\121\255\121\255\
\005\255\040\255\062\255\000\000\150\255\150\255\005\255\000\000\
\000\000\005\255\121\255\005\255\065\255\121\255\042\255\000\000\
\121\255\121\255\121\255\121\255\121\255\121\255\072\255\121\255\
\121\255\000\000\000\000\121\255\073\255\074\255\069\255\000\000\
\149\255\000\000\000\000\075\255\000\000\071\255\234\254\000\000\
\000\000\070\255\089\255\000\000\000\000\076\255\042\255\121\255\
\077\255\092\255\078\255\121\255\121\255\121\255\121\255\121\255\
\121\255\121\255\121\255\121\255\000\000\000\000\007\255\054\255\
\000\000\007\255\234\254\094\255\080\255\095\255\097\255\005\255\
\005\255\042\255\099\255\121\255\102\255\005\255\042\255\104\255\
\000\000\000\000\000\000\000\000\000\000\000\000\106\255\000\000\
\000\000\000\000\107\255\007\255\108\255\005\255\109\255\234\254\
\007\255\000\000\111\255\112\255\116\255\000\000\000\000\000\000\
\000\000\121\255\121\255\000\000\000\000\007\255\000\000\005\255\
\000\000\000\000\000\000\117\255\121\255\118\255\122\255\000\000\
\000\000\121\255\123\255\000\000\121\255\125\255\000\000\126\255\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\127\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\003\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\124\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\128\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\130\255\000\000\000\000\
\000\000\000\000\000\000\134\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\206\255\243\255\000\000\000\000\017\000\034\000\000\000\196\255\
\000\000\167\255\236\255\051\000\000\000\097\000"

let yytablesize = 184
let yytable = "\053\000\
\054\000\117\000\059\000\060\000\092\000\031\000\048\000\048\000\
\001\000\003\000\099\000\018\000\093\000\017\000\069\000\064\000\
\065\000\072\000\032\000\033\000\076\000\077\000\078\000\079\000\
\080\000\081\000\019\000\083\000\084\000\026\000\137\000\085\000\
\020\000\035\000\072\000\037\000\114\000\124\000\021\000\116\000\
\034\000\061\000\129\000\022\000\027\000\023\000\024\000\025\000\
\028\000\036\000\068\000\100\000\070\000\029\000\030\000\105\000\
\106\000\107\000\108\000\109\000\110\000\111\000\112\000\113\000\
\063\000\133\000\062\000\071\000\073\000\038\000\138\000\039\000\
\082\000\091\000\086\000\087\000\090\000\096\000\098\000\100\000\
\115\000\104\000\102\000\144\000\040\000\041\000\042\000\043\000\
\044\000\045\000\046\000\047\000\048\000\049\000\050\000\051\000\
\052\000\097\000\103\000\118\000\121\000\120\000\125\000\127\000\
\130\000\088\000\119\000\131\000\132\000\142\000\143\000\134\000\
\139\000\123\000\136\000\140\000\141\000\146\000\128\000\148\000\
\147\000\038\000\149\000\039\000\151\000\150\000\153\000\154\000\
\152\000\122\000\002\000\022\000\020\000\025\000\135\000\044\000\
\040\000\041\000\042\000\043\000\044\000\045\000\046\000\047\000\
\048\000\049\000\050\000\051\000\052\000\055\000\126\000\039\000\
\145\000\089\000\000\000\000\000\000\000\000\000\000\000\005\000\
\006\000\000\000\007\000\000\000\040\000\041\000\042\000\043\000\
\044\000\045\000\046\000\047\000\048\000\049\000\050\000\051\000\
\052\000\000\000\008\000\009\000\010\000\011\000\012\000\013\000"

let yycheck = "\020\000\
\021\000\091\000\023\000\024\000\027\001\001\001\004\001\005\001\
\001\000\003\001\071\000\012\001\035\001\027\001\035\000\029\000\
\030\000\038\000\014\001\015\001\041\000\042\000\043\000\044\000\
\045\000\046\000\027\001\048\000\049\000\012\001\120\000\052\000\
\001\001\017\000\055\000\019\000\087\000\098\000\001\001\090\000\
\036\001\025\000\103\000\027\001\027\001\027\001\001\001\027\001\
\004\001\027\001\034\000\072\000\036\000\005\001\005\001\076\000\
\077\000\078\000\079\000\080\000\081\000\082\000\083\000\084\000\
\003\001\116\000\027\001\003\001\027\001\001\001\121\000\003\001\
\001\001\003\001\002\001\002\001\002\001\008\001\003\001\100\000\
\027\001\004\001\006\001\134\000\016\001\017\001\018\001\019\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\027\001\
\028\001\009\001\007\001\006\001\004\001\007\001\004\001\002\001\
\001\001\037\001\027\001\002\001\002\001\130\000\131\000\004\001\
\002\001\097\000\006\001\004\001\001\001\001\001\102\000\002\001\
\141\000\001\001\001\001\003\001\002\001\146\000\002\001\002\001\
\149\000\096\000\004\001\004\001\009\001\004\001\118\000\002\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\001\001\100\000\003\001\
\136\000\057\000\255\255\255\255\255\255\255\255\255\255\010\001\
\011\001\255\255\013\001\255\255\016\001\017\001\018\001\019\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\027\001\
\028\001\255\255\029\001\030\001\031\001\032\001\033\001\034\001"

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
  VARADR\000\
  REF\000\
  ADR\000\
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
# 40 "parser.mly"
                               (_2)
# 285 "parser.ml"
               : Ast.block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.stat) in
    Obj.repr(
# 44 "parser.mly"
            ([Stat(_1)])
# 292 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 45 "parser.mly"
                             (Stat(_1) :: _3)
# 300 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.def) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.cmd list) in
    Obj.repr(
# 46 "parser.mly"
                          (Def(_1) :: _3)
# 308 "parser.ml"
               : Ast.cmd list))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 49 "parser.mly"
                             (Echo(_3))
# 315 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 50 "parser.mly"
                      (Set(_2, _3))
# 323 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.block) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 51 "parser.mly"
                                        (IfImp(_3, _5, _6))
# 332 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 52 "parser.mly"
                                  (While(_3, _5))
# 340 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp list) in
    Obj.repr(
# 53 "parser.mly"
                         (Call(_2, _3))
# 348 "parser.ml"
               : Ast.stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.apstype) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 55 "parser.mly"
                               (Const(_2, _3, _4))
# 357 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 6 : Ast.apstype) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : Ast.arg list) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 56 "parser.mly"
                                                              (Fun(_2, _3, _5, _8))
# 367 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : Ast.apstype) in
    let _6 = (Parsing.peek_val __caml_parser_env 4 : Ast.arg list) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 57 "parser.mly"
                                                                  (FunRec(_3, _4, _6, _9))
# 377 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 58 "parser.mly"
                        (Var(_2, _3))
# 385 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 59 "parser.mly"
                                               (Proc(_2, _4, _6))
# 394 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : Ast.block) in
    Obj.repr(
# 60 "parser.mly"
                                                   (ProcRec(_3, _5, _7))
# 403 "parser.ml"
               : Ast.def))
; (fun __caml_parser_env ->
    Obj.repr(
# 63 "parser.mly"
             (Int)
# 409 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "parser.mly"
              (Bool)
# 415 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 65 "parser.mly"
                     (Ref(_2))
# 422 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Ast.apstype list) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.apstype) in
    Obj.repr(
# 66 "parser.mly"
                                          (ComposedType(_2, _4))
# 430 "parser.ml"
               : Ast.apstype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 69 "parser.mly"
                       ([_1])
# 437 "parser.ml"
               : Ast.apstype list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.apstype) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype list) in
    Obj.repr(
# 70 "parser.mly"
                                 (_1 :: _3)
# 445 "parser.ml"
               : Ast.apstype list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 74 "parser.mly"
          ([_1])
# 452 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg list) in
    Obj.repr(
# 75 "parser.mly"
                      (_1::_3)
# 460 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 77 "parser.mly"
                          (Arg(_1, _3))
# 468 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg) in
    Obj.repr(
# 81 "parser.mly"
           ([_1])
# 475 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.arg list) in
    Obj.repr(
# 82 "parser.mly"
                        (_1::_3)
# 483 "parser.ml"
               : Ast.arg list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 85 "parser.mly"
                                  (Argp(_2, _4))
# 491 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.apstype) in
    Obj.repr(
# 86 "parser.mly"
                           (Arg(_1, _3))
# 499 "parser.ml"
               : Ast.arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 90 "parser.mly"
          (Num(_1))
# 506 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 91 "parser.mly"
            (CBool( _1))
# 513 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 92 "parser.mly"
                     (Add(_2, _3))
# 521 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 93 "parser.mly"
                     (Sub(_2, _3))
# 529 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 94 "parser.mly"
                     (Mul(_2, _3))
# 537 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 95 "parser.mly"
                     (Div(_2, _3))
# 545 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 96 "parser.mly"
                     (Not(_2))
# 552 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 97 "parser.mly"
                     (And(_2, _3))
# 560 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 98 "parser.mly"
                     (Eq(_2, _3))
# 568 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 99 "parser.mly"
                     (Lt(_2, _3))
# 576 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 100 "parser.mly"
                     (Or(_2, _3))
# 584 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : Ast.expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : Ast.expr) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 101 "parser.mly"
                                             (If(_3, _5, _7))
# 593 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 102 "parser.mly"
            (Ident(_1))
# 600 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : Ast.expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr list) in
    Obj.repr(
# 103 "parser.mly"
                           (App(_2, _3))
# 608 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Ast.arg list) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    Obj.repr(
# 104 "parser.mly"
                                             (AnonymousFun(_2, _5))
# 616 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 107 "parser.mly"
           ([_1])
# 623 "parser.ml"
               : Ast.expr list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr list) in
    Obj.repr(
# 108 "parser.mly"
                  (_1::_2)
# 631 "parser.ml"
               : Ast.expr list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.expr) in
    Obj.repr(
# 111 "parser.mly"
           (Experp(_1))
# 638 "parser.ml"
               : Ast.exprp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 112 "parser.mly"
                          (Adr(_3))
# 645 "parser.ml"
               : Ast.exprp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp) in
    Obj.repr(
# 115 "parser.mly"
            ([_1])
# 652 "parser.ml"
               : Ast.exprp list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Ast.exprp) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exprp list) in
    Obj.repr(
# 116 "parser.mly"
                    (_1::_2)
# 660 "parser.ml"
               : Ast.exprp list))
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
