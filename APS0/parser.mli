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

val prog :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.prog
