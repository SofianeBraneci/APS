%{


open Ast

%}
 

%token LPAR,RPAR,LBRACKET, RBRACKET
%token SEMICOLON, COLON, COMMA, STAR, ARROW
%token CONST, FUN, REC ECHO, BOOL
%token INT, CBOOL, INT,  EQ, LT, ADD, SUB, MUL, EQ, LT
%token DIV, IF, AND, OR, NUM, IDENT, NOT



%type<Ast.prog> prog
%type<Ast.cmd list> cmds
%type<Ast.stat> stat
%type<Ast.def> def
%type<Ast.apstype> apstype
%type<Ast.apstype list> apstypes
%type<Ast.arg> arg
%type<Ast.arg list> args
%type<Ast.expr> expr
%type<Ast.expr list> exprs
%type<string> IDENT
%type<int> NUM
%type<bool>CBOOL


%start prog
%% 

prog : LBRACKET cmds RBRACKET {$2}

cmds :  
     | stat    {[Stat($1)]}
     | def SEMICOLON cmds {Def($1) :: $3}

stat : 
     ECHO LPAR expr RPAR   {Echo($3)}
def : 
    | CONST IDENT apstype expr {Const($2, $3, $4)}
    | FUN IDENT apstype LBRACKET args RBRACKET LPAR expr RPAR {Fun($2, $3, $5, $8)}
    | FUN REC IDENT apstype LBRACKET args RBRACKET LPAR expr RPAR {FunRec($3, $4, $6, $9)}

apstype: 
       | INT {Int}
       | BOOL {Bool}
       | LPAR apstypes ARROW apstype RPAR {ComposedType($2, $4)}

apstypes : 
         | apstype     {[$1]}
         | apstype STAR apstypes {$1 :: $3}


args: 
    | arg {[$1]}
    | arg COMMA args  {$1::$3}

arg: IDENT COLON apstype  {Arg($1, $3)}

expr: 
    | NUM {Num($1)}
    | CBOOL {CBool( $1)}
    | ADD expr  expr {Add($2, $3)}
    | SUB expr  expr {Sub($2, $3)}
    | MUL expr  expr {Mul($2, $3)}
    | DIV expr  expr {Div($2, $3)}
    | NOT expr       {Not($2)}
    | AND expr  expr {And($2, $3)}
    | EQ  expr expr  {Eq($2, $3)}
    | LT  expr  expr {Lt($2, $3)}
    | OR  expr  expr {Or($2, $3)}
    | IF  LPAR expr RPAR expr LPAR expr RPAR {If($3, $5, $7)}
    | IDENT {Ident($1)}
    | LPAR expr exprs RPAR {App($2, $3)}
    | LBRACKET args RBRACKET expr {AnonymousFun($2, $4)}

exprs:
    | expr {[$1]}
    | expr  exprs {$1::$2}
