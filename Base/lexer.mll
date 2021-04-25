
{
  open Parser        (* The type token is defined in parser.mli *)
  exception Eof

}
rule token = parse
    [' ' '\t' '\n']       { token lexbuf }     (* skip blanks *)
  | '('              { LPAR }
  | ')'              { RPAR }
  | '['              {LBRACKET}
  | ']'              {RBRACKET}
  | ';'              {SEMICOLON}
  | ':'              {COLON}
  | ','              {COMMA}
  | '*'              {STAR}
  | "->"             {ARROW}
  | "CONST"          {CONST}
  | "FUN"            {FUN}
  | "REC"            {REC}
  | "ECHO"           {ECHO} 
  | "bool"           {BOOL}
  | "int"            {INT} 
  | "true"   as b        {CBOOL(bool_of_string b)}
  | "false"  as b        {CBOOL(bool_of_string b)}
  | "not"            {NOT}
  | "eq"             {EQ}
  | "lt"             {LT}
  | "add"            {ADD}
  | "sub"            {SUB}
  | "mul"            {MUL}
  | "div"            {DIV}
  | "if"             {IF}
  | "and"            {AND}
  | "or"             {OR}
  | '-'?['0'-'9']+('.'['0'-'9'])? as lxm { NUM(int_of_string lxm) }
  | ['a'-'z']['a'-'z''A'-'Z''0'-'9']* as lxm { IDENT(lxm) }
  | eof              { raise Eof }
