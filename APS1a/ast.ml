

type block = cmd list

and cmd = Stat of stat 
          | Def of def 
and stat =
      | Echo of expr
      | Set of string * expr
      | IfImp of expr * block * block
      | While of expr * block
      | Call of string * exprp list

and def = 
      | Var of string * apstype
      | Proc of string * arg list * block
      | ProcRec of string * arg list * block
      | Const of string * apstype * expr
      | Fun of string * apstype * arg list * expr
      | FunRec of string * apstype * arg list * expr

and apstype =
            | Int 
            | Bool 
            | Ref of apstype
            | ComposedType of apstype list * apstype

and arg = Arg of string * apstype | Argp of string * apstype

and expr = 
          | CBool of bool
          | Num of int
          | Add of expr * expr
          | Sub of expr * expr
          | Mul of expr * expr
          | Not of expr
          | And of expr * expr
          | Or of expr * expr
          | If of expr * expr * expr
          | Eq of expr * expr
          | Lt of expr * expr
          | Div of expr * expr
          | Ident of string
          | App of expr * expr list
          | AnonymousFun of arg list * expr
and exprp = 
          | Adr of string
          | Experp of expr 
          

