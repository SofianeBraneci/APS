

type prog = cmd list

and cmd = Stat of stat 
          | Def of def 
and stat = Echo of expr 

and def = 
      | Const of string * apstype * expr
      | Fun of string * apstype * arg list * expr
      | FunRec of string * apstype * arg list * expr

and apstype =
            | Int 
            | Bool 
            | ComposedType of apstype list * apstype

and arg = Arg of string * apstype

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

