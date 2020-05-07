(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Float of float                       (* floats *)
  | String of string                     (* strings *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
  match exp with 
  | Var x -> SS.singleton x
  | Num _ | Bool _ | Float _ | String _ -> SS.empty
  | Unop (_, exp1) -> free_vars exp1
  | Binop (_, exp1, exp2) -> SS.union (free_vars exp1) (free_vars exp2)
  | Conditional (c, c1, c2) -> SS.union (SS.union (free_vars c) (free_vars c1)) (free_vars c2)
  | Fun (var, exp1) -> SS.remove var (free_vars exp1)
  | Let (var, exp1, exp2) -> SS.union (SS.remove var (free_vars exp2)) (free_vars exp1)
  | Letrec (var, exp1, exp2) -> SS.union (SS.remove var (free_vars exp1)) (SS.remove var (free_vars exp2))
  | Raise | Unassigned -> SS.empty
  | App (exp1, exp2) -> SS.union (free_vars exp1) (free_vars exp2) ;;
  
(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname () : varid =
  let counter = ref 0 in
    let newvar = "n" ^ string_of_int(!counter) in
    counter := !counter + 1;
    newvar;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let rec subst2 (exp : expr) =
    match exp with
    | Var x -> if x = var_name then repl else exp
    | Num _ | Bool _ | Float _ | String _ -> exp               
    | Unop (un, e1) -> Unop (un, subst2 e1)      
    | Binop (bin, e1, e2) -> Binop (bin, subst2 e1, subst2 e2)  
    | Conditional (c, c1, c2) -> Conditional (subst2 c, subst2 c1, subst2 c2)
    | Fun (v, e1) -> if v = var_name then exp
                     else 
                       if SS.mem v (free_vars repl) then
                         let newvar = new_varname () in
                         Fun (newvar, subst2 (subst v (Var newvar) e1))
                       else
                         Fun(v, subst2 e1)
    | Let (v, e1, e2) ->  if v = var_name then
                            Let (v, subst2 e1, e2)
                          else 
                            if SS.mem v (free_vars repl) then
                              let newvar = new_varname () in
                              Let (newvar, subst2 e1, subst2 (subst v (Var newvar) e2))
                            else
                              Let (v, subst2 e1, subst2 e2)
    | Letrec (v, e1, e2) -> if v = var_name then exp
                            else
                              if SS.mem v (free_vars repl) then
                                let newvar = new_varname () in
                                Letrec (newvar, subst2 (subst v (Var newvar) e1), 
                                        subst2 (subst v (Var newvar) e2))
                              else 
                                Letrec (v, subst2 e1, subst2 e2)
    | Raise | Unassigned -> exp
    | App (e1, e2) -> App (subst2 e1, subst2 e2)
  in
  subst2 exp ;;
  ;;

(*......................................................................
  String representations of expressions
 *)
   

let string_of_unop (u : unop) : string = 
  match u with
  | Negate -> "~-"
;;

let string_of_binop (b : binop) : string = 
  match b with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Equals -> "="
  | LessThan -> "<"
;;


 
(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var a -> a                        
  | Num n -> string_of_int n
  | Float f -> string_of_float f 
  | String s -> "\"" ^ s ^ "\""                     
  | Bool b -> string_of_bool b                       
  | Unop (un, exp1) -> string_of_unop un ^ exp_to_concrete_string exp1      
  | Binop (bin, exp1, exp2) -> "(" ^ exp_to_concrete_string exp1 ^ " " ^ string_of_binop bin ^ " " ^ exp_to_concrete_string exp2 ^ ")" 
  | Conditional (c, c1, c2) -> "if " ^ exp_to_concrete_string c ^ " " ^ "then " ^ exp_to_concrete_string c1 ^ " " ^ "else " ^ exp_to_concrete_string c2
  | Fun (var, exp1) -> "fun " ^ var ^ " -> " ^ exp_to_concrete_string exp1             
  | Let (var, exp1, exp2) -> "let " ^ var ^ " = " ^ exp_to_concrete_string exp1 ^ " in " ^ exp_to_concrete_string exp2       
  | Letrec (var, exp1, exp2) -> "let rec " ^ var ^ " = " ^ exp_to_concrete_string exp1 ^ " in " ^ exp_to_concrete_string exp2         
  | Raise -> "Raise"                               
  | Unassigned -> "Unassigned"                         
  | App (exp1, exp2) -> exp_to_concrete_string exp1 ^ " " ^ exp_to_concrete_string exp2 ;;



(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var a -> "Var(" ^ a ^ ")"
  | Num n -> "Num(" ^ string_of_int n ^ ")"
  | Float f -> "Float(" ^ string_of_float f ^ ")" 
  | String s -> "String(" ^ s ^ ")" 
  | Bool b -> "Bool(" ^ string_of_bool b ^")"
  | Unop (un, e1) -> "Unop(" ^ string_of_unop un ^ "," ^ exp_to_abstract_string e1 ^ ")"
  | Binop (bin, e1, e2) -> "Binop(" ^ string_of_binop bin ^ "," ^ exp_to_abstract_string e1 ^ "," ^  exp_to_abstract_string e2 ^ ")"
  | Conditional (c, c1, c2) -> "Conditional(" ^ exp_to_abstract_string c ^ "," ^ exp_to_abstract_string c1 ^ "," ^ exp_to_abstract_string c2 ^ ")"
  | Fun (var, exp1) -> "Fun(" ^ var ^ "," ^ exp_to_abstract_string exp1 ^ ")"
  | Let (var, exp1, exp2) -> "Let(" ^ var ^ "," ^ exp_to_abstract_string exp1 ^ "," ^ exp_to_abstract_string exp2 ^ ")"
  | Letrec (var, exp1, exp2) -> "Letrec(" ^ var ^ "," ^ exp_to_abstract_string exp1 ^ "," ^ exp_to_abstract_string exp2 ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (exp1, exp2) -> "App(" ^ exp_to_abstract_string exp1 ^ "," ^ exp_to_abstract_string exp2 ^ ")" ;;
