(* 
                         CS 51 Final Project
                         MiniML -- Evaluation
*)

(* This module implements a small untyped ML-like language under
   various operational semantics.
 *)

open Expr ;;
  
(* Exception for evaluator runtime, generated by a runtime error in
   the interpreter *)
exception EvalError of string ;;
  
(* Exception for evaluator runtime, generated by an explicit `raise`
   construct in the object language *)
exception EvalException ;;

(*......................................................................
  Environments and values 
 *)

module type ENV = sig
    (* the type of environments *)
    type env
    (* the type of values stored in environments *)
    type value =
      | Val of expr
      | Closure of (expr * env)
   
    (* empty () -- Returns an empty environment *)
    val empty : unit -> env

    (* close expr env -- Returns a closure for `expr` and its `env` *)
    val close : expr -> env -> value

    (* lookup env varid -- Returns the value in the `env` for the
       `varid`, raising an `Eval_error` if not found *)
    val lookup : env -> varid -> value

    (* extend env varid loc -- Returns a new environment just like
       `env` except that it maps the variable `varid` to the `value`
       stored at `loc`. This allows later changing the value, an
       ability used in the evaluation of `letrec`. To make good on
       this, extending an environment needs to preserve the previous
       bindings in a physical, not just structural, way. *)
    val extend : env -> varid -> value ref -> env

    (* env_to_string env -- Returns a printable string representation
       of environment `env` *)
    val env_to_string : env -> string
                                 
    (* value_to_string ?printenvp value -- Returns a printable string
       representation of a value; the optional flag `printenvp`
       (default: `true`) determines whether to include the environment
       in the string representation when called on a closure *)
    val value_to_string : ?printenvp:bool -> value -> string
  end

module Env : ENV =
  struct
    type env = (varid * value ref) list
     and value =
       | Val of expr
       | Closure of (expr * env)

    let empty () : env = [] ;;

    let close (exp : expr) (env : env) : value =
      Closure (exp, env) ;;

    let lookup (env : env) (varname : varid) : value =
      !(List.assoc varname env) ;;

    let extend (env : env) (varname : varid) (loc : value ref) : env =
      try
        let a = lookup env varname in
        List.map (fun (name, value) -> if name = varname then (name, loc) else (name, value)) env
      with
        Not_found -> (varname, loc) :: env;;

    let value_to_string ?(printenvp : bool = true) (v : value) : string = failwith "not implemented";;
  
      (*match v with
      | Val a -> if printenvp then exp_to_concrete_string exp ^ "in environment: " ^ env_to_concrete_string env
                 else exp_to_concrete_string exp;;*)

    let env_to_string (env : env) : string = failwith "not implemented";;
      (*match env with
      | [] -> ""
      | (v, vref) :: [] -> var ^ "=" ^ value_to_string !valref
      | (v, vref) :: tl -> var ^ "=" ^ value_to_string !valref ^ ", " ^ env_to_string tl;;*)
  end
;;


(*......................................................................
  Evaluation functions

  Each of the evaluation functions below evaluates an expression `exp`
  in an enviornment `env` returning a result of type `value`. We've
  provided an initial implementation for a trivial evaluator, which
  just converts the expression unchanged to a `value` and returns it,
  along with "stub code" for three more evaluators: a substitution
  model evaluator and dynamic and lexical environment model versions.

  Each evaluator is of type `expr -> Env.env -> Env.value` for
  consistency, though some of the evaluators don't need an
  environment, and some will only return values that are "bare
  values" (that is, not closures). 

  DO NOT CHANGE THE TYPE SIGNATURES OF THESE FUNCTIONS. Compilation
  against our unit tests relies on their having these signatures. If
  you want to implement an extension whose evaluator has a different
  signature, implement it as `eval_e` below.  *)

(* The TRIVIAL EVALUATOR, which leaves the expression to be evaluated
   essentially unchanged, just converted to a value for consistency
   with the signature of the evaluators. *)


   
let eval_t (exp : expr) (_env : Env.env) : Env.value =
  (* coerce the expr, unchanged, into a value *)
  Env.Val exp ;;

(* The SUBSTITUTION MODEL evaluator -- to be completed *)

let val_to_e (Env.Val value : Env.value) = value ;;

let unopeval (uop : unop) (Env.Val e : Env.value) : Env.value =
  match uop, e with
  | Negate, Num a -> Env.Val (Num (~- a))
  | Negate, Float b -> Env.Val (Float (~-. b))
  | Negate, _ -> raise (EvalError "cannot be negated") ;;

let binopeval (bin : binop) (Env.Val e1 : Env.value) (Env.Val e2 : Env.value) : Env.value = 
  match bin, e1, e2 with
  (* Plus *)
  | Plus, Num x1, Num x2 -> Env.Val (Num (x1 + x2))
  | Plus, Float x1, Float x2 -> Env.Val (Float (x1 +. x2))
  | Plus, _, _ -> raise (EvalError "Cateogry Error")
  (* Minus *)
  | Minus, Num x1, Num x2 -> Env.Val (Num (x1 - x2))
  | Minus, Float x1, Float x2 -> Env.Val (Float (x1 -. x2))
  | Minus, _, _ -> raise (EvalError "Cateogry Error")
  (* Times *)
  | Times, Num x1, Num x2 -> Env.Val (Num (x1 * x2))
  | Times, Float x1, Float x2 -> Env.Val (Float (x1 *. x2))
  | Times, _, _ -> raise (EvalError "Cateogry Error")
  (* Equals *)
  | Equals, Num x1, Num x2 -> Env.Val (Bool (x1 = x2))
  | Equals, Float x1, Float x2 -> Env.Val (Bool (x1 = x2))
  | Equals, String s1, String s2 -> Env.Val (Bool (s1 = s2))
  | Equals, Bool x1, Bool x2 -> Env.Val (Bool (x1 = x2))
  | Equals, _, _ -> raise (EvalError "Cateogry Error")
  (* Less Than *)
  | LessThan, Num x1, Num x2 -> Env.Val (Bool (x1 < x2))
  | LessThan, Float x1, Float x2 -> Env.Val (Bool (x1 < x2))
  | LessThan, _, _ -> raise (EvalError "Cateogry Error")
;; 

   
let eval_s (_exp : expr) (_env : Env.env) : Env.value =
  let rec eval_s (_exp : expr) : Env.value =
    match _exp with
    | Var a -> raise (EvalError ("Unbound" ^ a))                    
    | Num _ | Float _ | String _ | Bool _ | Fun _ | Unassigned  -> Env.Val _exp                                                
    | Unop (un, e1) -> unopeval un (eval_s e1)                
    | Binop (bin, e1, e2) -> binopeval bin (eval_s e1) (eval_s e2)     
    | Conditional (c, c1, c2) -> 
        if (eval_s c = Env.Val (Bool true)) then eval_s c1 
        else eval_s c2            
    | Let (var, e1, e2) -> eval_s (subst var (val_to_e (eval_s e1)) e2)        
    | Letrec (var, e1, e2) -> eval_s (subst var (subst var (Letrec (var, e1, Var var)) e1)e2)  
    | Raise -> raise EvalException          
    | App (e1, e2) -> 
        match eval_s e1 with 
        | Env.Val Fun (a, b) -> eval_s (subst a (val_to_e (eval_s e2)) b)
        | _ -> raise (EvalError "does not work")
  in eval_s _exp ;; 
     
(* The DYNAMICALLY-SCOPED ENVIRONMENT MODEL evaluator -- to be
   completed *)
   
let eval_d (_exp : expr) (_env : Env.env) : Env.value =
  failwith "eval_d not implemented" ;;
       
(* The LEXICALLY-SCOPED ENVIRONMENT MODEL evaluator -- optionally
   completed as (part of) your extension *)
   
let eval_l (_exp : expr) (_env : Env.env) : Env.value =
  failwith "eval_l not implemented" ;;

(* The EXTENDED evaluator -- if you want, you can provide your
   extension as a separate evaluator, or if it is type- and
   correctness-compatible with one of the above, you can incorporate
   your extensions within `eval_s`, `eval_d`, or `eval_l`. *)

let eval_e _ =
  failwith "eval_e not implemented" ;;
  
(* Connecting the evaluators to the external world. The REPL in
   `miniml.ml` uses a call to the single function `evaluate` defined
   here. Initially, evaluate is the trivial evaluator `eval_t`. But
   you can define it to use any of the other evaluators as you proceed
   to implement them. (We will directly unit test the four evaluators
   above, not the evaluate function, so it doesn't matter how it's set
   when you submit your solution.) *)
   
let evaluate = eval_s ;; 
