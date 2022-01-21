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
  | Var v -> SS.singleton v
  | Raise | Unassigned | Num _ | Bool _ -> SS.empty
  | Unop (_u, e) -> free_vars e
  | Binop (_b, ea, eb) -> SS.union (free_vars ea) (free_vars eb)

  | Conditional (ea, eb, ec) -> SS.union (free_vars ea)
                                  (SS.union (free_vars eb) (free_vars ec))

  | Fun (v, e) -> SS.remove v (free_vars e)
  | Let (v, def, body) -> SS.union
                         (SS.remove v (free_vars body))
                         (free_vars def)
  | Letrec (v, def, body) -> SS.remove v
                               (SS.union (free_vars def) (free_vars body))

  | App (ea, eb) -> SS.union (free_vars ea) (free_vars eb)
;;

(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname () : varid =
  let run_ctr = ref 0 in
  let nw_v = "var" ^ string_of_int (!run_ctr) in
  run_ctr := !run_ctr + 1;
  nw_v;;
  
(*......................................................................
  substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
(* Rules: fig 13.4 *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  match exp with
  | Var x -> if x = var_name then repl else Var x (* rules 2 and 3 *)
  | Num _ | Bool _ | Raise | Unassigned -> exp (* all rule 1 *)
  | Unop (op, e) -> Unop (op, subst var_name repl e)
  | Binop (op, ea, eb) -> Binop (op, (* rule 4 *)
                                 subst var_name repl ea,
                                 subst var_name repl eb)
  | Conditional (ea, eb, ec) -> Conditional (
                                    subst var_name repl ea,
                                    subst var_name repl eb,
                                    subst var_name repl ec)
  | Fun (arg, ex) -> if arg = var_name then Fun (arg, ex) (* rule 6 *)
                     else if SS.mem arg (free_vars repl) then (* rule 8 *)
                       let z = new_varname () in
                       Fun (z, subst var_name repl (subst arg (Var z) ex))
                     else (* rule 7 *) 
                       Fun (arg, subst var_name repl ex)
  | App (ea, eb) -> App (subst var_name repl ea, subst var_name repl eb)
  | Let (arg, ea, eb) -> if arg = var_name then (* rule 9 *)
                           Let (arg, subst var_name repl ea, eb)
                         else if SS.mem arg (free_vars repl) then (* rule 11 *)
                           let z = new_varname () in
                           Let (z, subst var_name repl ea,
                                subst var_name repl (subst arg (Var z) eb))
                         else
                           Let (arg, subst var_name repl ea, subst var_name repl eb)


  | Letrec (x, e1, e2) -> if x = var_name then Letrec (x, e1, e2)
                                                      (*^ We can neither substitute 
                                                        in e1 nor e2, since x is 
                                                        bound by the let rec in 
                                                        both*)
                          else
                            if SS.mem x (free_vars repl) then
                              let x' = new_varname () in
                              Letrec (x', subst var_name repl (subst x (Var x') e1),
                                      subst var_name repl (subst x (Var x') e2))
                            (* ^We must replace x with a fresh variable in both e1 
                             and e2 since x is in scope for both. Then, repl can be
                             substituted for var_name in both expressions,
                             since free variable capture will no longer occur 
                             and the meaning of the expressions will not 
                             change based on the substitution. *)
                            else
                              Letrec (x, subst var_name repl e1,
                                      subst var_name repl e2)
(* ^If x is not in the free variables of repl and x is not equal to var_name,
   then we can substitute repl for var_name in both expressions without changing 
   their meanings (abiding by Leibniz's identity of the indiscernibles) *)
;;
  (* failwith "subst not implemented" ;; *)

(*......................................................................
  String representations of expressions
 *)

    
(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let exp_to_concrete_string (exp : expr) : string =
  failwith "exp_to_concrete_string not implemented" ;;


let string_of_binop (b : binop) : string =
  match b with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Equals -> "Equals"
  | LessThan -> "LessThan"

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v -> "Var (" ^ v ^ ")"
  | Num n -> "Num (" ^ string_of_int n ^ ")"
  | Bool b -> "Bool (" ^ string_of_bool b ^ ")"
  | Unop (_u, e) -> "Negate (" ^ exp_to_abstract_string e ^ ")"
  | Binop (b, ea, eb) -> (string_of_binop b)
                         ^ "("
                         ^ (exp_to_abstract_string ea)
                         ^ ", "
                         ^ (exp_to_abstract_string eb)
                         ^ ")"

  | Conditional (ea, eb, ec) -> "Conditional ("
                                ^ (exp_to_abstract_string ea)
                                ^ ", "
                                ^ (exp_to_abstract_string eb)
                                ^", "
                                ^ (exp_to_abstract_string ec)
                                ^ ")"
  | Fun (v, e) -> "Fun ("
                  ^ v
                  ^ ", "
                  ^ (exp_to_abstract_string e)
                  ^ ")"
  | Let (v, ea, eb) -> "Let (" ^ v ^ " -Equal- " ^ (exp_to_abstract_string ea) ^ " -In- " ^ (exp_to_abstract_string eb) ^ ")"
  | Letrec (v, ea, eb) -> "Letrec (" ^ v ^ " -Equal- " ^ (exp_to_abstract_string ea) ^ " -In- " ^ (exp_to_abstract_string eb) ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (ea, eb) -> "App (" ^ (exp_to_abstract_string ea) ^ ", " ^ (exp_to_abstract_string eb) ^ ")"
;;

  (* failwith "exp_to_abstract_string not implemented" ;;  *)
