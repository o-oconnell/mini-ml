(* 
                         CS 51 Final Project
                    MiniML -- Read-Eval-Print Loop
 *)

module Ev = Evaluation ;;
module MP = Miniml_parse ;;
module ML = Miniml_lex ;;
module Ex = Expr ;;


open Printf ;;

(* str_to_exp : string -> expr
   Return the expression specified by the string using the Miniml
   parser. *)
let str_to_exp (str: string) : Ex.expr =
  let lexbuf = Lexing.from_string str in
  let exp = MP.input ML.token lexbuf in
  exp ;;

(* repl : unit -> unit
   Read-eval-print loop for MiniML. *)
let repl () =
  (* lexical analyzer buffer from stdin *)
  let lexbuf = Lexing.from_channel stdin in
  (* set up the initial environment *)
  let env = Ev.Env.empty () in
  printf "Entering %s...\n" Sys.argv.(0);
  flush stdout;
  while true do
    (try
        (* prompt *)
        printf "<== ";
        flush stdout;
        
        (* read and parse an expression from the input *)
        let exp = MP.input ML.token lexbuf in
        
        (* evaluate it *)
        let res = Ev.evaluate exp env in
           
        (* print the result; in this initial version, the trivial
           evaluator just returns the expression unchanged as an
           element of the Env.value type (found in expr.ml), so we
           just extract the expr back out and print it *)
        match res with
        | Val resexp ->
           printf "==> %s\n" (Ex.exp_to_abstract_string resexp)
        | _ -> failwith "not handling other cases yet"
           
      with
      | Parsing.Parse_error -> printf "xx> parse error\n"
      | Ev.EvalError msg -> printf "xx> evaluation error: %s\n" msg
      | Ev.EvalException -> printf "xx> evaluation exception\n"
      | End_of_file -> printf "Goodbye.\n"; exit 0
    );
    flush stdout
  done
;;
        
(* Run REPL if called from command line *)

try
  let _ = Str.search_forward (Str.regexp "miniml\\.\\(byte\\|native\\)") (Sys.argv.(0)) 0 in
  repl ()
with Not_found -> () ;;
