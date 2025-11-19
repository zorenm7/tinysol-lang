(******************************************************************************)
(*                                    Tinysol CLI                             *)
(******************************************************************************)

open Ast
open Types
open Utils
open Main

let string_of_cli_cmd = function 
  | Faucet(a,n) -> "faucet " ^ a ^ " " ^ string_of_int n
  | Deploy(tx,filename) -> "deploy " ^ string_of_transaction tx ^ " " ^ filename
  | CallFun tx -> string_of_transaction tx
  | Assert(a,x,ev) -> "assert " ^ a ^ " " ^ x ^ " = " ^ string_of_exprval ev 

let is_empty_or_comment (s : string) =
  let len = String.length s in
  (* skip leading spaces *)
  let rec skip i =
    if i >= len then true                      (* string is only spaces → empty *)
    else if s.[i] = ' ' then skip (i + 1)
    else if i + 1 < len && s.[i] = '/' && s.[i+1] = '/' then true
    else false
  in
  skip 0

let is_assert = function 
  | Assert(_) -> true
  | _ -> false

let exec_cli_cmd (cc : cli_cmd) (st : sysstate) : sysstate = match cc with
  | Faucet(a,n) -> faucet a n st
  | Deploy(tx,filename) -> 
      let src = filename |> read_file 
      in st |> deploy_contract tx src
  | CallFun tx -> st |> exec_tx 1000 tx
  | Assert(a,x,ev) ->
      let v = 
        if x="balance" then Int(lookup_balance a st) 
        else lookup_var a x st
      in 
      if v = ev then st
      else failwith ("assertion violation: " ^ string_of_cli_cmd cc) 

let exec_cli_cmd_list (verbose : bool) (ccl : cli_cmd list) (st : sysstate) = 
  List.fold_left 
  (fun sti cc -> 
    if verbose && not (is_assert cc) then 
      print_endline (string_of_sysstate [] sti ^ "\n--- " ^ string_of_cli_cmd cc ^ " --->")
    else ();  
    try 
      exec_cli_cmd cc sti
    with ex -> print_endline (string_of_sysstate [] sti); raise ex)
  st
  ccl
