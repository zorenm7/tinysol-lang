(******************************************************************************)
(*                                    Tinysol CLI                             *)
(******************************************************************************)

open Ast
open Types
open Utils
open Main


let exec_cli_cmd (cc : cli_cmd) (st : sysstate) : sysstate = match cc with
  | Faucet(a,n) -> faucet a n st
  | Deploy(a,filename) -> 
      let c = filename |> read_file |> parse_contract 
      in st |> deploy_contract a c
  | ExecTx tx -> st |> exec_tx 1000 tx

let string_of_cli_cmd = function 
  | Faucet(a,n) -> "faucet " ^ a ^ " " ^ string_of_int n
  | Deploy(a,filename) -> "deploy " ^ a ^ " " ^ filename
  | ExecTx tx -> string_of_transaction tx

let exec_cli_cmd_list (ccl : cli_cmd list) (st : sysstate) = 
  List.fold_left 
  (fun sti cc -> 
    print_endline (string_of_sysstate [] sti ^ "\n--- " ^ string_of_cli_cmd cc ^ " --->"); 
    exec_cli_cmd cc sti)
  st
  ccl
