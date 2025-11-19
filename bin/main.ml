open TinysolLib.Main
open TinysolLib.Utils
open TinysolLib.Cli

;;

match Array.length(Sys.argv) with
(* parse_cmd *) 
  2 when Sys.argv.(1)="parse_cmd" -> (match read_line() with
      Some s when s<>"" -> s |> parse_cmd |> string_of_cmd |> print_string
    | _ -> print_newline())
(* exec_cmd *)
| 3 when Sys.argv.(1)="exec_cmd" -> (match read_line() with
    | Some s when s<>"" -> s |> parse_cmd 
      |> fun c -> trace_cmd (int_of_string Sys.argv.(2)) c "0xCAFE" init_sysstate
      |> string_of_trace |> print_string
    | _ -> print_newline())
(* parse_contract *) 
| 3 when Sys.argv.(1)="parse_contract" -> (match read_file Sys.argv.(2) with
      "" -> print_newline()
    | s -> s |> parse_contract |> string_of_contract |> print_string)
(* unittest *)
| 3 when Sys.argv.(1)="unittest" ->
  Sys.argv.(2) |> read_lines 
  |> List.filter (fun s -> not (is_empty_or_comment s)) 
  |> List.map parse_cli_cmd 
  |> fun l -> exec_cli_cmd_list true l init_sysstate 
  |> string_of_sysstate [] |> print_string
(* wrong usage *)      
| _ -> print_string "Usage:
  dune exec tinysol parse_cmd   : parses cmd in stdin
  dune exec tinysol exec_cmd <n_steps>   : executes n_steps of cmd in stdin
  dune exec tinysol parse_contract <file>   : parses contract in file
  dune exec tinysol unittest <file> : executes CLI commands from file 
"
