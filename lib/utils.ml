open Ast
open Types

(******************************************************************************)
(*                                   File utilities                           *)
(******************************************************************************)

(* read file, and output it to a string *)

let read_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch; s

(* read line from standard input, and output it to a string *)

let read_line () =
  try Some(read_line())
  with End_of_file -> None
;;

let read_lines filename =
  let chan = open_in filename in
  let rec loop acc =
    match input_line chan with
    | line -> loop (line :: acc)
    | exception End_of_file ->
        close_in chan;
        List.rev acc
  in
  loop []

(******************************************************************************)
(*                                   Parsing utilities                        *)
(******************************************************************************)

let parse_cmd (s : string) : cmd =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.cmd_test Lexer.read_token lexbuf in
  ast

let parse_contract (s : string) : contract =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.contract Lexer.read_token lexbuf in
  ast

let parse_transaction (s : string) : transaction =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.transaction Lexer.read_token lexbuf in
  ast

let parse_cli_cmd (s : string) : cli_cmd =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.cli_cmd Lexer.read_token lexbuf in
  ast

(******************************************************************************)
(*                            Getting set of variables                        *)
(******************************************************************************)

let rec union l1 l2 = match l1 with
    [] -> l2
  | x::l1' -> (if List.mem x l2 then [] else [x]) @ union l1' l2

let rec vars_of_expr = function
    True
  | False
  | IntConst _
  | AddrConst _
  | This -> []               
  | Var x -> [x]
  | BalanceOf e
  | Not e -> vars_of_expr e
  | And(e1,e2) 
  | Or(e1,e2) 
  | Add(e1,e2)
  | Sub(e1,e2)
  | Mul(e1,e2) 
  | Eq(e1,e2) 
  | Neq(e1,e2) 
  | Leq(e1,e2) 
  | Le(e1,e2)
  | Geq(e1,e2) 
  | Ge(e1,e2) -> union (vars_of_expr e1) (vars_of_expr e2)                    

and vars_of_cmd = function
    Skip -> []
  | Assign(x,e) -> union [x] (vars_of_expr e)
  | Seq(c1,c2) -> union (vars_of_cmd c1) (vars_of_cmd c2)
  | If(e,c1,c2) -> union (vars_of_expr e) (union (vars_of_cmd c1) (vars_of_cmd c2))
  | Send(e1,e2) -> union (vars_of_expr e1) (vars_of_expr e2)
  | Req(e) -> vars_of_expr e                    
  | Call(f,el) -> union [f] (List.fold_left (fun acc e -> union acc (vars_of_expr e)) [] el)
  | ExecCall(c) -> vars_of_cmd c
  | Block(_,c) -> vars_of_cmd c
  | ExecBlock(c) -> vars_of_cmd c

let vars_of_contract (Contract(_,vdl,_)) : ide list = 
  List.fold_left (fun acc vd -> match vd with 
    IntVar x | BoolVar x | AddrVar x -> x::acc ) [] vdl 


(******************************************************************************)
(*                         Converting syntax to strings                       *)
(******************************************************************************)

let string_of_exprval = function
    Bool b -> string_of_bool b
  | Int n  -> string_of_int n
  | Addr s -> s

let string_of_modifier = function
  | Public -> "public"
  | Private -> "private"

let string_of_args = List.fold_left (fun s a -> s ^ (if s<>"" then "," else "") ^ (string_of_exprval a)) ""

let rec string_of_expr = function
    True -> "true"
  | False -> "false"
  | IntConst n -> string_of_int n
  | AddrConst a -> "\"" ^ a ^ "\""
  | This -> "this"
  | Var x -> x
  | BalanceOf e -> string_of_expr e ^ ".balance"
  | Not e -> "!" ^ string_of_expr e
  | And(e1,e2) -> string_of_expr e1 ^ " && " ^ string_of_expr e2
  | Or(e1,e2) -> string_of_expr e1 ^ " || " ^ string_of_expr e2
  | Add(e1,e2) -> string_of_expr e1 ^ "+" ^ string_of_expr e2
  | Sub(e1,e2) -> string_of_expr e1 ^ "-" ^ string_of_expr e2
  | Mul(e1,e2) -> string_of_expr e1 ^ "*" ^ string_of_expr e2
  | Eq(e1,e2) -> string_of_expr e1 ^ "==" ^ string_of_expr e2
  | Neq(e1,e2) -> string_of_expr e1 ^ "!=" ^ string_of_expr e2
  | Leq(e1,e2) -> string_of_expr e1 ^ "<=" ^ string_of_expr e2
  | Le(e1,e2) -> string_of_expr e1 ^ "<" ^ string_of_expr e2                    
  | Geq(e1,e2) -> string_of_expr e1 ^ ">=" ^ string_of_expr e2
  | Ge(e1,e2) -> string_of_expr e1 ^ ">" ^ string_of_expr e2                    

and string_of_cmd = function
    Skip -> "skip;"
  | Assign(x,e) -> x ^ "=" ^ string_of_expr e ^ ";"
  | Seq(c1,c2) -> string_of_cmd c1 ^ " " ^ string_of_cmd c2
  | If(e,c1,c2) -> "if (" ^ string_of_expr e ^ ") {" ^ string_of_cmd c1 ^ "} else {" ^ string_of_cmd c2 ^ "}"
  | Send(e1,e2) -> string_of_expr e1 ^ ".transfer(" ^ (string_of_expr e2) ^ ");"
  | Req(e) -> "require " ^ string_of_expr e ^ ";"
  | Call(f,el) -> f ^ "(" ^ (List.fold_left (fun acc e -> acc ^ "," ^ string_of_expr e) "" el) ^ ")"
  | ExecCall(c) -> "exec{" ^ string_of_cmd c ^ "}"
  | Block(vdl,c) -> "{" 
    ^ List.fold_left (fun s d -> s ^ (if s<>"" then "; " else "") ^ string_of_var_decl d) "" vdl ^ ";" 
    ^ string_of_cmd c 
    ^ "}"
  | ExecBlock(c) -> "{" 
    ^ string_of_cmd c 
    ^ "}"

and string_of_var_decl = function
  | IntVar(x) -> "int " ^ x
  | BoolVar(x) -> "bool " ^ x
  | AddrVar(x) -> "address " ^ x

let string_of_var_decls = List.fold_left (fun s d -> s ^ (if s<>"" then ";\n  " else "  ") ^ string_of_var_decl d) ""

let string_of_fun_decl = function Proc(f,a,c,m) -> 
    if f="constructor" then
      "constructor " ^ f ^ "(" ^ (string_of_var_decls a) ^ ") {" ^ string_of_cmd c ^ "}\n"
    else
    "function " ^ f ^ "(" ^ (string_of_var_decls a) ^ ") " ^
    string_of_modifier m ^ " " ^ 
    "{" ^ string_of_cmd c ^ "}\n"

let string_of_fun_decls = List.fold_left (fun s d -> s ^ (if s<>"" then "  " else " ") ^ string_of_fun_decl d) ""

let string_of_contract (Contract(c,vdl,fdl)) = 
  "contract " ^ c ^ 
  " {\n" ^ 
  (let s = string_of_var_decls vdl in if s="" then "" else s ^ ";\n ") ^ 
  (string_of_fun_decls fdl) ^ 
  " }"

let string_of_env e vl = 
  let rec helper e vl = match vl with 
  | [] -> ""
  | x::vl' -> try (x ^ "->" ^
    match e x with 
      | Bool b -> string_of_bool b
      | Int  n -> string_of_int n
      | Addr a -> a
    )
    with _ -> helper e vl' 
  in "{" ^ helper e vl ^ "}"

let string_of_envstack el vl = 
  let rec helper el vl = match el with
    [] -> ""
  | [e] -> (string_of_env e vl)
  | e::el' -> (string_of_env e vl) ^ ";" ^ (helper el' vl)
in "[" ^ (helper el vl) ^ "]" 

let rec range a b = if b<a then [] else a::(range (a+1) b);;

let string_of_storage (stg : ide -> exprval) (xl : ide list) =
  List.fold_left (fun acc x -> acc ^ x ^ "=" ^ (string_of_exprval (stg x)) ^ "; ") "" xl

let string_of_account_state accst =
  "{ " ^
  "balance=" ^ string_of_int accst.balance ^ "; " ^
  (match accst.code with 
  | None -> ""
  | Some src -> string_of_storage accst.storage (vars_of_contract src)) ^
  "}"

let string_of_accounts (st : sysstate) =
  "[" ^ 
  (List.fold_left (fun acc a -> acc ^ a ^ " -> " ^ (string_of_account_state (st.accounts a)) ^ " ") "" st.active) ^ 
  "]"

(* TODO: add storage variables *)

let string_of_sysstate (evl : ide list) (st : sysstate) =
  "accounts: " ^ 
  string_of_accounts st ^
  if evl=[] then "" else 
  ("\n" ^
  "envstack: " ^
  string_of_envstack st.stackenv evl)

let string_of_execstate evl = function
  | St st -> string_of_sysstate evl st
  | Cmd (c,st,a) -> 
      "cmd: " ^ (string_of_cmd c) ^ "\n" ^ 
      (string_of_sysstate evl st) ^ "," ^ a 

let string_of_trace stl = match stl with
  [] -> ""
| St _::_ -> ""
| Cmd (c,_,_)::_ -> let evl = vars_of_cmd c in  
  let rec helper stl = (match stl with
    [] -> ""
  | [st] -> (string_of_execstate evl st)
  | st::l -> (string_of_execstate evl st) ^ "\n--->\n" ^ helper l)
in helper stl

let string_of_transaction (Tx(sender,rcv,f,al)) =
  sender ^ ":" ^ rcv ^ "." ^ f ^ string_of_args al


(******************************************************************************)
(*                         Manipulating execution traces                      *)
(******************************************************************************)

let rec last = function
    [] -> failwith "last on empty list"
  | [st] -> st
  | _::l -> last l

let print_sysstate_id (st : sysstate) : sysstate =
  st |> string_of_sysstate [] |> print_string |> fun _ -> st

let print_trace_and_return_last_sysstate tr = 
  let st = last_sysstate tr in
  tr |> string_of_trace |> print_string |> fun _ -> st
