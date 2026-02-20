open Ast
open Cli_ast

(******************************************************************************)
(*                Conversion between values and expressions                   *)
(******************************************************************************)

let is_val = function
  | BoolConst _ 
  | IntConst _
  | IntVal _
  | UintVal _
  | AddrConst _ -> true
  | _ -> false

let exprval_of_expr = function
  | BoolConst b   -> (Bool b)
  | IntConst n when n>=0 -> (Uint n)
  | IntConst n    -> (Int n)
  | IntVal n      -> (Int n)
  | UintVal n     -> (Uint n)
  | AddrConst s   -> (Addr s)
  | _ -> failwith ("expression is not a value")

let exprval_of_expr_typechecked (e : expr) (t : base_type)= match e,t with
  | BoolConst b,  BoolBT            -> Bool b
  | IntConst n,   IntBT             -> Int n
  | IntConst n,   UintBT when n>=0  -> Uint n
  | IntVal n,     IntBT             -> Int n
  | UintVal n,    UintBT            -> Uint n
  | AddrConst s,  AddrBT _          -> Addr s
  | AddrConst s,  ContractBT _      -> Addr s
  | _ -> failwith ("type mismatch")

let val_type_match (e : expr) (v : exprval) = match e,v with  
  | BoolConst _,  Bool _ 
  | IntConst _,   Int _
  | IntVal _,     Int _
  | UintVal _,    Uint _
  | AddrConst _,  Addr _ -> true
  | IntConst n,   Uint _ when n>=0 -> true
  | _ -> failwith ("type mismatch")

let int_of_expr e = match e with 
  | IntConst n 
  | IntVal n
  | UintVal n -> n
  | _ -> failwith "IntConst was expected"

let bool_of_expr e = match e with 
  | BoolConst b -> b
  | _  -> failwith "True or False was expected"

let addr_of_expr e = match e with 
  | AddrConst a -> a
  | IntConst n 
  | UintVal n -> "0x" ^ string_of_int n
  | _ -> failwith "AddrConst was expected"

let expr_of_exprval = function
  | Bool b -> BoolConst b
  | Int n  -> IntVal n
  | Uint n -> UintVal n
  | Addr b -> AddrConst b
  | Map _ -> failwith "step_expr: wrong type checking of map?"

let addr_of_exprval v = match v with 
  | Addr a -> a
  | Bool _ -> failwith "value has type bool but an address was expected"
  | Int _ -> failwith "value has type int but an address was expected"
  | Uint _ -> failwith "value has type uint but an address was expected"
  | Map _ -> failwith "value has type map but an address was expected"


(******************************************************************************)
(*                                   List utilities                           *)
(******************************************************************************)

let rec last = function
    [] -> failwith "last on empty list"
  | [st] -> st
  | _::l -> last l

let find_index f l =  
  let rec find_index_helper (b,i) f = function 
    [] -> (b,i)
  | x::l -> if b then (b,i)
            else if f x then (true,i) 
            else find_index_helper (b,i+1) f l 
  in 
    let (b,i) = find_index_helper (false,0) f l in
    if b then Some i else None

(******************************************************************************)
(*                     Read file, and output it to a string                   *)
(******************************************************************************)

let read_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch; s



(******************************************************************************)
(*                         Read given contract from file                      *)
(******************************************************************************)

let read_contract_in_file contract_name filename =
  let content = read_file filename in
  let len = String.length content in

  let is_space = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false in

  (* skip whitespace *)
  let rec skip_spaces i =
    if i < len && is_space content.[i] then skip_spaces (i + 1) else i
  in

  (* skip comments *)
  let rec skip_comments i =
    if i + 1 < len && content.[i] = '/' && content.[i + 1] = '/' then
      let rec skip_line j =
        if j < len && content.[j] <> '\n' then skip_line (j + 1) else j
      in
      skip_comments (skip_line (i + 2))
    else if i + 1 < len && content.[i] = '/' && content.[i + 1] = '*' then
      let rec skip_block j =
        if j + 1 >= len then failwith "Unterminated block comment"
        else if content.[j] = '*' && content.[j + 1] = '/' then j + 2
        else skip_block (j + 1)
      in
      skip_comments (skip_block (i + 2))
    else
      i
  in

  (* look for: contract <name> *)
  let rec find_contract i =
    let i = skip_comments (skip_spaces i) in
    if i + 8 >= len then
      failwith ("Contract " ^ contract_name ^ " not found")
    else if
      String.sub content i 8 = "contract"
      && is_space content.[i + 8]
    then
      let j = skip_spaces (i + 8) in
      let k = j + String.length contract_name in
      if k <= len && String.sub content j (String.length contract_name) = contract_name
      then i
      else find_contract (i + 1)
    else
      find_contract (i + 1)
  in

  let start = find_contract 0 in

  (* find opening brace *)
  let rec find_open i =
    let i = skip_comments i in
    if i >= len then failwith "Missing '{' in contract"
    else if content.[i] = '{' then i
    else find_open (i + 1)
  in

  let open_brace = find_open start in

  (* match braces *)
  let rec find_close i depth =
    if i >= len then failwith "Unbalanced braces"
    else
      match content.[i] with
      | '{' -> find_close (i + 1) (depth + 1)
      | '}' ->
          if depth = 1 then i
          else find_close (i + 1) (depth - 1)
      | _ -> find_close (i + 1) depth
  in

  let close_brace = find_close (open_brace + 1) 1 in
  String.sub content start (close_brace - start + 1)


(******************************************************************************)
(* Get the list of contract names in a file                                   *)
(******************************************************************************)

let contract_names_in_file filename =
  let s = read_file filename in
  let len = String.length s in

  let is_space = function
    | ' ' | '\t' | '\n' | '\r' -> true
    | _ -> false
  in

  let is_ident_char = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
    | _ -> false
  in

  let is_ident_start = function
    | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
    | _ -> false
  in

  (* skip // and /* */ comments *)
  let rec skip_comments i =
    if i + 1 < len && s.[i] = '/' && s.[i + 1] = '/' then
      let rec skip_line j =
        if j < len && s.[j] <> '\n' then skip_line (j + 1) else j
      in
      skip_comments (skip_line (i + 2))
    else if i + 1 < len && s.[i] = '/' && s.[i + 1] = '*' then
      let rec skip_block j =
        if j + 1 >= len then failwith "Unterminated block comment"
        else if s.[j] = '*' && s.[j + 1] = '/' then j + 2
        else skip_block (j + 1)
      in
      skip_comments (skip_block (i + 2))
    else
      i
  in

  (* skip string literals *)
  let rec skip_string i =
    if i >= len then failwith "Unterminated string literal"
    else if s.[i] = '"' then i + 1
    else skip_string (i + 1)
  in

  let rec skip_spaces i =
    if i < len && is_space s.[i] then skip_spaces (i + 1) else i
  in

  let read_ident i =
    let rec aux j =
      if j < len && is_ident_char s.[j] then aux (j + 1) else j
    in
    let j = aux i in
    String.sub s i (j - i), j
  in

  let rec scan i acc =
    if i >= len then
      List.rev acc
    else
      let i = skip_comments i in
      if i >= len then List.rev acc else
      match s.[i] with
      | '"' ->
          scan (skip_string (i + 1)) acc
      | _ ->
          (* check for keyword "contract" with proper boundaries *)
          if i + 8 < len
             && s.[i] = 'c'
             && String.sub s i 8 = "contract"
             && (i = 0 || not (is_ident_char s.[i - 1]))
             && i + 8 < len
             && is_space s.[i + 8]
          then
            let j = skip_spaces (i + 8) in
            if j < len && is_ident_start s.[j] then
              let name, k = read_ident j in
              scan k (name :: acc)
            else
              scan (i + 1) acc
          else
            scan (i + 1) acc
  in

  scan 0 []



(******************************************************************************)
(* Read line from standard input, and output it to a string                   *)
(******************************************************************************)

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

let parse_expr (s : string) : expr =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.expr_eof Lexer.read_token lexbuf in
  ast

let parse_cmd (s : string) : cmd =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.cmd_eof Lexer.read_token lexbuf in
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
(*                 Transform inline declarations into blocks                  *)
(******************************************************************************)

let rec gather_decls = function
  | Decl d -> [d]
  | Seq(c1,c2) -> gather_decls c1 @ gather_decls c2
  | _ -> []

let rec purge_decls = function
  | Decl _ -> Skip
  | Seq(Decl _,c2) -> purge_decls c2
  | Seq(c1,Decl _) -> purge_decls c1
  | Seq(c1,c2) -> Seq(purge_decls c1, purge_decls c2)
  | Block(vdl,c) -> Block(vdl @ gather_decls c, purge_decls c)
  | _ as c -> c 

let rec blockify_cmd c = 
  let vdl = gather_decls c in
  let c' = purge_decls c in
  if vdl=[] then blockify_subterms c'
  else Block(vdl, blockify_subterms c')

and blockify_subterms = function
  | Block(vdl,c) -> Block(vdl, blockify_subterms c) 
  | Seq(c1,c2) -> Seq(blockify_subterms c1, blockify_subterms c2) 
  | If(e,c1,c2) -> If(e, blockify_cmd c1, blockify_cmd c2)
  | _ as c -> c

let blockify_fun = function
  | Constr (al,c,p) -> Constr (al,blockify_cmd c,p)
  | Proc (f,al,c,v,m,ret) -> Proc(f,al,blockify_cmd c,v,m,ret)

let blockify_contract (Contract(c,el,vdl,fdl)) =
  Contract(c,el,vdl,List.map blockify_fun fdl)

(******************************************************************************)
(*            Transform unknown types into enum or contract types             *)
(******************************************************************************)

let exists_enum (enums : enum_decl list) (name : ide) = 
  List.exists (fun (Enum(x,_)) -> x=name) enums

let resolve_unknown_base_type (enums : enum_decl list) (bt : base_type) : base_type = match bt with
  | UnknownBT en when exists_enum enums en -> EnumBT en
  | UnknownBT en                           -> ContractBT en (* TODO: check if contract name exists in file?*)
  | _ as other -> other

let resolve_unknown_decls (enums : enum_decl list) (vdl : var_decl list) : var_decl list = List.map (
  fun (vd:var_decl) -> match vd.ty with
    | VarT(bt)   -> { vd with ty = VarT(resolve_unknown_base_type enums bt) } 
    | MapT(bt1,bt2) -> { vd with ty = MapT(resolve_unknown_base_type enums bt1, resolve_unknown_base_type enums bt2) }
  ) 
  vdl 

let resolve_unknown_local_decls (enums : enum_decl list) (vdl : local_var_decl list) : local_var_decl list = List.map (
  fun vd -> match vd.ty with
    | VarT(bt)   -> { vd with ty = VarT(resolve_unknown_base_type enums bt) } 
    | MapT(bt1,bt2) -> { vd with ty = MapT(resolve_unknown_base_type enums bt1, resolve_unknown_base_type enums bt2) }
  ) 
  vdl 

(* TODO: transform UnknownCast into EnumCast or ContractCast *)

let rec resolve_unknown_expr enums = function
  | BoolConst b -> BoolConst b
  | IntConst n -> IntConst n
  | IntVal n -> IntVal n
  | UintVal n -> UintVal n
  | AddrConst a -> AddrConst a
  | This -> This
  | BlockNum -> BlockNum
  | Var x -> Var x
  | MapR(e1,e2) -> MapR(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | BalanceOf e -> BalanceOf(resolve_unknown_expr enums e)
  | Not e -> Not(resolve_unknown_expr enums e)
  | And(e1,e2) -> And(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2) 
  | Or(e1,e2) -> Or(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Add(e1,e2) -> Add(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Sub(e1,e2) -> Sub(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Mul(e1,e2) -> Mul(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Div(e1,e2) -> Div(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Eq(e1,e2) -> Eq(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Neq(e1,e2) -> Neq(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Leq(e1,e2) -> Leq(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Lt(e1,e2) -> Lt(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Geq(e1,e2) -> Geq(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Gt(e1,e2) -> Gt(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | IfE(e1,e2,e3) -> IfE(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2,resolve_unknown_expr enums e3)
  | IntCast(e) -> IntCast(resolve_unknown_expr enums e)
  | UintCast(e) -> UintCast(resolve_unknown_expr enums e)
  | AddrCast(e) -> AddrCast(resolve_unknown_expr enums e)
  | PayableCast(e) -> PayableCast(resolve_unknown_expr enums e)
  | EnumOpt(x,o) -> EnumOpt(x,o)
  | UnknownCast(x,e) when exists_enum enums x -> EnumCast(x,e) 
  | UnknownCast(x,e) -> ContractCast(x,e)
  | EnumCast(_) -> assert(false) (* should not happen during preprocessing *)
  | ContractCast(_) -> assert(false) (* should not happen during preprocessing *) 
  | FunCall(e_to,f,e_value,e_args) -> FunCall(resolve_unknown_expr enums e_to,f,resolve_unknown_expr enums e_value,List.map (fun e -> resolve_unknown_expr enums e) e_args) 
  | ExecFunCall(_) -> assert(false) (* should not happen during preprocessing *) 
 
let rec resolve_unknown_cmd enums = function
  | Skip          -> Skip
  | Decl _        -> assert(false) (* should not happen after blockify *)
  | Assign(x,e)   -> Assign(x,resolve_unknown_expr enums e)
  | Decons(xl,e)  -> Decons(xl, resolve_unknown_expr enums e)
  | MapW(x,ek,ev) -> MapW(x,resolve_unknown_expr enums ek,resolve_unknown_expr enums ev)
  | Seq(c1,c2)    -> Seq(resolve_unknown_cmd enums c1,resolve_unknown_cmd enums c2)
  | If(e,c1,c2)   -> If(resolve_unknown_expr enums e,resolve_unknown_cmd enums c1,resolve_unknown_cmd enums c2)
  | Send(e1,e2)   -> Send(resolve_unknown_expr enums e1,resolve_unknown_expr enums e2)
  | Req(e)        -> Req(resolve_unknown_expr enums e)
  | Return(el)    -> Return(List.map (fun e -> resolve_unknown_expr enums e) el)
  | ExecBlock(_)  -> assert(false)
  | ProcCall(e_to,f,e_value,e_args) -> ProcCall(resolve_unknown_expr enums e_to,f,resolve_unknown_expr enums e_value,List.map (fun e -> resolve_unknown_expr enums  e) e_args) 
  | ExecProcCall(_) -> assert(false)
  | Block(vdl,c)  -> Block(resolve_unknown_local_decls enums vdl, resolve_unknown_cmd enums c) 

let resolve_unknown_fun enums = function
  | Constr (al,c,p) -> Constr (resolve_unknown_local_decls enums al,resolve_unknown_cmd enums c,p)
  | Proc (f,al,c,v,m,ret) -> Proc(f,resolve_unknown_local_decls enums al,resolve_unknown_cmd enums c,v,m,ret)

let resolve_unknown_contract (Contract(c,enums,vdl,fdl)) =
  Contract(c,enums,resolve_unknown_decls enums vdl, List.map (fun fd -> resolve_unknown_fun enums fd) fdl)


(******************************************************************************)
(*                                  Preprocess contract                       *)
(******************************************************************************)

let preprocess_contract c = c |> blockify_contract |> resolve_unknown_contract 