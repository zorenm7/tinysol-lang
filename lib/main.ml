open Ast
open Types
open Utils


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
  | Proc (f,al,c,v,p,r) -> Proc(f,al,blockify_cmd c,v,p,r)

let blockify_contract (Contract(c,el,vdl,fdl)) =
  Contract(c,el,vdl,List.map blockify_fun fdl)


(******************************************************************************)
(*              Retrieving contracts and functions from state                 *)
(******************************************************************************)

let find_fun_in_contract (Contract(_,_,_,fdl)) (f : ide) : fun_decl option =
  List.fold_left 
  (fun acc fd -> match fd with
    | Constr(_) -> if acc=None && f="constructor" then Some fd else acc  
    | Proc(g,_,_,_,_,_) -> if acc=None && f=g then Some fd else acc
  )
  None
  fdl

let find_fun_in_sysstate (st : sysstate) (a : addr) (f : ide) = 
  if not (exists_account st a) then
    failwith ("address " ^ a ^ " does not exist")
  else match (st.accounts a).code with
    | None -> None  (* "address " ^ a ^ " is not a contract address" *)
    | Some(c) -> find_fun_in_contract c f 

let get_cmd_from_fun = function
  | (Constr(_,c,_)) -> c
  | (Proc(_,_,c,_,_,_)) -> c

let get_var_decls_from_fun = function
  | (Constr(vdl,_,_)) -> vdl
  | (Proc(_,vdl,_,_,_,_)) -> vdl

let bind_fargs_aargs (xl : var_decl list) (vl : exprval list) : env =
  if List.length xl <> List.length vl then
    failwith "exec_tx: length mismatch between formal and actual arguments"
  else 
  List.fold_left2 
  (fun acc x_decl v -> match (x_decl,v) with 
   | ((VarT(IntBT,_),x), Int _)
   | ((VarT(BoolBT,_),x), Bool _) 
   | ((VarT(AddrBT _,_),x), Addr _) -> bind x v acc
   | ((VarT(UintBT,_),x), Int n) when n>=0 -> bind x v acc
   | ((MapT(_),_),_) -> failwith "Maps cannot be passed as function parameters"
   | _ -> failwith "exec_tx: type mismatch between formal and actual arguments") 
  botenv 
  xl 
  vl 

(******************************************************************************)
(*                      Small-step semantics of expressions                   *)
(******************************************************************************)

exception TypeError of string
exception NoRuleApplies

let rec step_expr (e,st) = match e with
  | e when is_val e -> raise NoRuleApplies

  | This -> (expr_of_exprval (Addr (List.hd(st.callstack)).callee), st)

  | BlockNum -> (IntConst st.blocknum, st)

  | Var x -> (expr_of_exprval (Option.get (lookup_var x st)), st)  

  | MapR(Var x,e2) when is_val e2 -> (match Option.get (lookup_var x st) with
    | Map m -> (expr_of_exprval (m (exprval_of_expr e2)), st)
    | _ -> failwith "step_expr: wrong type checking of map?")
  | MapR(Var x,e2) ->
    let (e2', st') = step_expr (e2, st) in (MapR(Var x,e2'), st')
  | MapR(e1,e2) ->
    let (e1', st') = step_expr (e1, st) in (MapR(e1',e2), st')

  | BalanceOf e when is_val e -> 
    let b = addr_of_expr e in (IntConst (lookup_balance b st), st)
  | BalanceOf e -> 
    let (e', st') = step_expr (e, st) in (BalanceOf e', st')

  | Not(e) when is_val e -> 
    let b = bool_of_expr e in (BoolConst (not b), st)
  | Not(e) -> 
    let (e', st') = step_expr (e, st) in (Not e', st')

  | And(e1,e2) when is_val e1 && is_val e2 ->
    let (b1,b2) = bool_of_expr e1,bool_of_expr e2 in 
    (BoolConst (b1 && b2), st)         
  | And(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (And(e1,e2'), st')
  | And(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (And(e1',e2), st')

  | Or(e1,e2) when is_val e1 && is_val e2 ->
    let (b1,b2) = bool_of_expr e1,bool_of_expr e2 in 
    (BoolConst(b1 || b2), st)
  | Or(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Or(e1,e2'), st')
  | Or(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Or(e1',e2), st')

  | Add(e1,e2) when is_val e1 && is_val e2 ->
    let (n1,n2) = int_of_expr e1,int_of_expr e2 in 
    (IntConst (n1+n2), st)         
  | Add(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Add(e1,e2'), st')
  | Add(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Add(e1',e2), st')

  | Sub(e1,e2) when is_val e1 && is_val e2 ->
    let (n1,n2) = int_of_expr e1,int_of_expr e2 in 
    (IntConst (n1-n2), st)         
  | Sub(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Sub(e1,e2'), st')
  | Sub(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Sub(e1',e2), st')

  | Mul(e1,e2) when is_val e1 && is_val e2 ->
    let (n1,n2) = int_of_expr e1,int_of_expr e2 in 
    (IntConst (n1*n2), st)         
  | Mul(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Mul(e1,e2'), st')
  | Mul(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Mul(e1',e2), st')

  | Eq(e1,e2) when is_val e1 && is_val e2 -> (match e1,e2 with
      | (IntConst n1,IntConst n2) -> (BoolConst(n1=n2), st)
      | (AddrConst a1,AddrConst a2) -> (BoolConst(a1=a2), st)
      | (BoolConst b1,BoolConst b2) -> (BoolConst(b1=b2), st)
      | _ -> raise (TypeError "Eq"))
  | Eq(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Eq(e1,e2'), st')
  | Eq(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Eq(e1',e2), st')

  | Neq(e1,e2) when is_val e1 && is_val e2 -> (match e1,e2 with
      | (IntConst n1,IntConst n2) -> (BoolConst(n1<>n2), st)
      | (AddrConst a1,AddrConst a2) -> (BoolConst(a1<>a2), st)
      | (BoolConst b1,BoolConst b2) -> (BoolConst(b1<>b2), st)
      | _ -> raise (TypeError "Neq"))
  | Neq(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Neq(e1,e2'), st')
  | Neq(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Neq(e1',e2), st')

  | Leq(e1,e2) when is_val e1 && is_val e2 -> (match e1,e2 with
      | (IntConst n1,IntConst n2) -> (BoolConst(n1<=n2), st)
      | _ -> raise (TypeError "Leq"))
  | Leq(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Leq(e1,e2'), st')
  | Leq(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Leq(e1',e2), st')

  | Lt(e1,e2) when is_val e1 && is_val e2 -> (match e1,e2 with
      | (IntConst n1,IntConst n2) -> (BoolConst(n1<n2), st)
      | _ -> raise (TypeError "Leq"))
  | Lt(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Lt(e1,e2'), st')
  | Lt(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Lt(e1',e2), st')

  | Geq(e1,e2) when is_val e1 && is_val e2 -> (match e1,e2 with
      | (IntConst n1,IntConst n2) -> (BoolConst(n1>=n2), st)
      | _ -> raise (TypeError "Leq"))
  | Geq(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Geq(e1,e2'), st')
  | Geq(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Geq(e1',e2), st')

  | Gt(e1,e2) when is_val e1 && is_val e2 -> (match e1,e2 with
      | (IntConst n1,IntConst n2) -> (BoolConst(n1>n2), st)
      | _ -> raise (TypeError "Leq"))
  | Gt(e1,e2) when is_val e1 ->
    let (e2', st') = step_expr (e2, st) in (Gt(e1,e2'), st')
  | Gt(e1,e2) -> 
    let (e1', st') = step_expr (e1, st) in (Gt(e1',e2), st')

  | IfE(e1,e2,e3) when is_val e1 -> 
    let b1 = bool_of_expr e1 in ((if b1 then e2 else e3), st)
  | IfE(e1,e2,e3) -> 
    let (e1', st') = step_expr (e1, st) in (IfE(e1',e2,e3), st')    

  | IntCast(e) when is_val e -> 
      let n = int_of_expr e in (IntConst n, st)
  | IntCast(e) -> 
    let (e', st') = step_expr (e, st) in (IntCast(e'), st')    

  | UintCast(e) when is_val e -> 
      let n = int_of_expr e in (IntConst n, st)
  | UintCast(e) -> 
    let (e', st') = step_expr (e, st) in (UintCast(e'), st')    

  | AddrCast(e) when is_val e -> 
      let b = addr_of_expr e in (AddrConst b, st)
  | AddrCast(e) -> 
    let (e', st') = step_expr (e, st) in (AddrCast(e'), st')    

  | PayableCast(e) when is_val e -> 
      let b = addr_of_expr e in (AddrConst b, st) (* payable cast is only implemented by the type checker *)
  | PayableCast(e) -> 
    let (e', st') = step_expr (e, st) in (PayableCast(e'), st')    


  | EnumOpt(x,o) -> (match lookup_enum_option st x o with
    | Some n -> (IntConst n, st)
    | None -> failwith "Enum lookup failed (bug in typechecking?)")

  | EnumCast(x,e) when is_val e -> (match exprval_of_expr e with
      | Int n -> (match reverse_lookup_enum_option st x n with
        | Some _ -> (IntConst n, st)
        | None -> raise (TypeError "EnumCast"))
      | _ -> raise (TypeError "EnumCast: expression is not an Int")
      )

  | EnumCast(x,e) -> 
    let (e', st') = step_expr (e, st) in (EnumCast(x,e'), st')    

  | FunCall(e_to,f,e_value,e_args) when is_val e_to && is_val e_value && List.for_all is_val e_args ->  
    (* retrieve function declaration *)
    let txfrom = addr_of_exprval (Addr (List.hd(st.callstack)).callee) in 
    let txto = addr_of_expr e_to in
    let txvalue  = int_of_expr e_value in
    let txargs = List.map (fun arg -> exprval_of_expr arg) e_args in
    if lookup_balance txfrom st < txvalue then 
      failwith ("sender has not sufficient wei balance")
    else
    let from_state = 
      { (st.accounts txfrom) with balance = (st.accounts txfrom).balance - txvalue } in
    let to_state  = 
      { (st.accounts txto) with balance = (st.accounts txto).balance + txvalue } in 
    let fdecl = Option.get (find_fun_in_sysstate st txto f) in  
    (* setup new callstack frame *)
    let xl = get_var_decls_from_fun fdecl in
    let xl',vl' =
      (VarT(AddrBT false,false),"msg.sender") :: (VarT(IntBT,false),"msg.value") :: xl,
      Addr txfrom :: Int txvalue :: txargs
    in
    let fr' = { callee = txto; locals = [bind_fargs_aargs xl' vl'] } in 
    let st' = { accounts = st.accounts 
                  |> bind txfrom from_state
                  |> bind txto to_state; 
                callstack = fr' :: st.callstack;
                blocknum = st.blocknum;
                active = st.active } in
    let c = get_cmd_from_fun fdecl in
    (ExecFunCall(c), st')

  | FunCall(e_to,f,e_value,e_args) when is_val e_to && is_val e_value -> 
    let (e_args', st') = step_expr_list (e_args, st) in 
    (FunCall(e_to,f,e_value,e_args'), st')

  | FunCall(e_to,f,e_value,e_args) when is_val e_to -> 
    let (e_value', st') = step_expr (e_value, st) in 
    (FunCall(e_to,f,e_value',e_args), st')
  
  | FunCall(e_to,f,e_value,e_args) -> 
    let (e_to', st') = step_expr (e_to, st) in
    (FunCall(e_to',f,e_value,e_args), st')

  | ExecFunCall(c) -> (match step_cmd (CmdSt(c,st)) with
    | St _ -> failwith "function terminated without return"
    | Reverted -> failwith "no"
    | Returned v -> (expr_of_exprval v, pop_callstack st)
    | CmdSt(c',st') -> (ExecFunCall(c'),st')
    )

  | _ -> assert(false)

and step_expr_list (el, st) = match el with
  | [] -> (el, st)
  | e::tl when is_val e -> 
    let (el',st') = step_expr_list (tl, st) in (e::el', st')
  | e::tl -> 
    let (e',st') = step_expr (e, st) in (e'::tl, st')

(******************************************************************************)
(*                       Small-step semantics of commands                     *)
(******************************************************************************)

and step_cmd = function
    St _ -> raise NoRuleApplies
  | Reverted -> Reverted
  | Returned v -> Returned v
  | CmdSt(c,st) -> (match c with

    | Skip -> St st

    | Assign(x,e) when is_val e -> St (update_var st x (exprval_of_expr e))

    | Assign(x,e) -> 
      let (e', st') = step_expr (e, st) in CmdSt(Assign(x,e'), st')

    | MapW(x,ek,ev) when is_val ek && is_val ev ->
        St (update_map st x (exprval_of_expr ek) (exprval_of_expr ev))
    | MapW(x,ek,ev) when is_val ek -> 
      let (ev', st') = step_expr (ev, st) in 
      CmdSt(MapW(x,ek,ev'), st')
    | MapW(x,ek,ev) -> 
      let (ek', st') = step_expr (ek, st) in 
      CmdSt(MapW(x,ek',ev), st')
    
    | Seq(c1,c2) -> (match step_cmd (CmdSt(c1,st)) with
        | St st1 -> CmdSt(c2,st1)
        | Reverted -> Reverted
        | Returned v -> Returned v
        | CmdSt(c1',st1) -> CmdSt(Seq(c1',c2),st1))

    | If(e,c1,c2) when is_val e -> (match exprval_of_expr e with
        | Bool true  -> CmdSt(c1,st)
        | Bool false -> CmdSt(c2,st)
        | _ -> failwith("if: type error"))
    | If(e,c1,c2) -> 
        let (e', st') = step_expr (e, st) in
        CmdSt(If(e',c1,c2), st')

    | Send(ercv,eamt) when is_val ercv && is_val eamt -> 
        let rcv = addr_of_expr ercv in 
        let amt = int_of_expr eamt in
        let from = (List.hd st.callstack).callee in 
        let from_bal = (st.accounts from).balance in
        if from_bal<amt then failwith "insufficient balance" else
        let from_state =  { (st.accounts from) with balance = from_bal - amt } in
        if exists_account st rcv then
          let rcv_state = { (st.accounts rcv) with balance = (st.accounts rcv).balance + amt } in
           St { st with accounts = st.accounts |> bind rcv rcv_state |> bind from from_state}
        else
          let rcv_state = { balance = amt; storage = botenv; code = None; } in
          St { st with accounts = st.accounts |> bind rcv rcv_state |> bind from from_state; active = rcv::st.active }

    | Send(ercv,eamt) when is_val ercv -> 
        let (eamt', st') = step_expr (eamt, st) in
        CmdSt(Send(ercv,eamt'), st')

    | Send(ercv,eamt) -> 
        let (ercv', st') = step_expr (ercv, st) in
        CmdSt(Send(ercv',eamt), st')

    | Req(e) when is_val e -> 
        let b = bool_of_expr e in if b then St st else Reverted
    | Req(e) -> 
      let (e', st') = step_expr (e, st) in CmdSt(Req(e'), st')

    | Return(e) when is_val e -> Returned (exprval_of_expr e) 
    | Return(e) -> 
      let (e', st') = step_expr (e, st) in CmdSt(Return(e'), st')
    
    | Block(vdl,c) ->
        let r' = List.fold_left (fun acc vd ->
          match vd with
            | VarT(IntBT,_),x  
            | VarT(UintBT,_),x -> acc |> bind x (Int 0)
            | VarT(BoolBT,_),x -> acc |> bind x (Bool false)
            | VarT(AddrBT _,_),x -> acc |> bind x (Addr "0")
            | VarT(CustomBT _,_),x -> acc |> bind x (Int 0)
            | MapT(_),_ -> failwith "mappings cannot be used in local declarations" 
        ) botenv vdl in
        let fr,frl = (List.hd st.callstack),(List.tl st.callstack) in
        let fr' = { fr with locals = r'::fr.locals } in
        CmdSt(ExecBlock c, { st with callstack = fr'::frl })

    | ExecBlock(c) -> (match step_cmd (CmdSt(c,st)) with
        | St st -> St (pop_locals st)
        | Reverted -> Reverted
        | Returned v -> Returned v
        | CmdSt(c1',st1) -> CmdSt(ExecBlock(c1'),st1))

    | Decl _ -> assert(false) (* should not happen after blockify *)

    | ProcCall(e_to,f,e_value,e_args) when is_val e_to && is_val e_value && List.for_all is_val e_args ->
        (* retrieve function declaration *)
        let txfrom = (List.hd (st.callstack)).callee in 
        let txto   = addr_of_expr e_to in
        let txvalue  = int_of_expr e_value in
        let txargs = List.map (fun arg -> exprval_of_expr arg) e_args in
        if lookup_balance txfrom st < txvalue then 
          failwith ("sender " ^ txfrom ^ " has not sufficient wei balance")
        else
        let from_state = 
          { (st.accounts txfrom) with balance = (st.accounts txfrom).balance - txvalue } in
        let to_state  = 
          { (st.accounts txto) with balance = (st.accounts txto).balance + txvalue } in 
        let fdecl = Option.get (find_fun_in_sysstate st txto f) in  
        (* setup new stack frame TODO *)
        let xl = get_var_decls_from_fun fdecl in
        let xl',vl' =
          (VarT(AddrBT false,false),"msg.sender") :: (VarT(IntBT,false),"msg.value") :: xl,
          Addr txfrom :: Int txvalue :: txargs
        in
        let fr' = { callee = txto; locals = [bind_fargs_aargs xl' vl'] } in
        let st' = { accounts = st.accounts 
                      |> bind txfrom from_state
                      |> bind txto to_state; 
                    callstack = fr' :: st.callstack;
                    blocknum = st.blocknum;
                    active = st.active } in
        let c = get_cmd_from_fun fdecl in
        CmdSt(ExecProcCall(c), st')

    | ProcCall(e_to,f,e_value,e_args) when is_val e_to && is_val e_value -> 
      let (e_args', st') = step_expr_list (e_args, st) in 
      CmdSt(ProcCall(e_to,f,e_value,e_args'), st')

    | ProcCall(e_to,f,e_value,e_args) when is_val e_to -> 
      let (e_value', st') = step_expr (e_value, st) in 
      CmdSt(ProcCall(e_to,f,e_value',e_args), st')

    | ProcCall(e_to,f,e_value,e_args) -> 
      let (e_to', st') = step_expr (e_to, st) in 
      CmdSt(ProcCall(e_to',f,e_value,e_args), st')

    | ExecProcCall(c) -> (match step_cmd (CmdSt(c,st)) with
      | St st -> St (pop_callstack st)
      | Reverted -> Reverted
      | Returned _ -> St (pop_callstack st)
      | CmdSt(c1',st1) -> CmdSt(ExecProcCall(c1'),st1))
  )

(* recursively evaluate expression until it reaches a value (might not terminate) *)
let rec eval_expr (st : sysstate) (e : expr) : exprval = 
  if is_val e then exprval_of_expr e
  else let (e', st') = step_expr (e, st) in eval_expr st' e'  

let default_value = function 
  IntBT  
| UintBT -> Int 0
| BoolBT -> Bool false
| AddrBT _ -> Addr "0"
| CustomBT _ -> Int 0

let init_storage (Contract(_,_,vdl,_)) : ide -> exprval =
  List.fold_left (fun acc vd -> 
      let (x,v) = (match vd with 
        | VarT(t,_),x -> (x, default_value t)
        | MapT(_,tv),x -> (x, Map (fun _ -> (default_value tv)))
      )
      in bind x v acc) botenv vdl 

let init_sysstate = { 
    accounts = (fun a -> failwith ("account " ^ a ^ " unbound")); 
    callstack = [];
    blocknum = 0;
    active = []; 
}

let exec_cmd (n_steps : int) (c : cmd) (st : sysstate) : exec_state =
  let rec exec_rec_cmd n s =
    if n<=0 then s
    else try
        let s' = step_cmd s
        in exec_rec_cmd (n-1) s'
      with NoRuleApplies -> s
    in exec_rec_cmd n_steps (CmdSt (c,st))

let trace_cmd n_steps (c:cmd) (st : sysstate) : exec_state list =
  let rec trace_rec_cmd n t =
    if n<=0 then [t]
    else try
        let t' = step_cmd t
        in t::(trace_rec_cmd (n-1) t')
      with NoRuleApplies -> [t]
  in trace_rec_cmd n_steps (CmdSt(c,st))


(******************************************************************************)
(* Funds an account in a system state. Creates account if it does not exist   *)
(******************************************************************************)

let faucet (a : addr) (n : int) (st : sysstate) : sysstate = 
  if exists_account st a then 
    let as' = { (st.accounts a) with balance = n + (st.accounts a).balance } in
    { st with accounts = bind a as' st.accounts }
  else
    let as' = { balance = n; storage = botenv; code = None; } in
    { st with accounts = bind a as' st.accounts; active = a::st.active }


(******************************************************************************)
(* Executes steps of a transaction in a system state, returning a trace       *)
(******************************************************************************)

let exec_tx (n_steps : int) (tx: transaction) (st : sysstate) : sysstate =
  if tx.txvalue < 0 then
    failwith ("exec_tx: trying to send a negative amount of tokens")
  else if not (exists_account st tx.txsender) then 
    failwith ("exec_tx: sender address " ^ tx.txsender ^ " does not exist")
  else if (st.accounts tx.txsender).balance < tx.txvalue then
    failwith ("exec_tx: sender address " ^ tx.txsender ^ " has not sufficient balance")
  else if not (exists_account st tx.txto) && tx.txfun <> "constructor" then
    failwith ("exec_tx: to address " ^ tx.txto ^ " does not exist")
  else if (exists_account st tx.txto) && tx.txfun = "constructor" then
    failwith ("exec_tx: calling constructor in already deployed contract at address " ^ tx.txto) 
  else 
  let (sender_state : account_state) = 
    { (st.accounts tx.txsender) with balance = (st.accounts tx.txsender).balance - tx.txvalue } in
  (* sets state of to address. If not created yet, deploys the contract *)
  let (to_state : account_state),(deploy : bool) = 
    if exists_account st tx.txto 
    then    { (st.accounts tx.txto) with balance = (st.accounts tx.txto).balance + tx.txvalue }, 
            false (* deploy=false ==> cannot call constructor *) 
    else (match tx.txargs with 
      | Addr(code)::_ ->
          (try let c = code |> parse_contract |> blockify_contract in 
            { balance=tx.txvalue; storage = init_storage c; code = Some c }, 
            true (* deploy=true ==> must call constructor *)
          with _ -> failwith ("exec_tx: syntax error in contract code: " ^ code))
      | _ -> failwith "exec_tx: the first parameter of a deploy transaction must be the contract code") in
  match to_state.code with
  | None -> failwith "Called address is not a contract"
  | Some src -> (match find_fun_in_contract src tx.txfun with
    | None when (not deploy) -> failwith ("Contract at address " ^ tx.txto ^ " has no function named " ^ tx.txfun)
    | None -> (* deploy a contract with no constructor (non-payable) *)
      if tx.txvalue > 0 then 
        failwith "The deployed contract should have a payable constructor if you send value"
      else
        { accounts = st.accounts 
            |> bind tx.txsender sender_state
            |> bind tx.txto to_state; 
          callstack = st.callstack;
          blocknum = 0;
          active = tx.txto :: st.active }
    | Some (Proc(_,xl,c,_,p,_))
    | Some (Constr(xl,c,p)) ->
        if not p && tx.txvalue>0 then 
          failwith "exec_tx: sending ETH to a non-payable function"
      else
        let xl',vl' =
          if deploy then match tx.txargs with 
            _::al -> 
            (VarT(AddrBT false,false),"msg.sender") :: xl,
            Addr tx.txsender :: al (* TODO: why null value?? *)
            | _ -> assert(false) (* should not happen *)
          else
            (VarT(AddrBT false,false),"msg.sender") :: (VarT(IntBT,false),"msg.value") :: xl,
            Addr tx.txsender :: Int tx.txvalue :: tx.txargs
        in
        let fr' = { callee = tx.txto; locals = [bind_fargs_aargs xl' vl'] } in
        let st' = { accounts = st.accounts 
                      |> bind tx.txsender sender_state
                      |> bind tx.txto to_state; 
                    callstack = fr' :: st.callstack;
                    blocknum = 0;
                    active = if deploy then tx.txto :: st.active else st.active } in
        try (match exec_cmd n_steps c st' with
          | St st'' -> st'' |> pop_callstack
          | Reverted -> st  (* if the command reverts, the new state is st *)
          | _ -> st (* exec_tx: execution of command not terminated (not enough gas?) => revert *)
        )
        with _ -> st (* exception thrown during execution of command => revert *)
    ) 

let exec_tx_list (n_steps : int) (txl : transaction list) (st : sysstate) = 
  List.fold_left 
  (fun sti tx -> exec_tx n_steps tx sti)
  st
  txl

(******************************************************************************)
(*                       Deploys a contract in a system state                 *)
(******************************************************************************)

let deploy_contract (tx : transaction) (src : string) (st : sysstate) : sysstate =
  if exists_account st tx.txto then 
    failwith ("deploy_contract: address " ^ tx.txto ^ " already bound in sysstate")
  else if tx.txfun <> "constructor" then
    failwith ("deploy_contract: deploying a contract must call the constructor")
  else let tx' = { tx with txargs = Addr(src) :: tx.txargs }
  in exec_tx 1000 tx' st
