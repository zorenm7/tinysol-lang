open Ast
open Types

(******************************************************************************)
(*                       Big-step semantics of expressions                    *)
(******************************************************************************)

exception TypeError of string
exception NoRuleApplies

let is_val = function
    True -> true
  | False -> true
  | IntConst _ -> true
  | AddrConst _ -> true
  | _ -> false

let int_of_exprval v = match v with 
  | Int n -> n
  | Bool _ -> failwith "value has type Bool but an Int was expected"
  | Addr _ -> failwith "value has type Addr but an Int was expected"

let bool_of_exprval v = match v with 
  | Bool b -> b
  | Int _ -> failwith "value has type Int but an Bool was expected"
  | Addr _ -> failwith "value has type Addr but an Bool was expected"

let addr_of_exprval v = match v with 
  | Addr a -> a
  | Bool _ -> failwith "value has type Bool but an Addr was expected"
  | Int _ -> failwith "value has type Int but an Addr was expected"

let rec eval_expr (st : sysstate) (a : addr) = function
    True -> Bool true
  | False -> Bool false
  | IntConst n -> Int n
  | AddrConst s -> Addr s
  | This -> Addr a
  | Var x -> lookup a x st
  | BalanceOf e ->
    let b = addr_of_exprval (eval_expr st a e) in (
      try (Int (st.accounts b).balance)
      with _ -> Int 0)
  | Not(e) -> (match eval_expr st a e with
        Bool b -> Bool(not b)
      | _ -> raise (TypeError "Not")
    )
  | And(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Bool b1,Bool b2) -> Bool(b1 && b2)
      | _ -> raise (TypeError "And")
    )
  | Or(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Bool b1,Bool b2) -> Bool(b1 || b2)
      | _ -> raise (TypeError "Or")
    )
  | Add(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) -> Int(n1 + n2)
      | _ -> raise (TypeError "Add")
    )    
  | Sub(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) when n1>=n2 -> Int(n1 - n2)
      | _ -> raise (TypeError "Sub")
    )
  | Mul(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) -> Int(n1 * n2)
      | _ -> raise (TypeError "Add")
    )        
  | Eq(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) -> Bool(n1 = n2)
      | _ -> raise (TypeError "Eq")
    )    
  | Neq(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) -> Bool(n1 <> n2)
      | _ -> raise (TypeError "Eq")
    )    
  | Leq(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) -> Bool(n1 <= n2)
      | _ -> raise (TypeError "Leq")
    )          
  | Le(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) -> Bool(n1 < n2)
      | _ -> raise (TypeError "Le")
    )          
  | Geq(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) -> Bool(n1 >= n2)
      | _ -> raise (TypeError "Geq")
    )          
  | Ge(e1,e2) -> (match (eval_expr st a e1,eval_expr st a e2)  with
        (Int n1,Int n2) -> Bool(n1 > n2)
      | _ -> raise (TypeError "Ge")
    )          

let eval_var_decls (vdl : var_decl list) (e : env): env =
  List.fold_left
    (fun acc vd ->
      match vd with
        | IntVar x  -> acc |> bind x (Int 0)
        | BoolVar x -> acc |> bind x (Bool false)
        | AddrVar x -> acc |> bind x (Addr "0")
    )
    e
    vdl

(******************************************************************************)
(*                       Small-step semantics of commands                     *)
(******************************************************************************)

let rec trace1_cmd = function
    St _ -> raise NoRuleApplies
  | Cmd(c,st,a) -> (match c with
    | Skip -> St st
    | Assign(x,e) -> (
        (* first tries to update environment if x is bound there *)
        try 
          St (update_env st x (eval_expr st a e)) 
        (* if not, tries to update storage of a *)
        with _ -> 
          St (update_storage st a x (eval_expr st a e)))
    | Seq(c1,c2) -> (match trace1_cmd (Cmd(c1,st,a)) with
          St st1 -> Cmd(c2,st1,a)
        | Cmd(c1',st1,a) -> Cmd(Seq(c1',c2),st1,a))
    | If(e,c1,c2) -> (match eval_expr st a e with
          Bool true -> Cmd(c1,st,a)
        | Bool false -> Cmd(c2,st,a)
        | _ -> failwith("if: type error"))
    | Send(ercv,eamt) -> 
        let rcv = addr_of_exprval (eval_expr st a ercv) in 
        let amt = int_of_exprval (eval_expr st a eamt) in
        let bal = (st.accounts a).balance in
        if bal<amt then failwith "insufficient balance" else
        let sender_state =  { (st.accounts a) with balance = (st.accounts a).balance - amt } in
        if exists_account st rcv then
          let rcv_state = { (st.accounts rcv) with balance = (st.accounts rcv).balance + amt } in
           St { st with accounts = st.accounts |> bind rcv rcv_state |> bind a sender_state}
        else
          let rcv_state = { balance = amt; storage = botenv; code = None; } in
          St { st with accounts = st.accounts |> bind rcv rcv_state |> bind a sender_state; active = rcv::st.active }
    | Req(_) -> failwith ("TODO")
    | Call(_,_) -> failwith "TODO"
    | ExecCall _  -> failwith "TODO"
    | Block(vdl,c) ->
        let e = topenv st in
        let e' = eval_var_decls vdl e in
        Cmd(ExecBlock c, { st with stackenv = e'::st.stackenv} , a)
    | ExecBlock(c) -> (match trace1_cmd (Cmd(c,st,a)) with
        | St st -> St (popenv st)
        | Cmd(c1',st1,a') -> Cmd(ExecBlock(c1'),st1,a'))
    )
(* (match (topenv st f,eval_expr st e) with
          (IProc(a,c),Int n) ->
          let l = getloc st in
          let env' = bind (topenv st) x (IVar l) in
          let mem' = bind (getmem st) l n in
          let st' = (env'::(getenv st), mem', l+1) in
          Cmd(CallExec(c),st')
        | _ -> raise (TypeError "Call of a non-procedure"))
*)
(*                    
    | CallExec(c) -> (match trace1_cmd (Cmd(c,st,a)) with
          St st' -> St (popenv st', getmem st', getloc st',a)
        | Cmd(c',st') -> Cmd(CallExec(c'),st',a))
*)

(*
let sem_decl (e,l) = function
  | IntVar(x) ->  let e' = bind e x (IVar l) in (e',l+1)
  | Constr(f,a,c) -> let e' = bind e f (IProc(a,c)) in (e',l)                                                
  | Proc(f,a,c) -> let e' = bind e f (IProc(a,c)) in (e',l)
*)

 
let init_storage (Contract(_,vdl,_)) : ide -> exprval =
  List.fold_left (fun acc var -> 
      let (x,v) = (match var with 
        | IntVar x  -> (x, Int 0)
        | BoolVar x -> (x, Bool false)
        | AddrVar x -> (x, Addr "0"))
      in bind x v acc) botenv vdl 

let init_sysstate = { 
    accounts = (fun a -> failwith ("account " ^ a ^ " unbound")); 
    stackenv = [botenv];
    active = []; 
}

let exec_cmd (n_steps : int) (c : cmd) (a : addr) (st : sysstate) : exec_state =
  let rec exec_rec_cmd n s =
    if n<=0 then s
    else try
        let s' = trace1_cmd s
        in exec_rec_cmd (n-1) s'
      with NoRuleApplies -> s
    in exec_rec_cmd n_steps (Cmd (c,st,a))

let trace_cmd n_steps (c:cmd) (a:addr) (st : sysstate) : exec_state list =
  let rec trace_rec_cmd n t =
    if n<=0 then [t]
    else try
        let t' = trace1_cmd t
        in t::(trace_rec_cmd (n-1) t')
      with NoRuleApplies -> [t]
  in trace_rec_cmd n_steps (Cmd(c,st,a))


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
(*                       Deploys a contract in a system state                 *)
(******************************************************************************)

(* TODO: we should execute constructor!! *)

let deploy_contract (a : addr) (c : contract) (st : sysstate) : sysstate =
  if exists_account st a then failwith ("deploy_contract: address " ^ a ^ " already bound in sysstate")
  else
    let as' = st.accounts |> bind a { balance=0; storage = init_storage c; code = Some c } in
  { st with accounts = as'; active = a::st.active }


(******************************************************************************)
(* Executes steps of a transaction in a system state, returning a trace       *)
(******************************************************************************)

let find_fun (Contract(_,_,fdl)) (f : ide) : fun_decl option =
  List.fold_left 
  (fun acc (Proc(g,al,c,m)) -> if acc <> None || g<>f then acc else Some (Proc(g,al,c,m)))
  None
  fdl

let bind_fargs_aargs (xl : var_decl list) (vl : exprval list) : env =
   List.fold_left2 
   (fun acc x_decl v -> match (x_decl,v) with 
    | (IntVar x, Int _) 
    | (BoolVar x, Bool _) 
    | (AddrVar x, Addr _) -> bind x v acc
    | _ -> failwith "bind_fargs_aargs") 
   botenv 
   xl 
   vl

let exec_tx (n_steps : int) (Tx(a,b,f,vl)) (st : sysstate) : sysstate =
  if not (exists_account st a) then failwith ("sender address " ^ a ^ " does not exist") else
  if not (exists_account st b) then failwith ("to address " ^ b ^ " does not exist") else
  let b_state = st.accounts b in match b_state.code with
  | None -> failwith "Call not to a contract"
  | Some src -> (match find_fun src f with
      | None -> failwith ("Contract at address " ^ b ^ " has no function named " ^ f)
      | Some (Proc(_,xl,c,_)) ->
          let xl' =  AddrVar "msg.sender" :: xl in
          let vl' = Addr a :: vl in
          let e' = bind_fargs_aargs xl' vl' in
          let st' = { st with stackenv = e' :: st.stackenv } in
          exec_cmd n_steps c b st'
          |> sysstate_of_exec_sysstate
          |> popenv)


let exec_tx_list (n_steps : int) (txl : transaction list) (st : sysstate) = 
  List.fold_left 
  (fun sti tx -> exec_tx n_steps tx sti)
  st
  txl
