open Ast

type exprtype = 
  | BoolT
  | IntT
  | IntConstT
  | UintT
  | UintConstT
  | AddrT

(* TypeError(expression, inferred type, expected type) *)
exception TypeError of expr * exprtype * exprtype
exception UndeclaredVar of ide
exception MultipleDecl of ide

let lookup_type (x : ide) (vdl : var_decl list) : exprtype option =
  if x="msg.sender" then Some AddrT
  else if x="msg.value" then Some UintT else 
  vdl 
  |> List.map (fun vd -> match vd with
    | IntVar x -> IntT,x 
    | UintVar x -> UintT,x
    | BoolVar x-> BoolT,x
    | AddrVar x -> AddrT,x )
  |> List.fold_left
  (fun acc (t,y) -> if acc=None && x=y then Some t else acc)
  None

let merge_var_decls old_vdl new_vdl = new_vdl @ old_vdl  

let rec dup = function 
  | [] -> None
  | x::l -> if List.mem x l then Some x else dup l

let no_dup_var_decls vdl = 
  vdl 
  |> List.map (fun vd -> match vd with IntVar x | UintVar x | BoolVar x | AddrVar x -> x) 
  |> dup
  |> fun res -> match res with None -> true | Some x -> raise (MultipleDecl x)  

let no_dup_fun_decls vdl = 
  vdl 
  |> List.map (fun fd -> match fd with 
    | Constr(_) -> "constructor"
    | Proc(f,_,_,_,_) -> f) 
  |> dup
  |> fun res -> match res with None -> true | Some x -> raise (MultipleDecl x)  

let subtype t0 t1 = match t1 with
  | UintConstT -> t0 = t1
  | UintT -> t0 = UintConstT || t0 = t1
  | IntConstT -> t0 = UintConstT || t0 = t1
  | IntT -> t0 = UintConstT || t0 == IntConstT || t0 = t1 (* uint is not convertible to int *)
  | _ -> t0 = t1

let rec typecheck_expr (vdl : var_decl list) = function
    True -> BoolT
  | False -> BoolT
  | IntConst n when n>=0 -> UintConstT
  | IntConst _ -> IntConstT
  | AddrConst _ -> AddrT
  | This -> AddrT (* TODO: make more coherent with Solidity *)
  | Var x -> (match lookup_type x vdl with
    | Some t -> t
    | None -> raise (UndeclaredVar x))
  | BalanceOf(e) -> (match typecheck_expr vdl e with
        AddrT -> UintT
      | _ as t -> raise (TypeError (e,t,AddrT)))
  | Not(e) -> (match typecheck_expr vdl e with
        BoolT -> BoolT
      | _ as t -> raise (TypeError (e,t,BoolT)))
  | And(e1,e2) 
  | Or(e1,e2) ->
    (match (typecheck_expr vdl e1,typecheck_expr vdl e2) with
       (BoolT,BoolT) -> BoolT
     | (t,_) when t<>BoolT -> raise (TypeError (e1,t,BoolT))
     | (_,t) -> raise (TypeError (e2,t,BoolT)))
  | Add(e1,e2)
  | Mul(e1,e2) ->
    (match (typecheck_expr vdl e1,typecheck_expr vdl e2) with
     | (UintConstT,UintConstT) -> UintConstT
     | (t1,t2) when subtype t1 UintT && subtype t2 UintT -> UintT
     | (t1,t2) when subtype t1 IntConstT && subtype t2 IntConstT -> IntConstT
     | (t1,t2) when subtype t1 UintT && subtype t2 UintT -> UintT
     | (t1,t2) when subtype t1 IntT && subtype t2 IntT -> IntT
     | (t1,_) when t1<>IntT -> raise (TypeError (e1,t1,IntT))
     | (_,t2) -> raise (TypeError (e2,t2,IntT)))
  | Sub(e1,e2) ->
    (match (typecheck_expr vdl e1,typecheck_expr vdl e2) with
     | (t1,t2) when subtype t1 IntConstT && subtype t2 IntConstT -> IntConstT
     | (t1,t2) when subtype t1 IntT && subtype t2 IntT -> IntT
     | (t1,_) when t1<>IntT -> raise (TypeError (e1,t1,IntT))
     | (_,t2) -> raise (TypeError (e2,t2,IntT)))
  | Eq(e1,e2)
  | Neq(e1,e2) ->
    (match (typecheck_expr vdl e1,typecheck_expr vdl e2) with
       (t1,t2) when t1=t2-> BoolT
     | (t1,t2) when subtype t1 UintT && subtype t2 UintT -> BoolT
     | (t1,t2) when subtype t1 IntT && subtype t2 IntT -> BoolT
     | (t1,t2) -> raise (TypeError (e2,t2,t1)))
  | Leq(e1,e2)
  | Le(e1,e2)
  | Geq(e1,e2)
  | Ge(e1,e2) ->
    (match (typecheck_expr vdl e1,typecheck_expr vdl e2) with
     | (t1,t2) when subtype t1 UintT && subtype t2 UintT -> BoolT
     | (t1,t2) when subtype t1 IntT && subtype t2 IntT -> BoolT
     | (t1,IntT) -> raise (TypeError (e1,t1,IntT))
     | (_,t2) -> raise (TypeError (e2,t2,IntT)))
  | IntCast(e) -> (match typecheck_expr vdl e with
      | IntT | UintT -> IntT
      | _ as t -> raise (TypeError (e,t,IntT)))
  | UintCast(e) -> (match typecheck_expr vdl e with
      | IntT | UintT -> UintT
      | _ as t -> raise (TypeError (e,t,IntT)))
  | AddrCast(e) -> (match typecheck_expr vdl e with
      | AddrT -> AddrT
      | IntT -> AddrT
      | _ as t -> raise (TypeError (e,t,IntT))) 
;;

let rec typecheck_cmd (vdl : var_decl list) = function 
    | Skip -> true
    | Assign(x,e) -> 
        let te = typecheck_expr vdl e in
        let tx = typecheck_expr vdl (Var x) in
        if subtype te tx then true else raise (TypeError (e,te,tx)) 
      | Seq(c1,c2) -> 
        typecheck_cmd vdl c1 && 
        typecheck_cmd vdl c2
    | If(e,c1,c2) ->
        let te = typecheck_expr vdl e in
        if te = BoolT then typecheck_cmd vdl c1 && typecheck_cmd vdl c2
        else raise (TypeError (e,te,BoolT))
    | Send(ercv,eamt) -> 
        typecheck_expr vdl ercv = AddrT &&
        typecheck_expr vdl eamt = IntT
    | Req(e) -> 
        let te = typecheck_expr vdl e in
        if te = BoolT then true else raise (TypeError (e,te,BoolT))
    | Block(lvdl,c) -> 
        let vdl' = merge_var_decls vdl lvdl in
        typecheck_cmd vdl' c
    | _ -> failwith "TODO"


let typecheck_fun (vdl : var_decl list) = function
  | Constr (al,c,_) -> typecheck_cmd (merge_var_decls vdl al) c
  | Proc (_,al,c,_,__) -> typecheck_cmd (merge_var_decls vdl al) c

let typecheck_contract (Contract(_,vdl,fdl)) =
  (* no multiply declared variables *)
  no_dup_var_decls vdl
  &&
  (* no multiply declared functions *)
  no_dup_fun_decls fdl
  &&
  List.fold_left 
  (fun acc fd -> acc && typecheck_fun vdl fd)
  true
  fdl  
