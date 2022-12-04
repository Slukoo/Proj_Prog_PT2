
open Format
open Lib
open Ast
open Tast

let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))

(* TODO environnement pour les types structure *)

(* TODO environnement pour les fonctions *)

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | _ -> error dummy_loc ("unknown struct ") (* TODO type structure *)

let rec eq_type ty1 ty2 = match ty1, ty2 with
  | Tint, Tint | Tbool, Tbool | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | _ -> false
    (* TODO autres types *)

let fmt_used = ref false
let fmt_imported = ref false

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = 0; v_depth = 0 }



let rec checktype = function
  |PTident {id; loc}-> List.mem id ["bool"; "int"; "string"] (*|| Hashtbl.mem tablestructs id*)
  |PTptr t -> checktype t

module FuncEnv = struct
  module M = Map.Make(String)
  type t = pfunc M.t
  let empty = M.empty
  let all_funcs = ref empty
  let find f = M.find f !all_funcs
  let exists f = M.mem f.pf_name.id !all_funcs

  let add f = 
    if exists f then
      error f.pf_name.loc ("duplicate function name " ^ f.pf_name.id)
    else
      all_funcs := M.add f.pf_name.id f !all_funcs

      let varduplicates f = 
        let table = Hashtbl.create 15 in
        let rec test_var = function
          |[] -> ()
          |p::t ->
            let pid = fst p in
            if Hashtbl.mem table pid.id then
              error pid.loc (" duplicate variable names in function " ^ f.pf_name.id)
            else (
              Hashtbl.add table pid.id ();
              test_var t
            )
        in test_var f.pf_params
      let paramtypes f =
        let rec aux = function
        | [] -> ()
        | p::l -> 
          let id = fst p in
          if checktype (snd p)
          then aux l
          else error id.loc ("unknown type for variable "^id.id^" in function "^f.pf_name.id)
        in aux f.pf_params
    
      let outtype f =
        let rec aux = function
        |[] -> ()
        | t::l ->
          if checktype t
          then aux l
          else error f.pf_name.loc ("unknown return type for function "^f.pf_name.id)
        in aux f.pf_typ

end

module Env = struct
  module M = Map.Make(String)
  type t = var M.t
  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env
  
  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && not v.v_used then (
        error v.v_loc ("unused variable "^v.v_name)) in
    List.iter check !all_vars


  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

  (* TODO type () et vecteur de types *)
end

let rec islvalue exp =
  match (exp.pexpr_desc) with
  | PEident _ -> true
  | PEdot (e,x) -> (islvalue e)
  | PEunop (Ustar, e) ->  (e.pexpr_desc <> PEnil)
  | _ -> false

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid

let rettyp = ref []

let list_to_typevect tl =
  match tl with
  | [x] -> x
  | _ -> Tmany tl




  let rec valid_type ty =
    match ty with
    | Tint | Tstring | Tbool | Twild -> true
    | Tptr t -> valid_type t
    | Tmany _ -> false
    | Tstruct s -> assert false







let rec expr env e =
let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt

and expr_desc env loc = function
  | PEskip -> TEskip, tvoid, false


  | PEconstant c -> (match c with 
    | Cbool _  -> TEconstant c, Tbool, false

    | Cint _ -> TEconstant c, Tint, false

    | Cstring _ -> TEconstant c, Tstring, false)


  | PEbinop (op, e1, e2) ->
    let t1 = (fst(expr env e1)).expr_typ  and t2 = (fst(expr env e2)).expr_typ in
    if (not (eq_type t1 t2)) then 
      error loc ("bad typing ")
    else ( 
      match op with
        | Badd | Bsub | Bmul | Bdiv | Bmod -> 
          if (eq_type t1 Tint) then 
            TEbinop(op, fst (expr env e1), fst (expr env e2)), Tint, false
          else 
            error loc ("expected int ")

        | Blt | Ble | Bgt | Bge ->
          if (eq_type t1 Tint) then
            TEbinop(op,fst (expr env e1), fst (expr env e2)), Tbool, false
          else
            error loc ("expected int ")

        | Beq | Bne ->
          if (e1.pexpr_desc = PEnil) then
            error loc "expression must not be nil for comparison "
          else
            TEbinop(op,fst (expr env e1),fst (expr env e2)), Tbool, false

        | Band | Bor ->
          if (eq_type t1 Tbool) then
            TEbinop(op,fst (expr env e1) ,fst (expr env e2)), Tbool, false
          else
            error loc "expected bool "
    )
  

  | PEunop (op, e1) ->
    let t = (fst(expr env e1)).expr_typ in
    (match op with
      | Uamp ->
        if islvalue e1 then
          TEunop(Uamp, fst (expr env e1)), Tptr t, false
        else
          error loc ("expected l-value ")
      |Ustar ->
        if e1.pexpr_desc = PEnil then
          error loc "cannot dereference null pointer "
        else
          (match t with
            | Tptr t -> 
              TEunop(Ustar, fst (expr env e1)), t, false
            | _ ->
              error loc ("expected pointer ")
        )

      | Uneg  ->
        if (eq_type t Tint) then
          TEunop(op, fst (expr env e1)), Tint, false
        else
          error loc ("expected int ")

      | Unot ->
        if (eq_type t Tbool) then
          TEunop(op, fst(expr env e1)), Tbool, false
        else
          error loc ("expected bool ")
    )


  | PEcall ({id = "fmt.Print"}, el) ->
    if not !fmt_imported then error loc ("fmt unimported ");
    let l = List.map (fun x -> fst (expr env x)) el in
    fmt_used := true;
    TEprint l, tvoid, false

  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) ->
    let ty = match id with
      | "int" -> Tint | "bool" -> Tbool | "string" -> Tstring
      | _ -> (* TODO *) error loc ("no such type " ^ id) in
    TEnew ty, Tptr ty, false
  | PEcall ({id="new"}, _) ->
    error loc "new expects a type"


  | PEcall (id, el) ->
    (
    try
      let pf = FuncEnv.find id.id in
      let exl = List.map (fun e -> fst( expr env e)) el in
      try
        if List.for_all2 (fun par ex -> eq_type ex.expr_typ (type_type (snd par))) (pf.pf_params) exl then
          let f = {fn_name = pf.pf_name.id ; fn_typ = List.map type_type pf.pf_typ ;
              fn_params = List.map (fun (id,typ) -> new_var id.id id.loc (type_type typ)) pf.pf_params} in
          let typ = list_to_typevect f.fn_typ in
          TEcall(f,exl), typ , false
        else
          error loc ("wrong type of arguments ")
      with
      |Invalid_argument _ -> error loc "wrong number of arguments "
    with
    |Not_found -> error loc ("unbound function "^id.id)
    )


  | PEfor (e, b) ->
    let e' = expr env e and b' = expr env b in
    if (eq_type (fst(b')).expr_typ Tbool) then
      TEfor(fst(e'), fst(b')), tvoid, (snd(e'))
    else
      error loc "boolean condition expected "

  | PEif (e1, e2, e3) ->
    let e1' = expr env e1  in
    if (eq_type (fst(e1')).expr_typ Tbool) then
      let e2' = expr env e2 and e3' = expr env e3 in
      TEif(fst(e1'),fst(e2'),fst(e3')), tvoid, (snd(e2') && snd(e3'))
    else
      error loc "boolean condition expected "


  | PEnil ->
    TEnil, Tptr Twild, false

  | PEident {id=id} ->
    (try let v = Env.find id env in 
      v.v_used <- true ; 
      TEident v, v.v_typ, false
    with Not_found -> error loc ("unbound variable " ^ id))

  | PEdot (e, id) ->
     (* TODO *) assert false

  | PEassign (lvl, el) ->
      let lvl' = List.map (fun lv -> if islvalue lv then fst(expr env lv) else error loc "only l-values are allowed for affectation ") lvl
      and exl = List.map (fun e -> fst (expr env e)) el in
      if List.equal (fun lv ex -> eq_type lv.expr_typ ex.expr_typ) lvl' exl then
        TEassign (lvl', exl), tvoid, false
      else if (List.length exl   = 1 && lvl <> []) then
        let {expr_desc = desc; expr_typ = ty} = List.hd exl in
        try
        match desc,ty with
        | TEcall(_,_), Tmany tl when (List.for_all2 (fun lv t -> eq_type lv.expr_typ t) lvl' tl) -> 
            TEassign(lvl',exl), tvoid, false
        | _ -> error loc "wrong affectation type "
        with | Invalid_argument _ -> error loc "unbalanced affectations "
      else
        error loc "unbalanced affectations "

  | PEreturn el ->
    let rl = List.map (fun e -> fst(expr env e)) el in 
    let tl = List.map (fun e -> e.expr_typ) rl in
      if tl = !rettyp then
        TEreturn(rl), tvoid, true
      else
        error loc "wrong return type "

  | PEblock el ->
      let rec declaration desc env' =
        match desc with
          | TEvars(vl,exl) -> (List.fold_left (fun e v -> Env.add e v) env' vl)
          | _ ->  env'
      in
      let f env' e =
        let ex = fst(expr !env' e) in
        env' := declaration ex.expr_desc !env';
        ex
      in
      let env' = ref env in
      let rl = List.map (f env') el in 
      let ret = List.fold_left (fun b e -> b || snd(expr !env' e)) false el in
      TEblock(rl), tvoid, ret

  | PEincdec (e, op) ->
    let ex = fst(expr env e) in
    if (eq_type ex.expr_typ Tint && islvalue e) then
      TEincdec(ex, op), tvoid, false
    else
      error loc "increase/decrease operation can only be done on l-values of type int "


  | PEvars(il,None,el) ->
    let exl = List.map(fun e -> fst(expr env e)) el in
    if il = [] then error loc "empty declaration " else
    if el = [] then
      error loc "declaration must specify at least a type or an expression"
    else
      if List.length il = 1 then
      let i = List.hd il in
        match exl with
        | [ex] ->
            if (valid_type ex.expr_typ) then
            let v = snd( Env.var i.id i.loc ex.expr_typ env) in
            TEvars([v],[ex]), tvoid, false 
          else
            error loc "expression type is not valid "
        | _ -> error loc "unbalanced delcaration: too many expressions"

      else if List.length il = List.length el then
        if List.for_all (fun ex -> valid_type ex.expr_typ) exl then
          let vl = List.map2 (fun ex i -> snd( Env.var i.id i.loc ex.expr_typ env)) exl il in
          TEvars(vl,exl), tvoid, false
        else
          error loc "expression type is not valid "
      else if List.length exl = 1 then
        let ex = List.hd exl in
        match ex.expr_typ with
          | Tmany tl when List.length tl = List.length il -> 
            let vl = List.map2 (fun t i -> snd(Env.var i.id i.loc t env)) tl il in
            TEvars(vl,exl), tvoid, false
          | _ -> error loc "wrong number/type of expressions "
      else
        error loc "wrong number of expressions "
            
  | PEvars(il,Some pt,el) -> 
    let t = type_type pt in
    if (not (valid_type t)) then error loc "type of declaration is not valid" 
    else
    let exl = List.map(fun e -> fst(expr env e)) el in
    if il = [] then error loc "empty declaration " else
    if el = [] then
      let vl = List.map (fun i -> snd(Env.var i.id i.loc t env)) il in
      TEvars(vl,[]), tvoid, false
    else
      if List.length il = 1 then
      let i = List.hd il in
        match exl with
        | [ex] ->
            if (eq_type ex.expr_typ t) then
            let v = snd( Env.var i.id i.loc t env) in
            TEvars([v],[ex]), tvoid, false 
          else
            error loc "expression type is not valid "
        | _ -> error loc "unbalanced delcaration: too many expressions"

      else 
        if List.length il = List.length el then
          if List.for_all (fun ex -> eq_type ex.expr_typ t) exl then
            let vl = List.map (fun i -> snd( Env.var i.id i.loc t env)) il in
            TEvars(vl,exl), tvoid, false
          else
            error loc "expression type is not valid "
        else if List.length exl = 1 then
          let ex = List.hd exl in
          match ex.expr_typ with
            | Tmany tl when ((List.length tl = List.length il) && (List.for_all (fun t' -> eq_type t' t) tl)) -> 
              let vl = List.map (fun i -> snd(Env.var i.id i.loc t env)) il in
              TEvars(vl,exl), tvoid, false
            | _ -> error loc "wrong number/type of expressions "
        else
          error loc "wrong number of expressions "

let found_main = ref false

(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id = id; loc = loc }} -> () (*TODO*)
  | PDfunction _ -> ()


let rec sizeof = function
  | Tint | Tbool | Tstring | Tptr _ -> 8
  | Tmany l -> List.fold_left (fun s t -> s + sizeof t) 0 l
  | _ -> (* TODO *) assert false 

(* 2. declare functions and type fields *)
let phase2 = function
  | PDfunction ({ pf_name={id; loc}; pf_params=pl; pf_typ=tyl; } as f)->
      if  id = "main" then (
        if pl = [] && tyl = [] then
          found_main := true
        else
          error loc "main must have 0 arguments and be of type void "
      );
      FuncEnv.add f;
      FuncEnv.varduplicates f;
      FuncEnv.paramtypes f;
      FuncEnv.outtype f;
  | PDstruct { ps_name = {id}; ps_fields = fl } ->
     (* TODO *) () 

(* 3. type check function bodies *)
let decl = function
  | PDfunction { pf_name={id; loc}; pf_params = par; pf_body = e; pf_typ=tyl } ->
    let env = ref Env.empty 
    and params = ref [] in
    List.iter (fun par -> let (e,v) = Env.var ((fst(par)).id) ((fst(par)).loc) (type_type (snd(par))) !env in env := e; params := v::!params) par;
    let ty = List.map type_type tyl in
    let f = { fn_name = id; fn_params = !params; fn_typ = ty} in
    rettyp := ty;
    let e, rt = expr !env e in
    if rt then
      if ty = [] then
        error loc "void function cannot return any value "
      else
        TDfunction (f, e)
    else
      if ty = [] then
        TDfunction (f, e)
      else
        error loc "non-void function must return a value "
  | PDstruct {ps_name={id}} ->
    (* TODO *) let s = { s_name = id; s_fields = Hashtbl.create 5; s_size = 0 } in
     TDstruct s

let file ~debug:b (imp, dl) =
  debug := b;
  fmt_imported := imp;
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  (*Env.check_unused (); (* TODO variables non utilisees *)*)
  if imp && not !fmt_used then (*error dummy_loc "fmt imported but not used";*) ();
  dl
