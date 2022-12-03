
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

let new_fun =
  fun name params typ -> {}

module FuncEnv = struct
  module M = Map.Make(String)
  type t = function_ M.t
  let empty = M.empty
  let find = M.find
  let add fenv f = 
    if exists fenv f then
      error loc "duplicate function name "
    else
      M.add f.fn_name f fenv
  let exists fenv fe = M.mem f.f_name fenv
  let all_funcs = ref empty

  let func name params typ =
    let f = { fn_name = name; fn_params = params; fn_typ = typ } in
    add f, f

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

let rettyp = ref tvoid 

let list_to_typevect tl =
  match tl with
  | [x] -> x
  | _ -> Tmany tl




let rec valid_type ty =
  match ty with
  | Tint | Tstring | Tbool | Twild -> true
  | Tptr t -> valid_type t
  | Tmany _ -> false
                (*match l with
                | [] -> true
                | t::l' -> valid_type t && valid_type Tmany l'*)
  | Tstruct s -> assert false
  | _ -> false


let rec ptyp_to_typ pt =
  match pt with
  | PTident i when i.id = "string" -> Tstring
  | PTident i when i.id = "int" -> Tint
  | PTident i when i.id = "bool" -> Tbool
  | PTident i -> (*check si i.id est une structure existante*) assert false
  | PTptr pt -> Tptr (ptyp_to_typ pt)





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
    if (t1 <> t2) then 
      error loc ("bad typing ")
    else ( 
      match op with
        | Badd | Bsub | Bmul | Bdiv | Bmod -> 
          if (t1 = Tint) then 
            TEbinop(op, fst (expr env e1), fst (expr env e2)), Tint, false
          else 
            error loc ("expected int ")

        | Blt | Ble | Bgt | Bge ->
          if (t1 = Tint) then
            TEbinop(op,fst (expr env e1), fst (expr env e2)), Tbool, false
          else
            error loc ("expected int ")

        | Beq | Bne ->
          if (e1.pexpr_desc = PEnil) then
            error loc "expression must not be nil for comparison "
          else
            TEbinop(op,fst (expr env e1),fst (expr env e2)), Tbool, false

        | Band | Bor ->
          if (t1 = Tbool) then
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
        if (t = Tint) then
          TEunop(op, fst (expr env e1)), Tint, false
        else
          error loc ("expected int ")

      | Unot ->
        if (t = Tbool) then
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
      (*TODO*) assert false


  | PEfor (e, b) ->
    let e' = expr env e and b' = expr env b in
    if ((fst(b')).expr_typ = Tbool) then
      TEfor(fst(e'), fst(b')), tvoid, (snd(e'))
    else
      error loc "boolean condition expected "

  | PEif (e1, e2, e3) ->
    let e1' = expr env e1  in
    if (fst(e1')).expr_typ = Tbool then
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
      if (List.length lvl <> List.length el) then
      error loc ("unbalanced affectations ")
      else
      let lvl' = List.map (fun lv -> if islvalue lv then fst(expr env lv) else error loc "only l-values are allowed for affectation ") lvl
      and el' = List.map (fun e -> fst(expr env e)) el in
      (*TODO vérification règles*)
      TEassign (lvl', el'), tvoid, false

  | PEreturn el ->
    let rl = List.map (fun e -> fst(expr env e)) el in 
    let tl = List.map (fun e -> e.expr_typ) rl in
      if (list_to_typevect tl) = !rettyp then
        TEreturn(rl), tvoid, true
      else
        error loc "wrong return type "

  | PEblock el ->
    (*TODO delcaration de variable dans le bloc*)
      let ret = List.fold_left (fun b e -> b || snd(expr env e)) false el
      and rl = List.map (fun e -> fst(expr env e)) el in 
      TEblock(rl), tvoid, ret

  | PEincdec (e, op) ->
    let ex = fst(expr env e) in
    if (ex.expr_typ = Tint && islvalue e) then
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
            (*let tl = list_to_typevect l in*)
            let vl = List.map2 (fun t i -> snd(Env.var i.id i.loc t env)) tl il in
            TEvars(vl,exl), tvoid, false
          | _ -> error loc "wrong number/type of expressions "
      else
        error loc "wrong number of expressions "
            
  | PEvars(il,Some pt,el) -> 
    let t = ptyp_to_typ pt in
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
            if (ex.expr_typ = t) then
            let v = snd( Env.var i.id i.loc t env) in
            TEvars([v],[ex]), tvoid, false 
          else
            error loc "expression type is not valid "
        | _ -> error loc "unbalanced delcaration: too many expressions"

      else 
        if List.length il = List.length el then
          if List.for_all (fun ex -> ex.expr_typ = t) exl then
            let vl = List.map (fun i -> snd( Env.var i.id i.loc t env)) il in
            TEvars(vl,exl), tvoid, false
          else
            error loc "expression type is not valid "
        else if List.length exl = 1 then
          let ex = List.hd exl in
          match ex.expr_typ with
            | Tmany tl when ((List.length tl = List.length il) && (List.for_all (fun t' -> t' = t) tl)) -> 
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
  | PDfunction { pf_name={id; loc}; pf_params=pl; pf_typ=tyl; } ->
      if  id = "main" && pl = [] then
        found_main := true;
  | PDstruct { ps_name = {id}; ps_fields = fl } ->
     (* TODO *) () 

(* 3. type check function bodies *)
let decl = function
  | PDfunction { pf_name={id; loc}; pf_body = e; pf_typ=tyl } ->
    (* TODO check name and type *) 
    let f = { fn_name = id; fn_params = []; fn_typ = []} in
    let e, rt = expr Env.empty e in
    TDfunction (f, e)
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
