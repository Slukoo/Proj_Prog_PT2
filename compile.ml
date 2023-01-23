(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...

*)

open Format
open Ast
open Tast
open X86_64

exception Anomaly of string

let debug = ref false

let strings = Hashtbl.create 32
let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  exit_label: string;
  ofs_this: int;
  nb_locals: int ref; (* maximum *)
  next_local: int; (* 0, 1, ... *)
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0 }

let fun_env f =
    { empty_env with exit_label = "E_" ^ f.fn_name; nb_locals = ref 0}

let mk_bool d = { expr_desc = d; expr_typ = Tbool }

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f=
  let l_true = new_label () and l_end = new_label () in
  f l_true ++
  movq (imm 0) (reg rdi) ++ jmp l_end ++
  label l_true ++ movq (imm 1) (reg rdi) ++ label l_end


let rec addspaces l =
  match l with
  | [] -> []
  | [printcall] -> [printcall]
  | printcall :: l' -> printcall :: (call "print_space") :: (addspaces l') 

let rec vecttype_size typelist= 
  match typelist with
  | [] -> 0
  | typ :: tl -> (sizeof typ) + vecttype_size tl

let rec expr env e = 

  match e.expr_desc with 
  | TEskip ->
    nop
  | TEconstant (Cbool true) ->
    movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)
  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)
  | TEnil ->
    xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) ->
    movq (ilab (alloc_string s)) (reg rdi)
  | TEbinop (Band, e1, e2) -> 
    let labelend = new_label () in 
      expr env e1 ++
      cmpq (imm 0) (reg rdi) ++
      je labelend ++
      expr env e2 ++
      label labelend

  | TEbinop (Bor, e1, e2) -> 
    let labelend = new_label () in 
      expr env e1 ++
      cmpq (imm 1) (reg rdi) ++
      je labelend ++
      expr env e2 ++
      label labelend

  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) ->
    let c = 
      match op with
        |Blt -> cmovl
        |Ble -> cmovle
        |Bgt -> cmovg
        |Bge -> cmovge
        | _ -> assert false
    in
    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    popq rsi ++
    cmpq (reg rdi) (reg rsi) ++
    movq (imm 0) (reg rdi) ++
    movq (imm 1) (reg rsi) ++
    c (reg rsi) (reg rdi)

  | TEbinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1, e2) ->
    let instr = 
      match op with
        |Badd -> addq (reg rsi) (reg rdi)
        |Bsub -> subq (reg rsi) (reg rdi)
        |Bmul -> imulq (reg rsi) (reg rdi)
        |Bdiv -> movq (reg rdi) (reg rax) ++ cqto ++ idivq (reg rdi) ++ movq (reg rax) (reg rdi)
        |Bmod -> movq (reg rdi) (reg rax) ++ cqto ++ idivq (reg rdi) ++ movq (reg rdx) (reg rdi)
        | _ -> assert false
    in
    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    pushq (reg rdi) ++
    popq rsi ++
    popq rdi ++
    instr


  | TEbinop (Beq | Bne as op, e1, e2) ->
    let c =
      match op with
      | Beq -> cmove
      | Bne -> cmovne
      | _ -> assert false
    in
    expr env e1 ++
    pushq (reg rdi) ++
    expr env e2 ++
    popq rsi ++
    cmpq (reg rdi) (reg rsi) ++
    movq (imm 0) (reg rdi) ++
    movq (imm 1) (reg rsi) ++
    c (reg rsi) (reg rdi)

  | TEunop (Uneg, e1) ->
    expr env e1 ++
    negq (reg rdi)
  | TEunop (Unot, e1) ->
    expr env e1 ++
    cmpq (imm 0) (reg rdi) ++
    sete (reg dil)
  | TEunop (Uamp, e1) ->
    addr env e1
  | TEunop (Ustar, e1) ->
    expr env e1 ++
    movq (ind rdi) (reg rdi)
  | TEprint el ->
    let prints = List.map (fun e ->
      let printcall = match e.expr_typ with
        | Tint -> call "print_int"
        | Tbool -> call "print_bool"
        | Tstring -> call "print_string"
        | Tptr _ -> call "print_ptr"
        | Tstruct s -> call ("print_struct_"^s.s_name)
        | Tptrnil -> call "print_nil"
        | _ -> nop
      in expr env e ++ printcall) el in
    List.fold_left (fun c e -> c ++ e) nop ( addspaces prints)
  | TEident x ->
    movq (ind ~ofs:x.v_addr rbp) (reg rdi)
  
  | TEassign ([lv], [e]) ->
    addr env lv ++
    pushq (reg rdi) ++
    expr env e ++ 
    popq rsi ++
    movq (reg rdi) (ind rsi)
  | TEassign (lvl, [e]) ->
    List.fold_left (fun code lv ->
      code ++
      addr env lv ++
      movq (reg r13) (ind rdi)) 
      
      (expr env e ++
      movq (reg rdi) (reg r13)) 
      
      (List.rev lvl)
  | TEassign (lvl, el) ->
    (List.fold_left (fun code e ->
      code ++
      expr env e ++
      pushq (reg rdi))
      nop
      (List.rev el)) ++
    (List.fold_left (fun code lv ->
      code ++
      addr env lv ++
      movq (reg rdi) (reg rsi) ++
      popq rdi ++
      movq (reg rdi) (ind rsi))
      nop
      lvl)
  | TEblock el ->
    let rec eval env l =
      match l with
      |[] -> nop
      |{expr_desc = TEvars (vl, el)} :: t ->
        let id = ref ((-8) * (!(env.nb_locals) + 1)) in
        List.iter (fun v -> v.v_addr <- !id  ;id := !id-8) vl;
        env.nb_locals := !(env.nb_locals) + (List.length vl);
        (if el = [] then (
          List.fold_left (fun code v ->
            code ++
            xorq (reg rdi) (reg rdi) ++
            pushq (reg rdi))
            nop
            vl)
        else (List.fold_left (fun code e ->
          code ++
          expr env e ++
          (match e.expr_typ with
          | Tmany _ -> nop
          | _ -> pushq (reg rdi)
          ))
          nop
          el) ++
          eval env t)
      | e::t -> 
        expr env e ++
        eval env t
      in
      eval env el
  | TEif (e1, e2, e3) ->
      let labelend = new_label () in
      let labelelse = new_label () in
      expr env e1 ++
      cmpq (imm 0) (reg rdi) ++
      je labelelse ++
      expr env e2 ++
      jmp labelend ++
      label labelelse ++
      expr env e3 ++
      label labelend ++
      nop

  | TEfor (e1, e2) ->
      let labelend = new_label () in
      let labelloop = new_label () in
      label labelloop ++
      expr env e1 ++
      cmpq (imm 0) (reg rdi) ++
      je labelend ++
      expr env e2 ++
      jmp labelloop ++
      label labelend ++
      nop

  | TEnew ty ->
    movq (imm (sizeof ty)) (reg rdi) ++
    call "allocz" ++
    (match ty with
        | Tstruct s ->
            pushq (reg rax) ++
            movq (imm 8) (reg rdi) ++
            call "allocz" ++
            popq rdi ++
            movq (reg rdi) (ind rax) ++
            movq (reg rax) (reg rdi)
        | _ ->
            movq (reg rax) (reg rdi))
    
  | TEcall (f, el) ->
    let argtype = List.map (fun v -> v.v_typ) f.fn_params in
    let argblock_size = vecttype_size argtype
    and retblock_size = vecttype_size f.fn_typ in
    (List.fold_left (fun code e ->
      code ++
      expr env e ++
      (match e.expr_typ with
        | Tmany _ -> nop
        | _ -> pushq (reg rdi)))
      nop
      el) ++
      call ("F_"^f.fn_name) ++
     (match e.expr_typ with
      | Tmany _ -> 
        addq (imm (argblock_size + retblock_size)) (reg rsp) ++
      (let code = ref nop in
      for i = 1 to (retblock_size/8) do
        code:= !code ++ pushq (ind ~ofs:(-8 - argblock_size) rsp)
      done;
      !code)
      | _ -> addq (imm argblock_size) (reg rsp)
     )

  | TEdot (e1, f) ->
    expr env e1 ++
    (match f.f_typ with 
      | Tstruct _ -> nop (*TO DO*)
      | _ -> movq (ind ~ofs:f.f_ofs rdi) (reg rdi)
    )
  | TEvars _ ->
     assert false (* fait dans block *)
  | TEreturn [] ->
    jmp env.exit_label
  | TEreturn [e1] ->
    expr env e1 ++
    jmp env.exit_label
  | TEreturn el ->
     List.fold_left (fun code e ->
      code ++
      expr env e ++
      pushq (reg rdi))
      nop
      el
  | TEincdec (e1, op) ->
    addr env e1 ++
    (match op with
    |Inc -> incq (ind rdi)
    |Dec -> decq (ind rdi))


and addr env e = 
  (match e.expr_desc with
  | TEunop (Ustar, e) ->
    expr env e
  | TEident x -> 
    movq (reg rbp) (reg rdi) ++ 
    addq (imm x.v_addr) (reg rdi)
  | TEdot (e,x) ->
    addr env e ++
    addq (imm x.f_ofs) (reg rdi)
  | _ -> assert false)


let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  (* TODO code pour fonction *) 
  let s = f.fn_name
  and env = fun_env f in 
  label ("F_" ^ s) ++ 
  pushq (reg rbp) ++
  movq (reg rsp) (reg rbp) ++
  expr env e ++
  label env.exit_label ++
  movq (reg rbp) (reg rsp)++
  popq rbp ++
  (if List.length f.fn_typ > 1 then
    popq r14 ++
    (let code = ref nop in
      for i = 1 to (List.length f.fn_typ) do
        code:= !code ++ pushq (ind ~ofs:(-24) rsp)
      done;
      !code  ++
      pushq (reg r14))
    else nop) ++
  ret

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code


let file ?debug:(b=false) dl =
  debug := b;
  let offset decl =
    match decl with
  | TDfunction _ -> ()
  | TDstruct s -> (
    let ofs = ref 0 in
    let set_offset f =
      f.f_ofs <- !ofs;
      ofs := !ofs + sizeof(f.f_typ) in
      Hashtbl.iter (fun key f -> set_offset f) s.s_fields;)
    (*TODO ajouter la fonction print correspondante*)
  (* TODO calcul offset champs *) in List.iter offset dl;
  (* TODO code fonctions *) let funs = List.fold_left decl nop dl in
  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      funs ++
      inline "




allocz:
  pushq %rbx
  movq %rdi, %rbx
  call malloc
allocz_loop:
  decq %rbx
  movb $0, (%rax,%rbx,1)
  testq %rbx, %rbx
  jne allocz_loop
  popq %rbx
  ret

print_ptr:
  testq %rdi, %rdi
  je print_nil
  movq $S_ptr, %rdi
  xorq %rax, %rax
  call printf
  ret

print_int:
  movq %rdi, %rsi
  movq $S_int, %rdi
  xorq %rax, %rax
  call printf
  ret

print_nil:
  xorq %rax, %rax
  mov $S_nil, %rdi
  call printf
  ret

print_string:
  testq %rdi, %rdi
  je print_nil
  movq %rdi, %rsi
  movq $S_string, %rdi
  xorq %rax, %rax
  call printf
  ret

print_bool:
  xorq %rax, %rax
  test %rdi, %rdi
  je print_false
  movq $S_true, %rdi
  call printf
  ret
print_false:
  movq $S_false, %rdi
  call printf
  ret


print_space:
  movq $S_space, %rdi
  xorq %rax, %rax
  call printf
  ret
  ";
    data =
      label "S_int" ++ string "%ld" ++
      label "S_ptr" ++ string "0x%x" ++
      label "S_true" ++ string "true" ++
      label "S_false" ++ string "false" ++
      label "S_string" ++ string "%s" ++
      label "S_nil" ++ string "(nil)" ++
      label "S_space" ++ string " " ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop)
    ;
  }

