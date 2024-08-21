From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From mathcomp Require Import word_ssrZ.

Require Import
  arch_params
  compiler_util
  expr
  fexpr.
Require Import
  linearization
  lowering
  stack_alloc
  stack_zeroization
  slh_lowering.
Require
  constant_prop
  protect_calls.
Require Import
  arch_decl
  arch_extra
  asm_gen
  label.
Require Import
  x86_decl
  x86_extra
  x86_instr_decl
  x86_lowering
  x86_stack_zeroization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Section.
Context {atoI : arch_toIdent}.

(* Used to set up stack. *)
Definition x86_op_align (x : var_i) (ws : wsize) (al : wsize) : fopn_args :=
  let f_to_lvar x := LLvar (mk_var_i (to_var x)) in
  let eflags := map f_to_lvar [:: OF; CF; SF; PF; ZF ] in
  let ex := Rexpr (Fvar x) in
  let emask := fconst ws (- wsize_size al) in
  (eflags ++ [:: LLvar x ], Ox86 (AND ws), [:: ex; Rexpr emask ]).

(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition lea_ptr x y tag ofs : instr_r :=
  Copn [:: x] tag (Ox86 (LEA Uptr)) [:: add y (cast_const ofs)].

Definition x86_mov_ofs x tag vpk y ofs :=
  let addr :=
    if mk_mov vpk is MK_LEA
    then
      lea_ptr x y tag ofs
    else
      if ofs == 0%Z
      then mov_ws Uptr x y tag
      else lea_ptr x y tag ofs
  in
  Some addr.

Definition x86_immediate x z :=
  mov_ws Uptr (Lvar x) (cast_const z) AT_none.

Definition x86_swap t (x y z w : var_i) :=
  Copn [:: Lvar x; Lvar y] t (Ox86 (XCHG reg_size)) [:: Plvar z; Plvar w].

Definition x86_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := x86_mov_ofs;
    sap_immediate := x86_immediate;
    sap_swap := x86_swap;
  |}.

(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Section LINEARIZATION.

Notation vtmpi := (mk_var_i (to_var RAX)).
Notation vtmp2i := (mk_var_i (to_var R10)).

Definition x86_allocate_stack_frame (rspi: var_i) (tmp: option var_i) (sz: Z) :=
  let p := Fapp2 (Osub (Op_w Uptr)) (Fvar rspi) (fconst Uptr sz) in
  [:: ([:: LLvar rspi ], Ox86 (LEA Uptr), [:: Rexpr p ])].

Definition x86_free_stack_frame (rspi: var_i) (tmp: option var_i) (sz: Z) :=
  let p := Fapp2 (Oadd (Op_w Uptr)) (Fvar rspi) (fconst Uptr sz) in
  [:: ([:: LLvar rspi ], Ox86 (LEA Uptr), [:: Rexpr p ])].

(* TODO: consider using VMOVDQA when the address is known to be aligned *)
Definition x86_lassign (x: lexpr) (ws: wsize) (e: rexpr) :=
  let op := if (ws <= U64)%CMP
            then MOV ws
            else VMOVDQU ws
  in ([:: x ], Ox86 op, [:: e ]).

Definition x86_set_up_sp_register
  (rspi : var_i) (sf_sz : Z) (al : wsize) (r : var_i) (tmp : var_i) : seq fopn_args :=
  let i0 := x86_lassign (LLvar r) Uptr (Rexpr (Fvar rspi)) in
  let i2 := x86_op_align rspi Uptr al in
  i0 :: rcons (if sf_sz != 0%Z then x86_allocate_stack_frame rspi None sf_sz else [::]) i2.

Definition x86_lmove (xd xs: var_i) :=
  x86_lassign (LLvar xd) (wsize_of_stype (vtype xd)) (Rexpr (Fvar xs)).

Definition x86_check_ws (_: wsize) := true.

Definition x86_lstore (xd : var_i) (ofs : Z) (xs :  var_i) :=
  let ws := wsize_of_stype (vtype xs) in
  x86_lassign (Store Aligned ws xd (fconst Uptr ofs)) ws (Rexpr (Fvar xs)).

Definition x86_lload (xd xs: var_i) (ofs : Z) :=
  let ws := wsize_of_stype (vtype xd) in
  x86_lassign (LLvar xd) ws (Load Aligned ws xs (fconst Uptr ofs)).

Definition x86_liparams : linearization_params :=
  {|
    lip_tmp := vname (v_var vtmpi);
    lip_tmp2 := vname (v_var vtmp2i);
    lip_not_saved_stack := [::];
    lip_allocate_stack_frame := x86_allocate_stack_frame;
    lip_free_stack_frame := x86_free_stack_frame;
    lip_set_up_sp_register := x86_set_up_sp_register;
    lip_lmove := x86_lmove;
    lip_check_ws := x86_check_ws;
    lip_lstore := x86_lstore;
    lip_lstores := lstores_dfl x86_lstore;
    lip_lloads := lloads_dfl x86_lload;
  |}.

End LINEARIZATION.

(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

Definition x86_loparams : lowering_params lowering_options :=
  {|
    lop_lower_i := lower_i;
    lop_fvars_correct := fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Speculative execution operator lowering parameters. *)

Definition lv_none_flags := nseq 5 (Lnone dummy_var_info sbool).

Definition x86_sh_lower
  (lvs : seq lval)
  (slho : slh_op)
  (es : seq pexpr) :
  option copn_args :=
  let O x := Oasm (ExtOp x) in
  match slho with
  | SLHinit   => Some (lvs, O Ox86SLHinit, es)

  | SLHupdate => Some (Lnone dummy_var_info ty_msf :: lvs, O Ox86SLHupdate, es)

  | SLHmove   => Some (lvs, O (Ox86SLHmove), es)

  | SLHprotect ws =>
      let extra :=
        if (ws <= U64)%CMP
        then lv_none_flags
        else [:: Lnone dummy_var_info (sword ws)]
      in
      Some (extra ++ lvs, O (Ox86SLHprotect ws), es)

  | SLHprotect_ptr _ | SLHprotect_ptr_fail _ => None (* Taken into account by stack alloc *)
  end.

Definition x86_update_after_call (msf : var_i) : copn_args :=
  let lvs := [:: Lnone dummy_var_info sreg; Lvar msf ] in
  let es := [:: Pvar (mk_lvar msf) ]
  in
  (lvs, Oasm (ExtOp Ox86SLHupdate_after_call), es).

Definition x86_shparams : sh_params :=
  {|
    shp_lower := x86_sh_lower;
    shp_update_after_call := fun _ msf => ok (x86_update_after_call msf);
  |}.


(* ------------------------------------------------------------------------ *)
(* Protect calls parameters. *)

Section PROTECT_CALLS.

Import protect_calls.

Section WITH_ERR.

  Context (err : option string -> pp_error_loc).
  Let err_invalid_return_tree := err (Some "invalid return tree"%string).
  Let err_empty_return_tree := err (Some "empty return tree"%string).

  Notation rvar := (fun v => Rexpr (Fvar v)) (only parsing).
  Notation rconst := (fun ws imm => Rexpr (fconst ws imm)) (only parsing).

  (* ------------------------------------------------------------------------ *)
  (* TODO: move. *)

  Definition lexpr_flags : seq lexpr :=
    map (fun f => LLvar (mk_var_i (to_var f))) [:: OF; CF; SF; PF; ZF ].

  Definition x86_fop_movi (x : var_i) (imm : Z) : fopn_args :=
    ([:: LLvar x ], Ox86 (MOV reg_size), [:: rconst reg_size imm ]).

  Definition x86_fop_movx (x y : var_i) : fopn_args :=
    ([:: LLvar x ], Ox86 (MOVX reg_size), [:: rvar y ]).

  Definition x86_fop_cmpi (x : var_i) (imm : Z) : fopn_args :=
    let res := [:: rvar x; rconst reg_size imm ] in
    (lexpr_flags, Ox86 (CMP reg_size), res).

  Definition x86_fop_protect_64 (x msf : var_i) : fopn_args :=
    let les := lexpr_flags ++ [:: LLvar x ] in
    (les, Oasm (ExtOp (Ox86SLHprotect U64)), [:: rvar x; rvar msf ]).

  (* TODO_RSB: Use [x86_free_stack_frame]. *)
  Definition x86_lcmd_pop (rsp x : var_i) : seq fopn_args :=
    let addr := Load Aligned reg_size rsp (fconst reg_size 0) in
    let rsp' :=
      Rexpr
        (Fapp2 (Oadd (Op_w reg_size)) (Fvar (mk_var_i rsp)) (fconst reg_size 8))
    in
    [:: ([:: LLvar x ], Ox86 (MOV reg_size), [:: addr ])
      ; ([:: LLvar rsp ], Ox86 (LEA reg_size), [:: rsp' ])
    ].

  (* TODO_RSB: Use [x86_allocate_stack_frame]. *)
  Definition x86_lcmd_pushi (rsp : var_i) (z : Z) : seq fopn_args :=
    let addr := Store Aligned reg_size rsp (fconst reg_size 0) in
    let rsp' :=
      Rexpr
        (Fapp2 (Osub (Op_w reg_size)) (Fvar (mk_var_i rsp)) (fconst reg_size 8))
    in
    [:: ([:: LLvar rsp ], Ox86 (LEA reg_size), [:: rsp' ])
      ; ([:: addr ], Ox86 (MOV reg_size), [:: rconst reg_size z ])
    ].

  Definition r_uncons
    {aT eT} (err : eT) (s : seq aT) : result eT (aT * seq aT) :=
    if s is a :: s' then ok (a, s') else Error err.

  (* ------------------------------------------------------------------------ *)

  Section COND.
    Import
      constant_prop
      flag_combination
    .

    Notation mk_pvar x := (Pvar (mk_lvar (mk_var_i (to_var x)))).

    Let mk_fcond cf :=
      let pvar_of := mk_pvar OF in
      let pvar_cf := mk_pvar CF in
      let pvar_sf := mk_pvar SF in
      let pvar_zf := mk_pvar ZF in
      let e := cf_xsem snot sand sor sbeq pvar_of pvar_cf pvar_sf pvar_zf cf in
      odflt (Fconst 0) (fexpr_of_pexpr e).

    Definition fcond_eq := Eval hnf in mk_fcond CF_EQ.
    Definition fcond_ne := Eval hnf in mk_fcond CF_NEQ.
    (* CF *)
    Definition fcond_lt := Eval hnf in mk_fcond (CF_LT Unsigned).
    (* !ZF && !CF *)
    Definition fcond_gt := Eval hnf in mk_fcond (CF_GT Unsigned).

  End COND.

  Definition x86_is_update_after_call (op : sopn) : bool :=
    if op is Oasm (ExtOp Ox86SLHupdate_after_call) then true else false.

  (* When we reach the last internal node, we need to know whether it's the
     leftmost (minimum tag) or rightmost (maximum tag) one to avoid recomputing
     the comparison. *)
  Variant btree_position :=
    | BTPleft
    | BTPright
    | BTPmiddle
  .

  Definition go_left (pos : btree_position) : btree_position :=
    if pos is BTPleft then BTPleft else BTPmiddle.

  Definition go_right (pos : btree_position) : btree_position :=
    if pos is BTPright then BTPright else BTPmiddle.

  Section UPDATE_AFTER_CALL.
    Context
      (tag : Z)
      (ra : var_i)
    .

    Fixpoint update_after_call_cond
      (pos : btree_position)
      (t : bintree cs_info) :
      cexec (seq fopn_args * fexpr) :=
      match t with
      | BTleaf => Error err_invalid_return_tree
      | BTnode (_, tag') BTleaf BTleaf =>
          Let _ := assert (tag == tag') err_invalid_return_tree in
          match pos with
          | BTPleft => ok ([::], fcond_lt)
          | BTPright => ok ([::], fcond_gt)
          | BTPmiddle => ok ([:: x86_fop_cmpi ra tag ], fcond_eq)
          end
      | BTnode (_, tag') t0 t1 =>
          match Z.compare tag tag' with
          | Eq => ok ([::], fcond_eq)
          | Lt => update_after_call_cond (go_left pos) t0
          | Gt => update_after_call_cond (go_right pos) t1
          end
      end.

    Definition lower_update_after_call
      (t : bintree cs_info)
      (les : seq lexpr)
      (res : seq rexpr) :
      cexec (seq fopn_args) :=
      match t with
      | BTleaf => Error err_empty_return_tree
      | BTnode _ BTleaf BTleaf => ok [::]
      | _ =>
          Let: (pre, cond) := update_after_call_cond BTPleft t in
          let update := (les, Oasm (ExtOp Ox86SLHupdate), Rexpr cond :: res) in
          ok (rcons pre update)
      end.

  End UPDATE_AFTER_CALL.

  (* TODO_RSB: We should always protect. *)
  Definition load_tag (lta : load_tag_args) : var_i * seq fopn_args :=
    let '(ra, args) :=
      match lta with
      | LTAstack rsp r msf =>
          (r, x86_lcmd_pop rsp r ++ [:: x86_fop_protect_64 r msf ])
      | LTAregister ra => (ra, [::])
      | LTAextra_register rx r => (r, [:: x86_fop_movx r rx ])
      end
    in
    (ra, args).

  Definition save_ra
    (err : option string -> pp_error_loc)
    (sral : save_tag_args)
    (tag : Z)
    : cexec (seq fopn_args) :=
    let c :=
      match sral with
      | STAstack rspi => x86_lcmd_pushi rspi tag
      | STAregister r => [:: x86_fop_movi r tag ]
      | STAextra_register rx r =>
          [:: x86_fop_movi r tag
            ; x86_fop_movx rx r
          ]
      end
    in ok c.

End WITH_ERR.

Definition x86_pcparams : protect_calls_params :=
  {|
    pcp_is_update_after_call := x86_is_update_after_call;
    pcp_lower_update_after_call := lower_update_after_call;
    pcp_load_tag := fun _ lta => ok (load_tag lta);
    pcp_cmpi := fun _ r tag => ok (x86_fop_cmpi r tag);
    pcp_cond_ne := fcond_ne;
    pcp_cond_gt := fcond_gt;
    pcp_save_ra := save_ra;
  |}.

End PROTECT_CALLS.


(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

Definition not_condt (c : condt) :=
  match c with
  | O_ct => NO_ct
  | NO_ct => O_ct
  | B_ct => NB_ct
  | NB_ct => B_ct
  | E_ct => NE_ct
  | NE_ct => E_ct
  | BE_ct => NBE_ct
  | NBE_ct => BE_ct
  | S_ct => NS_ct
  | NS_ct => S_ct
  | P_ct => NP_ct
  | NP_ct => P_ct
  | L_ct => NL_ct
  | NL_ct => L_ct
  | LE_ct => NLE_ct
  | NLE_ct => LE_ct
  end.

Definition or_condt ii e c1 c2 : cexec condt :=
  match c1, c2 with
  | L_ct, E_ct => ok LE_ct
  | E_ct, L_ct => ok LE_ct
  | B_ct, E_ct => ok BE_ct
  | E_ct, B_ct => ok BE_ct
  | _, _ => Error (E.berror ii e "Invalid condition (OR)")
  end.

Definition and_condt ii e c1 c2 :=
  match c1, c2 with
  | NB_ct, NE_ct => ok NBE_ct
  | NE_ct, NB_ct => ok NBE_ct
  | NE_ct, NL_ct => ok NLE_ct
  | NL_ct, NE_ct => ok NLE_ct
  | _, _ => Error (E.berror ii e "Invalid condition (AND)")
  end.

Definition of_var_e_bool ii (v: var_i) : cexec rflag :=
  match of_var v with
  | Some r => ok r
  | None => Error (asm_gen.E.invalid_flag ii v)
  end.

Fixpoint assemble_cond_r ii (e : fexpr) : cexec condt :=
  match e with
  | Fvar v =>
      Let r := of_var_e_bool ii v in
      match r with
      | OF => ok O_ct
      | CF => ok B_ct
      | ZF => ok E_ct
      | SF => ok S_ct
      | PF => ok P_ct
      end

  | Fapp1 Onot e =>
      Let c := assemble_cond_r ii e in
      ok (not_condt c)

  | Fapp2 Oor e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      or_condt ii e c1 c2

  | Fapp2 Oand e1 e2 =>
      Let c1 := assemble_cond_r ii e1 in
      Let c2 := assemble_cond_r ii e2 in
      and_condt ii e c1 c2

  | Fapp2 Obeq (Fvar x1) (Fvar x2) =>
      Let r1 := of_var_e_bool ii x1 in
      Let r2 := of_var_e_bool ii x2 in
      if ((r1 == SF) && (r2 == OF)) || ((r1 == OF) && (r2 == SF))
      then ok NL_ct
      else Error (E.berror ii e "Invalid condition (NL)")

  | _ => Error (E.berror ii e "don't known how to compile the condition")

  end.

Definition assemble_cond ii (e: fexpr) : cexec condt :=
  assemble_cond_r ii e.

Definition x86_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.

(* ------------------------------------------------------------------------ *)
(* Stack zeroization parameters. *)

Definition x86_szparams : stack_zeroization_params :=
  {|
    szp_cmd := x86_stack_zero_cmd;
  |}.

(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition x86_is_move_op (o : asm_op_t) :=
  match o with
  | BaseOp (None, MOV _) => true
  | BaseOp (None, VMOVDQA _) => true
  | BaseOp (None, VMOVDQU _) => true
  | ExtOp Ox86SLHmove => true
  | _ => false
  end.

(* ------------------------------------------------------------------------ *)

Definition x86_params : architecture_params lowering_options :=
  {|
    ap_sap := x86_saparams;
    ap_lip := x86_liparams;
    ap_lop := x86_loparams;
    ap_agp := x86_agparams;
    ap_szp := x86_szparams;
    ap_shp := x86_shparams;
    ap_pcp := x86_pcparams;
    ap_is_move_op := x86_is_move_op;
  |}.

End Section.
