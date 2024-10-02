(* Protect calls and returns against Spectre-RSB.
   This pass replaces [CALL]s and [RET]s by direct jumps and explicit [PUSH]
   and [POP]s.
   This pass is parametrized by the return table structure (a binary decision
   tree) for each function.
   The tree must have all the tags as nodes, and be sorted. *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require path.
From mathcomp.word Require Import word_ssrZ.

Require Import
  compiler_util
  expr
  fexpr
  label
  linear
  return_address_kind
  strings.
Require oseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

#[local]
Open Scope Z.

Module E.

  Definition pass : string := "protect calls".

  (* TODO_RSB: Depending on the checker, some of these might be user errors and
     not internal ones. *)

  Definition assoc_failed : pp_error_loc :=
    pp_internal_error_s pass "assoc failed".

  Definition debug : pp_error_loc :=
    pp_internal_error_s pass "debug failed".

  Definition cant_get_lti : pp_error_loc :=
    pp_internal_error_s pass "can't get load tag info".

  Definition invalid_use_vars : pp_error_loc :=
    pp_internal_error_s pass "invalid Ouse_vars".

  Definition invalid_state : pp_error_loc :=
    pp_internal_error_s pass "invalid protect calls state".

  Definition cant_get_lta : pp_error_loc :=
    pp_internal_error_s pass "can't get load tag arguments".

  Definition cant_get_tag_reg : pp_error_loc :=
    pp_internal_error_s pass "can't get register with tag".

  Definition gen_err_msg
    (pre : string) (ii : instr_info) (omsg : option string) : pp_error_loc :=
    let reason :=
      concat "" (if omsg is Some msg then [:: "("; msg; ")" ]%string else [::])
    in
    {|
      pel_msg := pp_box ([:: PPEstring pre; PPEstring reason ]);
      pel_fn := None;
      pel_fi := None;
      pel_ii := Some ii;
      pel_vi := None;
      pel_pass := Some pass;
      pel_internal := true;
    |}.

  Definition save_tag_failed := gen_err_msg "can't save return tag".

  Definition lower_ret_failed := gen_err_msg "could not lower Lret".

  Definition lower_update_after_call_failed :=
    gen_err_msg "Could not lower update after call".

End E.


Section WITH_PARAMS.

Context
  {asm_op : Type}
  {pd : PointerData}
  {asmop : asmOp asm_op}
  {pT : progT}.


(* ------------------------------------------------------------------------ *)

Section CALL_SITE_TABLE.
  (* Compute the call graph for the program.
     Keep track of maximum labels in each function (to generate fresh ones)
     and assign unique tags to each call site. *)

  (* Return info is the name of the callee and the return label. *)
  Notation ret_info := (funname * label)%type (only parsing).

  (* We keep track of return labels and assign unique tags to them (unique
     within each callee). *)
  Definition cs_info : Type := remote_label * Z.

  (* We collect for each function all return labels and their tags, and also
     their maximum internal label of the function. *)
  Definition cst_value : Type := seq cs_info * label.

  Definition cs_table : Type := Mf.t cst_value.

  Definition cst_lookup (cst : cs_table) (fn : funname) : cst_value :=
    if Mf.get cst fn is Some x then x else ([::], xH).

  (* Return the maximum label, and a list of callees and their return labels. *)
  Fixpoint label_info
    (ris : seq ret_info) (max_lbl : label) (lc : lcmd) : seq ret_info * label :=
    match lc with
    | MkLI _ (Lcall _ (fn, _)) :: MkLI _ (Llabel ExternalLabel lbl) :: lc =>
        label_info ((fn, lbl) :: ris) (Pos.max max_lbl lbl) lc
    | MkLI _ (Llabel InternalLabel lbl) :: lc =>
        label_info ris (Pos.max max_lbl lbl) lc
    | _ :: lc => label_info ris max_lbl lc
    | [::] => (ris, max_lbl)
    end.

  Definition next_tag (s : seq cs_info) : Z :=
    if s is (_, t) :: _ then Z.succ t else 0.

  (* Update the entry for the callee in [tbl] to include [(caller, ret_lbl)]. *)
  Definition acc_entry
    (caller : funname) (tbl : cs_table) (ri : ret_info) : cs_table :=
    let '(callee, ret_lbl) := ri in
    let '(old_info, max_lbl) := cst_lookup tbl callee in
    let new_info := ((caller, ret_lbl), next_tag old_info) :: old_info in
    Mf.set tbl callee (new_info, max_lbl).

  (* Update the entries of the callees of [caller], and set its max label. *)
  Definition add_call_sites
    (tbl0 : cs_table) (caller : funname) (lfd : lfundef) : cs_table :=
    let '(ris, max_lbl) := label_info [::] xH (lfd_body lfd) in
    let '(old_info, _) := cst_lookup tbl0 caller in
    let tbl1 := Mf.set tbl0 caller (old_info, max_lbl) in
    foldl (acc_entry caller) tbl1 ris.

  Definition call_sites_table (lp : lprog) : cs_table :=
    foldl (fun tbl => uncurry (add_call_sites tbl)) (Mf.empty _) (lp_funcs lp).

End CALL_SITE_TABLE.


(* ------------------------------------------------------------------------ *)

Section LOAD_TAG_INFO.
  (* Generate a map from function names to how they load the return tag.
     Remove [Ouse_vars IRpc_load_scratch] and [Ouse_vars IRpc_load_msf] from the
     code.

     Subroutines end in either one of two instructions:
     1. [Lret], and they expect the return tag on the stack (so they need a
     scratch register and an MSF).
     2. [Ligoto], and they expect the return tag in a register (general purpose
     or extra). If there is an internal [Ouse_vars IRpc_load_scratch] before then
     it carries the scratch register and it means that the return tag is in an
     extra register. *)

  Variant load_tag_info :=
    (* Scratch register and an MSF. *)
    | LTIstack of var_i & var_i
    (* Register where the tag is. *)
    | LTIregister of var_i
    (* Extra register where the tag is and scratch general purpose register. *)
    | LTIextra_register of var_i & var_i
  .

  Definition lti_table : Type := Mf.t load_tag_info.

  (* Use this instead of a list to allow the scratch register and the MSF to
     come in any order. *)
  Record lti_state :=
    {
      ltist_scratch : option var_i;
      ltist_msf : option var_i;
    }.

  Definition ltist_empty : lti_state :=
    {| ltist_scratch := None; ltist_msf := None; |}.

  Definition ltist_get_lti
    (st : lti_state) (lir : linstr_r) : cexec load_tag_info :=
    match lir, ltist_scratch st, ltist_msf st with
    | Lret, Some r, Some msf => ok (LTIstack r msf)
    | Ligoto (Rexpr (Fvar r)), Some r', None => ok (LTIextra_register r r')
    | Ligoto (Rexpr (Fvar r)), None, None => ok (LTIregister r)
    | _, _, _ => Error E.cant_get_lti
    end.

  Definition ltist_set_scratch
    (st : lti_state) (les : seq lexpr) : cexec lti_state :=
    if les is [:: LLvar r ]
    then ok {| ltist_scratch := Some r; ltist_msf := ltist_msf st; |}
    else Error E.invalid_use_vars.

  Definition ltist_set_msf
    (st : lti_state) (res : seq rexpr) : cexec lti_state :=
    if res is [:: Rexpr (Fvar msf) ]
    then ok {| ltist_scratch := ltist_scratch st; ltist_msf := Some msf; |}
    else Error E.invalid_use_vars.

  Fixpoint lti_lcmd
    (st : lti_state)
    (lc : lcmd) :
    cexec (load_tag_info * lcmd) :=
    match lc with
    | [::] => Error E.cant_get_lti

    | [:: MkLI _ lir ] =>
        Let lti := ltist_get_lti st lir in
        ok (lti, lc)

    | MkLI _ (Lopn les (Ointernal (Ouse_vars IRpc_load_scratch _ _)) _) :: lc =>
        Let st' := ltist_set_scratch st les in
        lti_lcmd st' lc

    | MkLI _ (Lopn _ (Ointernal (Ouse_vars IRpc_load_msf _ _)) res) :: lc =>
        Let st' := ltist_set_msf st res in
        lti_lcmd st' lc

    | li :: lc' =>
        Let: (lti, lc'') := lti_lcmd st lc' in
        ok (lti, li :: lc'')
    end.

  Definition lti_lfd
    (export_fs : seq funname)
    (tbl : lti_table)
    (fn : funname)
    (lfd : lfundef) :
    cexec (lti_table * (funname * lfundef)) :=
    if fn \in export_fs
    then ok (tbl, (fn, lfd))
    else
      Let: (lti, lbody') := lti_lcmd ltist_empty (lfd_body lfd) in
      ok (Mf.set tbl fn lti, (fn, with_lbody lfd lbody')).

  Definition lti_lfuncs
    (export_fs : seq funname)
    (lfuncs : seq (funname * lfundef)) :
    cexec (lti_table * seq (funname * lfundef)) :=
    fmapM
      (fun tbl '(fn, lfd) => lti_lfd export_fs tbl fn lfd)
      (Mf.empty _)
      lfuncs.

End LOAD_TAG_INFO.


(* ------------------------------------------------------------------------ *)
(* The pass has two parts, after the analyses above: protecting return
   instructions and protecting call instructions. *)

Variant save_tag_args :=
  (* Stack pointer. *)
  | STAstack of var_i
  (* Register to use. *)
  | STAregister of var_i
  (* Extra register to use and scratch general purpose register. *)
  | STAextra_register of var_i & var_i
.

Variant load_tag_args :=
  (* Stack pointer, scratch register and an MSF. *)
  | LTAstack of var_i & var_i & var_i
  (* Register where the tag is. *)
  | LTAregister of var_i
  (* Extra register where the tag is and scratch general purpose register. *)
  | LTAextra_register of var_i & var_i
.

Record protect_calls_params :=
  {
    pcp_is_update_after_call : sopn -> bool;

    pcp_lower_update_after_call :
      (option string -> pp_error_loc) ->
      Z -> (* Return tag of the call site to protect. *)
      var_i -> (* Register with the return tag. *)
      bintree cs_info -> (* Return tree of the callee. *)
      seq lexpr ->
      seq rexpr ->
      cexec (seq fopn_args);

    pcp_load_tag :
      (option string -> pp_error_loc) ->
      load_tag_args ->
      cexec (var_i * seq fopn_args);

    pcp_cmpi :
      (option string -> pp_error_loc) ->
      var_i ->
      Z ->
      cexec fopn_args;

    pcp_cond_ne : fexpr;
    pcp_cond_gt : fexpr;

    pcp_save_ra :
      (option string -> pp_error_loc) ->
      save_tag_args ->
      Z ->
      cexec (seq fopn_args);
  }.

Context
  (pcparams : protect_calls_params)
  (return_tree : funname -> seq cs_info -> bintree cs_info)
.

Section RETURN_TABLE.

Context (ii : instr_info).

Notation err := (E.lower_ret_failed ii).
Notation pcp_load_tag := (pcp_load_tag pcparams err).
Notation pcp_cmpi := (pcp_cmpi pcparams err).

(* We need to jump on the negation of the condition because conditional jumps do
   not allow far jumps, only short or near ([label] instead of
   [remote_label]). *)
Definition lcond_remote
  (cond : fexpr)
  (lbl_fresh : label)
  (lbl_remote : remote_label) :
  cexec (seq linstr_r) :=
  ok [:: Lcond cond lbl_fresh
       ; Lgoto lbl_remote
       ; Llabel InternalLabel lbl_fresh
     ].

(* General case, when the tree is [BTnode(pos, t0, t1)]:
       CMP ra, tag
       JMPeq tag
       JMPgt l_gt
       code for t0
       l_gt:
       code for t1

  If one of the two subtrees is empty, we don't introduce the [JMPgt] or
  [l_gt]. *)
Fixpoint lcmd_of_tree
  (ra : var_i)
  (lbl : label) (* Fresh label. *)
  (t : bintree cs_info) :
  cexec (seq linstr_r * label) :=
  match t with
  | BTleaf => ok ([::], lbl)
  | BTnode (ret_lbl, tag) BTleaf BTleaf =>
      ok ([:: Lgoto ret_lbl ], lbl)
  | BTnode (ret_lbl, tag) t0 t1 =>
      Let cmp_args := pcp_cmpi ra tag in
      Let jmpeq := lcond_remote (pcp_cond_ne pcparams) lbl ret_lbl in
      Let: (lcmd_t0, lbl) := lcmd_of_tree ra (next_lbl lbl) t0 in
      Let: (lcmd_t1, lbl) := lcmd_of_tree ra (next_lbl lbl) t1 in
      let '(jmp_gt, lbl_gt, lbl) :=
        if is_nil lcmd_t0 || is_nil lcmd_t1
        then ([::], [::], lbl)
        else
          ( [:: Lcond (pcp_cond_gt pcparams) lbl ]
          , [:: Llabel InternalLabel lbl ]
          , next_lbl lbl
          )
      in
      let lc :=
        lir_of_fopn_args cmp_args
        :: jmpeq
        ++ jmp_gt
        ++ lcmd_t0
        ++ lbl_gt
        ++ lcmd_t1
      in
      ok (lc, lbl)
  end.

(* We don't load the tag if there is just one call site. *)
Definition return_table
  (callee : funname)
  (lta : load_tag_args)
  (csi : cst_value) :
  cexec (seq linstr_r) :=
  let '(ris, max_lbl) := csi in
  Let: (ra, args) := pcp_load_tag lta in
  let t := return_tree callee ris in
  Let: (lc, _) := lcmd_of_tree ra (next_lbl max_lbl) t in
  let pop := if lc is [:: Lgoto _ ] then [::] else map lir_of_fopn_args args in

  (* DEBUG *)
  Let _ :=
    let is_label i := if i is Llabel _ lbl then Some lbl else None in
    let is_jump i := if i is Lgoto lbl then Some lbl else None in
    let lbls := pmap is_label lc in
    let remote_lbls := map fst ris in
    let targets := pmap is_jump lc in
    assert
      [&& uniq lbls
        , all (fun l => l \in remote_lbls) targets
        & all (fun l => l \in targets) remote_lbls
      ]
      (err (Some "invalid return table"%string))
  in

  ok (pop ++ lc).

End RETURN_TABLE.


Section PASS.

Context
  (export_fs : seq funname)
  (rsp : var_i)
  (cs_tbl : cs_table)
  (lti_tbl : lti_table)
  (fn : funname)
.

Notation pcp_is_update_after_call :=
  (pcp_is_update_after_call pcparams) (only parsing).
Notation pcp_lower_update_after_call :=
  (pcp_lower_update_after_call pcparams) (only parsing).
Notation pcp_save_ra := (pcp_save_ra pcparams) (only parsing).


(* ------------------------------------------------------------------------ *)

(* TODO: Should we merge the following and [lti_lfuncs]? *)
Section DO_RETURN.
  (* Replace return instructions ([Lret] and [Ligoto]) by return tables. *)

  Definition fn_csi : cst_value := cst_lookup cs_tbl fn.

  Definition get_lta : cexec load_tag_args :=
    match Mf.get lti_tbl fn with
    | None => Error E.cant_get_lta
    | Some (LTIstack r msf) => ok (LTAstack rsp r msf)
    | Some (LTIregister r) => ok (LTAregister r)
    | Some (LTIextra_register rx r) => ok (LTAextra_register rx r)
    end.

  Definition do_ret (ii : instr_info) (csi : cst_value) : cexec lcmd :=
    Let irs :=
      if csi is ([::], _)
      then Error (E.lower_ret_failed ii (Some "empty return table"%string))
      else Let lta := get_lta in return_table ii fn lta csi
    in
    ok (map (MkLI ii) irs).

  Definition do_ret_li (li : linstr) : cexec lcmd :=
    match li with
    | MkLI ii Lret => do_ret ii fn_csi
    | MkLI ii (Ligoto _) => do_ret ii fn_csi
    | _ => ok [:: li ]
    end.

  Definition do_ret_lcmd (lc : lcmd) : cexec lcmd :=
    conc_mapM do_ret_li lc.

End DO_RETURN.


(* ------------------------------------------------------------------------ *)

Section DO_CALLS.
  (* Replace call instructions by jumps, lower [update_after_call], and remove
     [Ouse_vars IRpc_save_scratch].

     When we find a [Ouse_vars IRpc_save_scratch] we need to keep the scratch
     register for when we find an [Lcall].
     When we find an [Lcall], we need to keep the return table, tag and load
     tag info for when we find an [update_after_call].

     [Ouse_vars IRpc_save_scratch] can overwrite [STcall], this means that the
     last call needs no [update_after_call]. *)

  Variant state :=
    | STempty
    | STscratch of var_i
    | STupdate_args of seq cs_info & Z & var_i
  .

  Definition get_sta
    (st : state) (ra_loc : option var_i) : save_tag_args * state :=
    match ra_loc, st with
    | Some rx, STscratch r => (STAextra_register rx r, STempty)
    | Some r, _ => (STAregister r, st)
    | None, _ => (STAstack rsp, st)
    end.

  Definition get_update_args
    (st : state) : cexec (seq cs_info * Z * var_i * state) :=
    if st is STupdate_args ris tag r
    then ok (ris, tag, r, STempty)
    else Error E.invalid_state.

  Definition set_scratch (les : seq lexpr) : cexec state :=
    if les is [:: LLvar r ]
    then ok (STscratch r)
    else Error E.invalid_use_vars.

  Definition set_update_args
    (st : state)
    (ris : seq cs_info)
    (tag : Z)
    (r : var_i) :
    cexec state :=
    if st is STempty
    then ok (STupdate_args ris tag r)
    else Error E.invalid_state.

  Definition get_tag_reg (callee : funname) : cexec var_i :=
    match Mf.get lti_tbl callee with
    | None => Error E.cant_get_tag_reg
    | Some (LTIstack r _) => ok r
    | Some (LTIregister r) => ok r
    | Some (LTIextra_register _ r) => ok r
    end.

  Definition do_call
    (ii : instr_info)
    (st : state)
    (ra_loc : option var_i)
    (callee : remote_label)
    (ret_lbl : label) :
    cexec (lcmd * state) :=
    let (ris, _) := cst_lookup cs_tbl callee.1 in
    Let tag := o2r E.assoc_failed (assoc ris (fn, ret_lbl)) in
    let '(sta, st') := get_sta st ra_loc in

    (* We don't need to save the tag if we are the only caller of callee. *)
    Let cmd_push :=
      match ris with
      | [::] => Error (E.save_tag_failed ii (Some "invalid table"%string))
      | [:: _ ] => ok [::]
      | _ =>
        Let args := pcp_save_ra (E.save_tag_failed ii) sta tag in
        ok (map (li_of_fopn_args ii) args)
      end
    in
    let lc := rcons cmd_push (MkLI ii (Lgoto callee)) in

    Let r := get_tag_reg callee.1 in
    Let st'' := set_update_args st' ris tag r in

    ok (lc, st'').

  (* TODO_RBS: Here we recompute the tree. It would be good to share it with
     [return_table]. Maybe [cst_value] holds a [cs_info bintree] instead of a
     list, but then we need to implement tree lookups and such. *)
  Definition do_update_after_call
    (ii : instr_info)
    (st : state)
    (les : seq lexpr)
    (res : seq rexpr)
    : cexec (lcmd * state) :=
    let err := E.lower_update_after_call_failed ii in
    Let: (ris, tag, r, st') := get_update_args st in
    let t := return_tree fn ris in
    Let args := pcp_lower_update_after_call err tag r t les res in
    ok (map (li_of_fopn_args ii) args, st').

  Fixpoint do_call_lcmd (st : state) (lc : lcmd) : cexec lcmd :=
    match lc with
    | MkLI _ (Lopn les (Ointernal (Ouse_vars IRpc_save_scratch _ _)) _) :: lc =>
        Let st' := set_scratch les in
        do_call_lcmd st' lc

    | MkLI ii (Lcall ra_loc callee)
        :: MkLI _ (Llabel ExternalLabel ret_lbl) as li_ret_lbl
        :: lc =>
        Let: (cmd_call, st') := do_call ii st ra_loc callee ret_lbl in
        Let rest := do_call_lcmd st' lc in
        ok (cmd_call ++ li_ret_lbl :: rest)

    | MkLI ii (Lopn les op res) as li_opn :: lc =>
        Let: (cmd_update, st') :=
          if pcp_is_update_after_call op
          then do_update_after_call ii st les res
          else ok ([:: li_opn ], st)
        in
        Let rest := do_call_lcmd st' lc in
        ok (cmd_update ++ rest)

    | li :: lc =>
        Let rest := do_call_lcmd st lc in
        ok (li :: rest)

    | [::] => ok [::]
    end.

End DO_CALLS.

Definition pc_lfd (lfd : lfundef) : cexec lfundef :=
  (* Export functions don't need protected returns. *)
  Let lbody_ret :=
    if fn \in export_fs
    then ok (lfd_body lfd)
    else do_ret_lcmd (lfd_body lfd)
  in
  Let lbody_call := do_call_lcmd STempty lbody_ret in
  ok (with_lbody lfd lbody_call).

End PASS.


(* TODO_RSB: Remove. *)
Section DEBUG.

Let get_label (i : linstr) : option label :=
  if li_i i is Llabel _ lbl then Some lbl else None.

Let labels_in_lcmd (body: lcmd) : seq label :=
  pmap get_label body.

Let is_max_label_in_fbody (lp : lprog) (fn : funname) (l : label) : bool :=
  if get_fundef (lp_funcs lp) fn is Some fd
  then all (fun x => x <=? l)%positive (labels_in_lcmd (lfd_body fd))
  else false.

Definition chk_f lp (fn : funname) (v : cst_value) : bool :=
  let '(s, max_lbl) := v in
  let tags := map snd s in
  [&& path.sort (fun x y => x <? y) tags == ziota 0 (Z.of_nat (size tags))
    & is_max_label_in_fbody lp fn max_lbl
  ].

End DEBUG.

Definition pc_lprog
  (export_fs : seq funname) (protect_calls : bool) (lp : lprog) : cexec lprog :=
  if protect_calls
  then
    let cs_tbl := call_sites_table lp in

    (* TODO_RSB: Remove. *)
    Let _ := assert (Mf.all (chk_f lp) cs_tbl) E.debug in

    Let: (lti_tbl, lfuncs) := lti_lfuncs export_fs (lp_funcs lp) in
    let f := pc_lfd export_fs (vid (lp_rsp lp)) cs_tbl lti_tbl  in
    Let lfds := map_cfprog_name_gen lfd_info f lfuncs in
    ok (with_lfds lp lfds)
  else ok lp.

End WITH_PARAMS.
