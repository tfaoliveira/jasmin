From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.

Require Import
  expr
  linear
  linear_sem.
Require Import
  compiler_util
  protect_calls.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

Context
  {asm_op : Type}
  {pd : PointerData}
  {asmop : asmOp asm_op}
  (pcparams : protect_calls_params)
  (return_tree : funname -> seq cs_info -> bintree cs_info)
  (export_fs : seq funname)
  (protect_calls : bool)
.

Notation lti_lfd := (lti_lfd export_fs).
Notation lti_lfuncs := (lti_lfuncs export_fs).
Notation pc_lfd := (pc_lfd pcparams return_tree export_fs).
Notation pc_lprog := (pc_lprog pcparams return_tree export_fs protect_calls).

Lemma pc_lprog_invariants lp lp' :
  pc_lprog lp = ok lp' ->
  [/\ lp_rip lp = lp_rip lp'
    , lp_rsp lp = lp_rsp lp'
    & lp_globs lp = lp_globs lp'
  ].
Proof.
  case: protect_calls => /= [|[->] //].
  t_xrbindP=> _ [??].
  by t_xrbindP=> _ ? _ <-.
Qed.

Variant and11 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 : Prop) : Prop :=
  And11 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 & P11 ]" :=
  (and11 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11) : type_scope.

Lemma pc_lfd_invariants rsp cst lti_tbl fn lfd lfd' :
  (if protect_calls then pc_lfd rsp cst lti_tbl fn lfd else ok lfd) = ok lfd' ->
  [/\ lfd_info lfd = lfd_info lfd'
    , lfd_align lfd = lfd_align lfd'
    , lfd_tyin lfd = lfd_tyin lfd'
    , lfd_arg lfd = lfd_arg lfd'
    , lfd_tyout lfd = lfd_tyout lfd'
    , lfd_res lfd = lfd_res lfd'
    , lfd_export lfd = lfd_export lfd'
    , lfd_callee_saved lfd = lfd_callee_saved lfd'
    , lfd_stk_max lfd = lfd_stk_max lfd'
    , lfd_frame_size lfd = lfd_frame_size lfd'
    & lfd_align_args lfd = lfd_align_args lfd'
  ].
Proof.
  case: protect_calls => [|[->] //]. rewrite /pc_lfd. by t_xrbindP=> _ _ ? _ <-.
Qed.

Lemma lti_lfuncs_get_fundef lfuncs lfuncs' lti_tbl fn lfd :
  lti_lfuncs lfuncs = ok (lti_tbl, lfuncs') ->
  get_fundef lfuncs fn = Some lfd ->
  exists fn' lfd' lti_tbl0 lti_tbl1,
    [/\ lti_lfd lti_tbl0 fn lfd = ok (lti_tbl1, (fn', lfd'))
      & get_fundef lfuncs' fn = Some lfd'
    ].
Proof.
  elim: lfuncs lti_tbl lfuncs' fn lfd => [// | [fn0 lfd0] lfuncs hind] lti_tbl
    lfuncs' fn lfd /=.
  case: eqP => [<- | hne]; rewrite /lti_lfuncs /=.
  - t_xrbindP=> -[lti_tbl0 [??]] hlfd [??] /= ? _ <- [?]; subst lfd0.
    move: hlfd.
    rewrite /lti_lfd.
    t_xrbindP.
    case: ifP => _.
    + move=> [_ <- <-]. exists fn, lfd, lti_tbl0, lti_tbl0. by rewrite /= eqxx.
    t_xrbindP=> -[lti lc] -> [? <- <-] /=; subst lti_tbl0.
    rewrite eqxx.
    by exists fn, (with_lbody lfd lc), lti_tbl, (Mf.set lti_tbl fn lti).
  t_xrbindP=> -[lti_tbl0 [??]] _ [??] /= hfuncs _ <- hget.
Admitted.

Lemma pc_lprog_get_fundef lp lp' fn lfd :
  let: cs_tbl := call_sites_table lp in
  pc_lprog lp = ok lp' ->
  get_fundef (lp_funcs lp) fn = Some lfd ->
  exists lfd' lti_tbl,
    [/\ let: res_lfd :=
          if protect_calls
          then pc_lfd (vid (lp_rsp lp)) cs_tbl lti_tbl fn lfd
          else ok lfd
        in
        res_lfd = ok lfd'
      & get_fundef (lp_funcs lp') fn = Some lfd'
    ].
Proof.
  case: protect_calls => /= [|[->]]; first last.
  - move=> ->. by eexists lfd, (Mf.empty _).
  t_xrbindP=> _ [lti_tbl lfuncs] hlti.
  t_xrbindP=> ? hmap <- hget /=.
Admitted.

End WITH_PARAMS.
