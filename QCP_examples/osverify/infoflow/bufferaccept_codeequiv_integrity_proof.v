Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs.
Require Import prt_apispecs.
Require Import buffer_apispecs.
Require Import intspecs.
Require Import osspecs.
Require Import properties.

Require Import data_invs.
Require Import equiv_prop.
Require Import if_assms.
Require Import if_succ_gen.
Require Import if_good_code.

Require Import hasrt_sat_preserve.
Require Import FunctionalExtensionality.

Require Import integrity_lemma.
Set Keyed Unification.
Require Import protect.
Require Import spec_aux_defs.
Require Import if_common_lemmas.

Lemma bufferaccept_nabt_spec_step_code_equiv_tskd'_preserve :
forall O cd  n vl sd cd' O' act ke ks t T i pr,
good_task_code T->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
bufferaccept vl <> ABORT -> 
nth_error (get_all_succs (bufferaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O' ->
code_equiv_tskd' i T (set T t (curs (hapi_code cd'), (ke, ks))) O O'.
Proof.
introv Hgtc Htpi Hctid Hgett Hnabt Hnth Hstep Hi_neq HO_neq.
remember vl as qp_vl.
lets Hnn: Hnth.
protect Hnn.
do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse).
clear Hnabt.
(* n = 0 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 1 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 2 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 3 *)
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
destruct n; [ my_succs_solver_same_absdata | idtac].
(* qacc_succ_body *)
inverts H3; simpljoin.
destruct H6 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid
(absecblist (set x7 x (absmsgq x9 x10 x11, x12)))).
eapply join_get_set_eq;eauto.
clear H3.
remember O as Ox.
clear HeqOx.
unfolds; intros.
lets Hm:tid_unique_set_ntls H2 H3 H0; eauto.
destruct Hm; auto.
intro; tryfalse.
subst i.

casetac pr pr0 Heq Hp_neq.
subst.
tryfalse.

lets Hn: task_prio_id_tidneq Htpi H2 Hp_neq.
rewrite set_a_get_a' ; eauto.
split;eauto. 
remember ((Aif | (buffer_indom (Vptr x1), nil)
| (fun _ : osabst => Vptr x1 = Vnull)
{asrt_and_ret (|v0 :: Vnull :: nil|)}
else {Aif (fun O : osabst =>
           exists qid qls,
           Vptr x1 = Vptr qid /\
           get O absecblsid = Some (absecblist qls) /\
           ~
           (exists x y pwl wls,
            get qls qid = Some (absmsgq x y pwl, wls)))
      {asrt_and_ret (|v0 :: Vnull :: nil|)}
      else {Aif (fun O : osabst =>
                 exists qid qls,
                 Vptr x1 = Vptr qid /\
                 get O absecblsid = Some (absecblist qls) /\
                 (exists wls n pwl,
                  get qls qid = Some (absmsgq nil n pwl, wls)))
            {asrt_and_ret (|v0 :: Vnull :: nil|)}
            else {Aif (fun O : osabst =>
                       exists qid qls msg0 mls n wl,
                       Vptr x1 = Vptr qid /\
                       get O absecblsid =
                       Some (absecblist qls) /\
                       get qls qid =
                       Some (absmsgq (msg0 :: mls) n nil, wl))
                  {qacc_succ_body (|Vptr x1 :: v0 :: nil|)}
                  else {ASSUME (fun _ : osabst => False)}}}});;
(fun (_ : osabst) (_ : priority) => True, v0 :: nil) # ret_val
[|v0 :: nil|]) as cd.
clear Heqcd.

intros.
lets Hgdcode: Hgtc H1.
unfolds in Hgdcode. simpl in Hgdcode.
destruct Hgdcode as (Hgde & Hgdks).
unfolds in Hgde.

splits.
destruct c.
left; unfolds; left; eauto.
destruct s; 
try solve [ left; unfolds; right; eexists; splits; eauto;
                   intro; simpljoin; tryfalse].
right. eexists. splits; eauto.
unfolds in Hgde.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_accept.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferacceptapi. eauto.
intros. subst.
unfolds in Hgdks.
destruct Hgdks as (Hgdel & Hgdks).
unfolds in Hgdel.
unfolds in Hgdel.
eapply head_asrt_sat_step_hold' with (sd := sd) (cd := cd); eauto.
eapply nth_error_In in Hnn; eauto.
unfolds. left.
exists buffer_accept.
do 3 eexists;splits; eauto.
unfolds. simpl. unfold bufferacceptapi. eauto.

(* qacc_succ_body *)
solve_endabt.
(* n = 4 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 5 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 6 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 7 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 8 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 9 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.










