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
Require Import confidentiality_tactics.
Require Import if_common_lemmas.
Require Import ports_cproof_common.



Lemma bufferaccept_nabt_spec_step_data_equiv_tskd_preserve:
forall O cd n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
good_client_code pc ->
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)->
task_prio_id O pr t ->
get O curtid = Some (oscurt t)->
get T t = Some (curs (hapi_code cd),(ke, ks))->
bufferaccept vl <> ABORT ->
nth_error (get_all_succs (bufferaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O'->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgtc Hgcc Hrec Hnflo Htpi Hctid Hgett Hnabt Hnth Hstep.
introv Hi_neq HO_neq.
remember vl as qp_vl.
do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse).
(* try destruct v0; simpl in Hnabt; tryfalse. *)

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
inverts H3.
simpljoin.
destruct H6 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
kvextH Hecb O0 absecblsid O.
assert (O'=set O absecblsid
(absecblist (set x7 x (absmsgq x9 x10 x11, x12)))).
eapply join_get_set_eq;eauto.

clear H3.
subst.
unfolds.
lets Hrec0: Hrec.

l_rew21_inv1 (get O absecblsid).
splits.
(* ctid_equiv  *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.
intros.
eapply prio_unique_set_ntls;eauto.
intro;tryfalse.

(* bufs_equiv *)
apply reachable_get_bufsid in Hrec.
destruct Hrec as (x' & y' & Hgetx & Hgety).
unfolds.
split.
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
(* kernel_data_equiv *)
unfolds.
apply reachable_get_knldataid in Hrec.
simpljoin.
l_rew21_inv1 (get O absecblsid).
splits.
(* kernel_task_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.
intros.
split.
split;intros; destruct H13;eexists.
unfold task_prio_id.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfold task_prio_id in H13.
rewrite set_a_get_a' in H13;eauto.
intro ; tryfalse.

intros.
assert(t1 = t2).
{
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
l_rew21_inv1 (get x0 t2).
splits;eauto.

(* kernel_mq_equiv  *)
unfold kernel_mq_equiv.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.
intros.
split.
split;eauto.
intros.
rewrite H13 in H14.
inverts H14.

(* mq_equiv *)
unfolds.
destruct mq2.
do 5 destruct p.
do 8 eexists.
splits;eauto.
destruct e.
left;eauto.
right.
left;eauto.
right.
right.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
destruct Hasrt1.
tryfalse.
simpljoin.
inverts H14.
inverts H.

assert (Hneqx2: x <> t0).
{
    lets Hnewa : not_both_mq_and_buffer H1 H13 .
    intro.
    subst.
    eapply Hnewa in H17.
    tryfalse.
}
lets Hsemq: mq_ecb H1 H13 Hecb.
destruct Hsemq.
do 3 destruct H.
rewrite set_a_get_a.
eexists x13,(set x13 x (absmsgq x9 x10 x11, x12)),t0.
do 4 eexists.
splits;eauto.
rewrite set_a_get_a';eauto.
(* mq_ed_equiv *)
unfolds.
do 4 eexists.
splits;eauto.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x19.
split;eauto.

unfolds in H18.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H18.
apply H19.

intros.
simpljoin.
unfolds in H18.
simpljoin.
rewrite set_a_get_a' in H18; try intro ;tryfalse.
eexists x19.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H18.
apply H19.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x19.
split;eauto.

unfolds in H18.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H18.
apply H19.

intros.
simpljoin.
unfolds in H18.
simpljoin.
rewrite set_a_get_a' in H18; try intro ;tryfalse.
eexists x19.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H18.
apply H19.
(* ports_equiv *)
unfolds.
do 4 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
eauto.
rewrite set_a_get_a;eauto.
intros.
split;eauto.

split.
split.
intros.
simpljoin.

casetac x a Hy Hn.
subst.
rewrite H4 in H13.
inverts H13.
eexists x2.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite set_a_get_a in H13.
inverts H13.
eexists x2.
rewrite set_a_get_a' in H13;eauto.

intros.
(* tls1 = tls2 *)
casetac x a Hy Hn.
subst.
rewrite set_a_get_a in H14.
inverts H14.
rewrite set_a_get_a' in H14;eauto.
rewrite H13 in H14; inverts H14.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x2.
split;eauto.

unfolds in H17.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H17.
apply H18.

intros.
simpljoin.
unfolds in H17.
simpljoin.
rewrite set_a_get_a' in H17; try intro ;tryfalse.
eexists x2.
split;eauto.
unfolds.
do 5 eexists.
split;eauto.
(* buffer_equiv *)
inverts H.
rewrite H12 in H4;inverts H4.
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.

intros.
assert(Hix: eid = x  \/  eid <> x) by tauto.
destruct Hix.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
destruct Hasrt1.
tryfalse.
simpljoin.
inverts H2.
lets Hfb: bufidx_diff_dom Hi_neq H H4.
tryfalse.

splits.
split.
intros.
simpljoin.
do 2 eexists.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
rewrite set_a_get_a' in H4;eauto.

intros.
rewrite set_a_get_a' in H13;eauto.
rewrite H4 in H13;inverts H13.
split.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H13 in H4;inverts H4.
(* mq_ed_equiv *)
unfolds.
do 4 eexists.
splits;eauto.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x4.
split;eauto.

unfolds in H14.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H14.
apply H17.

intros.
simpljoin.
unfolds in H14.
simpljoin.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
eexists x4.
split;eauto.
unfolds.
do 5 eexists.
split;eauto.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x1.
split;eauto.

unfolds in H14.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H14.
apply H17.

intros.
simpljoin.
unfolds in H14.
simpljoin.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
eexists x1.
split;eauto.
unfolds.
do 5 eexists.
split;eauto.
(* cap_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
eauto.

intros.
split.
intros.
split;intros;eauto.

intros.
split.
split.
intros.
simpljoin.

unfolds in H14.
simpljoin.

eexists.
unfolds.
do 8 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
eauto.

intros.
simpljoin.
unfolds in H14.
simpljoin.

eexists.
unfolds.
do 8 eexists.
splits;eauto.
rewrite set_a_get_a' in H2; try intro ;tryfalse.
rewrite H1 in H2;inverts H2.
eauto.

intros.
unfolds in H14.
unfolds in H17.
simpljoin.
rewrite set_a_get_a' in H17; try intro ;tryfalse.
rewrite H14 in H17;inverts H17.
rewrite H20 in H18;inverts H18.

assert(Heqob: objp1 = objp2).
{
  destruct H21.
  destruct H19.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H19.
  simpljoin.
  tryfalse.
  simpljoin.
  inverts H17.
  eauto.
}
rewrite Heqob.
split; intros; eauto.
(* client_data_equiv *)
unfolds.
destruct cst'.
destruct p.
do 6 eexists.
splits;eauto.

(* local_envs_equiv *)
unfolds.
intros.
assert(Heqt: t1 = t2).
{
  eapply tid_unique_set_ntls;eauto.
  intro.
  tryfalse.
}
rewrite Heqt.
eauto.

(* qacc_succ_body *)
solve_endabt.
destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.




