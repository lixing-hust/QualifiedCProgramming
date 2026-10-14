Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs.
Require Import prt_apispecs.
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


Lemma portaccept_nabt_spec_step_data_equiv_tskd_preserve:
forall O cd n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
good_client_code pc ->
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)->
task_prio_id O pr t ->
get O curtid = Some (oscurt t)->
get T t = Some (curs (hapi_code cd),(ke, ks))->
portaccept vl <> ABORT ->
nth_error (get_all_succs (portaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O'->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgtc Hgcc Hrec Hnflo Htpi Hctid Hgett Hnabt Hnth Hstep.
introv Hi_neq HO_neq.
lets Hasrt: rch_hasrt_sat Hrec Hgett Htpi.
remember vl as recv_vl.
do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
try destruct v0; simpl in Hnabt; tryfalse.
clear Hnabt.
(* n = 0 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 1 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 2 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 3 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 4 *)
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
destruct n; [ my_succs_solver_same_absdata | idtac].
(* receive_port_msg *)
inverts H3; simpljoin.
inverts H9.
inverts H.
unfolds in H4.
simpljoin.
kvextH Hcid O0 curtid O.  
kvextH Hosdp O0 osdomainportid O. 
kvextH Hoskpt O0 obufsid O. 
unfolds in H4.
simpljoin.
kvextH Htcb O0 abtcblsid O. 
assert (O'=set (set O osdomainportid (osdomainport x11)) obufsid
(obufs
   (upd_bufmp x9 (dom_for_prio x13)
      (x9 (dom_for_prio x13) ++ x8 :: nil)))).
eapply join_get_set_eq_2;eauto.
clear H0 H1 H H4.
subst.
l_rew21_inv1 (get O curtid).
unfolds.
lets Hrec0: Hrec.
splits.
(* ctid_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
eauto.
intros.
unfolds in H.
unfolds in H0.
simpljoin.
do 2 rewrite set_a_get_a' in H0; try intro; tryfalse; eauto.
rewrite H in H0;inverts H0.
rewrite H7 in H4;inverts H4.
eauto.
(* bufs_equiv *)
apply reachable_get_bufsid in Hrec.
destruct Hrec as (x' & y' & Hgetx & Hgety).
unfolds.
split.
(* ibufs_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
(* obufs_equiv *)
unfolds.
rewrite Hoskpt in Hgety;inverts Hgety.
do 2 eexists.



split;eauto.
rewrite set_a_get_a.
split.
eauto.
unfolds in Htpi.
simpljoin.
rewrite H in Htcb;inverts Htcb.
rewrite H6 in H0;inverts H0.
rewrite upd_bufmp_get_neq;eauto.
(* kernel_data_equiv *)
unfolds.
apply reachable_get_knldataid in Hrec.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
l_rew21_inv1 (get O osdomainportid).
splits.
(* kernel_task_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
eauto.
intros.
split.
split;intros; destruct H4;eexists.
unfold task_prio_id.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfold task_prio_id in H4.
rewrite set_a_get_a' in H4 ;try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H4 ;try intro ; tryfalse;eauto.
intros.
assert(t1 = t2).
{
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
l_rew21_inv1 (get x12 t2).
splits;eauto.
(* kernel_mq_equiv  *)
unfold kernel_mq_equiv.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
eauto.

intros.
split.
split;eauto.

intros.
rewrite H4 in H10.
inverts H10.
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
unfolds in Hasrt1.
simpljoin.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
lets Hsemq: mq_ecb H0 H4 H1.
simpljoin.
do 7 eexists.
splits;eauto.
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
eexists x26.
split;eauto.
unfolds in H16.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H16.
apply H17.

intros.
simpljoin.
unfolds in H16.
simpljoin.
rewrite set_a_get_a' in H16; try intro ;tryfalse.
rewrite set_a_get_a' in H16; try intro ;tryfalse.
eexists x26.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H16.
apply H17.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x26.
split;eauto.

unfolds in H16.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H16.
apply H17.

intros.
simpljoin.
unfolds in H16.
simpljoin.
rewrite set_a_get_a' in H16; try intro ;tryfalse.
rewrite set_a_get_a' in H16; try intro ;tryfalse.
eexists x26.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H16.
apply H17.
(* ports_equiv *)
unfolds.
do 4 eexists.

rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
splits;eauto.

intros.
destruct H3.
simpljoin.
casetac x a Hy Hn.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H3.
destruct x.
lets Hf: dom_disj_addrs Hi_neq H H4.
tryfalse.
rewrite set_a_get_a';eauto.
splits;eauto.
split;intros;eauto.
intros.
rewrite H3 in H4;inverts H4.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x7.
split;eauto.

unfolds in H10.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H10.
apply H13.

intros.
simpljoin.
unfolds in H10.
simpljoin.
rewrite set_a_get_a' in H10; try intro ;tryfalse.
rewrite set_a_get_a' in H10; try intro ;tryfalse.
eexists x7.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H10.
apply H13.
simpljoin.

splits;eauto.
split;intros;eauto.
intros.
rewrite H3 in H4;inverts H4.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x0.
split;eauto.

unfolds in H10.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H10.
apply H13.

intros.
simpljoin.
unfolds in H10.
simpljoin.
rewrite set_a_get_a' in H10; try intro ;tryfalse.
rewrite set_a_get_a' in H10; try intro ;tryfalse.
eexists x0.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H10.
apply H13.
(* buffer_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
eauto.

intros.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H4.

splits.
split;intros;eauto.
intros.
rewrite H4 in H13;inverts H13.
lets Hmqed : buffer_ecb H H1.
simpljoin.
rewrite H4 in H13;inverts H13.
split.
(* mq_ed_equiv *)
unfolds.
do 4 eexists; splits; eauto.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x25.
split;eauto.

unfolds in H14.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H14.
apply H15.

intros.
simpljoin.
unfolds in H14.
simpljoin.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
eexists x25.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H14.
apply H15.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x25.
split;eauto.

unfolds in H14.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H14.
apply H15.

intros.
simpljoin.
unfolds in H14.
simpljoin.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
eexists x25.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H14.
apply H15.
(* cap_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
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

unfolds in H10.
simpljoin.

eexists.
unfolds.
do 8 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
eauto.

intros.
simpljoin.
unfolds in H10.
simpljoin.

eexists.
unfolds.
do 8 eexists.
splits;eauto.
rewrite set_a_get_a' in H; try intro ;tryfalse.
rewrite set_a_get_a' in H; try intro ;tryfalse.
rewrite H in H0;inverts H0.
eauto.

intros.
unfolds in H10.
unfolds in H13.
simpljoin.
rewrite set_a_get_a' in H13; try intro ;tryfalse.
rewrite set_a_get_a' in H13; try intro ;tryfalse.
rewrite H10 in H13;inverts H13.
rewrite H16 in H14;inverts H14.
assert(Heqob: objp1 = objp2).
{
  destruct H17.
  destruct H15.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H15.
  simpljoin.
  tryfalse.
  simpljoin.
  inverts H13.
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
  unfolds in H0.
  unfolds in H1.
  simpljoin.
  rewrite set_a_get_a' in H1; try intro ;tryfalse.
  rewrite set_a_get_a' in H1; try intro ;tryfalse.
  rewrite H0 in H1;inverts H1.
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
rewrite Heqt.
eauto.

solve_endabt.

(* n = 5 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 6 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 7 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 8 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.















