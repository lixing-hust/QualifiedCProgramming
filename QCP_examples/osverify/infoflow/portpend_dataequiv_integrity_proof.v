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
Require Import mqsend_cproof.


Lemma qportpend_nabt_spec_step_data_equiv_tskd_preserve:
forall O cd n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
(* good_client_code pc -> *)
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)->
task_prio_id O pr t ->
get O curtid = Some (oscurt t)->
get T t = Some (curs (hapi_code cd),(ke, ks))->
qportpend vl <> ABORT ->
nth_error (get_all_succs (qportpend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O'->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgtc  Hrec Hnflo Htpi Hctid Hgett Hnabt Hnth Hstep.
introv Hi_neq HO_neq.
remember vl as qp_vl.
do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
try destruct v1; simpl in Hnabt; tryfalse.
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
(* qportpend_notnil_body *)
inverts H3 ;simpljoin.
inverts H11.
inverts H.
unfolds in H3;simpljoin.
unfolds in H3;simpljoin.

kvextH Htcb O0 abtcblsid O. 
kvextH Hcid O0 curtid O. 
kvextH Hasdom O0 osdomainportid O. 
kvextH Hobf O0 obufsid O. 
assert (O'=set
(set O osdomainportid
   (osdomainport
      (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11))))
obufsid
(obufs
   (upd_bufmp x13 (dom_for_prio x14)
      (x13 (dom_for_prio x14) ++ x10 :: nil)))).
eapply join_get_set_eq_2;eauto.
clear H H0 H2 H3.
subst.

unfolds.
lets Hrec0: Hrec.
l_rew21_inv1 (get O curtid).
splits.
(* ctid_equiv  *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
eauto.
intros.
unfolds in H0.
unfolds in H.
simpljoin.
rewrite set_a_get_a' in H0; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H0; try intro ; tryfalse;eauto.
rewrite H in H0;inverts H0.
rewrite H6 in H3;inverts H3.
eauto.
(* bufs_equiv *)
apply reachable_get_bufsid in Hrec.
destruct Hrec as (x' & y' & Hgetx & Hgety).
rewrite Hobf in Hgety;inverts Hgety.
unfolds.
split.
(* ibufs_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfolds.
do 2 eexists.
split;eauto.
rewrite set_a_get_a.
split.
eauto.
unfolds in Htpi.
simpljoin.
rewrite H in Htcb;inverts Htcb.
rewrite H4 in H0;inverts H0.
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
split;intros; destruct H3;eexists.
unfold task_prio_id.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfold task_prio_id in H3.
rewrite set_a_get_a' in H3 ;try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H3 ;try intro ; tryfalse;eauto.

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
rewrite H3 in H10.
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
lets Hsemq: mq_ecb H0 H3 H2.
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
eexists x28.
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
eexists x28.
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
eexists x28.
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
eexists x28.
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

casetac x a Hy Hn.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H3.
destruct x.
lets Hf: dom_disj_addrs Hi_neq H H10.
tryfalse.
rewrite set_a_get_a';eauto.
splits;eauto.
split;intros;eauto.
intros.
rewrite H3 in H10;inverts H10.

(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x1.
split;eauto.

unfolds in H11.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H11.
apply H14.

intros.
simpljoin.
unfolds in H11.
simpljoin.
rewrite set_a_get_a' in H11; try intro ;tryfalse.
rewrite set_a_get_a' in H11; try intro ;tryfalse.
eexists x1.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H11.
apply H14.

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
inverts H3.

splits.
split;intros;eauto.
intros.
rewrite H3 in H11;inverts H11.
lets Hmqed : buffer_ecb H H2.
simpljoin.
rewrite H3 in H11;inverts H11.
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
eexists x27.
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
eexists x27.
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
eexists x27.
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
eexists x27.
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
unfolds in H11.
simpljoin.
rewrite set_a_get_a' in H11; try intro ;tryfalse.
rewrite set_a_get_a' in H11; try intro ;tryfalse.
rewrite H10 in H11;inverts H11.
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
  inverts H11.
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
  unfolds in H2.
  simpljoin.
  rewrite set_a_get_a' in H2; try intro ;tryfalse.
  rewrite set_a_get_a' in H2; try intro ;tryfalse.
  rewrite H0 in H2;inverts H2.
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

(* qportpend_block *)
inverts H3 ;simpljoin.
inverts H16.
inverts H.
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 
kvextH Hcid O0 curtid O. 
kvextH Hodom O0 osdomainportid O. 
assert (O'=set
(set O abtcblsid
   (abstcblist
      (set x10 x14
         (x12, wait (os_stat_port x) x17, x15, x16, x18))))
absecblsid (absecblist (set x19 x (absport, x14 :: x20)))).
eapply join_get_set_eq_2;eauto.
clear H0 H2 H3 H4.
subst.

unfolds.
lets Hrec0: Hrec.
l_rew21_inv1 (get O curtid).
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
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a' in H0; try intro; tryfalse; eauto.
rewrite set_a_get_a in H0.
inverts H0.
rewrite set_a_get_a in H3; inverts H3.
rewrite H9 in H4;inverts H4.
eauto.
(* bufs_equiv *)
apply reachable_get_bufsid in Hrec.
destruct Hrec as (x' & y' & Hgetx & Hgety).
unfolds.
split.
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
(* kernel_data_equiv *)
unfolds.
apply reachable_get_knldataid in Hrec.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
l_rew21_inv1 (get O absecblsid).
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
split;intros. 
destruct H2.
unfolds in H2.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
eexists x10.

casetac x10 t Hxy Hxn.
subst.
unfold task_prio_id.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite H9 in H10;inverts H10.
rewrite set_a_get_a;eauto.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

destruct H2.
unfolds in H2.
simpljoin.
rewrite set_a_get_a' in H2; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H2.
inverts H2.
casetac x10 t Hy Hn.
subst.
rewrite set_a_get_a in H10.
inverts H10.

eexists t.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H10;eauto.
eexists x10.
unfolds.
do 5 eexists.
split;eauto.

intros.
assert(t1 = t2).
{
  casetac t t2 He Hne; subst;
  [ rewrite set_a_get_a in H10; inverts H10 |
  rewrite set_a_get_a' in H10; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.

lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H.

casetac t t2 Hy Hn.
subst.
rewrite set_a_get_a in H10; inverts H10.
unfolds in Htpi.
simpljoin.
rewrite Htcb in H;inverts H.
rewrite H2 in H10;inverts H10.
tryfalse.

rewrite set_a_get_a' in H10;eauto.
rewrite H2 in H10;inverts H10.
splits;eauto.
(* kernel_mq_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
eauto.

intros.
split.
split;eauto.

intros.
rewrite H2 in H10.
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
inverts H10.
rewrite set_a_get_a;eauto.
lets Hsemq: mq_ecb H0 H2 Hecb.
simpljoin.
do 7 eexists.
splits;eauto.
casetac x10 t0 Hy Hn.
subst.
rewrite H6 in H10.
inverts H10.
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
eexists x27.
split;eauto.

unfolds in H16.
simpljoin.
rewrite Htcb in H16; inverts H16.

casetac t x27 Hty Htn.
subst.
rewrite H9 in H17; inverts H17.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H16.
simpljoin.

casetac t x27 Hty Htn.
subst.
rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a in H17.
inverts H17.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a' in H17;eauto.
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
eexists x27.
split;eauto.

unfolds in H16.
simpljoin.
rewrite Htcb in H16; inverts H16.

casetac x27 t Hty Htn.
subst.
rewrite H9 in H17; inverts H17.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H16.
simpljoin.

casetac x27 t Hty Htn.
subst.
rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a in H17.
inverts H17.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a' in H17;eauto.
unfolds.
do 5 eexists.
split;eauto.

(* ports_equiv *)
unfolds.
do 4 eexists.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
splits;eauto.
intros.
split;eauto.

split.
split.
intros.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite H6 in H2.
inverts H2.
eexists.
rewrite set_a_get_a;eauto.
eexists.
rewrite set_a_get_a';eauto.

intros.
casetac x a Hy Hn.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H10.
destruct x.
lets Hf: dom_disj_addrs Hi_neq H H14.
tryfalse.
simpljoin.
rewrite set_a_get_a' in H2;eauto.
intros.
casetac x a Hy Hn.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H14.
destruct x.
lets Hf: dom_disj_addrs Hi_neq H H15.
tryfalse.
rewrite set_a_get_a' in H10;eauto.
rewrite H2 in H10;inverts H10.

(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x10.
split;eauto.
unfolds in H14.
simpljoin.
rewrite Htcb in H14;inverts H14.
casetac t x10 Hty Htn.
subst.
rewrite H9 in H15; inverts H15.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x10.
split;eauto.

unfolds in H14.
simpljoin.

casetac t x10 Hty Htn.
subst.
rewrite set_a_get_a' in H14; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H14.
inverts H14.
rewrite set_a_get_a in H15.
inverts H15.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H14; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H14.
inverts H14.
rewrite set_a_get_a' in H15;eauto.
unfolds.
do 5 eexists.
split;eauto.

(* buffer_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.

intros.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H2.
lets Hnew : H.
eapply bufadr_diff_dom in Hnew.
assert (eid <> x10).
intro.
subst.
destruct x10.
eapply dom_disj_addrs;eauto.
rewrite set_a_get_a';eauto.
splits.
split;intros;eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H14 in H15;inverts H15.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H14 in H15;inverts H15.
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
eexists x27.
split;eauto.

unfolds in H16.
simpljoin.
rewrite Htcb in H16; inverts H16.
casetac t x27 Hty Htn.
subst.
rewrite H9 in H17; inverts H17.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H16.
simpljoin.

casetac t x27 Hty Htn.
subst.
rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a in H17.
inverts H17.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a' in H17;eauto.
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
eexists x27.
split;eauto.

unfolds in H16.
simpljoin.
rewrite Htcb in H16; inverts H16.

casetac t x27 Hty Htn.
subst.
rewrite H9 in H17; inverts H17.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H16.
simpljoin.

casetac t x27 Hty Htn.
subst.
rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a in H17.
inverts H17.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a' in H17;eauto.
unfolds.
do 5 eexists.
split;eauto.

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
rewrite H0 in H;inverts H.
eauto.

intros.
unfolds in H10.
unfolds in H14.
simpljoin.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
rewrite H10 in H14;inverts H14.
rewrite H17 in H15;inverts H15.

assert(Heqob: objp1 = objp2).
{
  destruct H18.
  destruct H16.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H16.
  simpljoin.
  tryfalse.
  simpljoin.
  inverts H14.
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
  unfolds in H2.
  simpljoin.
  rewrite Htcb in H0;inverts H0.
  rewrite set_a_get_a' in H2; try intro ;tryfalse.
  rewrite set_a_get_a in H2.
  inverts H2.
  casetac t t2 He Hne; subst;
  [ rewrite set_a_get_a in H3; inverts H3 |
  rewrite set_a_get_a' in H3; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
eauto.

solve_endabt.

(* n = 8 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 9 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* qportpend_block_get_body *)
inverts H2.
simpljoin.
inverts H16.
inverts H.
kvextH Htcb O0 abtcblsid O. 
kvextH Hcid O0 curtid O. 
kvextH Hasdom O0 osdomainportid O. 
kvextH Hobf O0 obufsid O.
assert (O'=set
(set
   (set O abtcblsid
      (abstcblist (set x12 x16 (x14, rdy, Vnull, x17, x18))))
   osdomainportid
   (osdomainport
      (set x1 x
         (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11))))
obufsid
(obufs
   (upd_bufmp x20 (dom_for_prio x18)
      (x20 (dom_for_prio x18) ++ x10 :: nil)))).
eapply join_get_set_eq_3;eauto.
clear H4 H0 H2 H7.
subst.

unfolds.
lets Hrec0: Hrec.
l_rew21_inv1 (get O curtid).
splits.
(* ctid_equiv  *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
rewsimp.
eauto.
intros.
unfolds in H0.
unfolds in H.
simpljoin.
rewrite Htcb in H;inverts H.
rewrite set_a_get_a' in H0; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H0; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H0.
inverts H0.
rewrite set_a_get_a in H4.
inverts H4.
rewrite H6 in H7;inverts H7.
eauto.
(* bufs_equiv *)
apply reachable_get_bufsid in Hrec.
destruct Hrec as (x' & y' & Hgetx & Hgety).
rewrite Hobf in Hgety;inverts Hgety.
unfolds.
split.
(* ibufs_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfolds.
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
rewsimp.
eauto.
intros.
split.
split;intros.
destruct H4.
unfolds in H4.
simpljoin.
rewrite Htcb in H4;inverts H4.

assert(Hneq: t <> x1).
{
  intro.
  subst.
unfolds in Htpi.
simpljoin.
rewrite Htcb in H.
inverts H.
rewrite H10 in H4;inverts H4.
tryfalse.
}
unfold task_prio_id.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a.
eexists x1 , x12.
do 4 eexists.
split;eauto.
rewrite set_a_get_a';eauto.

destruct H4.
unfolds in H4.
simpljoin.
rewrite set_a_get_a' in H4; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H4; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H4.
inverts H4.
assert(Hneq: t <> x1).
{
  intro.
  subst.
unfolds in Htpi.
simpljoin.
rewrite Htcb in H.
inverts H.
rewrite set_a_get_a in H10.
inverts H10.
rewrite H6 in H4;inverts H4.
tryfalse.
}
rewrite set_a_get_a' in H10;eauto.
eexists.
unfolds.
do 5 eexists.
split;eauto.

intros.
assert(t1 = t2).
{
  casetac t t2 He Hne; subst;
  [ rewrite set_a_get_a in H10; inverts H10 |
  rewrite set_a_get_a' in H10; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H.

casetac t t2 Hy Hn.
subst.
rewrite set_a_get_a in H10; inverts H10.
unfolds in Htpi.
simpljoin.
rewrite Htcb in H;inverts H.
rewrite H4 in H10;inverts H10.
tryfalse.

rewrite set_a_get_a' in H10;eauto.
rewrite H4 in H10;inverts H10.
splits;eauto.
(* kernel_mq_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
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
inverts H10.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
lets Hsemq: mq_ecb H0 H4 H2.
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

unfolds in H15.
simpljoin.
rewrite Htcb in H15; inverts H15.

casetac t x26 Hty Htn.
subst.
rewrite H6 in H16; inverts H16.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x26.
split;eauto.

unfolds in H15.
simpljoin.

casetac t x26 Hty Htn.
subst.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H15.
inverts H15.
rewrite set_a_get_a in H16.
inverts H16.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H15.
inverts H15.
rewrite set_a_get_a' in H16;eauto.
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
eexists x26.
split;eauto.

unfolds in H15.
simpljoin.
rewrite Htcb in H15; inverts H15.

casetac t x26 Hty Htn.
subst.
rewrite H6 in H16; inverts H16.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x26.
split;eauto.

unfolds in H15.
simpljoin.

casetac t x26 Hty Htn.
subst.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H15.
inverts H15.
rewrite set_a_get_a in H16.
inverts H16.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H15.
inverts H15.
rewrite set_a_get_a' in H16;eauto.
unfolds.
do 5 eexists.
split;eauto.

(* ports_equiv *)
unfolds.
do 4 eexists.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
splits;eauto.
intros.
casetac x a Hy Hn.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H4.
destruct x.
lets Hf: dom_disj_addrs Hi_neq H H10.
tryfalse.
rewrite set_a_get_a';eauto.
splits;eauto.
split;intros;eauto.
intros.
rewrite H4 in H10;inverts H10.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x1.
split;eauto.

unfolds in H11.
simpljoin.
rewrite Htcb in H11; inverts H11.

casetac t x1 Hty Htn.
subst.
rewrite H6 in H14; inverts H14.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x1.
split;eauto.

unfolds in H11.
simpljoin.

casetac t x1 Hty Htn.
subst.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a in H14.
inverts H14.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a' in H14;eauto.
do 5 eexists.
split;eauto.

(* buffer_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
rewsimp.
eauto.

intros.
splits.
split;intros;eauto.
intros.
rewrite H4 in H10;inverts H10.
lets Hmqed : buffer_ecb H H2.
simpljoin.
rewrite H4 in H10;inverts H10.
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
eexists x26.
split;eauto.

unfolds in H11.
simpljoin.
rewrite Htcb in H11; inverts H11.

casetac t x26 Hty Htn.
subst.
rewrite H6 in H14; inverts H14.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x26.
split;eauto.

unfolds in H11.
simpljoin.

casetac t x26 Hty Htn.
subst.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a in H14.
inverts H14.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a' in H14;eauto.
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
eexists x26.
split;eauto.

unfolds in H11.
simpljoin.
rewrite Htcb in H11; inverts H11.

casetac t x26 Hty Htn.
subst.
rewrite H6 in H14; inverts H14.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x26.
split;eauto.

unfolds in H11.
simpljoin.

casetac t x26 Hty Htn.
subst.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a in H14.
inverts H14.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a' in H11; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a' in H14;eauto.
unfolds.
do 5 eexists.
split;eauto.

(* cap_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
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
rewrite set_a_get_a' in H; try intro ;tryfalse.
rewrite H0 in H;inverts H.
eauto.

intros.
unfolds in H10.
unfolds in H11.
simpljoin.
rewrite set_a_get_a' in H11; try intro ;tryfalse.
rewrite set_a_get_a' in H11; try intro ;tryfalse.
rewrite set_a_get_a' in H11; try intro ;tryfalse.
rewrite H10 in H11;inverts H11.
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
  inverts H11.
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
  unfolds in H2.
  simpljoin.
  rewrite Htcb in H0;inverts H0.
  rewrite set_a_get_a' in H2; try intro ;tryfalse.
  rewrite set_a_get_a' in H2; try intro ;tryfalse.
  rewrite set_a_get_a in H2.
  inverts H2.
  casetac t t2 He Hne; subst;
  [ rewrite set_a_get_a in H4; inverts H4 |
  rewrite set_a_get_a' in H4; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
eauto.

(* qportpend_block_timeout *)
inverts H2.
simpljoin.
inverts H18.
inverts H.
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 
kvextH Hcid O0 curtid O. 
kvextH Hodom O0 osdomainportid O. 
assert (O'=set
(set O abtcblsid
   (abstcblist (set x11 x15 (x13, rdy, Vnull, x17, x18))))
absecblsid
(absecblist (set x19 x (absport, remove_tid x15 x20)))).
eapply join_get_set_eq_2;eauto.
clear H0 H2 H10 H4.
subst.
unfolds.
lets Hrec0: Hrec.
l_rew21_inv1 (get O curtid).
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
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a' in H0; try intro; tryfalse; eauto.
rewrite set_a_get_a in H0.
inverts H0.
rewrite set_a_get_a in H4; inverts H4.
rewrite H9 in H6;inverts H6.
eauto.
(* bufs_equiv *)
apply reachable_get_bufsid in Hrec.
destruct Hrec as (x' & y' & Hgetx & Hgety).
unfolds.
split.
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
(* kernel_data_equiv *)
unfolds.
apply reachable_get_knldataid in Hrec.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
l_rew21_inv1 (get O absecblsid).
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
split;intros. 
destruct H2.
unfolds in H2.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
eexists x11.

casetac x11 t Hxy Hxn.
subst.
unfold task_prio_id.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite H6 in H15;inverts H15.
rewrite set_a_get_a;eauto.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

destruct H2.
unfolds in H2.
simpljoin.
rewrite set_a_get_a' in H2; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H2.
inverts H2.
casetac x11 t Hy Hn.
subst.
rewrite set_a_get_a in H15.
inverts H15.

eexists t.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H15;eauto.
eexists x11.
unfolds.
do 5 eexists.
split;eauto.

intros.
assert(t1 = t2).
{
  casetac t t2 He Hne; subst;
  [ rewrite set_a_get_a in H15; inverts H15 |
  rewrite set_a_get_a' in H15; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.

lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H.

casetac t t2 Hy Hn.
subst.
rewrite set_a_get_a in H15; inverts H15.
unfolds in Htpi.
simpljoin.
rewrite Htcb in H;inverts H.
rewrite H2 in H15;inverts H15.
tryfalse.

rewrite set_a_get_a' in H15;eauto.
rewrite H2 in H15;inverts H15.
splits;eauto.
(* kernel_mq_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
eauto.

intros.
split.
split;eauto.

intros.
rewrite H2 in H15.
inverts H15.
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
inverts H15.
rewrite set_a_get_a;eauto.
lets Hsemq: mq_ecb H0 H2 Hecb.
simpljoin.
do 7 eexists.
splits;eauto.
casetac x11 t0 Hy Hn.
subst.
rewrite H11 in H15.
inverts H15.
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
eexists x27.
split;eauto.

unfolds in H18.
simpljoin.
rewrite Htcb in H18; inverts H18.

casetac t x27 Hty Htn.
subst.
rewrite H6 in H19; inverts H19.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H18.
simpljoin.

casetac t x27 Hty Htn.
subst.
rewrite set_a_get_a' in H18; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a in H19.
inverts H19.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H18; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a' in H19;eauto.
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
eexists x27.
split;eauto.

unfolds in H18.
simpljoin.
rewrite Htcb in H18; inverts H18.

casetac t x27 Hty Htn.
subst.
rewrite H6 in H19; inverts H19.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H18.
simpljoin.

casetac t x27 Hty Htn.
subst.
rewrite set_a_get_a' in H18; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a in H19.
inverts H19.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H18; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a' in H19;eauto.
unfolds.
do 5 eexists.
split;eauto.

(* ports_equiv *)
unfolds.
do 4 eexists.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
splits;eauto.
intros.
split;eauto.

split.
split.
intros.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite H11 in H2.
inverts H2.
eexists.
rewrite set_a_get_a;eauto.
eexists.
rewrite set_a_get_a';eauto.

intros.
casetac x a Hy Hn.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H15.
destruct x.
lets Hf: dom_disj_addrs Hi_neq H H16.
tryfalse.
simpljoin.
rewrite set_a_get_a' in H2;eauto.
intros.
casetac x a Hy Hn.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H16.
destruct x.
lets Hf: dom_disj_addrs Hi_neq H H17.
tryfalse.
rewrite set_a_get_a' in H15;eauto.
rewrite H2 in H15;inverts H15.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x11.
split;eauto.

unfolds in H16.
simpljoin.
rewrite Htcb in H16; inverts H16.

casetac t x11 Hty Htn.
subst.
rewrite H6 in H17; inverts H17.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x11.
split;eauto.

unfolds in H16.
simpljoin.

casetac t x11 Hty Htn.
subst.
rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a in H17.
inverts H17.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H16; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H16.
inverts H16.
rewrite set_a_get_a' in H17;eauto.
unfolds.
do 5 eexists.
split;eauto.

(* buffer_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.

intros.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
simpljoin.
inverts H2.
lets Hnew : H.
eapply bufadr_diff_dom in Hnew.
assert (eid <> x11).
intro.
subst.
destruct x11.
eapply dom_disj_addrs;eauto.
rewrite set_a_get_a';eauto.
splits.
split;intros;eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H16 in H17;inverts H17.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H16 in H17;inverts H17.
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
eexists x27.
split;eauto.

unfolds in H18.
simpljoin.
rewrite Htcb in H18; inverts H18.

casetac t x27 Hty Htn.
subst.
rewrite H6 in H19; inverts H19.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H18.
simpljoin.

casetac t x27 Hty Htn.
subst.
rewrite set_a_get_a' in H18; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a in H19.
inverts H19.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H18; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a' in H19;eauto.
unfolds.
do 5 eexists.
split;eauto.
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H18.
simpljoin.
rewrite Htcb in H18; inverts H18.

casetac t x27 Hty Htn.
subst.
rewrite H6 in H19; inverts H19.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
eexists x27.
split;eauto.

unfolds in H18.
simpljoin.

casetac t x27 Hty Htn.
subst.
rewrite set_a_get_a' in H18; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a in H19.
inverts H19.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H18; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a' in H19;eauto.
unfolds.
do 5 eexists.
split;eauto.

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

unfolds in H15.
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
unfolds in H15.
simpljoin.

eexists.
unfolds.
do 8 eexists.
splits;eauto.
rewrite set_a_get_a' in H; try intro ;tryfalse.
rewrite set_a_get_a' in H; try intro ;tryfalse.
rewrite H0 in H;inverts H.
eauto.

intros.
unfolds in H15.
unfolds in H16.
simpljoin.
rewrite set_a_get_a' in H16; try intro ;tryfalse.
rewrite set_a_get_a' in H16; try intro ;tryfalse.
rewrite H15 in H16;inverts H16.
rewrite H17 in H19;inverts H19.

assert(Heqob: objp1 = objp2).
{
  destruct H18.
  destruct H20.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H20.
  simpljoin.
  tryfalse.
  simpljoin.
  inverts H.
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
  unfolds in H2.
  simpljoin.
  rewrite Htcb in H0;inverts H0.
  rewrite set_a_get_a' in H2; try intro ;tryfalse.
  rewrite set_a_get_a in H2.
  inverts H2.
  casetac t t2 He Hne; subst;
  [ rewrite set_a_get_a in H4; inverts H4 |
  rewrite set_a_get_a' in H4; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
eauto.
(* n = 10 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.
