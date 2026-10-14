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




Lemma bufferpost_nabt_spec_step_data_equiv_tskd_preserve:
forall O cd n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
good_client_code pc ->
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)->
task_prio_id O pr t ->
get O curtid = Some (oscurt t)->
get T t = Some (curs (hapi_code cd),(ke, ks))->
bufferpost vl <> ABORT ->
nth_error (get_all_succs (bufferpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O'->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgtc Hgcc Hrec Hnflo Htpi Hctid Hgett Hnabt Hnth Hstep.
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
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
destruct n; [ my_succs_solver_same_absdata | idtac].
(* qpost_nowt_succ_body *)
inverts H3; simpljoin.
destruct H12 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
kvextH Hecb O0 absecblsid O.
assert (O'=set O absecblsid
(absecblist
   (set x7 x (absmsgq (x9 ++ x0 :: nil) x8 x10, nil)))).
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
split;intros;destruct H19;eexists.
unfold task_prio_id.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfold task_prio_id in H19.
rewrite set_a_get_a' in H19;eauto.
intro ; tryfalse.

intros.
assert(t1 = t2).
{
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
l_rew21_inv1 (get x1 t2).
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
rewrite H19 in H20.
inverts H20.
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
inverts H20.
inverts H.

assert (Hneqx2: x <> t0).
{
    lets Hnewa : not_both_mq_and_buffer H1 H19 .
    intro.
    subst.
    eapply Hnewa in H21.
    tryfalse.
}
lets Hsemq: mq_ecb H1 H19 Hecb.
destruct Hsemq.
do 3 destruct H.
rewrite set_a_get_a.
eexists x11,(set x11 x (absmsgq (x9 ++ x0 :: nil) x8 x10, nil)),t0.
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
eexists x17.
split;eauto.

unfolds in H22.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H22.
apply H23.

intros.
simpljoin.
unfolds in H22.
simpljoin.
rewrite set_a_get_a' in H22; try intro ;tryfalse.
eexists x17.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H22.
apply H23.

(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x17.
split;eauto.

unfolds in H22.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H22.
apply H23.

intros.
simpljoin.
unfolds in H22.
simpljoin.
rewrite set_a_get_a' in H22; try intro ;tryfalse.
eexists x17.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H22.
apply H23.

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
rewrite H4 in H19.
inverts H19.
eexists x2.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite set_a_get_a in H19.
inverts H19.
eexists x2.
rewrite set_a_get_a' in H19;eauto.

intros.
(* tls1 = tls2 *)
casetac x a Hy Hn.
subst.
rewrite H4 in H19.
inverts H19.
rewrite set_a_get_a' in H20;eauto.
rewrite H19 in H20; inverts H20.

(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x2.
split;eauto.

unfolds in H21.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H21.
apply H22.

intros.
simpljoin.
unfolds in H21.
simpljoin.
rewrite set_a_get_a' in H21; try intro ;tryfalse.
eexists x2.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H21.
apply H22.

(* buffer_equiv *)
inverts H.
rewrite H15 in H4;inverts H4.
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
rewrite set_a_get_a' in H19;eauto.
rewrite H4 in H19;inverts H19.
split.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H19 in H4;inverts H19.
inverts H4.
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
eexists x5.
split;eauto.

unfolds in H19.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H19.
apply H20.

intros.
simpljoin.
unfolds in H19.
simpljoin.
rewrite set_a_get_a' in H19; try intro ;tryfalse.
eexists x5.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H19.
apply H20.

(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x2.
split;eauto.

unfolds in H20.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H20.
apply H21.

intros.
simpljoin.
unfolds in H20.
simpljoin.
rewrite set_a_get_a' in H20; try intro ;tryfalse.
eexists x2.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H20.
apply H21.

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

unfolds in H20.
simpljoin.

eexists.
unfolds.
do 8 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
eauto.

intros.
simpljoin.
unfolds in H20.
simpljoin.

eexists.
unfolds.
do 8 eexists.
splits;eauto.
rewrite set_a_get_a' in H2; try intro ;tryfalse.
rewrite H1 in H2;inverts H2.
eauto.

intros.
unfolds in H20.
unfolds in H21.
simpljoin.
rewrite set_a_get_a' in H21; try intro ;tryfalse.
rewrite H20 in H21;inverts H21.
rewrite H22 in H24;inverts H24.

assert(Heqob: objp1 = objp2).
{
  destruct H25.
  destruct H23.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H23.
  simpljoin.
  tryfalse.
  simpljoin.
  inverts H21.
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

(* qpost_nowt_succ_body *)
solve_endabt.

(* qpost_exwt_succ_body *)
inverts H3; simpljoin.
destruct H20 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
inverts H.
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 
assert (O'=set
(set O abtcblsid
   (abstcblist (set x9 x8 (x13, rdy, x0, x12, x17)))) absecblsid
(absecblist (set x4 x (absmsgq nil x15 x16, remove_tid x8 x6)))).
eapply join_get_set_eq_2;eauto.
clear H3 H4.
subst.
unfolds.
lets Hrec0: Hrec.

l_rew21_inv1 (get O absecblsid).
rewrite H6 in H23;inverts H23.
splits.
(* ctid_equiv  *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
rewsimp.
eauto.
intros.

unfolds in H.
unfolds in H1.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a' in H1; try intro; tryfalse; eauto.
rewrite set_a_get_a in H1.
inverts H1.

casetac x8 t He Hne.
subst.
rewrite set_a_get_a in H3; inverts H3.
rewrite H14 in H4;inverts H4.
eauto.

rewrite set_a_get_a' in H3;eauto.
rewrite H4 in H3;inverts H3.
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
eexists x3.
casetac x3 x8 Hxy Hxn.
subst.
unfold task_prio_id.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite H14 in H17;inverts H17.
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
casetac x3 x8 Hy Hn.
subst.
rewrite set_a_get_a in H17.
inverts H17.

eexists x8.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H17;eauto.
eexists x3.
unfolds.
do 5 eexists.
split;eauto.
intros.
assert(t1 = t2).
{
  casetac x8 t2 He Hne; subst;
  [ rewrite set_a_get_a in H17; inverts H17 |
  rewrite set_a_get_a' in H17; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
unfolds in H8.

lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
destruct Hasrt1.
tryfalse.
simpljoin.
inverts H.
rewrite H22 in H14;inverts H14.

lets Hbufa: buffer_part_consistent Hecb H20 H6.
specializes Hbufa.
left.
eauto.
simpljoin.
assert(x8 <> t2).
{
  unfolds in H.
  simpljoin.
  rewrite Htcb in H;inverts H.
  intro.
  subst.
  rewrite set_a_get_a in H17.
  inverts H17.
  rewrite <-H14 in Hi_neq.
  rewrite H2 in H26;inverts H26.
  tryfalse.
}
rewrite set_a_get_a' in H17;eauto.
rewrite H2 in H17;inverts H17.
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
rewrite H17 in H2.
inverts H2.
unfolds.
destruct mq1.
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
inverts H2.
assert (Hneqx2: x3 <> t0).
{
    lets Hnewa : not_both_mq_and_buffer H1 H17 .
    intro.
    subst.
    eapply Hnewa in H20.
    tryfalse.
}
lets Hsemq: mq_ecb H1 H17 Hecb.
destruct Hsemq.
do 3 destruct H2.
rewrite set_a_get_a.
eexists x4,(set x4 x3 (absmsgq nil x19 x20, remove_tid x8 x21)),t0.
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
eexists x16.
split;eauto.

unfolds in H23.
simpljoin.
rewrite Htcb in H23; inverts H23.

casetac x8 x16 Hty Htn.
subst.
rewrite H26 in H14; inverts H14.

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
eexists x16.
split;eauto.

unfolds in H23.
simpljoin.

casetac x8 x16 Hty Htn.
subst.
rewrite set_a_get_a' in H23; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H23.
inverts H23.
rewrite set_a_get_a in H26.
inverts H26.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H23; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H23.
inverts H23.
rewrite set_a_get_a' in H26;eauto.
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
eexists x16.
split;eauto.

unfolds in H23.
simpljoin.
rewrite Htcb in H23; inverts H23.

casetac x8 x16 Hty Htn.
subst.
rewrite H26 in H14; inverts H14.

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
eexists x16.
split;eauto.

unfolds in H23.
simpljoin.

casetac x8 x16 Hty Htn.
subst.
rewrite set_a_get_a' in H23; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H23.
inverts H23.
rewrite set_a_get_a in H26.
inverts H26.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H23; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H23.
inverts H23.
rewrite set_a_get_a' in H26;eauto.
unfolds.
do 5 eexists.
split;eauto.

(* ports_equiv *)
unfolds.
do 4 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
rewrite set_a_get_a'; try intro ;tryfalse.
eauto.
rewrite set_a_get_a;eauto.

intros.
split;eauto.

split.
split;intros.
simpljoin.

casetac x a Hay Han.
subst.
rewrite H6 in H2;inverts H2.

eexists x3.
rewrite set_a_get_a';eauto.

simpljoin.
casetac x a Hay Han.
subst.
rewrite set_a_get_a in H2;eauto.
inverts H2.
rewrite set_a_get_a' in H2;eauto.

intros.
casetac x a Hay Han.
subst.
rewrite set_a_get_a in H17;eauto.
inverts H17.
rewrite set_a_get_a' in H17;eauto.
rewrite H2 in H17;inverts H17.

(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x3.
split;eauto.

unfolds in H20.
simpljoin.
rewrite Htcb in H20; inverts H20.

casetac x8 x3 Hty Htn.
subst.
rewrite H22 in H14; inverts H14.

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
eexists x3.
split;eauto.

unfolds in H20.
simpljoin.

casetac x8 x3 Hty Htn.
subst.
rewrite set_a_get_a' in H20; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H20.
inverts H20.
rewrite set_a_get_a in H22.
inverts H22.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H20; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H20.
inverts H20.
rewrite set_a_get_a' in H22;eauto.
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
assert(Hix: eid = x  \/  eid <> x) by tauto.
destruct Hix.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
destruct Hasrt1.
tryfalse.
simpljoin.
inverts H2.
lets Hfb: bufidx_diff_dom Hi_neq H H17.
tryfalse.

splits.
split.
intros.
simpljoin.
do 2 eexists.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
rewrite set_a_get_a' in H17;eauto.

intros.
rewrite set_a_get_a' in H20;eauto.
rewrite H17 in H20;inverts H20.
split.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H17 in H20;inverts H20.

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
eexists x16.
split;eauto.

unfolds in H22.
simpljoin.
rewrite Htcb in H22; inverts H22.

casetac x8 x16 Hty Htn.
subst.
rewrite H23 in H14; inverts H14.

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
eexists x16.
split;eauto.

unfolds in H22.
simpljoin.

casetac x8 x16 Hty Htn.
subst.
rewrite set_a_get_a' in H22; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H22.
inverts H22.
rewrite set_a_get_a in H23.
inverts H23.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a' in H22; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H22.
inverts H22.
rewrite set_a_get_a' in H23;eauto.
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
eexists x3.
split;eauto.

unfolds in H22.
simpljoin.
rewrite Htcb in H22; inverts H22.

casetac x8 x3 Hty Htn.
subst.
rewrite H23 in H14; inverts H14.

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
eexists x3.
split;eauto.

unfolds in H22.
simpljoin.
casetac x8 x3 Hty Htn.
subst.
rewrite set_a_get_a' in H22; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H22.
inverts H22.
rewrite set_a_get_a in H23.
inverts H23.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a' in H22; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H22.
inverts H22.
rewrite set_a_get_a' in H23;eauto.
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

unfolds in H17.
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
unfolds in H17.
simpljoin.

eexists.
unfolds.
do 8 eexists.
splits;eauto.
rewrite set_a_get_a' in H; try intro ;tryfalse.
rewrite set_a_get_a' in H; try intro ;tryfalse.
rewrite H1 in H;inverts H.
eauto.

intros.
unfolds in H17.
unfolds in H20.
simpljoin.
rewrite set_a_get_a' in H20; try intro ;tryfalse.
rewrite set_a_get_a' in H20; try intro ;tryfalse.
rewrite H17 in H20;inverts H20.
rewrite H26 in H22;inverts H22.

assert(Heqob: objp1 = objp2).
{
  destruct H27.
  destruct H23.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H23.
  simpljoin.
  tryfalse.
  simpljoin.
  inverts H20.
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
  unfolds in H2.
  unfolds in H1.
  simpljoin.
  rewrite Htcb in H1;inverts H1.
  rewrite set_a_get_a' in H2; try intro ;tryfalse.
  rewrite set_a_get_a in H2.
  inverts H2.
  casetac x8 t2 He Hne; subst;
  [ rewrite set_a_get_a in H3; inverts H3 |
  rewrite set_a_get_a' in H3; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
eauto.

(* qpost_exwt_succ_body *)
solve_endabt.

destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.

