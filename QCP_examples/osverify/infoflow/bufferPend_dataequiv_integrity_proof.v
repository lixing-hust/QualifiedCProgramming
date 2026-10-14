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


Lemma bufferpend_nabt_spec_step_data_equiv_tskd_preserve:
forall O cd n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
good_client_code pc ->
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)->
task_prio_id O pr t ->
get O curtid = Some (oscurt t)->
get T t = Some (curs (hapi_code cd),(ke, ks))->
bufferpend vl <> ABORT ->
nth_error (get_all_succs (bufferpend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O'->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgtc Hgcc Hrec Hnflo Htpi Hctid Hgett Hnabt Hnth Hstep.
introv Hi_neq HO_neq.
remember vl as qp_vl.
do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
try destruct v0; simpl in Hnabt; tryfalse.

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

(* qpend_get_no_pwl_succ_body *)
inverts H3; simpljoin.
destruct H15 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

kvextH Hcur O0 curtid O. 
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 

assert (O'=set O absecblsid
(absecblist (set x8 x (absmsgq x11 x12 nil, x13)))).
eapply join_get_set_eq;eauto.

clear H1 H2 H3.
subst.
unfolds.
lets Hrec0: Hrec.
l_rew21_inv1 (get O curtid).
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
l_rew21_inv1 (get O abtcblsid).
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
split;intros;destruct H2;eexists.
unfold task_prio_id.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
unfold task_prio_id in H2.
rewrite set_a_get_a' in H2;eauto.
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
rewrite H2 in H14.
inverts H14.
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
    lets Hnewa : not_both_mq_and_buffer H1 H2.
    intro.
    subst.
    eapply Hnewa in H15.
    tryfalse.
}
lets Hsemq: mq_ecb H1 H2 Hecb.
destruct Hsemq.
do 3 destruct H.
rewrite set_a_get_a.
eexists x8,(set x8 x (absmsgq x11 x12 nil, x13)),t0.
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
eexists x18.
split;eauto.

unfolds in H16.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H16.
apply H20.

intros.
simpljoin.
unfolds in H16.
simpljoin.
rewrite set_a_get_a' in H16; try intro ;tryfalse.
eexists x18.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H16.
apply H20.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x18.
split;eauto.

unfolds in H16.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H16.
apply H20.

intros.
simpljoin.
unfolds in H16.
simpljoin.
rewrite set_a_get_a' in H16; try intro ;tryfalse.
eexists x18.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H16.
apply H20.
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
rewrite H4 in H2.
inverts H2.
eexists x2.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite set_a_get_a in H2.
inverts H2.
eexists x2.
rewrite set_a_get_a' in H2;eauto.

intros.
(* tls1 = tls2 *)
casetac x a Hy Hn.
subst.
rewrite H4 in H2.
inverts H2.
rewrite set_a_get_a' in H14;eauto.
rewrite H2 in H14; inverts H14.

(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x2.
split;eauto.

unfolds in H15.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H15.
apply H16.

intros.
simpljoin.
unfolds in H15.
simpljoin.
rewrite set_a_get_a' in H15; try intro ;tryfalse.
eexists x2.
split;eauto.
unfolds.
do 5 eexists.
split.
apply H15.
apply H16.
(* buffer_equiv *)
inverts H.
rewrite H19 in H4;inverts H4.
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
inverts H0.
lets Hfb: bufidx_diff_dom Hi_neq H H2.
tryfalse.

splits.
split.
intros.
simpljoin.
do 2 eexists.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
rewrite set_a_get_a' in H2;eauto.

intros.
rewrite set_a_get_a' in H4;eauto.
rewrite H4 in H2;inverts H2.
split.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H2 in H4;inverts H4.
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
apply H15.

intros.
simpljoin.
unfolds in H14.
simpljoin.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
eexists x4.
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
eexists x1.
split;eauto.

unfolds in H14.
simpljoin.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ;tryfalse.
apply H14.
apply H15.

intros.
simpljoin.
unfolds in H14.
simpljoin.
rewrite set_a_get_a' in H14; try intro ;tryfalse.
eexists x1.
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
rewrite set_a_get_a' in H0; try intro ;tryfalse.
rewrite H1 in H0;inverts H0.
eauto.

intros.
unfolds in H14.
unfolds in H15.
simpljoin.
rewrite set_a_get_a' in H15; try intro ;tryfalse.
rewrite H14 in H15;inverts H15.
rewrite H21 in H16;inverts H16.

assert(Heqob: objp1 = objp2).
{
  destruct H22.
  destruct H20.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H20.
  simpljoin.
  tryfalse.
  simpljoin.
  inverts H15.
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

(* qpend_get_no_pwl_succ_body *)
solve_endabt.

(* qpend_get_ex_pwl_before_sched_body *)
inverts H3.
simpljoin.
destruct H21 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

lets Hnew6: H6.
unfolds in H6.
simpljoin.
rewrite H4 in H8; inverts H8.
inverts H.
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 

assert (O'=set
(set O abtcblsid
   (abstcblist (set x9 x19 (x15, rdy, x18, x20, x22))))
absecblsid
(absecblist
   (set x8 x
      (absmsgq (x11 ++ x18 :: nil) x12 (remove_tid x19 x13),
      x14)))).
eapply join_get_set_eq_2;eauto.

clear H1 H2.
subst.
unfolds.
lets Hrec0: Hrec.
l_rew21_inv1 (get O absecblsid).
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
unfolds in H1.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a' in H1; try intro; tryfalse; eauto.
rewrite set_a_get_a in H1.
inverts H1.

casetac x19 t He Hne.
subst.
rewrite set_a_get_a in H8; inverts H8.
rewrite H4 in H15;inverts H15.
eauto.

rewrite set_a_get_a' in H8;eauto.
rewrite H15 in H8;inverts H8.
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
eexists x2.
casetac x2 x19 Hxy Hxn.
subst.
unfold task_prio_id.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite H4 in H18;inverts H18.
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
casetac x2 x19 Hy Hn.
subst.
rewrite set_a_get_a in H18.
inverts H18.

eexists x19.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H18;eauto.
eexists x2.
unfolds.
do 5 eexists.
split;eauto.
intros.
assert(t1 = t2).
{
  casetac x19 t2 He Hne; subst;
  [ rewrite set_a_get_a in H18; inverts H18 |
  rewrite set_a_get_a' in H18; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.

lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
unfolds in Hasrt1.
destruct Hasrt1.
tryfalse.
simpljoin.
inverts H.
rewrite H23 in H3;inverts H3.

lets Hbufa: buffer_part_consistent Hecb H21 H23.
specializes Hbufa.
right.
eauto.
simpljoin.
assert(x19 <> t2).
{
  unfolds in H.
  simpljoin.
  rewrite Htcb in H;inverts H.
  intro.
  subst.
  rewrite set_a_get_a in H18.
  inverts H18.
  rewrite <-H3 in Hi_neq.
  rewrite H2 in H22;inverts H22.
  tryfalse.
}
rewrite set_a_get_a' in H18;eauto.
rewrite H2 in H18;inverts H18.
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
rewrite H18 in H2.
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
assert (Hneqx2: x2 <> t0).
{
    lets Hnewa : not_both_mq_and_buffer H1 H18 .
    intro.
    subst.
    eapply Hnewa in H21.
    tryfalse.
}
lets Hsemq: mq_ecb H1 H18 Hecb.
destruct Hsemq.
do 3 destruct H2.
rewrite set_a_get_a.
eexists x8,(set x8 x2
(absmsgq (x11 ++ x18 :: nil) x12 (remove_tid x19 x13), x14)),t0.
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
eexists x26.
split;eauto.

unfolds in H26.
simpljoin.
rewrite Htcb in H26; inverts H26.

casetac x19 x26 Hty Htn.
subst.
rewrite H4 in H27; inverts H27.

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
eexists x26.
split;eauto.

unfolds in H26.
simpljoin.

casetac x19 x26 Hty Htn.
subst.
rewrite set_a_get_a' in H26; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H26.
inverts H26.
rewrite set_a_get_a in H27.
inverts H27.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H26; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H26.
inverts H26.
rewrite set_a_get_a' in H27;eauto.
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

unfolds in H26.
simpljoin.
rewrite Htcb in H26; inverts H26.

casetac x19 x26 Hty Htn.
subst.
rewrite H4 in H27; inverts H27.
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
eexists x26.
split;eauto.
unfolds in H26.
simpljoin.
casetac x19 x26 Hty Htn.
subst.
rewrite set_a_get_a' in H26; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H26.
inverts H26.
rewrite set_a_get_a in H27.
inverts H27.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a' in H26; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H26.
inverts H26.
rewrite set_a_get_a' in H27;eauto.
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
rewrite H3 in H2;inverts H2.

eexists x2.
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
rewrite set_a_get_a in H18;eauto.
inverts H18.
rewrite set_a_get_a' in H18;eauto.
rewrite H2 in H18;inverts H18.
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
rewrite Htcb in H21; inverts H21.

casetac x19 x2 Hty Htn.
subst.
rewrite H4 in H22; inverts H22.
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
eexists x2.
split;eauto.
unfolds in H21.
simpljoin.
casetac x19 x2 Hty Htn.
subst.
rewrite set_a_get_a' in H21; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H21.
inverts H21.
rewrite set_a_get_a in H22.
inverts H22.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a' in H21; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H21.
inverts H21.
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
lets Hfb: bufidx_diff_dom Hi_neq H H18.
tryfalse.

splits.
split.
intros.
simpljoin.
do 2 eexists.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
rewrite set_a_get_a' in H18;eauto.

intros.
rewrite set_a_get_a' in H21;eauto.
rewrite H18 in H21;inverts H21.
split.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H18 in H21;inverts H21.
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

unfolds in H22.
simpljoin.
rewrite Htcb in H22; inverts H22.

casetac x19 x26 Hty Htn.
subst.
rewrite H26 in H4; inverts H4.

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
eexists x26.
split;eauto.

unfolds in H22.
simpljoin.

casetac x19 x26 Hty Htn.
subst.
rewrite set_a_get_a' in H22; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H22.
inverts H22.
rewrite set_a_get_a in H26.
inverts H26.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a' in H22; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H22.
inverts H22.
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
eexists x2.
split;eauto.

unfolds in H22.
simpljoin.
rewrite Htcb in H22; inverts H22.

casetac x19 x2 Hty Htn.
subst.
rewrite H26 in H4; inverts H4.

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
eexists x2.
split;eauto.

unfolds in H22.
simpljoin.
casetac x19 x2 Hty Htn.
subst.
rewrite set_a_get_a' in H22; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H22.
inverts H22.
rewrite set_a_get_a in H26.
inverts H26.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a' in H22; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H22.
inverts H22.
rewrite set_a_get_a' in H26;eauto.
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

unfolds in H18.
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
unfolds in H18.
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
unfolds in H18.
unfolds in H21.
simpljoin.
rewrite set_a_get_a' in H21; try intro ;tryfalse.
rewrite set_a_get_a' in H21; try intro ;tryfalse.
rewrite H18 in H21;inverts H21.
rewrite H27 in H22;inverts H22.

assert(Heqob: objp1 = objp2).
{
  destruct H28.
  destruct H26.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H26.
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
  unfolds in H2.
  unfolds in H1.
  simpljoin.
  rewrite Htcb in H1;inverts H1.
  rewrite set_a_get_a' in H2; try intro ;tryfalse.
  rewrite set_a_get_a in H2.
  inverts H2.
  casetac x19 t2 He Hne; subst;
  [ rewrite set_a_get_a in H8; inverts H8 |
  rewrite set_a_get_a' in H8; eauto ];
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
eauto.

(* qpend_get_ex_pwl_before_sched_body *)
solve_endabt.

(* qpend_block_body *)
inverts H3.
simpljoin.
inverts H19.
inverts H.

kvextH Hcur O0 curtid O. 
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O.
assert (O'=set
(set O abtcblsid
   (abstcblist
      (set x8 x16 (x13, wait (os_stat_q x) x17, x1, x2, x19))))
absecblsid
(absecblist (set x10 x (absmsgq nil x15 x18, x16 :: x12)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H6.
subst.
unfolds.
lets Hrec0: Hrec.

l_rew21_inv1 (get O curtid).
l_rew21_inv1 (get O absecblsid).
rewrite H3 in H25;inverts H25.
splits.
(* ctid_equiv *)
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
rewrite set_a_get_a' in H0; try intro; tryfalse; eauto.
rewrite set_a_get_a in H0.
inverts H0.
rewrite set_a_get_a in H2.
inverts H2.
rewrite Htcb in H;inverts H.
rewrite H8 in H4;inverts H4.
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
(* obufs_equiv *)
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
destruct H1.
unfolds in H1.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
eexists x4.
casetac x4 t Hxy Hxn.
subst.
unfold task_prio_id.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite H8 in H18;inverts H18.
rewrite set_a_get_a;eauto.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

destruct H1.
unfolds in H1.
simpljoin.
rewrite set_a_get_a' in H1; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H1.
inverts H1.
casetac x4 t Hy Hn.
subst.
rewrite set_a_get_a in H18.
inverts H18.

eexists t.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H18;eauto.
eexists x4.
unfolds.
do 5 eexists.
split;eauto.

casetac pr pr0 Hy Hn.
subst.
tryfalse.
lets Hnewt: Htpi.
unfolds in Hnewt.
simpljoin.
rewrite Htcb in H1;inverts H1.
rewrite H8 in H18;inverts H18.
intros.

assert(Hneq: t <> t2).
{
  eapply task_prio_id_tidneq.
  unfolds;do 5 eexists;split;eauto.
  casetac t t2 Hty Htn.
  subst.
  rewrite set_a_get_a in H1.
  inverts H1.
  tryfalse.
  rewrite set_a_get_a' in H1;eauto.
  unfolds;do 5 eexists;split;eauto.
  eauto.
}
rewrite set_a_get_a' in H1;eauto.
assert(Heqt: t1 = t2).
{
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
rewrite H in H1;inverts H1.
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
rewrite H18 in H1.
inverts H1.
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
inverts H1.
assert (Hneqx2: x4 <> t0).
{
    lets Hnewa : not_both_mq_and_buffer H0 H18 .
    intro.
    subst.
    eapply Hnewa in H19.
    tryfalse.
}
lets Hsemq: mq_ecb H0 H18 Hecb.
destruct Hsemq.
do 3 destruct H1.
rewrite set_a_get_a.
eexists x10,(set x10 x4 (absmsgq nil x6 x7, t :: x5)),t0.
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
eexists x20.
split;eauto.

unfolds in H23.
simpljoin.
rewrite Htcb in H23; inverts H23.

casetac t x20 Hty Htn.
subst.
rewrite H8 in H24; inverts H24.

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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.

intros.
simpljoin.
eexists x20.
split;eauto.

unfolds in H23.
simpljoin.
casetac t x20 Hty Htn.
subst.
rewrite set_a_get_a' in H23; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H23.
inverts H23.
rewrite set_a_get_a in H24.
inverts H24.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H23; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H23.
inverts H23.
rewrite set_a_get_a' in H24;eauto.
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
eexists x20.
split;eauto.

unfolds in H23.
simpljoin.
rewrite Htcb in H23; inverts H23.

casetac t x20 Hty Htn.
subst.
rewrite H8 in H24; inverts H24.

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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x20.
split;eauto.

unfolds in H23.
simpljoin.
casetac t x20 Hty Htn.
subst.
rewrite set_a_get_a' in H23; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H23.
inverts H23.
rewrite set_a_get_a in H24.
inverts H24.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H23; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H23.
inverts H23.
rewrite set_a_get_a' in H24;eauto.
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
casetac x a Hau Han.
subst.
rewrite H3 in H1.
inverts H1.
eexists x4.
rewrite set_a_get_a'; eauto.

simpljoin.
casetac x a Hau Han.
subst.
rewrite set_a_get_a in H1.
inverts H1.
rewrite set_a_get_a' in H1; eauto.

intros.
casetac x a Hau Han.
subst.
rewrite set_a_get_a in H18.
inverts H18.
rewrite set_a_get_a' in H18; eauto.
rewrite H1 in H18;inverts H18.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x4.
split;eauto.

unfolds in H19.
simpljoin.
rewrite Htcb in H19; inverts H19.

casetac t x4 Hty Htn.
subst.
rewrite H8 in H22; inverts H22.
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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x4.
split;eauto.
unfolds in H19.
simpljoin.
casetac t x4 Hty Htn.
subst.
rewrite set_a_get_a' in H19; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H19.
inverts H19.
rewrite set_a_get_a in H22.
inverts H22.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H19; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H19.
inverts H19.
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
inverts H1.
lets Hfb: bufidx_diff_dom Hi_neq H H18.
tryfalse.

splits.
split.
intros.
simpljoin.
do 2 eexists.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
rewrite set_a_get_a' in H18;eauto.
intros.
rewrite set_a_get_a' in H19;eauto.
rewrite H18 in H19;inverts H19.
split.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H18 in H19;inverts H19.
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
eexists x20.
split;eauto.
unfolds in H22.
simpljoin.
rewrite Htcb in H22; inverts H22.

casetac t x20 Hty Htn.
subst.
rewrite H8 in H23; inverts H23.
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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x20.
split;eauto.
unfolds in H22.
simpljoin.
casetac t x20 Hty Htn.
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
eexists x4.
split;eauto.
unfolds in H22.
simpljoin.
rewrite Htcb in H22; inverts H22.

casetac t x4 Hty Htn.
subst.
rewrite H8 in H23; inverts H23.
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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x4.
split;eauto.
unfolds in H22.
simpljoin.
casetac t x4 Hty Htn.
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
unfolds in H18.
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
unfolds in H18.
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
unfolds in H19.
unfolds in H18.
simpljoin.
rewrite set_a_get_a' in H19; try intro ;tryfalse.
rewrite set_a_get_a' in H19; try intro ;tryfalse.
rewrite H18 in H19;inverts H19.
rewrite H24 in H22;inverts H22.
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
  inverts H19.
  eauto.
}
subst.
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
casetac pr pr0 Hy Hn.
subst.
tryfalse.
unfolds in H1.
simpljoin.

lets Hnewt: Htpi.
unfolds in Hnewt.
simpljoin.
rewrite set_a_get_a' in H1; try intro ;tryfalse.
rewrite set_a_get_a in H1.
inverts H1.
rewrite Htcb in H;inverts H.
rewrite H8 in H4;inverts H4.

assert(Hneq: t <> t2).
{
  eapply task_prio_id_tidneq.
  unfolds;do 5 eexists;split;eauto.
  casetac t t2 Hty Htn.
  subst.
  rewrite set_a_get_a in H2.
  inverts H2.
  tryfalse.
  rewrite set_a_get_a' in H2;eauto.
  unfolds;do 5 eexists;split;eauto.
  eauto.
}
rewrite set_a_get_a' in H2;eauto.
assert(Heqt: t1 = t2).
{
  unfolds in H0.
  simpljoin.
  rewrite Htcb in H.
  inverts H.
    eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
eauto.

(* qpend_block_body *)
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

(* qpend_block_get_body *)
inverts H3.
simpljoin.
destruct H10 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

kvextH Hcur O0 curtid O. 
kvextH Htcb O0 abtcblsid O.
assert (O'=set O abtcblsid
(abstcblist (set x8 x13 (x9, rdy, Vnull, false, x15)))).
eapply join_get_set_eq;eauto. 
clear H1 H2.
subst.
inverts H.
unfolds.
lets Hrec0: Hrec.
l_rew21_inv1 (get O curtid).
l_rew21_inv1 (get O curtid).
l_rew21_inv1 (get O abtcblsid).
splits.
(* ctid_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.
intros.

casetac pr pr1 Hy Hn.
subst.
tryfalse.
unfolds in H0.
unfolds in H.
simpljoin.
rewrite Htcb in H;inverts H.
rewrite H3 in H4.
inverts H4.
rewrite H12 in H3;inverts H3.
rewrite set_a_get_a in H0.
inverts H0.
rewrite set_a_get_a in H2.
inverts H2.
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
(* obufs_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.

(* kernel_data_equiv *)
unfolds.
apply reachable_get_knldataid in Hrec.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
splits.
(* kernel_task_equiv *)
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.
intros.
split.
split;intros.
destruct H8.
unfolds in H8.
simpljoin.
rewrite Htcb in H8;inverts H8.
rewrite H12 in H3;inverts H3.
eexists x1.

casetac x1 t Hy Hn.
subst.
unfold task_prio_id.
do 5 eexists.
split.
rewrite set_a_get_a;eauto.
rewrite H12 in H10;inverts H10.
rewrite set_a_get_a;eauto.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

destruct H8.
unfolds in H8.
simpljoin.
rewrite set_a_get_a in H8.
inverts H8.
casetac x1 t Hy Hn.
subst.
rewrite set_a_get_a in H10.
inverts H10.
rewrite H12 in H3;inverts H3.
eexists t.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H10;eauto.
rewrite H12 in H3;inverts H3.
eexists x1.
unfolds.
do 5 eexists.
split;eauto.

casetac pr pr0 Hy Hn.
subst.
tryfalse.
lets Hnewt: Htpi.
unfolds in Hnewt.
simpljoin.
rewrite Htcb in H8;inverts H8.
rewrite H10 in H3;inverts H3.
rewrite H12 in H10;inverts H10.
intros.

assert(Hneq: t <> t2).
{
  eapply task_prio_id_tidneq.
  unfolds;do 5 eexists;split;eauto.
  casetac t t2 Hty Htn.
  subst.
  rewrite set_a_get_a in H3.
  inverts H3.
  tryfalse.
  rewrite set_a_get_a' in H3;eauto.
  unfolds;do 5 eexists;split;eauto.
  eauto.
}
rewrite set_a_get_a' in H3;eauto.
assert(Heqt: t1 = t2).
{
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
rewrite H in H3;inverts H3.
splits;eauto.

(* kernel_mq_equiv *)
unfold kernel_mq_equiv.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.

intros.
split.
split;eauto.

intros.
rewrite H8 in H10.
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
destruct Hasrt1.
tryfalse.
simpljoin.
inverts H10.

assert (Hneqx2: x1 <> t0).
{
    lets Hnewa : not_both_mq_and_buffer H0 H8.
    intro.
    subst.
    eapply Hnewa in H11.
    tryfalse.
}
lets Hsemq: mq_ecb H0 H8 H1.
destruct Hsemq.
do 3 destruct H10.
rewrite set_a_get_a'; try intro;tryfalse.
eexists x8,x8,t0.
do 4 eexists.
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
eexists x20.
split;eauto.
unfolds in H17.
simpljoin.
rewrite Htcb in H17; inverts H17.
rewrite H12 in H3;inverts H3.
casetac t x20 Hty Htn.
subst.
rewrite H18 in H12; inverts H12.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.

intros.
simpljoin.
eexists x20.
split;eauto.
unfolds in H17.
simpljoin.
rewrite H12 in H3;inverts H3.
casetac t x20 Hty Htn.
subst.
rewrite set_a_get_a in H17.
inverts H17.
rewrite set_a_get_a in H18.
inverts H18.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a in H17.
inverts H17.
rewrite set_a_get_a' in H18;eauto.
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
eexists x20.
split;eauto.
unfolds in H17.
simpljoin.
rewrite Htcb in H17; inverts H17.
rewrite H12 in H3;inverts H3.
casetac t x20 Hty Htn.
subst.
rewrite H18 in H12; inverts H12.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.

rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.

intros.
simpljoin.
eexists x20.
split;eauto.
unfolds in H17.
simpljoin.
rewrite H12 in H3;inverts H3.
casetac t x20 Hty Htn.
subst.
rewrite set_a_get_a in H17.
inverts H17.
rewrite set_a_get_a in H18.
inverts H18.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a in H17.
inverts H17.
rewrite set_a_get_a' in H18;eauto.
unfolds.
do 5 eexists.
split;eauto.
(* ports_equiv *)
unfolds.
do 4 eexists.
splits;eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
eauto.
rewrite set_a_get_a'; try intro ;tryfalse.
eauto.
intros.
split;eauto.
split.
split;intros;eauto.
intros.
rewrite H8 in H10; inverts H10.
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
rewrite H12 in H3;inverts H3.
casetac t x1 Hty Htn.
subst.
rewrite H12 in H16; inverts H16.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x1.
split;eauto.
unfolds in H11.
simpljoin.
rewrite H12 in H3;inverts H3.
casetac t x1 Hty Htn.
subst.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a in H16.
inverts H16.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a' in H16;eauto.
unfolds.
do 5 eexists.
split;eauto.
(* buffer_equiv *)
rewrite H12 in H3;inverts H3.
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
inverts H3.
lets Hfb: bufidx_diff_dom Hi_neq H H8.
tryfalse.

splits.
split.
intros.
simpljoin.
do 2 eexists.
eauto.

intros.
simpljoin.
eauto.
intros.
rewrite H8 in H10;inverts H10.
split.
lets Hmqed : buffer_ecb H H1.
simpljoin.
rewrite H8 in H10;inverts H10.
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
unfolds in H11.
simpljoin.
rewrite Htcb in H11; inverts H11.

casetac t x5 Hty Htn.
subst.
rewrite H12 in H16; inverts H16.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x5.
split;eauto.
unfolds in H11.
simpljoin.
casetac t x5 Hty Htn.
subst.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a in H16.
inverts H16.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a in H11.
inverts H11.
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
eexists x1.
split;eauto.
unfolds in H11.
simpljoin.
rewrite Htcb in H11; inverts H11.
casetac t x1 Hty Htn.
subst.
rewrite H12 in H16; inverts H16.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a ; eauto.
rewrite set_a_get_a ; eauto.
unfolds.
do 5 eexists.
split.
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x1.
split;eauto.
unfolds in H11.
simpljoin.
casetac t x1 Hty Htn.
subst.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a in H16.
inverts H16.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a' in H16;eauto.
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
unfolds in H10.
simpljoin.
eexists.
unfolds.
do 8 eexists.
splits;eauto.
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
rewrite H in H0;inverts H0.
eauto.
intros.
unfolds in H10.
unfolds in H11.
simpljoin.
rewrite set_a_get_a' in H11; try intro ;tryfalse.
rewrite H10 in H11;inverts H11.
rewrite H18 in H16;inverts H16.
assert(Heqob: objp1 = objp2).
{
  destruct H19.
  destruct H17.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H17.
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

casetac pr pr0 Hy Hn.
subst.
tryfalse.
unfolds in H1.
simpljoin.
lets Hnewt: Htpi.
unfolds in Hnewt.
simpljoin.
rewrite set_a_get_a in H1.
inverts H1.

rewrite Htcb in H;inverts H.
rewrite H12 in H3;inverts H3.
rewrite H12 in H4;inverts H4.
assert(Hneq: t <> t2).
{
  eapply task_prio_id_tidneq.
  unfolds;do 5 eexists;split;eauto.
  casetac t t2 Hty Htn.
  subst.
  rewrite set_a_get_a in H2.
  inverts H2.
  tryfalse.
  rewrite set_a_get_a' in H2;eauto.
  unfolds;do 5 eexists;split;eauto.
  eauto.
}
rewrite set_a_get_a' in H2;eauto.
assert(Heqt: t1 = t2).
{
  unfolds in H0.
  simpljoin.
  rewrite Htcb in H.
  inverts H.
    eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
eauto.

lets Hasrt: rch_hasrt_sat Hrec Hgett Htpi.
simpl in Hasrt.

(* qpend_to_body *)
inverts H3; simpljoin.
destruct H12 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
inverts H.
kvextH Hcur O0 curtid O. 
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 

assert (O'=set
(set O abtcblsid
   (abstcblist (set x7 x9 (x8, rdy, Vnull, false, x17))))
absecblsid
(absecblist
   (set x10 x (absmsgq x12 x13 x14, remove_tid x9 x15)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H4.
subst.
unfolds.
lets Hrec0: Hrec.
l_rew21_inv1 (get O curtid).
l_rew21_inv1 (get O curtid).
l_rew21_inv1 (get O abtcblsid).
rewrite H3 in H17;inverts H17.
splits.
(* ctid_equiv *)
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
rewrite set_a_get_a' in H0; try intro; tryfalse; eauto.
rewrite set_a_get_a in H0.
inverts H0.
rewrite set_a_get_a in H2.
inverts H2.
rewrite Htcb in H;inverts H.
rewrite H3 in H4;inverts H4.
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
(* obufs_equiv *)
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
destruct H1.
unfolds in H1.
simpljoin.
l_rew21_inv1 (get O abtcblsid).
eexists x1.
casetac x1 t Hxy Hxn.
subst.
unfold task_prio_id.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite H3 in H11;inverts H11.
rewrite set_a_get_a;eauto.

unfolds.
do 5 eexists.
split.
rewrite set_a_get_a'; try intro ; tryfalse;eauto.
rewrite set_a_get_a;eauto.
rewrite set_a_get_a';eauto.

destruct H1.
unfolds in H1.
simpljoin.
rewrite set_a_get_a' in H1; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H1.
inverts H1.
casetac x1 t Hy Hn.
subst.
rewrite set_a_get_a in H11.
inverts H11.

eexists t.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H11;eauto.
eexists x1.
unfolds.
do 5 eexists.
split;eauto.

casetac pr pr0 Hy Hn.
subst.
tryfalse.
lets Hnewt: Htpi.
unfolds in Hnewt.
simpljoin.
rewrite Htcb in H1;inverts H1.
rewrite H3 in H11;inverts H11.
intros.

assert(Hneq: t <> t2).
{
  eapply task_prio_id_tidneq.
  unfolds;do 5 eexists;split;eauto.
  casetac t t2 Hty Htn.
  subst.
  rewrite set_a_get_a in H1.
  inverts H1.
  tryfalse.
  rewrite set_a_get_a' in H1;eauto.
  unfolds;do 5 eexists;split;eauto.
  eauto.
}
rewrite set_a_get_a' in H1;eauto.
assert(Heqt: t1 = t2).
{
  eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
rewrite H in H1;inverts H1.
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
rewrite H11 in H1.
inverts H1.
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
inverts H1.
assert (Hneqx2: x1 <> t0).
{
    lets Hnewa : not_both_mq_and_buffer H0 H11 .
    intro.
    subst.
    eapply Hnewa in H12.
    tryfalse.
}
lets Hsemq: mq_ecb H0 H11 Hecb.
destruct Hsemq.
do 3 destruct H1.
rewrite set_a_get_a.
eexists x4,(set x4 x1 (absmsgq x12 x13 x14, remove_tid t x15)),t0.
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

unfolds in H16.
simpljoin.
rewrite Htcb in H16; inverts H16.

casetac t x17 Hty Htn.
subst.
rewrite H3 in H17; inverts H17.

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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.

intros.
simpljoin.
eexists x17.
split;eauto.

unfolds in H16.
simpljoin.
casetac t x17 Hty Htn.
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
eexists x17.
split;eauto.

unfolds in H16.
simpljoin.
rewrite Htcb in H16; inverts H16.

casetac t x17 Hty Htn.
subst.
rewrite H3 in H17; inverts H17.

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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.

intros.
simpljoin.
eexists x17.
split;eauto.

unfolds in H16.
simpljoin.
casetac t x17 Hty Htn.
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
casetac x a Hau Han.
subst.
rewrite H6 in H1.
inverts H1.
eexists x1.
rewrite set_a_get_a'; eauto.

simpljoin.
casetac x a Hau Han.
subst.
rewrite set_a_get_a in H1.
inverts H1.
rewrite set_a_get_a' in H1; eauto.

intros.
casetac x a Hau Han.
subst.
rewrite set_a_get_a in H11.
inverts H11.
rewrite set_a_get_a' in H11; eauto.
rewrite H1 in H11;inverts H11.
(* tidls_equiv *)
unfolds.
split;eauto.
intros.
split.
intros.
simpljoin.
eexists x1.
split;eauto.

unfolds in H12.
simpljoin.
rewrite Htcb in H12; inverts H12.

casetac t x1 Hty Htn.
subst.
rewrite H3 in H15; inverts H15.
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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x1.
split;eauto.
unfolds in H12.
simpljoin.
casetac t x1 Hty Htn.
subst.
rewrite set_a_get_a' in H12; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H12.
inverts H12.
rewrite set_a_get_a in H15.
inverts H15.
unfolds.
do 5 eexists.
split;eauto.

rewrite set_a_get_a' in H12; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H12.
inverts H12.
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
assert(Hix: eid = x  \/  eid <> x) by tauto.
destruct Hix.
subst.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
destruct Hasrt1.
tryfalse.
simpljoin.
inverts H1.
lets Hfb: bufidx_diff_dom Hi_neq H H11.
tryfalse.

splits.
split.
intros.
simpljoin.
do 2 eexists.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
rewrite set_a_get_a' in H11;eauto.
intros.
rewrite set_a_get_a' in H12;eauto.
rewrite H11 in H12;inverts H12.
split.
lets Hmqed : buffer_ecb H Hecb.
simpljoin.
rewrite H11 in H12;inverts H12.
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
unfolds in H15.
simpljoin.
rewrite Htcb in H15; inverts H15.

casetac t x17 Hty Htn.
subst.
rewrite H3 in H16; inverts H16.
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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x17.
split;eauto.
unfolds in H15.
simpljoin.
casetac t x17 Hty Htn.
subst.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H15.
inverts H15.
rewrite set_a_get_a in H16.
inverts H16.
unfolds.
do 5 eexists.
split;eauto.

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
eexists x1.
split;eauto.
unfolds in H15.
simpljoin.
rewrite Htcb in H15; inverts H15.

casetac t x1 Hty Htn.
subst.
rewrite H3 in H16; inverts H16.
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
rewrite set_a_get_a ;eauto.
rewrite set_a_get_a' ;eauto.
intros.
simpljoin.
eexists x1.
split;eauto.
unfolds in H15.
simpljoin.
casetac t x1 Hty Htn.
subst.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H15.
inverts H15.
rewrite set_a_get_a in H16.
inverts H16.
unfolds.
do 5 eexists.
split;eauto.
rewrite set_a_get_a' in H15; try intro ; tryfalse;eauto.
rewrite set_a_get_a in H15.
inverts H15.
rewrite set_a_get_a' in H16;eauto.
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
unfolds in H11.
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
unfolds in H11.
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
unfolds in H11.
unfolds in H12.
simpljoin.
rewrite set_a_get_a' in H12; try intro ;tryfalse.
rewrite set_a_get_a' in H12; try intro ;tryfalse.
rewrite H11 in H12;inverts H12.
rewrite H17 in H15;inverts H15.
assert(Heqob: objp1 = objp2).
{
  destruct H19.
  destruct H16.
  simpljoin.
  simpljoin.
  tryfalse.
  destruct H16.
  simpljoin.
  tryfalse.
  simpljoin.
  inverts H12.
  eauto.
}
subst.
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
casetac pr pr0 Hy Hn.
subst.
tryfalse.
unfolds in H1.
simpljoin.

lets Hnewt: Htpi.
unfolds in Hnewt.
simpljoin.
rewrite set_a_get_a' in H1; try intro ;tryfalse.
rewrite set_a_get_a in H1.
inverts H1.
rewrite Htcb in H;inverts H.
rewrite H3 in H4;inverts H4.

assert(Hneq: t <> t2).
{
  eapply task_prio_id_tidneq.
  unfolds;do 5 eexists;split;eauto.
  casetac t t2 Hty Htn.
  subst.
  rewrite set_a_get_a in H2.
  inverts H2.
  tryfalse.
  rewrite set_a_get_a' in H2;eauto.
  unfolds;do 5 eexists;split;eauto.
  eauto.
}
rewrite set_a_get_a' in H2;eauto.
assert(Heqt: t1 = t2).
{
  unfolds in H0.
  simpljoin.
  rewrite Htcb in H.
  inverts H.
    eapply tid_unique;
  unfolds; do 5 eexists; eauto.
}
subst.
eauto.

(* qpend_to_body *)
solve_endabt.

(* qpend_block_get_body *)
solve_endabt.
destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
destruct n; [ my_succs_solver_same_absdata | idtac].
re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.









