(* Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs.
Require Import qprt_apispecs.
Require Import intspecs.
Require Import osspecs.
Require Import properties.

Require Import data_invs.
Require Import equiv_prop.
Require Import assms.
Require Import succ_gen.
Require Import if_good_code.

Require Import hasrt_sat_preserve.
Require Import FunctionalExtensionality.

Require Import integrity_lemma.
Set Keyed Unification.
Require Import protect.
Require Import spec_aux_defs.


Require Import confidentiality_tactics.
Require Import common_lemmas.


Lemma mqrecv_nabt_spec_step_data_equiv_tskd_preserve:
forall O cd n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
(* good_client_code pc -> *)
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)->
task_prio_id O pr t ->
get O curtid = Some (oscurt t)->
get T t = Some (curs (hapi_code cd),(ke, ks))->
mqreceive vl <> ABORT ->
nth_error (get_all_succs (mqreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O'->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgtc Hrec Hnflo Htpi Hctid Hgett Hnabt Hnth Hstep.
introv Hi_neq HO_neq.
remember vl as recv_vl.
do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
try destruct v; simpl in Hnabt; tryfalse;
try destruct v1; simpl in Hnabt; tryfalse;
try destruct v3; simpl in Hnabt; tryfalse;
try destruct v5; simpl in Hnabt; tryfalse;
try destruct v7; simpl in Hnabt; tryfalse.
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
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
destruct n; [ my_succs_solver_same_absdata | idtac].
(*qpend_get_no_pwl_succ_body*)
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
unfolds in Hasrt1.
destruct Hasrt1 as (Hmqd & Hmqptr).

unfolds in Hmqptr.
simpljoin.
destruct H16.
destruct H16.
tryfalse.
destruct H16.
destruct H16.
subst.
inverts H.
inverts H20.
rewrite H1 in H14;inverts H14.

assert(Hi40: i0 = i4  \/  i0 <> i4) by tauto.
destruct Hi40 as [ Hy40 | Hn40  ].
subst.

lets Hfa: mqidx_diff_dom Hi_neq H0 Hmqd;tryfalse.
lets Hneq: mq_ecb_ref_distinct Hn40 H15 H2. 

lets Hsemq: mq_ecb H1 H2 Hecb.
destruct Hsemq.
do 3 destruct H.

lets Hsemq1: mq_ecb H1 H15 Hecb.
destruct Hsemq1.
do 3 destruct H14.

rewrite H4 in H14;inverts H14.

eexists x8 ,(set x8 x23 (absmsgq x11 x25 nil, x27)) ,t0 .
do 4 eexists.
splits;eauto.
rewrite set_a_get_a;eauto.
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
eexists x12.
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
eexists x12.
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
eexists x12.
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
eexists x12.
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
unfolds.
do 2 eexists.
splits;eauto.
rewsimp.
eauto.

intros.
Require Import mqsend_cproof1.
lets Hasrt1 : rch_hasrt_sat Hrec0 Hgett Htpi.
simpl in Hasrt1.
lets Heif: mq_buffer_eid_diff Hasrt1 H0.
inverts H.

splits.
split.
intros.
simpljoin.
do 2 eexists.
rewrite set_a_get_a';eauto.

intros.
simpljoin.
rewrite set_a_get_a' in H;eauto.

intros.
rewrite set_a_get_a' in H2;eauto.
rewrite H in H2;inverts H2.
split.
lets Hmqed : buffer_ecb H0 Hecb.
simpljoin.
rewrite H in H2;inverts H2. *)



(* --------------------- *)



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
Require Import mqsend_cproof.

(* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\ *)

Lemma qpend_get_no_pwl_succ_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qpend_get_no_pwl_succ_body (v4 :: v0 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.
inverts Hspec; simpljoin.
destruct H7 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

kvextH Hcur O0 curtid O. 
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 

assert (O'=set O absecblsid (absecblist (set x2 x (absmsgq x5 x6 nil, x7)))).
eapply join_get_set_eq;eauto.

clear H1 H2 H0.
subst.

unfolds.
l_rew21_inv1 (get O curtid).
match goal with H: _ :: _ :: nil = _ :: _ :: nil |- _ => inverts H end.
splits.

(* ctid_equiv  *)
unfolds.
do 2 eexists.
rewrite set_a_get_a'; eauto.
splits;eauto.

intros.
eapply prio_unique_set_ntls; eauto.
intro; tryfalse.
intro; tryfalse.

(* bufs_equiv *)
destruct Hbusq as (Hib & Hob).
unfolds in Hib; simpljoin.
unfolds in Hob; simpljoin.

unfolds; split;
unfolds;
do 2 eexists;
splits;eauto;
rewrite set_a_get_a'; try intro ; tryfalse;eauto.

(* kernel_data_equiv *)
destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
unfolds; splits.

unfolds in Hkenlt; simpljoin.
unfolds.
{ 
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
intros.
splits.
splits; intros;
[ eapply task_prio_id_set_ntls_eq; eauto |
eapply task_prio_id_set_ntls_eq'; eauto];
intro; tryfalse.
do 2 l_rew21_inv1 (get O abtcblsid).
intros. 
assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H in H2;inverts H2.
splits; eauto. }

(*kernel_mq_equiv*)
unfolds in Hkernlq;simpljoin.
{
unfolds.
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

intros.
simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hdom & Hptr).
casetac i0 i1 Heq Hneq.
subst.
eapply mqidx_diff_dom in H5; eauto; tryfalse.
splits.
splits; intros; auto.
l_rew21_inv1 (get O absmqattrid).

intros.
unfolds.
eapply H4 in H5; eauto.
simpljoin.
eapply H7 in H; eauto.
unfolds in Hptr; simpljoin.
destruct H10 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin.
do 8 eexists; splits; eauto.
destruct H11 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get O absecblsid).
rewrite H13 in H14; inverts H14.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H9 H6.

do 2 right.
exists x2.
rewrite set_a_get_a; eauto. 
exists (set x2 p (absmsgq x5 x6 nil, x7)).
eexists.
rewrite set_a_get_a'; eauto.
do 4 eexists; splits; eauto.

(*mq_ed_equiv*)
unfolds.
unfolds in H15; simpljoin.
do 4 eexists; splits; eauto.

(* tidls_equiv_pws *)
unfolds.
unfold tidls_equiv in H10; simpljoin.
splits; eauto.
intros.
splits; intros; simpljoin.
eexists; splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 5 eexists; eauto.

unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
eexists; splits; eauto;
do 5 eexists; eauto.

(*tidls_equiv_ws*)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin;
[rewrite set_a_get_a'; try intro; tryfalse; eauto | 
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse ];
eexists; splits; eauto;
do 5 eexists; eauto. }

(*ports_equiv*)
unfold ports_equiv in *; simpljoin.
l_rew21_inv1 (get O osdomainportid).
l_rew21_inv1 (get O absecblsid).
rewrite set_a_get_a; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H3 in H5; inverts H5.
rewrite set_a_get_a'; eauto. 

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.

intros.
casetac a x Heq Hneq;
subst.
rewrite H3 in H5; inverts H5.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

(* tidls_equiv *)
l_rew21_inv1 (get O absecblsid).
eapply H6 in H7; eauto.
unfold tidls_equiv in *.
destruct H7 as (Hlen & Hsl).
splits; eauto.
intros pr0.
splits; intros Hg.
eapply Hsl in Hg; eauto.
destruct Hg as (tk & Hin & Htkid).
exists tk.
splits; eauto.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a' ; try intro; tryfalse.
do 5 eexists; splits; eauto.

eapply Hsl.
simpljoin.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
eexists; splits; eauto.
do 5 eexists; splits; eauto.

destruct Hcapq as (Hbufeq & Hcapq).
(* buffer_equiv *)
unfold buffer_equiv in *.
rewrite set_a_get_a.
simpljoin.
do 2 eexists; splits; eauto.
intros e0 Hb.
lets Hm: H1 Hb.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absecblsid).
destruct Hm as (Hcap1 & Hcap2).
lets Heif: mq_buffer_eid_diff Hasrt Hb.
rewrite set_a_get_a';eauto.
splits; eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H in H0;inverts H0.
lets Hmqed : buffer_ecb Hb Hecb.
simpljoin.
rewrite H in H0;inverts H0.

split.
(*mq_ed_equiv*)
unfolds.
do 4 eexists; splits; eauto.
(* tidls_equiv_pws *)
unfolds.
splits; eauto.
intros.
splits; intros; simpljoin.
eexists; splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 5 eexists; eauto.

unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
eexists; splits; eauto;
do 5 eexists; eauto.
(* tidls_equiv_pws *)
unfolds.
splits; eauto.
intros.
splits; intros; simpljoin.
eexists; splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 5 eexists; eauto.

unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
eexists; splits; eauto;
do 5 eexists; eauto.

(* cap_equiv *)
unfold cap_equiv in *.
rewrite set_a_get_a'; try intro; tryfalse.
simpljoin.
do 2 eexists; splits; eauto.

intros pr0 Hd.
lets Hm: H2 Hd.
l_rew21_inv1 (get O cspaceid).
destruct Hm as (Hcap1 & Hcap2).
splits; eauto.

intros idx Hdom.
lets Hs: Hcap2 Hdom.
destruct Hs as (Hs1 & Hs2).
splits.
splits; intros Hs;
unfold mq_ptr in *.
rewrite set_a_get_a'; try intro; tryfalse.
auto.
rewrite set_a_get_a' in Hs; try intro; tryfalse.
auto.

intros.
eapply Hs2; eauto.
unfold mq_ptr in *.
rewrite set_a_get_a' in H4; try intro; tryfalse.
auto.

(* client_data_equiv *)
unfold client_data_equiv in *.
simpljoin.
do 6 eexists; splits; eauto.

unfold local_envs_equiv in *.
intros.
eapply H2; eauto.
unfold task_prio_id in *.
rewrite set_a_get_a' in H1; try intro; tryfalse; auto.
Qed.

Lemma qpend_get_ex_pwl_before_sched_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qpend_get_ex_pwl_before_sched_body (v4 :: v0 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.
inverts Hspec; simpljoin.
destruct H9 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 
match goal with H: _ :: _ :: nil = _ :: _ :: nil |- _ => inverts H end.

assert (O'=set
           (set O abtcblsid
              (abstcblist (set x2 x12 (x8, rdy, x11, x13, x15)))) absecblsid
           (absecblist
              (set x1 x
                 (absmsgq (x4 ++ x11 :: nil) x5 (remove_tid x12 x6), x7)))).
eapply join_get_set_eq_2;eauto.

clear H1 H0.
subst.
splits.

(*ctid_equiv*)
destruct Hctq as (t1 & t2 & Hct1 & Hct2 & Hpreq).
unfolds; intros.
exists t1 t2.
splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a'; try intro; tryfalse.
eauto.

intros.
eapply Hpreq; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.

(*bufs_equiv*)
destruct Hbusq as (Hib & Hob).
unfolds in Hib; simpljoin.
unfolds in Hob; simpljoin.

unfolds; split;
unfolds;
intros;
do 2 eexists; split; eauto;
rewrite set_a_get_a'; try intro; tryfalse; eauto;
rewrite set_a_get_a'; try intro; tryfalse; eauto.

(*kernel_data_equiv*)
destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
unfolds; splits.

unfolds in Hkenlt; simpljoin.
unfolds.
{ 
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
intros.
splits.
splits; intros;
destruct H8 as (t1 & Htkid);
exists t1;
unfold task_prio_id in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a; eauto. 
l_rew21_inv1 (get O abtcblsid).
simpljoin.
l_rew21_inv1 (get O abtcblsid).
casetac x12 t1 He Hne;
subst;
do 5 eexists; splits; eauto;
[rewrite H5 in H9; inverts H9;
rewrite set_a_get_a; eauto |
rewrite set_a_get_a'; try intro; tryfalse; eauto].

rewrite set_a_get_a' in Htkid; try intro; tryfalse; eauto.
rewrite set_a_get_a in Htkid; eauto.
simpljoin.
match goal with H: Some _ = Some _ |- _ => inverts H end.
casetac x12 t1 He Hne.
subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
do 5 eexists; splits; eauto.
match goal with
   H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H; eauto end.
do 5 eexists; splits; eauto.

simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hmqid & Hptr).
unfolds in Hptr; simpljoin.
destruct H10 as [(Hn & Hn') | (p & He & Heq)]; tryfalse; subst.
inverts Heq.
unfolds in H4; simpljoin. (* GetHWait *)
lets Hf:mq_part_consistent H8 Hmqid H9 Hecb H2; eauto.
specialize (Hf x12).
destruct Hf; eauto.
rewrite H5 in H7; inverts H7.
destruct H11 as (Htkid' & Heq').
unfolds in Htkid'; simpljoin.
l_rew21_inv1 (get O abtcblsid).
rewrite H5 in H11; inverts H11. 

intros. 
do 2 l_rew21_inv1 (get O abtcblsid).
casetac x12 t2 He Hne;
subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.
assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H11 in H12;inverts H12.
splits; eauto.  
      }

(*kernel_mq_equiv*)
unfolds in Hkernlq;simpljoin.
{
unfolds.
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

intros.
simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hdom & Hptr).
casetac i0 i1 Heq Hneq.
subst.
eapply mqidx_diff_dom in H7; eauto; tryfalse.
splits.
splits; intros; auto.
l_rew21_inv1 (get O absmqattrid).

intros.
unfolds.
eapply H6 in H7; eauto.
simpljoin.
eapply H9 in H; eauto.
unfolds in Hptr; simpljoin.
destruct H12 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin. (*mq_equiv*)
do 8 eexists; splits; eauto.
destruct H13 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get O absecblsid).
rewrite H15 in H16; inverts H16.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H11 H8.

do 2 right.
exists x1.
rewrite set_a_get_a; eauto. 
exists (set x1 p (absmsgq (x4 ++ x11 :: nil) x5 (remove_tid x12 x6), x7)).
exists x30.
rewrite set_a_get_a'; eauto.
do 4 eexists; splits; eauto.

(*mq_ed_equiv*)
unfolds.
unfolds in H17; simpljoin.
do 4 eexists; splits; eauto.

(* tidls_equiv_pws *)
unfolds.
unfold tidls_equiv in H12; simpljoin.
splits; eauto.
intros.
splits; intros; simpljoin.
exists x29.
splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists.
exists (set x2 x12 (x8, rdy, x11, x13, x15)).
casetac x29 x12 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H5 in H19; inverts H19.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x29 x12 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto ];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(*tidls_equiv_ws*)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x2 x12 (x8, rdy, x11, x13, x15)).
casetac x12 x He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H5 in H16; inverts H16.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x12 x He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto. }

(*ports_equiv*)
unfold ports_equiv in *; simpljoin.
l_rew21_inv1 (get O osdomainportid).
l_rew21_inv1 (get O absecblsid).
rewrite set_a_get_a; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H2 in H7; inverts H7.
rewrite set_a_get_a'; eauto. 

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

intros.
casetac a x Heq Hneq;
subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

(* tidls_equiv *)
l_rew21_inv1 (get O absecblsid).
eapply H8 in H9; eauto.
unfold tidls_equiv in *.
destruct H9 as (Hlen & Hsl).
splits; eauto.
intros pr0.
splits; intros Hg.
eapply Hsl in Hg; eauto.
destruct Hg as (tk & Hin & Htkid).
exists tk.
splits; eauto.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a' ; try intro; tryfalse.
rewrite set_a_get_a; eauto.
 l_rew21_inv1 (get O abstcblsid).
casetac x12 tk He Hne; subst;
eexists;
[ exists (set x2 tk (x8, rdy, x11, x13, x15));
rewrite set_a_get_a; eauto;
rewrite H5 in H10; inverts H10 |
exists (set x2 x12 (x8, rdy, x11, x13, x15));
rewrite set_a_get_a';eauto];
do 3 eexists; splits; eauto.

eapply Hsl.
simpljoin.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x12 x1 He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto]; 
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* buffer_equiv *)
unfold buffer_equiv in *.
rewrite set_a_get_a.
simpljoin.
do 2 eexists; splits; eauto.
intros e0 Hb.
lets Hm: H3 Hb.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absecblsid).
destruct Hm as (Hcap1 & Hcap2).
lets Heif: mq_buffer_eid_diff Hasrt Hb.
rewrite set_a_get_a';eauto.
splits; eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H in H1;inverts H1.
lets Hmqed : buffer_ecb Hb Hecb.
simpljoin.
rewrite H in H1;inverts H1.

split.
(*mq_ed_equiv*)
unfolds.
do 4 eexists; splits; eauto.
(* tidls_equiv_pws *)
unfolds.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x2 x12 (x8, rdy, x11, x13, x15)).
casetac x12 x17 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H5 in H8; inverts H8.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x12 x17 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* tidls_equiv_pws *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x2 x12 (x8, rdy, x11, x13, x15)).
casetac x12 x17 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H5 in H8; inverts H8.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x12 x17 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.
(* cap_equiv *)
unfold cap_equiv in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a'; try intro; tryfalse.
simpljoin.
do 2 eexists; splits; eauto.

intros pr0 Hd.
lets Hm: H3 Hd.
l_rew21_inv1 (get O cspaceid).
destruct Hm as (Hcap1 & Hcap2).
splits; eauto.

intros idx Hdom.
lets Hs: Hcap2 Hdom.
destruct Hs as (Hs1 & Hs2).
splits.
splits; intros Hs;
unfold mq_ptr in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a'; try intro; tryfalse.
auto.
rewrite set_a_get_a' in Hs; try intro; tryfalse.
rewrite set_a_get_a' in Hs; try intro; tryfalse.
auto.

intros.
eapply Hs2; eauto.
unfold mq_ptr in *; simpljoin.
do 2 match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
do 8 eexists; splits; eauto.

(* client_data_equiv *)
unfold client_data_equiv in *.
simpljoin.
do 6 eexists; splits; eauto.

unfold local_envs_equiv in *.
intros.
eapply H3; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse.
match goal with H: Some _ = Some _ |- _ => inverts H end.

 l_rew21_inv1 (get O abstcblsid).
casetac t2 x12 He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse];
do 5 eexists; splits; eauto.
Qed. 

Lemma qpend_block_body_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qpend_block_body (v4 :: v0 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.
inverts Hspec; simpljoin.
inverts H8.
match goal with H: _ :: _ :: nil = _ :: _ :: nil |- _ => inverts H end.

kvextH Hcur O0 curtid O. 
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O.

assert (O'=set
          (set O abtcblsid
             (abstcblist
                (set x3 x11 (x8, wait (os_stat_q x) x12, x1, x2, x14))))
          absecblsid (absecblist (set x5 x (absmsgq nil x10 x13, x11 :: x7)))).
eapply join_get_set_eq_2;eauto.
clear H0 H1 H4.
subst.

l_rew21_inv1 (get O curtid).
splits.

(*ctid_equiv*)
destruct Hctq as (t1 & t2 & Hct1 & Hct2 & Hpreq).
unfolds; intros.
exists t1 t2.
splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a'; try intro; tryfalse.
eauto.

intros.
eapply Hpreq; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.

(*bufs_equiv*)
destruct Hbusq as (Hib & Hob).
unfolds in Hib; simpljoin.
unfolds in Hob; simpljoin.

unfolds; split;
unfolds;
intros;
do 2 eexists; split; eauto;
do 2 try rewrite set_a_get_a'; try intro; tryfalse; eauto.

(*kernel_data_equiv*)
destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
unfolds; splits.

(*kernel_task_equiv*)
unfolds in Hkenlt; simpljoin.
unfolds.
{ 
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
intros.
splits.
splits; intros;
destruct H8 as (t1 & Htkid);
exists t1;
unfold task_prio_id in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a; eauto. 
l_rew21_inv1 (get O abtcblsid).
simpljoin.
l_rew21_inv1 (get O abtcblsid).
casetac t t1 He Hne;
subst;
do 5 eexists; splits; eauto;
[rewrite H5 in H9; inverts H9;
rewrite set_a_get_a; eauto |
rewrite set_a_get_a'; try intro; tryfalse; eauto].

rewrite set_a_get_a' in Htkid; try intro; tryfalse; eauto.
rewrite set_a_get_a in Htkid; eauto.
simpljoin.
match goal with H: Some _ = Some _ |- _ => inverts H end.
casetac t t1 He Hne.
subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
do 5 eexists; splits; eauto.
match goal with
   H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H; eauto end.
do 5 eexists; splits; eauto.

simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hmqid & Hptr).
unfolds in Hptr; simpljoin.
destruct H10 as [(Hn & Hn') | (p & He & Heq)]; tryfalse; subst.
inverts Heq.
(* l_rew21_inv1 (get O curtid). *)
intros.
casetac t t2 He Hne; subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
unfolds in Htpi; simpljoin.
do 3 l_rew21_inv1 (get O abtcblsid).
rewrite H11 in H5; inverts H5; tryfalse.
match goal with
   H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H; eauto end.
assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H7 in H10; inverts H10; eauto. }

(*kernel_mq_equiv*)
unfolds in Hkernlq;simpljoin.
{
unfolds.
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

intros.
simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hdom & Hptr).
casetac i0 i1 Heq Hneq.
subst.
eapply mqidx_diff_dom in H7; eauto; tryfalse.
splits.
splits; intros; auto.
l_rew21_inv1 (get O absmqattrid).

intros.
unfolds.
eapply H4 in H7; eauto.
simpljoin.
eapply H9 in H; eauto.
unfolds in Hptr; simpljoin.
destruct H12 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin. (*mq_equiv*)
do 8 eexists; splits; eauto.
destruct H13 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get O absecblsid).
rewrite H15 in H16; inverts H16.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H11 H8.

do 2 right.
exists x5.
rewrite set_a_get_a; eauto. 
exists (set x5 p (absmsgq nil x10 x13, t :: x7)).
exists x29.
rewrite set_a_get_a'; eauto.
do 4 eexists; splits; eauto.

(*mq_ed_equiv*)
unfolds.
unfolds in H17; simpljoin.
do 4 eexists; splits; eauto.

(* tidls_equiv_pws *)
unfolds.
unfold tidls_equiv in H12; simpljoin.
splits; eauto.
intros.
splits; intros; simpljoin.
exists x28.
splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists.
exists (set x3 t (x8, wait (os_stat_q p) x12, x1, x2, x14)).
casetac x28 t He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H5 in H19; inverts H19.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x28 t He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto ];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(*tidls_equiv_ws*)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x3 t (x8, wait (os_stat_q p) x12, x1, x2, x14)).
casetac t x He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H5 in H16; inverts H16.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac t x He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto. }

(*ports_equiv*)
unfold ports_equiv in *; simpljoin.
l_rew21_inv1 (get O osdomainportid).
l_rew21_inv1 (get O absecblsid).
rewrite set_a_get_a; eauto.
do 2 try rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H2 in H7; inverts H7.
rewrite set_a_get_a'; eauto. 

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

intros.
casetac a x Heq Hneq;
subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

(* tidls_equiv *)
l_rew21_inv1 (get O absecblsid).
eapply H8 in H9; eauto.
unfold tidls_equiv in *.
destruct H9 as (Hlen & Hsl).
splits; eauto.
intros pr0.
splits; intros Hg.
eapply Hsl in Hg; eauto.
destruct Hg as (tk & Hin & Htkid).
exists tk.
splits; eauto.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a' ; try intro; tryfalse.
rewrite set_a_get_a; eauto.
 l_rew21_inv1 (get O abstcblsid).
casetac t tk He Hne; subst;
eexists;
[ exists (set x3 tk (x8, wait (os_stat_q x) x12, x1, x2, x14));
rewrite set_a_get_a; eauto;
rewrite H5 in H10; inverts H10 |
exists (set x3 t (x8, wait (os_stat_q x) x12, x1, x2, x14));
rewrite set_a_get_a';eauto];
do 3 eexists; splits; eauto.

eapply Hsl.
simpljoin.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac t x5 He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto]; 
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* buffer_equiv *)
unfold buffer_equiv in *.
rewrite set_a_get_a.
simpljoin.
do 2 eexists; splits; eauto.
intros e0 Hb.
lets Hm: H3 Hb.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absecblsid).
destruct Hm as (Hcap1 & Hcap2).
lets Heif: mq_buffer_eid_diff Hasrt Hb.
rewrite set_a_get_a';eauto.
splits; eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H in H1;inverts H1.
lets Hmqed : buffer_ecb Hb Hecb.
simpljoin.
rewrite H in H1;inverts H1.

split.
(*mq_ed_equiv*)
unfolds.
do 4 eexists; splits; eauto.
(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x3 t (x8, wait (os_stat_q x) x12, x1, x2, x14)).
casetac t x16 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H5 in H8; inverts H8.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac t x16 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x3 t (x8, wait (os_stat_q x) x12, x1, x2, x14)).
casetac t x16 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H5 in H8; inverts H8.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac t x16 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* cap_equiv *)
unfold cap_equiv in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a'; try intro; tryfalse.
simpljoin.
do 2 eexists; splits; eauto.

intros pr0 Hd.
lets Hm: H3 Hd.
l_rew21_inv1 (get O cspaceid).
destruct Hm as (Hcap1 & Hcap2).
splits; eauto.

intros idx Hdom.
lets Hs: Hcap2 Hdom.
destruct Hs as (Hs1 & Hs2).
splits.
splits; intros Hs;
unfold mq_ptr in *;
do 2 try rewrite set_a_get_a'; try intro; tryfalse;
auto.
do 2 try rewrite set_a_get_a' in Hs; try intro; tryfalse.
auto.

intros.
eapply Hs2; eauto.
unfold mq_ptr in *; simpljoin.
do 2 match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
do 8 eexists; splits; eauto.

(* client_data_equiv *)
unfold client_data_equiv in *.
simpljoin.
do 6 eexists; splits; eauto.

unfold local_envs_equiv in *.
intros.
eapply H3; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse.
match goal with H: Some _ = Some _ |- _ => inverts H end.

 l_rew21_inv1 (get O abstcblsid).
casetac t2 t He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse];
do 5 eexists; splits; eauto.
Qed. 

Lemma qpend_block_get_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qpend_block_get_body (v4 :: v0 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.
inverts Hspec; simpljoin.
destruct H6 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
match goal with H: _ :: _ :: nil = _ :: _ :: nil |- _ => inverts H end.

kvextH Hcur O0 curtid O. 
kvextH Htcb O0 abtcblsid O.

assert (O'= set O abtcblsid (abstcblist (set x1 x6 (x2, rdy, Vnull, false, x8)))).
eapply join_get_set_eq;eauto. 
clear H1 H0.
subst.

splits.
(*ctid_equiv*)
destruct Hctq as (t1 & t2 & Hct1 & Hct2 & Hpreq).
unfolds; intros.
exists t1 t2.
splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse.
eauto.

intros.
eapply Hpreq; eauto.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a' in H0; try intro; tryfalse.

(*bufs_equiv*)
destruct Hbusq as (Hib & Hob).
unfolds in Hib; simpljoin.
unfolds in Hob; simpljoin.

unfolds; split;
unfolds;
intros;
do 2 eexists; split; eauto;
rewrite set_a_get_a'; try intro; tryfalse; eauto;
rewrite set_a_get_a'; try intro; tryfalse; eauto.

(*kernel_data_equiv*)
destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
unfolds; splits.

(*kernel_task_equiv*)
unfolds in Hkenlt; simpljoin.
unfolds.
{ 
do 2 eexists; splits; eauto.
rewrite set_a_get_a; eauto.
intros.
splits.
splits; intros;
destruct H6 as (t1 & Htkid);
exists t1;
unfold task_prio_id in *.
rewrite set_a_get_a; eauto. 
l_rew21_inv1 (get O abtcblsid).
simpljoin.
l_rew21_inv1 (get O abtcblsid).
casetac x6 t1 He Hne;
subst;
do 5 eexists; splits; eauto;
[rewrite H2 in H7; inverts H7;
rewrite set_a_get_a; eauto |
rewrite set_a_get_a'; try intro; tryfalse; eauto].

rewrite set_a_get_a in Htkid; eauto.
simpljoin.
match goal with H: Some _ = Some _ |- _ => inverts H end.
casetac x6 t1 He Hne.
subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
do 5 eexists; splits; eauto.
match goal with
   H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H; eauto end.
do 5 eexists; splits; eauto.

simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hmqid & Hptr).
unfolds in Hptr; simpljoin.
destruct H8 as [(Hn & Hn') | (p & He & Heq)]; tryfalse; subst.
inverts Heq.
l_rew21_inv1 (get O curtid).
intros.

casetac t t2 He Hne; subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
unfolds in Htpi; simpljoin.
do 3 l_rew21_inv1 (get O abtcblsid).
rewrite H2 in H9; inverts H9; tryfalse.
match goal with
   H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H; eauto end.
assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H5 in H8; inverts H8; eauto. }

(*kernel_mq_equiv*)
unfolds in Hkernlq;simpljoin.
{
unfolds.
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

intros.
simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hdom & Hptr).
casetac i0 i1 Heq Hneq.
subst.
eapply mqidx_diff_dom in H5; eauto; tryfalse.
splits.
splits; intros; auto.
l_rew21_inv1 (get O absmqattrid).

intros.
unfolds.
eapply H4 in H5; eauto.
simpljoin.
eapply H7 in H; eauto.
unfolds in Hptr; simpljoin.
destruct H10 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin. (*mq_equiv*)
do 8 eexists; splits; eauto.
destruct H11 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get O absecblsid).
rewrite H13 in H14; inverts H14.
(* l_rew21_inv1 (get O absecblsid). *)
l_rew21_inv1 (get O absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H9 H6.

do 2 right.
exists x22.
rewrite set_a_get_a'; eauto.
do 6 eexists; splits; eauto.

(*mq_ed_equiv*)
unfolds.
unfolds in H15; simpljoin.
do 4 eexists; splits; eauto.

(* tidls_equiv_pws *)
unfolds.
unfold tidls_equiv in H10; simpljoin.
splits; eauto.
intros.
splits; intros; simpljoin.
exists x25.
splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a; eauto.
eexists.
exists (set x1 x6 (x2, rdy, Vnull, false, x8)).
casetac x25 x6 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H2 in H17; inverts H17.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x25 x6 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse;eauto ];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(*tidls_equiv_ws*)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x1 x6 (x2, rdy, Vnull, false, x8)).
casetac x6 x He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H2 in H14; inverts H14.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x6 x He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.
intro; tryfalse. }

(*ports_equiv*)
unfold ports_equiv in *; simpljoin.
l_rew21_inv1 (get O osdomainportid).
l_rew21_inv1 (get O absecblsid).
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; eauto. 

(* tidls_equiv *)
intros.
eapply H6 in H4; eauto.
unfold tidls_equiv in *.
destruct H4 as (Hlen & Hsl).
splits; eauto.
intros pr0.
splits; intros Hg.
eapply Hsl in Hg; eauto.
destruct Hg as (tk & Hin & Htkid).
exists tk.
splits; eauto.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a; eauto.
 l_rew21_inv1 (get O abstcblsid).
casetac x6 tk He Hne; subst;
eexists;
[ exists (set x1 tk (x2, rdy, Vnull, false, x8));
rewrite set_a_get_a; eauto;
rewrite H2 in H9; inverts H9 |
exists (set x1 x6 (x2, rdy, Vnull, false, x8));
rewrite set_a_get_a';eauto];
do 3 eexists; splits; eauto.

eapply Hsl.
simpljoin.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x7 x6 He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto]; 
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* buffer_equiv *)
unfold buffer_equiv in *.
rewrite set_a_get_a';try intro;tryfalse.
simpljoin.
do 2 eexists; splits; eauto.
intros e0 Hb.
lets Hm: H3 Hb.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O curtid).
destruct Hm as (Hcap1 & Hcap2).
lets Heif: mq_buffer_eid_diff Hasrt Hb.
splits; eauto.
intros.
rewrite H in H4;inverts H4.
lets Hmqed : buffer_ecb Hb H1.
simpljoin.
rewrite H in H4;inverts H4.

split.
(*mq_ed_equiv*)
unfolds.
do 4 eexists; splits; eauto.
(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x1 t (x2, rdy, Vnull, false, x8)).
casetac x11 t He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H2 in H7; inverts H7.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x11 t He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.
(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x1 t (x2, rdy, Vnull, false, x8)).
casetac x11 t He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H2 in H7; inverts H7.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x11 t He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* cap_equiv *)
unfold cap_equiv in *.
rewrite set_a_get_a'; try intro; tryfalse.
simpljoin.
do 2 eexists; splits; eauto.

intros pr0 Hd.
lets Hm: H3 Hd.
l_rew21_inv1 (get O cspaceid).
destruct Hm as (Hcap1 & Hcap2).
splits; eauto.

intros idx Hdom.
lets Hs: Hcap2 Hdom.
destruct Hs as (Hs1 & Hs2).
splits.
splits; intros Hs;
unfold mq_ptr in *.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a' in Hs; try intro; tryfalse; auto.

intros.
eapply Hs2; eauto.
unfold mq_ptr in *; simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
do 8 eexists; splits; eauto.

(* client_data_equiv *)
unfold client_data_equiv in *.
simpljoin.
do 6 eexists; splits; eauto.

unfold local_envs_equiv in *.
intros.
eapply H3; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse.
match goal with H: Some _ = Some _ |- _ => inverts H end.

 l_rew21_inv1 (get O abstcblsid).
casetac t2 x6 He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse];
do 5 eexists; splits; eauto.
Qed. 

Lemma qpend_to_body_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qpend_to_body (v4 :: v0 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.
inverts Hspec; simpljoin.
destruct H8 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
match goal with H: _ :: _ :: nil = _ :: _ :: nil |- _ => inverts H end.

kvextH Hcur O0 curtid O. 
kvextH Hecb O0 absecblsid O. 
kvextH Htcb O0 abtcblsid O. 
assert (O'=set
           (set O abtcblsid
              (abstcblist (set x1 x3 (x2, rdy, Vnull, false, x11))))
           absecblsid
           (absecblist (set x4 x (absmsgq x6 x7 x8, remove_tid x3 x9)))).
eapply join_get_set_eq_2;eauto.

clear H0 H1 H3.
subst.

splits.
(*ctid_equiv*)
destruct Hctq as (t1 & t2 & Hct1 & Hct2 & Hpreq).
unfolds; intros.
exists t1 t2.
splits; eauto.
do 2 try rewrite set_a_get_a'; try intro; tryfalse.
eauto.

intros.
eapply Hpreq; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.

(*bufs_equiv*)
destruct Hbusq as (Hib & Hob).
unfolds in Hib; simpljoin.
unfolds in Hob; simpljoin.

unfolds; split;
unfolds;
intros;
do 2 eexists; split; eauto;
rewrite set_a_get_a'; try intro; tryfalse; eauto;
rewrite set_a_get_a'; try intro; tryfalse; eauto.

(*kernel_data_equiv*)
destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
unfolds; splits.

unfolds in Hkenlt; simpljoin.
unfolds.
{ 
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
intros.
splits.
splits; intros;
destruct H8 as (t1 & Htkid);
exists t1;
unfold task_prio_id in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a; eauto. 
l_rew21_inv1 (get O abtcblsid).
simpljoin.
l_rew21_inv1 (get O abtcblsid).
casetac x3 t1 He Hne;
subst;
do 5 eexists; splits; eauto;
[rewrite H2 in H9; inverts H9;
rewrite set_a_get_a; eauto |
rewrite set_a_get_a'; try intro; tryfalse; eauto].

rewrite set_a_get_a' in Htkid; try intro; tryfalse; eauto.
rewrite set_a_get_a in Htkid; eauto.
simpljoin.
match goal with H: Some _ = Some _ |- _ => inverts H end.
casetac x3 t1 He Hne.
subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
do 5 eexists; splits; eauto.
match goal with
   H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H; eauto end.
do 5 eexists; splits; eauto.

simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hmqid & Hptr).
unfolds in Hptr; simpljoin.
destruct H10 as [(Hn & Hn') | (p & He & Heq)]; tryfalse; subst.
inverts Heq.
l_rew21_inv1 (get O curtid).
intros.
casetac t t2 He Hne; subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
unfolds in Htpi; simpljoin.
do 3 l_rew21_inv1 (get O abtcblsid).
rewrite H11 in H2; inverts H2; tryfalse.
match goal with
   H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H; eauto end.
assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H7 in H10; inverts H10; eauto. }

(*kernel_mq_equiv*)
unfolds in Hkernlq;simpljoin.
{
unfolds.
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

intros.
simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hdom & Hptr).
casetac i0 i1 Heq Hneq.
subst.
eapply mqidx_diff_dom in H7; eauto; tryfalse.
splits.
splits; intros; auto.
l_rew21_inv1 (get O absmqattrid).

intros.
unfolds.
eapply H6 in H7; eauto.
simpljoin.
eapply H9 in H; eauto.
unfolds in Hptr; simpljoin.
destruct H12 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin. (*mq_equiv*)
do 8 eexists; splits; eauto.
destruct H13 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get O absecblsid).
rewrite H15 in H16; inverts H16.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H11 H8.

do 2 right.
exists x4.
rewrite set_a_get_a; eauto. 
exists (set x4 p (absmsgq x6 x7 x8, remove_tid x3 x9)).
exists x27.
rewrite set_a_get_a'; eauto.
do 4 eexists; splits; eauto.

(*mq_ed_equiv*)
unfolds.
unfolds in H17; simpljoin.
do 4 eexists; splits; eauto.

(* tidls_equiv_pws *)
unfolds.
unfold tidls_equiv in H12; simpljoin.
splits; eauto.
intros.
splits; intros; simpljoin.
exists x26.
splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists.
exists (set x1 x3 (x2, rdy, Vnull, false, x11)).
casetac x26 x3 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H2 in H19; inverts H19.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x26 x3 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto ];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(*tidls_equiv_ws*)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x1 x3 (x2, rdy, Vnull, false, x11)).
casetac x3 x He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H2 in H16; inverts H16.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x3 x He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto. }

(*ports_equiv*)
unfold ports_equiv in *; simpljoin.
l_rew21_inv1 (get O osdomainportid).
l_rew21_inv1 (get O absecblsid).
rewrite set_a_get_a; eauto.
do 2 try rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H7 in H4; inverts H4.
rewrite set_a_get_a'; eauto. 

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

intros.
casetac a x Heq Hneq;
subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

(* tidls_equiv *)
l_rew21_inv1 (get O absecblsid).
eapply H8 in H9; eauto.
unfold tidls_equiv in *.
destruct H9 as (Hlen & Hsl).
splits; eauto.
intros pr0.
splits; intros Hg.
eapply Hsl in Hg; eauto.
destruct Hg as (tk & Hin & Htkid).
exists tk.
splits; eauto.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a' ; try intro; tryfalse.
rewrite set_a_get_a; eauto.
 l_rew21_inv1 (get O abstcblsid).
casetac x3 tk He Hne; subst;
eexists;
[ exists (set x1 tk (x2, rdy, Vnull, false, x11));
rewrite set_a_get_a; eauto;
rewrite H2 in H10; inverts H10 |
exists (set x1 x3 (x2, rdy, Vnull, false, x11));
rewrite set_a_get_a';eauto];
do 3 eexists; splits; eauto.

eapply Hsl.
simpljoin.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x3 x4 He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto]; 
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* buffer_equiv *)
unfold buffer_equiv in *.
rewrite set_a_get_a.
simpljoin.
do 2 eexists; splits; eauto.
intros e0 Hb.
lets Hm: H3 Hb.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absecblsid).
destruct Hm as (Hcap1 & Hcap2).
lets Heif: mq_buffer_eid_diff Hasrt Hb.
rewrite set_a_get_a';eauto.
splits; eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H in H1;inverts H1.
lets Hmqed : buffer_ecb Hb Hecb.
simpljoin.
rewrite H in H1;inverts H1.

split.
(*mq_ed_equiv*)
unfolds.
do 4 eexists; splits; eauto.
(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x1 x3 (x2, rdy, Vnull, false, x11)).
casetac x3 x14 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H2 in H8; inverts H8.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x3 x14 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.
(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists; splits; eauto.
eexists.
exists (set x1 x3 (x2, rdy, Vnull, false, x11)).
casetac x3 x14 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H2 in H8; inverts H8.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x3 x14 He Hne;
subst;
l_rew21_inv1 (get O abtcblsid);
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto];
eexists; splits; eauto;
do 5 eexists; splits; eauto.

(* cap_equiv *)
unfold cap_equiv in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a'; try intro; tryfalse.
simpljoin.
do 2 eexists; splits; eauto.

intros pr0 Hd.
lets Hm: H3 Hd.
l_rew21_inv1 (get O cspaceid).
destruct Hm as (Hcap1 & Hcap2).
splits; eauto.

intros idx Hdom.
lets Hs: Hcap2 Hdom.
destruct Hs as (Hs1 & Hs2).
splits.
splits; intros Hs;
unfold mq_ptr in *.
do 2 try rewrite set_a_get_a'; try intro; tryfalse.
auto.
do 2 try rewrite set_a_get_a' in Hs; try intro; tryfalse.
auto.

intros.
eapply Hs2; eauto.
unfold mq_ptr in *; simpljoin.
do 2 match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
do 8 eexists; splits; eauto.

(* client_data_equiv *)
unfold client_data_equiv in *.
simpljoin.
do 6 eexists; splits; eauto.

unfold local_envs_equiv in *.
intros.
eapply H3; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse.
match goal with H: Some _ = Some _ |- _ => inverts H end.

 l_rew21_inv1 (get O abstcblsid).
casetac t2 x3 He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse];
do 5 eexists; splits; eauto.
Qed. 

Lemma qacc_succ_body_equiv_tskd_preserve:
forall i pr i0 v4 O v0 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qacc_succ_body (v4 :: v0 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.
inverts Hspec; simpljoin.
destruct H4 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
match goal with H: _ :: _ :: nil = _ :: _ :: nil |- _ => inverts H end.

kvextH Hecb O0 absecblsid O.
assert (O'= set O absecblsid (absecblist (set x1 x (absmsgq x3 x4 x5, x6)))).
eapply join_get_set_eq;eauto.
subst.

splits.
(*ctid_equiv*)
unfolds; intros.
do 2 eexists. splits; eauto.
rewrite set_a_get_a'; eauto . intro; tryfalse.

intros.
eapply prio_unique_set_ntls; eauto.
intro; tryfalse.

(*bufs_equiv*)
destruct Hbusq as (Hib & Hob).
unfolds in Hib; simpljoin.
unfolds in Hob; simpljoin.

unfolds; split;
unfolds;
intros;
do 2 eexists; split; eauto;
rewrite set_a_get_a'; try intro; tryfalse; eauto.

(*kernel_data_equiv*)
destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
unfolds; splits.

(*kernel_task_equiv*)
unfolds in Hkenlt; simpljoin.
unfolds.
{ 
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
intros.
splits.
splits; intros;
[ eapply task_prio_id_set_ntls_eq; eauto |
eapply task_prio_id_set_ntls_eq'; eauto];
intro; tryfalse.
l_rew21_inv1 (get O abtcblsid).
intros. 
assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H7 in H; inverts H; eauto. }

(*kernel_mq_equiv*)
unfolds in Hkernlq;simpljoin.
{
unfolds.
do 2 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

intros.
simpl in Hasrt.
unfolds in Hasrt.
destruct Hasrt as (Hdom & Hptr).
casetac i0 i1 Heq Hneq.
subst.
eapply mqidx_diff_dom in H6; eauto; tryfalse.
splits.
splits; intros; auto.
(* l_rew21_inv1 (get Ox absecblsid). *)
l_rew21_inv1 (get O absmqattrid).

intros.
unfolds.
eapply H5 in H6; eauto.
simpljoin.
eapply H8 in H; eauto.
unfolds in Hptr; simpljoin.
destruct H11 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin.
do 8 eexists; splits; eauto.
destruct H12 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get O absecblsid).
rewrite H14 in H15; inverts H15.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H10 H7.

do 2 right.
exists x1.
rewrite set_a_get_a; eauto. 
exists (set x1 p (absmsgq x3 x4 x5, x6)).
eexists.
rewrite set_a_get_a'; eauto.
do 4 eexists; splits; eauto.

(*mq_ed_equiv*)
unfolds.
unfolds in H16; simpljoin.
do 4 eexists; splits; eauto.

(* tidls_equiv_pws *)
unfolds.
unfold tidls_equiv in H11; simpljoin.
splits; eauto.
intros.
splits; intros; simpljoin.
eexists; splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 5 eexists; eauto.

unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
eexists; splits; eauto;
do 5 eexists; eauto.

(*tidls_equiv_ws*)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin;
[rewrite set_a_get_a'; try intro; tryfalse; eauto | 
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse ];
eexists; splits; eauto;
do 5 eexists; eauto. }

(*ports_equiv*)
unfold ports_equiv in *; simpljoin.
l_rew21_inv1 (get O osdomainportid).
l_rew21_inv1 (get O absecblsid).
rewrite set_a_get_a; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H6 in H3; inverts H3.
rewrite set_a_get_a'; eauto. 

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto;
match goal with H: Some _ = Some _ |- _ => inverts H end; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.

intros.
casetac a x Heq Hneq;
subst.
rewrite H6 in H3; inverts H3.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

(* tidls_equiv *)
l_rew21_inv1 (get O absecblsid).
eapply H7 in H8; eauto.
unfold tidls_equiv in *.
destruct H8 as (Hlen & Hsl).
splits; eauto.
intros pr0.
splits; intros Hg.
eapply Hsl in Hg; eauto.
destruct Hg as (tk & Hin & Htkid).
exists tk.
splits; eauto.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a' ; try intro; tryfalse.
do 5 eexists; splits; eauto.

eapply Hsl.
simpljoin.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
eexists; splits; eauto.
do 5 eexists; splits; eauto.

(* buffer_equiv *)
unfold buffer_equiv in *.
rewrite set_a_get_a.
simpljoin.
do 2 eexists; splits; eauto.
intros e0 Hb.
lets Hm: H4 Hb.
l_rew21_inv1 (get O absecblsid).
l_rew21_inv1 (get O absecblsid).
destruct Hm as (Hcap1 & Hcap2).
lets Heif: mq_buffer_eid_diff Hasrt Hb.
rewrite set_a_get_a';eauto.
splits; eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H in H1;inverts H1.
lets Hmqed : buffer_ecb Hb Hecb.
simpljoin.
rewrite H in H1;inverts H1.

split.
(*mq_ed_equiv*)
unfolds.
do 4 eexists; splits; eauto.

(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin;
[rewrite set_a_get_a'; try intro; tryfalse; eauto | 
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse ];
eexists; splits; eauto;
do 5 eexists; eauto.

(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin;
[rewrite set_a_get_a'; try intro; tryfalse; eauto | 
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse ];
eexists; splits; eauto;
do 5 eexists; eauto.

(* cap_equiv *)
unfold cap_equiv in *.
rewrite set_a_get_a'; try intro; tryfalse.
simpljoin.
do 2 eexists; splits; eauto.

intros pr0 Hd.
lets Hm: H4 Hd.
l_rew21_inv1 (get O cspaceid).
destruct Hm as (Hcap1 & Hcap2).
splits; eauto.

intros idx Hdom.
lets Hs: Hcap2 Hdom.
destruct Hs as (Hs1 & Hs2).
splits.
splits; intros Hs;
unfold mq_ptr in *.
rewrite set_a_get_a'; try intro; tryfalse.
auto.
rewrite set_a_get_a' in Hs; try intro; tryfalse.
auto.

intros.
eapply Hs2; eauto.
unfold mq_ptr in *.
rewrite set_a_get_a' in H5; try intro; tryfalse.
auto.

(* client_data_equiv *)
unfold client_data_equiv in *.
simpljoin.
do 6 eexists; splits; eauto.

unfold local_envs_equiv in *.
intros.
eapply H4; eauto.
unfold task_prio_id in *.
rewrite set_a_get_a' in H1; try intro; tryfalse; auto.
Qed.

Lemma mqrecv_nabt_spec_step_data_equiv_tskd_preserve:
forall O cd n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
(* good_client_code pc -> *)
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)->
task_prio_id O pr t ->
get O curtid = Some (oscurt t)->
get T t = Some (curs (hapi_code cd),(ke, ks))->
mqreceive vl <> ABORT ->
nth_error (get_all_succs (mqreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O'->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgtc Hrec Hnflo Htpi Hctid Hgett Hnabt Hnth Hstep.
introv Hi_neq HO_neq.
lets Hasrt: rch_hasrt_sat Hrec Hgett Htpi.
remember vl as recv_vl.
do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
try destruct v; simpl in Hnabt; tryfalse;
try destruct v1; simpl in Hnabt; tryfalse;
try destruct v3; simpl in Hnabt; tryfalse;
try destruct v5; simpl in Hnabt; tryfalse;
try destruct v7; simpl in Hnabt; tryfalse.
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
lets Hgdcd: Hgtc Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets Hstep1: Hstep.
protect Hstep1.
protect Hgde'.
assert(HO:data_equiv_tskd i cst' cst' O O).
eapply data_equiv_tskd_same_preserve; eauto.
unfolds in HO.
destruct HO as (Hctq & Hbusq & Hkenl & Hdata).
destruct n; [ my_succs_solver_same_absdata | idtac].
(*qpend_get_no_pwl_succ_body*)
simpl in Hasrt.
eapply qpend_get_no_pwl_succ_data_equiv_tskd_preserve; eauto.
solve_endabt.

(*qpend_get_ex_pwl_before_sched_body*)
eapply qpend_get_ex_pwl_before_sched_data_equiv_tskd_preserve; eauto.
solve_endabt.

(* qpend_block_body *)
eapply qpend_block_body_data_equiv_tskd_preserve; eauto.
solve_endabt.

(* n = 10 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 11 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 12 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 13 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 14 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* qpend_block_get_body *)
eapply qpend_block_get_data_equiv_tskd_preserve; eauto.

(*qpend_to_body_data*)
eapply qpend_to_body_data_equiv_tskd_preserve; eauto.
solve_endabt.

solve_endabt.

(* n = 15 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 16 *)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* qacc_succ_body *)
eapply qacc_succ_body_equiv_tskd_preserve; eauto.
solve_endabt.

(* n = 17 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 18 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
re_err_contra n; try my_succs_solver_same_absdata.
tryfalse.
tryfalse.
Qed.


