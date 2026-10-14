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
Require Import if_common_lemmas.
Require Import mqsend_cproof.
(* Require Import mqsend_codeequiv_integrity_proof. *)
(* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\ *)

Lemma qtmpost_ovf_block_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 i4 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qtimedpost_ovf_block_body (v4 :: v0 :: Vint32 i4 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof.
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.

inverts Hspec; simpljoin.
match goal with H: Some _ = Some _ |- _ => inverts H end.
match goal with H: _ :: _ :: _ :: nil = _ :: _ :: _ :: nil |- _ => inverts H end.

assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.
assert ( get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.
assert ( get O curtid = Some (oscurt x6)) as Hct.
eapply join_get_get_l;eauto.

assert (O'=set
           (set O abtcblsid
              (abstcblist
                 (set x9 x6 (x2, wait (os_stat_postq x) None, x0, x1, x15))))
           absecblsid
           (absecblist (set x7 x (absmsgq x11 x12 (x6 :: x13), x14)))).
eapply join_get_set_eq_2;eauto.
clear H0 H1 H2.
remember O as Ox.
clear HeqOx.
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
l_rew21_inv1 (get Ox abtcblsid).
simpljoin.
l_rew21_inv1 (get Ox abtcblsid).
casetac x6 t1 He Hne;
subst;
do 5 eexists; splits; eauto;
[rewrite H6 in H9; inverts H9;
rewrite set_a_get_a; eauto |
rewrite set_a_get_a'; try intro; tryfalse; eauto].

rewrite set_a_get_a' in Htkid; try intro; tryfalse; eauto.
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
destruct H10 as [(Hn & Hn') | (p & He & Heq)]; tryfalse; subst.
inverts Heq.
l_rew21_inv1 (get Ox curtid).
intros.
casetac t t2 He Hne; subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
unfolds in Htpi; simpljoin.
do 3 l_rew21_inv1 (get Ox abtcblsid).
rewrite H11 in H6; inverts H6; tryfalse.
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
l_rew21_inv1 (get Ox absmqattrid).

intros.
unfolds.
eapply H5 in H; eauto.
simpljoin.
eapply H5 in H7; eauto.
unfolds in Hptr; simpljoin.
destruct H12 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin. (*mq_equiv*)
do 8 eexists; splits; eauto.
destruct H13 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get Ox absecblsid).
rewrite H15 in H16; inverts H16.
l_rew21_inv1 (get Ox absecblsid).
l_rew21_inv1 (get Ox absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H11 H8.

do 2 right.
exists x7.
rewrite set_a_get_a; eauto. 
exists (set x7 p (absmsgq x11 x12 (x6 :: x13), x14)).
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
exists (set x9 x6 (x2, wait (os_stat_postq p) None, x0, x1, x15)).
casetac x29 x6 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H6 in H19; inverts H19.
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

casetac x29 x6 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
exists (set x9 x6 (x2, wait (os_stat_postq p) None, x0, x1, x15)).
casetac x6 x He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H6 in H16; inverts H16.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x6 x He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
l_rew21_inv1 (get Ox osdomainportid).
l_rew21_inv1 (get Ox absecblsid).
rewrite set_a_get_a; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H7 in H3; inverts H3.
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
l_rew21_inv1 (get Ox absecblsid).
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
 l_rew21_inv1 (get Ox abstcblsid).
casetac x6 tk He Hne; subst;
eexists;
[ exists (set x9 tk (x2, wait (os_stat_postq x) None, x0, x1, x15));
rewrite set_a_get_a; eauto;
rewrite H6 in H10; inverts H10 |
exists (set x9 x6 (x2, wait (os_stat_postq x) None, x0, x1, x15));
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

casetac x6 x7 He Hne; subst;
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
lets Hm: H2 Hb.
l_rew21_inv1 (get Ox absecblsid).
l_rew21_inv1 (get Ox absecblsid).
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
exists (set x9 x6 (x2, wait (os_stat_postq x) None, x0, x1, x15)).
casetac x6 x17 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H6 in H8; inverts H8.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x6 x17 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
exists (set x9 x6 (x2, wait (os_stat_postq x) None, x0, x1, x15)).
casetac x6 x17 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H6 in H8; inverts H8.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x6 x17 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
lets Hm: H2 Hd.
l_rew21_inv1 (get Ox cspaceid).
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
eapply H2; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse.
match goal with H: Some _ = Some _ |- _ => inverts H end.

 l_rew21_inv1 (get Ox abstcblsid).
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

Lemma qtmpost_timeout_err_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 i4 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qtimedpost_timeout_err_body (v4 :: v0 :: Vint32 i4 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof.
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.

inverts Hspec; simpljoin.
destruct H9 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
match goal with H: _ :: _ :: _ :: nil = _ :: _ :: _ :: nil |- _ => inverts H end.

assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.
assert ( get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert ( get O curtid = Some (oscurt x2)) as Hct.
eapply join_get_get_l;eauto.

assert (O'=set
           (set O abtcblsid
              (abstcblist (set x3 x2 (x4, rdy, Vnull, false, x13))))
           absecblsid
           (absecblist (set x7 x (absmsgq x11 x10 (remove_tid x2 x9), x12)))).
eapply join_get_set_eq_2;eauto.
clear H4 H1 H2.
remember O as Ox.
clear HeqOx.
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
destruct H9 as (t1 & Htkid);
exists t1;
unfold task_prio_id in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a; eauto. 
l_rew21_inv1 (get Ox abtcblsid).
simpljoin.
l_rew21_inv1 (get Ox abtcblsid).
casetac x2 t1 He Hne;
subst;
do 5 eexists; splits; eauto;
[rewrite H3 in H10; inverts H10;
rewrite set_a_get_a; eauto |
rewrite set_a_get_a'; try intro; tryfalse; eauto].

rewrite set_a_get_a' in Htkid; try intro; tryfalse; eauto.
rewrite set_a_get_a in Htkid; eauto.
simpljoin.
match goal with H: Some _ = Some _ |- _ => inverts H end.
casetac x2 t1 He Hne.
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
destruct H11 as [(Hn & Hn') | (p & He & Heq)]; tryfalse; subst.
inverts Heq.
l_rew21_inv1 (get Ox curtid).
intros.
casetac t t2 He Hne; subst.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end.
match goal with H: Some _ = Some _ |- _ => inverts H end.
unfolds in Htpi; simpljoin.
do 3 l_rew21_inv1 (get Ox abtcblsid).
rewrite H12 in H3; inverts H3; tryfalse.
match goal with
   H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H; eauto end.
assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H8 in H11; inverts H11; eauto. }

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
eapply mqidx_diff_dom in H8; eauto; tryfalse.
splits.
splits; intros; auto.
l_rew21_inv1 (get Ox absmqattrid).

intros.
unfolds.
eapply H7 in H; eauto.
simpljoin.
(* eapply H7 in H; eauto. *)
unfolds in Hptr; simpljoin.
destruct H12 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin. (*mq_equiv*)
do 8 eexists; splits; eauto.
destruct H13 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get Ox absecblsid).
rewrite H15 in H16; inverts H16.
l_rew21_inv1 (get Ox absecblsid).
l_rew21_inv1 (get Ox absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H11 H9.

do 2 right.
exists x7.
rewrite set_a_get_a; eauto. 
exists (set x7 p (absmsgq x11 x10 (remove_tid x2 x9), x12)).
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
exists (set x3 x2 (x4, rdy, Vnull, false, x13)).
casetac x28 x2 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H3 in H19; inverts H19.
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

casetac x28 x2 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
exists (set x3 x2 (x4, rdy, Vnull, false, x13)).
casetac x2 x He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H3 in H16; inverts H16.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x2 x He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
l_rew21_inv1 (get Ox osdomainportid).
l_rew21_inv1 (get Ox absecblsid).
rewrite set_a_get_a; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H8 in H5; inverts H5.
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
l_rew21_inv1 (get Ox absecblsid).
eapply H9 in H10; eauto.
unfold tidls_equiv in *.
destruct H10 as (Hlen & Hsl).
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
 l_rew21_inv1 (get Ox abstcblsid).
casetac x2 tk He Hne; subst;
eexists;
[ exists (set x3 tk (x4, rdy, Vnull, false, x13));
rewrite set_a_get_a; eauto;
rewrite H3 in H11; inverts H11 |
exists (set x3 x2 (x4, rdy, Vnull, false, x13));
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

casetac x2 x7 He Hne; subst;
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
lets Hm: H4 Hb.
l_rew21_inv1 (get Ox absecblsid).
l_rew21_inv1 (get Ox absecblsid).
destruct Hm as (Hcap1 & Hcap2).
lets Heif: mq_buffer_eid_diff Hasrt Hb.
rewrite set_a_get_a';eauto.
splits; eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H in H2;inverts H2.
lets Hmqed : buffer_ecb Hb Hecb.
simpljoin.
rewrite H in H2;inverts H2.
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
exists (set x3 x2 (x4, rdy, Vnull, false, x13)).
casetac x2 x16 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H3 in H9; inverts H9.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x2 x16 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
exists (set x3 x2 (x4, rdy, Vnull, false, x13)).
casetac x2 x16 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H3 in H9; inverts H9.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x2 x16 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
lets Hm: H4 Hd.
l_rew21_inv1 (get Ox cspaceid).
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
eapply H4; eauto.
unfold task_prio_id in *.
simpljoin.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse.
match goal with H: Some _ = Some _ |- _ => inverts H end.

 l_rew21_inv1 (get Ox abstcblsid).
casetac t2 x2 He Hne; subst;
[ match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; try intro; tryfalse;
match goal with H: Some _ = Some _ |- _ => inverts H end |
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse];
do 5 eexists; splits; eauto.
Qed. 


Lemma qpost_nowt_succ_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 i4 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qpost_nowt_succ_body (v4 :: v0 :: Vint32 i4 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof.
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.

inverts Hspec; simpljoin.
destruct H5 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid
           (absecblist (set x2 x (absmsgq (x4 ++ x0 :: nil) x3 x5, nil)))).
eapply join_get_set_eq;eauto.
clear H2.
remember O as Ox.
clear HeqOx.
subst.
match goal with H: _ :: _ :: _ :: nil = _ :: _ :: _ :: nil |- _ => inverts H end.
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
l_rew21_inv1 (get Ox abtcblsid).
intros. 
assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H7 in H; inverts H; eauto.
}

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
l_rew21_inv1 (get Ox absmqattrid).

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
l_rew21_inv1 (get Ox absecblsid).
rewrite H14 in H15; inverts H15.
l_rew21_inv1 (get Ox absecblsid).
l_rew21_inv1 (get Ox absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H10 H7.

do 2 right.
exists x2.
rewrite set_a_get_a; eauto. 
exists (set x2 p (absmsgq (x4 ++ x0 :: nil) x3 x5, nil)).
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
l_rew21_inv1 (get Ox osdomainportid).
l_rew21_inv1 (get Ox absecblsid).
rewrite set_a_get_a; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H3 in H6; inverts H6.
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
rewrite H3 in H6; inverts H6.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; eauto.

(* tidls_equiv *)
l_rew21_inv1 (get Ox absecblsid).
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
lets Hm: H2 Hb.
l_rew21_inv1 (get Ox absecblsid).
l_rew21_inv1 (get Ox absecblsid).
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
eexists; splits; eauto.
do 5 eexists.
split;eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
eexists; splits; eauto.
do 5 eexists; splits; eauto.

(* tidls_equiv *)
unfold tidls_equiv in *; simpljoin.
splits; eauto.
intros.
splits; intros; unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
eexists; splits; eauto.
do 5 eexists.
split;eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
eexists; splits; eauto.
do 5 eexists; splits; eauto.

(* cap_equiv *)
unfold cap_equiv in *.
rewrite set_a_get_a'; try intro; tryfalse.
simpljoin.
do 2 eexists; splits; eauto.

intros pr0 Hd.
lets Hm: H2 Hd.
l_rew21_inv1 (get Ox cspaceid).
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
eapply H2; eauto.
unfold task_prio_id in *.
rewrite set_a_get_a' in H1; try intro; tryfalse; auto.
Qed. 

Lemma qpost_exwt_succ_data_equiv_tskd_preserve:
forall i pr i0 v4 O v0 i4 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
mqdes_dom_qptr i0 v4 O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
qpost_exwt_succ_body (v4 :: v0 :: Vint32 i4 :: nil) O0 act (v, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof.
introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
introv Hj1 Hj2.

inverts Hspec; simpljoin.
destruct H9 as [(He & Hsm) | (Hne & Hnone)]; tryfalse.
inverts Hsm.
match goal with H: _ :: _ :: _ :: nil = _ :: _ :: _ :: nil |- _ => inverts H end.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.
assert ( get O abtcblsid = Some (abstcblist x7)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'=set
           (set O abtcblsid (abstcblist (set x7 x6 (x11, rdy, x0, x10, x15))))
           absecblsid
           (absecblist (set x2 x (absmsgq nil x13 x14, remove_tid x6 x4)))).
eapply join_get_set_eq_2;eauto.
clear H3 H2.
remember O as Ox.
clear HeqOx.
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
rewrite set_a_get_a' in H1; try intro; tryfalse.

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
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
intros.
splits.
splits; intros;
destruct H9 as (t1 & Htkid);
exists t1;
unfold task_prio_id in *.
rewrite set_a_get_a'; try intro; tryfalse.
rewrite set_a_get_a; eauto. 
l_rew21_inv1 (get Ox abtcblsid).
simpljoin.
l_rew21_inv1 (get Ox abtcblsid).
casetac x6 t1 He Hne;
subst;
do 5 eexists; splits; eauto;
[rewrite H6 in H10; inverts H10;
rewrite set_a_get_a; eauto |
rewrite set_a_get_a'; try intro; tryfalse; eauto].

rewrite set_a_get_a' in Htkid; try intro; tryfalse; eauto.
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
destruct H11 as [(Hn & Hn') | (p & He & Heq)]; tryfalse; subst.
inverts Heq.
unfolds in H5; simpljoin. (* GetHWait *)
lets Hf:mq_part_consistent H9 Hmqid H10 Hecb H4; eauto.
specialize (Hf x6).
destruct Hf; eauto.
rewrite H8 in H6; inverts H6.
destruct H12 as (Htkid' & Heq').
unfolds in Htkid'; simpljoin.
l_rew21_inv1 (get Ox abtcblsid).
rewrite H8 in H12; inverts H12.

intros. 
do 2 l_rew21_inv1 (get Ox abtcblsid).
casetac x6 t2 He Hne;
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
rewrite H12 in H13; inverts H13; eauto.
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
eapply mqidx_diff_dom in H8; eauto; tryfalse.
splits.
splits; intros; auto.
l_rew21_inv1 (get Ox absmqattrid).

intros.
unfolds.
eapply H7 in H8; eauto.
simpljoin.
eapply H10 in H; eauto.
unfolds in Hptr; simpljoin.
destruct H13 as [(Hnul & Hf)| (p & Hei & Ht)]; tryfalse; inverts Ht.
subst.
unfolds in H; simpljoin. (*mq_equiv*)
do 8 eexists; splits; eauto.
destruct H14 as [Hnull | [ Hhold | Heid]]; simpljoin.
left; eauto.
right; left; eauto.
l_rew21_inv1 (get Ox absecblsid).
rewrite H16 in H17; inverts H17.
l_rew21_inv1 (get Ox absecblsid).
l_rew21_inv1 (get Ox absmqattrid).

lets Hm: mq_ecb_ref_distinct Hneq H12 H9.

do 2 right.
exists x2.
rewrite set_a_get_a; eauto. 
exists (set x2 p (absmsgq nil x13 x14, remove_tid x6 x4)).
exists x30.
rewrite set_a_get_a'; eauto.
do 4 eexists; splits; eauto.

(*mq_ed_equiv*)
unfolds.
unfolds in H18; simpljoin.
do 4 eexists; splits; eauto.

(* tidls_equiv_pws *)
unfolds.
unfold tidls_equiv in H13; simpljoin.
splits; eauto.
intros.
splits; intros; simpljoin.
exists x29.
splits; eauto;
unfold task_prio_id in *; simpljoin.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a; eauto.
eexists.
exists (set x7 x6 (x11, rdy, x0, x10, x15)).
casetac x29 x6 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H6 in H20; inverts H20.
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

casetac x29 x6 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
exists (set x7 x6 (x11, rdy, x0, x10, x15)).
casetac x6 x He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H6 in H17; inverts H17.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x6 x He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
l_rew21_inv1 (get Ox osdomainportid).
l_rew21_inv1 (get Ox absecblsid).
rewrite set_a_get_a; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
do 4 eexists; splits; eauto.

intros.
splits; eauto.
splits; intros; simpljoin;
casetac a x Heq Hneq;
subst.
rewrite H4 in H8; inverts H8.
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
l_rew21_inv1 (get Ox absecblsid).
eapply H9 in H10; eauto.
unfold tidls_equiv in *.
destruct H10 as (Hlen & Hsl).
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
 l_rew21_inv1 (get Ox abstcblsid).
casetac x6 tk He Hne; subst;
eexists;
[ exists (set x7 tk (x11, rdy, x0, x10, x15));
rewrite set_a_get_a; eauto;
rewrite H6 in H11; inverts H11 |
exists (set x7 x6 (x11, rdy, x0, x10, x15));
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

casetac x6 x2 He Hne; subst;
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
l_rew21_inv1 (get Ox absecblsid).
l_rew21_inv1 (get Ox absecblsid).
destruct Hm as (Hcap1 & Hcap2).
lets Heif: mq_buffer_eid_diff Hasrt Hb.
rewrite set_a_get_a';eauto.
splits; eauto.
rewrite set_a_get_a';eauto.
intros.
rewrite H in H2;inverts H2.
lets Hmqed : buffer_ecb Hb Hecb.
simpljoin.
rewrite H in H2;inverts H2.
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
exists (set x7 x6 (x11, rdy, x0, x10, x15)).
casetac x6 x17 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H6 in H9; inverts H9.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x6 x17 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
exists (set x7 x6 (x11, rdy, x0, x10, x15)).
casetac x6 x17 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid).
rewrite set_a_get_a; eauto.
rewrite H6 in H9; inverts H9.
do 3 eexists; splits; eauto.
rewrite set_a_get_a'; try intro; tryfalse; eauto.

match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse; eauto.
match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a in H end; eauto.
match goal with H: Some _ = Some _ |- _ => inverts H end.

casetac x6 x17 He Hne;
subst;
l_rew21_inv1 (get Ox abtcblsid);
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
l_rew21_inv1 (get Ox cspaceid).
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

 l_rew21_inv1 (get Ox abstcblsid).
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

Lemma mqsend_nabt_spec_step_data_equiv_tskd_preserve :
forall O cd  n vl sd cd' O' act ke ks t T i pr pc cst',
good_task_code T ->
(* good_client_code pc -> *)
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~ flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
mqsend vl <> ABORT -> 
nth_error (get_all_succs (mqsend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O' ->
data_equiv_tskd i cst' cst' O O'.
Proof. 
introv Hgdt Hrch Hflw Htpi Hctid Hgett Hnabt Hnth.
introv Hstep Hi_neq HO_neq.
lets Hasrt: rch_hasrt_sat Hrch Hgett Htpi.
lets Hss: Hnth.
(* eapply mqsend_nabt_spec_step_code_equiv_tskd'_preserve in Hss; eauto. *)
remember vl as recv_vl.
do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
try destruct v; simpl in Hnabt; tryfalse;
try destruct v1; simpl in Hnabt; tryfalse;
try destruct v3; simpl in Hnabt; tryfalse;
try destruct v5; simpl in Hnabt; tryfalse;
try destruct v6; simpl in Hnabt; tryfalse.
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
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 10 *)
lets Hgdcd: Hgdt Hgett.
unfolds in Hgdcd. simpl in Hgdcd.
destruct Hgdcd as (Hgde' & Hgdks').
lets H': Hstep.
protect H'.
protect Hgde'.
assert(HO:data_equiv_tskd i cst' cst' O O).
eapply data_equiv_tskd_same_preserve; eauto.
unfolds in HO.
destruct HO as (Hctq & Hbusq & Hkenl & Hdata).
destruct n; [ my_succs_solver_same_absdata | idtac].

(*qpost_nowt_succ_body*)
eapply qpost_nowt_succ_data_equiv_tskd_preserve; eauto.

(* qtimedpost_exwt_succ_body *)
eapply qpost_exwt_succ_data_equiv_tskd_preserve; eauto.
solve_endabt.

(* qtimedpost_ovf_block_body *)
eapply qtmpost_ovf_block_data_equiv_tskd_preserve; eauto.
solve_endabt.

(* qpost_nowt_succ_body *)
solve_endabt.

(*n=11*)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 12 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 13 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 14 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(*n=15*)
destruct n; [ my_succs_solver_same_absdata | idtac].

(*qtimedpost_timeout_err_body*)
eapply qtmpost_timeout_err_data_equiv_tskd_preserve; eauto.
solve_endabt.

(*n=16*)
destruct n; [ my_succs_solver_same_absdata | idtac].

(* qpost_nowt_succ_body *)
eapply qpost_nowt_succ_data_equiv_tskd_preserve; eauto.
solve_endabt.

(* qpost_exwt_succ_body *)
eapply qpost_exwt_succ_data_equiv_tskd_preserve; eauto.
solve_endabt.

(* n = 17 *) 
destruct n; [ my_succs_solver_same_absdata | idtac]. 
(* n = 18 *)
destruct n; [ my_succs_solver_same_absdata | idtac].
(* n = 19 *) 
destruct n; [ my_succs_solver_same_absdata | idtac]. 
simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse.
Qed.


