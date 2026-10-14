Require Import init_and_inv_PIF.
(* Require Import oscorrectness.  *)
Require Import PIF_sys.
(* Require Import PIF_succs. *)
Require Import PIF_spec.
Require Import PIF_os_mutex_cap.
Require Import PIF_language.
Require Import PIF_assertion.
Require Import PIF_Modules.
(* Require Import oscorrectness. *)
Require Import List.
Require Import PIF_opsem.
Require Import Maps.
Require Import PIF_memory.
Tactic Notation "unfold1" constr (x) :=
  unfold x; fold x.
Tactic Notation "unfold1" constr (x) "in" hyp (Hp) :=
  unfold x in Hp; fold x in Hp.
Tactic Notation "unfold1" constr (x) "in" "*" :=
  unfold x in *; fold x in *.

Ltac mytac :=
  heat; jeauto2.

(* init->inv *)
Theorem Init_no_abort_Prop:
  forall client_code T cst O,
    INIT T client_code cst O ->
    good_client_code client_code ->
    no_abort T.
Proof.
  intros.
  unfolds.
  intros. unfolds in H0.
  unfolds in H.
  destruct H as (inittsk & initst).
  unfolds in inittsk.
  destruct inittsk as (eq & Htsk).
  eapply Htsk in H1; eauto.
  mytac. inverts H.
  eapply H0 in H1.  destruct x; intro; tryfalse. 
Qed.

Theorem Init_Invprop_Prop:
  forall client_code T cst O,
    INIT T client_code cst O ->
    good_client_code client_code ->
    INV_PROP client_code O T.
Proof.
  intros.
  unfolds.
(*   lets Habt: Init_no_abort_Prop H H0. *)
  splits; eauto.
  eapply Init_no_abort_Prop; eauto. 
  destruct H as (Htask & (tls' & ptbl & ecb & muxinfo & Hst)).
  destruct Hst as (Htcb & Hptbl & Hg).
  unfolds in Htask.
  splits; auto.
  unfolds; intros.
  rewrite ecb in H.
  inverts H.
  mytac.
  
  inversion H11. mytac. unfolds in H13.
  mytac.
  rewrite EcbMod.map_emp_get in H14.
  inverts H14.
  unfolds in H13.
  mytac.
  rewrite EcbMod.map_emp_get in H19.
  inverts H19.
  
  unfolds; intros.
  rewrite ecb in H. inverts H.
  splits; simpl; unfolds; auto.
  splits; intros; auto.
  unfolds.
  introv Hs.
  unfolds in Hs.
  destruct Hs as (qid & p_q & ow & wl & Hn & Hin).
  rewrite EcbMod.map_emp_get in Hn.
  inverts Hn.

  unfolds.
(*   destruct Hg as (Hg & Hdup).  *)
  specialize (Hg t).
  rewrite H1 in Htcb.
  inverts Htcb.
  destruct Hg as (p' & msg & sus' & Hg).
  rewrite Hg in H.
  inverts H.
  unfolds in H.
  do 4 destruct H.
  rewrite EcbMod.map_emp_get in H.
  inverts H.

  intros.
  rewrite EcbMod.map_emp_get in H4. inverts H4.

  intros.
  rewrite H1 in Htcb.
  inverts Htcb.
(*   destruct Hg as (Hg & Hdup). *)
  specialize (Hg t).
  destruct Hg as (p' & mag & sus' & Hg).
  rewrite Hg in H. inverts H.
  left; auto.

  intros.
  rewrite H1 in Htcb.
  inverts Htcb.
(*   destruct Hg as (Hg & Hdup). *)
  specialize (Hg t).
  destruct Hg as (p' & mag & sus' & Hg).
  rewrite Hg in H. inverts H.

  intros.
  unfolds in H4.
  destruct H4. rewrite H; auto. introv Hf; tryfalse.
  destruct H4 as (qid & Hecb). unfolds in Hecb.
  destruct Hecb as (p_q & ow & Hecb).
  rewrite EcbMod.map_emp_get in Hecb. inverts Hecb.
  destruct H4 as (Hfal & Ht).
  destruct Ht as (st' & msg & sus' & Ht).
  rewrite H in Ht. inverts Ht; right. rewrite Int.eq_true.  auto.

  intros.
  unfolds in H5.
  destruct H5. rewrite H; auto. introv Hf; tryfalse.
  destruct H5 as (qid & Hecb). unfolds in Hecb.
  destruct Hecb as (p_q & ow & Hecb).
  rewrite EcbMod.map_emp_get in Hecb. inverts Hecb.
  destruct H5 as (Hfal & Ht).
  destruct Ht as (st' & msg & sus' & Ht).
  rewrite H in Ht. inverts Ht. auto.  

Qed.

Lemma init_goodks_h:
  forall T client_code cst O,
    InitTasks T client_code cst O ->
    good_client_code client_code ->
    no_abort T -> 
    goodtasks_h T .
Proof.
  intros.
  unfolds in H.
  unfolds.
  intros.
  mytac.
  apply H3 in H2.
  mytac.
  unfolds in H0.
  mytac.
  apply H0 in H4.
  clear -H4.
  unfolds.
(*   unfolds in H4. *)
  induction x;simpl in *; auto; tryfalse.
  simpljoin; repeat try splits; auto.
(*   mytac. *)
  apply IHx1;auto.
  apply IHx2;auto.
   simpljoin; repeat try splits; auto.
(*   mytac. *)
  apply IHx1;auto.
  apply IHx2;auto.
Qed.
