Require Import log_code_defs.
Require Import log_code_notations.

Require Import FIFO_inv_and_init.
Require Import FIFO_spec. 
(* Require Import FIFO_succ.  *)
Require Import FIFO_sys.
Require Import FIFO_pure.

(* Require Import mqsend_good_stmt_preserve. *)
(* Require Import mqreceive_good_stmt_preserve. *)
(* Require Import mqtimedreceive_good_stmt_preserve. *)
(* Require Import mqgetinfo_good_stmt_preserve. *)

Require Import seplog_tactics.
Import DeprecatedTactic.

Open Scope type_scope.
Open Scope list_scope.

(******************INIT*******************************)
Theorem INIT_INVPROP_Prop:
  forall client_code T cst O ,
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    INV_PROP client_code O.
Proof.
  intros.
  unfolds. splits;auto.
  clear H1.
  
  unfolds.
  unfold init_st in H0.
  mytac.
  
  intros.
  rewrite H0 in H8.
  inverts H8.
  rewrite EcbMod.emp_sem in H9;tryfalse.
Qed.  

(*****************STEP ************************)

Ltac destruct_inverts1 H:=
  let Hx:= fresh in
  match type of H with
    | ?H1 \/ ?H2 => destruct H as [Hx | H]; [inverts Hx | destruct_inverts1 H]
    | exists _, _ = _ => let x:= fresh in (destruct H as (x&H);inverts H)
    | _ => idtac
  end.

Require Import auxdef.
Require Import join_lib.
Require Import fifo_ext_steps_preserve.

Lemma joinsig_neq_get:
  forall x y els els0 s eid,
    eid <> x ->
    MqcntMod.get els0 eid = s ->
    MqcntMod.joinsig x y els els0 ->
    MqcntMod.get els eid = s.
Proof.
  intros.
  pose proof H1 eid.
  rewrite MqcntMod.get_sig_none in H2; auto.
  destruct (MqcntMod.get els eid);
  destruct (MqcntMod.get els0 eid); tryfalse; substs; auto.
Qed.

Lemma hpstep_inv_prop_hold:
  forall client_code T cst O T' cst' O' ,
    goodtasks_h T ->
    hpstep (client_code, os_spec') T cst O T' cst' O' ->
    INV_PROP client_code O  ->
    INV_PROP client_code O' .
Proof.
  introv Hgoodtasks.
  introv Hp Hinv.
  unfolds in Hinv.
  destruct Hinv as (Hinv1 & Hinv2 ).
  splits; auto.
  lets Hps: fifo_ext_hpstep_preserve Hgoodtasks Hinv2 Hp; eauto. 
Qed.
  
Lemma init_goodks_h:
  forall T client_code cst O,
    InitTasks T client_code cst O ->
    INV_PROP client_code O -> 
    goodtasks_h T .
Proof.
  intros.
  unfolds in H.
  unfolds.
  intros.
  mytac.
  apply H2 in H1.
  mytac.
  unfolds in H0.
  mytac.
  unfolds in H0.
  apply H0 in H3.
  clear -H3.
  unfolds.
  unfolds in H3.
  induction x;simpl in *;auto;tryfalse.
  mytac.
  apply IHx1;auto.
  apply IHx2;auto.
  mytac.
  apply IHx1;auto.
  apply IHx2;auto.
Qed.

Require Import FIFO_good_stmt_preserve.
  
(**********Theorem First_In_First_Out_Prop  ******************)
Theorem First_In_First_Out_Prop:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    INV_PROP client_code O' .
Proof.
  introv Hinit_tasks Hinit_st Hgood_client Hhpstepstar.
  lets Hinv_prop : INIT_INVPROP_Prop Hinit_tasks Hinit_st Hgood_client.
  lets hgoodtasks:init_goodks_h Hinit_tasks Hinv_prop.
  clear Hinit_tasks Hinit_st.
  inductions Hhpstepstar.
  auto.
  eapply IHHhpstepstar;eauto.
  eapply hpstep_inv_prop_hold; eauto.
  eapply hpstepok_goodcode_h; eauto. 
Qed.


Theorem First_In_First_Out_Proof:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    hpstepstar (client_code, os_spec') T cst O T' cst' O' ->
    First_In_First_Out O'.
Proof.
  introv Hinit_tasks Hinit_st Hgood_client Hhpstepstar.
  lets Hinv_prop' : First_In_First_Out_Prop Hinit_tasks Hinit_st Hgood_client Hhpstepstar.
  unfolds in Hinv_prop'.
  mytac.
  unfolds in H0.
  unfolds.
  intros.
  destruct H7.
  eapply H0;eauto.
Qed.


