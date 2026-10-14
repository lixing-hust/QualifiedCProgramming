Require Import PIF_sys.
(* Require Import PIF_succs. *)
Require Import PIF_spec.
Require Import PIF_language.
Require Import PIF_Modules.
Require Import List.
Require Import PIF_opsem.
Require Import Coqlib.
Require Import Maps.
Require Import PIF_memory.
Require Import PIF_assertion.
Require Import init_and_inv_PIF.
Require Import inv_hold_init.
Open Scope nat_scope.
Require Import PIF_LibTactics.
Require Import Integers.

Require Import PIF_os_mutex.
Require Import PIF_os_code_defs. 
Require Import aux_lemmas. 
Open Scope int_scope.
Require Import PIF_join_lib.
Require Import int_auto.

Lemma hpstepok_no_abt_hold:
  forall client_code T cst O T' cst' O' ,
    goodtasks_h T ->
    good_client_code client_code ->
    hpstepok (client_code, os_spec') T cst O T' cst' O' ->
    no_abort T  ->
    no_abort T'.
Proof.
  intros.
  inverts H1; auto.
Qed.

Lemma hpstepstarok_no_abt_hold:
  forall client_code T cst O T' cst' O' ,
    goodtasks_h T ->
    good_client_code client_code ->
    hpstepstarok (client_code, os_spec') T cst O T' cst' O' ->
    no_abort T  ->
    no_abort T'.
Proof.
  intros.
  inverts H1; auto.
Qed.

Definition isrdy (st:taskstatus):=
  match st with
    | rdy => True
    | _ => False
  end.

Require Import pif_steps_preserve.
  
Lemma hpstepok_pif_hold:
  forall client_code T cst O T' cst' O' ,
    goodtasks_h T ->
    (* good_client_code client_code -> *)
    no_nest_client client_code O T cst ->
    hpstepok (client_code, os_spec') T cst O T' cst' O' ->
    (* no_abort T  -> *)
    GOOD_DT O ->
    PIF O ->
    PIF O'.
Proof.
  introv Hgdtk (* Hgdcode *) Hnonest Hpok (* Habt *) Hgdst Hpif.
  assert (Hpok_:=Hpok).
  inverts Hpok_.
  assert (Hnn1: NO_NEST_PENDING_O O).
  {
    unfolds in Hnonest. eapply Hnonest; eauto.
    constructors.
  }
  assert (Hnn2: NO_NEST_PENDING_O O').
  {
    unfolds in Hnonest. eapply Hnonest; eauto.
    repeat (constructors; eauto).
  }
  eapply no_nest_pif_hpstepok_preserve with (O:=O) (O':=O'); eauto.
Qed.   

Lemma no_nest_prop_step_hold:
  forall client_code T cst O T' cst' O' ,
    no_nest_client client_code O T cst ->
    hpstepok (client_code, os_spec') T cst O T' cst' O' ->
    no_nest_client client_code O' T' cst'.
Proof.
  introv Hn Hp.
  lets Hpp: Hp.
  inverts Hp.
  unfolds in Hn.
  unfolds.
  intros.
  eapply Hn; eauto.
  constructors; eauto.
  inverts H1; eauto.
Qed.

Require Import pif_tacs.
Require Import good_stmt_preserve.
Require Import good_dt_steps_preserve. 

Lemma hpstepstarok_pif_hold:
  forall client_code T cst O T' cst' O' ,
    goodtasks_h T ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstarok (client_code, os_spec') T cst O T' cst' O' ->
    no_abort T  ->
    GOOD_DT O ->
    PIF O ->
    PIF O'.
Proof.
  introv Hgdtasks.
  intros.
  inductions H1;auto.
  
  eapply IHhpstepstarok with (T:= T' );eauto.
  2: eapply no_nest_prop_step_hold;eauto.
  2: eapply hpstepok_no_abt_hold; eauto.
  eapply hpstepok_goodcode_h; eauto.
  eapply good_dt_hpstepok_preserve; eauto.
  eapply hpstepok_pif_hold; eauto.
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
  unfolds in H4.
  induction x;simpl in *;auto;tryfalse.
  mytac.
  simpljoin. splits; auto. splits.
  apply IHx1;auto.
  apply IHx2;auto.
  simpljoin. splits; auto. splits.
  apply IHx1;auto.
  apply IHx2;auto.
Qed.

Lemma Priority_Inversion_Free_Prop:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    no_abort T  ->
    GOOD_DT O ->
    hpstepstarok (client_code, os_spec') T cst O T' cst' O' ->
    PIF O ->
    PIF O'.
Proof.
  introv Hinittasks.
  intros.
  lets hgoodtasks:init_goodks_h Hinittasks H H1.
  clear Hinittasks.
  inductions H3.
  auto.
  eapply IHhpstepstarok;eauto.
  eapply good_dt_hpstepok_preserve; eauto. 
  eapply hpstepok_no_abt_hold; eauto.
  eapply no_nest_prop_step_hold; eauto.
  eapply hpstepok_pif_hold; eauto.
  eapply hpstepok_goodcode_h;eauto.
Qed.

Lemma Priority_Inversion_Free_Proof:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstarok (client_code, os_spec') T cst O T' cst' O' ->
    PIF O'.
Proof.
  intros.
  eapply Priority_Inversion_Free_Prop;eauto.
  eapply Init_no_abort_Prop; eauto.
  splits; eauto.
  assert(Hr: INV_PROP client_code O T).
  eapply Init_Invprop_Prop; eauto.
  unfolds; split; auto.
  destruct Hr as (Hr1 & (Hr2 & Hr3)).
  destruct Hr3 as (Hr3 & Hr4).
  auto.

  unfolds.
  intros.
  unfolds in H15.
  mytac.
  unfolds in H0.
  mytac.
  rewrite H0 in H4; inverts H4.
  rewrite EcbMod.emp_sem in H15;tryfalse.
  Unshelve.
  exact cst.
Qed.

Lemma pif_to_upif:
  forall O,
    GOOD_DT O ->
    PIF O ->
    UPIF O.
Proof.
  intros.
  unfolds; intros.
  eapply H0; eauto.
  unfolds in H.
  lets Hx:H H1 H2 H4 H5; eauto.
  mytac.
  clear H.  

  inverts H12.
  destruct H.
  unfolds in H.
  mytac.
  unfolds in H13.
  mytac.
  apply H20 in H.
  unfolds in H;unfolds.
  mytac;do 4 eexists;eauto.
  unfolds in H.
  mytac.
  unfolds in H13.
  mytac.
  apply H20 in H.
  unfolds in H;unfolds;mytac.
  do 4 eexists;eauto.
Qed.

Lemma init_goodks_h':
  forall T client_code cst O,
    InitTasks T client_code cst O ->
    good_client_code client_code ->
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
  apply H0 in H3.
  clear -H3.
  unfolds.
  unfolds in H3.
  induction x;simpl in *;auto;tryfalse.
  mytac.
  simpljoin. splits; auto. splits.
  apply IHx1;auto.
  apply IHx2;auto.
  simpljoin. splits; auto. splits.
  apply IHx1;auto.
  apply IHx2;auto.
Qed.

Lemma GOOD_DT_Prop:
  forall client_code T cst O T' cst' O',
    goodtasks_h T ->
    good_client_code client_code ->
    GOOD_DT O->
    no_nest_client client_code O T cst ->
    hpstepstarok (client_code, os_spec') T cst O T' cst' O' ->
    GOOD_DT O'.
Proof.
  intros.
  inductions H3; auto.
  eapply IHhpstepstarok with (O:= O') (T:= T');eauto.
  2:eapply hpstepok_goodcode_h;eauto.
  2: eapply no_nest_prop_step_hold;eauto.
  eapply good_dt_hpstepok_preserve; eauto. 
Qed.

Lemma GOOD_DT_Prop':
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstarok (client_code, os_spec') T cst O T' cst' O' ->
    GOOD_DT O'.
Proof.
  intros.
  eapply GOOD_DT_Prop;eauto.
  eapply init_goodks_h';eauto.
  assert(Hr:INV_PROP client_code O T).
  eapply Init_Invprop_Prop; eauto.
  unfolds; split; auto.
  unfolds in Hr; mytac.
  unfolds in H6; mytac.

  Unshelve.
  exact cst.
Qed.

Theorem Unbounded_Priority_Inversion_Free_Proof:
  forall client_code T cst O T' cst' O',
    InitTasks T client_code cst O ->
    init_st O ->
    goodtasks_h T ->
    good_client_code client_code ->
    no_nest_client client_code O T cst ->
    hpstepstarok (client_code, os_spec') T cst O T' cst' O' ->
    UPIF O'.
Proof.
  intros.
  assert (GOOD_DT O').
  eapply GOOD_DT_Prop';eauto.
  unfolds.
  lets Hx: Priority_Inversion_Free_Proof H H0 H2 H3; eauto.
  lets Hs: Hx H4.
  eapply pif_to_upif; eauto.
Qed.
