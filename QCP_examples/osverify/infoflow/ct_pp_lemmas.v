Require Import base_tac. 
Require Import memory. 
Require Import seplog_lemmas. 
Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import prt_apispecs. 
Require Import buffer_apispecs. 
Require Import osspecs. 
Require Import properties.
Require Import FunctionalExtensionality.
Require Import if_assms.
Require Import sem_prop.
Require Import sem_prop_2. 
Require Import if_succ_gen.
Require Import if_common_lemmas. 
Require Import spec_aux_defs. 
Require Import confidentiality_tactics.
Require Import confidentiality_lemmas. 
Require Import math_auto. 
Require Import data_invs.
Require Import equiv_prop.
Require Import if_good_code.
Set Keyed Unification. 

Lemma qtimedpost_ovf_block_ctid_same:
  forall vp v0 i O0 act O0' v' Of O O', 
    qtimedpost_ovf_block_body (vp :: v0 :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    get O curtid = get O' curtid. 
Proof.
  introv Hovf Hjo Hjo'.
  inverts Hovf.
  simpljoin.
  match goal with
    H: ?f _ = ?f _ |- _ => inverts H
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  rewrite set_a_get_a'; eauto.
  2: {introv Hf; inverts Hf. }
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qtimedpost_timeout_err_ctid_same:
  forall vp v0 i O0 act O0' v' Of O O', 
    qtimedpost_timeout_err_body (vp :: v0 :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    get O curtid = get O' curtid. 
Proof.
  introv Hto Hjo Hjo'.
  inverts Hto.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end. 
  match goal with
    H: ?f _ = ?f _ |- _ => inverts H
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  rewrite set_a_get_a'; eauto.
  2: {introv Hf; inverts Hf. }
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.


(********************* lemmas for prio_preserved (mq_send) ************************)

Lemma qpost_nowt_succ_prio_preserved: 
  forall vp v i O O' act v' O0 O0' Of, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    prio_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds. intros. unfolds.
  introv Hd.
  unfolds in Hpost.
  simpljoin.
  match goal with
    H: _ /\ Some _ = Some _ \/ _ /\ Some _ = None |- _ =>
      inverts H; simpljoin; tryfalse 
  end.
  match goal with
    H: Some _ = Some _ |- _ => inversion H1
  end.
  assert (Hgeq: get O0 abstcblsid = get O0' abstcblsid).
  {
    subst O0'.
    rewrite set_a_get_a'; eauto.
    introv Hf.
    inverts Hf. 
  }
  split.
  introv Htpi.
  lets H_: tpi_upd_frm_preserved Htpi Hgeq; eauto.
  symmetry in Hgeq.
  introv Htpi'.
  lets H_: tpi_upd_frm_preserved Htpi' Hgeq; eauto.
Qed.

Lemma qpost_exwt_succ_prio_preserved: 
  forall vp v i O O' act v' O0 O0' Of, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    prio_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds. intros. unfolds.
  introv Hd.
  unfolds in Hpost.
  simpljoin.
  match goal with
    H: _ /\ Some _ = Some _ \/ _ /\ Some _ = None |- _ =>
      inverts H; simpljoin; tryfalse 
  end.
  match goal with
    H: Some _ = Some _ |- _ => inversion H; clear H
  end.
  assert (Hgeq: get O0' abstcblsid = Some (abstcblist (set x7 x6 (x11, rdy, x0, x10, x15)))).
  {
    subst O0'.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a; eauto. 
    introv Hf.
    inverts Hf. 
  }
  assert (Hg1: get O abstcblsid = Some (abstcblist x7)).
  { eapply join_get_get_l; eauto. }
  assert (Hg2: get O' abstcblsid = Some (abstcblist (set x7 x6 (x11, rdy, x0, x10, x15)))). 
  { eapply join_get_get_l; eauto. }
  split; 
    introv Htpi.
  -
    unfold task_prio_id in *.
    simpljoin.
    l_rew21_inv1 (get O abstcblsid).
    casetac x6 t Ht Hf.
    + subst. l_rew21_inv1 (get x7 t).
      do 5 eexists. split; eauto.
      rewrite set_a_get_a. eauto.
    + do 5 eexists. split; eauto.
      rewrite set_a_get_a'; eauto. 
  -
    unfold task_prio_id in *.
    simpljoin.
    l_rew21_inv1 (get O' abstcblsid).
    casetac x6 t Ht Hf.
    + subst. rewrite set_a_get_a in H1. inverts H1.
      do 5 eexists.
      split; eauto. 
    + rewrite set_a_get_a' in H1; eauto.
      do 5 eexists.
      split; eauto.  
Qed.

Lemma qtimedpost_ovf_block_prio_preserved: 
  forall vp v i O O' act v' O0 O0' Of, 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->              
    join O0 Of O ->
    join O0' Of O' -> 
    prio_preserved O O'.
Proof.
  introv Hovf Hjo Hjo'.
  unfolds. intros. unfolds.
  introv Hd.
  unfolds in Hovf.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inversion H; clear H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  match goal with
    H: context [abstcblist ?tcbs] |- _ => assert (HgO': get O' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto.
    subst.
    rewrite set_a_get_a'; eauto.
    2: { introv Hf; inverts Hf. }
    rewrite set_a_get_a.
    auto.
  }
  match goal with
    H: get O0 abstcblsid = ?stcbs |- _ => assert (HgO: get O abstcblsid = stcbs)
  end.
  {
    eapply join_get_get_l; eauto.
  }
  match goal with H: get O0 curtid = Some (oscurt ?t) |- _ => rename t into ct end.
  split; introv Htpi.
  -
    unfold task_prio_id in *.
    simpljoin.
    rewrite HgO'.
    l_rew21_inv1 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.      
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      match goal with
        H1: get _ t = Some (_, ?pr1), H2: get _ t = Some (_, ?pr2) |- _ =>
          rewrite H1 in H2; inverts H2
      end.
      eauto.
    +
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a'; eauto.
  -
    unfold task_prio_id in *.
    simpljoin.
    rewrite HgO.
    l_rew21_inv1 (get O' abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      rewrite set_a_get_a in H5; inverts H5.
      do 5 eexists. split; eauto.
    +
      rewrite set_a_get_a' in H5; eauto.
      do 5 eexists.
      split; eauto.
Qed. 

Lemma qtimedpost_timeout_err_prio_preserved: 
  forall vp v i O O' act v' O0 O0' Of, 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->   
    join O0 Of O ->
    join O0' Of O' -> 
    prio_preserved O O'.
Proof.
  introv Hto Hjo Hjo'.
  unfolds. intros. unfolds.
  introv Hd.
  unfolds in Hto.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end. 
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  kvext_h Hjo' abstcblsid O'.
  rename H into HgO'.
  kvext0 O0 abstcblsid O.
  rename H into HgO. 
  match goal with H: get O0 curtid = Some (oscurt ?t) |- _ => rename t into ct end.
  split; introv Htpi.
  -
    unfold task_prio_id in *.
    simpljoin.
    rewrite HgO'.
    l_rew21_inv1 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      match goal with
        H1: get _ t = Some (_, ?pr1), H2: get _ t = Some (_, ?pr2) |- _ =>
          rewrite H1 in H2; inverts H2
      end.
      eauto.
    +
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a'; eauto.
  -
    unfold task_prio_id in *.
    simpljoin.
    rewrite HgO.
    l_rew21_inv1 (get O' abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      rewrite set_a_get_a in H0; inverts H0.
      do 5 eexists. split; eauto.
    +
      rewrite set_a_get_a' in H0; eauto.
      do 5 eexists.
      split; eauto.
Qed. 


(********************* lemmas for prio_preserved (QPortPost) ************************)

Lemma tcbl_upd_task_prio_id_iff: 
  forall O O' tls tls' kportl cdstkpl els dpl, 
    get O abstcblsid = Some (abstcblist tls) -> 
    get O' abstcblsid = Some (abstcblist tls') -> 
    tcbl_upd kportl cdstkpl dpl els tls tls' ->
    prio_preserved O O'.
Proof.
  introv Hgt Hgt' Htupd.
  unfolds.
  intros.
  unfolds.
  introv Hd.
  unfolds in Htupd.
  specialize (Htupd t).
  destruct Htupd as [Hu | Hnu].
  - destruct Hu as (wl & a & Hwp & Hall). 
    split.
    + 
      introv Htpi.
      unfold task_prio_id in *.
      simpljoin.
      l_rew21_inv1 (get O abstcblsid).
      match goal with H1: get tls t = _, H2: get tls t = _ |- _ => rewrite H1 in H2; inverts H2 end.
      do 5 eexists. split; eauto.
    +
      introv Htpi'.
      unfold task_prio_id in *.
      simpljoin.
      l_rew21_inv1 (get O' abstcblsid).
      match goal with H1: get tls' t = _, H2: get tls' t = _ |- _ => rewrite H1 in H2; inverts H2 end.
      do 5 eexists. split; eauto.
  - destruct Hnu as (Hnex & Hgeq).
    unfold task_prio_id.
    rewrite Hgt. rewrite Hgt'.
    split.
    + introv Hex.
      simpljoin.
      match goal with H: Some _ = Some _ |- _ => inverts H end.
      match goal with
        H1: get tls' t = ?t, H2: ?t' = _ |- _ => unify t t'; rewrite H2 in H1 end.
      do 5 eexists. split; eauto.
    + introv Hex.
      simpljoin.
      match goal with H: Some _ = Some _ |- _ => inverts H end.
      match goal with
        H: ?t = get tls t, H': ?t' = _ |- _ => unify t t'; rewrite H' in H
      end.
      do 5 eexists. split; eauto. 
Qed.

Lemma q_send_to_domain_prio_preserved:
  forall v O O' act v' O0 O0' Of, 
    q_send_to_domain (v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    prio_preserved O O'. 
Proof.
  introv Hsend Hjo Hjo'. 
  unfolds. intros. unfolds.
  introv Hd.
  unfolds in Hsend.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H; tryfalse 
  end.
  match goal with
    H: _ :: nil = _ :: nil |- _ => inverts H
  end. 
  kvext_h Hjo' abstcblsid O'.
  kvext0 O0 abstcblsid O.
  eapply tcbl_upd_task_prio_id_iff; eauto. 
Qed. 

Lemma store_msg_prio_preserved:
  forall v act v0 O O' Of O0 O0',  
    store_msg (v :: nil) O0 act (v0, Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    prio_preserved O O'.
Proof.
  introv Hsm Hjo Hjo'.
  inverts Hsm.
  simpljoin.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  assert (Hgeq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  unfolds.
  intros.
  unfolds.
  intros.
  unfold task_prio_id. 
  rewrite <- Hgeq. 
  tauto.
Qed.


(********************* lemmas for prio_preserved (QPortPend) ************************)

Lemma qportpend_notnil_prio_preserved:
  forall v v0 O0 O0' Of O O' act v', 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    prio_preserved O O'.
Proof.
  introv Hqpn Hjo Hjo'.
  unfolds. 
  introv Hd.
  unfolds in Hqpn.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H; tryfalse 
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  assert (Heq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l abstcblsid Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  unfold task_prio_id.
  rewrite <- Heq.
  tauto.
Qed.

Lemma qportpend_block_prio_preserved:
  forall v v0 O0 act v' O0' Of O O', 
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqpb Hjo Hjo'.
  unfolds. 
  introv Hd.
  unfolds in Hqpb.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H; tryfalse 
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  kvext_h Hjo' abstcblsid O'. 
  unfold task_prio_id. 
  match goal with H: get O' abstcblsid = _ |- _ => rewrite H end.
  kvext O0 abstcblsid O.
  match goal with
    H: get O0 curtid = Some (oscurt ?t) |- _ => rename t into ct
  end.
  split.
  - introv Hex.
    simpljoin.
    l_rew12_inv2 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      match goal with
        H1: get _ t = _, H2: get _ t = _ |- _ => rewrite H1 in H2; inverts H2
      end. 
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      eauto.
    +
      do 5 eexists.
      rewrite set_a_get_a'; eauto.
  -
    introv Hex.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    casetac ct t Ht Hf.
    + subst.
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a in H; inverts H
      end.
      do 5 eexists. split; eauto.
    + 
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a' in H; eauto; inverts H
      end.
      do 5 eexists. split; eauto.
Qed.

Lemma qportpend_block_get_prio_preserved: 
  forall v v0 O0 act v' O0' Of O O',
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqpg Hjo Hjo'.
  unfolds. 
  introv Hd.
  unfolds in Hqpg.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H; tryfalse 
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  kvext_h Hjo' abstcblsid O'. 
  unfold task_prio_id. 
  match goal with H: get O' abstcblsid = _ |- _ => rewrite H end.
  kvext O0 abstcblsid O.
  match goal with
    H: get O0 curtid = Some (oscurt ?t) |- _ => rename t into ct
  end.
  split. 
  - introv Hex.
    simpljoin.
    l_rew12_inv2 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      match goal with
        H1: get _ t = _, H2: get _ t = _ |- _ => rewrite H1 in H2; inverts H2
      end. 
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      eauto.
    +
      do 5 eexists.
      rewrite set_a_get_a'; eauto.
  -
    introv Hex.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    casetac ct t Ht Hf.
    + subst.
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a in H; inverts H
      end.
      do 5 eexists. split; eauto.
    + 
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a' in H; eauto; inverts H
      end.
      do 5 eexists. split; eauto.
Qed.

Lemma qportpend_block_to_prio_preserved: 
  forall v v0 O0 act v' O0' Of O O',
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqpt Hjo Hjo'.
  unfolds. 
  introv Hd.
  unfolds in Hqpt.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H; tryfalse 
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  kvext_h Hjo' abstcblsid O'. 
  unfold task_prio_id. 
  match goal with H: get O' abstcblsid = _ |- _ => rewrite H end.
  kvext O0 abstcblsid O.
  match goal with
    H: get O0 curtid = Some (oscurt ?t) |- _ => rename t into ct
  end.
  split. 
  - introv Hex.
    simpljoin.
    l_rew12_inv2 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      match goal with
        H1: get _ t = _, H2: get _ t = _ |- _ => rewrite H1 in H2; inverts H2
      end. 
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      eauto.
    +
      do 5 eexists.
      rewrite set_a_get_a'; eauto.
  -
    introv Hex.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    casetac ct t Ht Hf.
    + subst.
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a in H; inverts H
      end.
      do 5 eexists. split; eauto.
    + 
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a' in H; eauto; inverts H
      end.
      do 5 eexists. split; eauto.
Qed.


(********************* lemmas for prio_preserved (SamplePortPost) ************************)

Lemma sample_send_to_domain_prio_preserved: 
  forall v O0 act v' O0' Of O O',
    sample_send_to_domain (v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hsstd Hjo Hjo'.
  unfolds. 
  introv Hd.
  unfolds in Hsstd.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H; tryfalse 
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  unfold task_prio_id.
  assert (Hgteq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto. 
  }
  rewrite <- Hgteq.
  tauto.
Qed. 

(********************* lemmas for prio_preserved (PortPend) ************************)

Lemma receive_port_msg_prio_preserved:
  forall v O0 act v' O0' Of O O',
    receive_port_msg (v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hrpm Hjo Hjo'.
  unfolds. 
  introv Hd.
  unfolds in Hrpm.
  simpljoin.
  inv_some.
  inv_lst.
  rem_dis; unfold task_prio_id.
  -
    assert (Hgteq: get O abstcblsid = get O' abstcblsid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      repeat rewsimp. auto. 
    }
    rewrite <- Hgteq.
    tauto.
  -
    assert (Hgteq: get O abstcblsid = get O' abstcblsid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      repeat rewsimp. auto. 
    }
    rewrite <- Hgteq.
    tauto.
Qed.     


(*****************************************)  

Lemma reachable_get_ctid: 
  forall hp T cst O,
    reachable hp T cst O ->
    exists t, get O curtid = Some (oscurt t).               
Proof.
  introv Hrc.
  unfolds in Hrc.
  simpljoin.
  lets H_: hpstepokstar_eqdomO0 H1.
  unfold init in H0.
  destruct H0 as (Hinittsk & Hinitst).
  unfolds in Hinitst.
  simpljoin.
  unfold init_tsk_st in *.
  simpljoin.
  unfold eqdomO0 in H_.
  destruct H_ as (H1_2 & _).
  unfolds in H1_2.
  specialize (H1_2 curtid).
  match goal with H: get _ curtid = _ |- _ => rewrite H in H1_2 end.
  auto.
Qed. 

Lemma spec_step_ctid_eq:
  forall cd O cd' O' act, 
    spec_step (snd (api_spec, int_spec, get_hprio_d)) cd O cd' O' act ->
    get O curtid = get O' curtid. 
Proof.
  introv Hsp.
  induction Hsp; try (eapply join_get_same_l; eauto; fail); auto.
Qed.  

Lemma ctid_same_prio_preserved_dest:
  forall O O' t, 
    get O curtid = Some (oscurt t) -> 
    get O curtid = get O' curtid ->
    prio_preserved O O' ->
    ct_ex_prio_dom_eq O O'. 
Proof.
  introv Hgceq Hgt Hpp.
  unfolds in Hpp.
  unfold prio_preserved_d in Hpp.
  unfolds.
  rewrite Hgceq in Hgt.
  do 2 eexists.
  split; eauto.
  split; eauto.
  split.
  - split.
    +
      introv Hex.
      destruct Hex as (pr & Htpi).
      specialize (Hpp (dom_for_prio pr) pr t (eq_refl _)).
      destruct Hpp.
      eexists; eapply H; eauto.
    +
      introv Hex.
      destruct Hex as (pr & Htpi).
      specialize (Hpp (dom_for_prio pr) pr t (eq_refl _)).
      destruct Hpp.
      eexists; eapply H0; eauto.
  -
    introv Htpi1 Htpi2.
    specialize (Hpp (dom_for_prio pr1) pr1 t (eq_refl _)).
    destruct Hpp as (Htpi12 & Htpi21).
    lets H__: Htpi12 Htpi1.
    lets H_: prio_unique Htpi2 H__; eauto. 
    subst.
    auto.
Qed. 

Ltac des_vl_absprog hstep := 
  match goal with
    vl: vallist, H: nth_error (get_all_succs (match ?vl with _ => _ end)) _ = _ |- _ =>
      destruct vl; inverts H; tryfalse
  | H: nth_error (get_all_succs (ABORT)) _ = Some _ |- _ => 
      apply abt_succs_contra in H; subst; inverts hstep
  | H: nth_error (get_all_succs (match ?v with _ => _ end)) _ = _ |- _ =>
      destruct v; simpl in H;  
      try (apply abt_succs_contra in H; subst; inverts hstep)   
  end.

Lemma nabt_abt_false:
  forall T t ke ks, 
    nabt (set T t (curs (hapi_code (ABORT)), (ke, ks))) -> False. 
Proof.
  introv Hnabt.
  unfolds in Hnabt.
  specialize (Hnabt t).
  rewrite set_a_get_a in Hnabt.
  eapply Hnabt; eauto. 
Qed.

Lemma rv_Oeq_: 
  forall vl O act v O', 
    ret_val vl O act (v, Some O') -> O = O'. 
Proof.
  introv Hrv.
  unfolds in Hrv.
  simpljoin.
  congruence. 
Qed. 

Hint Resolve rv_Oeq_ : oeq_lemmas.

Lemma sskp_Oeq: 
  forall vl O act v O',
    spec_skip_step vl O act (v, Some O') -> 
    O = O'. 
Proof.
  introv Hstp.
  unfolds in Hstp.
  simpljoin.
  congruence. 
Qed. 

Hint Resolve sskp_Oeq : oeq_lemmas.

Lemma get_msize_Oeq:
  forall vl O act v O', 
    mqsend_get_msgsize vl O act (Some v, Some O') ->
    O = O'. 
Proof.
  introv Hgs.
  unfolds in Hgs.
  simpljoin.
  inverts H3.
  simpljoin.
  congruence.
  simpljoin.
  tryfalse. 
Qed.

Hint Resolve get_msize_Oeq : oeq_lemmas.

Lemma ms_getep_Oeq: 
  forall vl O act v' O', 
    mqsend_get_ecb_ptr vl O act (v', Some O') ->
    O = O'. 
Proof.
  introv Hgep.
  inverts Hgep.
  simpljoin.
  inverts H3.
  simpljoin.
  congruence.
  simpljoin. 
  tryfalse. 
Qed. 

Hint Resolve ms_getep_Oeq : oeq_lemmas.

Lemma mqgf_Oeq: 
  forall vl O act v O', 
    mqsend_get_mqflags vl O act (v, Some O') ->
    O = O'. 
Proof.
  introv Hmf.
  inverts Hmf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; solve [congruence | false] end.
Qed.

Hint Resolve mqgf_Oeq : oeq_lemmas.

Lemma aar_Oeq:
  forall vl O O' act v, asrt_and_ret vl O act (v, Some O') -> O = O'.
Proof.
  introv Haar.
  unfolds in Haar.
  simpljoin.
  inverts H2; simpljoin.
  inverts H0. auto.
  tryfalse. 
Qed.   

Hint Resolve aar_Oeq : oeq_lemmas.

Lemma qtimedpost_after_sched_Oeq: 
  forall O act v0 v1 v' i O', 
    qtimedpost_after_sched (v0 :: v1 :: Vint32 i :: nil) O act (v', Some O') -> 
    O = O'. 
Proof.
  introv Hmf.
  inverts Hmf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; solve [congruence | false] end.
Qed.

Hint Resolve qtimedpost_after_sched_Oeq : oeq_lemmas. 

Lemma mce_Oeq:
  forall v1 v2 v3 i O O' act,
    memcpy_empty (v1 :: v2 :: Vint32 i :: nil) O act (v3, Some O') ->
    O = O'.
Proof.
  introv Hme.
  inverts Hme.
  simpljoin.
  congruence.
Qed.   

Hint Resolve mce_Oeq : oeq_lemmas. 

Lemma qpend_nopwl_succ_prio_preserved: 
  forall v1 v2 v3 O0 O0' Of O O' act, 
    qpend_get_no_pwl_succ_body (v1 :: v2 :: nil) O0 act (v3, Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqp Hjo Hjo'.
  inverts Hqp.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  unfolds.
  intros.
  unfolds.
  introv Hd.
  unfold task_prio_id.
  assert (Hgeq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  rewrite <- Hgeq.
  split; auto.
Qed. 

Lemma qpend_block_get_prio_preserved:
  forall v1 v2 v3 O0 O0' Of act O O', 
    qpend_block_get_body (v1 :: v2 :: nil) O0 act (v3, Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqb Hjo Hjo'.
  inverts Hqb.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with
    H: Some _ = Some _ |- _ => inverts H; tryfalse 
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  kvext_h Hjo' abstcblsid O'. 
  unfolds. intros. unfolds. 
  unfold task_prio_id. 
  match goal with H: get O' abstcblsid = _ |- _ => rewrite H end.
  kvext O0 abstcblsid O.
  match goal with
    H: get O0 curtid = Some (oscurt ?t) |- _ => rename t into ct
  end.
  split. 
  - introv Hex.
    simpljoin.
    l_rew12_inv2 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      match goal with
        H1: get _ t = _, H2: get _ t = _ |- _ => rewrite H1 in H2; inverts H2
      end. 
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      eauto.
    +
      do 5 eexists.
      rewrite set_a_get_a'; eauto.
  -
    introv Hex.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    casetac ct t Ht Hf.
    + subst.
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a in H; inverts H
      end.
      do 5 eexists. split; eauto.
    + 
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a' in H; eauto; inverts H
      end.
      do 5 eexists. split; eauto.
Qed. 

Lemma qpend_get_expwl_before_sched_prio_preserved: 
  forall v1 v2 v3 O0 O0' act Of O O', 
    qpend_get_ex_pwl_before_sched_body (v1 :: v2 :: nil) O0 act (v3, Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqg Hjo Hjo'.
  inverts Hqg.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  kvext_h Hjo' abstcblsid O'. 
  unfolds. intros. unfolds. 
  unfold task_prio_id. 
  match goal with H: get O' abstcblsid = _ |- _ => rewrite H end.
  kvext O0 abstcblsid O.
  match goal with
    H: GetHWait _ _ ?x |- _ => rename x into ct
  end.
  split. 
  - introv Hex.
    simpljoin.
    l_rew12_inv2 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      match goal with
        H1: get _ t = _, H2: get _ t = _ |- _ => rewrite H1 in H2; inverts H2
      end. 
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      eauto.
    +
      do 5 eexists.
      rewrite set_a_get_a'; eauto.
  -
    introv Hex.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    casetac ct t Ht Hf.
    + subst.
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a in H; inverts H
      end.
      do 5 eexists. split; eauto.
    + 
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a' in H; eauto; inverts H
      end.
      do 5 eexists. split; eauto.
Qed.   

Lemma qpend_block_prio_preserved: 
  forall v1 v2 v3 O0 O0' act Of O O',  
    qpend_block_body (v1 :: v2 :: nil) O0 act (v3, Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqb Hjo Hjo'.
  inverts Hqb.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  kvext_h Hjo' abstcblsid O'. 
  unfolds. intros. unfolds. 
  unfold task_prio_id. 
  match goal with H: get O' abstcblsid = _ |- _ => rewrite H end.
  kvext O0 abstcblsid O.
  match goal with
    H: get _ curtid = Some (oscurt ?x) |- _ => rename x into ct
  end.
  split. 
  - introv Hex.
    simpljoin.
    l_rew12_inv2 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      match goal with
        H1: get _ t = _, H2: get _ t = _ |- _ => rewrite H1 in H2; inverts H2
      end. 
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      eauto.
    +
      do 5 eexists.
      rewrite set_a_get_a'; eauto.
  -
    introv Hex.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    casetac ct t Ht Hf.
    + subst.
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a in H; inverts H
      end.
      do 5 eexists. split; eauto.
    + 
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a' in H; eauto; inverts H
      end.
      do 5 eexists. split; eauto.
Qed.

Lemma qpend_to_body_prio_preserved: 
  forall v1 v2 v3 O0 O0' act Of O O',  
    qpend_to_body (v1 :: v2 :: nil) O0 act (v3, Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqt Hjo Hjo'.
  inverts Hqt.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.  
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  kvext_h Hjo' abstcblsid O'. 
  unfolds. intros. unfolds. 
  unfold task_prio_id. 
  match goal with H: get O' abstcblsid = _ |- _ => rewrite H end.
  kvext O0 abstcblsid O.
  match goal with
    H: get _ curtid = Some (oscurt ?x) |- _ => rename x into ct
  end.
  split. 
  - introv Hex.
    simpljoin.
    l_rew12_inv2 (get O abstcblsid).
    casetac ct t Ht Hf.
    +
      subst.
      match goal with
        H1: get _ t = _, H2: get _ t = _ |- _ => rewrite H1 in H2; inverts H2
      end. 
      do 5 eexists.
      split; eauto.
      rewrite set_a_get_a.
      eauto.
    +
      do 5 eexists.
      rewrite set_a_get_a'; eauto.
  -
    introv Hex.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    casetac ct t Ht Hf.
    + subst.
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a in H; inverts H
      end.
      do 5 eexists. split; eauto.
    + 
      match goal with
        H: get (set _ _ _) _ = _ |- _ => rewrite set_a_get_a' in H; eauto; inverts H
      end.
      do 5 eexists. split; eauto.
Qed.

Lemma qpend_assm_stat_prio_preserved:
  forall v1 v3 O0 O0' act Of O O', 
    qpend_assm_stat (v1 :: nil) O0 act (v3, Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqa Hjo Hjo'.
  inverts Hqa.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  assert (O = O') by join auto.
  subst.
  apply prio_preserved_refl; auto. 
Qed.   

Lemma aqcc_succ_prio_preserved: 
  forall v1 v2 v3 O0 O0' act Of O O',  
    qacc_succ_body (v1 :: v2 :: nil) O0 act (v3, Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    prio_preserved O O'. 
Proof.
  introv Hqs Hjo Hjo'.
  inverts Hqs.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.  
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (Hgeq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  unfolds. intros. unfolds.
  introv Hd.
  unfold task_prio_id.
  rewrite <- Hgeq.
  split; auto.  
Qed.  
  

Ltac symexe :=
  match goal with
    H: spec_step _ _ _ _ _ _ |- _ => inverts H; symexe
  | H: nabt (set _ _ (curs (hapi_code (ABORT)), _)) |- _ =>
      apply nabt_abt_false in H; solve [false]; symexe
  | H: ~(exists _, END _ = END _) /\ _ |- _ =>
      let hf := fresh in (destruct H as (hf & _); false; apply hf; eexists; eauto); symexe
  | H: _ /\ (ABORT <> ABORT) |- _ =>
      let hf := fresh in (destruct H as (_ & hf)); false; apply hf; auto; symexe
  | H: _ |- prio_preserved ?O1 ?O2 =>
      unify O1 O2; apply prio_preserved_refl; symexe
  | act: action, H: ?f _ ?O ?act (_, Some ?O'), H1: join _ _ ?O1, H2: join _ _ ?O2 |- _ =>
      (assert (O = O') by eauto with oeq_lemmas; subst); 
      (assert (O1 = O2) by join auto; subst); symexe
  | _ => idtac
  end.

Lemma spec_step_prio_preserved: 
  forall cd O cd' O' act fid ac ft vl, 
    spec_step (snd (api_spec, int_spec, get_hprio_d)) cd O cd' O' act ->
    api_spec fid = Some (ac, ft) ->
    In cd (get_all_succs (ac vl)) ->
    prio_preserved O O'. 
Proof.
  introv Hsp Hgf Hin.
  apply In_nth_error in Hin.
  destruct Hin as (n & Hin).
  unfolds in Hgf.
  simpl in Hgf. inverts Hgf.
  destruct (Zeq_bool mq_send fid) eqn: Ems.
  - 
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    unfold mqsend in Hin.
    repeat des_vl_absprog Hsp.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe. 
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    eapply qpost_nowt_succ_prio_preserved; eauto. 
    eapply qpost_exwt_succ_prio_preserved; eauto.
    eapply qtimedpost_ovf_block_prio_preserved; eauto.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    eapply qtimedpost_timeout_err_prio_preserved; eauto.
    destruct n. simpl in H0; inverts H0.
    symexe.
    eapply qpost_nowt_succ_prio_preserved; eauto. 
    eapply qpost_exwt_succ_prio_preserved; eauto. 
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    destruct n. simpl in H0; inverts H0.
    symexe.
    match goal with
      H: context [nth_error] |- _ =>
        simpl in H; rewrite nth_error_nil in H; false
    end.
  -
    destruct (Zeq_bool mq_recv fid) eqn: Emr.
    +
      match goal with H: Some _ = Some _ |- _ => inverts H end.
      unfold mqreceive in Hin.
      repeat des_vl_absprog Hsp.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      eapply qpend_nopwl_succ_prio_preserved; eauto. 
      eapply qpend_get_expwl_before_sched_prio_preserved; eauto.
      eapply qpend_block_prio_preserved; eauto.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      eapply qpend_assm_stat_prio_preserved; eauto.
      destruct n. simpl in H0; inverts H0.
      symexe.
      eapply qpend_block_get_prio_preserved; eauto.
      eapply qpend_to_body_prio_preserved; eauto. 
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      eapply aqcc_succ_prio_preserved; eauto. 
      destruct n. simpl in H0; inverts H0.
      symexe.
      destruct n. simpl in H0; inverts H0.
      symexe.
      simpl in H0. rewrite nth_error_nil in H0.
      false.
    +
      destruct (Zeq_bool mq_timedrecv fid) eqn: Emqt.
      *
        match goal with H: Some _ = Some _ |- _ => inverts H end.
        unfold mqtimedreceive in Hin.
        repeat des_vl_absprog Hsp.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        eapply qpend_nopwl_succ_prio_preserved; eauto.
        eapply qpend_get_expwl_before_sched_prio_preserved; eauto. 
        eapply qpend_block_prio_preserved; eauto.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        destruct n. simpl in H0; inverts H0.
        symexe.
        eapply qpend_assm_stat_prio_preserved; eauto.
        destruct n. simpl in H0; inverts H0.
        symexe.
        eapply qpend_block_get_prio_preserved; eauto.
        eapply qpend_to_body_prio_preserved; eauto.         
        destruct n. simpl in H0; inverts H0.        
        symexe.
        destruct n. simpl in H0; inverts H0.        
        symexe.
        eapply aqcc_succ_prio_preserved; eauto. 
        destruct n. simpl in H0; inverts H0.        
        symexe.
        destruct n. simpl in H0; inverts H0.        
        symexe.
        simpl in H0.
        rewrite nth_error_nil in H0.
        false. 
      *
        destruct (Zeq_bool q_port_post fid) eqn: Eqp.
        **
          match goal with H: Some _ = Some _ |- _ => inverts H end.
          unfold qportpost in Hin.
          repeat des_vl_absprog Hsp.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          eapply q_send_to_domain_prio_preserved; eauto.
          eapply store_msg_prio_preserved; eauto.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          destruct n. simpl in H0; inverts H0.
          symexe.
          simpl in H0. rewrite nth_error_nil in H0.
          false. 
        **
          destruct (Zeq_bool q_port_pend fid) eqn: Eqpd.
          *** 
            match goal with H: Some _ = Some _ |- _ => inverts H end.
            unfold qportpend in Hin.
            repeat des_vl_absprog Hsp.
            destruct n. simpl in H0; inverts H0.
            symexe.
            destruct n. simpl in H0; inverts H0.
            symexe.
            destruct n. simpl in H0; inverts H0.
            symexe.
            destruct n. simpl in H0; inverts H0.
            symexe.
            destruct n. simpl in H0; inverts H0.
            symexe.
            eapply qportpend_notnil_prio_preserved; eauto.
            destruct n. simpl in H0; inverts H0.
            symexe.
            destruct n. simpl in H0; inverts H0.
            symexe.
            destruct n. simpl in H0; inverts H0.
            symexe.
            eapply qportpend_block_prio_preserved; eauto.
            destruct n. simpl in H0; inverts H0.
            symexe.
            destruct n. simpl in H0; inverts H0.
            symexe.
            eapply qportpend_block_get_prio_preserved; eauto.
            eapply qportpend_block_to_prio_preserved; eauto.
            simpl in H0.
            rewrite nth_error_nil in H0.
            false. 
          ***
            destruct (Zeq_bool sample_port_post fid) eqn: Eqsp.
            ****
              match goal with H: Some _ = Some _ |- _ => inverts H end.
              unfold sampleportpost in Hin.
              repeat des_vl_absprog Hsp.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe. 
              destruct n. simpl in H0; inverts H0.
              symexe. 
              destruct n. simpl in H0; inverts H0.
              symexe. 
              destruct n. simpl in H0; inverts H0.
              symexe.
              eapply sample_send_to_domain_prio_preserved; eauto.  
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              simpl in H0.
              rewrite nth_error_nil in H0.
              false.
            ****
              destruct (Zeq_bool port_accept fid) eqn: Eqpa.
              *****
              match goal with H: Some _ = Some _ |- _ => inverts H end.
              unfold portaccept in Hin.
              repeat des_vl_absprog Hsp.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              eapply receive_port_msg_prio_preserved; eauto.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              simpl in H0.
              rewrite nth_error_nil in H0.
              false. 
                
              *****
              destruct (Zeq_bool buffer_post fid) eqn: Eqbp.
              ******
              match goal with H: Some _ = Some _ |- _ => inverts H end.
              unfold bufferpost in Hin.
              repeat des_vl_absprog Hsp.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              eapply qpost_nowt_succ_prio_preserved; eauto. 
              eapply qpost_exwt_succ_prio_preserved; eauto. 
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              simpl in H0.
              rewrite nth_error_nil in H0.
              false. 
              ******
              destruct (Zeq_bool buffer_accept fid) eqn: Eqba.
              *******
              match goal with H: Some _ = Some _ |- _ => inverts H end.
              unfold bufferaccept in Hin.
              repeat des_vl_absprog Hsp.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe. 
              eapply aqcc_succ_prio_preserved; eauto.
              destruct n. simpl in H0; inverts H0.
              symexe.
              simpl in H0.
              rewrite nth_error_nil in H0.
              false.
              *******
              destruct (Zeq_bool buffer_pend fid) eqn: Eqbp_.
              match goal with H: Some _ = Some _ |- _ => inverts H end.
              unfold bufferpend in Hin.
              repeat des_vl_absprog Hsp.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe. 
              eapply qpend_nopwl_succ_prio_preserved; eauto.
              eapply qpend_get_expwl_before_sched_prio_preserved; eauto.
              eapply qpend_block_prio_preserved; eauto. 
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              eapply qpend_assm_stat_prio_preserved; eauto.
              destruct n. simpl in H0; inverts H0.
              symexe.
              eapply qpend_block_get_prio_preserved; eauto.
              eapply qpend_to_body_prio_preserved; eauto.
              destruct n. simpl in H0; inverts H0.
              symexe.
              destruct n. simpl in H0; inverts H0.
              symexe.
              simpl in H0.
              rewrite nth_error_nil in H0. false. 

          false.

          Unshelve.
          trivial.
          trivial.
          trivial.
Qed. 


Lemma GoodStmt_noabs: 
  forall s, GoodStmt_h s -> stmt_noabs s.
Proof.
  inductions s; 
    introv HGS;
    try (simpl; auto).
  - 
    simpl in HGS.
    simpljoin.
    split; eauto.
  -
    simpl in HGS.
    simpljoin.
    split; eauto.
Qed. 


Lemma good_client_code_impl_noabs:
  forall cliprogs, 
    good_client_code cliprogs ->
    pu_noabs cliprogs.
Proof.
  introv Hgcc.
  unfolds in Hgcc.
  unfolds.
  introv Hcf.
  lets H__: Hgcc Hcf.
  apply GoodStmt_noabs; auto. 
Qed. 


Lemma nintr_absintcont_none: 
  forall O T t cd ke ks, 
    get O curtid = Some (oscurt t) ->
    get T t = Some (curs (hapi_code cd), (ke, ks)) ->
    ~ in_intr T O ->
    absintcont ks = None.
Proof.
  introv Hgct Hgt Hnintr.
  unfolds in Hnintr.
  unfold in_intr in Hnintr.
  destruct (absintcont ks) eqn: E.
  - false.
    eapply Hnintr.
    unfold code_cur_task.
    rewrite Hgct.
    rewrite Hgt.
    do 3 eexists.
    split; eauto.
    rewrite E.
    introv Hf; false.
  - auto.
Qed. 

Lemma reachable_htstep_ct_same_pp: 
  forall pu T cst O t d cst' O' C C' act, 
    good_client_code pu -> 
    reachable (pu, (api_spec, int_spec, get_hprio_d)) T cst O ->
    ~ in_intr T O ->
    get O curtid = Some (oscurt t) -> 
    get T t = Some C -> 
    htstep (pu, (api_spec, int_spec, get_hprio_d)) t d C cst O C' cst' O' act ->
    ((exists t, get O curtid = Some (oscurt t)) /\
       get O curtid = get O' curtid /\ 
       prio_preserved O O').  
Proof.
  introv Hgoodcli Hrc Hnintr Hct HC Hsp. 
  lets Hpu: good_client_code_impl_noabs Hgoodcli. 
  lets Hgc: reachable_get_ctid Hrc; eauto.
  split; auto. 
  inverts Hsp.
  - (* cstep *)
    match goal with H: (_, _) = _ |- _ => inverts H end.
    split; auto.
    apply prio_preserved_refl. 
  - (* hapistep *)
    match goal with H: (_, _) = _ |- _ => inverts H end.
    match goal with H: context [hapistep] |- _ => inverts H end.
    + split; auto.
      apply prio_preserved_refl.
    + split.
      eapply spec_step_ctid_eq; eauto.
      destruct Hgc as (t_ & Hgct).
      l_rew12_inv2 (get O curtid).
      lets H__: reachable_ks_noint_apicode Hpu Hrc.
      lets H_: H__ HC; eauto. 
      lets Hni: nintr_absintcont_none HC; eauto.
      specializes Hni; eauto.
      simpl in H_.
      destruct H_ as (Hna & _).
      unfolds in Hna.
      specializes Hna; eauto.
      destruct Hna as [Hcd | [Habt | Hend]].
      *
        destruct Hcd as (fid & ac & ft & vl & Hgf & Hin).
        eapply spec_step_prio_preserved; eauto. 
      *
        subst.
        match goal with H: context [spec_step] |- _ => inverts H end.
      *
        simpljoin.
        match goal with H: context [spec_step] |- _ => inverts H end.
    + split; auto.
      apply prio_preserved_refl.
    + split; auto.
      apply prio_preserved_refl.
Qed.      


Lemma reachable_htstep_ct_ex_prio_dom_eq:
  forall pu T cst O t d cst' O' C C' act, 
    good_client_code pu -> 
    reachable (pu, (api_spec, int_spec, get_hprio_d)) T cst O ->
    ~ in_intr T O ->
    get O curtid = Some (oscurt t) -> 
    get T t = Some C -> 
    htstep (pu, (api_spec, int_spec, get_hprio_d)) t d C cst O C' cst' O' act ->
    ct_ex_prio_dom_eq O O'. 
Proof.
  introv Hgoodcli Hrc Hnintr Hgct HC Hsp.
  lets H__: reachable_htstep_ct_same_pp Hgoodcli Hrc Hnintr; eauto.
  specializes H__; eauto.
  simpljoin.  
  eapply ctid_same_prio_preserved_dest; eauto. 
Qed. 
