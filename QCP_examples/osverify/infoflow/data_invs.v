
Require Import memory. 
Require Import if_language. 
Require Import if_opsem.
Require Import join_lib.
Require Import properties. 

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

Set Keyed Unification.

Lemma join_eqdom0_eqdom0 :
  forall O O' O1 O2' O2 , 
    join O O1 O2 ->
    join O' O1 O2'->
    eqdomO0 O O' -> 
    eqdomO0 O2 O2'.
Proof.
  unfold eqdomO0 in *; intros.
  destruct H1 as (Hlr & Hrl).
  split.
  -
    unfold dom_impl in *.
    intro x.
    specialize (Hlr x). specialize (Hrl x).
    destruct (get O2 x) eqn: E.
    assert (Hor: get O x = Some a \/ get O1 x = Some a).
    { eapply join_get_or; eauto. }
    destruct Hor as [Hget1 | Hget2].
    + rewrite Hget1 in Hlr.
      destruct a;
        try (simpljoin; eexists; eapply join_get_l; eauto).
    +
      destruct a; 
        try (eexists; eapply join_get_r; eauto).
    +
      assert (Hnone: get O x = None /\ get O1 x = None).
      { eapply join_get_none_rev; eauto. }
      destruct Hnone as (Hg1 & Hg2).
      rewrite Hg1 in Hlr. 
      assert (get O2' x = get O1 x).
      { eapply map_join_get_none; eauto. }
      rewrite H1. auto.
  -
    unfold dom_impl in *.
    intro x.
    specialize (Hlr x). specialize (Hrl x).
    destruct (get O2' x) eqn: E.
    assert (Hor: get O' x = Some a \/ get O1 x = Some a).
    { eapply join_get_or; eauto. }
    destruct Hor as [Hget1 | Hget2].
    + rewrite Hget1 in Hrl.
      destruct a;
        try (simpljoin; eexists; eapply join_get_l; eauto).
    +
      destruct a; 
        try (eexists; eapply join_get_r; eauto).
    +
      assert (Hnone: get O' x = None /\ get O1 x = None).
      { eapply join_get_none_rev; eauto. }
      destruct Hnone as (Hg1 & Hg2).
      rewrite Hg1 in Hrl.
      assert (get O2 x = get O1 x).
      { eapply map_join_get_none; eauto. }
      rewrite H1. auto.
    
Qed.     
  

(* same lemma as in framework/proof/step_prop.v *) 
Lemma eqdomO0_refl :
  forall O, eqdomO0 O O.
Proof.
  intros; unfolds.
  split.
  unfolds.
  intro x.
  destruct (get O x) eqn: E.
  destruct a eqn: E'; try (eexists; eauto).
  auto.
  unfolds.
  intro x.
  destruct (get O x) eqn: E.
  destruct a eqn: E'; try (eexists; eauto).
  auto.
Qed.

Lemma spec_step_eqdomo0:
  forall sd O O' c c' act,
    spec_step sd c O c' O' act -> eqdomO0 O O'.
Proof.
  intros.
  inductions H.
  eapply join_eqdom0_eqdom0; eauto.
  unfold eqdomO in H0. simpljoin. auto.

  (* the case where a primitive abs op yields None *)
  apply eqdomO0_refl.
  auto.
  apply eqdomO0_refl.
  auto.
  auto.
  auto.
  apply eqdomO0_refl.
  apply eqdomO0_refl.
  apply eqdomO0_refl.
  apply eqdomO0_refl.
  apply eqdomO0_refl.
  apply eqdomO0_refl.
  apply eqdomO0_refl.
  apply eqdomO0_refl.
Qed.

Lemma hapistep_eqdomO0 :
  forall A C C' O O' act,
    hapistep A C O C' O' act -> eqdomO0 O O'.
Proof.
  intros.
  inversion H; substs;
  try(apply eqdomO0_refl).
  eapply spec_step_eqdomo0; eauto.
Qed.

Lemma htstep_eqdomO0 :
  forall p t C C' cst cst' O O' td act,
    htstep p t td C cst O C' cst' O' act -> eqdomO0 O O'.
Proof.
  intros.
  inversion H; substs.
  apply eqdomO0_refl. 
  eapply hapistep_eqdomO0; eauto.
Qed.
  
Lemma htistep_eqdomO0 :
  forall ispec C C' O O',
    htistep ispec C O C' O' -> eqdomO0 O O'. 
Proof.
  intros.
  inversion H; substs.
  apply eqdomO0_refl.
Qed.

Lemma set_eqdomO0_curt:
  forall O x a a',
    get O x = Some (oscurt a) ->
    eqdomO0 O (set O x (oscurt a')).
Proof.
  introv Hget.
  unfolds.
  split.
  +
    unfolds; intro x0.    
    casetac x x0 He Hne.
    * subst. rewrite set_a_get_a.
      rewrite Hget. eexists; eauto.
    * rewrite set_a_get_a'; eauto.
      destruct (get O x0) eqn: E.
      destruct a0 eqn: E'; 
        try (eexists; eauto).
      auto.
  +
    unfolds; intro x0.
    casetac x x0 He Hne.
    * subst.
      rewrite set_a_get_a.
      eexists; eauto.
    * rewrite set_a_get_a'; eauto.
      destruct (get O x0) eqn: E.
      destruct a0 eqn: E';
        try (eexists; eauto).
      auto.
Qed.

Lemma set_eqdomO0_tcblist: 
  forall O x a a',
    get O x = Some (abstcblist a) ->
    eqdomO0 O (set O x (abstcblist a')).
Proof.
  introv Hget.
  unfolds.
  split.
  +
    unfolds; intro x0.    
    casetac x x0 He Hne.
    * subst. rewrite set_a_get_a.
      rewrite Hget. eexists; eauto.
    * rewrite set_a_get_a'; eauto.
      destruct (get O x0) eqn: E.
      destruct a0 eqn: E'; 
        try (eexists; eauto).
      auto.
  +
    unfolds; intro x0.
    casetac x x0 He Hne.
    * subst.
      rewrite set_a_get_a.
      eexists; eauto.
    * rewrite set_a_get_a'; eauto.
      destruct (get O x0) eqn: E.
      destruct a0 eqn: E';
        try (eexists; eauto).
      auto.
Qed.
  
Lemma hpstep_eqdomO0: 
  forall hp T cst O T' cst' O' act, 
    hpstep hp T cst O T' cst' O' act ->
    eqdomO0 O O'. 
Proof.
  introv Hstep.
  inverts Hstep.
  - 
    eapply htstep_eqdomO0; eauto.    
  -
    eapply htistep_eqdomO0; eauto.
  -
    eapply set_eqdomO0_curt; eauto.
Qed. 

Lemma eqdomO0_trans:
  forall O1 O2 O3,
    eqdomO0 O1 O2 ->
    eqdomO0 O2 O3 ->
    eqdomO0 O1 O3.
Proof.
  introv He1 He2.
  unfold eqdomO0 in *.
  simpljoin.
  split.
  -
    unfold dom_impl in H1, H.
    unfold dom_impl.
    intro x.
    specialize (H1 x).
    specialize (H x).
    destruct (get O1 x) eqn: E.
    destruct a eqn: E'; 
      try (destruct H1 as (y & Hg2); 
           rewrite Hg2 in H; 
           simpljoin; eexists; eauto).
    rewrite H1 in H; auto.
  -
    unfold dom_impl in H2, H0.
    unfold dom_impl.
    intro x.
    specialize (H2 x).
    specialize (H0 x).
    destruct (get O3 x) eqn: E.
    destruct a eqn: E'; 
      try (destruct H0 as (y & Hg2); 
           rewrite Hg2 in H2; 
           simpljoin; eexists; eauto).
    rewrite H0 in H2; auto.
Qed.     
  
Lemma hpstepokstar_eqdomO0:
  forall hp T cst O T' cst' O', 
    hpstepokstar hp T cst O T' cst' O' ->
    eqdomO0 O O'. 
Proof.
  intros.
  inductions H; intros; auto.
  -
    lets H_: eqdomO0_refl O.
    unfolds in H_. unfolds.  simpljoin. auto.
  -
    inverts H.
    lets H_: hpstep_eqdomO0 H1.
    eapply eqdomO0_trans; eauto.
Qed. 

Lemma reachable_get_bufsid:
  forall hp T cst O, 
    reachable hp T cst O ->
    exists x y,
      get O ibufsid = Some (ibufs x) /\ get O obufsid = Some (obufs y). 
Proof.
  introv Hrc.
  unfolds in Hrc.
  simpljoin.
  lets H_: hpstepokstar_eqdomO0 H1.
  unfold init in H0.
  destruct H0 as (Hinittsk & Hinitst).
  unfolds in Hinitst.
  simpljoin.
  unfold init_buf_st in H6.
  simpljoin.
  unfold eqdomO0 in H_.
  assert (H__ := H_).
  destruct H_ as (H12 & _).
  specialize (H12 ibufsid).
  rewrite H6 in H12. 
  destruct H__ as (H12' & _).
  specialize (H12' obufsid).
  rewrite H8 in H12'.
  simpljoin.
  do 2 eexists.
  splits; eauto.
Qed. 

Lemma reachable_get_knldataid:
  forall hp T cst O,
    reachable hp T cst O ->
    exists x1 x2 x3 x4 x5 x6, 
      get O abstcblsid = Some (abstcblist x1) /\ 
        get O absmqattrid = Some (absmqattr x2) /\
        get O absecblsid = Some (absecblist x3) /\
        get O osdomainportid = Some (osdomainport x4) /\
        get O oskportid = Some (oskport x5) /\ 
        get O cspaceid = Some (capcspace x6).  
Proof.
  introv Hrc.
  unfolds in Hrc.
  simpljoin.
  lets H_: hpstepokstar_eqdomO0 H1.
  unfold init in H0.
  destruct H0 as (Hinittsk & Hinitst).
  unfolds in Hinitst.
  simpljoin.
  unfold init_tsk_st, init_evt_st, init_prt_st, init_cap_st in *.
  simpljoin.
  
  unfold eqdomO0 in H_.
  destruct H_ as (H1_2 & _).
  assert (H1_2' := H1_2).
  assert (H1_2'' := H1_2).
  assert (H1_2''' := H1_2).
  assert (H1_2'''' := H1_2).
  assert (H1_2''''' := H1_2). 
  specialize (H1_2 abstcblsid).
  unfold get in H1_2. unfold AMap in H1_2. 
  rewrite H3 in H1_2.
  specialize (H1_2' absmqattrid).
  unfold get in H1_2'. unfold AMap in H1_2'.
  rewrite H4 in H1_2'. 
  specialize (H1_2'' absecblsid). 
  unfold get in H1_2''. unfold AMap in H1_2''.
  rewrite H11 in H1_2''.
  specialize (H1_2''' osdomainportid). 
  unfold get in H1_2'''. unfold AMap in H1_2'''.
  rewrite H10 in H1_2'''.
  specialize (H1_2'''' oskportid). 
  unfold get in H1_2''''. unfold AMap in H1_2''''.
  rewrite H5 in H1_2''''.
  specialize (H1_2''''' cspaceid).
  rewrite H7 in H1_2'''''.

  simpljoin.
  do 6 eexists. 
  splits; eauto.
Qed. 



      
