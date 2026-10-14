
Set Keyed Unification.

Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import prt_apispecs. 
Require Import osspecs. 
Require Import properties.
Require Import spec_aux_defs.
Require Import if_assms.

Require Import if_succ_gen. 

Definition no_common_fid (pu: progunit) (spc: osspec) :=
  forall f aspc ispc sc,
    pu f <> None -> spc = (aspc, ispc, sc) -> aspc f <> None -> False. 

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

Ltac gamma_contra r := 
  match goal with H: r _ _ _ _ |- _ => unfolds in H; simpljoin; tryfalse end.

Ltac step_contra0 := 
  match goal with H: spec_step _ _ _ _ _ _ |- _ => inverts H end.

Ltac step_contra f := 
  match goal with H: spec_step _ _ _ _ _ _ |- _ => inverts H end; 
  try (gamma_contra f; fail).

Ltac l_rew21_inv1 trm :=
  match goal with
    H1: trm = _, H2: trm = _ |- _ =>
      rewrite H2 in H1; inverts H1
  end.

Ltac l_rew12_inv2 trm :=
  match goal with
    H1: trm = _, H2: trm = _ |- _ =>
      rewrite H1 in H2; inverts H2
  end.

Lemma prio_unique:
  forall O pr t pr', task_prio_id O pr t -> task_prio_id O pr' t -> pr = pr'.
Proof.
  introv Htpi Htpi'.
  unfold task_prio_id in *.
  simpljoin.
  rewrite H0 in H.
  inverts H.
  rewrite H2 in H1.
  inverts H1.
  auto.
Qed.   

Lemma abt_succs_contra: 
  forall cd i, 
    nth_error (get_all_succs (ABORT)) i = Some cd ->
    cd = ABORT.
Proof.
  induction i. 
  introv H.
  simpl in H. inverts H. auto.
  introv H.
  simpl in H.
  rewrite nth_error_nil in H. tryfalse.
Qed.



Lemma beq_tid_true : forall t, beq_tid t t = true.
Proof.
  intros.
  unfolds; destruct t.
  rewrite beq_pos_Pos_eqb_eq.
  rewrite Pos.eqb_refl.
  rewrite Int.eq_true.
  simpl; auto.
Qed.

Lemma beq_tid_true_eq: forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
Proof.
  intros.
  unfolds in H; destruct t1; destruct t2.
  apply andb_true_iff in H; destruct H.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Pos.eqb_eq in H.
  pose proof Int.eq_spec i i0.
  rewrite H0 in H1.
  substs; auto.
Qed.

Lemma remove_tid_nin_eq:
  forall wls a, ~(In a wls) -> remove_tid a wls = wls.
Proof.
  induction wls.
  simpl. auto.
  intros.
  eapply not_in_cons in H.
  destruct H.
  simpl.
  destruct (beq_tid a0 a) eqn: eq1.
  eapply beq_tid_true_eq in eq1; subst.
  tryfalse.
  eapply IHwls in H0.
  rewrite H0. auto.
Qed.

Lemma distinct_sub2:
  forall t a ws, 
    distinct (t::a::ws) ->
    distinct (t::ws).
Proof.
  introv Hds.
  unfold distinct in *.
  introv Hn1 Hn2 Hneq.
  casetac i 0%nat Ht Hf.
  -
    subst.  simpl in Hn1. inverts Hn1.
    specialize (Hds 0%nat (S j) t1 t2).
    simpl in Hds.
    eapply Hds; eauto.
    destruct j.
    false.
    simpl.
    simpl in Hn2.
    auto.
  -
    destruct i.
    false.
    simpl in Hn1.
    casetac j 0%nat Htt Hff.
    +
      subst.
      simpl in Hn2.
      inverts Hn2.
      specialize (Hds (S (S i)) 0%nat t1 t2).
      simpl in Hds.
      eapply Hds; eauto.
    +
      destruct j.
      false.
      simpl in Hn2.
      specialize (Hds (S (S i)) (S (S j)) t1 t2).
      simpl in Hds.
      eapply Hds; eauto. 
Qed.                 


Lemma distinct_in_contr:
  forall ws t, 
    distinct (t :: ws) -> In t ws -> False.
Proof. 
  induction ws.
  intros. simpl in H0. false.
  introv Hds Hin.
  simpl in Hin.
  destruct Hin.
  subst.
  unfolds in Hds.
  specialize (Hds 0%nat 1%nat t t).
  simpl in Hds.
  eapply Hds; eauto.
  assert (distinct (t :: ws)).
  { eapply distinct_sub2; eauto. } 
  eapply IHws; eauto.
Qed. 

Lemma distinct_sub1:
  forall a ws, 
    distinct (a::ws) -> 
    distinct ws. 
Proof.
  introv Hds.
  unfold distinct in *.
  introv Hnth1 Hnth2 Hneq.
  specialize (Hds (S i) (S j) t1 t2).
  eapply Hds; eauto. 
Qed. 

Lemma rm_len: 
  forall ws t, 
    In t ws ->
    distinct ws -> 
    (length (remove_tid t ws) = length ws - 1)%nat.
Proof.
  induction ws.
  intros.
  - 
    simpl in H. false.
  -
    introv Hin Hds.
    simpl in Hin.            
    
    destruct Hin as [Hhd | Htl].
    + subst. simpl.
      asserts_rewrite (beq_tid t t = true). 
      { apply beq_tid_true. }
      assert (~In t ws).
      { introv Hf. eapply distinct_in_contr; eauto. }
      rewrite remove_tid_nin_eq; auto.
      auto with arith.
    +
      casetac t a Ht Hf.
      *
        subst. unfolds in Hds.
        eapply In_nth in Htl; eauto.
        simpljoin.
        assert (nth_error ws x = Some a).
        { rewrite <- H0.
          eapply nth_error_nth' ; eauto. }
        specialize (Hds 0%nat (S x) a a). 
        simpl in Hds.
        false.
        eapply Hds; eauto.
      *
        simpl.
        asserts_rewrite (beq_tid t a = false).
        {
          destruct (beq_tid t a) eqn: E.
          apply beq_tid_true_eq in E. subst. false. auto.
        }
        simpl.
        apply distinct_sub1 in Hds.
        specializes IHws; eauto.
        rewrite IHws.
        destruct ws.
        ** simpl in Htl. false.
        ** simpl. auto with arith.

           Unshelve.
           trivial.
Qed.                  

Lemma in_remove_tid_false :
  forall l tid, In tid (remove_tid tid l) -> False.
Proof.
  inductions l; intros.
  simpl in H; auto.
  simpl in H.
  destruct (beq_tid tid a) eqn : eq1.
  eapply IHl; eauto.
  simpl in H; destruct H.
  substs.
  rewrite beq_tid_true in eq1; tryfalse.
  eapply IHl; eauto.
Qed.


Lemma in_remove_in: forall tid t wl, In tid (remove_tid t wl) -> In tid wl.
Proof.
  intros.
  gen tid t H.
  inductions wl; intros.
  simpl in H; auto.
  simpl in H.
  destruct (beq_tid t a) eqn : eq1.
  simpl.
  apply IHwl in H.
  auto.
  simpl in H.
  destruct H.
  simpl.
  left; auto.
  apply IHwl in H.
  simpl; right; auto.
Qed.

Lemma in_remove_tid' : forall l t1 t2, In t1 l -> t1 <> t2 -> In t1 (remove_tid t2 l).
Proof.
  inductions l ; intros.
  simpl in H; tryfalse.
  simpl in H.
  destruct H; substs.
  simpl.
  destruct(beq_tid t2 t1) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; tryfalse.
  simpl; auto.
  simpl.
  destruct(beq_tid t2 a) eqn : eq1.
  eapply IHl; eauto.
  simpl.
  right.
  eapply IHl; eauto.
Qed.

Lemma gethwait_in:
  forall x ws t, 
    GetHWait x ws t -> In t ws. 
Proof.
  intros.
  unfolds in H.
  simpljoin.
  auto.  
Qed.   

Definition prio_preserved_d td O O' :=
  forall pr t,
    dom_for_prio pr = td ->
    (task_prio_id O pr t <-> task_prio_id O' pr t). 

Definition prio_preserved O O' :=
  forall td, prio_preserved_d td O O'. 

Lemma tps_tst_corr_preserve: 
  forall O O' tps, 
    tps_tst_corr O tps ->
    prio_preserved O O' -> 
    dom_impl O O' -> 
    tps_tst_corr O' tps.
Proof.
  introv Httc Hpp.
  unfold tps_tst_corr in *.
  unfolds in Hpp.
  unfold prio_preserved_d in Hpp.
  destruct Httc as (tls & Hget & Htp & Htl).
  introv Hdi.
  unfolds in Hdi.
  specialize (Hdi abstcblsid).
  rewrite Hget in Hdi.
  destruct Hdi as (tls' & Hg').
  eexists.
  split; eauto.
  split.
  - introv Hgt'.
    specialize (Hpp (dom_for_prio p0) p0 t eq_refl).
    assert (Htpi': task_prio_id O' p0 t).
    {
      unfolds. do 5 eexists. split; eauto. 
    }
    apply Hpp in Htpi'.
    unfolds in Htpi'.
    simpljoin.
    l_rew21_inv1 (get O abstcblsid).
    specializes Htp; eauto.
  - introv Hgtp.
    lets H__: Htl Hgtp; eauto.
    simpljoin.
    assert (Htpi: task_prio_id O p0 t).
    {
      unfolds. do 5 eexists; eauto. 
    }
    specialize (Hpp (dom_for_prio p0) p0 t eq_refl).
    apply Hpp in Htpi.
    unfolds in Htpi.
    simpljoin.
    l_rew21_inv1 (get O' abstcblsid).
    do 4 eexists. eauto.
Qed.


Lemma join_get_same_l:
  forall (O0 O0' O O' Of: osabst) x, 
    get O0 x = get O0' x ->
    join O0 Of O ->
    join O0' Of O' ->
    get O x = get O' x.
Proof.
  introv Hg Hjo Hjo'.
  assert ((exists z, get O0 x = Some z) \/ get O0 x = None).
  {
    destruct (get O0 x) eqn: E.
    left. eexists; eauto. right; auto.
  }
  destruct H.
  -
    simpljoin.
    rewrite H in Hg.
    assert (Hg': get O' x = Some x0).
    {
      symmetry in Hg.
      eapply join_get_get_l; eauto. 
    }
    rewrite Hg'.
    eapply join_get_get_l; eauto.
  -
    assert (get O x = get Of x).
    {
      eapply map_join_get_none; eauto. 
    }
    assert (get O' x = get Of x).
    {
      rewrite H in Hg; symmetry in Hg.
      eapply map_join_get_none; eauto. 
    }
    congruence. 
Qed.
