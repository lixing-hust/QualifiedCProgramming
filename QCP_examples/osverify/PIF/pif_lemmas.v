
Require Import base_tac. 
Require Import PIF_memory. 
Require Import PIF_language.
Require Import succ_gen.
Require Import PIF_sys.
Require Import init_and_inv_PIF.
Require Import mux_succ_gen.

Set Keyed Unification.

Lemma join_get_same_l:
  forall (O0 O0' O O' Of: osabst) x, 
    join O0 Of O ->
    join O0' Of O' ->
    get O0 x = get O0' x ->
    get O x = get O' x.
Proof.
  introv Hjo Hjo' Hg.
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

Lemma abt_no_succ:
  forall cd, 
    has_succ (ABORT) cd -> cd = ABORT.
Proof.
  introv Hhsabt.
  inverts Hhsabt.
  auto.
  inverts H.
Qed. 




Definition mutinfo_ex_impl O O' :=  
  (exists mls', get O' absmutinfoid = Some (absmutinfo mls'))
  -> (exists mls, get O absmutinfoid = Some (absmutinfo mls)). 

Definition ptinfo_ex_impl O O' :=
  (exists ptbl', get O' absptlsid = Some (absptls ptbl'))
  -> (exists ptbl, get O absptlsid = Some (absptls ptbl)). 

Set Keyed Unification.

Lemma mutinfo_eq_impl:
  forall O O',
    get O absmutinfoid = get O' absmutinfoid -> 
    mutinfo_ex_impl O O'. 
Proof.
  introv Heq.
  unfolds; introv Hex.
  destruct Hex as (mls' & H').
  exists mls'.
  congruence. 
Qed.   

Lemma ptls_eq_impl:
  forall O O',
    get O absptlsid = get O' absptlsid ->
    ptinfo_ex_impl O O'. 
Proof.
  introv Heq.
  unfolds; introv Hex.
  destruct Hex as (ptbl' & Hg').
  exists ptbl'. rewrite Heq. auto. 
Qed. 

Lemma good_dt_preserve0:
  forall O O', 
    GOOD_DT O ->
    get O abstcblsid = get O' abstcblsid ->
    get O absecblsid = get O' absecblsid ->    
    mutinfo_ex_impl O O' ->
    ptinfo_ex_impl O O' -> 
    GOOD_DT O'. 
Proof.
  introv Hgdt Hgteq Hgeeq Hmi Hpi.
  unfold GOOD_DT in *.
  introv Hge Hgt Hgm Hgp.
  unfolds in Hmi.
  unfolds in Hpi.
  unfold get in Hgteq, Hgeeq.
  unfold AMap in Hgteq, Hgeeq. 
  assert (exists mls', get O' absmutinfoid = Some (absmutinfo mls')).
  {  eexists; eauto. }
  specializes Hmi; eauto.
  assert (exists ptbl', get O' absptlsid = Some (absptls ptbl')).
  { eexists; eauto. } 
  specializes Hpi; eauto. 
  simpljoin. 
  specializes Hgdt; eauto.
  congruence.
  congruence.
Qed.   

Lemma good_dt_preserve00:
  forall O O', 
    GOOD_DT O ->
    get O abstcblsid = get O' abstcblsid ->
    get O absecblsid = get O' absecblsid ->    
    get O absmutinfoid = get O' absmutinfoid ->
    get O absptlsid = get O' absptlsid ->  
    GOOD_DT O'. 
Proof.
  introv Hgdt Heqt Heqe Heqm Heqp.
  eapply good_dt_preserve0; eauto.
  {
    unfolds. 
    introv Hex.
    simpljoin.
    exists x.
    rewrite Heqm.
    auto.
  }
  {
    unfolds.
    introv Hex.
    simpljoin.
    exists x.
    rewrite Heqp. 
    auto.
  }
Qed. 

Lemma pif_preserve0:
  forall O O', 
    PIF O ->
    get O abstcblsid = get O' abstcblsid ->
    get O absecblsid = get O' absecblsid ->   
    get O curtid = get O' curtid -> 
    mutinfo_ex_impl O O' ->
    ptinfo_ex_impl O O' -> 
    PIF O'. 
Proof.
  introv Hpif Hgteq Hgeeq Hgceq Hmi Hpi.
  unfold PIF in *.
  introv Hge Hgt Hgc_ Hgm Hgp.
  introv Hgo Hhr Hno Hneq Hnn Hgo' Hwt.
  unfolds in Hmi.
  unfolds in Hpi.
  unfold get in Hgteq, Hgeeq, Hgceq.
  unfold AMap in Hgteq, Hgeeq, Hgceq. 
  assert (exists mls', get O' absmutinfoid = Some (absmutinfo mls')).
  { eexists; eauto. }
  specializes Hmi; eauto.
  assert (exists ptbl', get O' absptlsid = Some (absptls ptbl')).
  { eexists; eauto. } 
  specializes Hpi; eauto. 
  simpljoin.
  eapply Hpif with (ct:=ct); eauto. 
  congruence.
  congruence.
  congruence.   
Qed.   

Lemma pif_preserve00:
  forall O O', 
    PIF O ->
    get O abstcblsid = get O' abstcblsid ->
    get O absecblsid = get O' absecblsid ->    
    get O absmutinfoid = get O' absmutinfoid ->
    get O absptlsid = get O' absptlsid ->  
    get O curtid = get O' curtid -> 
    PIF O'. 
Proof.
  introv Hpif Heqt Heqe Heqm Heqp Hgc.
  eapply pif_preserve0; eauto.
  {
    unfolds. 
    introv Hex.
    simpljoin.
    exists x.
    rewrite Heqm.
    auto.
  }
  {
    unfolds.
    introv Hex.
    simpljoin.
    exists x.
    rewrite Heqp. 
    auto.
  }
Qed. 

