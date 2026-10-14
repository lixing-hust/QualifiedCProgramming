
Require Import log_language.
Require Import log_opsem.
Require Import base_tac. 
Require Import mq_succ_gen.

Require Import FIFO_inv_and_init. 

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

Lemma abt_no_succ:
  forall cd, 
    has_succ (ABORT) cd -> cd = ABORT.
Proof.
  introv Hhsabt.
  inverts Hhsabt.
  auto.
  inverts H.
Qed. 

Lemma fifo_ext_preserve00:
  forall O O', 
    FIFO_ext O ->
    get O absecblsid = get O' absecblsid ->    
    get O loglsid = get O' loglsid ->
    get O mqcntid = get O' mqcntid ->  
    FIFO_ext O'. 
Proof.
  introv Hfe Hgee Hgel Hgem.
  unfold FIFO_ext in *.
  introv Hgl' Hlgeq Hnc Hnd Hge'.
  introv Hgeid Hgcnt.
  rewrite <- Hgee in Hge'.
  rewrite <- Hgel in Hgl'.
  rewrite <- Hgem in Hgcnt.
  specializes Hfe; eauto.
Qed.
