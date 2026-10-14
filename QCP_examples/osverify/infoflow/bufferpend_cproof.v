
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import buffer_apispecs. 
Require Import osspecs. 
Require Import properties.

Require Import if_assms.
Require Import sem_prop.
Require Import if_succ_gen.
Require Import if_common_lemmas. 
Require Import spec_aux_defs. 
Require Import confidentiality_tactics.
Require Import confidentiality_lemmas. 

Require Import FunctionalExtensionality.

Require Import math_auto. 
Require Import seplog_lemmas. 

Require Import equiv_prop.
Require Import ct_pp_lemmas.
Require Import hasrt_sat_preserve. 
Require Import mqrecv_lemmas.
Require Import ports_cproof_common.
Require Import bufferpost_cproof.
Set Keyed Unification.  

Ltac solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 k :=
  unfolds;
  match type of Hlenvl with length ?vl = _ => exists vl end; 
  match type of Hlenvl1 with length ?vl = _ => exists vl end; 
  match type of Hlenvl2 with length ?vl = _ => exists vl end; 
  exists k%nat; 
  split; [simpl; auto | 
           split; [ simpl; auto | 
                    split;  [ simpl; auto | 
                              split;  [ simpl; auto | 
                                        simpl; auto]]]].

Lemma buffer_equiv_nemp_impl_: 
  forall vp O1 O2 pr,
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qid qls ml n pwl wl msg0,
        vp = Vptr qid /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq (msg0 :: ml) n pwl, wl)) ->
    (exists qid qls ml n pwl wl msg0,
        vp = Vptr qid /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq (msg0 :: ml) n pwl, wl)). 
Proof.
  introv Hbe Hbi Hlen1.
  destruct Hlen1 as (qid & qls & ml & n & pwl & wl & Hvp1  & Hget & Hgetq & Hne).
  unfolds in Hbe.
  unfold buffer_indom in *.
  rem_dis.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  match goal with H: forall _, _ |- _ => specializes H; eauto; destruct H as (Hiff & Ha) end.
  destruct Hiff as (Hlr & Hrl).
  l_rew21_inv1 (get O1 absecblsid).
  specializes Hlr; eauto.
  simpljoin. 
  specializes Ha; eauto.
  destruct Ha as (Hme & Hte).
  unfolds in Hme.
  simpljoin.
  match goal with H: absmsgq _ _ _ = absmsgq _ _ _ |- _ => inverts H end.
  unfolds in H4.
  simpljoin.
  do 7 eexists.
  split; eauto.
Qed.

Lemma buffer_equiv_nil_impl_: 
  forall vp O1 O2 pr,
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qid qls n pwl wl,
        vp = Vptr qid /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq nil n pwl, wl)) ->
    (exists qid qls n pwl wl,
        vp = Vptr qid /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq nil n pwl, wl)). 
Proof.
  introv Hbe Hbi Hlen1.
  destruct Hlen1 as (qid & qls  & n & pwl & wl & Hvp1  & Hget).
  unfolds in Hbe.
  unfold buffer_indom in *.
  rem_dis.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  match goal with H: forall _, _ |- _ => specializes H; eauto; destruct H as (Hiff & Ha) end.
  destruct Hiff as (Hlr & Hrl).
  l_rew21_inv1 (get O1 absecblsid).
  specializes Hlr; eauto.
  simpljoin. 
  specializes Ha; eauto.
  destruct Ha as (Hme & Hte).
  unfolds in Hme.
  simpljoin.
  match goal with H: absmsgq _ _ _ = absmsgq _ _ _ |- _ => inverts H end.
  unfolds in H6.
  simpljoin.
  do 5 eexists.
  split; eauto.
Qed.

Lemma qpend_npsb_succ_mqref_preserve: 
  forall v  O v' v1 O' O0 O0' Of act, 
    qpend_get_no_pwl_succ_body (v :: v1 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    hasrt_sat_preserve.mq_ref_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get O0 absmqattrid = Some (absmqattr mqs)
               \/ get Of absmqattrid = Some (absmqattr mqs)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=absmqattrid) (b:=absmqattr mqs) in Hjo'; eauto.
    2: { 
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf.
    }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto. 
  -
    assert (get O' absmqattrid = Some (absmqattr mqs)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto. 
Qed.

Lemma qpend_npsb_succ_qprt_preserve: 
  forall v v1 O v' O' O0 O0' Of act, 
    qpend_get_no_pwl_succ_body ( v :: v1 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    hasrt_sat_preserve.qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get O0 osdomainportid = Some (osdomainport dpl)
               \/ get Of osdomainportid = Some (osdomainport dpl)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=osdomainportid) (b:=osdomainport dpl) in Hjo'; eauto.
    2: {
      repeat rewsimp. auto.
    }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
  -
    assert (get O' osdomainportid = Some (osdomainport dpl)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
Qed.

Lemma join_get_set_eq_1
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) ,
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    join (set O1 a b')  O2 O' ->
   O' = (set O a b').
Proof.
  intros.
  repeat progress(eapply join_set_l_rev in H2; eauto; simpljoin).
  eapply map_join_deter in H0; eauto.
  subst; auto.
Qed.

Lemma qpend_npsb_succ_csp_preserve: 
  forall v v1 O v' O' O0 O0' Of act, 
    qpend_get_no_pwl_succ_body ( v :: v1 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid. 
Proof.
  introv Hpost Hj1 Hj1'.
  unfolds in Hpost. simpljoin.
  destruct H7;simpljoin;tryfalse.
  inverts H5.
  eapply join_get_set_eq_1 in Hj1';eauto.
  inverts Hj1'. clear H4.
  try repeat(rewrite set_a_get_a';[eauto|introv Hfff;tryfalse]).
Qed.

Lemma buffer_equiv_nnil_impl_: 
  forall vp O1 O2 pr,
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qid qls ml n pwl wl msg0,
        vp = Vptr qid /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq (msg0 :: ml) n pwl, wl) /\
          pwl <> nil) ->
    (exists qid qls ml n pwl wl msg0,
        vp = Vptr qid /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq (msg0 :: ml) n pwl, wl) /\
          pwl <> nil). 
Proof.
  introv Hbe Hbi Hlen1.
  destruct Hlen1 as (qid & qls & ml & n & pwl & wl & Hvp1  & Hget & Hgetq & Hne).
  unfolds in Hbe.
  unfold buffer_indom in *.
  rem_dis.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  match goal with H: forall _, _ |- _ => specializes H; eauto; destruct H as (Hiff & Ha) end.
  destruct Hiff as (Hlr & Hrl).
  l_rew21_inv1 (get O1 absecblsid).
  specializes Hlr; eauto.
  simpljoin. 
  specializes Ha; eauto.
  destruct Ha as (Hme & Hte).
  unfolds in Hme.
  simpljoin.
  match goal with H: absmsgq _ _ _ = absmsgq _ _ _ |- _ => inverts H end.
  unfolds in H6.
  simpljoin.
  do 7 eexists.
  split; eauto.
  split. eauto.
  split. eauto.
  destruct x6. tryfalse.
  destruct x7. tryfalse.
  eapply hd_error_some_nil.
  simpl.
  eauto.
Qed.

Lemma buffer_equiv_pwlnil_impl_: 
  forall vp O1 O2 pr,
    buffer_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom vp O1 pr -> 
    (exists qid qls ml n wl msg0,
        vp = Vptr qid /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq (msg0 :: ml) n nil, wl)) ->
    (exists qid qls ml n wl msg0,
        vp = Vptr qid /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq (msg0 :: ml) n nil, wl)). 
Proof.
  introv Hbe Hbi Hlen1.
  destruct Hlen1 as (qid & qls & ml & n  & wl & Hvp1  & Hget & Hgetq & Hne).
  unfolds in Hbe.
  unfold buffer_indom in *.
  rem_dis.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  match goal with H: forall _, _ |- _ => specializes H; eauto; destruct H as (Hiff & Ha) end.
  destruct Hiff as (Hlr & Hrl).
  l_rew21_inv1 (get O1 absecblsid).
  specializes Hlr; eauto.
  simpljoin. 
  specializes Ha; eauto.
  destruct Ha as (Hme & Hte).
  unfolds in Hme.
  simpljoin.
  match goal with H: absmsgq _ _ _ = absmsgq _ _ _ |- _ => inverts H end.
  unfolds in H4.
  simpljoin. inverts H0. destruct x7. 2:simpl in H5;tryfalse.
  do 7 eexists.
  split; eauto.
  split. eauto. eauto.
Qed.

Lemma qpend_exwt_succ_mqref_preserve: 
  forall v i O v' O' O0 O0' Of act, 
    qpend_get_ex_pwl_before_sched_body (v :: i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    hasrt_sat_preserve.mq_ref_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get O0 absmqattrid = Some (absmqattr mqs)
               \/ get Of absmqattrid = Some (absmqattr mqs)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=absmqattrid) (b:=absmqattr mqs) in Hjo'; eauto.
    2: { 
      rewrite set_a_get_a'; eauto.
      2: introv Hf; inverts Hf.
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf.
    }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto. 
  -
    assert (get O' absmqattrid = Some (absmqattr mqs)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto. 
Qed.

Lemma qpend_exwt_succ_qprt_preserve: 
  forall v i O v' O' O0 O0' Of act, 
    qpend_get_ex_pwl_before_sched_body ( v :: i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    hasrt_sat_preserve.qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get O0 osdomainportid = Some (osdomainport dpl)
               \/ get Of osdomainportid = Some (osdomainport dpl)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=osdomainportid) (b:=osdomainport dpl) in Hjo'; eauto.
    2: {
      repeat rewsimp. auto.
    }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
  -
    assert (get O' osdomainportid = Some (osdomainport dpl)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
Qed.

Lemma qpend_exwt_succ_cpid_same:
  forall v i O0 act v' O0' Of O O', 
    qpend_get_ex_pwl_before_sched_body ( v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O cspaceid = get O' cspaceid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed. 
Lemma join_get_set_eq_2
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a a': A) (b b' c c': B) ,
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    join (set(set O1 a b')a' c')  O2 O' ->
   O' = (set(set O a b')a' c').
Proof.
  intros.
  repeat progress(eapply join_set_l_rev in H3; eauto; simpljoin).
  eapply map_join_deter in H0; eauto.
  subst; auto.
Qed.

Lemma qpend_gepb_succ_csp_preserve: 
  forall v v1 O v' O' O0 O0' Of act, 
    qpend_get_ex_pwl_before_sched_body ( v :: v1 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid. 
Proof.
  introv Hpost Hj1 Hj1'.
  unfolds in Hpost. simpljoin.
  destruct H9;simpljoin;tryfalse.
  inverts H6.
  eapply join_get_set_eq_2 in Hj1';eauto.
  inverts Hj1'. 
  try repeat(rewrite set_a_get_a';[eauto|introv Hfff;tryfalse]).
Qed.

Lemma qpend_get_ex_pwl_mqattr_same:
  forall vp  i O0 act v' O0' Of O O', 
    qpend_get_ex_pwl_before_sched_body (vp ::  i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O absmqattrid = get O' absmqattrid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed.

Lemma qpend_get_ex_pwl_prio_preserved: 
  forall vp  i O O' act v' O0 O0' Of, 
    qpend_get_ex_pwl_before_sched_body (vp ::  i :: nil) O0 act (v', Some O0') ->
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
  assert (Hgeq: get O0' abstcblsid = Some (abstcblist (set x2 x12 (x8, rdy, x11, x13, x15)))).
  {
    subst O0'.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a; eauto. 
    introv Hf.
    inverts Hf. 
  }
  assert (Hg1: get O abstcblsid = Some (abstcblist x2)).
  { eapply join_get_get_l; eauto. }
  assert (Hg2: get O' abstcblsid = Some (abstcblist (set x2 x12 (x8, rdy, x11, x13, x15)))). 
  { eapply join_get_get_l; eauto. }
  split; 
    introv Htpi.
  -
    unfold task_prio_id in *.
    simpljoin.
    l_rew21_inv1 (get O abstcblsid).
    casetac x12 t Ht Hf.
    + subst. l_rew21_inv1 (get x2 t).
      do 5 eexists. split; eauto.
      rewrite set_a_get_a. eauto.
    + do 5 eexists. split; eauto.
      rewrite set_a_get_a'; eauto. 
  -
    unfold task_prio_id in *.
    simpljoin.
    l_rew21_inv1 (get O' abstcblsid).
    casetac x12 t Ht Hf.
    + subst. rewrite set_a_get_a in H6. inverts H6.
      do 5 eexists.
      split; eauto. 
    + rewrite set_a_get_a' in H6; eauto.
      do 5 eexists.
      split; eauto.  
Qed.
 

Lemma be_kte_gethpwait_eq: 
  forall O1 O2 x pr tcbs1 tcbs2 ecbs1 ecbs2
         ms1 ms2 ml1 ml2 pwl1 pwl2 wl1 wl2 t1 t2,
    kernel_task_equiv (dom_for_prio pr) O1 O2 ->
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_indom (Vptr x) O1 pr ->
    get O1 abstcblsid = Some (abstcblist tcbs1) ->
    get O1 absecblsid = Some (absecblist ecbs1) ->
    get O2 abstcblsid = Some (abstcblist tcbs2) ->
    get O2 absecblsid = Some (absecblist ecbs2) ->
    get ecbs1 x = Some (absmsgq ms1 ml1 pwl1, wl1) ->
    get ecbs2 x = Some (absmsgq ms2 ml2 pwl2, wl2) -> 
    GetHWait tcbs1 pwl1 t1 ->
    GetHWait tcbs2 pwl2 t2 ->
    (exists pr0,
        task_prio_id O1 pr0 t1 /\ task_prio_id O2 pr0 t2
        /\ dom_for_prio pr0 = dom_for_prio pr). 
Proof.
  introv Hkte Hbe Hbi Hgt1 Hge1 Hgt2 Hge2.
  introv He1 He2 Hgw1 Hgw2.
  unfolds in Hbe.
  unfolds in Hbi.
  simpljoin.
  rem_dis.
  inv_vptr.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid). 
  specializes H1; eauto.
  destruct H1 as (Hiff & Ha).
  specializes Ha; eauto.
  unfold mq_equiv in Ha.
  simpljoin.
  lets H__: kte_tidls_eq_gethwait_eq Hkte Hgt1 Hgt2 Hgw1 Hgw2.
  specializes H__; eauto.
  {
    introv Hin.  
    lets H__: buffer_part_consistent O1 wl1 pwl1. 
    specializes H__; eauto.
  }
  {
    introv Hin.
    lets H__: buffer_part_consistent O2 wl2 pwl2. 
    specializes H__; eauto. 
  }
  unfolds in H.
  simpljoin. inverts H. inverts H1.
  eauto.
Qed. 

Lemma knl_mq_equiv_pendexwt_preserve2:
  forall td O1 O2 vp  i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr, 
    kernel_data_equiv td O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_indom vp O1 pr -> 
    qpend_get_ex_pwl_before_sched_body (vp ::  i1 :: nil) O10 act (v1, Some O10') ->
    qpend_get_ex_pwl_before_sched_body (vp ::  i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    (kernel_task_equiv td O1' O2').     
Proof.
  introv Hkde Hkte Hbe Hbi Hpost1 Hpost2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  lets Hpp1: qpend_get_ex_pwl_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qpend_get_ex_pwl_prio_preserved Hjo2 Hjo2'; eauto.

  assert (Hkte_ := Hkte).
  unfolds in Hkte.
  simpljoin. 
  assert (Hpost1_:= Hpost1).
  assert (Hpost2_ := Hpost2). 
  inverts Hpost1. 
  inverts Hpost2. 
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  do 2 (match goal with H: Some _ = Some _ |- _ => inversion H; clear H end).
  assert (Hgeq1: get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: qpend_get_ex_pwl_mqattr_same Hpost1_; eauto. 
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: qpend_get_ex_pwl_mqattr_same Hpost2_; eauto. 
  }
  kvext O10 abstcblsid O1.
  kvext O20 abstcblsid O2.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  match goal with
    H: context [set O10 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O1' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto. subst O10'.
    repeat rewsimp. auto. 
  }
  match goal with
    H: context [set O20 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O2' abstcblsid = Some (abstcblist tcbs))
  end.
  {    
    eapply join_get_get_l; eauto. subst O20'.
    repeat rewsimp. auto. 
  }
 
  -
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    unfolds in Hkte.
    destruct Hkte as (tcbs1 & tcbs2 & Hgtcbs1 & Hgtcbs2 & Hall). 
    unfold kernel_task_equiv.    
    do 2 eexists. 
    split; eauto.
    split; eauto.
    introv Hd.
    lets H__: Hall Hd. clear Hall.
    destruct H__ as ((Htpi12 & Htpi21) & Hall).
    split.
    + (* eq. for task_prio_id *) 
      split.
      * 
        introv Htpi1'.
        assert (Hex: exists t, task_prio_id O1 pr0 t).
        {
          destruct Htpi1' as (t_ & Htpi1').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi12 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
      *
        introv Htpi2'.
        assert (Hex: exists t, task_prio_id O2 pr0 t).
        {
          destruct Htpi2' as (t_ & Htpi2').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi21 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
    + 
      introv Hg1' Hg2'.
      assert (Htpi1': task_prio_id O1' pr0 t1).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi2': task_prio_id O2' pr0 t2).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi1_: task_prio_id O1 pr0 t1).
      {
        eapply prio_preserved_tpi; eauto.
      }
      assert (Htpi2_: task_prio_id O2 pr0 t2).
      {
        eapply prio_preserved_tpi; eauto.
      }
      unfolds in Htpi1_. unfolds in Htpi2_.
      simpljoin.
      do 2 l_rew21_inv1 (get O1 abstcblsid).
      do 2 l_rew21_inv1 (get O2 abstcblsid).

      kvext O10 absecblsid O1.
      kvext O20 absecblsid O2. 
      lets H__: be_kte_gethpwait_eq Hkte_ Hbe Hbi.
      specialize(H__ H12 H2 H11 H3).
      specialize(H__ H16 H6 H18 H8).
      

      match goal with
        H1: GetHWait _ _ ?x1, H2: GetHWait _ _ ?x2 |- _ =>
          rename x1 into t1_; rename x2 into t2_
      end.
      destruct H__ as (pr0_ & Htpi1_ & Htpi2_ & Hdd).
      match goal with
        H: get tcbs1 t1_ = Some (_, ?x1) |- _ => rename x1 into pr10
      end.
      match goal with
        H: get tcbs2 t2_ = Some (_, ?x2) |- _ => rename x2 into pr20
      end.
      assert (task_prio_id O1 pr10 t1_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.  
      assert (task_prio_id O2 pr20 t2_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
      assert (Hor: t1_ = t1 /\ t2_ = t2 \/ t1_ <> t1 /\ t2_ <> t2).
      {
        eapply prio_tid_corr_ext; eauto.
      }
      destruct Hor as [(Heq1 & Heq2) | (Hneq1 & Hneq2)].
      * subst.
        rewrite set_a_get_a in Hg1'. inverts Hg1'.
        rewrite set_a_get_a in Hg2'. inverts Hg2'.
        match goal with
          H1: get tcbs1 t1 = _, H2: get tcbs1 t1 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        match goal with
          H1: get tcbs2 t2 = _, H2: get tcbs2 t2 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        specializes Hall; eauto.
        simpljoin.
        splits; auto.
      * rewrite set_a_get_a' in Hg1'; eauto.
        rewrite set_a_get_a' in Hg2'; eauto.
 
Qed. 



Lemma buffer_qpend_get_ex_pwl_before_sched_dteq_preserve2:
  forall td pr v act  rv_post1 rv_post2 cst1 cst2 v1 v2 O1 O2 O1' O2' Of1 Of2 OO1 OO2 OO1' OO2', 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    buffer_equiv (dom_for_prio pr) O1 O2->
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    buffer_indom v O1 pr ->
    buffer_indom v O2 pr -> 
    qpend_get_ex_pwl_before_sched_body (v :: rv_post1 :: nil) OO1 act (v1, Some OO1') -> 
    qpend_get_ex_pwl_before_sched_body (v :: rv_post2 :: nil) OO2 act (v2, Some OO2') -> 
    ports_equiv td O1' O2' /\ buffer_equiv td O1' O2' /\ cap_equiv td O1' O2'/\
    client_data_equiv td cst1 cst2 O1' O2'.
Proof.
  introv Hde Hbufe Hkte Hkme Hjo1 Hjo2 Hjo1' Hjo2'. 
  introv Hmd1 Hmd2 Hpost1 Hpost2. 
  lets Hpost1_:Hpost1.
  lets Hpost2_:Hpost2.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  splits.
  + (* ports_equiv *)
    destructs Hkde. 
    eapply ports_equiv_same_prts_preserve2; eauto.          
    eapply qpend_get_ex_pwl_before_sched_dpid_same; eauto. 
    eapply qpend_get_ex_pwl_before_sched_dpid_same; eauto. 
    eapply qpend_get_ex_pwl_before_sched_kpid_same; eauto.
    eapply qpend_get_ex_pwl_before_sched_kpid_same; eauto.
    eapply qpend_get_ex_pwl_before_sched_same_prt_ecbs; eauto.
    eapply qpend_get_ex_pwl_before_sched_same_prt_ecbs ; eauto.
    eapply qpend_get_ex_pwl_before_sched_dom_impl; eauto.
    eapply qpend_get_ex_pwl_before_sched_dom_impl; eauto.
    eapply qpend_get_expwl_before_sched_prio_preserved with (O0:=OO1); eauto.
    eapply qpend_get_expwl_before_sched_prio_preserved; eauto.
  + (* buffer_equiv *)
    unfolds.
    destruct Hkde as (Hk1 & Hk2 & Hk3 & Hbuf & Hk4).
    lets Hbuf_:Hbuf.
    unfolds in Hbuf.
    unfolds in Hpost1. unfolds in Hpost2.
    simpljoin. 
    lets Hecb1_:H12. lets Htcb1_:H13.
    lets Hecb2_:H2. lets Htcb2_:H3.
    eapply join_get_get_l in H12;eauto.
    eapply join_get_get_l in H13;eauto.
    eapply join_get_get_l in H2;eauto.
    eapply join_get_get_l in H3;eauto.
    lets H':be_kte_gethpwait_eq. inverts H0. inverts H.
    specializes H'. eapply Hkte. eapply Hbufe.
    eapply Hmd1. eapply H13. eapply H12.
    eapply H3. eapply H2. eapply H14.
    eapply H4. eapply H16. eapply H6.

    destruct H11;simpljoin;tryfalse.
    destruct H21;simpljoin;tryfalse.
    inverts H10. inverts H9.
    lets Hjo2_:Hjo2'.
    lets Hjo1_:Hjo1'.
    eapply join_get_set_eq_2 in Hjo2';eauto.
    eapply join_get_set_eq_2 in Hjo1';eauto.
    inverts Hjo1'. inverts Hjo2'.
    clear H. clear H9.
    try repeat (rewrite set_a_get_a).
    do 2 eexists. split. eauto.
    split. eauto.
    introv Hbid.
    lets H__ : H23 Hbid.
    simpljoin.
    rewrite H2 in H22. rewrite H12 in H1.
    inverts H22. inverts H1.
    split.
    casetac eid x Hte Htne.
    2:{
      try repeat (rewrite set_a_get_a';[idtac|introv Hff;tryfalse]).
      eauto.
    }
    {
      subst eid.
      try repeat (rewrite set_a_get_a).
      split. 
      introv Habs. simpljoin. inverts H.
      do 2 eexists. eauto.
      intros. do 2 eexists. eauto.
    }
    introv Habs1 Habs2.
    split.
    {
      unfolds. inverts Habs1. inverts Habs2.
      casetac x eid Hte Htne.
      {
        subst x.
        rewrite set_a_get_a in H11.
        rewrite set_a_get_a in H10.
        inverts H11. inverts H10.
        unfolds in Hkte.
        simpljoin.
        unfolds in H0. unfolds in H5.
        simpljoin.
        rewrite H13 in H0. inverts H0.
        rewrite H3 in H5. inverts H5.
        rewrite H17 in H18. inverts H18.
        rewrite H7 in H15. inverts H15.
        lets H__:H11 H8. destruct H__ as (He & Hfa).
        rewrite H13 in H1. rewrite H3 in H10.
        inverts H1. inverts H10.
        lets H__: Hfa H17 H7.
        simpljoin.
        lets H__:H9 H14 H4.
        destruct H__ as (Hmq1 & Htid1).
        unfolds in Hmq1.
        simpljoin.
        inverts H0. inverts H1.
        do 4 eexists. split. eauto. split. eauto.
        


        unfolds in H16. unfolds in H6.
        simpljoin.
        eapply tidls_equiv_rm_preserve2.
        eapply H5. 
        eapply H10. eapply H0.
        unfolds. do 5 eexists. split;eauto.
        unfolds. do 5 eexists. split;eauto.
        eapply qpend_get_expwl_before_sched_prio_preserved.
        eapply Hpost1_. eauto. eauto.
        eapply qpend_get_expwl_before_sched_prio_preserved.
        eapply Hpost2_. eauto. eauto.
        lets Hdis1:distinct_wait_tids H12  H14. simpljoin.
        eauto.
        lets Hdis2:distinct_wait_tids H2  H4. simpljoin.
        eauto.
      }
      try repeat (rewrite set_a_get_a' in H10;[idtac|introv Hff;tryfalse]).
      try repeat (rewrite set_a_get_a' in H11;[idtac|introv Hff;tryfalse]).
      lets H__:H9 H10 H11.
      destruct H__ as (H1_ & H2_).
      unfolds in H1_.
      simpljoin.
      do 4 eexists. split. eauto. split. eauto.
      
      eapply tidls_equiv_pp_preserve2.
      eapply H18. 
      eapply qpend_get_expwl_before_sched_prio_preserved.
      eapply Hpost1_. eauto. eauto.
      eapply qpend_get_expwl_before_sched_prio_preserved.
      eapply Hpost2_. eauto. eauto.
    }
    {
      inverts Habs1. inverts Habs2.
      casetac x eid Hte Htne.
      {
        subst x.
        rewrite set_a_get_a in H11.
        rewrite set_a_get_a in H10.
        inverts H11. inverts H10.
        unfolds in Hkte.
        simpljoin.
        unfolds in H0. unfolds in H5.
        simpljoin.
        rewrite H13 in H0. inverts H0.
        rewrite H3 in H5. inverts H5.
        rewrite H17 in H18. inverts H18.
        rewrite H7 in H15. inverts H15.
        lets H__:H11 H8. destruct H__ as (He & Hfa).
        rewrite H13 in H1. rewrite H3 in H10.
        inverts H1. inverts H10.
        lets H__: Hfa H17 H7.
        simpljoin.
        lets H__:H9 H14 H4.
        destruct H__ as (Hmq1 & Htid1).
        unfolds in Hmq1.
        simpljoin.
        inverts H0. inverts H1.
        eapply tidls_equiv_pp_preserve2.
        eapply Htid1. 
        eapply qpend_get_expwl_before_sched_prio_preserved.
        eapply Hpost1_. eauto. eauto.
        eapply qpend_get_expwl_before_sched_prio_preserved.
        eapply Hpost2_. eauto. eauto.
      }
      try repeat (rewrite set_a_get_a' in H10;[idtac|introv Hff;tryfalse]).
      try repeat (rewrite set_a_get_a' in H11;[idtac|introv Hff;tryfalse]).
      lets H__:H9 H10 H11.
      destruct H__ as (H1_ & H2_).
      unfolds in H1_.
      simpljoin.
      eapply tidls_equiv_pp_preserve2.
      eapply H2_. 
      eapply qpend_get_expwl_before_sched_prio_preserved.
      eapply Hpost1_. eauto. eauto.
      eapply qpend_get_expwl_before_sched_prio_preserved.
      eapply Hpost2_. eauto. eauto.
    }
  +
    destruct Hkde as (_ & _ & _ & _ & Hcp).
    eapply cap_equiv_preserve2; eauto.
    eapply qpend_get_ex_pwl_before_sched_cpid_same; eauto.
    eapply qpend_get_ex_pwl_before_sched_cpid_same; eauto.

    eapply qpend_get_ex_pwl_before_sched_mqptr_iff; eauto.
    eapply qpend_get_ex_pwl_before_sched_mqptr_iff; eauto.
    
  +
    eapply cde_prio_preserved_preserve2; eauto.
    eapply qpend_get_expwl_before_sched_prio_preserved with (O0:=OO1); eauto.
    eapply qpend_get_expwl_before_sched_prio_preserved; eauto.
Qed.

Lemma buffer_qpend_block_knl_mq_equiv_preserve2:
  forall td O1 O2 vp v O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr t1_ t2_, 
    kernel_data_equiv td O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_indom vp O1 pr -> 
    qpend_block_body (vp :: v :: nil) O10 act (v1, Some O10') ->
    qpend_block_body (vp :: v :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    get O1 curtid = Some (oscurt t1_) ->
    get O2 curtid = Some (oscurt t2_) ->
    task_prio_id O1 pr t1_ ->
    task_prio_id O2 pr t2_ ->
    (kernel_task_equiv td O1' O2' /\ buffer_equiv td O1' O2').     
Proof.
  introv Hkde Hkte Hbe Hbi Hpost1 Hpost2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2' Hcurt1 Hcurt2 Htpi1 Htpi2.
  lets Hpp1: qpend_block_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qpend_block_prio_preserved Hjo2 Hjo2'; eauto.

  assert (Hkte_ := Hkte).
  unfolds in Hkte.
  simpljoin. 
  assert (Hpost1_:= Hpost1).
  assert (Hpost2_ := Hpost2). 
  inverts Hpost1. 
  inverts Hpost2. 
  simpljoin.

  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  do 2 (match goal with H: Some _ = Some _ |- _ => inversion H; clear H end).
  assert (Hgeq1: get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    inverts H7. repeat rewsimp. auto.  
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    inverts H3. repeat rewsimp. auto.  
  }
  kvext O10 abstcblsid O1.
  kvext O20 abstcblsid O2.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  match goal with
    H: context [set O10 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O1' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto. subst O10'.
    repeat rewsimp. auto. 
  }
  match goal with
    H: context [set O20 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O2' abstcblsid = Some (abstcblist tcbs))
  end.
  {    
    eapply join_get_get_l; eauto. subst O20'.
    repeat rewsimp. auto. 
  }
  
  split.
  -
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    unfolds in Hkte.
    destruct Hkte as (tcbs1 & tcbs2 & Hgtcbs1 & Hgtcbs2 & Hall). 
    unfold kernel_task_equiv.    
    do 2 eexists. 
    split; eauto.
    split; eauto.
    introv Hd.
    lets H__: Hall Hd. clear Hall.
    destruct H__ as ((Htpi12 & Htpi21) & Hall).
    split.
    + (* eq. for task_prio_id *) 
      split.
      * 
        introv Htpi1'.
        assert (Hex: exists t, task_prio_id O1 pr0 t).
        {
          destruct Htpi1' as (t_ & Htpi1').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi12 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
      *
        introv Htpi2'.
        assert (Hex: exists t, task_prio_id O2 pr0 t).
        {
          destruct Htpi2' as (t_ & Htpi2').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi21 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
    + 
      introv Hg1' Hg2'.
      assert (get O1 curtid = Some (oscurt x29)).
      { eapply join_get_get_l; eauto. }
      l_rew21_inv1 (get O1 curtid).
      assert (get O2 curtid = Some (oscurt x17)).
      { eapply join_get_get_l; eauto. }
      l_rew21_inv1 (get O2 curtid).
      
      assert (task_prio_id O1 x32 t1_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.  
      assert (task_prio_id O2 x20 t2_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.

      assert (task_prio_id O1' pr0 t1).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi2': task_prio_id O2' pr0 t2).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi1_: task_prio_id O1 pr0 t1).
      {
        eapply prio_preserved_tpi; eauto.
      }
      assert (Htpi2_: task_prio_id O2 pr0 t2).
      {
        eapply prio_preserved_tpi; eauto.
      }
      unfolds in Htpi1_. unfolds in Htpi2_.
      simpljoin.
      do 2 l_rew21_inv1 (get O1 abstcblsid).
      do 2 l_rew21_inv1 (get O2 abstcblsid).

      kvext O10 absecblsid O1.
      kvext O20 absecblsid O2.

      assert (task_prio_id O1 pr0 t1).
      { do 5 eexists; eauto. }
      assert (task_prio_id O2 pr0 t2).
      { do 5 eexists; eauto. }
      
      assert (Hor: t1_ = t1 /\ t2_ = t2 \/ t1_ <> t1 /\ t2_ <> t2).
      {
        eapply prio_tid_corr_ext; eauto.
        apply prio_preserved_refl.
        apply prio_preserved_refl.
      }
      destruct Hor as [(Heq1 & Heq2) | (Hneq1 & Hneq2)].
      * subst.
        rewrite set_a_get_a in Hg1'. inverts Hg1'.
        rewrite set_a_get_a in Hg2'. inverts Hg2'.
        match goal with
          H1: get tcbs1 t1 = _, H2: get tcbs1 t1 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        match goal with
          H1: get tcbs2 t2 = _, H2: get tcbs2 t2 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        specializes Hall; eauto.
        simpljoin.
        splits; auto.
        do 2 match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
      * rewrite set_a_get_a' in Hg1'; eauto.
        rewrite set_a_get_a' in Hg2'; eauto.
  - (* buffer_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    destruct Hbe_ as (els1 & els2 & Hge1 & Hge2 & Hall).
    subst O10'. subst O20'.
    kvext_h Hjo1' absecblsid O1'.
    kvext_h Hjo2' absecblsid O2'.
    kvext O10 absecblsid O1.
    kvext O20 absecblsid O2.
    unfolds.
    do 2 eexists.
    split; eauto.
    split; eauto.
    introv Hd.
    specializes Hall; eauto.
    destruct Hall as (Hiff & Ha).
    l_rew21_inv1 (get O1 absecblsid).
    l_rew21_inv1 (get O2 absecblsid).

    casetac x1 eid Ht Hf.
    + (* x1 = eid *)
      subst.
      repeat rewrite set_a_get_a.
      split.
      * split; introv Hex; simpljoin; do 2 eexists; eauto.
      * introv Hso1 Hso2.
        inverts Hso1.
        inverts Hso2.
        specializes Ha; eauto.
        destruct Ha as (Hme & Hte).
        unfold mq_ed_equiv. 
        unfold mq_ed_equiv in Hme.
        destruct Hme as (ms & mlen & pws1 & pwl2 & Hq1 & Hq2 & Heq).
        inverts Hq1. inverts Hq2.
        split.
        ** 
          do 4 eexists. split; eauto. split; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
        **
          assert (get O1 curtid = Some (oscurt x29)).
          { eapply join_get_get_l; eauto. }
          l_rew21_inv1 (get O1 curtid).
          assert (get O2 curtid = Some (oscurt x17)).
          { eapply join_get_get_l; eauto. }
          l_rew21_inv1 (get O2 curtid).
          assert (task_prio_id O1 x32 t1_).
          { do 5 eexists; eauto. }
          apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.  
          assert (task_prio_id O2 x20 t2_).
          { do 5 eexists; eauto. }
          apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
          eapply tidls_equiv_cons_preserve2; eauto.
    + (* x1<> eid *)
      repeat (rewrite set_a_get_a'; eauto).
      split.
      * (* _ <-> _ *)
        auto.
      *
        introv Hg1 Hg2.
        specializes Ha; eauto.
        destruct Ha as (Hme & Hte).
        split.
        **
          unfold mq_ed_equiv in *.
          simpljoin.
          do 4 eexists.
          split; eauto.
          split; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
        **
          eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma qpend_block_buffer_indom_preserve2: 
  forall td O1 O2 O10 O20 Of1 Of2 vp v act v1 v2 O10' O20' O1' O2' pr, 
    kernel_mq_equiv td O1 O2 ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 -> 
    qpend_block_body (vp :: v :: nil) O10 act (v1, Some O10') ->
    qpend_block_body (vp :: v :: nil) O20 act (v2, Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    kernel_mq_equiv td O1' O2'.
Proof.
  introv Hkme Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hbi.
  lets Hpp1: qpend_block_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpend_block_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto. 
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_lst.
  do 2 inv_some.
  unfold kernel_mq_equiv in *.
  simpljoin.
  assert (get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  match goal with
    H: get O1 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O1' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  match goal with
    H: get O2 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O2' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets H__: H Hd; eauto end.
  destruct H__ as (Hiff & Ha).
  split; auto.
  introv Hgm1 Hgm2.
  specializes Ha; eauto. 
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.

  eapply mq_equiv_buffer_ref_preserve2; eauto.
Qed.


Lemma buffer_qpend_block_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr vp v v1 v2 O10 O20 O10' O20' O1' O2' act Of1 Of2 t1 t2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qpend_block_body (vp :: v :: nil) O10 act (v1, Some O10') ->
    qpend_block_body (vp :: v :: nil) O20 act (v2, Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hde Hkte Hbe_ Hjo1 Hjo2 Hpost1 Hpost2.
  introv Hjo1' Hjo2' Hbi Hcurt1 Hcurt2 Htpi1 Htpi2 Hdi1 Hdi2.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  lets H__: buffer_qpend_block_knl_mq_equiv_preserve2 Hkde Hkte Hbe_ Hbi.
  lets H_: H__ Hpost1 Hpost2. clear H__.
  specializes H_; eauto. 
  splits.
  -
    eapply prio_preserved_ctid_eq_preserved; eauto.
    lets H__: qpend_block_ctid_same Hjo1 Hjo1'; eauto.
    lets H__: qpend_block_ctid_same Hjo2 Hjo2'; eauto.
    lets H__: qpend_block_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpend_block_prio_preserved Hjo2 Hjo2'; eauto.
  -
    lets H1__: qpend_block_bufs_same Hpost1 Hjo1 Hjo1'.
    lets H2__: qpend_block_bufs_same Hpost2 Hjo2 Hjo2'.
    simpljoin. 
    lets H__: bufs_equiv_preserve2 O1 O2 O1' O2' Hbfe.
    specializes H__; eauto. 
  -
    unfold kernel_data_equiv.
    splits.
    + (* kernel_task_equiv *)
      destructs H_. auto. 

    + (* kernel_mq_equiv *)
      destructs Hkde. 
      eapply qpend_block_buffer_indom_preserve2; eauto. 

    + (* ports_equiv *)
      destructs Hkde. 
      eapply ports_equiv_same_prts_preserve2; eauto.          
      lets H__: qpend_block_dpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qpend_block_dpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qpend_block_kpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_kpid_same Hjo2 Hjo2'; eauto.
      lets H__: qpend_block_same_prt_ecbs Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_same_prt_ecbs Hjo2 Hjo2'; eauto.
      lets H__: qpend_block_prio_preserved Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_prio_preserved Hjo2 Hjo2'; eauto.

    + (* buffer_equiv *) 
      destructs H_. auto. 

    + (* cap_equiv *)
      destructs Hkde.
      eapply cap_equiv_preserve2; eauto.
      lets H__: qpend_block_cpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_cpid_same Hjo2 Hjo2'; eauto.

      lets H__: qpend_block_mqptr_iff Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_mqptr_iff Hjo2 Hjo2'; eauto.

  -
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: qpend_block_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpend_block_prio_preserved Hjo2 Hjo2'; eauto.
Qed.

Lemma buffer_qpend_block_get_knl_mq_equiv_preserve2:
  forall td O1 O2 vp O10 O20 act v1 v2 v1' v2' O10' O20' Of1 Of2 O1' O2' pr t1_ t2_, 
    kernel_data_equiv td O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_indom vp O1 pr -> 
    qpend_block_get_body (vp :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_block_get_body (vp :: v2 :: nil) O20 act (v2', Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    get O1 curtid = Some (oscurt t1_) ->
    get O2 curtid = Some (oscurt t2_) ->
    task_prio_id O1 pr t1_ ->
    task_prio_id O2 pr t2_ ->
    (kernel_task_equiv td O1' O2' /\ buffer_equiv td O1' O2').     
Proof.
  introv Hkde Hkte Hbe Hbi Hpost1 Hpost2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2' Hcurt1 Hcurt2 Htpi1 Htpi2.
  lets Hpp1: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.

  assert (Hkte_ := Hkte).
  unfolds in Hkte.
  simpljoin. 
  assert (Hpost1_:= Hpost1).
  assert (Hpost2_ := Hpost2). 
  inverts Hpost1. 
  inverts Hpost2. 
  simpljoin.

  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  do 2 (match goal with H: Some _ = Some _ |- _ => inversion H; clear H end).
  assert (Hgeq1: get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    inverts H3. repeat rewsimp. auto.  
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    inverts H7. repeat rewsimp. auto.  
  }
  kvext O10 abstcblsid O1.
  kvext O20 abstcblsid O2.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  match goal with
    H: context [set O10 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O1' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto. subst O10'.
    repeat rewsimp. auto. 
  }
  match goal with
    H: context [set O20 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O2' abstcblsid = Some (abstcblist tcbs))
  end.
  {    
    eapply join_get_get_l; eauto. subst O20'.
    repeat rewsimp. auto. 
  }
  
  split.
  -
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    unfolds in Hkte.
    destruct Hkte as (tcbs1 & tcbs2 & Hgtcbs1 & Hgtcbs2 & Hall). 
    unfold kernel_task_equiv.    
    do 2 eexists. 
    split; eauto.
    split; eauto.
    introv Hd.
    lets H__: Hall Hd. clear Hall.
    destruct H__ as ((Htpi12 & Htpi21) & Hall).
    split.
    + (* eq. for task_prio_id *) 
      split.
      * 
        introv Htpi1'.
        assert (Hex: exists t, task_prio_id O1 pr0 t).
        {
          destruct Htpi1' as (t_ & Htpi1').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi12 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
      *
        introv Htpi2'.
        assert (Hex: exists t, task_prio_id O2 pr0 t).
        {
          destruct Htpi2' as (t_ & Htpi2').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi21 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
    + 
      introv Hg1' Hg2'.
      assert (get O1 curtid = Some (oscurt x18)).
      { eapply join_get_get_l; eauto. }
      l_rew21_inv1 (get O1 curtid).
      assert (get O2 curtid = Some (oscurt x10)).
      { eapply join_get_get_l; eauto. }
      l_rew21_inv1 (get O2 curtid).
      
      assert (task_prio_id O1 x20 t1_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.  
      assert (task_prio_id O2 x12 t2_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.

      assert (task_prio_id O1' pr0 t1).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi2': task_prio_id O2' pr0 t2).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi1_: task_prio_id O1 pr0 t1).
      {
        eapply prio_preserved_tpi; eauto.
      }
      assert (Htpi2_: task_prio_id O2 pr0 t2).
      {
        eapply prio_preserved_tpi; eauto.
      }
      unfolds in Htpi1_. unfolds in Htpi2_.
      simpljoin.
      do 2 l_rew21_inv1 (get O1 abstcblsid).
      do 2 l_rew21_inv1 (get O2 abstcblsid).

      assert (task_prio_id O1 pr0 t1).
      { do 5 eexists; eauto. }
      assert (task_prio_id O2 pr0 t2).
      { do 5 eexists; eauto. }
      
      assert (Hor: t1_ = t1 /\ t2_ = t2 \/ t1_ <> t1 /\ t2_ <> t2).
      {
        eapply prio_tid_corr_ext; eauto.
        apply prio_preserved_refl.
        apply prio_preserved_refl.
      }
      destruct Hor as [(Heq1 & Heq2) | (Hneq1 & Hneq2)].
      * subst.
        rewrite set_a_get_a in Hg1'. inverts Hg1'.
        rewrite set_a_get_a in Hg2'. inverts Hg2'.
        match goal with
          H1: get tcbs1 t1 = _, H2: get tcbs1 t1 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        match goal with
          H1: get tcbs2 t2 = _, H2: get tcbs2 t2 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        specializes Hall; eauto.
        simpljoin.
        splits; auto.
      * rewrite set_a_get_a' in Hg1'; eauto.
        rewrite set_a_get_a' in Hg2'; eauto.
  - (* buffer_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    destruct Hbe_ as (els1 & els2 & Hge1 & Hge2 & Hall).
    subst O10'. subst O20'.
    unfolds.
    do 2 eexists.
    assert (get O1 absecblsid = get O1' absecblsid).
    {
      lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
      rewrite set_a_get_a'. auto. introv Hv. congruence.
    }
    l_rew21_inv1 (get O1 absecblsid).
    split; eauto.
    assert (get O2 absecblsid = get O2' absecblsid).
    {
      lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
      rewrite set_a_get_a'. auto. introv Hv. congruence.
    }
    l_rew21_inv1 (get O2 absecblsid).
    split; eauto.
    introv Hd.
    specializes Hall; eauto.
    auto.
    destruct Hall as (Hiff & Ha).
    split; auto.
    intros.
    specializes Ha; eauto.
    destruct Ha as (Hme & Hte).
    split.
    unfold mq_ed_equiv. 
    unfold mq_ed_equiv in Hme.
    destruct Hme as (ms & mlen & pws1 & pwl2 & Hq1 & Hq2 & Heq).
    inverts Hq1. inverts Hq2.
    do 4 eexists. split; eauto. split; eauto.
    eapply tidls_equiv_pp_preserve2; eauto.
    eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma qpend_block_get_buffer_indom_preserve2: 
  forall td O1 O2 O10 O20 Of1 Of2 vp v1 v2 act v1' v2' O10' O20' O1' O2' pr, 
    kernel_mq_equiv td O1 O2 ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 -> 
    qpend_block_get_body (vp :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_block_get_body (vp :: v2 :: nil) O20 act (v2', Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    kernel_mq_equiv td O1' O2'.
Proof.
  introv Hkme Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hbi.
  lets Hpp1: qpend_block_get_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpend_block_get_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto. 
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_lst.
  do 2 rem_dis.
  do 2 inv_some.
  unfold kernel_mq_equiv in *.
  simpljoin.
  assert (get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  match goal with
    H: get O1 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O1' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  match goal with
    H: get O2 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O2' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets H__: H Hd; eauto end.
  destruct H__ as (Hiff & Ha).
  split; auto.
  introv Hgm1 Hgm2.
  specializes Ha; eauto.
  unfolds in Ha. simpljoin.
  unfolds.
  do 8 eexists. splits; eauto.
  destruct H14 as[H14 | [H14 | H14]]. auto. auto.
  right. right.
  assert (get O1' absecblsid = get O1 absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  rewrite H12.
  assert (get O2' absecblsid = get O2 absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  rewrite H13. auto.
  simpljoin. do 7 eexists. splits; eauto.
  unfolds in H20. unfolds.
  simpljoin. do 4 eexists. splits; eauto.
  eapply tidls_equiv_pp_preserve2; eauto.
  eapply tidls_equiv_pp_preserve2; eauto.
Qed.


Lemma buffer_qpend_block_get_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr vp v1 v2 v1' v2' O10 O20 O10' O20' O1' O2' act Of1 Of2 t1 t2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qpend_block_get_body (vp :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_block_get_body (vp :: v2 :: nil) O20 act (v2', Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hde Hkte Hbe_ Hjo1 Hjo2 Hpost1 Hpost2.
  introv Hjo1' Hjo2' Hbi Hcurt1 Hcurt2 Htpi1 Htpi2 Hdi1 Hdi2.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  lets H__: buffer_qpend_block_get_knl_mq_equiv_preserve2 Hkde Hkte Hbe_ Hbi.
  lets H_: H__ Hpost1 Hpost2. clear H__.
  specializes H_; eauto. 
  splits.
  -
    eapply prio_preserved_ctid_eq_preserved; eauto.
    lets H__: qpend_block_get_ctid_same Hjo1 Hjo1'; eauto.
    lets H__: qpend_block_get_ctid_same Hjo2 Hjo2'; eauto.
    lets H__: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.
  -
    lets H1__: qpend_block_get_bufs_same Hpost1 Hjo1 Hjo1'.
    lets H2__: qpend_block_get_bufs_same Hpost2 Hjo2 Hjo2'.
    simpljoin. 
    lets H__: bufs_equiv_preserve2 O1 O2 O1' O2' Hbfe.
    specializes H__; eauto. 
  -
    unfold kernel_data_equiv.
    splits.
    + (* kernel_task_equiv *)
      destructs H_. auto. 

    + (* kernel_mq_equiv *)
      destructs Hkde. 
      eapply qpend_block_get_buffer_indom_preserve2; eauto. 

    + (* ports_equiv *)
      destructs Hkde. 
      eapply ports_equiv_same_prts_preserve2; eauto.          
      lets H__: qpend_block_get_dpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qpend_block_get_dpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qpend_block_get_kpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_get_kpid_same Hjo2 Hjo2'; eauto.
      lets H__: qpend_block_get_same_prt_ecbs Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_get_same_prt_ecbs Hjo2 Hjo2'; eauto.
      lets H__: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.

    + (* buffer_equiv *) 
      destructs H_. auto. 

    + (* cap_equiv *)
      destructs Hkde.
      eapply cap_equiv_preserve2; eauto.
      lets H__: qpend_block_get_cpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_get_cpid_same Hjo2 Hjo2'; eauto.

      lets H__: qpend_block_get_mqptr_iff Hjo1 Hjo1'; eauto.
      lets H__: qpend_block_get_mqptr_iff Hjo2 Hjo2'; eauto.

  -
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.
Qed.


Lemma os_stat_qpend_false:
  forall pr v O1 O2 t1 t2,
    (exists tls prio t qid sus pr,
      v = Vptr qid /\
      get O1 curtid = Some (oscurt t) /\
      get O1 abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (prio, wait (os_stat_q qid) (Some Int.zero), Vnull, sus, pr)) ->
    ~ (exists tls prio t qid sus pr,
      v = Vptr qid /\
      get O2 curtid = Some (oscurt t) /\
      get O2 abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (prio, wait (os_stat_q qid) (Some Int.zero), Vnull, sus, pr)) ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    buffer_indom v O1 pr ->
    buffer_indom v O2 pr ->
    False.
Proof.
  introv Ht Hf Hkteq Hcurt1 Hcurt2 Htpi1 Htpi2 Hkmeq Hmdq1 Hmdq2.
  apply Hf.
  destruct Ht as (tls1 & prio1 & t & qid1 & sus1 & pr1 &
    H & Hcurt1_ & Hget_tcb_map1 & Hget_tcb1).
  subst.
  assert (Hnnull: Vptr qid1 <> Vnull) by congruence.
  unfolds in Hmdq1. unfolds in Hmdq2.
  destruct Hmdq1. inverts H. 
  assert (Htpi1_: task_prio_id O1 pr1 t).
  unfolds; do 5 eexists; split; eauto. rewrite Hcurt1 in Hcurt1_. inverts Hcurt1_.
  assert (pr1 = pr) by (eapply prio_unique; eauto); subst.
  destruct Htpi2 as (pr'2 & tcbs2 & st2 & msg2 & sus2 & Hget_tcb_map2 & Hget_tcb2).
  destruct Hkteq as (tcbs1_ & tcbs2_ & Hget_tcb_map1_ & Hget_tcb_map2_ & H').
  specialize(H' pr ltac:(tauto)). simpljoin.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew12_inv2 (get O2 abstcblsid).
  lets H_: H2 Hget_tcb1 Hget_tcb2.
  simpljoin; subst.
  do 6 eexists. splits; eauto. inverts H. eauto.
Qed.

Lemma buffer_qpend_to_knl_mq_equiv_preserve2:
  forall td O1 O2 vp O10 O20 act v1 v2 v1' v2' O10' O20' Of1 Of2 O1' O2' pr t1_ t2_, 
    kernel_data_equiv td O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_indom vp O1 pr -> 
    qpend_to_body (vp :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_to_body (vp :: v2 :: nil) O20 act (v2', Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    get O1 curtid = Some (oscurt t1_) ->
    get O2 curtid = Some (oscurt t2_) ->
    task_prio_id O1 pr t1_ ->
    task_prio_id O2 pr t2_ ->
    (kernel_task_equiv td O1' O2' /\ buffer_equiv td O1' O2').     
Proof.
  introv Hkde Hkte Hbe Hbi Hpost1 Hpost2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2' Hcurt1 Hcurt2 Htpi1 Htpi2.
  lets Hpp1: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto.

  assert (Hkte_ := Hkte).
  unfolds in Hkte.
  simpljoin. 
  assert (Hpost1_:= Hpost1).
  assert (Hpost2_ := Hpost2). 
  inverts Hpost1. 
  inverts Hpost2. 
  simpljoin.

  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  do 2 (match goal with H: Some _ = Some _ |- _ => inversion H; clear H end).
  assert (Hgeq1: get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    inverts H3. repeat rewsimp. auto.  
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    inverts H10. repeat rewsimp. auto.  
  }
  kvext O10 abstcblsid O1.
  kvext O20 abstcblsid O2.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  match goal with
    H: context [set O10 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O1' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto. subst O10'.
    repeat rewsimp. auto. 
  }
  match goal with
    H: context [set O20 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O2' abstcblsid = Some (abstcblist tcbs))
  end.
  {    
    eapply join_get_get_l; eauto. subst O20'.
    repeat rewsimp. auto. 
  }
  
  split.
  -
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    unfolds in Hkte.
    destruct Hkte as (tcbs1 & tcbs2 & Hgtcbs1 & Hgtcbs2 & Hall). 
    unfold kernel_task_equiv.    
    do 2 eexists. 
    split; eauto.
    split; eauto.
    introv Hd.
    lets H__: Hall Hd. clear Hall.
    destruct H__ as ((Htpi12 & Htpi21) & Hall).
    split.
    + (* eq. for task_prio_id *) 
      split.
      * 
        introv Htpi1'.
        assert (Hex: exists t, task_prio_id O1 pr0 t).
        {
          destruct Htpi1' as (t_ & Htpi1').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi12 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
      *
        introv Htpi2'.
        assert (Hex: exists t, task_prio_id O2 pr0 t).
        {
          destruct Htpi2' as (t_ & Htpi2').
          eexists.
          eapply prio_preserved_tpi; eauto. 
        }
        apply Htpi21 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym; auto. 
    + 
      introv Hg1' Hg2'.
      assert (get O1 curtid = Some (oscurt x18)).
      { eapply join_get_get_l; eauto. }
      l_rew21_inv1 (get O1 curtid).
      assert (get O2 curtid = Some (oscurt x7)).
      { eapply join_get_get_l; eauto. }
      l_rew21_inv1 (get O2 curtid).
      
      assert (task_prio_id O1 x26 t1_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.  
      assert (task_prio_id O2 x15 t2_).
      { do 5 eexists; eauto. }
      apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.

      assert (task_prio_id O1' pr0 t1).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi2': task_prio_id O2' pr0 t2).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi1_: task_prio_id O1 pr0 t1).
      {
        eapply prio_preserved_tpi; eauto.
      }
      assert (Htpi2_: task_prio_id O2 pr0 t2).
      {
        eapply prio_preserved_tpi; eauto.
      }
      unfolds in Htpi1_. unfolds in Htpi2_.
      simpljoin.
      do 2 l_rew21_inv1 (get O1 abstcblsid).
      do 2 l_rew21_inv1 (get O2 abstcblsid).

      assert (task_prio_id O1 pr0 t1).
      { do 5 eexists; eauto. }
      assert (task_prio_id O2 pr0 t2).
      { do 5 eexists; eauto. }
      
      assert (Hor: t1_ = t1 /\ t2_ = t2 \/ t1_ <> t1 /\ t2_ <> t2).
      {
        eapply prio_tid_corr_ext; eauto.
        apply prio_preserved_refl.
        apply prio_preserved_refl.
      }
      destruct Hor as [(Heq1 & Heq2) | (Hneq1 & Hneq2)].
      * subst.
        rewrite set_a_get_a in Hg1'. inverts Hg1'.
        rewrite set_a_get_a in Hg2'. inverts Hg2'.
        match goal with
          H1: get tcbs1 t1 = _, H2: get tcbs1 t1 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        match goal with
          H1: get tcbs2 t2 = _, H2: get tcbs2 t2 = _ |- _ => rewrite H2 in H1; inverts H1
        end.
        specializes Hall; eauto.
        simpljoin.
        splits; auto.
      * rewrite set_a_get_a' in Hg1'; eauto.
        rewrite set_a_get_a' in Hg2'; eauto.
  - (* buffer_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte & _ & _ & Hbe_ & _).
    destruct Hbe_ as (els1 & els2 & Hge1 & Hge2 & Hall).
    subst O10'. subst O20'.
    kvext_h Hjo1' absecblsid O1'.
    kvext_h Hjo2' absecblsid O2'.
    kvext O10 absecblsid O1.
    kvext O20 absecblsid O2.
    unfolds.
    do 2 eexists.
    split; eauto.
    split; eauto.
    introv Hd.
    specializes Hall; eauto.
    destruct Hall as (Hiff & Ha).
    l_rew21_inv1 (get O1 absecblsid).
    l_rew21_inv1 (get O2 absecblsid).

    casetac x1 eid Ht Hf.
    + (* x1 = eid *)
      subst.
      repeat rewrite set_a_get_a.
      split.
      * split; introv Hex; simpljoin; do 2 eexists; eauto.
      * introv Hso1 Hso2.
        inverts Hso1.
        inverts Hso2.
        specializes Ha; eauto.
        destruct Ha as (Hme & Hte).
        unfold mq_ed_equiv. 
        unfold mq_ed_equiv in Hme.
        destruct Hme as (ms & mlen & pws1 & pwl2 & Hq1 & Hq2 & Heq).
        inverts Hq1. inverts Hq2.
        split.
        ** 
          do 4 eexists. split; eauto. split; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
        **
          assert (get O1 curtid = Some (oscurt x18)) by (eapply join_get_get_l; eauto).
          assert (get O2 curtid = Some (oscurt x7)) by (eapply join_get_get_l; eauto).
          l_rew21_inv1 (get O1 curtid).
          l_rew21_inv1 (get O2 curtid).
          assert (task_prio_id O1 x26 t1_).
          { do 5 eexists; eauto. }
          apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.  
          assert (task_prio_id O2 x15 t2_).
          { do 5 eexists; eauto. }
          apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.

          assert (get (set els1 eid (absmsgq ms mlen pws1, remove_tid t1_ x24)) eid = 
            Some (absmsgq ms mlen pws1, remove_tid t1_ x24)).
          { rewrite set_a_get_a; eauto. }
          match goal with
            H: get els1 eid = _ |- _ => lets H1_: distinct_wait_tids H; eauto
          end.
          assert (get (set els2 eid (absmsgq ms mlen pwl2, remove_tid t2_ x13)) eid = 
            Some (absmsgq ms mlen pwl2, remove_tid t2_ x13)).
          { rewrite set_a_get_a; eauto. }
          match goal with
            H: get els2 eid = _ |- _ => lets H2_: distinct_wait_tids H; eauto
          end.
          simpljoin.
          eapply tidls_equiv_rm_preserve2; eauto.
    + (* x1<> eid *)
      repeat (rewrite set_a_get_a'; eauto).
      split.
      * (* _ <-> _ *)
        auto.
      *
        introv Hg1 Hg2.
        specializes Ha; eauto.
        destruct Ha as (Hme & Hte).
        split.
        **
          unfold mq_ed_equiv in *.
          simpljoin.
          do 4 eexists.
          split; eauto.
          split; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
        **
          eapply tidls_equiv_pp_preserve2; eauto.
Qed.
Lemma qpend_to_buffer_indom_preserve2: 
  forall td O1 O2 O10 O20 Of1 Of2 vp v1 v2 act v1' v2' O10' O20' O1' O2' pr t1 t2, 
    kernel_mq_equiv td O1 O2 ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 -> 
    qpend_to_body (vp :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_to_body (vp :: v2 :: nil) O20 act (v2', Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    kernel_mq_equiv td O1' O2'.
Proof.
  introv Hkme Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hbi.
  introv Hcurt1 Hcurt2 Htip1 Htip2.
  lets Hpp1: qpend_to_body_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpend_to_body_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto. 
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_lst.
  do 2 rem_dis.
  do 2 inv_some.
  unfold kernel_mq_equiv in *.
  simpljoin.
  assert (get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  match goal with
    H: get O1 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O1' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  match goal with
    H: get O2 absmqattrid = Some (absmqattr ?x) |- _ =>
      assert (get O2' absmqattrid = Some (absmqattr x)) by congruence 
  end.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets H__: H Hd; eauto end.
  destruct H__ as (Hiff & Ha).
  split; auto.
  introv Hgm1 Hgm2.
  specializes Ha; eauto.
  unfolds in Ha. simpljoin.
  unfolds.
  do 8 eexists. splits; eauto.
  destruct H20 as [H20 | [H20 | H20]]. auto. auto.
  right. right.
  simpljoin.
  assert (get O1 absecblsid = Some (absecblist x17)).
  { eapply join_get_get_l; eauto. }
  l_rew21_inv1 (get O1 absecblsid).
  assert (get O2 absecblsid = Some (absecblist x6)).
  { eapply join_get_get_l; eauto. }
  l_rew21_inv1 (get O2 absecblsid).
  assert (get O1' absecblsid = Some (absecblist (set x30 x (absmsgq x19 x20 x21, remove_tid x16 x22)))).
  { eapply join_get_get_l; eauto. rewrite set_a_get_a. auto. }
  assert (get O2' absecblsid = Some (absecblist (set x31 x (absmsgq x8 x9 x10, remove_tid x5 x11)))).
  { eapply join_get_get_l; eauto. rewrite set_a_get_a. auto. }
  casetac x32 x Ht Hf.
  subst. rewrite H23 in H5; inverts H5. rewrite H22 in H14; inverts H14.
  do 7 eexists. splits; eauto.
  rewrite set_a_get_a. auto.
  rewrite set_a_get_a. auto.
  unfolds. unfolds in H24. simpljoin. do 4 eexists. splits; eauto.
  eapply tidls_equiv_pp_preserve2; eauto.
  assert (get O1 curtid = Some (oscurt x16)).
  { eapply join_get_get_l; eauto. }
  l_rew21_inv1 (get O1 curtid).
  assert (get O2 curtid = Some (oscurt x5)).
  { eapply join_get_get_l; eauto. }
  assert (get O1 abstcblsid = Some (abstcblist x14)).
  { eapply join_get_get_l; eauto. }
  assert (get O2 abstcblsid = Some (abstcblist x3)).
  { eapply join_get_get_l; eauto. }
  l_rew21_inv1 (get O2 curtid).
  assert (task_prio_id O1 x24 t1).
  { do 5 eexists; eauto. }
  apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.  
  assert (task_prio_id O2 x13 t2).
  { do 5 eexists; eauto. }
  apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
  assert (get (set x30 x (absmsgq x19 x20 x21, remove_tid t1 x22)) x = 
    Some (absmsgq x19 x20 x21, remove_tid t1 x22)).
  { rewrite set_a_get_a; eauto. }
  match goal with
    H: get x30 x = _ |- _ => lets H1_: distinct_wait_tids H; eauto
  end.
  assert (get (set x31 x (absmsgq x8 x9 x10, remove_tid t2 x11)) x = 
    Some (absmsgq x8 x9 x10, remove_tid t2 x11)).
  { rewrite set_a_get_a; eauto. }
  match goal with
    H: get x31 x = _ |- _ => lets H2_: distinct_wait_tids H; eauto
  end.
  simpljoin.
  eapply tidls_equiv_rm_preserve2; eauto.

  do 7 eexists. splits; eauto.
  rewrite set_a_get_a'. eauto. auto.
  rewrite set_a_get_a'. eauto. auto.
  unfolds. unfolds in H24.
  simpljoin. do 4 eexists. splits; eauto.
  eapply tidls_equiv_pp_preserve2; eauto.
  eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma buffer_qpend_to_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr vp v1 v2 v1' v2' O10 O20 O10' O20' O1' O2' act Of1 Of2 t1 t2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    buffer_equiv (dom_for_prio pr) O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qpend_to_body (vp :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_to_body (vp :: v2 :: nil) O20 act (v2', Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    buffer_indom vp O1 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hde Hkte Hbe_ Hjo1 Hjo2 Hpost1 Hpost2.
  introv Hjo1' Hjo2' Hbi Hcurt1 Hcurt2 Htpi1 Htpi2 Hdi1 Hdi2.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  lets H__: buffer_qpend_to_knl_mq_equiv_preserve2 Hkde Hkte Hbe_ Hbi.
  lets H_: H__ Hpost1 Hpost2. clear H__.
  specializes H_; eauto. 
  splits.
  -
    eapply prio_preserved_ctid_eq_preserved; eauto.
    lets H__: qpend_to_ctid_same Hjo1 Hjo1'; eauto.
    lets H__: qpend_to_ctid_same Hjo2 Hjo2'; eauto.
    lets H__: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto.
  -
    lets H1__: qpend_to_bufs_same Hpost1 Hjo1 Hjo1'.
    lets H2__: qpend_to_bufs_same Hpost2 Hjo2 Hjo2'.
    simpljoin. 
    lets H__: bufs_equiv_preserve2 O1 O2 O1' O2' Hbfe.
    specializes H__; eauto. 
  -
    unfold kernel_data_equiv.
    splits.
    + (* kernel_task_equiv *)
      destructs H_. auto. 

    + (* kernel_mq_equiv *)
      destructs Hkde. 
      eapply qpend_to_buffer_indom_preserve2; eauto. 

    + (* ports_equiv *)
      destructs Hkde. 
      eapply ports_equiv_same_prts_preserve2; eauto.          
      lets H__: qpend_to_dpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qpend_to_dpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qpend_to_kpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpend_to_kpid_same Hjo2 Hjo2'; eauto.
      lets H__: qpend_to_same_prt_ecbs Hjo1 Hjo1'; eauto.
      lets H__: qpend_to_same_prt_ecbs Hjo2 Hjo2'; eauto.
      lets H__: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto.
      lets H__: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto.

    + (* buffer_equiv *) 
      destructs H_. auto. 

    + (* cap_equiv *)
      destructs Hkde.
      eapply cap_equiv_preserve2; eauto.
      lets H__: qpend_to_cpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpend_to_cpid_same Hjo2 Hjo2'; eauto.

      lets H__: qpend_to_mqptr_iff Hjo1 Hjo1'; eauto.
      lets H__: qpend_to_mqptr_iff Hjo2 Hjo2'; eauto.

  -
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto.
Qed.

Lemma hidapistep_hidapistep_bufferpend_lemma:
forall
  (pc0 : progunit) (pr pr0 : priority) (t1 t2 : addrval)
  (T1 T2 : tasks) (C' C1 : code) (cst1' cst2' : clientst)
  (O1 O2 O1' O2' : osabst)(act : action)(r : list val -> spec_code)
  (cd' : spec_code)(ks0 : stmtcont)(i : taskdom)
(Hncfid : no_common_fid pc0 (api_spec, int_spec, get_hprio_d))
(Hpu : pu_noabs pc0)
(Hrch2 : reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2)
(Hrch1 : reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1)
(Hfloweq : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
        obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1'
          cst2' O1 O2)
(Hsceq : obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1 O2)
(Htmeq : obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1 O2)
(Htdeq : obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1 O2)
(Hact : act = TauAct \/ act = SendAct \/ act = RecvAct)
(Hnint1 : ~ in_intr T1 O1)
(Hcurt1 : get O1 curtid = Some (oscurt t1))
(Htpi1 : task_prio_id O1 pr t1)
(ks1_ : stmtcont)
(ke0 : exprcont)
(Hnabt1 : nabt (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_))))
(Hnint2 : ~ in_intr T2 O2)
(Hcurt2 : get O2 curtid = Some (oscurt t2))
(Hdomeq : dom_for_prio pr = dom_for_prio pr)
(Htpi2 : task_prio_id O2 pr t2)
(ks1 : stmtcont)
(cd'0 : spec_code)
(Hnabt2 : nabt (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))))
(cd1 : spec_code)
(HC1 : get T1 t1 = Some (curs (hapi_code cd1), (ke0, ks1_)))
(Hceq : forall (pr0 : priority) (t1 t2 : tid),
     dom_for_prio pr0 = dom_for_prio pr ->
     task_prio_id O1 pr0 t1 ->
     task_prio_id O2 pr0 t2 ->
     exists c1 c2 ke ks1 ks2,
     get T1 t1 = Some (c1, (ke, ks1)) /\
     get T2 t2 = Some (c2, (ke, ks2)) /\
     cmd_equiv pr0 c1 c2 O1 O2 /\ cont_equiv pr0 ks1 ks2 O1 O2)
(Hd'eq : obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1'
        cst2' O1 O2)
(Hstepdm : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i))
(Hfa : forall pr1 pr2 : priority,
    task_prio_id O1 pr1 t1 ->
    task_prio_id O2 pr2 t2 ->
    dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2)
(Ht1_ : get O1 curtid = Some (oscurt t1))
(Ht2_ : get O2 curtid = Some (oscurt t2))
(Hbufe : bufs_equiv (dom_for_prio pr) O1 O2)
(Hkde : kernel_data_equiv (dom_for_prio pr) O1 O2)
(Hcde : client_data_equiv (dom_for_prio pr) cst1' cst2' O1 O2)
(Hkte : kernel_task_equiv (dom_for_prio pr) O1 O2)
(Hkme : kernel_mq_equiv (dom_for_prio pr) O1 O2)
(Hprte : ports_equiv (dom_for_prio pr) O1 O2)
(Hbfe : buffer_equiv (dom_for_prio pr) O1 O2)
(Hctide_ : ctid_equiv (dom_for_prio pr) O1 O2)
(cd2 : spec_code)
(H : spec_step get_hprio_d cd1 O1 cd' O1' act)
(Hcpe : cap_equiv (dom_for_prio pr) O1 O2)
(H0 : spec_step get_hprio_d cd2 O2 cd'0 O2' act)
(Hhsat1 : head_asrt_sat pr cd1 O1)
(Hhsat2 : head_asrt_sat pr cd2 O2)
(Hvleq : vl_equiv cd1 cd2)
(Hnex : ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2))
(Hbpend : bufferpend_equiv cd1 cd2)
(Hcont : cont_equiv pr ks1_ ks1 O1 O2)
(HC2 : get T2 t2 = Some (curs (hapi_code cd2), (ke0, ks1))), 

  code_equiv_tskd i
    (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_)))
    (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))) O1' O2' /\
    data_equiv_tskd i cst1' cst2' O1' O2'. 
Proof.
intros.
match goal with H: spec_step _ cd1 _ ?cd' _ _ |- _ => rename cd' into cd1'; rename H into Hstep1 end.
match goal with H: spec_step _ cd2 _ ?cd' _ _ |- _ => rename cd' into cd2'; rename H into Hstep2 end.

unfolds in Hbpend.
destruct Hbpend as (vl & vl1 & vl2 & k & Hlenvl & Hlenvl1 & Hlenvl2 & Hnth1 & Hnth2).
do 3 try destruct vl; tryfalse.
do 2 try destruct vl1; tryfalse.
do 2 try destruct vl2; tryfalse.
simpl in Hnth1.
simpl in Hnth2.
destruct v0; simpl in Hnth1;
  try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).
simpl in Hnth1.
simpl in Hnth2.


unfold obsr_equiv_tskd in Htdeq.
destruct Htdeq as (Hce & Hde).
unfolds in Hsceq.
unfolds in Hsceq.
destruct Hsceq as (Hce_sch & Hde_sch).

unfolds in Htmeq.

destruct k.
(* k=0 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
symexe.
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  simpljoin.
  split. simpl. auto.
  split. simpl. auto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  introv Hf. rewrite nth_error_nil in Hf. tryfalse.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split.
  introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. right. right. left.
  (* establish bufferpend_equiv *)
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 1%nat.
}

destruct k.
(* k=1 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
symexe.
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl. auto.
  split. simpl. auto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  introv Hf. rewrite nth_error_nil in Hf. tryfalse.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split. introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. right. right. left.
  (* establish bufferpost_equiv *)
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 2%nat.
}
{
  apply data_equiv_schd_sym in Hde_sch; eauto.
  lets H__: buf_in_dom_contra Hde_sch;  eauto.
  specializes H__; eauto.
  false.
}
{
  lets H__: buf_in_dom_contra Hde_sch;  eauto.
  specializes H__; eauto.
  false.
}
{
  simpl in Hhsat1.
  simpl in Hhsat2.
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl.
  eapply n_buf_in_dom_false_dest; eauto.
  split. simpl.
  eapply n_buf_in_dom_false_dest; eauto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  introv Hf. rewrite nth_error_nil in Hf. tryfalse.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split.
  introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. right. right. left.
  (* establish bufferpost_equiv *)
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 3%nat.
}

destruct k.
(* k=2 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
symexe.
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto.
  match goal with
    H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
      lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst
  end.
  apply cmd_equiv_end.
}

destruct k.
(* k=3 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
simpl in Hhsat1.
simpl in Hhsat2.
symexe.

{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.

  apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.

  inverts H1_. inverts H2_.
  unfolds in H3. unfolds in H4. simpljoin.
  inverts H1. inverts H2.
  unfolds. right.
  do 2 eexists. split. eauto. split. eauto.
  split. simpl. eauto.
  split. simpl. eauto.
  split. unfolds. introv Hn1 Hn2 Hl1 Hl2.
  simpl in *. inverts Hn1. inverts Hn2.
  destruct i1.
  simpl in *. inverts Hl1. inverts Hl2.
  eauto.
  simpl in *.   destruct i1.
  simpl in *. inverts Hl1. inverts Hl2.
  eauto.
  unfolds. right. 
  split. introv Hff. simpljoin. tryfalse.
  do 9 right. left.
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 10%nat.
}
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
  inverts H1_. inverts H2_.
  unfolds in H3. unfolds in H4. simpljoin.
  inverts H1. inverts H2.
  unfolds. right.
  do 2 eexists. split. eauto. split. eauto.
  split. simpl. eauto.
  split. simpl. eauto.
  split. unfolds. introv Hn1 Hn2 Hl1 Hl2.
  simpl in *. inverts Hn1. inverts Hn2.
  destruct i1.
  simpl in *. inverts Hl1. inverts Hl2.
  eauto.
  simpl in *.   destruct i1.
  simpl in *. inverts Hl1. inverts Hl2.
  eauto.
  unfolds. right. 
  split. introv Hff. simpljoin. tryfalse.
  do 9 right. left.
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 10%nat.
}
{  

  lets Hfff:buffer_equiv_nemp_impl_ Hbfe Hhsat1.
  destruct Hfff.
  unfolds in H3.
  unfolds in H4.
  simpljoin.
  inverts H1.   inverts H.
  eapply join_get_get_l in H4;eauto.
  inverts H0.
  do 7 eexists.
  split. eauto. split. eauto. eauto.
  simpljoin.
  destruct H22.
  rewrite H21 in H2. inverts H2.
  inverts H. do 4 eexists. eauto.
}
{
  lets Hfff:buffer_equiv_nemp_impl_ Hbfe Hhsat1.
  destruct Hfff.
  unfolds in H3.
  unfolds in H4.
  simpljoin.
  inverts H1.   inverts H.
  eapply join_get_get_l in H4;eauto.
  inverts H0.
  do 7 eexists.
  split. eauto. split. eauto. eauto.
  simpljoin.
  destruct H26.
  rewrite H25 in H2. inverts H2.
  inverts H. do 4 eexists. eauto.

}

{
  lets Hfff:buffer_equiv_nil_impl_ Hbfe Hhsat1.
  destruct Hfff.
  unfolds in H3.
  unfolds in H4.
  simpljoin.
  inverts H1.   inverts H.
  eapply join_get_get_l in H4;eauto.
  inverts H0.
  do 5 eexists.
  split. eauto. split. eauto. eauto.
  simpljoin.
  destruct H26.
  rewrite H24 in H2. inverts H2.
  inverts H. do 4 eexists. eauto.
}
{
  eapply buffer_equiv_sym in Hbfe.
  lets Hfff:buffer_equiv_nemp_impl_ Hbfe Hhsat2.
  destruct Hfff.
  unfolds in H3.
  unfolds in H4.
  simpljoin.
  inverts H1.   inverts H.
  eapply join_get_get_l in H22;eauto.
  inverts H0.
  do 7 eexists.
  split. eauto. split. eauto. eauto.
  simpljoin.
  destruct H15.
  rewrite H13 in H2. inverts H2.
  inverts H0.
  inverts H. do 4 eexists. eauto.
}
{
  (* qpend_get_no_pwl_succ_body *) 
  unfolds in H3. unfolds in H4. simpljoin.
  inverts H. inverts H1.
  match goal with H: _ /\ _ \/ _ /\ _ |- _=>rename H into Hm2 end.
  destruct Hm2 as [Hm2|Hm2]. 2:destruct Hm2;tryfalse.
  match goal with H: _ /\ _ \/ _ /\ _ |- _=>rename H into Hm1 end.
  destruct Hm1 as [Hm1|Hm1]. 2:destruct Hm1;tryfalse.
  destruct Hm2 as (Hm21 & Hm22). destruct Hm1 as (Hm11&Hm12).
  inverts Hm21. inverts Hm11.
  inverts Hm22.
  lets Hjoin1:H29. lets Hjoin2:H18.
  eapply join_get_set_eq_1 in H29;eauto.
  inverts Hm12.
  eapply join_get_set_eq_1 in H18;eauto.
  inverts H29. inverts H18.
  split. unfolds.
  introv Hdom Htpi1' Htpi2'.
  lets Htce_:Hce.
  unfolds in Htce_.
  unfolds in Htpi1'. unfolds in Htpi2'.
  rewrite set_a_get_a' in Htpi1'.
  rewrite set_a_get_a' in Htpi2'.
  casetac t1 t0 Ht1e Ht1ne.
  2:{
    casetac pr pr1 Hpe Hpne.
    subst pr1.
    lets Hf:tid_unique Htpi1.
    unfold task_prio_id in Hf.
    specialize(Hf Htpi1').
    tryfalse.
    casetac t2 t3 Ht2e Ht2ne.
    {
      subst t3.
      lets Hf:prio_unique Htpi2.
      unfold task_prio_id in Hf.
      specialize(Hf Htpi2').
      tryfalse.
    }
    {
      rewrite set_a_get_a';eauto.
      rewrite set_a_get_a';eauto.
      unfold task_prio_id in Htce_.
      lets Ht: Htce_ Htpi1' Htpi2'.
      eauto.
      destruct Ht as (c1' & c2' & ke' & ks1' & ks2' & Hg1 & Hg2 & Hcmd' & Hcont').
      do 5  eexists. split. eauto. split. eauto.
      split.
      unfolds in Hcmd'.
      destruct Hcmd' as [Hcmd'|Hcmd'].
      unfolds. left. eauto.
      unfolds. right.
      simpljoin.
      do 2 eexists.
      split. eauto. split. eauto.
      split. 2:split. 3:split;eauto.
      eapply stmt_equiv_qref_preserve.
      eapply H37.
      instantiate(1:= O1).
      unfolds.
      introv Habs1 Habs1'.
      rewrite set_a_get_a' in Habs1';[idtac|introv Hfalse;tryfalse].
      rewrite Habs1' in Habs1. inverts Habs1.
      introv Hmqs. eauto.
      
      unfolds. 
      introv Ha1 Ha1'.
      rewrite set_a_get_a' in Ha1';[idtac|introv Hfalse;tryfalse].
      rewrite Ha1' in Ha1. inverts Ha1.
      introv He. eauto.

      eapply eqdom_frm_domimpl.
      eapply H14. eapply H28. eapply Hjoin1.
      
      unfolds.
      intros. unfolds.
      introv Hdom. split. introv Htpi1'.
      unfolds. rewrite set_a_get_a'.
      unfolds in Htpi1'. eauto.
      introv Hfalse. tryfalse.
      introv Htpi1'. unfolds in Htpi1'.
      rewrite set_a_get_a' in Htpi1'.
      unfolds. eauto.
      introv Hfalse. tryfalse.
      rewrite set_a_get_a';[eauto|introv Hfalse;tryfalse].
      eapply H29.
      
      eapply stmt_equiv_qref_preserve.
      lets Hst:stmt_equiv_sym H37.
      eapply Hst.
      instantiate(1:= O2).
      unfolds.
      introv Habs1 Habs1'.
      rewrite set_a_get_a' in Habs1';[idtac|introv Hfalse;tryfalse].
      rewrite Habs1' in Habs1. inverts Habs1.
      introv Hmqs. eauto.
      
      unfolds. 
      introv Ha1 Ha1'.
      rewrite set_a_get_a' in Ha1';[idtac|introv Hfalse;tryfalse].
      rewrite Ha1' in Ha1. inverts Ha1.
      introv He. eauto.

      eapply eqdom_frm_domimpl.
      eapply H5. eapply H17. eapply Hjoin2.
      
      unfolds.
      intros. unfolds.
      introv Hdom. split. introv Htpi1'.
      unfolds. rewrite set_a_get_a'.
      unfolds in Htpi1'. eauto.
      introv Hfalse. tryfalse.
      introv Htpi1'. unfolds in Htpi1'.
      rewrite set_a_get_a' in Htpi1'.
      unfolds. eauto.
      introv Hfalse. tryfalse.
      rewrite set_a_get_a';[eauto|introv Hfalse;tryfalse].
      eapply H35.

      unfolds.
      unfolds in Hcont'.
      destruct Hcont' as [Hcont'|Hcont'].
      left. eauto.
      right. destruct Hcont' as (c1_ & c2_ & ke_ & ks'_ & Hks1 & Hks2 & Hcmd_).
      inverts Hks1. inverts Hks2. do 4 eexists. split. eauto. split. eauto.
      
      unfolds in Hcmd_.
      destruct Hcmd_ as [Hcmd_|Hcmd_].
      unfolds. left. eauto.
      unfolds. right.
      simpljoin.
      do 2 eexists.
      split. eauto. split. eauto.
      split. 2:split. 3:split;eauto.
      eapply stmt_equiv_qref_preserve.
      eapply H41.
      instantiate(1:= O1).
      unfolds.
      introv Habs1 Habs1'.
      rewrite set_a_get_a' in Habs1';[idtac|introv Hfalse;tryfalse].
      rewrite Habs1' in Habs1. inverts Habs1.
      introv Hmqs. eauto.
      
      unfolds. 
      introv Ha1 Ha1'.
      rewrite set_a_get_a' in Ha1';[idtac|introv Hfalse;tryfalse].
      rewrite Ha1' in Ha1. inverts Ha1.
      introv He. eauto.

      eapply eqdom_frm_domimpl.
      eapply H14. eapply H28. eapply Hjoin1.
      
      unfolds.
      intros. unfolds.
      introv Hdom. split. introv Htpi1'.
      unfolds. rewrite set_a_get_a'.
      unfolds in Htpi1'. eauto.
      introv Hfalse. tryfalse.
      introv Htpi1'. unfolds in Htpi1'.
      rewrite set_a_get_a' in Htpi1'.
      unfolds. eauto.
      introv Hfalse. tryfalse.
      rewrite set_a_get_a';[eauto|introv Hfalse;tryfalse].
      eapply H36.
      
      eapply stmt_equiv_qref_preserve.
      lets Hst:stmt_equiv_sym H41.
      eapply Hst.
      instantiate(1:= O2).
      unfolds.
      introv Habs1 Habs1'.
      rewrite set_a_get_a' in Habs1';[idtac|introv Hfalse;tryfalse].
      rewrite Habs1' in Habs1. inverts Habs1.
      introv Hmqs. eauto.
      
      unfolds. 
      introv Ha1 Ha1'.
      rewrite set_a_get_a' in Ha1';[idtac|introv Hfalse;tryfalse].
      rewrite Ha1' in Ha1. inverts Ha1.
      introv He. eauto.

      eapply eqdom_frm_domimpl.
      eapply H5. eapply H17. eapply Hjoin2.
      
      unfolds.
      intros. unfolds.
      introv Hdom. split. introv Htpi1'.
      unfolds. rewrite set_a_get_a'.
      unfolds in Htpi1'. eauto.
      introv Hfalse. tryfalse.
      introv Htpi1'. unfolds in Htpi1'.
      rewrite set_a_get_a' in Htpi1'.
      unfolds. eauto.
      introv Hfalse. tryfalse.
      rewrite set_a_get_a';[eauto|introv Hfalse;tryfalse].
      eapply H37.
    }
  }
  casetac t2 t3 Ht2e Ht2ne.
  2:{
    casetac pr pr1 Hpe Hpne.
    {
      subst pr1. lets Hfalse:tid_unique Htpi2.
      unfold task_prio_id in Hfalse.
      specialize(Hfalse Htpi2'). tryfalse.
    }
    {
      subst t0. lets Hfalse:prio_unique Htpi1.
      unfold task_prio_id in Hfalse.
      specialize(Hfalse Htpi1'). tryfalse.
    }
  }
  subst t0. subst t3.
  rewrite set_a_get_a. rewrite set_a_get_a.
  unfold task_prio_id in Htce_. 
  lets Htc:Htce_ Hdom Htpi1' Htpi2'.
  clear Htce_.
  destruct Htc as (c1' & c2' & ke' & ks1' & ks2' & Hg1 & Hg2 & Hcmd' & Hcont').
  rewrite HC1 in Hg1. inverts Hg1. rewrite HC2 in Hg2. inverts Hg2.
  do 5 eexists. split. eauto. split. eauto.
  unfolds in Hcmd'. split. unfolds.
  destruct Hcmd' as [Hcmd'|Hcmd'].
  destruct Hcmd' as (Hcmd1' & Hcmd2').
  inverts Hcmd2'.
  destruct Hcmd1' as (Hcmd11' & Hcmd12').
  unfolds in Hcmd11'. destruct Hcmd11' as [Hcmd111' | Hcmd112'].
  simpljoin. tryfalse.
  simpljoin. inverts H18. destruct H47.
  eexists. eauto.
  right. 
  destruct Hcmd' as (cd1_ & cd2_ & Hcurs1 & Hcurs2 & Hhead1 & Hhead2 & Hve & Hse).
  inverts Hcurs1. inverts Hcurs2.
  do 2 eexists. split. eauto. split. eauto.
  split. simpl. eauto. split. simpl. eauto.
  
  lets Hbfe_:Hbfe.
  unfolds in Hbfe_.
  simpljoin. unfolds in Hhsat1. simpljoin. destruct Hhsat1;tryfalse. simpljoin. inverts H.
  lets He1:H29 H1.
  destruct He1 as (He1 & He2).
  eapply join_get_get_l in H32;eauto.
  eapply join_get_get_l in H4;eauto.
  rewrite H4 in H18. inverts H18.
  rewrite H32 in H26. inverts H26.
  lets Hp:He2 H13 H34.
  destruct Hp as (Hp1 & Hp2).
  unfolds in Hp1.
  simpljoin. inverts H2.
  split. unfolds. introv Hn1 Hn2 Hl1 Hl2. simpl in *.
  inverts Hn1. inverts Hn2. destruct i. simpl in *.
  inverts Hl1. inverts Hl2. eauto.
  simpl in *. inverts H. eauto. simpl in *.
  destruct i;simpl in *;tryfalse.
  unfolds.
  right. split. introv Hfaf. simpljoin. tryfalse.
  do 9 right. left. 
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 10%nat.


  unfolds in Hcont'. unfolds.
  destruct Hcont' as [Hcont'|Hcont']. left. eauto.
  destruct Hcont' as (c1_ & c2_ & ke_ & ks_ & Hke1 & Hke2 & Hcmd).
  inverts Hke1. inverts Hke2. right. do 4 eexists. split. eauto.
  split. eauto. 
  unfolds in Hcmd. unfolds. destruct Hcmd as [Hcmd|Hcmd].
  left. eauto. right. destruct Hcmd as (cd1_ & cd2_ & Hc1 & Hc2 & Hhead1 & Hhead2 & Hvl & Hst).
  inverts Hc1. inverts Hc2. do 2 eexists. split. eauto. split. eauto.
  split.
  eapply stmt_equiv_qref_preserve.
  eapply Hst.
  instantiate(1:= O1).
  unfolds.
  introv Habs1 Habs1'.
  rewrite set_a_get_a' in Habs1';[idtac|introv Hfalse;tryfalse].
  rewrite Habs1' in Habs1. inverts Habs1.
  introv Hmqs. eauto.
  
  unfolds. 
  introv Ha1 Ha1'.
  rewrite set_a_get_a' in Ha1';[idtac|introv Hfalse;tryfalse].
  rewrite Ha1' in Ha1. inverts Ha1.
  introv He. eauto.

  eapply eqdom_frm_domimpl.
  eapply H14. eapply H28. eapply Hjoin1.
  
  unfolds.
  intros. unfolds.
  introv Hdom'. split. introv Htpi1_.
  unfolds. rewrite set_a_get_a'.
  unfolds in Htpi1_. eauto.
  introv Hfalse. tryfalse.
  introv Htpi1_. unfolds in Htpi1_.
  rewrite set_a_get_a' in Htpi1_.
  unfolds. eauto.
  introv Hfalse. tryfalse.
  rewrite set_a_get_a';[eauto|introv Hfalse;tryfalse].
  eapply Hhead1.
  split.
  eapply stmt_equiv_qref_preserve.
  lets Hst_:stmt_equiv_sym Hst.
  eapply Hst_.
  instantiate(1:= O2).
  unfolds.
  introv Habs1 Habs1'.
  rewrite set_a_get_a' in Habs1';[idtac|introv Hfalse;tryfalse].
  rewrite Habs1' in Habs1. inverts Habs1.
  introv Hmqs. eauto.
  
  unfolds. 
  introv Ha1 Ha1'.
  rewrite set_a_get_a' in Ha1';[idtac|introv Hfalse;tryfalse].
  rewrite Ha1' in Ha1. inverts Ha1.
  introv He. eauto.

  eapply eqdom_frm_domimpl.
  eapply H5. eapply H17. eapply Hjoin2.
  
  unfolds.
  intros. unfolds.
  introv Hdom_. split. introv Htpi1_.
  unfolds. rewrite set_a_get_a'.
  unfolds in Htpi1_. eauto.
  introv Hfalse. tryfalse.
  introv Htpi1_. unfolds in Htpi1_.
  rewrite set_a_get_a' in Htpi1_.
  unfolds. eauto.
  introv Hfalse. tryfalse.
  rewrite set_a_get_a';[eauto|introv Hfalse;tryfalse].
  eapply Hhead2.
  split;eauto.
  introv Hfalse;tryfalse.
  introv Hfalse;tryfalse.
  (*data equiv*)
  lets Hde_:Hde.
  unfolds in Hde_.
  destruct Hde_ as (Hce' & Hbe' & Hkde' & Hcde').
  unfolds. split. 
  unfolds in Hce'. unfolds.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  destruct Hce' as (t1' & t2' & Hgc1 & Hgc2 & Hd).
  do 2 eexists. split. eauto. split. eauto.
  introv Htpi1' Htpi2' Hdom'.
  unfolds in Htpi1'. rewrite set_a_get_a' in Htpi1';[idtac|introv Hff;tryfalse].
  unfolds in Htpi2'. rewrite set_a_get_a' in Htpi2';[idtac|introv Hff;tryfalse].
  unfold task_prio_id in Hd. lets H': Hd Htpi1' Htpi2' Hdom'.
  eauto.

  split. unfolds.
  unfolds in Hbe'. destruct Hbe' as (Hbe1' & Hbe2').
  split. unfolds. unfolds in Hbe1'.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  eapply Hbe1'.

  unfolds. unfolds in Hbe2'.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  eapply Hbe2'.

  split.
  unfolds in Hkde'. unfolds.
  destruct Hkde' as (Hkde1' & Hkde2' & Hkde3' & Hkde4' & Hkde5').
  split. unfolds. unfolds in Hkde1'.
  
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  unfold task_prio_id.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  unfold task_prio_id in Hkde1'.
  eapply Hkde1'.
  
  split. unfolds. unfolds in Hkde2'.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].

  simpljoin. do 2 eexists.
  intros. split. eauto. split. eauto.
  introv Hmqidx.
  lets Hkde2': H25 Hmqidx.
  simpljoin. split. eauto.
  introv Hgmq1 Hgmq2.
  lets Hkde2': H1 Hgmq1 Hgmq2.
  simpljoin.



  eapply join_get_get_l in H4;eauto.
  eapply join_get_get_l in H32;eauto.
  rewrite H27 in H4. rewrite H39 in H32.
  inverts H4. inverts H32.
  eapply mq_equiv_buffer_ref_preserve2; eauto.
  rewrite set_a_get_a. eauto.
  rewrite set_a_get_a. eauto.

  unfolds.
  intros. unfolds.
  introv Hdom_. split.
  introv Htpi1'. unfolds. rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  unfolds in Htpi1'. eauto.
  introv Htpi1'. unfolds in Htpi1'.
  rewrite set_a_get_a' in Htpi1';[idtac|introv Hff;tryfalse].
  unfolds. eauto.

  unfolds.
  introv Hdom_. split.
  introv Htpi1'. unfolds. rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  unfolds in Htpi1'. eauto.
  introv Htpi1'. unfolds in Htpi1'.
  rewrite set_a_get_a' in Htpi1';[idtac|introv Hff;tryfalse].
  unfolds. eauto.

  split.
  unfolds. unfolds in Hkde3'.
  simpljoin.
  do 4 eexists. split.
  rewrite set_a_get_a';[eauto|introv Hff;tryfalse].
  split.
  rewrite set_a_get_a';[eauto|introv Hff;tryfalse].
  split. rewrite set_a_get_a. eauto.
  split. rewrite set_a_get_a. eauto.
  introv Haddr.
  lets Hpe: H29 Haddr.
  destruct Hpe as (Hpe1 & Hpe).
  split. eauto.
  eapply join_get_get_l in H4;eauto.
  eapply join_get_get_l in H32;eauto.
  rewrite H25 in H4. rewrite H26 in H32.
  inverts H32. inverts H4.
  casetac x7 a Ht Hf.
-
  subst.
  do 4 rewrite set_a_get_a. 
  split.
  {
    split. intros. destruct H as (tls1 & H).
    inverts H. intros. destruct H as (tls1 & H).
    inverts H.
  }
  introv He1 He2.
  inverts He1.
-
  do 4 (rewrite set_a_get_a'; eauto).
  destruct Hpe as (Hpe1_ & Hpe2_).
  split; auto.

  introv Hg1 Hg2.
  specializes Hpe2_; eauto.
  eapply tidls_equiv_pp_preserve2.
  eapply Hpe2_.

  unfolds. intros. unfolds. introv Hdom_.
  split. introv Htpi1_.
  unfolds in Htpi1_. unfolds.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  eauto. introv Htpi1_.
  unfolds in Htpi1_. unfolds.
  rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
  eauto.

  unfolds. intros. unfolds. introv Hdom_.
  split. introv Htpi1_.
  unfolds in Htpi1_. unfolds.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  eauto. introv Htpi1_.
  unfolds in Htpi1_. unfolds.
  rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
  eauto.
(*data->bufferequiv*)
-
  split.
  unfolds. rewrite set_a_get_a.
  rewrite set_a_get_a.
  do 2 eexists. split. eauto. split. eauto.
  introv Hbufdom.
  unfolds in Hkde4'.
  simpljoin.
  casetac x7 eid Ht Hf.
  + subst.
    repeat rewrite set_a_get_a.
    split.
    * split; 
        introv Hex; simpljoin; do 2 eexists; eauto.
    * introv Hso1 Hso2.
      inverts Hso1.
      inverts Hso2.
      lets Hd: H25 Hbufdom.
      destruct Hd as (Hy& Ha).
      eapply join_get_get_l in H4;eauto.
      eapply join_get_get_l in H32;eauto.
      rewrite H18 in H4. rewrite H24 in H32.
      inverts H4. inverts H32.
      specializes Ha; eauto.
      destruct Ha as (Hme & Hte).
      split.
      **
        unfold mq_ed_equiv in *.
        simpljoin.
        do 2 inv_msgq. 
        do 4 eexists. split; eauto. split; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
        unfolds. intros. unfolds. introv Hdom_.
        split. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
        eauto. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
        eauto.

        unfolds. intros. unfolds. introv Hdom_.
        split. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
        eauto. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
        eauto.

      **
        eapply tidls_equiv_pp_preserve2; eauto.
        unfolds. intros. unfolds. introv Hdom_.
        split. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
        eauto. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
        eauto.

        unfolds. intros. unfolds. introv Hdom_.
        split. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
        eauto. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
        eauto.

  +
    eapply join_get_get_l in H4;eauto.
    eapply join_get_get_l in H32;eauto.
    rewrite H18 in H4. rewrite H24 in H32.
    inverts H4. inverts H32.
    lets Hd: H25 Hbufdom.
    destruct Hd as (Hy& Ha).
    repeat (rewrite set_a_get_a'; eauto).
    split.
    * auto.
    * introv Hg1 Hg2.
      specializes Ha; eauto.
      simpljoin.
      split.
      ** 


        eapply mq_ed_equiv_pp_preserve2; eauto. 
        unfolds. intros. unfolds. introv Hdom_.
        split. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
        eauto. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
        eauto.

        unfolds. intros. unfolds. introv Hdom_.
        split. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
        eauto. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
        eauto.
      ** 
        eapply  tidls_equiv_pp_preserve2; eauto. 
        unfolds. intros. unfolds. introv Hdom_.
        split. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
        eauto. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
        eauto.

        unfolds. intros. unfolds. introv Hdom_.
        split. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
        eauto. introv Htpi1_.
        unfolds in Htpi1_. unfolds.
        rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
        eauto.
  +
    eapply cap_equiv_preserve2; eauto.
    rewrite set_a_get_a';[eauto|introv Hff;tryfalse].
    rewrite set_a_get_a';[eauto|introv Hff;tryfalse].
    unfold mq_ptr.
    rewrite set_a_get_a';[eauto|introv Hff;tryfalse].
    split. intros. eauto. intros. eauto.
    unfold mq_ptr.
    rewrite set_a_get_a';[eauto|introv Hff;tryfalse].
    split. intros. eauto. intros. eauto.
-
  eapply cde_prio_preserved_preserve2; eauto.
  unfolds. intros. unfolds. introv Hdom_.
  split. introv Htpi1_.
  unfolds in Htpi1_. unfolds.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  eauto. introv Htpi1_.
  unfolds in Htpi1_. unfolds.
  rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
  eauto.

  unfolds. intros. unfolds. introv Hdom_.
  split. introv Htpi1_.
  unfolds in Htpi1_. unfolds.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  eauto. introv Htpi1_.
  unfolds in Htpi1_. unfolds.
  rewrite set_a_get_a' in Htpi1_;[idtac|introv Hff;tryfalse].
  eauto.
}



{
  false. lets Hff: buffer_equiv_nnil_impl_ Hbfe Hhsat1 .
  destruct Hff. simpljoin.
  do 7 eexists. split. eauto.
  split. eauto. split.  eauto. eauto.
  simpljoin. rewrite H29 in H2.
  inverts H2. inverts H. rewrite H32 in H6.
  inverts H6. tryfalse.
}

{
  false. lets Hff: buffer_equiv_nil_impl_ Hbfe Hhsat1 .
  destruct Hff. simpljoin.
  do 5 eexists. split. eauto. split. eauto. eauto.
  simpljoin. rewrite H27 in H2. inverts H2.
  inverts H. rewrite H29 in H6. inverts H6.
}
{
  eapply buffer_equiv_sym in Hbfe.
  lets Hfff:buffer_equiv_nemp_impl_ Hbfe Hhsat2.
  destruct Hfff.
  unfolds in H3.
  unfolds in H4.
  simpljoin.
  inverts H1.   inverts H.
  eapply join_get_get_l in H23;eauto.
  inverts H0.
  do 7 eexists.
  split. eauto. split. eauto. eauto.
  simpljoin.
  destruct H17.
  rewrite H15 in H2. inverts H5.
  inverts H0. inverts H. inverts H2.
   do 4 eexists. eauto.
}

{
  false. lets Hff: buffer_equiv_pwlnil_impl_ Hbfe Hhsat1 .
  destruct Hff. simpljoin.
  do 7 eexists. split. eauto.
  split. eauto. inverts H. eauto.
  simpljoin.
  inverts H. rewrite H2 in H26. inverts H26.
  rewrite H6 in H27. inverts H27. tryfalse.
}
{
  (*qpend_get_ex_pwl_before_sched_body*) 
  lets Hpp1: qpend_get_expwl_before_sched_prio_preserved H4 H32 H33.
  lets Hpp2: qpend_get_expwl_before_sched_prio_preserved H3 H19 H20.
  split.   
  - (* code_equiv_tskd *)
    eapply code_equiv_upd2_preserve_st'; eauto.
    {
      (* cmd_equiv *)
      unfolds.
      right.
      do 2 eexists.
      split; eauto. split; eauto.
      split. simpl; auto. split. simpl; auto.
      split.
      unfolds in H3. unfolds in H4. simpljoin.
      inverts H. inverts H1.
      lets Hbuf: Hbfe. lets Hbid1: Hhsat2. 
      lets Hbid2: Hhsat1.
      eapply join_get_get_l in H3;eauto.
      eapply join_get_get_l in H39;eauto.
      inverts H3. inverts H39. inverts H0.
      rewrite H49 in H2. rewrite H35 in H1.
      inverts H1. inverts H2.
      unfolds in Hbuf.
      destruct Hbuf as (els1 & els2 & Hgete1 & Hgete2 & Hbuf).
      rewrite Hgete1 in H35. rewrite Hgete2 in H49.
      inverts H35. inverts H49.
      unfolds in Hbid1. unfolds in Hbid2.
      destruct Hbid1 as [Hbid1|Hbid1];tryfalse.
      destruct Hbid1 as (a & Hi & Hbindom).
      inverts Hi. specialize(Hbuf a Hbindom).
      destruct Hbuf as (Hbuf1 & Hbuf2).
      destruct H48;simpljoin;tryfalse.
      destruct H34;simpljoin;tryfalse.
      lets H': Hbuf2 H6 H41.
      destruct H' as (H1' & H2').
      unfolds in H1'.
      simpljoin. inverts H. inverts H2.
      unfolds. introv Hh1 Hh2 Hn1 Hn2.
      simpl in Hh1. simpl in Hh2.
      inverts Hh1. inverts Hh2.
      destruct i1. simpl in *.
      inverts Hn1. inverts Hn2. eauto.
      simpl in *. destruct i1.
      simpl in *. inverts Hn1. inverts Hn2. eauto.

      unfolds.
      right. 
      split. introv Hf. simpljoin. tryfalse.
      right. right. right. right. right.  right. right. right. right. left.

      solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 4%nat. 
    }
    eapply cont_equiv_qref_preserve; eauto. 
    eapply qpend_exwt_succ_mqref_preserve; eauto.
    eapply qpend_exwt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qpend_exwt_succ_qprt_preserve; eauto.
    eapply qpend_exwt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.      
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.    
    eapply qpend_gepb_succ_csp_preserve;eauto.
    eapply qpend_gepb_succ_csp_preserve. eapply H3. eauto. eauto.

    lets H__: code_equiv_hsat_neq_st'. 
    eapply H__; eauto.
    eapply qpend_exwt_succ_mqref_preserve; eauto.
    eapply qpend_exwt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qpend_exwt_succ_qprt_preserve; eauto.
    eapply qpend_exwt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.                    
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    eapply qpend_gepb_succ_csp_preserve;eauto.
    eapply qpend_gepb_succ_csp_preserve. eapply H3. eauto. eauto.
  - (*data_equiv_tskd *)




  (*data_equiv*)   
   
  unfolds. lets Hspec1 : H3. lets Hspec2 : H4.
  unfolds in H3. unfolds in H4.
  simpljoin.
  
  destruct H48;simpljoin;tryfalse.
  destruct H34;simpljoin;tryfalse.
  inverts H28. inverts H15.
  lets Hjoin1: H33. lets Hjoin2: H20.
  eapply join_get_set_eq_2 in H33;eauto.
  eapply join_get_set_eq_2 in H20;eauto.
  inverts H33. inverts H20.
  clear H15. clear H2.
  
  (*ctid equiv*)
  split.  unfolds.
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  rewrite set_a_get_a';[idtac|introv Hff;tryfalse].
  lets Hce_:Hctide_. 
  unfolds in Hce_. 
  destruct Hce_ as (t1' & t2' & Hgc1 & Hgc2 & Hd).
  do 2 eexists. split. eauto. split. eauto.
  introv Htpi1' Htpi2' Hdom.
  unfolds in Hpp1. 
  specialize(Hpp1 i).
  unfolds in Hpp1.
  lets Hpp1_:Hpp1 Hdom.
  destruct Hpp1_ as (Hpp11 & Hpp12).
  lets He1: Hpp12 Htpi1'.
  assert(exists td,dom_for_prio pr2 = td);eauto.
  destruct H2.
  unfolds in Hpp2. 
  specialize(Hpp2 x0).
  unfolds in Hpp2.
  lets Hpp2_:Hpp2 H2.
  destruct Hpp2_ as (Hpp21 & Hpp22).
  lets He2: Hpp22 Htpi2'.
  lets Ht: Hd He1 He2.
  unfolds in Hde. 
  destruct Hde as (Hd1 & _ & _ & _ &_).
  unfolds in Hd1. destruct Hd1 as (t1_ & t2_ & Hgo1 & Hgo2 & Hd_).
  rewrite Hgc1 in Hgo1. rewrite Hgc2 in Hgo2.
  inverts Hgo1. inverts Hgo2.
  lets Htt:Hd_ He1 He2 Hdom. eauto.
  (*bufquiv*)
  split.
  destruct Hde as (_ & bf & _ & _ &_).
  lets Hbuf: bf.
  unfolds in Hbuf. destruct Hbuf as (Hbuf1 & Hbuf2).
  destruct Hbuf1 as (ibuf1 & ibuf2 & Hgibu1 &Hgibu2 & Hibue).
  destruct Hbuf2 as (obu1 & obu2 & Hgobu1 & Hgobu2 & Hobue).
  unfolds. split.
  unfolds. try repeat (rewrite set_a_get_a';[eauto|introv Hff;tryfalse]).
  unfolds. try repeat (rewrite set_a_get_a';[eauto|introv Hff;tryfalse]).

  (*kernl equiv*)
  split.
  unfolds. split.
  (*kernl task equiv*)

  unfolds in Hde. destruct Hde as (_ & _ & Hkde_ &_).
  eapply knl_mq_equiv_pendexwt_preserve2.
  eapply Hkde_. eauto. eapply Hbfe. eapply Hhsat1.
  eapply Hspec2. eapply Hspec1. eauto. eauto. eauto. eauto.

  (*kernl mq equiv*)
  split.
  unfolds in Hde. destruct Hde as (_ & _ & Hkde_ &_).
  destruct Hkde_ as (_ & Hmqe & _).
  lets Hmqe_:Hmqe.
  unfolds. unfolds in Hmqe_.
  try repeat (rewrite set_a_get_a';[eauto|introv Hff;tryfalse]).
  destruct Hmqe_ as (mq1 & mq2 & Hgmq1 & Hgmq2 & Hmq).
  do 2 eexists. split. eauto. split. eauto.
  introv Hmqi. specialize(Hmq i1 Hmqi).
  destruct Hmq as (Hmq1 & Hmq2).
  split. eauto. introv Hme1 Hme2.
  specializes Hmq2;eauto.
  eapply mq_equiv_buffer_ref_preserve2;eauto.
  rewrite set_a_get_a. 
  eapply join_get_get_l in H3;eauto.
  rewrite H3 in H35. inverts H35.
  inverts H. eauto.
  rewrite set_a_get_a. 
  eapply join_get_get_l in H39;eauto.
  rewrite H39 in H49. inverts H49.
  inverts H1. eauto.
  (*port_equiv*)
  lets H__: buffer_qpend_get_ex_pwl_before_sched_dteq_preserve2.
  specializes H__;eauto. simpljoin.
  split. eauto. split. eauto. eauto. eauto.
  lets H__: buffer_qpend_get_ex_pwl_before_sched_dteq_preserve2.
  specializes H__;eauto. simpljoin. eauto.
}
{
  false. lets Hff: buffer_equiv_nil_impl_ Hbfe Hhsat1 .
  destruct Hff. simpljoin.
  do 5 eexists. split. eauto. split. eauto. eauto.
  simpljoin. inverts H. rewrite H29 in H2. inverts H2.
  rewrite H31 in H6. inverts H6. 
}
{
  eapply buffer_equiv_sym in Hbfe.
  lets Hfff:buffer_equiv_nil_impl_ Hbfe Hhsat2.
  destruct Hfff.
  unfolds in H3.
  unfolds in H4.
  simpljoin.
  inverts H1.   inverts H.
  eapply join_get_get_l in H25;eauto.
  inverts H0.
  do 7 eexists.
  eauto.  eauto. 
  simpljoin.
  destruct H18.
  rewrite H16 in H2. inverts H2.
  inverts H0.
  inverts H. do 4 eexists. eauto.
}
{
  eapply buffer_equiv_sym in Hbfe.
  false. lets Hff: buffer_equiv_nil_impl_ Hbfe Hhsat2 .
  destruct Hff. simpljoin.
  do 5 eexists. split. eauto. split. eauto. eauto. inverts H. eauto.
  simpljoin. inverts H. rewrite H16 in H2. inverts H2.
  inverts H0. rewrite H18 in H6. inverts H6. 
}
{
  eapply buffer_equiv_sym in Hbfe.
  false. lets Hff: buffer_equiv_nil_impl_ Hbfe Hhsat2 .
  destruct Hff. simpljoin.
  do 5 eexists. split. eauto. split. eauto. eauto. inverts H. eauto.
  simpljoin. inverts H. rewrite H16 in H2. inverts H2.
  inverts H0. rewrite H18 in H6. inverts H6. 
}
{
  (*qpend_block_body dyw*)

split.
- (* code_equiv *) 
  lets Hpp1: qpend_block_prio_preserved O0 O'0 Of0 O1 O1'; eauto. 
  specializes Hpp1; eauto.
  lets Hpp2: qpend_block_prio_preserved O O' Of O2 O2'; eauto.
  specializes Hpp2; eauto.
  apply11 qpend_block_body qpend_block_body
    qpend_block_cpid_same Hcpeq2 Hcpeq1.
  specializes Hcpeq1; eauto.
  specializes Hcpeq2; eauto. 

  eapply code_equiv_upd2_preserve_st'; eauto.

  (* cmd_equiv *)
  unfolds.
  right.
  do 2 eexists.
  split; eauto. split; eauto.
  split. simpl; auto.
  split. auto.
  split.
  eapply vl_equiv_nil; eauto.
  unfolds.
  right.
  split. introv Hf. simpljoin. tryfalse.
  right; right; right; right; right; right; right; right; right; left.
  unfolds. 
  match type of Hlenvl with length ?vl = _ => exists vl end. 
  match type of Hlenvl1 with length ?vl = _ => exists vl end.
  match type of Hlenvl2 with length ?vl = _ => exists vl end.
  exists 6%nat. splits; auto.
  
  (* cont_equiv *)
  eapply cont_equiv_qref_preserve; eauto.  
  eapply qpend_block_mqref_preserve; eauto. 
  eapply qpend_block_mqref_preserve with (O0:=O) (O0':=O'); eauto.
  eapply qpend_block_qprt_preserve; eauto. 
  eapply qpend_block_qprt_preserve with (O0:=O) (O0':=O'); eauto.
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
  
  lets H__: code_equiv_hsat_neq_st'; eauto.
  eapply H__; eauto. 
  eapply qpend_block_mqref_preserve; eauto.
  eapply qpend_block_mqref_preserve with (O0:=O) (O0':=O'); eauto.
  eapply qpend_block_qprt_preserve; eauto. 
  eapply qpend_block_qprt_preserve with (O0:=O) (O0':=O'); eauto.
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
- eapply buffer_qpend_block_dteq_preserve2; eauto. 
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

}
destruct k.
(* k=4 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
simpl in Hhsat1.
simpl in Hhsat2.
symexe.
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl. auto.
  split. simpl. auto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  unfolds in Hvleq. simpl in Hvleq.
  simpl in Hhvl2.
  inverts Hhvl2.
  introv Hv1 Hv2.  specialize(Hvleq ( v1 :: nil) (v2 :: nil)).
  assert (Some (v1 :: nil) = Some (v1 :: nil));eauto.
  assert (Some (v2 :: nil) = Some (v2 :: nil));eauto.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split.
  introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. right. right. left.
  (* establish bufferpost_equiv *)
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 5%nat.
}
destruct k.
(* k=5 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
simpl in Hhsat1.
simpl in Hhsat2.
symexe.
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl. auto.
  split. simpl. auto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  unfolds in Hvleq. simpl in Hvleq.
  simpl in Hhvl2.
  inverts Hhvl2.
  introv Hv1 Hv2.  specialize(Hvleq ( v1 :: nil) (v2 :: nil)).
  assert (Some (v1 :: nil) = Some (v1 :: nil));eauto.
  assert (Some (v2 :: nil) = Some (v2 :: nil));eauto.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split.
  introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. right. right. left.
  (* establish bufferpost_equiv *)
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 10%nat.
}
destruct k.
(* k=6 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
simpl in Hhsat1.
simpl in Hhsat2.
symexe.
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl. auto.
  split. simpl. auto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  introv Hf. rewrite nth_error_nil in Hf. tryfalse.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split.
  introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. right. right. left.
  (* establish bufferpost_equiv *)
  solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 7%nat.
}
destruct k.
(* k=7 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
simpl in Hhsat1.
simpl in Hhsat2.
symexe.

{
  lets Htemp1 : qst_Oeq H3; lets Htemp2 : qst_Oeq H4. subst.
  lets H_:join_Oeq_lemma H18 H19.
  lets H__:join_Oeq_lemma H12 H13.
  subst O1'. subst O2'.
  split;eauto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl. auto.
  split. simpl. auto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  introv Hf. rewrite nth_error_nil in Hf. tryfalse.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split.
  introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. right. right. left.
  (* establish bufferpost_equiv *)
  solve_bufferpost_eq Hlenvl Hlenvl1 Hlenvl2 8%nat.
  
}
destruct k.
(* k=8 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
simpl in Hhsat1.
simpl in Hhsat2.
symexe.
{
  (*qpend_block_get_body*)
split.
- (* code_equiv *) 
  lets Hpp1: qpend_block_get_prio_preserved O0 O'0 Of0 O1 O1'; eauto. 
  specializes Hpp1; eauto.
  lets Hpp2: qpend_block_get_prio_preserved O O' Of O2 O2'; eauto.
  specializes Hpp2; eauto.
  apply11 qpend_block_get_body qpend_block_get_body
    qpend_block_get_cpid_same Hcpeq2 Hcpeq1.
  specializes Hcpeq1; eauto.
  specializes Hcpeq2; eauto. 

  eapply code_equiv_upd2_preserve_st'; eauto.

  (* cmd_equiv *)
  unfolds.
  right.
  do 2 eexists.
  split; eauto. split; eauto.
  split. simpl; auto.
  split. auto.
  split. auto.
  split.
  {
    clear H8; clear H15.
    unfolds in Hkte.
    unfold qpend_block_get_body in *.
    simpljoin.
    assert (get O1 curtid = Some (oscurt x10)) by (eapply join_get_get_l; eauto).
    assert (get O2 curtid = Some (oscurt x18)) by (eapply join_get_get_l; eauto).
    l_rew21_inv1 (get O1 curtid).
    l_rew21_inv1 (get O2 curtid).
    assert (get O1 abstcblsid = Some (abstcblist x5)) by (eapply join_get_get_l; eauto).
    assert (get O2 abstcblsid = Some (abstcblist x13)) by (eapply join_get_get_l; eauto).
    l_rew21_inv1 (get O1 abstcblsid).
    l_rew21_inv1 (get O2 abstcblsid).
    specialize(H27 pr ltac:(tauto)).
    destruct H27 as (_ & H27).
    assert (task_prio_id O1 x12 t1) by (unfolds; do 5 eexists; split; eauto).
    assert (task_prio_id O2 x20 t2) by (unfolds; do 5 eexists; split; eauto).
    assert (x12 = pr) by (eapply prio_unique; eauto).
    assert (x20 = pr) by (eapply prio_unique; eauto).
    subst.
    lets H_: H27 H4 H19.
    inverts H. inverts H0.
    destruct H15; simpljoin; tryfalse.
    destruct H25; simpljoin; tryfalse.
    apply vl_equiv_refl.
  }
  unfolds.
  right.
  split. introv Hf. simpljoin. tryfalse.
  right; right; right; right; right; right; right; right; right; left.
  unfolds. 
  match type of Hlenvl with length ?vl = _ => exists vl end. 
  match type of Hlenvl1 with length ?vl = _ => exists vl end.
  match type of Hlenvl2 with length ?vl = _ => exists vl end.
  exists 10%nat. splits; auto.
  
  (* cont_equiv *)
  eapply cont_equiv_qref_preserve; eauto.  
  eapply qpend_block_get_mqref_preserve; eauto. 
  eapply qpend_block_get_mqref_preserve with (O0:=O) (O0':=O'); eauto.
  eapply qpend_block_get_qprt_preserve; eauto. 
  eapply qpend_block_get_qprt_preserve with (O0:=O) (O0':=O'); eauto.
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
  
  lets H__: code_equiv_hsat_neq_st'; eauto.
  eapply H__; eauto. 
  eapply qpend_block_get_mqref_preserve; eauto.
  eapply qpend_block_get_mqref_preserve with (O0:=O) (O0':=O'); eauto.
  eapply qpend_block_get_qprt_preserve; eauto. 
  eapply qpend_block_get_qprt_preserve with (O0:=O) (O0':=O'); eauto.
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
- 
  eapply buffer_qpend_block_get_dteq_preserve2 ; eauto. 
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

}


{
  lets Hfals:os_stat_qpend_false H17 H9.
  destruct Hfals.
  eauto. eauto. eauto.
  eauto. eauto. eauto.  eauto. eauto.
  
}
{
  lets Hfals:os_stat_qpend_false H10 H16.
  destruct Hfals.
  eapply kernel_task_equiv_sym.
  eauto. eauto. eauto.
  eauto. eauto. 
  eapply kernel_mq_equiv_sym.
  eauto.  eauto. eauto.
}
{

split.
- (* code_equiv *) 
  lets Hpp1: qpend_to_body_prio_preserved O0 O'0 Of0 O1 O1'; eauto. 
  specializes Hpp1; eauto.
  lets Hpp2: qpend_to_body_prio_preserved O O' Of O2 O2'; eauto.
  specializes Hpp2; eauto.
  apply11 qpend_to_body qpend_to_body
    qpend_to_cpid_same Hcpeq2 Hcpeq1.
  specializes Hcpeq1; eauto.
  specializes Hcpeq2; eauto. 

  eapply code_equiv_upd2_preserve_st'; eauto.

  (* cmd_equiv *)
  unfolds.
  right.
  do 2 eexists.
  split; eauto. split; eauto.
  split. simpl; auto.
  split. auto.
  split. auto.
  split.
  {
    clear H10; clear H17.
    unfolds in Hkte.
    unfold qpend_to_body in *.
    simpljoin.
    assert (get O1 curtid = Some (oscurt x7)) by (eapply join_get_get_l; eauto).
    assert (get O2 curtid = Some (oscurt x18)) by (eapply join_get_get_l; eauto). 
    l_rew21_inv1 (get O1 curtid).
    l_rew21_inv1 (get O2 curtid).
    assert (get O1 abstcblsid = Some (abstcblist x5)) by (eapply join_get_get_l; eauto).
    assert (get O2 abstcblsid = Some (abstcblist x16)) by (eapply join_get_get_l; eauto).
    l_rew21_inv1 (get O1 abstcblsid).
    l_rew21_inv1 (get O2 abstcblsid).
    specialize(H33 pr ltac:(tauto)).
    destruct H33 as (_ & H33).
    assert (task_prio_id O1 x15 t1) by (unfolds; do 5 eexists; split; eauto).
    assert (task_prio_id O2 x26 t2) by (unfolds; do 5 eexists; split; eauto).
    assert (x15 = pr) by (eapply prio_unique; eauto).
    assert (x26 = pr) by (eapply prio_unique; eauto).
    subst.
    lets H_: H33 H4 H24.
    inverts H. inverts H0.
    destruct H18; simpljoin; tryfalse.
    destruct H30; simpljoin; tryfalse.
    apply vl_equiv_refl.
  }
  unfolds.
  right.
  split. introv Hf. simpljoin. tryfalse.
  right; right; right; right; right; right; right; right; right; left.
  unfolds. 
  match type of Hlenvl with length ?vl = _ => exists vl end. 
  match type of Hlenvl1 with length ?vl = _ => exists vl end.
  match type of Hlenvl2 with length ?vl = _ => exists vl end.
  exists 9%nat. splits; auto.
  
  (* cont_equiv *)
  eapply cont_equiv_qref_preserve; eauto.  
  eapply qpend_to_mqref_preserve; eauto. 
  eapply qpend_to_mqref_preserve with (O0:=O) (O0':=O'); eauto.
  eapply qpend_to_qprt_preserve; eauto. 
  eapply qpend_to_qprt_preserve with (O0:=O) (O0':=O'); eauto.
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
  
  lets H__: code_equiv_hsat_neq_st'; eauto.
  eapply H__; eauto. 
  eapply qpend_to_mqref_preserve; eauto.
  eapply qpend_to_mqref_preserve with (O0:=O) (O0':=O'); eauto.
  eapply qpend_to_qprt_preserve; eauto. 
  eapply qpend_to_qprt_preserve with (O0:=O) (O0':=O'); eauto.
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
- eapply buffer_qpend_to_dteq_preserve2 ; eauto. 
  eapply eqdom_frm_domimpl; eauto.
  eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

}
destruct k.
(* k=9 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
simpl in Hhsat1.
simpl in Hhsat2.
symexe. 
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl. auto.
  split. simpl. auto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  unfolds in Hvleq. simpl in Hvleq.
  simpl in Hhvl2.
  inverts Hhvl2.
  introv Hv1 Hv2.  specialize(Hvleq ( v1 :: nil) (v2 :: nil)).
  assert (Some (v1 :: nil) = Some (v1 :: nil));eauto.
  assert (Some (v2 :: nil) = Some (v2 :: nil));eauto.
  (* stmt_equiv *)
  unfold stmt_equiv.
  right.
  split.
  introv Hf. simpljoin. tryfalse.
  right. right. right. right. right. right. right. right. right. left.
  (* establish bufferpost_equiv *)
  solve_bufferpend_eq Hlenvl Hlenvl1 Hlenvl2 10%nat.
}
destruct k.
(* k=10 *)
simpl in Hnth1; inverts Hnth1.
simpl in Hnth2; inverts Hnth2.
simpl in Hhsat1.
simpl in Hhsat2.
symexe. 
{
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto. clear H__.
  unfold cmd_equiv.
  right.
  do 2 eexists. split; eauto. split; eauto.
  split. simpl. auto.
  split. simpl. auto.
  split.
  introv Hhvl1 Hhvl2.
  simpl in Hhvl1.
  inverts Hhvl1.
  unfolds in Hvleq. simpl in Hvleq.
  specialize(Hvleq ( v1 :: nil) (v2 :: nil)).
  assert (Some (v1 :: nil) = Some (v1 :: nil));eauto.
  assert (Some (v2 :: nil) = Some (v2 :: nil));eauto.
  lets Hvle:Hvleq H H0.
  specialize (Hvle 0%nat v1 v2).
  destruct Hvle.
  simpl. eauto.
  simpl. eauto.
  unfolds in H2. unfolds in H4. simpljoin.
  inverts H2. inverts H1.
  (* stmt_equiv *)
  unfold stmt_equiv.
  left. eexists. split;eauto.
}
simpl in Hnth2.
rewrite nth_error_nil in Hnth2.
tryfalse.
Qed. 

