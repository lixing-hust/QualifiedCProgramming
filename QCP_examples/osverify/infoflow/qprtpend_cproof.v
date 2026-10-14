
Require Import FunctionalExtensionality.
Require Import base_tac. 
Require Import memory. 

Require Import math_auto. 
Require Import seplog_lemmas. 

Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import prt_apispecs. 
Require Import osspecs. 
Require Import properties.

Require Import if_assms.
Require Import sem_prop.
Require Import if_succ_gen.
Require Import if_common_lemmas. 
Require Import spec_aux_defs. 
Require Import confidentiality_tactics.
Require Import confidentiality_lemmas.
Require Import equiv_prop. 

Require Import hasrt_sat_preserve.

Require Import ports_cproof_common. 

Require Import ct_pp_lemmas.
          
Set Keyed Unification.  

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

Lemma cpe_no_prtpend_cap_impl:   
  forall pr t1 t2 O1 O2, 
    cap_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    has_no_cap_prtpend O1 ->
    has_no_cap_prtpend O2. 
Proof.
  introv Hce Hct1 Hct2 Htpi1 Htpi2 Hncp.
  unfold cap_equiv in Hce.
  unfold has_no_cap_prtpend in *.
  destruct Hce as (cspc1 & cspc2 & Hg1 & Hg2 & Hall).
  specialize (Hall pr (eq_refl)).
  destruct Hall as (Hcpiff & _).
  simpljoin.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O1 cspaceid).
  unfold task_prio_id in *.
  simpljoin.
  l_rew21_inv1 (get O1 abstcblsid).
  rewrite H1 in H7. inverts H7.
  do 7 eexists. 
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hhcp. apply H3. clear -Hhcp Hcpiff.
  eapply Hcpiff; eauto. 
Qed. 

Lemma prte_port_dir_impl:
  forall O1 O2 vprt pr t1, 
    ~wrong_dom O1 vprt ->
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    get O1 curtid = Some (oscurt t1) ->
    task_prio_id O1 pr t1 ->
    (exists a dpl pcn pd pid pst pin pout pt,
        vprt = Vptr a /\
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, pt)) -> 
    (exists a dpl pcn pd pid pst pin pout pt,
        vprt = Vptr a /\
          get O2 osdomainportid = Some (osdomainport dpl) /\
          get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, pt)). 
Proof.
  introv Hnwd Hpe Hgc1 Htpi1 Hex.
  simpljoin.
  eapply nwrong_dom_dest in Hnwd; eauto.
  unfolds in Hpe.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  match goal with
    H: forall _, _ -> _ |- _ => lets H__: H Hnwd
  end.
  destruct H__ as (Hprteq & _).
  match goal with H: ?t = _, H': ?t = _ |- _ => rewrite H in H' end.
  symmetry in Hprteq. 
  do 9 eexists.
  split; eauto.
Qed. 

Lemma prte_port_type_impl: 
  forall O1 O2 vprt pr t1, 
    ~wrong_dom O1 vprt ->
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    get O1 curtid = Some (oscurt t1) ->
    task_prio_id O1 pr t1 ->
    (exists a dpl pcn pd pid pst pin pout msg,
        vprt = Vptr a /\
          get O1 osdomainportid = Some (osdomainport dpl) /\ 
          get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin, pout, SamplePort msg)) -> 
    (exists a dpl pcn pd pid pst pin pout msg,
        vprt = Vptr a /\
          get O2 osdomainportid = Some (osdomainport dpl) /\ 
          get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin, pout, SamplePort msg)). 
Proof.
  introv Hnwd Hpe Hgc1 Htpi1 Hex. 
  simpljoin. 
  eapply nwrong_dom_dest in Hnwd; eauto. 
  unfolds in Hpe. 
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  match goal with
    H: forall _, _ -> _ |- _ => lets H__: H Hnwd
  end.
  destruct H__ as (Hprteq & _).
  match goal with H: ?t = _, H': ?t = _ |- _ => rewrite H in H' end.
  symmetry in Hprteq. 
  do 9 eexists.
  split; eauto.
Qed.

Lemma qportpend_notnil_tls_same:
  forall v v0 O0 O0' O O' Of v' act, 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    get O abstcblsid = get O' abstcblsid. 
Proof.
  introv Hqnb Hjo Hjo'.
  inverts Hqnb.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  lets H__: join_get_same_l abstcblsid Hjo Hjo'; eauto. 
  repeat rewsimp.
  auto.
Qed. 

Lemma qportpend_notnil_mqref_preserve:
  forall v v0 v' O O' O0 O0' Of act, 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hsend Hjo Hjo'.
  unfolds in Hsend.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgeq: get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  l_rew21_inv1 (get O absmqattrid).
  l_rew21_inv1 (get O' absmqattrid).
  tauto.
Qed.

Lemma qportpend_notnil_qprt_preserve: 
  forall v v0 v' O O' O0 O0' Of act, 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hqpn Hjo Hjo'.
  unfolds in Hqpn.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
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
    l_rew12_inv2 (get O0 osdomainportid).
    kvext_h Hjo' osdomainportid O'.
    l_rew21_inv1 (get O' osdomainportid). 
    introv Hg.
    simpljoin.    
    casetac x a Ht Hf.
    + subst.
      match goal with
        H1: get dpl _ = _, H2: get dpl _ = _ |- _ =>
          rewrite H1 in H2; inverts H2
      end.    
      rewrite set_a_get_a. 
      do 7 eexists. eauto.
    + rewrite set_a_get_a'; eauto.
      do 7 eexists; eauto.
  -
    assert (get O' osdomainportid = Some (osdomainport dpl)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
Qed.

Lemma qportpend_notnil_ctid_equiv_preserve2:
  forall td O1 O2 v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    qportpend_notnil_body (v :: v0 :: nil) O10 act (v1', Some O10') -> 
    qportpend_notnil_body (v :: v0 :: nil) O20 act (v2', Some O20') -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hqpn1 Hqpn2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets H1_: qportpend_notnil_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: qportpend_notnil_prio_preserved Hjo2 Hjo2'; eauto.  
  
  unfold ctid_equiv in *.
  unfold qportpend_notnil_body in *.
  simpljoin.
  do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  assert (Hgc1': get O1' curtid = get O1 curtid).  
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (Hgc2': get O2' curtid = get O2 curtid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  symmetry in Hgc1'. symmetry in Hgc2'. 
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid). 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Htd.

  lets Htpi1_: prio_preserved_tpi Htpi1' H1_.
  lets Htpi2_: prio_preserved_tpi Htpi2' H2_.
  match goal with
    H1: forall _ _, _ |- _ => lets H__: H1 Htpi1_ Htpi2_ Htd; eauto
  end.
  
Qed.

Lemma qportpend_notnil_bufs_equiv_preserve2: 
  forall td O1 O2 O10 O20 O10' O20' O1' O2' v v0 v1' v2' pr act t1 t2 Of1 Of2, 
    bufs_equiv td O1 O2 ->
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    qportpend_notnil_body (v :: v0 :: nil) O10 act (v1', Some O10') ->
    qportpend_notnil_body (v :: v0 :: nil) O20 act (v2', Some O20') ->
    prt_indom v O1 pr -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    bufs_equiv td O1' O2'.
Proof.
  introv Hbe Hpe Hqpn1 Hqpn2 Hpi Hjo1 Hjo2 Hjo1' Hjo2'.
  introv Hgct1 Hgct2 Htpi1 Htpi2.
  unfold bufs_equiv in *.
  destruct Hbe as (Hibeq & Hobeq).
  inverts Hqpn1.
  inverts Hqpn2.
  simpljoin.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end. 
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  unfold dom_cur_tsk in *.
  simpljoin.
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  apply11 (task_prio_id O10) (task_prio_id O20) tpi_frm_ext H1_ H2_.
  specializes H1_; eauto.
  specializes H2_; eauto.
  apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
  apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
  kvext O10 osdomainportid O1.
  kvext O20 osdomainportid O2. 

  split.
  - (* ibufs_equiv *)
    assert (Hgieq1: get O1 ibufsid = get O1' ibufsid).
    {
      lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
      repeat rewsimp. auto. 
    }
    assert (Hgieq2: get O2 ibufsid = get O2' ibufsid).
    {
      lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
      repeat rewsimp. auto. 
    }
    unfolds.
    rewrite <- Hgieq1. rewrite <- Hgieq2.
    unfolds in Hibeq.
    auto. 
  - (* obufs_equiv *) 
    unfold obufs_equiv in *.
    destruct Hobeq as (omp1 & omp2 & Hgom1 & Hgom2 & Homeq).
    kvext_h Hjo1' obufsid O1'.
    kvext_h Hjo2' obufsid O2'.
    kvext O10 obufsid O1.
    kvext O20 obufsid O2.
    l_rew21_inv1 (get O1 obufsid).
    l_rew21_inv1 (get O2 obufsid).
    do 2 eexists.
    split; eauto.
    split; eauto.
    casetac (dom_for_prio pr) td Ht Hf.
    + subst.
      rewrite upd_bufmp_get_eq.
      rewrite upd_bufmp_get_eq.
      unfolds in Hpi.
      destruct Hpi as (a & Hptreq & Hid).
      inverts Hptreq.
      inverts Hpe.
      simpljoin.
      l_rew12_inv2 (get O1 osdomainportid).
      l_rew12_inv2 (get O2 osdomainportid).
      match goal with H: forall _, _ |- _ => lets H__: H Hid end.
      destruct H__ as (Hprteq & _).
      match goal with
        H1: ?t1 = _, H2: ?t2 = _, Hprteq: ?t1 = ?t2 |- _ =>
          rewrite H1 in Hprteq; rewrite H2 in Hprteq; inverts Hprteq
      end.
      rewrite Homeq.
      auto.
    +
      rewrite upd_bufmp_get_neq; eauto.
      rewrite upd_bufmp_get_neq; eauto.
Qed.
    
Lemma qportpend_notnil_same_mqattr:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O absmqattrid = get O' absmqattrid. 
Proof.
  introv Hpnb Hjo Hjo'.
  inverts Hpnb.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto. 
  repeat rewsimp. 
  auto.
Qed.

Lemma qportpend_notnil_mq_ecbs_preserve: 
  forall v v0 v' O O' O0 O0' Of act, 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ecbs_preserved O O'. 
Proof.
  introv Hpn Hjo Hjo'.
  unfolds in Hpn.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgeq: get O absecblsid = get O' absecblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto. 
  }  
  introv Hge.
  symmetry in Hgeq.
  l_rew21_inv1 (get O' absecblsid).
  l_rew21_inv1 (get O absecblsid).
  auto.
  
Qed. 

Ltac sp_forall1 :=
  match goal with
    H: forall _, _ |- _ => specializes H; eauto
  end.

Ltac sp_forall1' hypname :=
  match goal with
    H: forall _, _ |- _ => rename H into hypname; specializes hypname; eauto
  end. 

Lemma ports_equiv_qportpend_notnil_preserve2: 
  forall O1 O2 v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 pr O1' O2' td, 
    ports_equiv td O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    qportpend_notnil_body (v :: v0 :: nil) O10 act (v1', Some O10') ->
    qportpend_notnil_body (v :: v0 :: nil) O20 act (v2', Some O20') ->
    prt_indom v O1 pr ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    ports_equiv td O1' O2'.
Proof.
  introv Hprte Hprte_ Hqpn1 Hqpn2.
  introv Hpi1 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets Hpp1: qportpend_notnil_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qportpend_notnil_prio_preserved Hjo2 Hjo2'; eauto. 
  unfold ports_equiv in Hprte.
  unfolds. 
  inverts Hqpn1.
  inverts Hqpn2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  kvext_h Hjo1' osdomainportid O1'.
  kvext_h Hjo2' osdomainportid O2'.
  assert (Hecbeq1: get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto.
  }
  assert (Hecbeq2: get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto.
  }
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  kvext O10 osdomainportid O1.
  kvext O20 osdomainportid O2.
  l_rew12_inv2 (get O1 osdomainportid).
  l_rew12_inv2 (get O2 osdomainportid).            
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hd.
  sp_forall1' Ha.
  destruct Ha as (Hprteq & Hiff & Htlseq).
  casetac x a Ht Hf.
  - 
    subst.
    rewrite set_a_get_a.
    rewrite set_a_get_a.
    match goal with
      H1: ?t1 = _, H2: ?t2 = _, Hprteq: ?t1 = ?t2 |- _ =>
        rewrite H1 in Hprteq; rewrite H2 in Hprteq; inverts Hprteq
    end.
    split. auto.
    split. auto.
    introv Hge1 Hge2.
    lets H__: Htlseq Hge1 Hge2; eauto.
    eapply tidls_equiv_pp_preserve2; eauto.
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto.
    split. auto. 
    split. auto. 
    introv Hge1 Hge2.
    lets H__: Htlseq Hge1 Hge2; eauto.
    eapply tidls_equiv_pp_preserve2; eauto.
Qed. 

Lemma qportpend_notnil_cpid_same:
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid.      
Proof.
  introv Hqnb Hjo Hjo'.
  inverts Hqnb.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  repeat rewsimp. auto.
Qed.   

Lemma qportpend_notnil_mqptr_impl:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hqnb Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  inverts Hqnb.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  match goal with H: _ \/ _ |- _ => destruct H as [Hnull | Hptr] end.
  -
    simpljoin.
    do 8 eexists. split; eauto. congruence. 
  -
    simpljoin.
    do 8 eexists. split; eauto. congruence. 
Qed. 

Lemma qportpend_notnil_mqptr_iff:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_notnil_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hqnb Hjo Hjo'.
  intros.
  split.
  - eapply qportpend_notnil_mqptr_impl; eauto.
  - 
    introv Hmp'.
    unfold mq_ptr in *.
    inverts Hqnb.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end. 
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      repeat rewsimp. auto.
    }
    match goal with H: _ \/ _ |- _ => destruct H as [Hnull | Hptr] end.
    +
      simpljoin.
      do 8 eexists. split; eauto. congruence. 
    +
      simpljoin.
      do 8 eexists. split; eauto. congruence. 
Qed.

Lemma buffer_equiv_qportpend_notnil_preserve2:
  forall v1 v2 va' vb' O10 O20 O10' O20' O1 O2 act td Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qportpend_notnil_body (v1 :: v2 :: nil) O10 act (va', Some O10') -> 
    qportpend_notnil_body (v1 :: v2 :: nil) O20 act (vb', Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2'. 
  lets Hpp1: qportpend_notnil_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qportpend_notnil_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_some.
  do 2 inv_lst.
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  assert (get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp; auto.
  }
  assert (get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp; auto.
  }
  eapply buffer_equiv_same_els_preserve2; eauto. 
Qed. 

Lemma qportpend_notnil_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr t1 t2 O1' O2' O10 O20 O10' O20' Of1 Of2 act v v0 v1' v2', 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    ports_equiv (dom_for_prio pr) O1 O2 ->
    prt_indom v O1 pr -> 
    qportpend_notnil_body (v::v0::nil) O10 act (v1', Some O10') ->
    qportpend_notnil_body (v::v0::nil) O20 act (v2', Some O20') ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hdet Hpe Hid1 Hqpn1 Hqpn2 Hdi1 Hdi2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2' Hgct1 Hgct2 Htpi1 Htpi2.
  lets Hpp1: qportpend_notnil_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qportpend_notnil_prio_preserved Hjo2 Hjo2'; eauto.   

  unfold data_equiv_tskd in *. 
  destruct Hdet as (Hce & Hbe_ & Hkde & Hcde).
  splits.
  - (* ctid_equiv *) 
    lets H__: qportpend_notnil_ctid_equiv_preserve2 Hjo1 Hjo2; eauto.
    
  - (* bufs_equiv *)
    lets H__: qportpend_notnil_bufs_equiv_preserve2 Hjo1 Hjo2; eauto. 

  - (* kernel_data_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte & Hkme & Hprte & Hbfe & Hcape).        
    unfolds.
    splits.

    + (* kernel_task_equiv *) 
      lets H__: knl_tsk_equiv_same_tls_preserve2 O1' O2' Hkte; eauto.
      specializes H__; eauto.
      lets H__: qportpend_notnil_tls_same Hjo1 Hjo1'; eauto.
      lets H__: qportpend_notnil_tls_same Hjo2 Hjo2'; eauto.

    + (* kernel_mq_equiv *)       
      lets H__: knl_mq_equiv_preserve2 O1' O2' Hkme; eauto.
      specializes H__; eauto.
      lets H__: qportpend_notnil_same_mqattr Hjo1 Hjo1'; eauto.
      lets H__: qportpend_notnil_same_mqattr Hjo2 Hjo2'; eauto.
      lets H__: qportpend_notnil_mq_ecbs_preserve Hjo1 Hjo1'; eauto.
      lets H__: qportpend_notnil_mq_ecbs_preserve Hjo2 Hjo2'; eauto.

    + (* ports_equiv *)
      lets H__: ports_equiv_qportpend_notnil_preserve2 Hprte Hpe; eauto. 

    + (* buffer_equiv *)
      eapply buffer_equiv_qportpend_notnil_preserve2; eauto. 
      
    + (* cap_equiv *) 
      eapply cap_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto.
      lets H__: qportpend_notnil_cpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_notnil_cpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qportpend_notnil_mqptr_iff Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_notnil_mqptr_iff Hjo2 Hjo2'; eauto. 

  - (* client_data_equiv *)
    eapply cde_prio_preserved_preserve2; eauto. 
    
Qed. 

Lemma prteq_port_not_empty_impl:
  forall O1 O2 v pr,
    prt_indom v O1 pr -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->      
    port_not_empty O1 v ->
    port_not_empty O2 v.
Proof.
  introv Hpi Hpe Hpne1.
  unfold port_not_empty in *.
  unfolds in Hpi.
  destruct Hpi as (a & Hprt & Hd).
  unfolds in Hpe.
  simpljoin.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  sp_forall1' Ha.
  destruct Ha as (Hprteq & Hiff & Htlseq).
  l_rew12_inv2 (get O1 osdomainportid).
  match goal with H1: ?t = _, H2: ?t = _ |- _ => rewrite H1 in H2; inverts H2 end.
  do 12 eexists.
  split; eauto.
Qed.  

Lemma qportpend_block_mqref_preserve:
  forall v v0 v' O O' O0 O0' Of act, 
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hqpb Hjo Hjo'.
  unfolds in Hqpb.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgeq: get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  l_rew21_inv1 (get O absmqattrid).
  l_rew21_inv1 (get O' absmqattrid).
  tauto.
Qed.

Lemma qportpend_block_qprt_preserve: 
  forall v v0 v' O O' O0 O0' Of act, 
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hqpn Hjo Hjo'.
  unfolds in Hqpn.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgeq: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; eauto. 
  }
  rewrite Hget in Hgeq.
  rewrite Hget' in Hgeq.
  inverts Hgeq.
  auto.
Qed.

Lemma qportpend_block_ctid_equiv_preserve2:
  forall td O1 O2 v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    qportpend_block (v :: v0 :: nil) O10 act (v1', Some O10') -> 
    qportpend_block (v :: v0 :: nil) O20 act (v2', Some O20') -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hqb1 Hqb2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets H1_: qportpend_block_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: qportpend_block_prio_preserved Hjo2 Hjo2'; eauto.  
  
  unfold ctid_equiv in *.
  unfold qportpend_block in *.
  simpljoin.
  do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  assert (Hgc1': get O1' curtid = get O1 curtid).  
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (Hgc2': get O2' curtid = get O2 curtid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  symmetry in Hgc1'. symmetry in Hgc2'. 
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid). 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Htd.

  lets Htpi1_: prio_preserved_tpi Htpi1' H1_.
  lets Htpi2_: prio_preserved_tpi Htpi2' H2_.
  match goal with
    H1: forall _ _, _ |- _ => lets H__: H1 Htpi1_ Htpi2_ Htd; eauto
  end.
  
Qed.

Lemma qportpend_block_bufs_same:
  forall v v0 O0 act v' O0' Of O O', 
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hpb Hjo Hjo'.
  inverts Hpb.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  split.
  -
    symmetry. 
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; eauto. 
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; eauto. 
Qed.       

Lemma qportpend_block_task_equiv_preserve2:
  forall td O1 O2 pr v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 O1' O2' t1 t2, 
    kernel_task_equiv td O1 O2 ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 ->
    qportpend_block (v :: v0 :: nil) O10 act (v1', Some O10') ->
    qportpend_block (v :: v0 :: nil) O20 act (v2', Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    kernel_task_equiv td O1' O2'.
Proof. 
  introv Hkte Hkte_ Hqb1 Hqb2 Hjo1 Hjo2 Hjo1' Hjo2'.
  introv Hgct1 Hgct2  Htpi1 Htpi2.
  lets Hpp1: qportpend_block_prio_preserved Hjo1 Hjo1'; eauto.
  lets Hpp2: qportpend_block_prio_preserved Hjo2 Hjo2'; eauto. 
  unfolds in Hkte.
  inverts Hqb1.
  inverts Hqb2.
  unfolds in Hkte_.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end. 
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  kvext O10 abstcblsid O1.
  kvext O20 abstcblsid O2.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.

  kvext_h Hjo1' abstcblsid O1'.
  kvext_h Hjo2' abstcblsid O2'.

  unfold kernel_task_equiv.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with
    H1: forall _,_, H2: forall _,_ |- _ =>
    specialize (H1 _ Hd); rename H1 into Htdeq; rename H2 into Hpreq
  end.
  specialize (Hpreq _ eq_refl).
  destruct Htdeq as (Htdiff & Htdteq).
  destruct Hpreq as (Hpriff & Hprteq).
  split.
  - 
    lets H__: prio_preserved_tpieq_impl Htdiff; eauto.
  -
    intros t1_ t2_.
    introv Hgt1_ Hgt2_.
    assert (Htpi1_: task_prio_id O1' pr0 t1_).
    {
      unfolds. do 5 eexists. split; eauto.
    }
    assert (Htpi2_: task_prio_id O2' pr0 t2_).
    {
      unfolds. do 5 eexists. split; eauto. 
    }
    assert (Htcs: t1 = t1_ /\ t2 = t2_ \/ t1 <> t1_ /\ t2 <> t2_).
    {
      eapply prio_tid_corr_ext; eauto. 
    }
    destruct Htcs as [(Hteq1 & Hteq2) | (Htneq1 & Htneq2)].
    +
      subst.
      rewrite set_a_get_a in Hgt1_.
      rewrite set_a_get_a in Hgt2_.
      inverts Hgt1_.
      inverts Hgt2_.
      specializes Htdteq; eauto.
      match goal with
        H1: ?x1 = Some _ /\ _ \/ _ /\ _, H2: ?x2 = Some _ /\ _ \/ _ /\ _ |- _ =>
          inverts H1; inverts H2; simpljoin; tryfalse
      end.
      splits; auto.
      splits; auto.
    +
      rewrite set_a_get_a' in Hgt1_; auto.
      rewrite set_a_get_a' in Hgt2_; auto.
      specializes Htdteq; eauto.  
Qed. 

Lemma qportpend_block_same_mqattr:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O absmqattrid = get O' absmqattrid. 
Proof.
  introv Hpb Hjo Hjo'.
  inverts Hpb.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto. 
  repeat rewsimp. 
  auto.
Qed.

Lemma qportpend_block_mq_ecbs_preserve: 
  forall v v0 O v' O' O0 O0' Of act, 
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ecbs_preserved O O'. 
Proof.
  introv Hqp Hjo Hjo'.
  unfolds in Hqp.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  kvext_h Hjo' absecblsid O'.
  introv Hge.
  l_rew21_inv1 (get O' absecblsid).
  kvext O0 absecblsid O.
  l_rew21_inv1 (get O absecblsid).
  casetac x eid Ht Hf.
  -
    subst. 
    match goal with
      H1: get els _ = _, H2: get els _ = _ |- _ => rewrite H1 in H2; inverts H2
    end.
  -
    rewrite set_a_get_a'; auto.
Qed. 

Lemma ports_equiv_qportpend_block_preserve2:
  forall td O1 O2 v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 O1' O2' t1 t2 pr, 
    ports_equiv td O1 O2 ->
    qportpend_block (v :: v0 :: nil) O10 act (v1', Some O10') ->
    qportpend_block (v :: v0 :: nil) O20 act (v2', Some O20') ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    join O10 Of1 O1 -> 
    join O20 Of2 O2 -> 
    join O10' Of1 O1' -> 
    join O20' Of2 O2' -> 
    ports_equiv td O1' O2'.
Proof.
  introv Hprte Hqb1 Hqb2 Hct1 Hct2 Htpi1 Htpi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  lets Hpp1: qportpend_block_prio_preserved Hjo1 Hjo1'; eauto.
  lets Hpp2: qportpend_block_prio_preserved Hjo2 Hjo2'; eauto.
  inverts Hqb1.
  inverts Hqb2.
  unfolds in Hprte.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  unfolds.
  kvext O10 osdomainportid O1.
  kvext O20 osdomainportid O2.
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.
  assert (Hpeq1: get O1 osdomainportid = get O1' osdomainportid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp; auto. 
  }
  assert (Hpeq2: get O2 osdomainportid = get O2' osdomainportid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp; auto. 
  }
  l_rew12_inv2 (get O1 osdomainportid).
  l_rew12_inv2 (get O2 osdomainportid).
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  l_rew12_inv2 (get O1 absecblsid).
  l_rew12_inv2 (get O2 absecblsid).
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew12_inv2 (get O1 curtid).
  l_rew12_inv2 (get O2 curtid). 
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hd.
  sp_forall1' Ha.
  destruct Ha as (Hpeq_ & Hiff & Htlseq).
  split; auto.
  casetac x a Ht Hf.
  -
    subst.
    do 4 rewrite set_a_get_a. 
    split.
    {
      split; intros; eexists; eauto.
    }
    introv He1 He2.
    inverts He1. inverts He2.
    specializes Htlseq; eauto.
    lets H__: tidls_equiv_cons_preserve2 Htlseq Hpp1 Hpp2; eauto. 
  -
    do 4 (rewrite set_a_get_a'; eauto).
    split; auto.
    introv Hg1 Hg2.
    specializes Htlseq; eauto.
    lets H__: tidls_equiv_pp_preserve2 Htlseq; eauto. 
Qed.             

Lemma qportpend_block_cpid_same:
  forall v v0 O act v' O' O0 O0' Of,
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid.      
Proof.
  introv Hqb Hjo Hjo'.
  inverts Hqb.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  repeat rewsimp. auto.
Qed.   

Lemma qportpend_block_mqptr_impl:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hqb Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  inverts Hqb.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  match goal with H: _ \/ _ |- _ => destruct H as [Hnull | Hptr] end.
  -
    simpljoin.
    do 8 eexists. split; eauto. congruence. 
  -
    simpljoin.
    do 8 eexists. split; eauto. congruence. 
Qed. 

Lemma qportpend_block_mqptr_iff:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_block (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hqb Hjo Hjo'.
  intros.
  split.
  - eapply qportpend_block_mqptr_impl; eauto.
  - 
    introv Hmp'.
    unfold mq_ptr in *.
    inverts Hqb.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end. 
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      repeat rewsimp. auto.
    }
    match goal with H: _ \/ _ |- _ => destruct H as [Hnull | Hptr] end.
    +
      simpljoin.
      do 8 eexists. split; eauto. congruence. 
    +
      simpljoin.
      do 8 eexists. split; eauto. congruence. 
Qed.

Lemma buffer_equiv_qportpend_block_preserve2:
  forall v1 v2 va' vb' O10 O20 O10' O20' O1 O2 act td Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qportpend_block (v1 :: v2 :: nil) O10 act (va', Some O10') -> 
    qportpend_block (v1 :: v2 :: nil) O20 act (vb', Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2'. 
  lets Hpp1: qportpend_block_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qportpend_block_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_some.
  do 2 inv_lst.
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.
  eapply buffer_equiv_nupd_preserve2; eauto. 
  {
    introv Hd.
    lets H__: buffer_ecb O1 Hd; eauto.
    specializes H__; eauto.
    simpljoin.
    casetac x eid Ht Hf.
    - subst. 
      match goal with H1: get _ eid = _, H2: get _ eid = _ |- _ => rewrite H1 in H2; inverts H2 end.
    - rewrite set_a_get_a'; eauto. 
  }
  {
    introv Hd.
    lets H__: buffer_ecb O2 Hd; eauto.
    specializes H__; eauto.
    simpljoin.
    casetac x eid Ht Hf.
    - subst. 
      match goal with H1: get _ eid = _, H2: get _ eid = _ |- _ => rewrite H1 in H2; inverts H2 end.
    - rewrite set_a_get_a'; eauto.           
  }                              
Qed. 

Lemma qportpend_block_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr t1 t2 O1' O2' O10 O20 O10' O20' Of1 Of2 act v v0 v1' v2', 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    prt_indom v O1 pr -> 
    qportpend_block (v::v0::nil) O10 act (v1', Some O10') ->
    qportpend_block (v::v0::nil) O20 act (v2', Some O20') ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hdet Hkte Hprte Hpi Hqb1 Hqb2.
  introv Hdi1 Hdi2 Hjo1 Hjo2 Hjo1' Hjo2'.
  introv Hct1 Hct2 Htpi1 Htpi2.
  unfolds in Hdet.
  destruct Hdet as (Hcte & Hbfe & Hkde & Hcde).
  lets Hpp1: qportpend_block_prio_preserved Hjo1 Hjo1'; eauto.
  lets Hpp2: qportpend_block_prio_preserved Hjo2 Hjo2'; eauto.
  unfolds.
  splits.
  -
    lets H__: qportpend_block_ctid_equiv_preserve2 Hjo1 Hjo2; eauto.
  -
    lets H1__: qportpend_block_bufs_same Hqb1 Hjo1 Hjo1'.
    lets H2__: qportpend_block_bufs_same Hqb2 Hjo2 Hjo2'.
    simpljoin. 
    lets H__: bufs_equiv_preserve2 O1 O2 O1' O2' Hbfe.
    specializes H__; eauto.
  -
    unfolds.
    unfolds in Hkde.
    destruct Hkde as (Hkte_ & Hkme_ & Hprte_ & Hbfe_ & Hcpe_).
    splits.
    + 
      lets H__: qportpend_block_task_equiv_preserve2 Hkte_ Hkte Hjo1 Hjo2; eauto.
    +
      eapply knl_mq_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto. 
      lets H__: qportpend_block_same_mqattr Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_same_mqattr Hjo2 Hjo2'; eauto. 
      lets H__: qportpend_block_mq_ecbs_preserve Hjo1 Hjo1'; eauto.
      lets H__: qportpend_block_mq_ecbs_preserve Hjo2 Hjo2'; eauto. 
    +            
      lets H__: ports_equiv_qportpend_block_preserve2 Hprte_; eauto.
    +
      eapply buffer_equiv_qportpend_block_preserve2; eauto.
    +
      eapply cap_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto.
      lets H__: qportpend_block_cpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_cpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qportpend_block_mqptr_iff Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_mqptr_iff Hjo2 Hjo2'; eauto. 
      
  -
    eapply cde_prio_preserved_preserve2; eauto.
    
Qed.

Lemma qbg_veq:
  forall v v0 O0 act v' O0', 
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') ->
    v' = Some (V$ OS_NO_ERR).
Proof.
  introv Hqbg.
  inverts Hqbg.
  simpljoin.
Qed.

Lemma qportpend_block_get_mqref_preserve:
  forall v v0 v' O O' O0 O0' Of act,
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') ->    
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hqbg Hjo Hjo'.
  unfolds in Hqbg.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgeq: get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  l_rew21_inv1 (get O absmqattrid).
  l_rew21_inv1 (get O' absmqattrid).
  tauto.
Qed.

Lemma qportpend_block_get_qprt_preserve: 
  forall v v0 v' O O' O0 O0' Of act,
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') ->   
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hqpb Hjo Hjo'.
  unfolds in Hqpb.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  kvext_h Hjo' osdomainportid O'.
  l_rew21_inv1 (get O' osdomainportid).
  introv Hex.
  simpljoin.
  kvext O0 osdomainportid O.
  l_rew21_inv1 (get O osdomainportid).  
  casetac x a Ht Hf.
  - subst.
    rewrite set_a_get_a.
    match goal with
      H1: get dpl a = _, H2: get dpl a = _ |- _ => rewrite H1 in H2; inverts H2
    end. 
    do 7 eexists. 
    eauto.
  -
    rewrite set_a_get_a'; eauto.
    do 7 eexists; eauto. 
Qed.

Lemma qportpend_block_get_ctid_equiv_preserve2:
  forall td O1 O2 v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    qportpend_block_get_body (v :: v0 :: nil) O10 act (v1', Some O10') -> 
    qportpend_block_get_body (v :: v0 :: nil) O20 act (v2', Some O20') -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hqb1 Hqb2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets H1_: qportpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: qportpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.  
  
  unfold ctid_equiv in *.
  unfold qportpend_block_get_body in *.
  simpljoin.
  do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  assert (Hgc1': get O1' curtid = get O1 curtid).  
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (Hgc2': get O2' curtid = get O2 curtid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  symmetry in Hgc1'. symmetry in Hgc2'. 
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid). 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Htd.

  lets Htpi1_: prio_preserved_tpi Htpi1' H1_.
  lets Htpi2_: prio_preserved_tpi Htpi2' H2_.
  match goal with
    H1: forall _ _, _ |- _ => lets H__: H1 Htpi1_ Htpi2_ Htd; eauto
  end.
  
Qed.

Lemma qportpend_block_get_bufs_equiv_preserve2:
  forall td O1 O2 v v0 v1 v2 act O10 O20 O10' O20' O1' O2' t1 t2 pr Of1 Of2, 
    bufs_equiv td O1 O2 ->
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    qportpend_block_get_body (v :: v0 :: nil) O10 act (v1, Some O10') ->
    qportpend_block_get_body (v :: v0 :: nil) O20 act (v2, Some O20') ->         
    prt_indom v O1 pr ->         
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    bufs_equiv td O1' O2'. 
Proof.
  introv Hbfe Hqpe Hqbg1 Hqbg2 Hpi Hgct1 Hgct2 Htpi1 Htpi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  inverts Hqbg1.
  inverts Hqbg2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  destruct Hbfe as (Hie & Hoe).
  unfolds.
  split.
  - (* ibufs_equiv *) 
    assert (Hgibe1: get O1 ibufsid = get O1' ibufsid).
    {
      lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
      repeat rewsimp; eauto. 
    }
    assert (Hgibe2: get O2 ibufsid = get O2' ibufsid).
    {
      lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
      repeat rewsimp; eauto.
    }
    unfolds.
    rewrite <- Hgibe1. rewrite <- Hgibe2.
    unfolds in Hie.
    tauto.
  - (* obufs_equiv *)
    unfolds.
    kvext_h Hjo1' obufsid O1'.
    kvext_h Hjo2' obufsid O2'.
    unfolds in Hqpe.
    simpljoin.
    kvext O10 osdomainportid O1.
    kvext O20 osdomainportid O2.
    l_rew21_inv1 (get O1 osdomainportid).
    l_rew21_inv1 (get O2 osdomainportid).
    unfolds in Hpi.
    destruct Hpi as (a & Hptr & Hd).
    inverts Hptr.
    sp_forall1' Ha.
    destruct Ha as (Hpeq & Hiff & Htidlseq). 
    do 2 eexists.
    split; eauto.
    split; eauto.
    kvext O10 obufsid O1.
    kvext O20 obufsid O2.
    unfolds in Hoe.
    destruct Hoe as (obmp1 & obmp2 & Hgob1 & Hgob2 & Hobmpeq).
    l_rew21_inv1 (get O1 obufsid).
    l_rew21_inv1 (get O2 obufsid).
    kvext O10 abstcblsid O1.
    kvext O20 abstcblsid O2.
    match goal with
      |- upd_bufmp _ (dom_for_prio ?xx) _ _ = upd_bufmp obmp2 (dom_for_prio ?yy) _ _
      => assert (Htpi__: task_prio_id O1 xx t1 /\ task_prio_id O2 yy t2)            
    end.
    { split; unfolds; do 5 eexists; split; eauto. }
    destruct Htpi__ as (Htpi1_ & Htpi2_).
    apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
    apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
    casetac (dom_for_prio pr) td Ht Hf.
    +
      subst.
      do 2 rewrite upd_bufmp_get_eq.
      match goal with
        H1: ?t1 = _, H2: ?t2 = _, Hpeq: ?t1 = ?t2 |- _ =>
          rewrite H1 in Hpeq; rewrite H2 in Hpeq; inverts Hpeq
      end.
      congruence.
    +
      do 2 (rewrite upd_bufmp_get_neq; eauto).
Qed.

Lemma qportpend_block_get_same_mqattr:  
  forall v v0 O act v' O' O0 O0' Of,
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O absmqattrid = get O' absmqattrid. 
Proof.
  introv Hpbg Hjo Hjo'.
  inverts Hpbg.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto. 
  repeat rewsimp. 
  auto.
Qed.

Lemma qportpend_block_get_mq_ecbs_preserve: 
  forall v v0 O v' O' O0 O0' Of act,
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ecbs_preserved O O'. 
Proof.
  introv Hqpg Hjo Hjo'.
  unfolds in Hqpg.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgeq: get O absecblsid = get O' absecblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto. 
  }
  rewrite Hget in Hgeq.
  rewrite Hget' in Hgeq.
  inverts Hgeq.
  introv Hge. auto.
Qed. 

Lemma qportpend_block_get_cpid_same:
  forall v v0 O act v' O' O0 O0' Of,
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid.      
Proof.
  introv Hqbg Hjo Hjo'.
  inverts Hqbg.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  repeat rewsimp. auto.
Qed.

Lemma qportpend_block_get_mqptr_impl:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hqbg Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  inverts Hqbg.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  match goal with H: _ \/ _ |- _ => destruct H as [Hnull | Hptr] end.
  -
    simpljoin.
    do 8 eexists. split; eauto. congruence. 
  -
    simpljoin.
    do 8 eexists. split; eauto. congruence. 
Qed. 

Lemma qportpend_block_get_mqptr_iff:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_block_get_body (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hqbg Hjo Hjo'.
  intros.
  split.
  - eapply qportpend_block_get_mqptr_impl; eauto.
  - 
    introv Hmp'.
    unfold mq_ptr in *.
    inverts Hqbg.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end. 
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      repeat rewsimp. auto.
    }
    match goal with H: _ \/ _ |- _ => destruct H as [Hnull | Hptr] end.
    +
      simpljoin.
      do 8 eexists. split; eauto. congruence. 
    +
      simpljoin.
      do 8 eexists. split; eauto. congruence. 
Qed.

Lemma ports_equiv_qportpend_block_get_preserve2: 
  forall O1 O2 v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 pr O1' O2' td, 
    ports_equiv td O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    qportpend_block_get_body (v :: v0 :: nil) O10 act (v1', Some O10') ->
    qportpend_block_get_body (v :: v0 :: nil) O20 act (v2', Some O20') -> 
    prt_indom v O1 pr ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    ports_equiv td O1' O2'.
Proof.
  introv Hprte Hprte_ Hqpn1 Hqpn2.
  introv Hpi1 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets Hpp1: qportpend_block_get_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qportpend_block_get_prio_preserved Hjo2 Hjo2'; eauto. 
  unfold ports_equiv in Hprte.
  unfolds. 
  inverts Hqpn1.
  inverts Hqpn2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  kvext_h Hjo1' osdomainportid O1'.
  kvext_h Hjo2' osdomainportid O2'.
  assert (Hecbeq1: get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto.
  }
  assert (Hecbeq2: get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto.
  }
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  kvext O10 osdomainportid O1.
  kvext O20 osdomainportid O2.
  l_rew12_inv2 (get O1 osdomainportid).
  l_rew12_inv2 (get O2 osdomainportid).            
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hd.
  sp_forall1' Ha.
  destruct Ha as (Hprteq & Hiff & Htlseq).
  casetac x a Ht Hf.
  - 
    subst.
    rewrite set_a_get_a.
    rewrite set_a_get_a.
    match goal with
      H1: ?t1 = _, H2: ?t2 = _, Hprteq: ?t1 = ?t2 |- _ =>
        rewrite H1 in Hprteq; rewrite H2 in Hprteq; inverts Hprteq
    end.
    split. auto.
    split. auto.
    introv Hge1 Hge2.
    lets H__: Htlseq Hge1 Hge2; eauto.
    eapply tidls_equiv_pp_preserve2; eauto.
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto.
    split. auto. 
    split. auto. 
    introv Hge1 Hge2.
    lets H__: Htlseq Hge1 Hge2; eauto.
    eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma qportpend_block_get_task_equiv_preserve2: 
  forall td O1 O2 pr v v0 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' t1 t2, 
    kernel_task_equiv td O1 O2 ->
    qportpend_block_get_body (v :: v0 :: nil) O10 act (v1, Some O10') -> 
    qportpend_block_get_body (v :: v0 :: nil) O20 act (v2, Some O20') -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    kernel_task_equiv td O1' O2'.
Proof.
  introv Hkte  Hqbg1 Hqbg2 Hjo1 Hjo2 Hjo1' Hjo2'.
  introv Hgct1 Hgct2 Htpi1 Htpi2.
  lets Hpp1: qportpend_block_get_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qportpend_block_get_prio_preserved Hjo2 Hjo2'; eauto. 
  unfold kernel_task_equiv in Hkte.
  inverts Hkte.
  inverts Hqbg1.
  inverts Hqbg2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  kvext_h Hjo1' abstcblsid O1'.
  kvext_h Hjo2' abstcblsid O2'.
  unfolds. 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  sp_forall1' Ha.
  destruct Ha as (Htiff & Hteq).        
  split.
  -
    eapply prio_preserved_tpieq_impl; eauto. 
  -
    intros t1_ t2_.
    introv Hget1 Hget2.
    kvext O10 abstcblsid O1.
    kvext O20 abstcblsid O2.
    l_rew21_inv1 (get O1 abstcblsid).
    l_rew21_inv1 (get O2 abstcblsid).
    assert (Htpi1_: task_prio_id O1' pr0 t1_).
    { unfolds. do 5 eexists. split; eauto. }
    assert (Htpi2_: task_prio_id O2' pr0 t2_).
    { unfolds. do 5 eexists. split; eauto. }
    lets H__: prio_tid_corr_ext Htpi1 Htpi2 Htpi1_ Htpi2_; eauto.
    specializes H__; eauto.
    destruct H__ as [(Hteq1 & Hteq2) | (Htneq1 & Htneq2)].
    +
      subst.
      rewrite set_a_get_a in Hget1. inverts Hget1.
      rewrite set_a_get_a in Hget2. inverts Hget2.
      specializes Hteq; eauto.
      simpljoin.
      splits; eauto.
    +
      rewrite set_a_get_a' in Hget1; eauto.
      rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma buffer_equiv_qportpend_block_get_preserve2:
  forall v1 v2 va' vb' O10 O20 O10' O20' O1 O2 act td Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qportpend_block_get_body (v1 :: v2 :: nil) O10 act (va', Some O10') -> 
    qportpend_block_get_body (v1 :: v2 :: nil) O20 act (vb', Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2'. 
  lets Hpp1: qportpend_block_get_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qportpend_block_get_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_some.
  do 2 inv_lst.
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  assert (get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp; auto.
  }
  assert (get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp; auto.
  }
  eapply buffer_equiv_same_els_preserve2; eauto. 
  
Qed. 

Lemma qportpend_block_get_dteq_preserve2: 
  forall td cst1 cst2 O1 O2 pr t1 t2 O1' O2' O10 O20 O10' O20' Of1 Of2 act v v0 v1' v2', 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    bufs_equiv (dom_for_prio pr) O1 O2 -> 
    prt_indom v O1 pr -> 
    qportpend_block_get_body (v::v0::nil) O10 act (v1', Some O10') ->
    qportpend_block_get_body (v::v0::nil) O20 act (v2', Some O20') ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hdet Hkte Hprte Hbfe Hpi Hqpg1 Hqpg2.
  introv Hdi1 Hdi2 Hjo1 Hjo2 Hjo1' Hjo2'.
  introv Hgct1 Hgct2 Htpi1 Htpi2.
  unfolds in Hdet. 
  destruct Hdet as (Hcte & Hbfe_ & Hkde & Hcde). 
  lets Hpp1: qportpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
  lets Hpp2: qportpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.
  unfolds.
  splits.
  - (* ctid_equiv *) 
    lets H__: qportpend_block_get_ctid_equiv_preserve2 Hjo1 Hjo2; eauto.
  - (* bufs_equiv *) 

    lets H__: qportpend_block_get_bufs_equiv_preserve2
                Hbfe_ Hjo1 Hjo2 Hjo1' Hjo2'; eauto. 

  - (* kernel_data_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte_ & Hkme_ & Hpe_ & Hbfe'_ & Hce_).
    unfolds.
    splits.
    + (* kernel_task_equiv *)
      lets H__: qportpend_block_get_task_equiv_preserve2 Hkte_ Hjo1 Hjo2 Hjo1' Hjo2'; eauto. 
      
    + (* kernel_mq_equiv *)
      eapply knl_mq_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto. 
      lets H__: qportpend_block_get_same_mqattr Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_get_same_mqattr Hjo2 Hjo2'; eauto. 
      lets H__: qportpend_block_get_mq_ecbs_preserve Hjo1 Hjo1'; eauto.
      lets H__: qportpend_block_get_mq_ecbs_preserve Hjo2 Hjo2'; eauto.

    + (* ports_equiv *) 
      lets H__: ports_equiv_qportpend_block_get_preserve2 Hpe_ Hprte; eauto.  

    + (* buffer_equiv *)
      eapply buffer_equiv_qportpend_block_get_preserve2; eauto.
      
    + (* cap_equiv *)
      eapply cap_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto.
      lets H__: qportpend_block_get_cpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_get_cpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qportpend_block_get_mqptr_iff Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_get_mqptr_iff Hjo2 Hjo2'; eauto. 
      
  - (* client_data_equiv *)
    eapply cde_prio_preserved_preserve2; eauto. 
    
Qed. 

Lemma kte_msg_come_impl:
  forall pr O1 O2 t1 t2,
    kernel_task_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    msg_come O1 ->
    msg_come O2.
Proof.
  introv  Hkte Hgc1 Hgc2 Htpi1 Htpi2 Hmc1.
  unfolds in Hkte.
  simpljoin.
  match goal with
    H: forall _, _ |- _ => specialize (H _ eq_refl)
  end.
  simpljoin. 
  unfold msg_come in *.
  simpljoin.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O1 abstcblsid).
  unfolds in Htpi1.
  unfolds in Htpi2.
  simpljoin.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  match goal with
    H1: get _ t1 = _, H2: get _ t1 = _ |- _ => rewrite H1 in H2; inverts H2
  end.
  sp_forall1' Ha.
  simpljoin.
  do 7 eexists.
  split; eauto. 
Qed.

Lemma qbt_veq:
  forall v v0 O0 act v' O0', 
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') ->
    v' = Some (V$ OS_TIMEOUT). 
Proof.
  introv Hqbt.
  inverts Hqbt.
  simpljoin.
Qed. 

Lemma qportpend_block_to_mqref_preserve:
  forall v v0 v' O O' O0 O0' Of act,
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hqbt Hjo Hjo'.
  unfolds in Hqbt.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgeq: get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  l_rew21_inv1 (get O absmqattrid).
  l_rew21_inv1 (get O' absmqattrid).
  tauto.
Qed.

Lemma qportpend_block_to_qprt_preserve: 
  forall v v0 v' O O' O0 O0' Of act,
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hqpt Hjo Hjo'.
  unfolds in Hqpt.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgeq: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto. 
  }
  rewrite Hget in Hgeq.
  rewrite Hget' in Hgeq.
  inverts Hgeq.
  introv Hex.
  simpljoin.
  do 7 eexists.
  eauto.
Qed. 

Lemma qportpend_block_to_ctid_equiv_preserve2:
  forall td O1 O2 v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    qportpend_block_timeout (v :: v0 :: nil) O10 act (v1', Some O10') -> 
    qportpend_block_timeout (v :: v0 :: nil) O20 act (v2', Some O20') -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hqb1 Hqb2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets H1_: qportpend_block_to_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: qportpend_block_to_prio_preserved Hjo2 Hjo2'; eauto.  
  
  unfold ctid_equiv in *.
  unfold qportpend_block_timeout in *.
  simpljoin.
  do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end).
  assert (Hgc1': get O1' curtid = get O1 curtid).  
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto. 
  }
  assert (Hgc2': get O2' curtid = get O2 curtid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto. 
  }
  symmetry in Hgc1'. symmetry in Hgc2'. 
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid). 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Htd.

  lets Htpi1_: prio_preserved_tpi Htpi1' H1_.
  lets Htpi2_: prio_preserved_tpi Htpi2' H2_.
  match goal with
    H1: forall _ _, _ |- _ => lets H__: H1 Htpi1_ Htpi2_ Htd; eauto
  end.
  
Qed.

Lemma qprtpend_bufs_same:
  forall v v0 O0 act v' O0' Of O O', 
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hpp Hjo Hjo'.
  inverts Hpp.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  split. 
  -
    symmetry. 
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.  
Qed.  

Lemma qportpend_block_to_cpid_same:
  forall v v0 O act v' O' O0 O0' Of,
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid.      
Proof.
  introv Hqbg Hjo Hjo'.
  inverts Hqbg.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  repeat rewsimp. auto.
Qed.

Lemma qportpend_block_to_mqptr_impl:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hqbt Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  inverts Hqbt.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  match goal with H: _ \/ _ |- _ => destruct H as [Hnull | Hptr] end.
  -
    simpljoin.
    do 8 eexists. split; eauto. congruence. 
  -
    simpljoin.
    do 8 eexists. split; eauto. congruence. 
Qed. 

Lemma qportpend_block_to_mqptr_iff:  
  forall v v0 O act v' O' O0 O0' Of, 
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hqbt Hjo Hjo'.
  intros.
  split.
  - eapply qportpend_block_to_mqptr_impl; eauto.
  - 
    introv Hmp'.
    unfold mq_ptr in *.
    inverts Hqbt.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end. 
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      repeat rewsimp. auto.
    }
    match goal with H: _ \/ _ |- _ => destruct H as [Hnull | Hptr] end.
    +
      simpljoin.
      do 8 eexists. split; eauto. congruence. 
    +
      simpljoin.
      do 8 eexists. split; eauto. congruence. 
Qed.

Lemma qportpend_block_to_same_mqattr:  
  forall v v0 O act v' O' O0 O0' Of,
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O absmqattrid = get O' absmqattrid. 
Proof.
  introv Hpbt Hjo Hjo'.
  inverts Hpbt.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto. 
  repeat rewsimp. 
  auto.
Qed.

Lemma qportpend_block_to_mq_ecbs_preserve: 
  forall v v0 O v' O' O0 O0' Of act,
    qportpend_block_timeout (v :: v0 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ecbs_preserved O O'. 
Proof.
  introv Hqpt Hjo Hjo'.
  unfolds in Hqpt.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  kvext_h Hjo' absecblsid O'.
  l_rew21_inv1 (get O' absecblsid).
  introv Hget'.
  kvext O0 absecblsid O.
  l_rew21_inv1 (get O absecblsid). 
  casetac x eid Ht Hf.
  - subst.
    match goal with
      H1: get els eid = _, H2: get els eid = _ |- _ => rewrite H1 in H2; inverts H2
    end.
  - rewrite set_a_get_a'; eauto. 
Qed.     

Lemma qportpend_block_to_task_equiv_preserve2: 
  forall td O1 O2 pr v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 O1' O2' t1 t2, 
    kernel_task_equiv td O1 O2 ->
    qportpend_block_timeout (v :: v0 :: nil) O10 act (v1', Some O10') ->
    qportpend_block_timeout (v :: v0 :: nil) O20 act (v2', Some O20') ->     
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    kernel_task_equiv td O1' O2'.
Proof.
  introv Hkte  Hqbt1 Hqbt2 Hjo1 Hjo2 Hjo1' Hjo2'.
  introv Hgct1 Hgct2 Htpi1 Htpi2.
  lets Hpp1: qportpend_block_to_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qportpend_block_to_prio_preserved Hjo2 Hjo2'; eauto. 
  unfold kernel_task_equiv in Hkte.
  inverts Hkte.
  inverts Hqbt1.
  inverts Hqbt2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  kvext_h Hjo1' abstcblsid O1'.
  kvext_h Hjo2' abstcblsid O2'.
  unfolds. 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  sp_forall1' Ha.
  destruct Ha as (Htiff & Hteq).        
  split.
  -
    eapply prio_preserved_tpieq_impl; eauto. 
  -
    intros t1_ t2_.
    introv Hget1 Hget2.
    kvext O10 abstcblsid O1.
    kvext O20 abstcblsid O2.
    l_rew21_inv1 (get O1 abstcblsid).
    l_rew21_inv1 (get O2 abstcblsid).
    assert (Htpi1_: task_prio_id O1' pr0 t1_).
    { unfolds. do 5 eexists. split; eauto. }
    assert (Htpi2_: task_prio_id O2' pr0 t2_).
    { unfolds. do 5 eexists. split; eauto. }
    lets H__: prio_tid_corr_ext Htpi1 Htpi2 Htpi1_ Htpi2_; eauto.
    specializes H__; eauto.
    destruct H__ as [(Hteq1 & Hteq2) | (Htneq1 & Htneq2)].
    +
      subst.
      rewrite set_a_get_a in Hget1. inverts Hget1.
      rewrite set_a_get_a in Hget2. inverts Hget2.
      specializes Hteq; eauto.
      simpljoin.
      splits; eauto.
    +
      rewrite set_a_get_a' in Hget1; eauto.
      rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma ports_equiv_qportpend_block_to_preserve2: 
  forall O1 O2 v v0 O10 O20 act v1' v2' O10' O20' Of1 Of2 pr O1' O2' td t1 t2, 
    ports_equiv td O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    qportpend_block_timeout (v :: v0 :: nil) O10 act (v1', Some O10') ->
    qportpend_block_timeout (v :: v0 :: nil) O20 act (v2', Some O20') -> 
    prt_indom v O1 pr ->
    get O1 curtid = Some (oscurt t1) -> 
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    ports_equiv td O1' O2'.
Proof.
  introv Hprte Hprte_ Hqpn1 Hqpn2.
  introv Hpi1 Hgc1 Hgc2 Htpi1 Htpi2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets Hpp1: qportpend_block_to_prio_preserved Hjo1 Hjo1'; eauto. 
  lets Hpp2: qportpend_block_to_prio_preserved Hjo2 Hjo2'; eauto. 
  unfold ports_equiv in Hprte.
  unfolds. 
  inverts Hqpn1.
  inverts Hqpn2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  assert (Hgeq1: get O1 osdomainportid = get O1' osdomainportid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto.  
  }
  assert (Hgeq2: get O2 osdomainportid = get O2' osdomainportid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto.  
  }
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2. 
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid). 
  kvext O10 osdomainportid O1.
  kvext O20 osdomainportid O2.
  l_rew12_inv2 (get O1 osdomainportid).
  l_rew12_inv2 (get O2 osdomainportid).
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew12_inv2 (get O1 curtid).
  l_rew12_inv2 (get O2 curtid). 
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hd.
  sp_forall1' Ha.
  destruct Ha as (Hprteq & Hiff & Htlseq).
  casetac x a Ht Hf.
  - 
    subst.
    rewrite set_a_get_a.
    rewrite set_a_get_a.
    split.
    congruence. 
    split.
    {
      split.
      intros. simpljoin. eexists; eauto.
      intros. simpljoin. eexists; eauto. 
    }
    do 2 (rewrite set_a_get_a). 
    introv Hge1 Hge2.
    inverts Hge1. inverts Hge2. 
    specializes Htlseq; eauto. 
    lets H__: tidls_equiv_rm_preserve2 Htlseq; eauto.
    specializes H__; eauto.
    match goal with
      H: get O1 absecblsid = _ |- _ =>  
        lets H__: distinct_wait_tids_prt H; eauto
    end.
    match goal with
      H: get O2 absecblsid = _ |- _ =>  
        lets H__: distinct_wait_tids_prt H; eauto
    end.    
  -
    do 4 (rewrite set_a_get_a'; eauto).
    split. congruence.
    split. auto. 
    introv Hg1 Hg2.
    specializes Htlseq; eauto.
    lets H__: tidls_equiv_pp_preserve2 Htlseq; eauto. 
    
Qed.

Lemma buffer_equiv_qportpend_block_timeout_preserve2:
  forall v1 v2 va' vb' O10 O20 O10' O20' O1 O2 act td Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qportpend_block_timeout (v1 :: v2 :: nil) O10 act (va', Some O10') -> 
    qportpend_block_timeout (v1 :: v2 :: nil) O20 act (vb', Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2'. 
  lets Hpp1: qportpend_block_to_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qportpend_block_to_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2 inv_some.
  do 2 inv_lst.
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.
  eapply buffer_equiv_nupd_preserve2; eauto. 
  {
    introv Hd.
    lets H__: buffer_ecb O1 Hd; eauto.
    specializes H__; eauto.
    simpljoin.
    casetac x eid Ht Hf.
    - subst. 
      match goal with H1: get _ eid = _, H2: get _ eid = _ |- _ => rewrite H1 in H2; inverts H2 end.
    - rewrite set_a_get_a'; eauto. 
  }
  {
    introv Hd.
    lets H__: buffer_ecb O2 Hd; eauto.
    specializes H__; eauto.
    simpljoin.
    casetac x eid Ht Hf.
    - subst. 
      match goal with H1: get _ eid = _, H2: get _ eid = _ |- _ => rewrite H1 in H2; inverts H2 end.
    - rewrite set_a_get_a'; eauto.           
  }                              
Qed.

Lemma qportpend_block_to_dteq_preserve2: 
  forall td cst1 cst2 O1 O2 pr t1 t2 O1' O2' O10 O20 O10' O20' Of1 Of2 act v v0 v1' v2', 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    prt_indom v O1 pr -> 
    qportpend_block_timeout (v::v0::nil) O10 act (v1', Some O10') ->
    qportpend_block_timeout (v::v0::nil) O20 act (v2', Some O20') ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hdet Hkte Hprte Hpi Hqbt1 Hqbt2.
  introv Hdi1 Hdi2 Hjo1 Hjo2 Hjo1' Hjo2'.
  introv Hgc1 Hgc2 Htpi1 Htpi2.
  unfolds in Hdet. 
  destruct Hdet as (Hcte & Hbfe_ & Hkde & Hcde). 
  lets Hpp1: qportpend_block_to_prio_preserved Hjo1 Hjo1'; eauto.
  lets Hpp2: qportpend_block_to_prio_preserved Hjo2 Hjo2'; eauto.
  unfolds.
  splits.
  - (* ctid_equiv *) 
    lets H__: qportpend_block_to_ctid_equiv_preserve2 Hjo1 Hjo2; eauto.
  - (* bufs_equiv *)        
    apply11 qportpend_block_timeout
      qportpend_block_timeout qprtpend_bufs_same H1_ H2_.
    specializes H1_; eauto.
    specializes H2_; eauto.
    simpljoin. 
    eapply bufs_equiv_preserve2; eauto.
  - (* kernel_data_equiv *) 
    unfolds in Hkde.
    destruct Hkde as (Hkte_ & Hkme_ & Hpe_ & Hbfe'_ & Hce_).
    unfolds.
    splits.
    + (* kernel_task_equiv *)
      lets H__: qportpend_block_to_task_equiv_preserve2 Hkte_ Hjo1 Hjo2 Hjo1' Hjo2'; eauto. 

    + (* kernel_mq_equiv *)  
      eapply knl_mq_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto. 
      lets H__: qportpend_block_to_same_mqattr Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_to_same_mqattr Hjo2 Hjo2'; eauto. 
      lets H__: qportpend_block_to_mq_ecbs_preserve Hjo1 Hjo1'; eauto.
      lets H__: qportpend_block_to_mq_ecbs_preserve Hjo2 Hjo2'; eauto.

    + (* ports_equiv *)
      lets H__: ports_equiv_qportpend_block_to_preserve2 Hpe_ Hjo1 Hjo2 Hjo1' Hjo2'; eauto.

    + (* buffer_equiv *)   
      eapply buffer_equiv_qportpend_block_timeout_preserve2; eauto. 
      
    + (* cap_equiv *)
      eapply cap_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto.
      lets H__: qportpend_block_to_cpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_to_cpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qportpend_block_to_mqptr_iff Hjo1 Hjo1'; eauto. 
      lets H__: qportpend_block_to_mqptr_iff Hjo2 Hjo2'; eauto. 

  - (* client_data_equiv *)
    eapply cde_prio_preserved_preserve2; eauto.
    
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
  | H1: ?P, H2: ~(?P) |- _ => try solve [false]
  | H: ?x1 <> ?x2 |- _ => unify x1 x2; try solve [false]
  | _ => idtac
  end. 

Ltac solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 k :=
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


Lemma hidapistep_hidapistep_qprtpend_lemma:
  forall (pc0 : progunit) (pr : priority) (t1 t2 : addrval) (T1 T2 : tasks)
         (cst1' cst2' : clientst) (O1 O2 O1' O2' : osabst) (act : action) (cd1 cd2 : spec_code)
         (cd' cd'0 : spec_code) (i : taskdom) (ks0 ks1 ks1_ : stmtcont) (ke0 : exprcont) 
         (Hncfid : no_common_fid pc0 (api_spec, int_spec, get_hprio_d))
         (Hpu : pu_noabs pc0) 
         (Hrch1 : reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1)
         (Hrch2 : reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2)
         (Hfloweq : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
            obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2)
         (Hsceq : obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1 O2)
         (Htmeq : obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1 O2)
         (Htdeq : obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1 O2)
         (Hact : act = TauAct \/ act = SendAct \/ act = RecvAct)
         (Hnint1 : ~ in_intr T1 O1)
         (Hcurt1 : get O1 curtid = Some (oscurt t1))
         (Htpi1 : task_prio_id O1 pr t1)
         (Hnabt1 : nabt (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_))))
         (Hnint2 : ~ in_intr T2 O2)
         (Hcurt2 : get O2 curtid = Some (oscurt t2))
         (Hdomeq : dom_for_prio pr = dom_for_prio pr)
         (Htpi2 : task_prio_id O2 pr t2)
         (Hnabt2 : nabt (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))))
         (HC1 : get T1 t1 = Some (curs (hapi_code cd1), (ke0, ks1_)))
         (Hceq : forall (pr0 : priority) (t1 t2 : tid),
             dom_for_prio pr0 = dom_for_prio pr ->
             task_prio_id O1 pr0 t1 ->
             task_prio_id O2 pr0 t2 ->
             exists c1 c2 ke ks1 ks2,
               get T1 t1 = Some (c1, (ke, ks1)) /\
                 get T2 t2 = Some (c2, (ke, ks2)) /\
                 cmd_equiv pr0 c1 c2 O1 O2 /\ cont_equiv pr0 ks1 ks2 O1 O2)
         (Hd'eq : obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2)
         (Hstepdm : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i))
         (Hfa : forall pr1 pr2 : priority,
             task_prio_id O1 pr1 t1 ->
             task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2)
         (Hcurt1 : get O1 curtid = Some (oscurt t1))
         (Hcurt2 : get O2 curtid = Some (oscurt t2))
         (Hbufe : bufs_equiv (dom_for_prio pr) O1 O2)
         (Hkde : kernel_data_equiv (dom_for_prio pr) O1 O2)
         (Hcde : client_data_equiv (dom_for_prio pr) cst1' cst2' O1 O2)
         (Hkte : kernel_task_equiv (dom_for_prio pr) O1 O2)
         (Hkme : kernel_mq_equiv (dom_for_prio pr) O1 O2)
         (Hprte : ports_equiv (dom_for_prio pr) O1 O2)
         (Hctide_ : ctid_equiv (dom_for_prio pr) O1 O2)
         (H : spec_step get_hprio_d cd1 O1 cd' O1' act)
         (Hcpe : cap_equiv (dom_for_prio pr) O1 O2)
         (H0 : spec_step get_hprio_d cd2 O2 cd'0 O2' act)
         (Hhsat1 : head_asrt_sat pr cd1 O1)
         (Hhsat2 : head_asrt_sat pr cd2 O2)
         (Hvleq : vl_equiv cd1 cd2)
         (Hnex : ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2))
         (Hpend : qprtpend_equiv cd1 cd2)
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
  
  unfolds in Hpend.  
  destruct Hpend as (vl & vl1 & vl2 & k & Hlenvl & Hlenvl1 & Hlenvl2 & Hnth1 & Hnth2).
  do 3 try destruct vl; tryfalse.
  do 3 try destruct vl1; tryfalse.
  do 3 try destruct vl2; tryfalse.
  simpl in Hnth1. 
  destruct v1; simpl in Hnth1;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).  
  simpl in Hnth2.
  destruct v3; simpl in Hnth2; 
    try (eapply abt_succs_contra in Hnth2; inverts Hstep2; tryfalse; fail). 

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
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto.      
  }
  {
    apply cap_equiv_sym in Hcpe.
    match goal with
      H: has_no_cap_prtpend _ |- _ => lets H__: cpe_no_prtpend_cap_impl
    end. 
    specializes H__; eauto. 
    false. 
  }
  {
    match goal with
      H: has_no_cap_prtpend _ |- _ => lets H__: cpe_no_prtpend_cap_impl
    end. 
    specializes H__; eauto. 
    false.     
  }  
  {
    Set Nested Proofs Allowed.
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.    
    unfolds.
    right.
    do 2 eexists.
    do 2 (split; eauto).
    split. simpl; auto.
    match goal with
      H: _ = Vnull \/ port_indomainport v O0 |- _ =>
        destruct H; [left; auto | right; eapply port_indomainport_frm_preserve; eauto]
    end.
    split. simpl.
    unfolds. 
    match goal with
      H: _ = Vnull \/ port_indomainport v O |- _ =>
        destruct H; [left;auto | right; eapply port_indomainport_frm_preserve; eauto]
    end.
    split. 
    eapply vl_equiv_nil; eauto.
    unfolds.
    right.
    split. introv Hf; simpljoin; tryfalse.
    right; right; right; right; left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 1%nat.
  }

  destruct k.
  (* k=1 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  simpl in Hhsat1.
  simpl in Hhsat2.    
  symexe. 
  
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto.     
  }
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto.       
  }
  {
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    apply ports_equiv_sym in Hprte. 
    lets H__: prts_equiv_orcond_impl Hprte. 
    specializes H__; eauto.
    false.    
  }
  {
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    apply ports_equiv_sym in Hprte.
    lets H__: prts_equiv_orcond_impl Hprte. 
    specializes H__; eauto.
    false.        
  }
  {
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    apply ports_equiv_sym in Hprte.
    lets H__: prts_equiv_orcond_impl Hprte. 
    specializes H__; eauto.
    false.        
  }
  {
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    lets H__: prts_equiv_orcond_impl Hprte. 
    specializes H__; eauto.
    false.            
  }
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto.      
  }
  {    
    lets Hnwd: ncond_dest_wd O2.
    specializes Hnwd; eauto. 
    apply ports_equiv_sym in Hprte.
    lets H__: prte_port_dir_impl Hnwd Hprte; eauto. 
    specializes H__; eauto.
    false.
  }
  {
    lets Hnwd: ncond_dest_wd O2.
    specializes Hnwd; eauto. 
    apply ports_equiv_sym in Hprte.
    lets H__: prte_port_dir_impl Hnwd Hprte; eauto. 
    specializes H__; eauto.
    false.    
  }
  {
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    lets H__: prts_equiv_orcond_impl Hprte. 
    specializes H__; eauto.
    false.            
  }
  {
    lets Hnwd: ncond_dest_wd O1.
    specializes Hnwd; eauto. 
    lets H__: prte_port_dir_impl Hnwd Hprte; eauto. 
    specializes H__; eauto.
    false.        
  }
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto.              
  }
  { 
    lets Hnwd: ncond_dest_wd O2.
    specializes Hnwd; eauto. 
    apply ports_equiv_sym in Hprte.
    lets H__: prte_port_type_impl Hnwd Hprte; eauto. 
    specializes H__; eauto.
    false.    
  }
  {
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    lets H__: prts_equiv_orcond_impl Hprte. 
    specializes H__; eauto.
    false.                
  }
  {
    lets Hnwd: ncond_dest_wd O1.
    specializes Hnwd; eauto. 
    lets H__: prte_port_dir_impl Hnwd Hprte; eauto. 
    specializes H__; eauto.
    false.            
  }
  {
    lets Hnwd: ncond_dest_wd O1. 
    specializes Hnwd; eauto. 
    lets H__: prte_port_type_impl Hnwd Hprte; eauto. 
    specializes H__; eauto.
    false.        
  }
  {
    simpl in Hhsat1. simpl in Hhsat2.
    apply11 spec_skip_step spec_skip_step sskp_Oeq H1_ H2_.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists.
    split; eauto. split; eauto.
    split. simpl.
    eapply nwd_prt_indom; eauto.
    split. simpl.
    eapply nwd_prt_indom; eauto.
    split.
    eapply vl_equiv_nil; eauto.
    unfolds. right. split. introv Hf; simpljoin; tryfalse.
    right. right. right. right. left. 
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 2%nat.     
  }

  destruct k. 
  (* k=2 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  simpl in Hhsat1.
  simpl in Hhsat2.    
  symexe. 
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    apply cmd_equiv_end.    
  }
  {
    apply obsr_equiv_chnd_sym in Htmeq. 
    apply ports_equiv_sym in Hprte. 
    lets H__: cheq_no_chan_impl Htmeq Hprte; eauto. 
    specializes H__; eauto. 
    false.     
  }
  {
    apply obsr_equiv_chnd_sym in Htmeq. 
    apply ports_equiv_sym in Hprte.
    lets H__: cheq_no_chan_impl Htmeq Hprte; eauto. 
    specializes H__; eauto. 
    false.         
  }
  {
    lets H__: cheq_no_chan_impl Htmeq Hprte; eauto. 
    specializes H__; eauto. 
    false.             
  }
  {
    apply11 spec_skip_step spec_skip_step sskp_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists.
    split; eauto.
    split; eauto.
    split. simpl. auto.
    split. simpl. auto.
    split. eapply vl_equiv_nil; eauto. 
    unfolds. right. split. introv Hf; simpljoin; tryfalse.
    right; right; right; right; left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 4%nat.      
  }
  {
    lets H__: cheq_intercore_impl Hprte; eauto. 
    specializes H__; eauto. 
    false.    
  }
  {
    lets H__: cheq_no_chan_impl Htmeq Hprte; eauto. 
    specializes H__; eauto. 
    false.                 
  }
  {
    apply ports_equiv_sym in Hprte.
    apply obsr_equiv_chnd_sym in Htmeq. 
    lets H__: cheq_intercore_impl Hprte; eauto. 
    specializes H__; eauto. 
    false.    
  }
  {
    apply2 chsem_res chsem_res chsem_res_eq. 
    apply obsr_equiv_chnd_sym in Htmeq.
    auto.
    split; eauto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists.
    split; eauto.
    split; eauto.
    split. simpl. auto.
    split. simpl. auto.
    split. eapply veq_vlequiv; eauto. 
    simpl. eauto. simpl. eauto.
    unfolds.
    right. split. introv Hf; simpljoin; tryfalse.
    right. right. right. right. left.
    (* qprtpend_equiv *) 
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 3%nat.     
  }

  destruct k. 
  (* k=3 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe.
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto. split. simpl. auto.
    split.
    eapply vl_equiv_nil; eauto.
    unfolds.
    right. split. introv Hf; simpljoin; tryfalse.
    right. right. right. right. left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 4%nat.         
  }
  {
    eapply vlequiv_veq_ext in Hvleq; eauto. 
    2: { simpl. eauto. }
    2: { simpl. eauto. }
    tryfalse. 
  }
  {
    eapply vlequiv_veq_ext in Hvleq; eauto. 
    2: { simpl. eauto. }
    2: { simpl. eauto. }
    tryfalse.     
  }  
  {
    apply11 spec_skip_step spec_skip_step sskp_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto. split. simpl. auto.
    split. eapply vl_equiv_nil; eauto. 
    unfolds.
    right.
    split. introv Hf. simpljoin; tryfalse.
    right. right. right. right. left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 4%nat.      
  }

  destruct k. 
  (* k=4 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe.
  {
    lets Hpp1: qportpend_notnil_prio_preserved O0 O'0 Of0; eauto.
    specializes Hpp1; eauto.
    lets Hpp2: qportpend_notnil_prio_preserved O O' Of; eauto.
    specializes Hpp2; eauto.
    split.
    (* code_equiv *)
    apply11 qportpend_notnil_body qportpend_notnil_body qportpend_notnil_cpid_same Hcpeq2 Hcpeq1.
    specializes Hcpeq1; eauto.
    specializes Hcpeq2; eauto. 
    eapply code_equiv_upd2_preserve_st'; eauto.
    {
      (* cmd_equiv *)
      unfolds.
      right.
      do 2 eexists.
      split; eauto.
      split; eauto.
      split.
      simpl. eapply prt_indom_preserve; eauto.
      split.
      simpl. eapply prt_indom_preserve; eauto.
      split. eapply vl_equiv_nil; eauto.
      unfolds.
      right. split. introv Hf. simpljoin; tryfalse.
      right; right; right; right; left.
      (* qprtpend_equiv *)
      solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 5%nat. 
    }

    eapply cont_equiv_qref_preserve; eauto. 
    eapply qportpend_notnil_mqref_preserve; eauto. 
    eapply qportpend_notnil_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qportpend_notnil_qprt_preserve; eauto. 
    eapply qportpend_notnil_qprt_preserve with (O0:=O) (O0':=O'); eauto.
    eapply eqdom_frm_domimpl; eauto. 
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
    
    lets H__: code_equiv_hsat_neq_st'; eauto. 
    eapply H__; eauto.
    eapply qportpend_notnil_mqref_preserve; eauto.
    eapply qportpend_notnil_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qportpend_notnil_qprt_preserve; eauto.
    eapply qportpend_notnil_qprt_preserve with (O0:=O) (O0':=O'); eauto. 
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
    
    (* data_equiv *)    
    eapply qportpend_notnil_dteq_preserve2
      with (O10:=O0) (O10':=O'0) (O20:=O) (O20':=O'); eauto.
    eapply eqdom_frm_domimpl with (O10:=O0) (O20:=O'0); eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.        
  }
  {
    apply ports_equiv_sym in Hprte.
    lets H__: prteq_port_not_empty_impl Hhsat2.
    specializes H__; eauto.
    false.
  }
  {
    apply ports_equiv_sym in Hprte.
    lets H__: prteq_port_not_empty_impl Hhsat2.
    specializes H__; eauto.
    false.    
  }
  {
    lets H__: prteq_port_not_empty_impl Hhsat1.
    specializes H__; eauto.
    false.        
  }
  {
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto. split. simpl. auto.
    split. eapply vl_equiv_nil; eauto. 
    unfolds.
    right.
    split. introv Hf. simpljoin; tryfalse.
    right. right. right. right. left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 7%nat.      
  }
  {
    apply ports_equiv_sym in Hprte.
    apply obsr_equiv_chnd_sym in Htmeq. 
    lets H__: cheq_intercore_impl Hprte; eauto. 
    specializes H__; eauto. 
    false.        
  }
  {
    lets H__: prteq_port_not_empty_impl Hhsat1.
    specializes H__; eauto.
    false.            
  }
  {
    lets H__: cheq_intercore_impl Hprte; eauto. 
    specializes H__; eauto. 
    false.      
  }
  {
    apply11 spec_skip_step spec_skip_step sskp_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto. split. simpl. auto.
    split. eapply vl_equiv_nil; eauto. 
    unfolds.
    right.
    split. introv Hf. simpljoin; tryfalse.
    right. right. right. right. left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 7%nat.  
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
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto. split. simpl. auto.
    split. eapply vl_equiv_nil; eauto. 
    unfolds.
    right.
    split. introv Hf. simpljoin; tryfalse.
    right. right. right. right. left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 6%nat.   
  }
  {
    apply ports_equiv_sym in Hprte.
    apply obsr_equiv_chnd_sym in Htmeq. 
    lets H__: cheq_intercore_impl Hprte; eauto. 
    specializes H__; eauto. 
    false.            
  }
  {
    lets H__: cheq_intercore_impl Hprte; eauto. 
    specializes H__; eauto. 
    false.          
  }
  {
    apply11 spec_skip_step spec_skip_step sskp_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto. split. simpl. auto.
    split. eapply vl_equiv_nil; eauto. 
    unfolds.
    right.
    split. introv Hf. simpljoin; tryfalse.
    right. right. right. right. left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 6%nat.      
  }
  
  destruct k.
  (* k=6 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe.
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst.
    apply cmd_equiv_end.
  }

  destruct k.
  (* k=7 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe.
  apply11 qportpend_block qportpend_block qportpend_block_cpid_same Hcpeq2 Hcpeq1.
  specializes Hcpeq1; eauto.
  specializes Hcpeq2; eauto. 
  {    
    apply11 qportpend_block qportpend_block qportpend_block_prio_preserved H2_ H1_.
    specializes H1_; eauto.
    specializes H2_; eauto.
    split.
    (* code_equiv *) 
    eapply code_equiv_upd2_preserve_st'; eauto.
    {
      (* cmd_equiv *)
      unfolds.
      right.
      do 2 eexists.
      split; eauto.
      split; eauto.
      split.
      simpl. eapply prt_indom_preserve; eauto.
      split.
      simpl. eapply prt_indom_preserve; eauto.
      split. eapply vl_equiv_nil; eauto.
      unfolds.
      right. split. introv Hf. simpljoin; tryfalse.
      right; right; right; right; left.
      (* qprtpend_equiv *)
      solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 8%nat. 
    }
    
    eapply cont_equiv_qref_preserve; eauto. 
    eapply qportpend_block_mqref_preserve; eauto. 
    eapply qportpend_block_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qportpend_block_qprt_preserve; eauto. 
    eapply qportpend_block_qprt_preserve with (O0:=O) (O0':=O'); eauto. 
    eapply eqdom_frm_domimpl; eauto. 
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    lets H__: code_equiv_hsat_neq_st'; eauto. 
    eapply H__; eauto.
    eapply qportpend_block_mqref_preserve; eauto.
    eapply qportpend_block_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qportpend_block_qprt_preserve; eauto.
    eapply qportpend_block_qprt_preserve with (O0:=O) (O0':=O'); eauto. 
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
    
    (* data_equiv *) 
    eapply qportpend_block_dteq_preserve2
      with (O10:=O0) (O10':=O'0) (O20:=O) (O20':=O'); eauto.
    eapply eqdom_frm_domimpl with (O10:=O0) (O20:=O'0); eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.  
  }

  destruct k.
  (* k=8 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe.
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl. auto. split. simpl. auto.
    split. eapply vl_equiv_nil; eauto. 
    unfolds.
    right.
    split. introv Hf. simpljoin; tryfalse.
    right. right. right. right. left.
    (* qprtpend_equiv *)
    solve_prtpend_equiv Hlenvl Hlenvl1 Hlenvl2 9%nat. 
  }

  destruct k.
  (* k=9 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe.

  { (* qportpend_block_get_body *)
    apply11
      qportpend_block_get_body qportpend_block_get_body
        qportpend_block_get_prio_preserved Hpp2 Hpp1. 
    specializes Hpp2; eauto. 
    specializes Hpp1; eauto.

    split.
    (* code_equiv *) 
    apply11 qportpend_block_get_body qportpend_block_get_body
      qportpend_block_get_cpid_same Hcpeq2 Hcpeq1.
    specializes Hcpeq1; eauto.
    specializes Hcpeq2; eauto.
    
    eapply code_equiv_upd2_preserve_st'; eauto.
    {
      (* cmd_equiv *)
      apply11
        qportpend_block_get_body qportpend_block_get_body
          qbg_veq H1_ H2_.
      subst. 
      apply cmd_equiv_end.      
    }   
  
    eapply cont_equiv_qref_preserve; eauto. 
    eapply qportpend_block_get_mqref_preserve; eauto. 
    eapply qportpend_block_get_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qportpend_block_get_qprt_preserve; eauto. 
    eapply qportpend_block_get_qprt_preserve with (O0:=O) (O0':=O'); eauto.
    eapply eqdom_frm_domimpl; eauto. 
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
    
    lets H__: code_equiv_hsat_neq_st'; eauto. 
    eapply H__; eauto.
    eapply qportpend_block_get_mqref_preserve; eauto.
    eapply qportpend_block_get_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qportpend_block_get_qprt_preserve; eauto.
    eapply qportpend_block_get_qprt_preserve with (O0:=O) (O0':=O'); eauto. 
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
 
    (* data_equiv_tskd *)
    eapply qportpend_block_get_dteq_preserve2
      with (O10:=O0) (O10':=O'0) (O20:=O) (O20':=O'); eauto.
    eapply eqdom_frm_domimpl with (O10:=O0) (O20:=O'0); eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.      
  }
  {
    apply kernel_task_equiv_sym in Hkte.
    lets H__: kte_msg_come_impl Hkte.
    specializes H__; eauto.
    false. 
  }
  {
    lets H__: kte_msg_come_impl Hkte.
    specializes H__; eauto.
    false. 
  }
  {
    apply11
      qportpend_block_timeout qportpend_block_timeout 
        qportpend_block_to_prio_preserved Hpp2 Hpp1. 
    specializes Hpp2; eauto.
    specializes Hpp1; eauto.
    
    split.
    (* code_equiv_tskd *) 
    apply11 qportpend_block_timeout qportpend_block_timeout 
      qportpend_block_to_cpid_same Hcpeq2 Hcpeq1.
    specializes Hcpeq1; eauto.
    specializes Hcpeq2; eauto.

    eapply code_equiv_upd2_preserve_st'; eauto.
    {
      (* cmd_equiv *)
      apply11
        qportpend_block_timeout qportpend_block_timeout
          qbt_veq H1_ H2_. 
      subst. 
      apply cmd_equiv_end.      
    }   
    (* cont_equiv *)     
    eapply cont_equiv_qref_preserve; eauto.
    eapply qportpend_block_to_mqref_preserve; eauto. 
    eapply qportpend_block_to_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qportpend_block_to_qprt_preserve; eauto.
    eapply qportpend_block_to_qprt_preserve with (O0:=O) (O0':=O'); eauto.
    eapply eqdom_frm_domimpl; eauto. 
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    lets H__: code_equiv_hsat_neq_st'; eauto. 
    eapply H__; eauto.
    eapply qportpend_block_to_mqref_preserve; eauto.
    eapply qportpend_block_to_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply qportpend_block_to_qprt_preserve; eauto.
    eapply qportpend_block_to_qprt_preserve with (O0:=O) (O0':=O'); eauto. 
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
  
    (* data_equiv_tskd *)
    eapply qportpend_block_to_dteq_preserve2
      with (O10:=O0) (O10':=O'0) (O20:=O) (O20':=O'); eauto.
    eapply eqdom_frm_domimpl with (O10:=O0) (O20:=O'0); eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.      
  }

  destruct k.
  (* k=10 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  
Qed. 
