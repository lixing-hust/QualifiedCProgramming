
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

Lemma prte_port_type_impl:
  forall O1 O2 vprt pr t1, 
    ~wrong_dom O1 vprt ->
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    get O1 curtid = Some (oscurt t1) ->
    task_prio_id O1 pr t1 ->
    (* has_port vprt O1 pr -> *)
    (* has_port vprt O2 pr ->  *)
    (exists a dpl pcn pd pid pdir pst pin pout pt,
        get O1 osdomainportid = Some (osdomainport dpl) /\
          vprt = Vptr a /\
          get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
          (pdir <> SourceP \/ (exists ml, pt = SamplePort ml))) -> 
    (exists a dpl pcn pd pid pdir pst pin pout pt,
        get O2 osdomainportid = Some (osdomainport dpl) /\
          vprt = Vptr a /\
          get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
          (pdir <> SourceP \/ (exists ml, pt = SamplePort ml))). 
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
  match goal with
    H1: ?t1 = Some _, H2: ?t1' = _ |- _ => unify t1 t1'; rewrite H1 in H2
  end.
  do 10 eexists.
  split; eauto.
Qed.    

Lemma prteq_cheq_dst_ports_impl:
  forall O1 O2 v pr,
    prt_indom v O1 pr -> 
    obsr_equiv_chnd O1 O2 ->
    ports_equiv (dom_for_prio pr) O1 O2 ->
    has_dst_ports O1 v ->
    has_dst_ports O2 v. 
Proof.
  introv Hpi Hoe Hpe Hhp.
  unfolds in Hhp.
  unfolds in Hpe.
  simpljoin.
  unfolds in Hpi.
  destruct Hpi as (a & Hptreq & Hid).
  inverts Hptreq.
  match goal with H: forall _, _->_ |- _ => lets H__: H Hid end.
  destruct H__ as (Hdpleq & _).
  l_rew21_inv1 (get O1 osdomainportid). 
  match goal with
    H: ?t = _, H': ?t' = _ |- _ => unify t t'; rewrite H in H'
  end.
  symmetry in Hdpleq.
  unfolds in Hoe.
  destruct Hoe as ((Hchnn & Hcneq) & (Hkpnn & Hkpeq)).
  l_rew12_inv2 (get O1 oskportid).
  l_rew12_inv2 (get O1 oschannelid).
  unfolds.
  do 21 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
Qed.

Lemma prteq_src_prt_nfull_impl:
  forall O1 O2 v pr,
    prt_indom v O1 pr -> 
    (* obsr_equiv_chnd O1 O2 -> *)
    ports_equiv (dom_for_prio pr) O1 O2 ->      
    (exists a dpl pcn pd pid pst pin pout n msgl,
        v = Vptr a /\
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort n msgl) /\
          (length msgl < n)%nat) ->
    (exists a dpl pcn pd pid pst pin pout n msgl,
        v = Vptr a /\
          get O2 osdomainportid = Some (osdomainport dpl) /\
          get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort n msgl) /\
          (length msgl < n)%nat).
Proof.
  introv Hpi Hpe Hex1.
  simpljoin.
  unfolds in Hpi.
  destruct Hpi as (a & Hptreq & Hid).
  inverts Hptreq.
  unfolds in Hpe.
  simpljoin.
  match goal with
    H: forall _, _ -> _ |- _ => lets H__: H Hid
  end.
  destruct H__ as (Hdpleq & _).
  l_rew21_inv1 (get O1 osdomainportid).
  match goal with
    H: ?t = _, H': ?t' = _ |- _ => rewrite H in H'
  end.
  do 10 eexists.
  split; eauto. 
Qed.            

Lemma q_send_to_domain_mqref_preserve: 
  forall v v0 O O' O0 O0' Of act, 
    q_send_to_domain (v :: nil) O0 act (v0, Some O0') -> 
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
  assert (Hor: get O0 absmqattrid = Some (absmqattr mqs)
               \/ get Of absmqattrid = Some (absmqattr mqs)).
  {
    eapply join_get_or; eauto.
  }
  destruct Hor as [Hl | Hr].
  -
    eapply join_get_get_l with (a:=absmqattrid) (b:=absmqattr mqs) in Hjo'; eauto.
    2: {
      repeat rewsimp. auto. 
    }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto.
  -
    assert (get O' absmqattrid = Some (absmqattr mqs)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto.
Qed.

Lemma q_send_to_domain_qprt_preserve: 
  forall v O v' O' O0 O0' Of act, 
    q_send_to_domain (v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hsend Hjo Hjo'.
  unfolds in Hsend.
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
    match goal with
      H: dpl_upd _ _ _ _ _ |- _ =>
        unfolds in H; specialize (H a); rename H into Hdupd
    end.
    destruct Hdupd as [(Hnfull & Hupd) | (Hnfull & Hupdeq)].
    +
      simpljoin.
      match goal with H: get dpl' _ = _ |- _ => rewrite H end.
      match goal with
        H1: get dpl _ = _, H2: get dpl _ = _ |- _ =>
          rewrite H1 in H2; inverts H2
      end.
      do 7 eexists. eauto.
    +
      rewrite Hupdeq. eauto.
  -
    assert (get O' osdomainportid = Some (osdomainport dpl)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
Qed.


Lemma q_send_to_domain_ctid_equiv_preserve2:
  forall td O1 O2 vp1 vp2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    q_send_to_domain (vp1 :: nil) O10 act (v1, Some O10') ->
    q_send_to_domain (vp2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hsend1 Hsend2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets H1_: q_send_to_domain_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: q_send_to_domain_prio_preserved Hjo2 Hjo2'; eauto. 
  
  unfold ctid_equiv in *.
  unfold q_send_to_domain in *.
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
  lets H__: H37 Htpi1_ Htpi2_ Htd.
  auto.
  
Qed.

Lemma q_send_to_domain_bufs_equiv_preserve2:
  forall td O1 O2 vp O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr t1 t2, 
    bufs_equiv td O1 O2 -> 
    q_send_to_domain (vp :: nil) O10 act (v1, Some O10') ->
    q_send_to_domain (vp :: nil) O20 act (v2, Some O20') ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    prt_indom vp O1 pr -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    bufs_equiv td O1' O2'.
Proof.
  introv Hbfe Hsd1 Hsd2 Ht1 Ht2 Htpi1 Htpi2.
  introv Hid Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold bufs_equiv in *.
  destruct Hbfe as (Hibe & Hobe).
  inverts Hsd1. inverts Hsd2.
  simpljoin.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  do 2 match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  assert (Hgeq1: get O1' obufsid = get O1 obufsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto.     
  }
  assert (Hgeq2: get O2' obufsid = get O2 obufsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto.         
  }
  split.
  2: { (* obufs_equiv *)
    unfold obufs_equiv in *.
    destruct Hobe as (obm1 & obm2 & Hgom1 & Hgom2 & Hobeq).
    rewrite Hgeq1. rewrite Hgeq2. 
    do 2 eexists.
    split; eauto.
  }
  (* ibufs_equiv *)
  unfold ibufs_equiv in *.
  destruct Hibe as (ibm1 & ibm2 & Hgm1 & Hgm2 & Hibeq).
  kvext_h Hjo1' ibufsid O1'.
  kvext_h Hjo2' ibufsid O2'.
  do 2 eexists.
  split; eauto.
  split; eauto.
  kvext O10 ibufsid O1. 
  l_rew21_inv1 (get O1 ibufsid).
  kvext O20 ibufsid O2.
  l_rew21_inv1 (get O2 ibufsid).

  unfold dom_cur_tsk in *.
  simpljoin.
  kvext0 O10 curtid O1. kvext0 O20 curtid O2.
  l_rew21_inv1 (get O1 curtid). l_rew21_inv1 (get O2 curtid).
  
  apply11 (task_prio_id O10) (task_prio_id O20) tpi_frm_ext H1_ H2_.
  specializes H1_; eauto.
  specializes H2_; eauto.
  apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
  apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
  
  casetac (dom_for_prio pr) td Ht Hf.
  - subst. do 2 rewrite upd_bufmp_get_eq. congruence.
  - do 2 (rewrite upd_bufmp_get_neq; eauto). 
Qed.

Lemma q_send_to_domain_cpid_same:
  forall vp O act v' O' O0 O0' Of, 
    q_send_to_domain (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid.      
Proof.
  introv Hqsd Hjo Hjo'.
  inverts Hqsd.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  repeat rewsimp. auto.
Qed.   
  
Lemma q_send_to_domain_same_mqattr:  
  forall vp O act v' O' O0 O0' Of, 
    q_send_to_domain (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O absmqattrid = get O' absmqattrid. 
Proof.
  introv Hsd Hjo Hjo'.
  inverts Hsd.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto. 
  repeat rewsimp. 
  auto.
Qed.

Lemma q_send_to_domain_mqptr_impl:  
  forall vp O act v' O' O0 O0' Of, 
    q_send_to_domain (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hsend Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  inverts Hsend.
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

Lemma q_send_to_domain_mqptr_iff:  
  forall vp O act v' O' O0 O0' Of, 
    q_send_to_domain (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hsend Hjo Hjo'.
  intros.
  split.
  - 
    eapply q_send_to_domain_mqptr_impl; eauto. 
  -
    introv Hmqp.
    unfold mq_ptr in *.
    inverts Hsend.
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

Lemma q_send_to_domain_mq_ecbs_preserve: 
  forall v O v' O' O0 O0' Of act, 
    q_send_to_domain (v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ecbs_preserved O O'. 
Proof.
  introv Hsend Hjo Hjo'.
  unfolds in Hsend.
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
  match goal with
    H: ecbl_upd _ _ _ _ _ _ |- _ => rename H into Heu; specialize (Heu eid)
  end.
  destruct Heu as [Hnf | Hf].
  -
    unfold hwait_prt in *.
    simpljoin.
    unfold get in *. unfold EcbMap in *.
    l_rew21_inv1 (EcbMod.get els eid). 
  -
    simpljoin.
    congruence.
  
Qed. 

Lemma tidls_equiv_wl_nnil_impl:
  forall wl1 wl2 O1 O2, 
    tidls_equiv wl1 wl2 O1 O2 ->
    wl1 <> nil ->
    wl2 <> nil.
Proof.
  introv Hte Hnn1.
  unfolds in Hte.
  destruct Hte as (Hleneq & Htpieq).
  destruct wl1; destruct wl2; tryfalse. 
  introv Hf. false.
Qed.

Lemma tidls_equiv_gethwait_impl: 
  forall wl1 wl2 O1 O2 tls1 tls2 pr t1 t2, 
    tidls_equiv wl1 wl2 O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    (forall t, In t wl2 -> (exists pr', task_prio_id O2 pr' t /\ dom_for_prio pr' = dom_for_prio pr)) -> 
    GetHWait tls1 wl1 t1 ->
    GetHWait tls2 wl2 t2.
Proof.
  introv Hte Hgt1 Hgt2 Htpi1 Htpi2 Hinex2 Hghw1.
  unfold GetHWait in *.
  destruct Hghw1 as (Hin1 & Hex1).
  simpljoin.
  assert (Hte' := Hte). 
  unfold tidls_equiv in Hte.
  destruct Hte as (Hleneq & Htpreq).
  specialize (Htpreq pr).
  destruct Htpreq as (H12_ & H21_).
  assert (H12__ := H12_).
  specializes H12__; eauto.
  destruct H12__ as (t2_ & Hin2 & Htpi2_).
  apply2_rev (task_prio_id O2) (task_prio_id O2) tid_unique.
  split; auto.
  unfolds in Htpi2_.
  simpljoin.
  l_rew21_inv1 (get O2 abstcblsid).
  do 5 eexists.
  split; eauto.
  assert (Htpi1_ := Htpi1).
  unfolds in Htpi1_.
  simpljoin.
  l_rew21_inv1 (get O1 abstcblsid).
  match goal with
    H1: context [get tls1], H2: context [get tls1] |- _ => rewrite H1 in H2; inverts H2
  end.
  introv Hne2 Hin2'.
  lets H2__: Hinex2 Hin2'.
  destruct H2__ as (pr' & Htpi2' & Hdeq').
  rename t' into t2'.

  destruct Hte' as (Hleneq' & Htpieq').
  specialize (Htpieq' pr').
  destruct Htpieq' as (Hintpi2' & Hintpi1').
  specializes Hintpi1'; eauto.
  destruct Hintpi1' as (t1' & Hin1' & Htpi1').
  casetac t1 t1' Ht Hf.
  - subst t1'.
    apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
    apply2 (task_prio_id O2) (task_prio_id O2) tid_unique.
    (* t2' <> t2' --- contradiction *) 
    false. 
  - match goal with
      H: forall _, _ <> _ -> _ |- _ => lets H__: H Hf Hin1'
    end.
    simpljoin.
    match goal with
      H: get tls1 t1' = Some (_, ?p) |- _ => assert (Htpi1'_: task_prio_id O1 p t1')
    end.
    unfolds. do 5 eexists. split; eauto.
    apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
    unfolds in Htpi2'. simpljoin.
    l_rew21_inv1 (get O2 abstcblsid).
    do 5 eexists.
    split; eauto. 
Qed.              

Lemma hwait_prt_impl:
  forall kmp kaddrs dpl1 dpl2 els1 els2 tls1 tls2 t1 t2 pr0 O1 O2, 
    ports_equiv (dom_for_prio pr0) O1 O2 ->
    get O1 osdomainportid = Some (osdomainport dpl1) -> 
    get O2 osdomainportid = Some (osdomainport dpl2) ->
    get O1 absecblsid = Some (absecblist els1) ->
    get O2 absecblsid = Some (absecblist els2) ->
    (exists wl a, hwait_prt a kmp kaddrs dpl1 els1 tls1 wl t1) ->
    task_prio_id O1 pr0 t1 ->
    task_prio_id O2 pr0 t2 ->
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) -> 
    (exists wl a, hwait_prt a kmp kaddrs dpl2 els2 tls2 wl t2).
Proof. 
  introv Hpe Hgdp1 Hgdp2 Hgels1 Hgels2 Hex Hgt1 Hgt2.
  introv Hgtcbs1 Hgtcbs2.
  unfold hwait_prt in *.
  simpljoin.
  match goal with H: context [(absport, ?x)] |- _ => rename x into wl1 end.
  assert (Hinwl1: In t1 wl1).
  { unfold GetHWait in *. simpljoin. auto. }
  lets H__: qprt_part_consistent (dom_for_prio pr0) Hgels1 Hinwl1; eauto.
  destruct H__ as (Hpdom & Htdom).
  specializes Hpdom.
  { eexists. split; eauto. }
  unfolds in Hpe.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  match goal with H: forall _, _->_ |- _ => lets H__: H Hpdom end.
  destruct H__ as (Hprteq & Hexprteq &  Htidlseq).
  match goal with H1: ?t = _, Hprteq: ?t = _ |- _ => rewrite H1 in Hprteq end.
  symmetry in Hprteq.
  lets H__: prt_ecb_consistent Hgdp2 Hgels2 x0; eauto.
  destruct H__ as (Hexecb & Hexdp).
  specializes Hexecb.
  { eexists; eauto. }
  destruct Hexecb as (wl2 & Hgwl2).
  specializes Htidlseq; eauto.  
  do 15 eexists.
  split; eauto.
  split; eauto.
  split; eauto. 
  split; eauto. 
  split. eapply tidls_equiv_wl_nnil_impl; eauto.
  assert (Hextpi2:
           forall t, In t wl2 -> (exists pr, task_prio_id O2 pr t /\ dom_for_prio pr = dom_for_prio pr0)).
  {
    introv Hin2.
    lets H__: qprt_part_consistent Hgels2 Hgwl2 Hin2. 
    eapply H__ in Hpdom. auto.
  }
  eapply tidls_equiv_gethwait_impl; eauto. 

Qed.

Lemma knl_task_equiv_send_to_domain_preserve2:
  forall td O1 O2 vp O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr, 
    obsr_equiv_chnd O1 O2 ->
    kernel_task_equiv td O1 O2 -> 
    ports_equiv td O1 O2 -> 
    q_send_to_domain (vp :: nil) O10 act (v1, Some O10') ->
    q_send_to_domain (vp :: nil) O20 act (v2, Some O20') ->
    prt_indom vp O1 pr ->
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    kernel_task_equiv td O1' O2'.
Proof.
  introv Hoec Hkte Hpe Hsd1 Hsd2 Hpi Hpe_. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold kernel_task_equiv in *.
  lets Hpp1: q_send_to_domain_prio_preserved Hjo1 Hjo1' ; eauto. 
  lets Hpp2: q_send_to_domain_prio_preserved Hjo2 Hjo2'; eauto.  
  inverts Hsd1. inverts Hsd2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _  |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end. 
  kvext_h Hjo1' abstcblsid O1'.
  kvext_h Hjo2' abstcblsid O2'. 
  do 2 eexists. 
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _->_ |- _ => lets H__: H Hd end.
  destruct H__ as (Htpi_iff & Htskeq).  
  split.
  - eapply prio_preserved_tpieq_impl; eauto.
  - 
    kvext O10 abstcblsid O1.
    kvext O20 abstcblsid O2.
    l_rew21_inv1 (get O1 abstcblsid).
    l_rew21_inv1 (get O2 abstcblsid).
    match goal with
      H: get O1 abstcblsid = Some (abstcblist ?tcbs) |- _ => rename tcbs into tcbs1
    end.
    match goal with
      H: get O2 abstcblsid = Some (abstcblist ?tcbs) |- _ => rename tcbs into tcbs2
    end.
    match goal with
      H: get O1' abstcblsid = Some (abstcblist ?tcbs) |- _ => rename tcbs into tcbs1'
    end.
    match goal with
      H: get O2' abstcblsid = Some (abstcblist ?tcbs) |- _ => rename tcbs into tcbs2'
    end.
    unfold ports_equiv in Hpe_.
    simpljoin.
    unfolds in Hpi.
    destruct Hpi as (a & Hptreq & Haid).
    inverts Hptreq.
    lets H__: H35 Haid.
    destruct H__ as (Hgeteq & Hforall).
    kvext O10 osdomainportid O1.
    kvext O20 osdomainportid O2.
    l_rew21_inv1 (get O1 osdomainportid).
    l_rew21_inv1 (get O2 osdomainportid).
    match goal with H: ?t = _, H': ?t = ?t' |- _ => rewrite H in H' end.
    match goal with H: ?t' = _, H': _ = ?t' |- _ => rewrite H in H' end.
    inverts Hgeteq.
    unfolds in Hoec.
    destruct Hoec as ((Hcne & Hceq) & (Hkne & Hkeq)).
    kvext O10 oschannelid O1.
    kvext O20 oschannelid O2.
    match goal with
      Hceq: ?t1 = ?t2, H1: ?t1 = _, H2: ?t2 = _ |- _ =>
        rewrite H1 in Hceq; rewrite H2 in Hceq; inverts Hceq
    end.
    kvext O10 oskportid O1.
    kvext O20 oskportid O2.
    match goal with
      Hkeq: ?t1 = ?t2, H1: ?t1 = _, H2: ?t2 = _ |- _ =>
        rewrite H1 in Hkeq; rewrite H2 in Hkeq; inverts Hkeq
    end.
    match goal with H: tcbl_upd ?km _ _ _ _ _ |- _ => rename km into kmp end. 
    match goal with
      H: get O1 oskportid = _ |- _ =>
        lets H__: kprt_addr_unique H; eauto
    end.
    match goal with
      H1: get kmp _ = _, H2: get kmp _ = _ |- _ => lets H'__: H__ H1 H2; eauto; clear H__
    end.
    subst.
    match goal with
      H1: get kmp _ = _, H2: get kmp _ = _ |- _ =>
        rewrite H1 in H2; inverts H2
    end.
    match goal with
      H: get O1 oschannelid = Some (oschannel ?chs) |- _ =>
        rename chs into chmp
    end.
    match goal with
      H1: get chmp _ = _, H2: get chmp _ = _ |- _ =>
        rewrite H1 in H2; inverts H2
    end.
    kvext O10 absecblsid O1.
    kvext O20 absecblsid O2.
    l_rew21_inv1 (get O1 absecblsid).
    l_rew21_inv1 (get O2 absecblsid).
    
    match goal with x: list addrval |- _ => rename x into dstkpaddrs end.
    (* assert (Hcs: *)
    (*          dom_among_dest dstkpaddrs kmp (dom_for_prio pr0) \/ *)
    (*            ~dom_among_dest dstkpaddrs kmp (dom_for_prio pr0)) by tauto. *)
    (* destruct Hcs as [Haffected | Hnaffected]. *)
    (* + *)

    (* unfold tcbl_upd in *. *)

    intros t1_ t2_.
    introv Hgt1_ Hgt2_.
    match goal with
      H: tcbl_upd _ _ _ _ tcbs1 tcbs1' |- _ =>
        specialize (H t1_); rename H into Hupd1
    end.
    match goal with
      H: tcbl_upd _ _ _ _ tcbs2 tcbs2' |- _ =>
        specialize (H t2_); rename H into Hupd2
    end.
    assert (Htpi1_: task_prio_id O1' pr0 t1_).
    { unfolds. do 5 eexists. split; eauto. }
    assert (Htpi2_: task_prio_id O2' pr0 t2_).
    { unfolds. do 5 eexists. split; eauto. }
    lets Htpi1: prio_preserved_tpi Htpi1_ Hpp1; eauto.
    lets Htpi2: prio_preserved_tpi Htpi2_ Hpp2; eauto. 
    destruct Hupd1 as [(Hex1 & Hupd1) | (Hnex1 & Hupdeq1)];
      destruct Hupd2 as [(Hex2 & Hupd2) | (Hnex2 & Hupdeq2)].
    2: {
      lets H__: hwait_prt_impl Hpe Hex1; eauto. 
      specializes H__; eauto.
      false.
    }
    2: {
      apply ports_equiv_sym in Hpe.
      lets H__: hwait_prt_impl Hpe Hex2; eauto.
      specializes H__; eauto.
      false.
    }
    (* hwait_prt *)
    destruct Hupd1 as (p1 & st1_ & msg1_ & sus1_ & p01 & Htcbs1 & Htcbs1').
    destruct Hupd2 as (p2 & st2_ & msg2_ & sus2_ & p02 & Htcbs2 & Htcbs2').
    assert (Htpi10_: task_prio_id O1 p01 t1_).
    { unfolds. do 5 eexists. split; eauto. }
    assert (Htpi20_: task_prio_id O2 p02 t2_).
    { unfolds. do 5 eexists. split; eauto. }
    apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
    apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
    lets Heq0: Htskeq Htcbs1 Htcbs2.
    rewrite Htcbs1' in Hgt1_. inverts Hgt1_.
    rewrite Htcbs2' in Hgt2_. inverts Hgt2_. 
    simpljoin.
    splits; auto.
    (* ~hwait_prt *)
    rewrite Hupdeq1 in Hgt1_.
    rewrite Hupdeq2 in Hgt2_.
    eapply Htskeq; eauto. 
Qed. 

Lemma dst_port_not_full_impl: 
  forall kprts dstkpaddrs dpl1 dpl2 a, 
    dst_port_not_full kprts dstkpaddrs dpl1 a ->
    get dpl1 a = get dpl2 a -> 
    dst_port_not_full kprts dstkpaddrs dpl2 a. 
Proof.
  introv Hdnf1 Hgeq.
  unfold dst_port_not_full in *.
  simpljoin.
  match goal with
    H: ?t = _, Hgeq: ?t = _ |- _ => rewrite H in Hgeq
  end.
  symmetry in Hgeq.
  do 13 eexists.
  split; eauto.
Qed. 

Lemma hwait_prt_tsk_exists:
  forall O a kprtmp dstkpas dpl els tls wl t' td,
    get O absecblsid = Some (absecblist els) ->
    get O abstcblsid = Some (abstcblist tls)  -> 
    hwait_prt a kprtmp dstkpas dpl els tls wl t' ->
    addrval_in_dom a td = true -> 
    exists p st msg sus p0, 
      get tls t' = Some (p, st, msg, sus, p0) /\ dom_for_prio p0 = td.
Proof.
  introv Hgels Hgtls Hw Hid.
  unfolds in Hw.
  simpljoin.
  unfold GetHWait in *.
  simpljoin.
  lets H__: qprt_part_consistent.
  specializes H__; eauto.
  apply H__ in Hid.
  simpljoin.
  unfold task_prio_id in *.
  simpljoin.
  l_rew12_inv2 (get O abstcblsid).
  match goal with H1: ?t1 = _, H2: ?t2 = _ |- _ => rewrite H1 in H2; inverts H2 end. 
  do 5 eexists.
  split; eauto.
Qed.

Require Import protect.

Lemma hwait_prt_impl':
  forall kmp kaddrs dpl1 dpl2 els1 els2 tls1 tls2 t1 O1 O2 td a, 
    ports_equiv td O1 O2 ->
    kernel_task_equiv td O1 O2 -> 
    get O1 osdomainportid = Some (osdomainport dpl1) -> 
    get O2 osdomainportid = Some (osdomainport dpl2) ->
    get O1 absecblsid = Some (absecblist els1) ->
    get O2 absecblsid = Some (absecblist els2) ->
    addrval_in_dom a td = true ->
    (exists wl, hwait_prt a kmp kaddrs dpl1 els1 tls1 wl t1) ->
    (* task_prio_id O1 pr0 t1 -> *)
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) -> 
    (exists t wl, hwait_prt a kmp kaddrs dpl2 els2 tls2 wl t).
Proof. 
  introv Hpe Hkte Hgdp1 Hgdp2 Hgels1 Hgels2 Hid Hex.
  introv Hgtcbs1 Hgtcbs2.
  assert (Hex_ := Hex).
  unfold hwait_prt in Hex. unfold hwait_prt.
  protect Hex_. 
  simpljoin.
  match goal with H: context [(absport, ?x)] |- _ => rename x into wl1 end.
  unfolds in Hpe.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  match goal with H: forall _, _->_ |- _ => lets H__: H Hid end.
  destruct H__ as (Hprteq & Htidlseq).
  match goal with H1: ?t = _, Hprteq: ?t = _ |- _ => rewrite H1 in Hprteq end.
  symmetry in Hprteq.
  lets H__: prt_ecb_consistent Hgdp2 Hgels2 a; eauto.
  destruct H__ as (Hexecb & Hexdp).
  specializes Hexecb.
  { eexists; eauto. }
  destruct Hexecb as (wl2 & Hgwl2).
  specializes Htidlseq; eauto.

  unprotect Hex_.
  destruct Hex_ as (ws_ & Hwp).
  lets H__: hwait_prt_tsk_exists td Hwp; eauto.
  specializes H__; eauto. 
  simpljoin.
  match type of Hkte with context [dom_for_prio ?pr] => rename pr into pr0 end.
  assert (Hext1: exists t, task_prio_id O1 pr0 t).
  { exists t1. unfolds. do 5 eexists. split; eauto. }
  unfolds in Hkte.
  destruct Hkte as (tls1_ & tls2_ & Hg1 & Hg2 & Hallp).
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).
  specialize (Hallp pr0 (eq_refl _)).
  destruct Hallp as (Hiff & _).
  assert (Hext2: exists t, task_prio_id O2 pr0 t).
  { apply Hiff in Hext1. auto. }
  destruct Hext2 as (t2 & Htpi2).
  exists t2.
  destruct Hext1 as (t1_ & Htpi1).
  assert (task_prio_id O1 pr0 t1).
  { unfolds. do 5 eexists. split; eauto. }
  apply2 (task_prio_id O1) (task_prio_id O1) tid_unique. 
  
  do 14 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  split. eapply tidls_equiv_wl_nnil_impl; eauto.
  assert (Hextpi2:
           forall t, In t wl2 -> (exists pr, task_prio_id O2 pr t /\ dom_for_prio pr = dom_for_prio pr0)).
  {
    introv Hin2.
    lets H__: qprt_part_consistent Hgels2 Hgwl2 Hin2.
    eapply H__ in Hid. auto.
  }
  lets H__: qprt_part_consistent a t1 (dom_for_prio pr0) Hgels1; eauto.
  specializes H__; eauto.
  { unfold GetHWait in *. simpljoin. auto. }
  destruct H__ as (Htdom & Hpdom).
  specialize (Hpdom Hid).
  simpljoin.
  apply2 (task_prio_id O1) (task_prio_id O1) prio_unique.

  eapply tidls_equiv_gethwait_impl; eauto.

Qed.

Lemma hwait_prt_in_wl:
  forall a kprtmp dstkpas dpl els tls wl t', 
    hwait_prt a kprtmp dstkpas dpl els tls wl t' -> In t' wl. 
Proof.
  introv Hwt.
  unfolds in Hwt.
  simpljoin.
  unfold GetHWait in *.
  simpljoin.
  auto.
Qed. 

Lemma hwait_prt_get_ecb:
  forall a kprtmp dstkpas dpl els tls wl t, 
    hwait_prt a kprtmp dstkpas dpl els tls wl t ->
    get els a = Some (absport, wl).
Proof.
  introv Hwp.
  unfolds in Hwp.
  simpljoin.
  auto.
Qed. 

Lemma kte_tidls_eq_hwait_prt_eq: 
  forall td O1 O2 wl1 wl2 tls1 tls2 els1 els2 t1 t2 a x8 x17 dpl1 dpl2, 
    kernel_task_equiv td O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tls1) ->
    get O2 abstcblsid = Some (abstcblist tls2) ->
    get O1 absecblsid = Some (absecblist els1) ->
    get O2 absecblsid = Some (absecblist els2) -> 
    addrval_in_dom a td = true -> 
    hwait_prt a x8 x17 dpl1 els1 tls1 wl1 t1 ->
    hwait_prt a x8 x17 dpl2 els2 tls2 wl2 t2 -> 
    tidls_equiv wl1 wl2 O1 O2 -> 
    (exists pr0, task_prio_id O1 pr0 t1 /\ task_prio_id O2 pr0 t2 /\ dom_for_prio pr0 = td).
Proof.
  introv Hkte Hgt1 Hgt2 Hge1 Hge2 Hid Hwt1 Hwt2 Hteq.
  lets Hin1: hwait_prt_in_wl Hwt1; eauto.
  lets Hin2: hwait_prt_in_wl Hwt2; eauto.
  unfolds in Hwt1.
  unfolds in Hwt2.
  simpljoin. 
  assert (Ha1: forall t : tid, In t wl1 -> exists pr, task_prio_id O1 pr t /\ dom_for_prio pr = td).
  {
    introv Hint1.    
    lets H1_: qprt_part_consistent td Hge1 Hint1; eauto.
    tauto.
  }
  assert (Ha2: forall t : tid, In t wl2 -> exists pr, task_prio_id O2 pr t /\ dom_for_prio pr = td).
  {
    introv Hint2.    
    lets H2_: qprt_part_consistent td Hge2 Hint2; eauto.
    tauto.
  }
  lets H__: kte_tidls_eq_gethwait_eq Hkte Hteq; eauto.
Qed. 

Lemma ports_equiv_send_to_domain_preserve2:
  forall td O1 O2 vp O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr t1 t2, 
    obsr_equiv_chnd O1 O2 ->    
    ports_equiv td O1 O2 ->
    kernel_task_equiv td O1 O2 -> 
    bufs_equiv (dom_for_prio pr) O1 O2 -> 
    q_send_to_domain (vp :: nil) O10 act (v1, Some O10') ->
    q_send_to_domain (vp :: nil) O20 act (v2, Some O20') ->
    prt_indom vp O1 pr ->
    ports_equiv (dom_for_prio pr) O1 O2 ->
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
  introv Hoe Hpe Hkte Hbe Hsd1 Hsd2 Hpi Hpe_. 
  introv Hgct1 Hgct2 Htpi1 Htpi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  assert (Hsd1_ := Hsd1). assert (Hsd2_ := Hsd2). 
  unfolds in Hsd1. unfolds in Hsd2.
  assert (Hpe0 := Hpe). 
  unfolds in Hpe.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ =>  inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end. 
  kvext_h Hjo1' osdomainportid O1'.
  kvext_h Hjo2' osdomainportid O2'.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext O10 oskportid O1.
  kvext O20 oskportid O2.
  kvext O10 oschannelid O1.
  kvext O20 oschannelid O2.
  unfolds in Hoe.
  destruct Hoe as ((Hcne & Hceq) & (Hkne & Hkeq)).
  match goal with
    Hceq: ?t1 = ?t2, H1: ?t1 = _, H2: ?t2 = _ |- _ =>
      rewrite H1 in Hceq; rewrite H2 in Hceq; inverts Hceq
  end.
  match goal with
    Hkeq: ?t1 = ?t2, H1: ?t1 = _, H2: ?t2 = _ |- _ =>
      rewrite H1 in Hkeq; rewrite H2 in Hkeq; inverts Hkeq
  end.
  unfolds.
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _->_ |- _ => lets H__: H Hd end.
  destruct H__ as (Hgeq & Hiff & Hforall).
  kvext O10 osdomainportid O1.
  kvext O20 osdomainportid O2.
  l_rew12_inv2 (get O1 osdomainportid).
  l_rew12_inv2 (get O2 osdomainportid).

  match goal with
    H1: get O1 osdomainportid = Some (osdomainport ?z1) |- _ => rename z1 into dpl1
  end.
  match goal with
    H2: get O2 osdomainportid = Some (osdomainport ?z2) |- _ => rename z2 into dpl2
  end.

  unfolds in Hpi.
  destruct Hpi as (a' & Hptreq & Hid).
  inverts Hptreq.
  unfolds in Hpe_.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.
  match goal with
    H: forall _, _ _ (dom_for_prio pr) = _ -> _ |- _ => lets H__: H Hid
  end.
  destruct H__ as (Hpeq' & Hprtiff & Htidlseq').
  match goal with
    Hpeq': ?t1 = ?t2, H1: ?t1 = _, H2: ?t2 = _ |- _ =>
      rewrite H1 in Hpeq'; rewrite H2 in Hpeq'; inverts Hpeq'
  end.
  match goal with
    H: get O1 oskportid = Some (oskport ?kpl),
    H1: get ?kpl _ = _, H2: get ?kpl _ = _ |- _ => 
      lets H__: kprt_addr_unique H H1 H2; eauto; subst;
      rewrite H1 in H2; inverts H2
  end.
  match goal with
    H: get O1 oschannelid = Some (oschannel ?chs) |- _ => rename chs into chmp
  end.
  match goal with
    H1: get chmp _ = _, H2: get chmp _ = _ |- _ => rewrite H1 in H2; inverts H2
  end.
  kvext O10 ibufsid O1.
  kvext O20 ibufsid O2.
  lets H__: dom_cur_tsk_dom_eq Hjo1 Hjo2; eauto.
  specializes H__; eauto.
  destruct H__; subst.
  
  lets H__: bufs_equiv_ibmp_eq Hbe Hjo1 Hjo2; eauto.
  match goal with
    H1: ?t1 = _, H2: ?t2 = _, H__: ?t1 = ?t2 |- _ =>
      rewrite H1 in H__; rewrite H2 in H__; inverts H__
  end.
  
  split.
  
  - (* get dpl1' a = get dpl2' a *)
    match goal with
      |- get ?z1 _ = get ?z2 _ => rename z1 into dpl1'; rename z2 into dpl2'
    end.
    match goal with
      H1: dpl_upd _ _ _ dpl1 _, H2: dpl_upd _ _ _ dpl2 _ |- _ =>
        rename H1 into Hdu1; rename H2 into Hdu2
    end.
    specialize (Hdu1 a). specialize (Hdu2 a).
    destruct Hdu1 as [(Hnfull1 & Hprtupd1) | (Hfull1 & Hprtupdeq1)];
      destruct Hdu2 as [(Hnfull2 & Hprtupd2) | (Hfull2 & Hprtupdeq2)].
    2: { 
      lets H__: dst_port_not_full_impl Hnfull1 Hgeq; eauto.
      false.
    }
    2: {
      symmetry in Hgeq.
      lets H__: dst_port_not_full_impl Hnfull2 Hgeq; eauto.
      false.
    }
    (* dst_port_not_full *)
    simpljoin.
    match goal with 
      H1: ?t1 = _, H2: ?t2 = _, Hgeq: ?t1 = ?t2 |- _ =>
        rewrite H1 in Hgeq; rewrite H2 in Hgeq; inverts Hgeq 
    end.
    match goal with
      H1: ?t1 = _, H2: ?t2 = _ |- ?t1 = ?t2 =>
        rewrite H1; rewrite H2
    end.
    auto. 
  (* ~dst_port_not_full *)
    match goal with
      H1: ?t1 = _, H2: ?t2 = _ |- ?t1 = ?t2 =>
        rewrite H1; rewrite H2
    end.
    auto.

  -    
    lets Hpp1: q_send_to_domain_prio_preserved Hjo1 Hjo1'; eauto.
    lets Hpp2: q_send_to_domain_prio_preserved Hjo2 Hjo2'; eauto.     
    l_rew12_inv2 (get O1 absecblsid).
    l_rew12_inv2 (get O2 absecblsid). 
    
    split.
    (* iff *)
    +
      match goal with
        H1: ecbl_upd _ _ _ _ _ _, H2: ecbl_upd _ _ _ _ _ _ |- _ =>
          rename H1 into Hupd1; rename H2 into Hupd2
      end.
      kvext O10 abstcblsid O1.
      kvext O20 abstcblsid O2.
      specialize (Hupd1 a). specialize (Hupd2 a).

      destruct Hupd1 as [(t1' & wl1' & Hexhw1 & Heupd1) | (Hnexhw1 & Heupdeq1')];
        destruct  Hupd2 as [(t2' & wl2' & Hexhw2 & Heupd2) | (Hnexhw2 & Heupdeq2')].
      2: {
        lets H__: hwait_prt_impl' Hpe0.
        specializes H__; eauto. 
        false.
      }
      2: {
        apply ports_equiv_sym in Hpe0.
        apply kernel_task_equiv_sym in Hkte.
        lets H__: hwait_prt_impl' Hpe0.
        specializes H__; eauto.
        false.
      }
      {
        rewrite Heupd1.
        rewrite Heupd2.
        split; intros; eexists; eauto.      
      }
      {
        rewrite Heupdeq1'.
        rewrite Heupdeq2'.
        auto.
      }
    +
      (* tidls_equiv *)
      introv Hecb1' Hecb2'. 
      match type of Hecb1' with get ?e _ = _  => rename e into els1 end.
      match type of Hecb2' with get ?e _ = _  => rename e into els2 end.
      match goal with
        H1: ecbl_upd _ _ _ _ _ _, H2: ecbl_upd _ _ _ _ _ _ |- _ =>
          rename H1 into Hupd1; rename H2 into Hupd2
      end.
      kvext O10 abstcblsid O1.
      kvext O20 abstcblsid O2.
      specialize (Hupd1 a). specialize (Hupd2 a).

      destruct Hupd1 as [(t1' & wl1' & Hexhw1 & Heupd1) | (Hnexhw1 & Heupdeq1')];
        destruct  Hupd2 as [(t2' & wl2' & Hexhw2 & Heupd2) | (Hnexhw2 & Heupdeq2')].
      2: {
        lets H__: hwait_prt_impl' Hpe0.
        specializes H__; eauto. 
        false.
      }
      2: {
        apply ports_equiv_sym in Hpe0.
        apply kernel_task_equiv_sym in Hkte.
        lets H__: hwait_prt_impl' Hpe0.
        specializes H__; eauto.
        false.
      }
      (*  *)
      rewrite Heupd1 in Hecb1'.
      rewrite Heupd2 in Hecb2'.
      inverts  Hecb1'. inverts Hecb2'.
      lets Hecb1: hwait_prt_get_ecb Hexhw1; eauto.
      lets Hecb2: hwait_prt_get_ecb Hexhw2; eauto.


      lets Hteq0: Hforall Hecb1 Hecb2.
      lets Hin1: hwait_prt_in_wl Hexhw1; eauto.
      lets Hin2: hwait_prt_in_wl Hexhw2; eauto. 
      assert (Hex: exists pr0, task_prio_id O1 pr0 t1'
                               /\ task_prio_id O2 pr0 t2'
                               /\ dom_for_prio pr0 = td).
      { eapply kte_tidls_eq_hwait_prt_eq; eauto. }
      destruct Hex as (pr0 & Htpi1'0 & Htpi2'0 & Hpd).
      lets H__: tidls_equiv_rm_preserve2 t1' t2' Hteq0 Hin1 Hin2; eauto.
      specializes H__; eauto.
      lets H1__: distinct_wait_tids_prt Hecb1; eauto.
      lets H2__: distinct_wait_tids_prt Hecb2; eauto.
      (*  *)
      assert (Hteq0: tidls_equiv tls1 tls2 O1 O2).
      {
        eapply Hforall; eauto.
        rewrite <- Heupdeq1'.
        auto.
        rewrite <- Heupdeq2'.
        auto.
      }
      eapply tidls_equiv_pp_preserve2; eauto. 
Qed.

Lemma buffer_equiv_q_send_to_domain_preserve2:
  forall vp O10 O20 O10' O20' O1 O2 act v1 v2 td Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    q_send_to_domain (vp :: nil) O10 act (v1, Some O10') -> 
    q_send_to_domain (vp :: nil) O20 act (v2, Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2'. 
  lets Hpp1: q_send_to_domain_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: q_send_to_domain_prio_preserved Hqn2; eauto.
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
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  match goal with
    H1: context [ecbl_upd], H2: context [ecbl_upd] |- _ =>
      rename H1 into Heu1; rename H2 into Heu2
  end.
  eapply buffer_equiv_nupd_preserve2; eauto.
  {          
    intro eid. intro Hd.
    unfolds in Heu1.
    specialize (Heu1 eid).
    destruct Heu1 as [Hupd | Hnupd].
    - destruct Hupd as (t' & wl &  Hhp & Hgprt).
      unfolds in Hhp.
      simpljoin.
      match goal with
        H: get O1 absecblsid = _ |- _ => lets Hbf: buffer_ecb Hd H; eauto
      end.
      simpljoin.
      match goal with
        H1: get _ eid = _, H2: get _ eid = _ |- _ => rewrite H1 in H2; inverts H2
      end.
    -
      simpljoin.
      auto.
  }
  {          
    intro eid. intro Hd.
    unfolds in Heu2.
    specialize (Heu2 eid).
    destruct Heu2 as [Hupd | Hnupd].
    - destruct Hupd as (t' & wl &  Hhp & Hgprt).
      unfolds in Hhp.
      simpljoin.
      match goal with
        H: get O2 absecblsid = _ |- _ => lets Hbf: buffer_ecb Hd H; eauto
      end.
      simpljoin.
      match goal with
        H1: get _ eid = _, H2: get _ eid = _ |- _ => rewrite H1 in H2; inverts H2
      end.
    -
      simpljoin.
      auto.
  }
Qed.
    
Lemma q_send_to_domain_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr vp v1 v2 O10 O20 O10' O20' O1' O2' act Of1 Of2 t1 t2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    bufs_equiv (dom_for_prio pr) O1 O2 -> 
    obsr_equiv_chnd O1 O2 -> 
    prt_indom vp O1 pr -> 
    prt_indom vp O2 pr -> 
    q_send_to_domain (vp :: nil) O10 act (v1, Some O10') -> 
    q_send_to_domain (vp :: nil) O20 act (v2, Some O20') -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hde Hkte Hpe Hbe_ Hoec Hpi1 Hpi2 Hsend1 Hsend2. 
  introv Hgc1 Hgc2 Htpi1 Htpi2 Hdi1 Hdi2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'. 
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hce & Hbe & Hkde & Hcde).
  splits.
  -
    (*ctid_equiv *)
    lets H__: q_send_to_domain_ctid_equiv_preserve2 Hjo1 Hjo2; eauto.
  - 
    (* bufs_equiv *)
    clear Hbe_.
    lets H__: q_send_to_domain_bufs_equiv_preserve2 Hpi1 Hjo1 Hjo2; eauto. 
  -
    (* kernel_data_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte_ & Hkme_ & Hpe_ & Hbfe_ &  Hce_).
    splits.
    + (* kernel_task_equiv *)    
    lets H__: knl_task_equiv_send_to_domain_preserve2
                Hkte_ Hjo1 Hjo2 Hjo1' Hjo2'; eauto.
    + (* kernel_mq_equiv *)
      eapply knl_mq_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto. 
      lets H__: q_send_to_domain_same_mqattr Hjo1 Hjo1'; eauto. 
      lets H__: q_send_to_domain_same_mqattr Hjo2 Hjo2'; eauto. 
      lets H__: q_send_to_domain_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: q_send_to_domain_prio_preserved Hjo2 Hjo2'; eauto. 
      lets H__: q_send_to_domain_mq_ecbs_preserve Hjo1 Hjo1'; eauto.
      lets H__: q_send_to_domain_mq_ecbs_preserve Hjo2 Hjo2'; eauto.
    + (* ports_equiv *)
      lets H__: ports_equiv_send_to_domain_preserve2 Hoec Hpe_ Hkte_ Hbe_; eauto. 
    + (* buffer_equiv *)      
      eapply buffer_equiv_q_send_to_domain_preserve2; eauto.           
    + (* cap_equiv *)
      eapply cap_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto.
      lets H__: q_send_to_domain_cpid_same Hjo1 Hjo1'; eauto. 
      lets H__: q_send_to_domain_cpid_same Hjo2 Hjo2'; eauto. 
      lets H__: q_send_to_domain_mqptr_iff Hjo1 Hjo1'; eauto. 
      lets H__: q_send_to_domain_mqptr_iff Hjo2 Hjo2'; eauto. 
  -
    (* client_data_equiv *)
    eapply cde_prio_preserved_preserve2; eauto. 
    lets H__: q_send_to_domain_prio_preserved Hjo1 Hjo1'; eauto. 
    lets H__: q_send_to_domain_prio_preserved Hjo2 Hjo2'; eauto. 
 
Qed. 

Lemma store_msg_tls_same:
  forall v act v0 O O' Of O0 O0',  
    store_msg (v :: nil) O0 act (v0, Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    get O abstcblsid = get O' abstcblsid. 
Proof.
  introv Hsm Hjo Hjo'.
  inverts Hsm.
  simpljoin.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  repeat rewsimp. auto.
Qed.

Lemma store_msg_mqref_preserve: 
  forall v v0 O O' O0 O0' Of act, 
    store_msg (v :: nil) O0 act (v0, Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hsm Hjo Hjo'.
  unfolds in Hsm.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
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
      repeat rewsimp. auto. 
    }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto.
  -
    assert (get O' absmqattrid = Some (absmqattr mqs)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' absmqattrid).
    introv Hg. auto.
Qed.

Lemma store_msg_qprt_preserve: 
  forall v O v' O' O0 O0' Of act, 
    store_msg (v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hsm Hjo Hjo'.
  unfolds in Hsm.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  kvext_h Hjo' osdomainportid O'.
  l_rew21_inv1 (get O' osdomainportid).
  introv Hgdp.
  simpljoin.

  assert (get O osdomainportid = Some (osdomainport x0)). 
  { eapply join_get_get_l; eauto. } 
  l_rew21_inv1 (get O osdomainportid).
  
  casetac x a Ht Hf.
  + subst.
    rewrite set_a_get_a.
    match goal with
      H1: get dpl a = _, H2: get dpl a = _ |- _ => rewrite H1 in H2; inverts H2
    end.
    do 7 eexists; eauto.
  + rewrite set_a_get_a'; eauto.
    do 7 eexists; eauto. 
Qed. 

Lemma store_msg_ctid_equiv_preserve2:
  forall td O1 O2 vp1 vp2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    store_msg (vp1 :: nil) O10 act (v1, Some O10') ->
    store_msg (vp2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hsm1 Hsm2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets H1_: store_msg_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: store_msg_prio_preserved Hjo2 Hjo2'; eauto. 
  
  unfold ctid_equiv in *.
  unfold store_msg in *.
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
  lets H__: H19 Htpi1_ Htpi2_ Htd.
  auto.
  
Qed.

Lemma tpi_frm_extend:
  forall O0 Of O p t, 
    task_prio_id O0 p t ->
    join O0 Of O ->
    task_prio_id O p t.
Proof.
  introv Htpi Hjo.
  unfold task_prio_id in *.
  simpljoin.
  do 5 eexists.
  split; eauto.
  eapply join_get_get_l; eauto. 
Qed. 

Lemma strore_msg_bufs_equiv_preserve2:
  forall td O1 O2 vp v1 v2 act O10 O20 O10' O20' O1' O2' t1 t2 pr Of1 Of2, 
    bufs_equiv td O1 O2 ->
    store_msg (vp :: nil) O10 act (v1, Some O10') ->
    store_msg (vp :: nil) O20 act (v2, Some O20') ->
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
  introv Hbe Hsm1 Hsm2 Hgct1 Hgct2 Htpi1 Htpi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  inverts Hsm1.
  inverts Hsm2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  unfold dom_cur_tsk in *.
  simpljoin.
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  match goal with
    H: task_prio_id O10 ?x t1 |- _ => assert (Htpi1_: task_prio_id O1 x t1)
  end.
  eapply tpi_frm_extend; eauto.
  match goal with
    H: task_prio_id O20 ?x t2 |- _ => assert (Htpi2_: task_prio_id O2 x t2)
  end.
  eapply tpi_frm_extend; eauto.
  apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
  apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
  unfold bufs_equiv in *.
  destruct Hbe as (Hie & Hoe).
  split.
  - (* ibufs_equiv *)
    unfolds.
    kvext_h Hjo1' ibufsid O1'.
    kvext_h Hjo2' ibufsid O2'.
    do 2 eexists.
    split; eauto.
    split; eauto.
    casetac (dom_for_prio pr) td Ht Hf.
    +
      subst.
      do 2 rewrite upd_bufmp_get_eq.
      kvext O10 ibufsid O1.
      kvext O20 ibufsid O2.
      unfolds in Hie.
      simpljoin.
      l_rew12_inv2 (get O1 ibufsid).
      l_rew12_inv2 (get O2 ibufsid).
      match goal with H1: get O10 ibufsid = Some (ibufs ?x1) |- _ => rename x1 into ibmp1 end.
      match goal with H2: get O20 ibufsid = Some (ibufs ?x2) |- _ => rename x2 into ibmp2 end.
      match goal with
        H0: ibmp1 (_) = ibmp2 (_), H1: ibmp1 _ = _ :: _ , H2: ibmp2 _  = _ :: _ |- _ =>
          rewrite H1 in H0; rewrite H2 in H0; inverts H0
      end.
      auto.
    +
      rewrite upd_bufmp_get_neq; auto.
      rewrite upd_bufmp_get_neq; auto.
      kvext O10 ibufsid O1.
      kvext O20 ibufsid O2.
      unfolds in Hie.
      simpljoin.
      l_rew12_inv2 (get O1 ibufsid).
      l_rew12_inv2 (get O2 ibufsid).
      auto.
      
  - (* obufs_equiv *)
    assert (Hgobe1: get O1 obufsid = get O1' obufsid).
    {
      lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
      repeat rewsimp; eauto. 
    }
    assert (Hgobe2: get O2 obufsid = get O2' obufsid).
    {
      lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
      repeat rewsimp; eauto.
    }
    unfolds.
    rewrite <- Hgobe1. rewrite <- Hgobe2.
    unfolds in Hoe.
    tauto.
Qed.

Lemma store_msg_same_mqattr:  
  forall vp O act v' O' O0 O0' Of, 
    store_msg (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O absmqattrid = get O' absmqattrid. 
Proof.
  introv Hsm Hjo Hjo'.
  inverts Hsm.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto. 
  repeat rewsimp. 
  auto.
Qed.

Lemma store_msg_mq_ecbs_preserve: 
  forall v O v' O' O0 O0' Of act, 
    store_msg (v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ecbs_preserved O O'. 
Proof.
  introv Hsm Hjo Hjo'.
  unfolds in Hsm.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hgecbeq: get O absecblsid = get O' absecblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  rewrite Hget in Hgecbeq.
  rewrite Hget' in Hgecbeq.
  inverts Hgecbeq.
  tauto.
Qed.

Lemma store_msg_cpid_same: 
  forall vp O act v' O' O0 O0' Of, 
    store_msg (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid.      
Proof.
  introv Hsm Hjo Hjo'.
  inverts Hsm.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  repeat rewsimp. auto.
Qed.   

Lemma store_msg_mqptr_impl:  
  forall vp O act v' O' O0 O0' Of, 
    store_msg (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hsm Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  inverts Hsm. 
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

Lemma store_msg_mqptr_iff:  
  forall vp O act v' O' O0 O0' Of, 
    store_msg (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hsm Hjo Hjo'.
  intros.
  split.
  - introv Hmqp'.
    eapply store_msg_mqptr_impl; eauto.
  - introv Hmqp.
    unfold mq_ptr in *.
    inverts Hsm. 
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

Lemma ports_equiv_store_msg_preserve2:
  forall td O1 O2 vp O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr t1 t2, 
    ports_equiv td O1 O2 ->
    (* kernel_task_equiv td O1 O2 ->  *)
    bufs_equiv (dom_for_prio pr) O1 O2 -> 
    store_msg (vp :: nil) O10 act (v1, Some O10') ->
    store_msg (vp :: nil) O20 act (v2, Some O20') ->
    prt_indom vp O1 pr ->
    (* ports_equiv (dom_for_prio pr) O1 O2 -> *)
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
  introv Hpe Hbe Hsm1 Hsm2 Hpi Hgct1 Hgct2 Htpi1 Htpi2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold ports_equiv in *.
  lets Hpp1: store_msg_prio_preserved Hsm1 Hjo1 Hjo1'; eauto.
  lets Hpp2: store_msg_prio_preserved Hsm2 Hjo2 Hjo2'; eauto. 
  inverts Hsm1.
  inverts Hsm2.
  simpljoin.
  do 2 match goal with H: Some _ = Some _ |- _ => inverts H end.
  do 2 match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  kvext_h Hjo1' osdomainportid O1'.
  kvext_h Hjo2' osdomainportid O2'.
  assert (Hgeq1: get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp; eauto. 
  }
  assert (Hgeq2: get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp; eauto. 
  }
  match goal with
    H1: ?t = _, Hgeq1: ?t = _ |- _ => rewrite H1 in Hgeq1
  end.
  match goal with
    H1: ?t = _, Hgeq2: ?t = _ |- _ => rewrite H1 in Hgeq2
  end.
  symmetry in Hgeq1. symmetry in Hgeq2.
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hid.
  split.
  -
    match type of Hpi with context [Vptr ?x] => rename x into a0 end.
    casetac a0 a Ht Hf.
    +
      subst.
      rewrite set_a_get_a. rewrite set_a_get_a.
      kvext O10 osdomainportid O1.
      kvext O20 osdomainportid O2.
      l_rew12_inv2 (get O1 osdomainportid).
      l_rew12_inv2 (get O2 osdomainportid).
      match goal with H: forall _, _ -> _ |- _ => specialize (H _ Hid); rename H into Hpeq end.
      destruct Hpeq as (Hdpeq & Hpecbeq).
      match goal with
        Hdpeq: ?t1 = ?t2, H1: ?t1 = Some _, H2: ?t2 = Some _ |- _ =>
          rewrite H1 in Hdpeq; rewrite H2 in Hdpeq; inverts Hdpeq
      end.
      kvext O10 ibufsid O1.
      kvext O20 ibufsid O2.
      unfold dom_cur_tsk in *.
      simpljoin.
      kvext O10 curtid O1.
      kvext O20 curtid O2.
      l_rew21_inv1 (get O1 curtid).
      l_rew21_inv1 (get O2 curtid).
      match goal with
        H: task_prio_id O10 ?x t1 |- _ => assert (Htpi1_: task_prio_id O1 x t1)
      end.
      eapply tpi_frm_extend; eauto.
      match goal with
        H: task_prio_id O20 ?x t2 |- _ => assert (Htpi2_: task_prio_id O2 x t2)
      end.
      eapply tpi_frm_extend; eauto.
      apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
      apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
      unfold bufs_equiv in *.
      destruct Hbe as (Hibeq & _).
      unfold ibufs_equiv in *.
      simpljoin.
      l_rew21_inv1 (get O1 ibufsid).
      l_rew21_inv1 (get O2 ibufsid).
      match goal with
        H: ?t1 = ?t2, H1: ?t1 = _ :: _, H2: ?t2 = _ :: _ |- _ =>
          rewrite H1 in H; rewrite H2 in H; inverts H
      end.
      auto.
    +
      rewrite set_a_get_a'; eauto.
      rewrite set_a_get_a'; eauto.
      kvext O10 osdomainportid O1.
      kvext O20 osdomainportid O2.
      l_rew21_inv1 (get O1 osdomainportid).
      l_rew21_inv1 (get O2 osdomainportid).
      match goal with
        H: forall _, _->_ |- _ =>
          specialize (H _ Hid); rename H into Hpeq
      end.
      destruct Hpeq.
      auto.
  -
    split.
    + 
      match goal with
        H: forall _, _->_ |- _ =>
          specialize (H _ Hid); rename H into Hpeq
      end.
      simpljoin.
      auto.
    +
    match goal with
      H: forall _, _->_ |- _ =>
        specialize (H _ Hid); rename H into Hpeq
    end.
    destruct Hpeq as (_ & _ & Hecbeq).
    introv Hge1 Hge2.
    lets H__: Hecbeq Hge1 Hge2.
    eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma buffer_equiv_q_store_msg_preserve2:
  forall vp O10 O20 O10' O20' O1 O2 act v1 v2 td Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    store_msg (vp :: nil) O10 act (v1, Some O10') -> 
    store_msg (vp :: nil) O20 act (v2, Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hsm1 Hsm2 Hjo1' Hjo2'. 
  lets Hpp1: store_msg_prio_preserved Hsm1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: store_msg_prio_preserved Hsm2; eauto.
  specializes Hpp2; eauto.
  inverts Hsm1.
  inverts Hsm2.
  simpljoin.
  do 2 inv_some.
  do 2 inv_lst.
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  assert (Heq1: get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp; auto. 
  }
  assert (Heq2: get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp; auto. 
  }
  eapply buffer_equiv_same_els_preserve2; eauto. 
Qed.         
    
Lemma store_msg_dteq_preserve2:
  forall (td : taskdom) (cst1 cst2 : clientst) (O1 O2 : osabst) 
         (pr : priority) (vp : val) (v1 v2 : option val)
         (O10 O20 O10' O20' O1' O2' : osabst) (act : action) (Of1 Of2 : osabst)
         (t1 t2 : addrval), 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 ->
    ports_equiv (dom_for_prio pr) O1 O2 ->
    bufs_equiv (dom_for_prio pr) O1 O2 ->
    prt_indom vp O1 pr ->
    prt_indom vp O2 pr ->
    store_msg (vp :: nil) O10 act (v1, Some O10') ->
    store_msg (vp :: nil) O20 act (v2, Some O20') ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof. 
  introv Hde Hkte Hpe Hbe Hpi1 Hpi2 Hsm1 Hsm2. 
  introv Hgc1 Hgc2 Htpi1 Htpi2 Hdi1 Hdi2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'. 
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hce & Hbe_ & Hkde & Hcde).
  splits.
  -
    (* ctid_equiv *)
    lets H__: store_msg_ctid_equiv_preserve2 Hjo1 Hjo2; eauto.
  -
    (* bufs_equiv *)        
    lets H__: strore_msg_bufs_equiv_preserve2 Hbe_ Hjo1 Hjo2; eauto.
  -
    (* kernel_data_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte_ & Hkme_ & Hpe_ & Hbfe & Hce_).
    splits.
    + (* kernel_task_equiv *)    
      eapply knl_tsk_equiv_same_tls_preserve2; eauto.
      lets H__: store_msg_tls_same Hjo1 Hjo1'; eauto.
      lets H__: store_msg_tls_same Hjo2 Hjo2'; eauto.
    + (* kernel_mq_equiv *)
      eapply knl_mq_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto. 
      lets H__: store_msg_same_mqattr Hjo1 Hjo1'; eauto. 
      lets H__: store_msg_same_mqattr Hjo2 Hjo2'; eauto.  
      lets H__: store_msg_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: store_msg_prio_preserved Hjo2 Hjo2'; eauto. 
      lets H__: store_msg_mq_ecbs_preserve Hjo1 Hjo1'; eauto.
      lets H__: store_msg_mq_ecbs_preserve Hjo2 Hjo2'; eauto.
    + (* ports_equiv *)
      (* lets H__: ports_equiv_send_to_domain_preserve2 Hoec Hpe_ Hkte_ Hbe_; eauto.  *)
      lets H__: ports_equiv_store_msg_preserve2 Hpe_ Hjo1 Hjo2 Hjo1' Hjo2'; eauto. 
    + (* buffer_equiv *)      
      eapply buffer_equiv_q_store_msg_preserve2; eauto.
    + (* cap_equiv *)
      eapply cap_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto.
      lets H__: store_msg_cpid_same Hjo1 Hjo1'; eauto. 
      lets H__: store_msg_cpid_same Hjo2 Hjo2'; eauto. 
      lets H__: store_msg_mqptr_iff Hjo1 Hjo1'; eauto. 
      lets H__: store_msg_mqptr_iff Hjo2 Hjo2'; eauto. 
  -
    (* client_data_equiv *)
    eapply cde_prio_preserved_preserve2; eauto. 
    lets H__: store_msg_prio_preserved Hjo1 Hjo1'; eauto. 
    lets H__: store_msg_prio_preserved Hjo2 Hjo2'; eauto. 
    
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

Ltac solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 k :=
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



Lemma hidapistep_hidapistep_qprtpost_lemma:
  forall (pc0 : progunit) (pr pr0 : priority) (t1 t2 : addrval) (T1 T2 : tasks)
  (cst1' cst2' : clientst) (O1 O2 O1' O2' : osabst) (act : action) (cd1 cd2 : spec_code)
  (cd' cd'0: spec_code) (i : taskdom) (ks0 ks1 ks1_: stmtcont) (ke0 : exprcont) 
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
  (Hbufe : bufs_equiv (dom_for_prio pr) O1 O2)
  (Hkprte : kernel_data_equiv (dom_for_prio pr) O1 O2)
  (Hprte : client_data_equiv (dom_for_prio pr) cst1' cst2' O1 O2)
  (Hkqe : kernel_task_equiv (dom_for_prio pr) O1 O2)
  (Hkte : kernel_mq_equiv (dom_for_prio pr) O1 O2)
  (Hpde : ports_equiv (dom_for_prio pr) O1 O2)
  (* (Hkde : kports_equiv (dom_for_prio pr) O1 O2) *)
  (Hctide_ : ctid_equiv (dom_for_prio pr) O1 O2)
  (* (H2 : hapistep (api_spec, int_spec, get_hprio_d) (curs (hapi_code cd2), (ke0, ks1)) O2 *)
  (*        (curs (hapi_code cd'0), (ke0, ks1)) O2' act) *)
  (H : spec_step get_hprio_d cd1 O1 cd' O1' act)
  (Hcpe : cap_equiv (dom_for_prio pr) O1 O2)
  (H0 : spec_step get_hprio_d cd2 O2 cd'0 O2' act)
  (Hhsat1 : head_asrt_sat pr cd1 O1)
  (Hhsat2 : head_asrt_sat pr cd2 O2)
  (Hvleq : vl_equiv cd1 cd2)
  (Hnex : ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2))
  (Hpost : qprtpost_equiv cd1 cd2)
  (Hcont : cont_equiv pr ks1_ ks1 O1 O2)
  (HC2 : get T2 t2 = Some (curs (hapi_code cd2), (ke0, ks1))),
    
    code_equiv_tskd i (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_)))
      (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))) O1' O2' /\
      data_equiv_tskd i cst1' cst2' O1' O2'.

Proof.
  intros.  
  match goal with H: spec_step _ cd1 _ ?cd' _ _ |- _ => rename cd' into cd1'; rename H into Hstep1 end.
  match goal with H: spec_step _ cd2 _ ?cd' _ _ |- _ => rename cd' into cd2'; rename H into Hstep2 end.  
  
  unfolds in Hpost. 
  destruct Hpost as (vl & vl1 & vl2 & k & Hlenvl & Hlenvl1 & Hlenvl2 & Hnth1 & Hnth2).
  do 2 try destruct vl; tryfalse.
  do 3 try destruct vl1; tryfalse.
  do 3 try destruct vl2; tryfalse.
  simpl in Hnth1. 
  destruct v0; simpl in Hnth1;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).  
  simpl in Hnth2.
  destruct v2; simpl in Hnth2; 
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
      H: has_no_cap_prtpost _ |- _ => lets H__: cpe_no_prtpost_cap_impl
    end. 
    specializes H__; eauto. 
    false. 
  }
  {
    match goal with
      H: has_no_cap_prtpost _ |- _ => lets H__: cpe_no_prtpost_cap_impl
    end. 
    specializes H__; eauto. 
    false.     
  }
  {
    split; auto.
    (* code_equiv *)
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.    
    unfolds.
    right.
    do 2 eexists.
    split; eauto.
    split; eauto. 

    split. simpl. 
    split. (* unfolds. *)
    match goal with
      H: _ = Vnull \/ port_indomainport v O0 |- _ =>
        destruct H; [subst; auto | right; eapply port_indomainport_frm_preserve; eauto]
    end. 
                   
    eapply ceq_nnocap_hascap; eauto.       
    
    split. simpl.
    split. unfolds. 
    match goal with
      H: _ = Vnull \/ port_indomainport v O |- _ =>
        destruct H; [subst; auto | right; eapply port_indomainport_frm_preserve; eauto]
    end.
    apply cap_equiv_sym in Hcpe.
    eapply ceq_nnocap_hascap; eauto. 
    
    split. 
    eapply vl_equiv_nil; eauto.
    unfolds.
    right.
    split. introv Hf; simpljoin; tryfalse.
    right; right; right; left. 
    (* qprtpost_equiv *)
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 1%nat.         
  }

  destruct k. 
  (* k=1 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
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
    simpl in Hhsat1.
    simpl in Hhsat2.    
    destruct Hhsat1; destruct Hhsat2.
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr). 
    apply ports_equiv_sym in Hpde.
    lets H__: prts_equiv_orcond_impl Hpde. 
    specializes H__; eauto.
    false.
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.    
    destruct Hhsat1; destruct Hhsat2.
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    apply ports_equiv_sym in Hpde.
    lets H__: prts_equiv_orcond_impl Hpde. 
    specializes H__; eauto.
    false.    
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.    
    destruct Hhsat1; destruct Hhsat2.
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    apply ports_equiv_sym in Hpde.
    lets H__: prts_equiv_orcond_impl Hpde. 
    specializes H__; eauto.
    false.    
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.    
    destruct Hhsat1; destruct Hhsat2.
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    lets H__: prts_equiv_orcond_impl Hpde. 
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
    apply ports_equiv_sym in Hpde.
    lets H__: prte_port_type_impl Hnwd Hpde; eauto. 
    specializes H__; eauto.
    false.
  }
  {
    lets Hnwd: ncond_dest_wd O2.
    specializes Hnwd; eauto. 
    apply ports_equiv_sym in Hpde.
    lets H__: prte_port_type_impl Hnwd Hpde; eauto. 
    specializes H__; eauto.
    false.
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.    
    destruct Hhsat1; destruct Hhsat2.
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    lets H__: prts_equiv_orcond_impl Hpde. 
    specializes H__; eauto.
    false.    
  }
  {
    lets Hnwd: ncond_dest_wd O1.
    specializes Hnwd; eauto. 
    lets H__: prte_port_type_impl Hnwd Hpde; eauto. 
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
    apply ports_equiv_sym in Hpde.
    specializes Hnwd; eauto. 
    lets H__: prte_prtid_invalid_impl Hnwd Hpde; eauto. 
    specializes H__; eauto.
    false.
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.    
    destruct Hhsat1; destruct Hhsat2.
    assert (Hptr: exists a, v = Vptr a) by (eapply has_port_ptr; eauto). 
    destruct Hptr as (a & Hptr).
    lets H__: prts_equiv_orcond_impl Hpde. 
    specializes H__; eauto.
    false.        
  }
  {
    lets Hnwd: ncond_dest_wd O1.
    specializes Hnwd; eauto. 
    lets H__: prte_port_type_impl Hnwd Hpde; eauto. 
    specializes H__; eauto.
    false.    
  }  
  {    
    lets Hnwd: ncond_dest_wd O1.
    specializes Hnwd; eauto. 
    lets H__: prte_prtid_invalid_impl Hnwd Hpde; eauto. 
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
    destruct Hhsat1. 
    split; [eapply nwd_prt_indom; eauto | auto].
    split. simpl.
    destruct Hhsat2.
    split; [eapply nwd_prt_indom; eauto | auto].
    split.
    eapply vl_equiv_nil; eauto.
    unfolds. right. split. introv Hf; simpljoin; tryfalse.
    right. right. right. left. 
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 2%nat. 
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
    destruct Hhsat2.
    apply obsr_equiv_chnd_sym in Htmeq. 
    apply ports_equiv_sym in Hpde.
    lets H__: cheq_no_chan_impl Htmeq Hpde; eauto. 
    specializes H__; eauto. 
    false. 
  }
  {
    destruct Hhsat2.
    apply obsr_equiv_chnd_sym in Htmeq. 
    apply ports_equiv_sym in Hpde.
    lets H__: cheq_no_chan_impl Htmeq Hpde; eauto. 
    specializes H__; eauto. 
    false.     
  }  
  {
    destruct Hhsat1.
    lets H__: cheq_no_chan_impl Htmeq Hpde; eauto. 
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
    right; right; right; left.
    (* qprtpost_equiv *)
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 4%nat.      
  }
  {
    destruct Hhsat1.
    lets H__: cheq_intercore_impl Hpde; eauto. 
    specializes H__; eauto. 
    false.
  }
  {
    destruct Hhsat1.
    lets H__: cheq_no_chan_impl Htmeq Hpde; eauto. 
    specializes H__; eauto. 
    false.         
  }
  {
    destruct Hhsat2.
    apply ports_equiv_sym in Hpde.
    apply obsr_equiv_chnd_sym in Htmeq. 
    lets H__: cheq_intercore_impl Hpde; eauto. 
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
    destruct Hhsat1.
    destruct Hhsat2.
    split. simpl. auto.
    split. simpl. auto.
    split. eapply veq_vlequiv; eauto. 
    simpl. eauto. simpl. eauto.
    unfolds.
    right. split. introv Hf; simpljoin; tryfalse.
    right. right. right. left.
    (* qprtpost_equiv *)
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 3%nat. 
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
    right. right. right. left.
    (* qprtpost_equiv *)
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 4%nat.     
  }
  {
    unfolds in Hvleq.
    specialize (Hvleq (v1::nil) (Vint32 Int.zero::nil)).
    simpl in Hvleq.
    specialize (Hvleq eq_refl eq_refl (0%nat)).
    simpl in Hvleq.
    specializes Hvleq; eauto.
    false. 
  }
  {
    unfolds in Hvleq.
    specialize (Hvleq (Vint32 Int.zero::nil) (v3::nil)).
    simpl in Hvleq.
    specialize (Hvleq eq_refl eq_refl (0%nat)).
    simpl in Hvleq.
    specializes Hvleq; eauto.
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
    right. right. right. left.
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 4%nat.  
  }

  destruct k. 
  (* k=4 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  simpl in Hhsat1.
  simpl in Hhsat2.
  symexe.
  {
    split. 
    (* code_equiv *)
    lets Hpp1: q_send_to_domain_prio_preserved O1 O1' O0 O'0; eauto.
    specializes Hpp1; eauto.
    lets Hpp2: q_send_to_domain_prio_preserved O2 O2' O O'; eauto.
    specializes Hpp2; eauto.
    apply11 q_send_to_domain q_send_to_domain q_send_to_domain_cpid_same Hcpeq2 Hcpeq1.
    specializes Hcpeq1; eauto.
    specializes Hcpeq2; eauto. 
    eapply code_equiv_upd2_preserve_st'; eauto.
    {
      (* cmd_equiv *)
      destruct Hhsat1; destruct Hhsat2.
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
      right; right; right; left.
      (* qprtpost_equiv *)
      solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 5%nat. 
    }
    eapply cont_equiv_qref_preserve; eauto. 
    eapply q_send_to_domain_mqref_preserve; eauto.
    eapply q_send_to_domain_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply q_send_to_domain_qprt_preserve; eauto.
    eapply q_send_to_domain_qprt_preserve with (O0:=O) (O0':=O'); eauto.
    eapply eqdom_frm_domimpl; eauto. 
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    lets H__: code_equiv_hsat_neq_st'; eauto. 
    eapply H__; eauto.
    eapply q_send_to_domain_mqref_preserve; eauto.
    eapply q_send_to_domain_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply q_send_to_domain_qprt_preserve; eauto.
    eapply q_send_to_domain_qprt_preserve with (O0:=O) (O0':=O'); eauto.              
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    (* data_equiv_tskd *)
    destruct Hhsat1; destruct Hhsat2.
    eapply q_send_to_domain_dteq_preserve2 
      with (O10:=O0) (O10':=O'0) (O20:=O) (O20':=O'); eauto.
    eapply eqdom_frm_domimpl with (O10:=O0) (O20:=O'0); eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
  }  
  {
    destruct Hhsat2.
    apply obsr_equiv_chnd_sym in Htmeq.
    apply ports_equiv_sym in Hpde.
    lets H__: prteq_cheq_dst_ports_impl Hpde; eauto. 
    specializes H__; eauto.
    false. 
  }
  {
    destruct Hhsat2.
    apply obsr_equiv_chnd_sym in Htmeq.
    apply ports_equiv_sym in Hpde.
    lets H__: prteq_cheq_dst_ports_impl Hpde; eauto. 
    specializes H__; eauto.
    false.     
  }
  {
    destruct Hhsat2.
    apply obsr_equiv_chnd_sym in Htmeq.
    apply ports_equiv_sym in Hpde.
    lets H__: prteq_cheq_dst_ports_impl Hpde; eauto. 
    specializes H__; eauto.
    false.     
  }
  {
    destruct Hhsat1.
    lets H__: prteq_cheq_dst_ports_impl Hpde; eauto. 
    specializes H__; eauto.
    false.     
  }
  {
    (* store_msg *)    
    split. 
    (* code_equiv *)
    lets Hpp1: store_msg_prio_preserved O1 O1' Of0 O0 O'0; eauto.
    specializes Hpp1; eauto.
    lets Hpp2: store_msg_prio_preserved O2 O2' Of O O'; eauto.
    specializes Hpp2; eauto. 
    apply11 store_msg store_msg store_msg_cpid_same Hcpeq2 Hcpeq1.
    specializes Hcpeq1; eauto.
    specializes Hcpeq2; eauto. 

    eapply code_equiv_upd2_preserve_st'; eauto.
    {
      (* cmd_equiv *)
      destruct Hhsat1; destruct Hhsat2.
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
      right; right; right; left.
      (* qprtpost_equiv *)
      solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 8%nat. 
    }
    eapply cont_equiv_qref_preserve; eauto. 
    eapply store_msg_mqref_preserve; eauto.
    eapply store_msg_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    
    eapply store_msg_qprt_preserve; eauto.
    eapply store_msg_qprt_preserve with (O0:=O) (O0':=O'); eauto.
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
    
    lets H__: code_equiv_hsat_neq_st'; eauto. 
    eapply H__; eauto.
    eapply store_msg_mqref_preserve; eauto.
    eapply store_msg_mqref_preserve with (O0:=O) (O0':=O'); eauto.
    eapply store_msg_qprt_preserve; eauto.
    eapply store_msg_qprt_preserve with (O0:=O) (O0':=O'); eauto.              
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    (* data_equiv_tskd *)
    destruct Hhsat1; destruct Hhsat2.
    eapply store_msg_dteq_preserve2
      with (O1:=O1) (O2:=O2) (O10:=O0) (O20:=O) (O10':=O'0) (O20':=O'); eauto. 
    eapply eqdom_frm_domimpl with (O10:=O0) (O20:=O'0); eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
  }  
  {
    destruct Hhsat2.
    apply ports_equiv_sym in Hpde.
    lets H__: prteq_src_prt_nfull_impl Hpde; eauto.
    specializes H__; eauto.
    false. 
  }
  {
    destruct Hhsat2.
    apply ports_equiv_sym in Hpde.
    lets H__: prteq_src_prt_nfull_impl Hpde; eauto.
    specializes H__; eauto.
    false. 
  }
  {
    destruct Hhsat1.
    lets H__: prteq_cheq_dst_ports_impl Hpde; eauto. 
    specializes H__; eauto.
    false.     
  }
  {
    destruct Hhsat1.
    lets H__: prteq_src_prt_nfull_impl Hpde; eauto.
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
    split. simpl. auto.
    split. simpl. auto.
    split. eapply vl_equiv_nil; eauto.
    unfolds.
    right.
    split. introv Hf; simpljoin; tryfalse.
    right; right; right; left.
    (* qprtpost_equiv *)
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 7%nat.       
  }
  {
    destruct Hhsat2.
    apply ports_equiv_sym in Hpde.
    apply obsr_equiv_chnd_sym in Htmeq. 
    lets H__: cheq_intercore_impl Hpde; eauto. 
    specializes H__; eauto. 
    false.    
  }
  {
    destruct Hhsat1.
    lets H__: prteq_cheq_dst_ports_impl Hpde; eauto. 
    specializes H__; eauto.
    false.         
  }
  {
    destruct Hhsat1.
    lets H__: prteq_src_prt_nfull_impl Hpde; eauto.
    specializes H__; eauto.
    false.     
  }
  {
    destruct Hhsat1.
    lets H__: cheq_intercore_impl Hpde; eauto. 
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
    right. right. right. left.
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 7%nat.      
  }
  
  destruct k.
  (* k=5 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  unfold conditional_semrel in Hstep1.
  unfold conditional_semrel in Hstep2.
  symexe.
   
  {
    simpl in Hhsat1.
    simpl in Hhsat2.
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
    right. right. right. left.
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 6%nat.      
  }
  {    
    apply ports_equiv_sym in Hpde.
    apply obsr_equiv_chnd_sym in Htmeq.
    lets H__: cheq_intercore_impl Hhsat2; eauto.
    specializes H__; eauto.
    false.
  }
  {
    lets H__: cheq_intercore_impl Hhsat1; eauto.
    specializes H__; eauto.
    false.
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.
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
    right. right. right. left.
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 6%nat.          
  }

  destruct k.
  (* k=6 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  symexe.
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
    right. right. right. left.
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 7%nat.           
  }

  destruct k.
  (* k=7 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  symexe.
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    apply cmd_equiv_end. 
  }

  destruct k.
  (* k=8 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  symexe.
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
    right. right. right. left.
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 7%nat.     
  }
  {
    apply ports_equiv_sym in Hpde.
    apply obsr_equiv_chnd_sym in Htmeq.
    lets H__: cheq_intercore_impl Hhsat2; eauto.
    specializes H__; eauto.
    false.
  }
  {
    lets H__: cheq_intercore_impl Hhsat1; eauto.
    specializes H__; eauto.
    false.
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.
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
    right. right. right. left.
    solve_prtpost_equiv Hlenvl Hlenvl1 Hlenvl2 7%nat.          
  }

  destruct k.
  (* k=9 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  symexe.
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    apply cmd_equiv_end.     
  }

  destruct k.
  (* k=10 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2. 
  symexe.
  {
    apply11 ret_val ret_val rv_Oeq H1_ H2_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    specializes H__; eauto.
    apply11 ret_val ret_val rv_veq H1_ H2_.
    subst. 
    apply cmd_equiv_end.         
  }

  simpl in Hnth2.
  rewrite nth_error_nil in Hnth2.
  false. 
Qed. 
