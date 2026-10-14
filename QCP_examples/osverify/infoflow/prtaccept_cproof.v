
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
Require Import ct_pp_lemmas.

Require Import mqrecv_lemmas. 
Require Import ports_cproof_common. 

Set Keyed Unification. 

Lemma obsr_equiv_tskd_upd2_preserve'_lemma:
  forall td pr T1 T2 t1 t2 O1 O2 c1 c2 cd1 cd2
      ke ks1 ks2 vl vl1 vl2 cst1 cst2, 
    bind_all vl vl1 vl2 cd1 cd2 ->
    code_equiv_tskd td T1 T2 O1 O2 ->
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    get T1 t1 = Some (c1, (ke, ks1)) ->
    get T2 t2 = Some (c2, (ke, ks2)) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    cont_equiv pr ks1 ks2 O1 O2 ->
    head_asrt_sat pr cd1 O1 ->
    head_asrt_sat pr cd2 O2 ->
    vl_equiv cd1 cd2 ->
    ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2) ->
    length vl = 1%nat ->
    length vl1 = 2%nat ->
    length vl2 = 2%nat ->
    (exists k, 
      nth_error (get_all_succs (portaccept (vl ++ vl1))) k = Some cd1 /\
      nth_error (get_all_succs (portaccept (vl ++ vl2))) k = Some cd2) ->
    code_equiv_tskd td (set T1 t1 (curs (hapi_code cd1), (ke, ks1))) 
      (set T2 t2 (curs (hapi_code cd2), (ke, ks2))) O1 O2 /\
      data_equiv_tskd td cst1 cst2 O1 O2. 
Proof.
  split.
  - eapply code_equiv_upd2_preserve'; eauto.
    right; do 2 eexists. splits; auto.
    right; split.
    + auto.
    + right; right; right; right; right; right; left.
      destruct H14 as (k & Hnth1 & Hnth2).
      exists vl vl1 vl2 k.
      splits; auto.
  - auto.
Qed.

Ltac obsr_equiv_tskd_upd2_preserve' k :=
  join_Oeq;
  match goal with H: bind_all ?vl ?vl1 ?vl2 ?cd1 ?cd2 |- _ => 
    assert (exists k', 
      nth_error (get_all_succs (portaccept (vl ++ vl1))) k' = Some cd1 /\
      nth_error (get_all_succs (portaccept (vl ++ vl2))) k' = Some cd2 )
    by (exists k; splits; auto 20)
  end;
  eapply obsr_equiv_tskd_upd2_preserve'_lemma; simpl; eauto.

Lemma prt_indom_has_port:
  forall v O0 Of O pr, 
    join O0 Of O -> 
    v = Vnull \/ port_indomainport v O0 -> 
    has_port v O pr. 
Proof.
  introv Hjo Hv.
  unfolds.
  destruct Hv.
  left; auto.
  right.
  eapply port_indomainport_frm_preserve; eauto. 
Qed. 

Lemma cpe_no_prtaccept_cap_impl:   
  forall pr t1 t2 O1 O2, 
    cap_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    has_no_cap_prtaccept O1 ->
    has_no_cap_prtaccept O2.
Proof.
  introv Hce Hct1 Hct2 Htpi1 Htpi2 Hncp.
  unfold cap_equiv in Hce.
  unfold has_no_cap_prtaccept in *.
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

Lemma cpe_no_prtaccept_cap_impl_f:   
  forall pr t1 t2 O1 O2, 
    has_no_cap_prtaccept O1 ->
    ~has_no_cap_prtaccept O2 ->
    cap_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    False.
Proof.
  introv Hnc Hnnc Hce Hct1 Hct2 Htpi1 Htpi2.
  lets H__: cpe_no_prtaccept_cap_impl Hce; eauto.
Qed. 

Lemma prts_equiv_orcond_impl_f :
  forall pr O1 O2 vprt t1 t2, 
    (not_port O1 vprt \/ wrong_core O1 vprt \/ wrong_dom O1 vprt) ->
    ~(not_port O2 vprt \/ wrong_core O2 vprt \/ wrong_dom O2 vprt) -> 
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    has_port vprt O1 pr ->
    has_port vprt O2 pr ->        
    vprt <> Vnull -> 
    False.
Proof.
  introv Hor Hnor Hpe Hg1 Hg2 Htpi1 Htpi2 Hhp1 Hhp2 Hnn.
  assert (exists a, vprt = Vptr a).
  {
    unfolds in Hhp1.
    destruct Hhp1; subst.
    false.
    unfold port_indomainport in *.
    destruct vprt; tryfalse. 
    eexists; eauto. 
  }
  simpljoin. 
  lets H__: prts_equiv_orcond_impl Hpe; eauto. 
Qed. 
    
Lemma prte_port_type_impl_f:
  forall O1 O2 v pr t1, 
    (exists a dpl pcn pd pid pst pin pout pt,
        v = Vptr a /\
          get O1 osdomainportid = Some (osdomainport dpl) /\
          get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, pt)) ->
    (~(exists a dpl pcn pd pid pst pin pout pt,
           v = Vptr a /\
             get O2 osdomainportid = Some (osdomainport dpl) /\
             get dpl a = Some (pcn, pd, pid, SourceP, pst, pin, pout, pt))) ->
    ~wrong_dom O1 v ->
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    get O1 curtid = Some (oscurt t1) ->
    task_prio_id O1 pr t1 ->
    False. 
Proof.
  introv Hex Hnex Hnnd Hpe Hg1 Htpi1.
  simpljoin.
  eapply nwrong_dom_dest in Hnnd; eauto.
  unfolds in Hpe.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  match goal with
    H: forall _, _ -> _ |- _ => lets H__: H Hnnd
  end.
  destruct H__ as (Hprteq & _).
  match goal with
    H1: ?t1 = Some _, H2: ?t1' = _ |- _ => unify t1 t1'; rewrite H1 in H2
  end.
  apply Hnex.
  do 9 eexists.
  splits; eauto. 
Qed. 

Lemma cheq_no_chan_impl_f:
  forall O1 O2 v pr,
    no_channel O1 v ->
    ~no_channel O2 v ->     
    prt_indom v O1 pr -> 
    obsr_equiv_chnd O1 O2 ->
    ports_equiv (dom_for_prio pr) O1 O2 ->
    False.
Proof. 
  introv Hnc1 Hnnc2 Hpi Hoe Hpe.
  lets H__: cheq_no_chan_impl Hpe; eauto.
Qed. 

Lemma cheq_intercore_impl_f: 
  forall O1 O2 v pr, 
    (exists a, v = Vptr a /\ is_intercore O1 a) ->
    ~(exists a, v = Vptr a /\ is_intercore O2 a) -> 
    prt_indom v O1 pr -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    obsr_equiv_chnd O1 O2 -> 
    False. 
Proof.
  introv Hex Hnex Hpi Hpe Hoe.
  lets H__: cheq_intercore_impl Hpe; eauto.
Qed.   

Lemma receive_port_msg_prio_preserved:
  forall v O O' act v' O0 O0' Of, 
    join O0 Of O ->
    join O0' Of O' -> 
    receive_port_msg (v :: nil) O0 act (v', Some O0') -> 
    prio_preserved O O'. 
Proof.
  introv Hjo Hjo' Hrpm. 
  unfolds. intros. unfolds.
  introv Hd.
  unfolds in Hrpm.
  simpljoin.
  inv_some.
  inv_lst.
  assert (Hgteq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto. 
  }
  unfold task_prio_id.
  rewrite <- Hgteq.
  tauto.
Qed. 

Lemma receive_port_msg_cpid_same:
  forall vp O act v' O' O0 O0' Of, 
    receive_port_msg (vp :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    get O cspaceid = get O' cspaceid.      
Proof.
  introv Hrpm Hjo Hjo'.
  inverts Hrpm.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  repeat rewsimp. auto.
Qed.   

Lemma receive_port_msg_mqref_preserve: 
  forall v v0 O O' O0 O0' Of act, 
    join O0 Of O ->
    join O0' Of O' -> 
    receive_port_msg (v :: nil) O0 act (v0, Some O0') -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hjo Hjo' Hrcv.
  unfolds in Hrcv.
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

Lemma receive_port_msg_qprt_preserve: 
  forall v O v' O' O0 O0' Of act, 
    join O0 Of O ->
    join O0' Of O' -> 
    receive_port_msg (v :: nil) O0 act (v', Some O0') ->
    qprt_preserved O O'. 
Proof.
  introv Hjo Hjo' Hrcv.
  unfolds in Hrcv.
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
    rem_dis.
    + 
      casetac x a Ht Hf.
      *
        subst.
        rewrite H2 in H5; inverts H5.
        rewrite set_a_get_a.
        do 7 eexists; eauto.
      *
        rewrite set_a_get_a'; eauto.
        do 7 eexists; eauto. 
    +
      do 7 eexists; eauto. 
  -
    assert (get O' osdomainportid = Some (osdomainport dpl)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
Qed.

Lemma receive_port_msg_ctid_equiv_preserve2:
  forall td O1 O2 vp1 vp2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    receive_port_msg (vp1 :: nil) O10 act (v1, Some O10') ->
    receive_port_msg (vp2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hr1 Hr2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets Hpp1: receive_port_msg_prio_preserved Hjo1 Hjo1'; eauto.
  specializes Hpp1; eauto. 
  lets Hpp2: receive_port_msg_prio_preserved Hjo2 Hjo2'; eauto. 
  specializes Hpp2; eauto. 
  unfold ctid_equiv in *.
  unfold receive_port_msg in *.
  simpljoin.
  do 2 inv_some.
  do 2 inv_lst.
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

  lets Htpi1_: prio_preserved_tpi Htpi1' Hpp1.
  lets Htpi2_: prio_preserved_tpi Htpi2' Hpp2.
  lets H__: H19 Htpi1_ Htpi2_ Htd.
  auto.
  
Qed.

Lemma receive_port_msg_bufs_equiv_preserve2:
  forall td O1 O2 vp O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr t1 t2, 
    bufs_equiv td O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    receive_port_msg (vp :: nil) O10 act (v1, Some O10') ->
    receive_port_msg (vp :: nil) O20 act (v2, Some O20') ->
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
  introv Hbfe Hpe Hr1 Hr2 Ht1 Ht2 Htpi1 Htpi2.
  introv Hid Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold bufs_equiv in *.
  destruct Hbfe as (Hibe & Hobe).
  inverts Hr1. inverts Hr2.
  simpljoin.
  do 2 inv_lst.
  do 2 inv_some.
  assert (Hgeq1: get O1' ibufsid = get O1 ibufsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp. auto.     
  }
  assert (Hgeq2: get O2' ibufsid = get O2 ibufsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp. auto.         
  }
  split.
  { (* ibufs_equiv *)
    unfold ibufs_equiv in *.
    destruct Hibe as (ibm1 & ibm2 & Hgim1 & Hgim2 & Hibeq).
    rewrite Hgeq1. rewrite Hgeq2. 
    do 2 eexists.
    split; eauto.
  }
  (* obufs_equiv *)
  unfold obufs_equiv in *.
  destruct Hobe as (obm1 & obm2 & Hgm1 & Hgm2 & Hobeq).
  kvext_h Hjo1' obufsid O1'.
  kvext_h Hjo2' obufsid O2'.
  do 2 eexists.
  split; eauto.
  split; eauto.
  unfolds in Hpe.
  destruct Hpe as (prts1 & prts2 & els1 & els2 & Hgd1 & Hgd2 & Hge1 & Hge2 & Ha).
  unfolds in Hid.
  destruct Hid as (a & Heqptr & Hid).
  inverts Heqptr.
  lets Haa: Ha Hid; eauto.
  destruct Haa as (Hgpeq & Hiff & Ha_).
  kvext O10 osdomainportid O1.
  kvext O20 osdomainportid O2.
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  kvext O10 obufsid O1.
  kvext O20 obufsid O2.
  l_rew21_inv1 (get O1 obufsid).
  l_rew21_inv1 (get O2 obufsid).

  unfold dom_cur_tsk in *.
  simpljoin.
  kvext0 O10 curtid O1. kvext0 O20 curtid O2.
  l_rew21_inv1 (get O1 curtid). l_rew21_inv1 (get O2 curtid).
  
  apply11 (task_prio_id O10) (task_prio_id O20) tpi_frm_ext H1_ H2_.
  specializes H1_; eauto.
  specializes H2_; eauto.
  apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
  apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.

  rewrite H11 in Hgpeq. rewrite H3 in Hgpeq.
  inverts Hgpeq.
  rem_dis; rem_dis.
  -
    match goal with
      H: QueuePort _ _ = QueuePort _ _ |- _ => inverts H
    end.                
    casetac (dom_for_prio pr) td Ht Hf.
    + subst. do 2 rewrite upd_bufmp_get_eq. congruence.
    + do 2 (rewrite upd_bufmp_get_neq; eauto).
  -
    match goal with
      H: SamplePort _ = SamplePort _ |- _ => inverts H
    end.                
    casetac (dom_for_prio pr) td Ht Hf.
    + subst. do 2 rewrite upd_bufmp_get_eq. congruence.
    + do 2 (rewrite upd_bufmp_get_neq; eauto).

Qed.

Lemma receive_port_msg_same_mqattr:  
  forall vp O act v' O' O0 O0' Of, 
    join O0 Of O ->
    join O0' Of O' -> 
    receive_port_msg (vp :: nil) O0 act (v', Some O0') -> 
    get O absmqattrid = get O' absmqattrid. 
Proof.
  introv Hjo Hjo' Hsd.
  inverts Hsd.
  simpljoin.
  match goal with
    H: Some _ = Some _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto. 
  repeat rewsimp. auto.
Qed. 

Lemma receive_port_msg_mq_ecbs_preserve: 
  forall v O v' O' O0 O0' Of act, 
    join O0 Of O ->
    join O0' Of O' -> 
    receive_port_msg (v :: nil) O0 act (v', Some O0') ->
    mq_ecbs_preserved O O'. 
Proof.
  introv Hjo Hjo' Hrc.
  unfolds in Hrc.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Heq: get O absecblsid = get O' absecblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  introv Hge.
  rewrite Hget in Heq.
  rewrite Hget' in Heq.
  inverts Heq. 
  auto.
Qed. 

Lemma buffer_equiv_receive_port_msg_preserve2:
  forall vp O10 O20 O10' O20' O1 O2 act v1 v2 td Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    receive_port_msg (vp :: nil) O10 act (v1, Some O10') -> 
    receive_port_msg (vp :: nil) O20 act (v2, Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hrpm1 Hrpm2 Hjo1' Hjo2'. 
  lets Hpp1: receive_port_msg_prio_preserved Hrpm1; eauto.
  lets Hpp2: receive_port_msg_prio_preserved Hrpm2; eauto.
  inverts Hrpm1.
  inverts Hrpm2.
  simpljoin.
  do 2 inv_some.
  do 2 inv_lst.
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  assert (Hgeq1: get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp; auto. 
  }
  assert (Hgeq2: get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp; auto.         
  }      
  eapply buffer_equiv_nupd_preserve2; eauto.
  congruence.
  congruence. 
Qed.

Lemma receive_port_msg_mqptr_impl:  
  forall vp O act v' O' O0 O0' Of, 
    join O0 Of O ->
    join O0' Of O' -> 
    receive_port_msg (vp :: nil) O0 act (v', Some O0') -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hjo Hjo' Hrc Hmp'.
  unfold mq_ptr in *.
  inverts Hrc.
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

Lemma receive_port_msg_mqptr_iff:  
  forall vp O act v' O' O0 O0' Of, 
    join O0 Of O ->
    join O0' Of O' ->         
    receive_port_msg (vp :: nil) O0 act (v', Some O0') -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hjo Hjo' Hrc.
  intros.
  split.
  - 
    eapply receive_port_msg_mqptr_impl; eauto. 
  -
    introv Hmqp.
    unfold mq_ptr in *.
    inverts Hrc.
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

Lemma ports_equiv_receive_port_msg_preserve2:
  forall td O1 O2 vp O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' pr t1 t2, 
    obsr_equiv_chnd O1 O2 ->    
    ports_equiv td O1 O2 ->
    (* kernel_task_equiv td O1 O2 ->  *)
    receive_port_msg (vp :: nil) O10 act (v1, Some O10') ->
    receive_port_msg (vp :: nil) O20 act (v2, Some O20') ->
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
  introv Hoe Hpe (* Hkte *) Hrc1 Hrc2 Hpi Hpe_. 
  introv Hgct1 Hgct2 Htpi1 Htpi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  lets Hpp1: receive_port_msg_prio_preserved Hrc1; eauto.
  lets Hpp2: receive_port_msg_prio_preserved Hrc2; eauto. 
  assert (Hrc1_ := Hrc1). 
  assert (Hrc2_ := Hrc2). 
  unfolds in Hrc1.
  unfolds in Hrc2.
  assert (Hpe0 := Hpe). 
  unfolds in Hpe.
  simpljoin.
  do 2 inv_some.
  do 2 inv_lst.
  kvext_h Hjo1' osdomainportid O1'.
  kvext_h Hjo2' osdomainportid O2'.
  assert (Heeq1: get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    repeat rewsimp; auto. 
  }
  assert (Heeq2: get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    repeat rewsimp; auto. 
  }
  unfolds in Hoe.
  destruct Hoe as ((Hcne & Hceq) & (Hkne & Hkeq)).
  unfolds.
  rewrite <- Heeq1. rewrite <- Heeq2.

  kvext O10 osdomainportid O1.
  kvext O20 osdomainportid O2.
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  unfolds in Hpe_.
  destruct Hpe_ as (prts1_ & prts2_ & els1_ & els2_ & Hgd1 & Hgd2 & Hge1 & Hge2 & Ha_). 
  match type of Hpi with
    context [Vptr ?x] => rename x into a
  end.
  assert (Haid: addrval_in_dom a (dom_for_prio pr) = true).
  {
    unfolds in Hpi. 
    destruct Hpi as (a_ & Hptreq & Hin).
    inverts Hptreq.
    auto.
  }
  lets H__: Ha_ Haid; eauto.
  destruct H__ as (Hpeq_ & Hiff_ & Hgteqv_).
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  rewrite H12 in Hpeq_. rewrite H4 in Hpeq_.
  inverts Hpeq_.

  do 4 eexists.
  split; eauto. 
  split; eauto.
  split; eauto.
  split; eauto.
  introv Haid'.
  rem_dis; rem_dis.
  -
    match goal with H: QueuePort _ _ = QueuePort _ _ |- _ => inverts H end.
    casetac a a0 Ht Hf.
    +
      subst. do 2 rewrite set_a_get_a.
      splits; auto.
      introv Hge1' Hge2'.
      lets H__: Hgteqv_ Hge1' Hge2'; eauto.
      eapply tidls_equiv_pp_preserve2; eauto.
    +
      do 2 (rewrite set_a_get_a'; eauto).
      l_rew21_inv1 (get O1 absecblsid).
      l_rew21_inv1 (get O2 absecblsid).
      lets Haa: H21 Haid'; eauto.
      destruct Haa as (Hgpeq & Hiff' & Hteq').
      match goal with 
        H: get O1 absecblsid = Some (absecblist ?x) |- _ =>
          assert (Heq1: els1_ = x) by congruence
      end.
      match goal with
        H: get O2 absecblsid = Some (absecblist ?x) |- _ =>
          assert (Heq2: els2_ = x) by congruence
      end.
      subst.
      splits; eauto.
      introv Hgt1' Hgt2'.
      specializes Hteq'; eauto.
      eapply tidls_equiv_pp_preserve2; eauto.
  -
    match goal with H: SamplePort _ = SamplePort _ |- _ => inverts H end.
    lets H__: H21 Haid'; eauto.
    clear Heeq1 Heeq2.
    l_rew21_inv1 (get O1 absecblsid).
    l_rew21_inv1 (get O2 absecblsid).
    destruct H__ as (Hgpeq & Hiff & Hgteq).
    splits; eauto.
    introv Hgt1' Hgt2'.
    specializes Hgteq; eauto.
    eapply tidls_equiv_pp_preserve2; eauto.
Qed.     

Lemma receive_port_msg_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr vp v1 v2 O10 O20 O10' O20' O1' O2' act Of1 Of2 t1 t2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    bufs_equiv (dom_for_prio pr) O1 O2 -> 
    obsr_equiv_chnd O1 O2 -> 
    prt_indom vp O1 pr -> 
    prt_indom vp O2 pr -> 
    receive_port_msg (vp :: nil) O10 act (v1, Some O10') -> 
    receive_port_msg (vp :: nil) O20 act (v2, Some O20') -> 
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
  lets Hpp1: receive_port_msg_prio_preserved Hjo1 Hjo1'; eauto. 
  specializes Hpp1; eauto. 
  lets Hpp2: receive_port_msg_prio_preserved Hjo2 Hjo2'; eauto.
  specializes Hpp2; eauto.
  
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hce & Hbe & Hkde & Hcde).
  splits.
  -
    (*ctid_equiv *)
    lets H__: receive_port_msg_ctid_equiv_preserve2 Hjo1 Hjo2; eauto.
  -
    (* bufs_equiv *)
    clear Hbe_.
    lets H__: receive_port_msg_bufs_equiv_preserve2 Hpi1 Hjo1 Hjo2; eauto.
  -
    (* kernel_data_equiv *)
    unfolds in Hkde.
    destruct Hkde as (Hkte_ & Hkme_ & Hpe'_ & Hbfe_ &  Hce_).
    splits.
    + (* kernel_task_equiv *)
      eapply knl_tsk_equiv_same_tls_preserve2; eauto. 
      {
        inverts Hsend1; inverts Hsend2. 
        simpljoin. do 2 inv_some.
        lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
        repeat rewsimp; auto.
      }
      {
        inverts Hsend1; inverts Hsend2. 
        simpljoin. do 2 inv_some.
        lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
        repeat rewsimp; auto.
      }
    + (* kernel_mq_equiv *)
      eapply knl_mq_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto.
      eapply receive_port_msg_same_mqattr; eauto.
      eapply receive_port_msg_same_mqattr; eauto.
      eapply receive_port_msg_mq_ecbs_preserve; eauto.
      eapply receive_port_msg_mq_ecbs_preserve; eauto. 
    + (* ports_equiv *)
      eapply ports_equiv_receive_port_msg_preserve2
        with (O1:=O1) (O2:=O2) (O10:=O10) (O20:=O20); eauto. 
    + (* buffer_equiv *)
      eapply buffer_equiv_receive_port_msg_preserve2; eauto.
    + (* cap_equiv *) 
      eapply cap_equiv_preserve2 with (O1:=O1) (O2:=O2); eauto.
      lets H__: receive_port_msg_cpid_same Hjo1 Hjo1'; eauto. 
      lets H__: receive_port_msg_cpid_same Hjo2 Hjo2'; eauto. 
      eapply receive_port_msg_mqptr_iff; eauto.
      eapply receive_port_msg_mqptr_iff; eauto. 
  - (* client_data_equiv *) 
    eapply cde_prio_preserved_preserve2; eauto. 
Qed.
    
Ltac unwrap :=
  match goal with
    H1: context [Step1], H2: context [Step2] |- _ => unfolds in H1; unfolds in H2
  end.

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
  | H1: join ?O01 ?Of1 ?O1, H1': join ?O01 ?Of1 ?O1',
        H2: join ?O02 ?Of2 ?O2, H2': join ?O02 ?Of2 ?O2' |- _ =>
      (assert (O1 = O1') by join auto; subst);
      (assert (O2 = O2') by join auto; subst)
  | act: action, H1: ?f _ ?O1 ?act (_, Some ?O1'), H2: ?f _ ?O2 ?act (_, Some ?O2') |- _ => 
      (assert (O1 = O1') by eauto with oeq_lemmas; subst);
      (assert (O2 = O2') by eauto with oeq_lemmas; subst); 
      symexe 
  | _ => idtac
  end. 

Ltac try_false_app lst :=
  match lst with
    (?lst', ?lem) => try (solve [false; eapply lem; eauto]); try_false_app lst'
  | pnil => idtac
  end.

Ltac solve_contra :=
  try_false_app
    (pnil,
      cpe_no_prtaccept_cap_impl_f,
      prts_equiv_orcond_impl_f,
      prte_port_type_impl_f, 
      cheq_no_chan_impl_f, 
      cheq_intercore_impl_f).
    (* (pnil, *)
    (*   cpe_no_prtpost_cap_impl_f,  *)
    (*   prts_equiv_orcond_impl_f,  *)
    (*   prte_port_type_impl_f,  *)
    (*   prte_prtid_invalid_impl_f,  *)
    (*   cheq_no_chan_impl_f,  *)
    (*   cheq_intercore_impl_f). *)

Ltac solve_prtacc_equiv Hlenvl Hlenvl1 Hlenvl2 k :=
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


Lemma hidapistep_hidapistep_prtaccept_lemma:
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
  (Hstep1: spec_step get_hprio_d cd1 O1 cd' O1' act)
  (Hstep2 : spec_step get_hprio_d cd2 O2 cd'0 O2' act)
  (Hcpe : cap_equiv (dom_for_prio pr) O1 O2)
  (Hhsat1 : head_asrt_sat pr cd1 O1)
  (Hhsat2 : head_asrt_sat pr cd2 O2)
  (Hvleq : vl_equiv cd1 cd2)
  (Hnex : ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2))
  (Hacce : prtaccept_equiv cd1 cd2) 
  (Hcont : cont_equiv pr ks1_ ks1 O1 O2)
  (HC2 : get T2 t2 = Some (curs (hapi_code cd2), (ke0, ks1))),
    
    code_equiv_tskd i (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_)))
      (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))) O1' O2' /\
      data_equiv_tskd i cst1' cst2' O1' O2'.  
Proof.
  intros. 
  unfolds in Hacce.
  destruct Hacce as (vl & vl1 & vl2 & k & Hlenvl & Hlenvl1 & Hlenvl2 & Hnth1 & Hnth2).  
  rename cd' into cd1'. rename cd'0 into cd2'.  
  assert (Hbind_all : bind_all vl vl1 vl2 cd1' cd2') by (unfolds; apply n_block_cross_part).
  assert (Hnex':
    match (cd1', cd2') with
      (spec_done _, spec_done _) => True
    | (_, _) => ~ (exists vo1 vo2, cd1' = END vo1 /\ cd2' = END vo2)
    end).
  {
    destruct cd1'; try (unfolds; intros; simpljoin; congruence).
    destruct cd2'; try (unfolds; intros; simpljoin; congruence).
    auto.
  }
  do 2 try destruct vl; tryfalse.
  do 3 try destruct vl1; tryfalse.
  do 3 try destruct vl2; tryfalse.
  destruct v0; simpl in Hnth1;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).  
  destruct v2; simpl in Hnth2; 
    try (eapply abt_succs_contra in Hnth2; inverts Hstep2; tryfalse; fail).

  unfold obsr_equiv_tskd in Htdeq. 
  destruct Htdeq as (Hce & Hde).
  unfolds in Hsceq. unfolds in Hsceq.
  destruct Hsceq as (Hce_sch & Hde_sch). 
  unfolds in Htmeq.
  lets Hcpe_sym: cap_equiv_sym Hcpe; eauto.
  lets Hprte_sym: ports_equiv_sym Hpde; eauto. 
  lets Htmeq_sym: obsr_equiv_chnd_sym Htmeq; eauto. 
    
  start k.
  (* k=0 *)
  symexe; solve_contra. 
  {
    apply11 ret_val ret_val rv_veq H1_ H2_. subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    apply cmd_equiv_end.    
  }
  {
    obsr_equiv_tskd_upd2_preserve' 1%nat.
    - eapply prt_indom_has_port; eauto. 
    - eapply prt_indom_has_port; eauto. 
  }

  start k.
  (* k=1 *)
  symexe; solve_contra. 
  {
    apply11 ret_val ret_val rv_veq H1_ H2_. subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    apply cmd_equiv_end.        
  }
  {
    apply11 ret_val ret_val rv_veq H1_ H2_. subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    apply cmd_equiv_end.            
  }
  {
    apply11 ret_val ret_val rv_veq H1_ H2_. subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    apply cmd_equiv_end.            
  }
  {
    obsr_equiv_tskd_upd2_preserve' 2%nat.
    - eapply nwd_prt_indom; eauto.
    - eapply nwd_prt_indom; eauto.
  }

  start k.
  (* k=2 *)
  symexe; solve_contra.
  {
    apply11 ret_val ret_val rv_veq H1_ H2_. subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    apply cmd_equiv_end.      
  }
  {
    obsr_equiv_tskd_upd2_preserve' 4%nat.
  }
  {
    apply2 chsem_res chsem_res chsem_res_eq; eauto. 
    obsr_equiv_tskd_upd2_preserve' 3%nat.
    eapply veq_vlequiv; eauto. 
    simpl. eauto. simpl. eauto.     
  }

  start k.
  (* k=3 *)
  lets Hve: vlequiv_veq_ext Hvleq; eauto.
  specializes Hve; simpl; eauto.
  subst. 
  symexe; solve_contra.
  {
    apply11 ret_val ret_val rv_veq H1_ H2_. subst.
    obsr_equiv_tskd_upd2_preserve' 4%nat.
    eapply vl_equiv_nil; eauto. 
  }
  {
    obsr_equiv_tskd_upd2_preserve' 4%nat.
    eapply vl_equiv_nil; eauto. 
  }

  start k.
  (* k=4 *)
  symexe; solve_contra.
  {
    split.
    (* code_equiv *)
    Set Nested Proofs Allowed. 

    assert (Hpp1: prio_preserved O1 O1').
    { eapply receive_port_msg_prio_preserved; eauto. }
    assert (Hpp2: prio_preserved O2 O2').
    { eapply receive_port_msg_prio_preserved; eauto. }    
    apply11 receive_port_msg receive_port_msg
      receive_port_msg_cpid_same Hcpeq2 Hcpeq1.
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
      right; right; right; right; right; right; left.
      (* sprtpost_equiv *)
      solve_prtacc_equiv Hlenvl Hlenvl1 Hlenvl2 5%nat. 
    }
    eapply cont_equiv_qref_preserve; eauto.
    eapply receive_port_msg_mqref_preserve; eauto.
    eapply receive_port_msg_mqref_preserve; eauto.
    eapply receive_port_msg_qprt_preserve; eauto.
    eapply receive_port_msg_qprt_preserve; eauto. 
    eapply eqdom_frm_domimpl; eauto. 
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    lets H__: code_equiv_hsat_neq_st'; eauto. 
    eapply H__; eauto.
    eapply receive_port_msg_mqref_preserve; eauto.
    eapply receive_port_msg_mqref_preserve; eauto.
    eapply receive_port_msg_qprt_preserve; eauto.
    eapply receive_port_msg_qprt_preserve; eauto. 
    eapply eqdom_frm_domimpl; eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

    (* data_equiv *)  
    eapply receive_port_msg_dteq_preserve2 with (O10:=O0) (O20:=O); eauto. 
    eapply eqdom_frm_domimpl with (O10:=O0) (O20:=O'0); eauto.
    eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
  }

  start k.
  (* k=5 *)
  symexe; solve_contra.
  {
    obsr_equiv_tskd_upd2_preserve' 6%nat.    
  }
  {
    obsr_equiv_tskd_upd2_preserve' 6%nat.        
  }

  start k.
  (* k=6 *)
  symexe; solve_contra.
  {
    apply11 ret_val ret_val rv_veq H1_ H2_. subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    apply cmd_equiv_end.          
  }

  simpl in Hnth2.
  rewrite nth_error_nil in Hnth2.
  false. 
Qed. 
