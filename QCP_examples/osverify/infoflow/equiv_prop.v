
Require Import base_tac. 
Require Import if_language. 
Require Import if_opsem.
Require Import properties.
Require Import if_assms.

Require Import if_common_lemmas. 

Definition ex_tsk_equiv (td: taskdom) O1 O2 := 
  forall pr,
    dom_for_prio pr = td ->
    ((exists t, task_prio_id O1 pr t) <-> (exists t, task_prio_id O2 pr t)). 
    
Set Keyed Unification.

Lemma code_equiv_trans:
  forall (td: taskdom) (T1 T2 T3: tasks) (O1 O2 O3: osabst),
    ex_tsk_equiv td O1 O2 ->
    code_equiv_tskd td T1 T2 O1 O2 ->
    code_equiv_tskd' td T2 T3 O2 O3 ->
    code_equiv_tskd td T1 T3 O1 O3.
Proof.
  introv Hte Hce Hce'.
  unfold code_equiv_tskd in Hce.
  unfold code_equiv_tskd.
  unfold code_equiv_tskd' in Hce'.

  introv Hdom Htpi Htpi'.
  rename t2 into t3.
  lets Hte_: Hte Hdom. clear Hte.
  assert (Hex: exists t, task_prio_id O1 pr t) by eauto.
  apply Hte_ in Hex.
  destruct Hex as [t2 Htpi2].
  lets Hce_: Hce Hdom Htpi Htpi2.
  lets Hce'_: Hce' Hdom Htpi2 Htpi'.
  
  destruct Hce_ as (c1 & c2 & ke & ks1 & ks2 & Hcebody).
  destruct Hcebody as (Hget1 & Hget2 & Hcmd & Hcont).
  destruct Hce'_ as (Hceq23 & Hbody).
  lets Hdisj: Hbody Hget2. 

  exists c1.  exists c2.
  exists ke. exists ks1. exists ks2.
  rewrite <- Hceq23. 
  splits; eauto.
  unfold cmd_equiv in *.
  destruct Hcmd as [Hceq12 | Hceq'12].
  -
    left. auto.
  -
    destruct Hdisj as (Hnknl & Hknl).
    destruct Hceq'12 as
        (cd1 & cd2 & Hc1 & Hc2 & Hhdsat1 & Hhdsat2 & Hvleq1 & Hvleq2).
    destruct Hnknl as [Hnknl1 | Hnknl2].
    
    rewrite Hc2 in Hnknl1.
    unfold not_knl_stmt in Hnknl1.
    destruct Hnknl1.
    destruct H. inverts H.
    simpljoin. inverts H. false. apply H0. eexists. eauto.

    destruct Hnknl2 as (cd & Hc2' & Hhdsat23).
    right.
    exists cd1.
    exists cd2.
    rewrite Hc2' in Hc2.
    inverts Hc2.
    splits; auto.
    rewrite Hhdsat23 in Hhdsat2; eauto.

  -
    unfold cont_equiv in *.
    destruct Hdisj as (Hnknl & Hknl).
    
    destruct Hcont as [Hcont1 | Hcont2].
    left. auto.
    
    right.
    destruct Hcont2 as (c1_ & c2_ & ke_ & ks'_ & Hks1 & Hks2 & Hcmdeq).
    exists c1_. exists c2_.
    exists ke_. exists ks'_.
    splits; eauto.
    
    unfold cmd_equiv in *.
    destruct Hcmdeq as [Hcmdeq1 | Hcmdeq2].
    left. eauto.
    right.
    destruct Hcmdeq2 as (cd1 & cd2 & Hc1_ & Hc2_ & Hsat1 & Hsat2 & Hvl & Hstmt).
    exists cd1. exists cd2.
    splits; auto.
    lets Htrans: Hknl Hks2 Hc2_.
    rewrite Htrans in Hsat2; eauto.
Qed.

Lemma kernel_task_equiv_trans:
  forall td O1 O2 O3,
    kernel_task_equiv td O1 O2 ->
    kernel_task_equiv td O2 O3 ->
    kernel_task_equiv td O1 O3.
Proof.
  introv Hkte12 Hkte23.
  unfold kernel_task_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O2 abstcblsid).
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  do 2 match goal with H: forall _, _ |- _ => specialize (H _ Hd) end.
  simpljoin.
  split.
  -
    tauto.
  -
    introv Hget1 Hget3.
    assert (Hextpi: exists t, task_prio_id O1 pr t).
    {
      eexists t1. unfolds. do 5 eexists.
      split; eauto. 
    }
    assert (Hextpi': exists t, task_prio_id O2 pr t)
      by tauto.
    destruct Hextpi' as (t2_ & Htpi2).
    unfolds in Htpi2.
    simpljoin.
    l_rew21_inv1 (get O2 abstcblsid).
    match goal with H: forall _, _ |- _ => specializes H; eauto end. 
    match goal with H: forall _, _ |- _ => specializes H; eauto end.
    simpljoin.
    split; eauto.
Qed. 

Lemma tidls_equiv_trans: 
  forall ts1 ts2 ts3 O1 O2 O3, 
    tidls_equiv ts1 ts2 O1 O2 ->
    tidls_equiv ts2 ts3 O2 O3 ->
    tidls_equiv ts1 ts3 O1 O3.
Proof.
  introv Hte1 Hte2.
  unfold tidls_equiv in *.
  simpljoin.
  split.
  - congruence.
  - intros.
    do 2 match goal with H: forall _, _ |- _ => specialize (H pr) end.
    tauto.
Qed.     

Lemma mq_ed_equiv_trans:
  forall ed1 ed2 ed3 O1 O2 O3, 
    mq_ed_equiv ed1 ed2 O1 O2 ->
    mq_ed_equiv ed2 ed3 O2 O3 ->
    mq_ed_equiv ed1 ed3 O1 O3.
Proof.
  introv Hmv12 Hmv23.
  unfold mq_ed_equiv in *.
  simpljoin.
  match goal with H: ?f _ _ _ = ?f _ _ _ |- _ => inverts H end.
  do 4 eexists.
  split; eauto.
  split; eauto.
  eapply tidls_equiv_trans; eauto.
Qed. 

Lemma mq_equiv_trans:
  forall td mq1 mq2 mq3 O1 O2 O3, 
    mq_equiv td mq1 mq2 O1 O2 ->
    mq_equiv td mq2 mq3 O2 O3 ->
    mq_equiv td mq1 mq3 O1 O3.
Proof.
  introv Hme12 Hme23.
  unfold mq_equiv in *.
  simpljoin.
  match goal with
    H1: _ \/ _, H2: _ \/ _ |- _ =>
      destruct H1 as [Hnull1 | [Hhd1 | Hptr1]];
      destruct H2 as [Hnull2 | [Hhd2 | Hptr2]];
      simpljoin; tryfalse
  end.
  - do 8 eexists. split; eauto.
  - do 8 eexists. split; eauto.
  - l_rew21_inv1 (get O2 absecblsid).    
    match goal with H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H end.
    match goal with H1: ?t = _, H2: ?t = _ |- _ => rewrite H1 in H2; inverts H2 end.
    do 8 eexists.
    split; eauto.
    split; eauto.
    right; right.
    do 7 eexists.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    split.
    + eapply mq_ed_equiv_trans; eauto.
    + eapply tidls_equiv_trans; eauto.
Qed.       
    
Lemma kernel_mq_equiv_trans:
  forall td O1 O2 O3, 
    kernel_mq_equiv td O1 O2 ->
    kernel_mq_equiv td O2 O3 ->
    kernel_mq_equiv td O1 O3.
Proof.
  introv Hkme12 Hkme23.
  unfold kernel_mq_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O2 absmqattrid).
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hid. 
  do 2 match goal with H: forall _, _ |- _ => specialize (H _ Hid) end.
  simpljoin.
  split.
  - tauto.
  - introv Hg1 Hg3.
    match type of Hg1 with
      ?t = _ => assert (t <> None); [destruct t; tryfalse; introv Hf; inverts Hf | ]
    end.
    assert (Hg2: get x2 i <> None).
    { tauto. }
    destruct (get x2 i) eqn: E.
    + 
      do 2 match goal with H: forall _, _ |- _ => specializes H; eauto end.
      eapply mq_equiv_trans; eauto. 
    +
      tryfalse.
Qed.

Lemma ports_equiv_trans:
  forall td O1 O2 O3, 
    ports_equiv td O1 O2 ->
    ports_equiv td O2 O3 ->
    ports_equiv td O1 O3.
Proof.
  introv Hpe12 Hpe23.
  unfold ports_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O2 osdomainportid).
  l_rew21_inv1 (get O2 absecblsid).
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hd.
  do 2 match goal with H: forall _, _ |- _ => specializes H; eauto end.
  simpljoin.
  split.
  congruence.
  split.
  tauto.
  introv Hg1 Hg3.
  rename tls2 into tls3.
  match type of Hg1 with
    ?t = Some (absport, ?ts) => assert (exists tls, t = Some (absport, tls))
  end.
  { eexists. eauto. }
  match goal with
    H1: ?P1 <-> ?P2, H2: ?P1 |- _ => apply H1 in H2
  end.
  simpljoin.
  do 2 match goal with
      H: forall _, _ |- _ => specializes H; eauto
  end.
  eapply tidls_equiv_trans; eauto.
Qed.   
      
Lemma cap_equiv_trans:
  forall td O1 O2 O3, 
    cap_equiv td O1 O2 ->
    cap_equiv td O2 O3 ->
    cap_equiv td O1 O3.
Proof.
  introv Hce12 Hce23.
  unfold cap_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O2 cspaceid).
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  do 2 match goal with
    H: forall _, _ |- _ => specializes H; eauto
    end.
  simpljoin.
  split.
  - 
    intros.
    do 2 match goal with
        H: forall _ _, _ |- _ => specialize (H cls cap)
      end.
    tauto.
  -
    introv Hid. 
    do 2 match goal with H: forall _, _ |- _ => specialize (H idx); specializes H; eauto end.
    simpljoin.
    split.
    +
      tauto.
    +
      introv Hg1 Hg3.
      rename objp2 into objp3.
      match type of Hg1 with
        spec_aux_defs.mq_ptr _ _ ?p =>
          assert (exists objp, spec_aux_defs.mq_ptr O1 idx objp)
      end.
      { eexists. eauto. }
      match goal with
        H1: ?P1 <-> ?P2, H2: ?P1 |- _ => apply H1 in H2
      end.
      simpljoin.
      specializes H6; eauto.
      specializes H7; eauto.
      tauto.
Qed.

Lemma buffer_equiv_trans:
  forall td O1 O2 O3, 
    buffer_equiv td O1 O2 ->
    buffer_equiv td O2 O3 ->
    buffer_equiv td O1 O3.
Proof.
  introv Hbe12 Hbe23.
  unfold buffer_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H1: forall _, _, H2: forall _,_ |- _ =>
    lets H1_: H1 Hd; eauto;
    lets H2_: H2 Hd; eauto
  end.
  destruct H1_ as (Hiff12 & Heq12).
  destruct H2_ as (Hiff23 & Heq23).
  l_rew21_inv1 (get O2 absecblsid).
  split.
  -
    clear -Hiff12 Hiff23.
    destruct Hiff12.
    destruct Hiff23.
    split; introv Hex; tauto.
  -
    introv Hg1 Hg3.
    destruct Hiff12 as (Hex12 & Hex21).
    specializes Hex12; eauto.
    destruct Hex12 as (ed2_ & ws2_ & Hg2).
    specializes Heq12; eauto.
    specializes Heq23; eauto.
    simpljoin. 
    split.
    eapply mq_ed_equiv_trans; eauto.
    eapply tidls_equiv_trans; eauto. 
Qed.   
  
Lemma kernel_data_equiv_trans:
  forall td O1 O2 O3, 
    kernel_data_equiv td O1 O2 ->
    kernel_data_equiv td O2 O3 ->
    kernel_data_equiv td O1 O3.
Proof.
  introv Hkde12 Hkde23.
  unfold kernel_data_equiv in *.
  simpljoin.
  splits.
  - eapply kernel_task_equiv_trans; eauto.
  - eapply kernel_mq_equiv_trans; eauto.
  - eapply ports_equiv_trans; eauto.
  - eapply buffer_equiv_trans; eauto. 
  - eapply cap_equiv_trans; eauto.
Qed.     

Lemma ibufs_equiv_trans:
  forall td O1 O2 O3, 
    ibufs_equiv td O1 O2 ->
    ibufs_equiv td O2 O3 ->
    ibufs_equiv td O1 O3.
Proof.
  introv Hie12 Hie23.
  unfold ibufs_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  congruence.
Qed.

Lemma obufs_equiv_trans:
  forall td O1 O2 O3, 
    obufs_equiv td O1 O2 ->
    obufs_equiv td O2 O3 ->
    obufs_equiv td O1 O3.
Proof.
  introv Hie12 Hie23.
  unfold obufs_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  congruence.
Qed.

Lemma bufs_equiv_trans:
  forall td O1 O2 O3,
    bufs_equiv td O1 O2 ->
    bufs_equiv td O2 O3 ->
    bufs_equiv td O1 O3.
Proof.
  introv Hbe12 Hbe23.
  unfold bufs_equiv in *.
  simpljoin.
  split.
  - eapply ibufs_equiv_trans; eauto.
  - eapply obufs_equiv_trans; eauto.
Qed.     

Definition ct_ex_prio_dom_eq (O1 O2: osabst) := 
  exists t1 t2, 
    get O1 curtid = Some (oscurt t1) 
    /\ get O2 curtid = Some (oscurt t2) 
    /\ ((exists pr, task_prio_id O1 pr t1) <-> (exists pr, task_prio_id O2 pr t2))
    /\ (forall pr1 pr2 : priority,
           task_prio_id O1 pr1 t1 ->
           task_prio_id O2 pr2 t2 ->
           dom_for_prio pr1 = dom_for_prio pr2). 

Lemma data_equiv_schd_impl_pdeq: 
  forall O1 O2, 
    data_equiv_schd O1 O2 ->
    ct_ex_prio_dom_eq O1 O2. 
Proof.
  introv Hde.
  unfolds in Hde.
  simpljoin.
  unfolds.
  do 2 eexists; eauto. 
Qed. 

Lemma ct_ex_prio_dom_eq_trans:
  forall O1 O2 O3,
    ct_ex_prio_dom_eq O1 O2 ->
    ct_ex_prio_dom_eq O2 O3 ->
    ct_ex_prio_dom_eq O1 O3.
Proof.
  introv Hce12 Hce23.
  unfold ct_ex_prio_dom_eq in *.
  simpljoin.
  l_rew21_inv1 (get O2 curtid).
  do 2 eexists.
  split; eauto.
  split; eauto.
  split.
  tauto.
  introv Htpi1 Htpi3.
  assert (Hex1: exists pr, task_prio_id O1 pr x1).
  { eexists; eauto. }
  apply H5 in Hex1.
  simpljoin.
  specializes H6; eauto.
  specializes H3; eauto.
  congruence.
Qed.   
  
Lemma ctid_equiv_trans_:
  forall td O1 O2 O3,
    ct_ex_prio_dom_eq O1 O2 -> 
    ctid_equiv td O1 O2 ->
    ctid_equiv td O2 O3 ->
    ctid_equiv td O1 O3.
Proof.
  introv Hcep Hce12 Hce23.
  unfold ctid_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O2 curtid).
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1 Htpi3 Hd.
  unfolds in Hcep.  
  simpljoin.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  match goal with H: ?P1 <-> ?P2 |- _ => assert (P2); [apply H | ] end.
  { eexists; eauto. }
  simpljoin.
  match goal with
    H3: forall _ _, _, H1: forall _ _, _, H2: forall _ _, _ |- _ =>
    rename H1 into Heq12; rename H2 into Heq23; rename H3 into Hdeq
  end.
  specializes Hdeq; eauto.
  rewrite Hdeq in *.
  specializes Heq12; eauto.
  specializes Heq23; eauto.
  congruence.
Qed.   

Lemma ctid_equiv_trans:
  forall td O1 O2 O3,
    data_equiv_schd O1 O2 -> 
    ctid_equiv td O1 O2 ->
    ctid_equiv td O2 O3 ->
    ctid_equiv td O1 O3.
Proof.
  introv Hdesch Hce12 Hce23.
  unfold ctid_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O2 curtid).
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1 Htpi3 Hd.
  unfolds in Hdesch.
  simpljoin.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  match goal with H: ?P1 <-> ?P2 |- _ => assert (P2); [apply H | ] end.
  { eexists; eauto. }
  simpljoin.
  match goal with
    H1: forall _ _, _, H2: forall _ _, _, H3: forall _ _, _ |- _ =>
    rename H1 into Hdeq; rename H2 into Heq12; rename H3 into Heq23
  end.
  specializes Hdeq; eauto.
  rewrite Hdeq in *.
  specializes Heq12; eauto.
  specializes Heq23; eauto.
  congruence.
Qed. 

Lemma local_envs_equiv_trans:
  forall td O1 O2 O3 cenvs1 cenvs2 cenvs3, 
    ex_tsk_equiv td O1 O2 ->
    local_envs_equiv td cenvs1 cenvs2 O1 O2 ->
    local_envs_equiv td cenvs2 cenvs3 O2 O3 ->
    local_envs_equiv td cenvs1 cenvs3 O1 O3. 
Proof.
  introv Hete Hleq12 Hleq23.
  unfold local_envs_equiv in *.
  unfold ex_tsk_equiv in *.
  introv Hd.
  specialize (Hleq12 _ Hd).
  specialize (Hleq23 _ Hd).
  introv Htpi1 Htpi3.
  rename t2 into t3.
  assert (Hex: exists t, task_prio_id O1 pr t).
  { eexists; eauto. }
  specialize (Hete _ Hd).
  apply Hete in Hex.
  simpljoin. 
  specializes Hleq12; eauto.
  specializes Hleq23; eauto.
  congruence.
Qed.

Lemma client_data_equiv_trans:
  forall td O1 O2 O3 cst1 cst2 cst3, 
    ex_tsk_equiv td O1 O2 -> 
    client_data_equiv td cst1 cst2 O1 O2 ->
    client_data_equiv td cst2 cst3 O2 O3 ->
    client_data_equiv td cst1 cst3 O1 O3.
Proof.
  introv Hete Hcde12 Hcde23.
  unfold client_data_equiv in *.
  simpljoin.
  do 6 eexists.
  split; eauto.
  split; eauto.
  split.
  congruence.
  split.
  eapply local_envs_equiv_trans; eauto.
  congruence. 
Qed.

Lemma obsr_equiv_impl_ex_tsk_equiv: 
  forall td T1 T2 cst1 cst2 O1 O2 sc, 
    obsr_equiv sc (TaskDom td) T1 T2 cst1 cst2 O1 O2 ->
    ex_tsk_equiv td O1 O2.
Proof.
  introv Hoe.
  unfolds in Hoe.
  unfolds in Hoe.
  destruct Hoe as (_ & Hdet).
  unfolds in Hdet.
  destruct Hdet as (_ & _ & Hkde & _).
  unfolds in Hkde.
  destruct Hkde as (Hkte & _ & _ & _).
  unfolds in Hkte.
  simpljoin.
  unfolds.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets H_: H Hd end.
  simpljoin.
  auto.
Qed.

Lemma obsr_equiv_tskd_trans_: 
  forall sc td T1 T2 T3 cst1 cst2 cst3 O1 O2 O3,
    ct_ex_prio_dom_eq O1 O2 -> 
    obsr_equiv_tskd sc td T1 T2 cst1 cst2 O1 O2 ->
    obsr_equiv_tskd' sc td T2 T3 cst2 cst3 O2 O3 ->
    obsr_equiv_tskd sc td T1 T3 cst1 cst3 O1 O3.
Proof.
  introv Hde Hoe12 Hoe23.
  assert (Hete: ex_tsk_equiv td O1 O2).
  {
    lets H__: obsr_equiv_impl_ex_tsk_equiv Hoe12; eauto.
  }
  unfolds in Hoe12.
  unfolds in Hoe23.
  unfolds.
  unfold obsr_equiv_tskd in *.
  destruct Hoe12 as (Hcet12 & Hdet12).
  destruct Hoe23 as (Hcet23 & Hdet23).
  split.
  - 
    eapply code_equiv_trans; eauto. 
  -
    unfold data_equiv_tskd in *.
    simpljoin.
    splits.
    +
      eapply ctid_equiv_trans_; eauto.
    +
      eapply bufs_equiv_trans; eauto.
    +
      eapply kernel_data_equiv_trans; eauto.
    +
      eapply client_data_equiv_trans; eauto.
Qed.    

Lemma obsr_equiv_tskd_trans:
  forall sc td T1 T2 T3 cst1 cst2 cst3 O1 O2 O3,
    data_equiv_schd O1 O2 -> 
    obsr_equiv_tskd sc td T1 T2 cst1 cst2 O1 O2 ->
    obsr_equiv_tskd' sc td T2 T3 cst2 cst3 O2 O3 ->
    obsr_equiv_tskd sc td T1 T3 cst1 cst3 O1 O3.
Proof.
  introv Hde Hoe12 Hoe23.
  assert (Hete: ex_tsk_equiv td O1 O2).
  {
    lets H__: obsr_equiv_impl_ex_tsk_equiv Hoe12; eauto.
  }
  unfolds in Hoe12.
  unfolds in Hoe23.
  unfolds.
  unfold obsr_equiv_tskd in *.
  destruct Hoe12 as (Hcet12 & Hdet12).
  destruct Hoe23 as (Hcet23 & Hdet23).
  split.
  - 
    eapply code_equiv_trans; eauto. 
  -
    unfold data_equiv_tskd in *.
    simpljoin.
    splits.
    +
      eapply ctid_equiv_trans; eauto.
    +
      eapply bufs_equiv_trans; eauto.
    +
      eapply kernel_data_equiv_trans; eauto.
    +
      eapply client_data_equiv_trans; eauto.
Qed.    


(* same lemma as in confidentiality_proof.v *)
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

Lemma ctid_equiv_refl:
  forall t d O,
    get O curtid = Some (oscurt t) -> 
    ctid_equiv d O O.
Proof.
  introv Hctid.
  unfolds.
  exists t t.
  splits; auto.
  introv Htpi1 Htpi2 Hd. 
  lets H_: prio_unique Htpi1 Htpi2.
  auto.
Qed.   

Lemma bufs_equiv_refl:
  forall d O x y,
    get O ibufsid = Some (ibufs x) -> 
    get O obufsid = Some (obufs y) -> 
    bufs_equiv d O O.
Proof.
  intros.
  unfold bufs_equiv.
  split.
  unfold ibufs_equiv.
  do 2 eexists.
  splits; eauto.
  unfold obufs_equiv.
  do 2 eexists.
  splits; eauto. 
Qed.   

Lemma kernel_task_equiv_refl:
  forall d O x,
    get O abstcblsid = Some (abstcblist x) ->
    kernel_task_equiv d O O.
Proof.
  introv Htcb.
  unfolds.
  exists x x.
  splits; auto.
  introv Hd.
  split.
  -
    split; intros; auto.
  -
    introv Hget1 Hget2.
    assert (Htpi1: task_prio_id O pr t1).
    {
      unfolds. repeat eexists; eauto.
    }
    assert (Htpi2: task_prio_id O pr t2).
    {
      unfolds. repeat eexists; eauto. 
    }
    lets H_: tid_unique Htpi1 Htpi2.
    subst.
    rewrite Hget1 in Hget2.
    inverts Hget2.
    splits; auto.
Qed.

Lemma tidls_equiv_refl:
  forall pwl O, 
    tidls_equiv pwl pwl O O. 
Proof.
  intros.
  unfolds.
  intros.
  split; auto. 
  split; intros; auto.
Qed.   
  
Lemma kernel_mq_equiv_refl:
  forall d O x y,
    get O absmqattrid = Some (absmqattr x) ->
    get O absecblsid = Some (absecblist y) -> 
    kernel_mq_equiv d O O.
Proof.
  introv Hmq Hecb.
  unfolds.
  exists x x.
  splits; auto.
  introv Hindom.
  split.
  tauto.
  introv Hget1 Hget2. 
  unfolds.
  rewrite Hget1 in Hget2.
  inverts Hget2.
  destruct mq2. destruct p. destruct p. destruct p. destruct p. destruct p. 
  repeat eexists; eauto.
  destruct e.
  - left. split; auto.
  - right. left. split; auto.
  - right. right.
    exists y y. exists t.
    lets H_: mq_ecb Hmq Hget1 Hecb.
    destruct H_ as (ms & sz & pwl & wl & He).
    remember (absmsgq ms sz pwl) as mqevt. 
    exists mqevt mqevt wl wl.
    splits; auto.
    2: { apply tidls_equiv_refl; auto. }
    unfolds.
    rewrite Heqmqevt.
    do 4 eexists.
    splits; eauto.
    apply tidls_equiv_refl; auto.
Qed.       
    
Lemma ports_equiv_refl:
  forall d O x y z, 
    get O osdomainportid = Some (osdomainport x) ->
    get O oskportid = Some (oskport y) -> 
    get O absecblsid = Some (absecblist z) ->
    ports_equiv d O O.
Proof.
  introv Hdp Hkp Heb.
  unfolds.
  exists x x z z.
  splits; auto.
  split.
  -
    auto.
  -
    split.
    + tauto.
    + introv Hgett1 Hgett2.
      unfolds.
      rewrite Hgett1 in Hgett2. inverts Hgett2.
      split; auto. 
      intros.
      split; introv H_; auto.
Qed.     

Lemma cap_equiv_refl: 
  forall d O x, 
    get O cspaceid = Some (capcspace x) ->
    cap_equiv d O O.  
Proof.
  introv Hget.
  unfolds.
  exists x x.
  splits; auto.
  introv Hd.
  split.
  intros.
  split; auto.
  split.
  tauto.
  introv Hp1 Hp2.
  unfolds in Hp1.
  unfolds in Hp2. 
  simpljoin.
  match goal with
    H1: get O absmqattrid = _, H2: get O absmqattrid = _ |- _ => rewrite H1 in H2; inverts H2
  end.
  match goal with
    H1: get _ idx = Some _, H2: get _ idx = Some _ |- _ => rewrite H1 in H2; inverts H2 
  end.
  assert (objp1 = objp2).
  {
    repeat match goal with H: _ \/ _ |- _ => inverts H end; 
      simpljoin;
      congruence. 
  }
  subst.
  split; eauto. 
Qed.

Lemma buffer_equiv_refl:
  forall td O els,
    get O absecblsid = Some (absecblist els) -> 
    buffer_equiv td O O. 
Proof.
  intros.
  unfolds.
  do 2 eexists.
  split; eauto.
  split; eauto.
  intros.
  split.
  - split; intros; auto.
  - introv Hg1 Hg2.
    rewrite Hg1 in Hg2; inverts Hg2.
    lets H__: buffer_ecb.
    specializes H__; eauto.
    simpljoin.
    rewrite H1 in Hg1; inverts Hg1.
    split.
    + unfolds.
      do 4 eexists.
      split; eauto.
      split; eauto.
      eapply tidls_equiv_refl; eauto. 
    + eapply tidls_equiv_refl; eauto. 
Qed. 

Lemma kernel_data_equiv_refl:
  forall d O x1 x2 x3 x4 x5 x6, 
    get O abstcblsid = Some (abstcblist x1) ->
    get O absmqattrid = Some (absmqattr x2) ->
    get O absecblsid = Some (absecblist x3) ->
    get O osdomainportid = Some (osdomainport x4) ->
    get O oskportid = Some (oskport x5) ->
    get O cspaceid = Some (capcspace x6) -> 
    kernel_data_equiv d O O.
Proof.
  introv Hgett Hgetm Hgete Hgetdp Hgetkp Hgetcp.
  unfolds.
  splits.
  eapply kernel_task_equiv_refl; eauto.
  eapply kernel_mq_equiv_refl; eauto.
  eapply ports_equiv_refl; eauto.
  eapply buffer_equiv_refl; eauto. 
  eapply cap_equiv_refl; eauto. 
Qed.
  

Lemma ct_ex_prio_dom_eq_sym:
  forall O1 O2,
    ct_ex_prio_dom_eq O1 O2 ->
    ct_ex_prio_dom_eq O2 O1. 
Proof.
  introv Hceq12.
  unfold ct_ex_prio_dom_eq in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  split.
  tauto.
  introv Htpi2 Htpi1.
  symmetry.
  eapply H2; eauto.
Qed. 

Lemma tidls_equiv_sym:
  forall tl1 tl2 O1 O2, 
    tidls_equiv tl1 tl2 O1 O2 ->
    tidls_equiv tl2 tl1 O2 O1.
Proof.
  introv Hte.
  unfold tidls_equiv in *.
  simpljoin.
  split. symmetry; auto. 
  intros.
  specialize (H0 pr).
  destruct H0.
  split; eauto. 
Qed.         

Lemma mqed_equiv_sym:
  forall ed1 ed2 O1 O2, 
    mq_ed_equiv ed1 ed2 O1 O2 ->
    mq_ed_equiv ed2 ed1 O2 O1. 
Proof.
  introv Hmee.
  unfold mq_ed_equiv in *.
  simpljoin.
  do 4 eexists.
  splits; eauto.
  eapply tidls_equiv_sym; eauto. 
Qed. 

Lemma mq_equiv_sym:
  forall mq1 mq2 O1 O2 td, 
    mq_equiv td mq1 mq2 O1 O2 ->
    mq_equiv td mq2 mq1 O2 O1.  
Proof.
  introv Hme.
  unfold mq_equiv in *.
  simpljoin.
  repeat eexists.
  match goal with
    H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hhd | Haddr]]
  end.
  -
    left. simpljoin. split; auto. 
  -
    right; left.
    simpljoin. split; auto.
  -
    right; right.
    simpljoin. do 7 eexists. splits; eauto.
    2: { eapply tidls_equiv_sym; eauto. }
    eapply mqed_equiv_sym; eauto. 
Qed. 

Lemma knl_mq_equiv_sym:
  forall O1 O2 td, 
    kernel_mq_equiv td O1 O2 -> 
    kernel_mq_equiv td O2 O1. 
Proof.
  introv Hkme.
  unfold kernel_mq_equiv in *.
  simpljoin.
  do 2 eexists.
  splits; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets H__: H Hd; eauto end.
  simpljoin.
  split.
  tauto.
  introv Hg1 Hg2.
  specializes H1; eauto.
  eapply mq_equiv_sym; eauto. 
Qed.

Lemma cap_equiv_sym:
  forall td O1 O2, 
    cap_equiv td O1 O2 ->
    cap_equiv td O2 O1. 
Proof.
  introv Hce.
  unfold cap_equiv in *.
  simpljoin.
  do 2 eexists.
  splits; eauto.
  introv Hd.
  specializes H1; eauto.
  simpljoin.
  split.
  - intros. symmetry. auto. 
  - introv Hid.
    match goal with H: forall _, _ |- _ => lets H__: H Hid; eauto end.
    simpljoin.
    split.
    + tauto.
    + introv Hmp1 Hmp2.
      specializes H2; eauto.
      symmetry.
      auto. 
Qed.   

Lemma kernel_task_equiv_sym:
  forall td O1 O2, 
    kernel_task_equiv td O1 O2 ->
    kernel_task_equiv td O2 O1.
Proof.
  introv Hke.
  unfold kernel_task_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  specialize (H1 pr Hd).
  simpljoin.
  split.
  - split.
    introv Htpi2. apply H1 in Htpi2. auto.
    introv Htpi1. apply H1 in Htpi1. auto.
  - introv Hget1 Hget2.
    lets H__: H2 Hget2 Hget1.
    simpljoin. splits; eauto. 
Qed.

Lemma ctid_equiv_sym_:  
  forall td O1 O2, 
    ctid_equiv td O1 O2 -> 
    ct_ex_prio_dom_eq O1 O2 ->
    ctid_equiv td O2 O1. 
Proof.
  introv Hce Hsce.
  unfold ctid_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1 Htpi2 Hd.
  symmetry.
  eapply H1; eauto.
  unfolds in Hsce.  
  simpljoin.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  eapply H5; eauto.
Qed.   
                  
Lemma ctid_equiv_sym:
  forall td O1 O2, 
    ctid_equiv td O1 O2 ->
    data_equiv_schd O1 O2 -> 
    ctid_equiv td O2 O1. 
Proof.
  introv Hce Hsce.
  unfold ctid_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1 Htpi2 Hd.
  symmetry.
  eapply H1; eauto.
  unfolds in Hsce.
  simpljoin.
  l_rew12_inv2 (get O1 curtid).
  l_rew12_inv2 (get O2 curtid). 
  eapply H9; eauto. 
Qed.

Lemma data_equiv_schd_sym:
  forall O1 O2, 
    data_equiv_schd O1 O2 ->
    data_equiv_schd O2 O1. 
Proof.
  introv Hsche.
  unfold data_equiv_schd in *.
  simpljoin.
  split. split; congruence.
  split. split; congruence.
  split. split; congruence.
  split. split; congruence.
  do 2 eexists.
  split; eauto.
  split; eauto.
  split. tauto.
  introv Htpi2 Htpi1. symmetry. eauto.
Qed.

Lemma vl_equiv_sym:
  forall cd1 cd2, 
    vl_equiv cd1 cd2 ->
    vl_equiv cd2 cd1. 
Proof.
  introv Hvle.
  unfold vl_equiv in *.
  introv Hg1 Hg2 Hn1 Hn2.
  specializes Hvle; eauto. 
Qed.   

Lemma stmt_equiv_sym:
  forall cd1 cd2, 
    stmt_equiv cd1 cd2 ->
    stmt_equiv cd2 cd1. 
Proof.
  introv Hse. 
  unfold stmt_equiv in *.
  inverts Hse.

  - left. simpljoin. eexists; eauto.

  - simpljoin.
    right. 
    split.
    introv Hend. apply H.
    simpljoin.
    do 2 eexists; eauto.
    
    inverts H0.
    left.
    unfold mqsend_equiv in *.
    simpljoin.
    do 4 eexists; eauto.
    
    inverts H1.
    right; left.
    unfold mqrecv_equiv in *.
    simpljoin.
    do 4 eexists; eauto.
    
    inverts H0.
    right; right; left.
    unfold mqtimedrecv_equiv in *.
    simpljoin.    
    do 4 eexists; eauto.
    
    inverts H1.
    right; right; right; left.
    unfold qprtpost_equiv in *.
    simpljoin.
    do 4 eexists; eauto.
    
    inverts H0.
    right; right; right; right; left.
    unfold qprtpend_equiv in *.
    simpljoin.
    do 4 eexists; eauto.

    inverts H1.
    right; right; right; right; right; left.
    unfold sprtpost_equiv in *.
    simpljoin.
    do 4 eexists; eauto.

    inverts H0.
    right; right; right; right; right; right; left.
    unfold prtaccept_equiv in *.
    simpljoin.
    do 4 eexists; eauto.

    inverts H1.
    right; right; right; right; right; right; right; left.
    unfold bufferpost_equiv in *.
    simpljoin.
    do 4 eexists; eauto.

    inverts H0.
    right; right; right; right; right; right; right; right; left.
    unfold bufferaccept_equiv in *.
    simpljoin.
    do 4 eexists; eauto.

    inverts H1.
    right; right; right; right; right; right; right; right; right; left.
    unfold bufferpend_equiv in *.
    simpljoin.
    do 4 eexists; eauto.
    
    inverts H0.
    right; right; right; right; right; right; right; right; right; right; left.
    unfold intr_equiv in *.
    simpljoin.
    eexists; eauto.

    simpljoin.
    auto 20.
Qed.   
  
Lemma cmd_equiv_sym:
  forall pr c1 c2 O1 O2, 
    cmd_equiv pr c1 c2 O1 O2 ->
    cmd_equiv pr c2 c1 O2 O1. 
Proof.
  introv Hcde.
  unfolds.
  unfolds in Hcde.
  inverts Hcde.
  -
    simpljoin.
    left. eauto.
  -
    simpljoin.
    right.
    do 2 eexists.
    splits; eauto. 
    apply vl_equiv_sym; auto.
    apply stmt_equiv_sym; auto. 
Qed.

Lemma cont_equiv_sym:
  forall pr ks1 ks2 O1 O2, 
    cont_equiv pr ks1 ks2 O1 O2 ->
    cont_equiv pr ks2 ks1 O2 O1.
Proof.
  introv Hcnte.
  unfold cont_equiv in *.
  inverts Hcnte.
  -
    left. simpljoin. splits; eauto.
  -
    right. simpljoin. do 4 eexists. splits; eauto. 
    apply cmd_equiv_sym; auto.
Qed.      
  
Lemma code_equiv_tskd_sym:
  forall d T1 T2 O1 O2, 
    code_equiv_tskd d T1 T2 O1 O2 ->
    code_equiv_tskd d T2 T1 O2 O1. 
Proof.
  introv Hce.
  unfolds.
  unfolds in Hce.
  introv Hd Htpi2 Htpi1.
  specializes Hce; eauto.
  simpljoin.
  do 5 eexists.
  splits; eauto.
  apply cmd_equiv_sym; auto. 
  apply cont_equiv_sym; auto. 
Qed.

Lemma ports_equiv_sym:
  forall td O1 O2, 
    ports_equiv td O1 O2 ->
    ports_equiv td O2 O1. 
Proof.
  introv Hpe.
  unfold ports_equiv in *.
  simpljoin.  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with
    H: forall _, _ -> _ |- _ => lets H__: H Hd
  end.
  destruct H__ as (Heq & Heqv & Hteq).
  splits.
  - 
    symmetry. auto.
  -
    tauto.
  -    
    introv Hgt1 Hgt2.
    eapply tidls_equiv_sym; eauto.
Qed.

Lemma ibufs_equiv_sym:
  forall td O1 O2, 
    ibufs_equiv td O1 O2 ->
    ibufs_equiv td O2 O1.
Proof.
  introv Hie.
  unfold ibufs_equiv in *.
  simpljoin.
  do 2 eexists; eauto.
Qed.

Lemma obufs_equiv_sym:
  forall td O1 O2, 
    obufs_equiv td O1 O2 ->
    obufs_equiv td O2 O1.
Proof.
  introv Hoe.
  unfold obufs_equiv in *.
  simpljoin.
  do 2 eexists; eauto.
Qed.

Lemma bufs_equiv_sym:
  forall td O1 O2,
    bufs_equiv td O1 O2 ->
    bufs_equiv td O2 O1.
Proof.
  introv Hb.
  unfold bufs_equiv in *.
  simpljoin.
  split.
  eapply ibufs_equiv_sym; auto.
  eapply obufs_equiv_sym; auto.
Qed. 

Lemma obsr_equiv_chnd_sym:
  forall O1 O2, 
    obsr_equiv_chnd O1 O2 ->
    obsr_equiv_chnd O2 O1. 
Proof.
  introv Hoec.
  unfold obsr_equiv_chnd in *.
  simpljoin.
  split.
  split; congruence.
  split; congruence. 
Qed.

Lemma kernel_mq_equiv_sym:
  forall td O1 O2, 
    kernel_mq_equiv td O1 O2 ->
    kernel_mq_equiv td O2 O1.
Proof.
  introv Hkme.
  unfold kernel_mq_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => specializes H; eauto end.
  simpljoin.
  split; eauto.
  tauto.
  introv Hg1 Hg2.
  match goal with H: forall _, _ |- _ => specializes H; eauto end.
  eapply mq_equiv_sym; eauto. 
Qed.

Lemma buffer_equiv_sym:
  forall td O1 O2,
    buffer_equiv td O1 O2 ->
    buffer_equiv td O2 O1. 
Proof.
  introv Hbe.
  unfold buffer_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets H__: H Hd end.
  destruct H__ as (Hiff & Ha).
  split.
  tauto.
  introv Hg2 Hg1.
  specializes Ha; eauto.
  destruct Ha as (Hmee & Hte).
  lets H__: buffer_ecb H; eauto.
  simpljoin.
  unfold get in *. unfold EcbMap in *.
  l_rew12_inv2 (EcbMod.get x eid).
  lets H__: buffer_ecb H0; eauto.
  simpljoin.
  unfold get in *. unfold EcbMap in *.
  l_rew12_inv2 (EcbMod.get x0 eid).
  unfolds in Hmee.
  simpljoin.
  match goal with
    H1: absmsgq _ _ _ = _, H2: absmsgq _ _ _ = _ |- _ =>
      inverts H1; inverts H2
  end.
  split.
  - unfolds.
    do 4 eexists.
    split; eauto.
    split; eauto.
    eapply tidls_equiv_sym; eauto.    
  - eapply tidls_equiv_sym; eauto.    
Qed.     

Lemma kernel_data_equiv_sym:
  forall td O1 O2, 
    kernel_data_equiv td O1 O2 ->
    kernel_data_equiv td O2 O1. 
Proof.
  introv Hkde.
  unfold kernel_data_equiv in *.
  simpljoin.
  splits.
  - eapply kernel_task_equiv_sym; eauto.
  - eapply kernel_mq_equiv_sym; eauto.
  - eapply ports_equiv_sym; eauto.
  - eapply buffer_equiv_sym; eauto. 
  - eapply cap_equiv_sym; eauto. 
Qed.     

Lemma local_envs_equiv_sym:
  forall td ces1 ces2 O1 O2, 
    local_envs_equiv td ces1 ces2 O1 O2 ->
    local_envs_equiv td ces2 ces1 O2 O1.
Proof.
  introv Hlee.
  unfold local_envs_equiv in *.
  introv Hd Htpi2 Htpi1.
  specializes Hlee; eauto. 
Qed.   
  
Lemma client_data_equiv_sym:
  forall td O1 O2 cst1 cst2,
    client_data_equiv td cst1 cst2 O1 O2 ->
    client_data_equiv td cst2 cst1 O2 O1. 
Proof.
  introv Hcde.
  unfold client_data_equiv in *.
  simpljoin.
  do 6 eexists.
  split; eauto.
  split; eauto.
  split.
  eauto. 
  split.
  eapply local_envs_equiv_sym; eauto.
  eauto.
Qed.   

Lemma obsr_equiv_tskd_sym:
  forall sc td T1 T2 cst1 cst2 O1 O2,     
    data_equiv_schd  O1 O2 -> 
    obsr_equiv_tskd sc td T1 T2 cst1 cst2 O1 O2 ->
    obsr_equiv_tskd sc td T2 T1 cst2 cst1 O2 O1.
Proof.
  introv Hes Hoe.
  unfold obsr_equiv_tskd in *.
  destruct Hoe as (Hcet & Hdet).
  split.
  -
    eapply code_equiv_tskd_sym; eauto.
  -
    unfold data_equiv_tskd in *.
    simpljoin.
    splits.
    + eapply ctid_equiv_sym; eauto.
    + eapply bufs_equiv_sym; eauto.
    + eapply kernel_data_equiv_sym; eauto. 
    + eapply client_data_equiv_sym; eauto. 
Qed.       
