
Require Import FunctionalExtensionality.
Require Import math_auto.

Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import osspecs. 
Require Import properties.

Require Import if_assms.
Require Import sem_prop.
Require Import if_succ_gen.
Require Import if_common_lemmas.
Require Import spec_aux_defs.

Require Import mq_apispecs.
Require Import prt_apispecs.
Require Import equiv_prop. 

Require Import confidentiality_tactics.
Require Import hasrt_sat_preserve.

Set Keyed Unification.  

Lemma prio_preserved_tpi:
  forall O O' pr t, 
    task_prio_id O' pr t ->
    prio_preserved O O' ->
    task_prio_id O pr t. 
Proof.
  introv Htpi Hpp.
  unfold prio_preserved in Hpp.
  unfold prio_preserved_d in Hpp.
  specialize (Hpp (dom_for_prio pr) pr t (eq_refl _)).
  destruct Hpp as (Htpi_ & Htpi_').
  eapply Htpi_'; eauto. 
Qed.

Lemma prio_preserved_refl:
  forall O, prio_preserved O O. 
Proof.
  intros.
  unfolds.
  intros.
  unfolds.
  intros.
  split; auto.  
Qed. 

Lemma prio_preserved_sym:
  forall O1 O2, prio_preserved O1 O2 -> prio_preserved O2 O1. 
Proof.
  introv Hpp.
  unfold prio_preserved in *.
  intros.
  unfold prio_preserved_d in *.
  introv Hd.
  lets H__: Hpp Hd.
  destruct H__.
  split; eauto.
Qed. 

Lemma prio_tid_corr_ext:      
  forall O1 O2 O1' O2' t1 t2 pr t1' t2' pr', 
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    task_prio_id O1' pr' t1' ->
    task_prio_id O2' pr' t2' ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' -> 
    (t1 = t1' /\ t2 = t2' \/ t1 <> t1' /\ t2 <> t2').
Proof.
  introv Htpi1 Htpi2 Htpi1' Htpi2' Hpp1 Hpp2.
  casetac t1 t1' Ht Hf.
  - subst. 
    assert (t2 = t2').
    {
      casetac t2 t2' Ht Hf.
      - auto.
      - casetac pr pr' He Hne.
        +
          subst.
          lets Htpi2_: prio_preserved_tpi Htpi2' Hpp2.
          lets H'_: tid_unique Htpi2 Htpi2_.
          tryfalse.
        +
          lets Htpi1_: prio_preserved_tpi Htpi1' Hpp1. 
          lets Hf_: prio_unique Htpi1 Htpi1_.
          tryfalse.
    }
    subst.
    left; auto.
  -
    casetac pr pr' He Hne.
    +
      subst.
      lets Htpi1_: prio_preserved_tpi Htpi1' Hpp1. 
      lets H_: tid_unique Htpi1 Htpi1_.
      tryfalse.
    + 
      casetac t2 t2' Ht_ Hf_.
      *
        subst.
        lets Htpi2_: prio_preserved_tpi Htpi2' Hpp2.
        lets Hf_: prio_unique Htpi2 Htpi2_. 
        tryfalse.
      *
        right. split; auto.
Qed.       


Lemma code_equiv_upd2_preserve:
  forall td pr T1 T2 O1 O2 t1 t2 c1 c2 ke ks1 ks2 O1' O2' T1' T2' (* pr' *) c1' c2', 
    code_equiv_tskd td T1 T2 O1' O2' -> 
    get T1 t1 = Some (c1, (ke, ks1)) ->
    get T2 t2 = Some (c2, (ke, ks2)) ->
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' -> 
    cmd_equiv pr c1' c2' O1' O2' ->
    cont_equiv pr ks1 ks2 O1' O2' -> 
    T1' = set T1 t1 (c1', (ke, ks1)) ->
    T2' = set T2 t2 (c2', (ke, ks2)) -> 
    code_equiv_tskd td T1' T2' O1' O2'. 
Proof.
  introv Hcde Hg1 Hg2 Htpi1 Htpi2 Hpp1 Hpp2. 
  introv Hcmde Hconte HT1' HT2'.
  unfolds.
  introv Hd' Htpi1_ Htpi2_.
  lets Hcases: prio_tid_corr_ext Htpi1 Htpi2 Htpi1_ Htpi2_ Hpp1 Hpp2.
  destruct Hcases as [(Hteq1 & Hteq2) | (Htne1 & Htne2)].
  -
    subst.
    rewrite set_a_get_a.
    rewrite set_a_get_a.
    lets H_: prio_preserved_tpi Htpi1_ Hpp1.
    asserts_rewrite (pr0 = pr).
    { eapply prio_unique; eauto. }
    do 5 eexists.
    splits; eauto.    
  -
    rewrite HT1'.
    rewrite HT2'.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto.
Qed. 
    
Lemma code_equiv_upd2_preserve':
  forall td pr T1 T2 O1 O2 t1 t2 c1 c2 ke ks1 ks2 T1' T2' (* pr' *) c1' c2', 
    code_equiv_tskd td T1 T2 O1 O2 -> 
    get T1 t1 = Some (c1, (ke, ks1)) ->
    get T2 t2 = Some (c2, (ke, ks2)) ->
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    cmd_equiv pr c1' c2' O1 O2 ->
    cont_equiv pr ks1 ks2 O1 O2 -> 
    T1' = set T1 t1 (c1', (ke, ks1)) ->
    T2' = set T2 t2 (c2', (ke, ks2)) -> 
    code_equiv_tskd td T1' T2' O1 O2. 
Proof.
  introv Hcde Hg1 Hg2 Htpi1 Htpi2 Hd. 
  introv Hcmde Hconte HT1' HT2'.
  eapply code_equiv_upd2_preserve; eauto.
  apply prio_preserved_refl.
  apply prio_preserved_refl.
Qed.   


Definition hasrtsat_neq td (T1 T2: tasks) (O1 O2: osabst) t1 t2 := 
    (forall t1' t2' ke1' ks1' ke2' ks2' pr' c1_ c2_,
        t1' <> t1 ->
        t2' <> t2 ->
        get T1 t1' = Some (c1_, (ke1', ks1')) ->
        get T2 t2' = Some (c2_, (ke2', ks2')) ->
        dom_for_prio pr' = td -> 
        task_prio_id O1 pr' t1' ->
        task_prio_id O2 pr' t2' -> 
        ((forall cd1 cd2,
             c1_ = curs (hapi_code cd1) -> c2_ = curs (hapi_code cd2) -> 
             (head_asrt_sat pr' cd1 O1 /\ head_asrt_sat pr' cd2 O2))
         /\
           (forall cd1_ cd2_ ke1_ ks1_ ke2_ ks2_,
               ks1' = kevent (curs (hapi_code cd1_)) ke1_ ks1_ -> 
               ks2' = kevent (curs (hapi_code cd2_)) ke2_ ks2_ -> 
               (head_asrt_sat pr' cd1_ O1 /\ head_asrt_sat pr' cd2_ O2)))). 

Lemma code_equiv_upd2_preserve_st':
  forall td pr T1 T2 O1 O2 t1 t2 c1 c2 ke ks1 ks2 O1' O2' T1' T2' (* pr' *) c1' c2', 
    code_equiv_tskd td T1 T2 O1 O2 -> 
    get T1 t1 = Some (c1, (ke, ks1)) ->
    get T2 t2 = Some (c2, (ke, ks2)) ->
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' -> 
    cmd_equiv pr c1' c2' O1' O2' ->
    cont_equiv pr ks1 ks2 O1' O2' -> 
    hasrtsat_neq td T1 T2 O1' O2' t1 t2 -> 
    T1' = set T1 t1 (c1', (ke, ks1)) ->
    T2' = set T2 t2 (c2', (ke, ks2)) -> 
    code_equiv_tskd td T1' T2' O1' O2'.
Proof.
  introv Hce Hg1 Hg2 Htpi1 Htpi2 Hpp1 Hpp2. 
  introv Hcmde Hcnte Hhsat HT1' HT2'. 
  unfold hasrtsat_neq in Hhsat. 
  unfolds.
  introv Hd Htpi1' Htpi2'.
  lets Htpi1_: prio_preserved_tpi Htpi1' Hpp1.
  lets Htpi2_: prio_preserved_tpi Htpi2' Hpp2.
  lets Hcases: prio_tid_corr_ext Htpi1 Htpi2 Htpi1' Htpi2' Hpp1 Hpp2.
  destruct Hcases as [(Hteq1 & Hteq2) | (Htne1 & Htne2)].
  - subst.
    apply2 (task_prio_id O1 pr) (task_prio_id O1 pr0) prio_unique.
    do 2 (rewrite set_a_get_a).
    do 5 eexists.
    splits; eauto.    
  - subst T1'.
    subst T2'.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto.
    unfolds in Hce.
    rename t0 into t1_.
    rename t3 into t2_.
    lets H__: Hce Hd Htpi1_ Htpi2_.
    destruct H__ as (c1'_ & c2'_ & ke'_ & ks1'_ & ks2'_ & Hg1' & Hg2' & Hcmde' & Hcnte').
    do 5 eexists.
    splits; eauto.
    (* cmd_equiv *)
    unfolds.  
    unfolds in Hcmde'.
    destruct Hcmde' as [Hnknl | Hknl].
    left. auto.
    right.
    simpljoin.
    lets H__: Hhsat Hg1' Hg2' Htpi1' Htpi2'; eauto.
    destruct H__ as (Hcd & Hcnt).
    specializes Hcd; eauto. 
    destruct Hcd as (Hhsat1' & Hhsat2').
    do 2 eexists. splits; eauto.
    (* cont_equiv *)
    unfolds.
    unfolds in Hcnte'.
    destruct Hcnte' as [Hnkevt | Hkevt].
    left. auto.
    right.
    destruct Hkevt as (c1_ & c2_ & ke_ & ks_ & Hks1' & Hks2' & Hcmde'_).
    do 4 eexists; splits; eauto. 
    unfolds.
    unfolds in Hcmde'_.
    destruct Hcmde'_ as [Hnknl'_ | Hknl'_].
    left. auto.
    right.
    simpljoin.
    lets H__: Hhsat Hg1' Hg2' Htpi1' Htpi2'; eauto.
    destruct H__ as (Hcmd_ & Hcnt_).
    specializes Hcnt_; eauto.
    simpljoin. 
    do 2 eexists.
    splits; eauto.  
Qed.

Lemma cmd_equiv_abort:
  forall O1 O2 pr, 
    cmd_equiv pr (curs (hapi_code (ABORT))) (curs (hapi_code (ABORT))) O1 O2. 
Proof.
  intros. 
  unfold cmd_equiv.
  right.
  do 2 eexists.
  split; eauto. split; eauto.
  split. simpl; auto.
  split. simpl; auto.
  split. unfolds. introv Hvl1 Hvl2. simpl in Hvl1. tryfalse.
  unfolds. right.
  split. introv Hf. simpljoin; tryfalse.
  do 11 right.
  split; auto.
Qed. 

Lemma cmd_equiv_end:
  forall O1 O2 pr v, 
    cmd_equiv pr (curs (hapi_code (END v))) (curs (hapi_code (END v))) O1 O2. 
Proof.
  intros. 
  unfold cmd_equiv.
  right.
  do 2 eexists.
  splits; eauto.
  simpl; auto.
  simpl; auto.
  unfolds. introv Hf. simpl in Hf. tryfalse. 
  unfolds.
  left. eexists; split; eauto. 
Qed.   

Lemma data_equiv_schd_dom_equiv:
  forall O1 O2, 
    data_equiv_schd O1 O2 ->
    (forall td, (dom_cur_tsk O1 td <-> dom_cur_tsk O2 td))(* ) *). 
Proof.
  introv Hdes.
  unfolds in Hdes.
  simpljoin.
  intros.
  unfolds.
  unfold dom_cur_tsk.
  split.
  -
    introv Hex.
    simpljoin.
    match goal with
      H1: get O1 curtid = Some (oscurt ?x1), H2: get O1 curtid = Some (oscurt ?x2) |- _ => 
        assert (x1 = x2) by congruence; subst
    end.
    assert (Hexpr: exists pr, task_prio_id O1 pr x1).
    { eexists. eauto. }
    eapply H5 in Hexpr; eauto.
    simpljoin.
    exists x0 x.
    splits; auto. 
    symmetry.
    eapply H6; eauto. 
  -
    introv Hex.
    simpljoin.
    match goal with
      H1: get O2 curtid = Some (oscurt ?x1), H2: get O2 curtid = Some (oscurt ?x2) |- _ => 
        assert (x1 = x2) by congruence; subst
    end.
    assert (Hexpr: exists pr, task_prio_id O2 pr x1).
    { eexists; eauto. }
    apply H5 in Hexpr; eauto. 
    simpljoin.
    exists x x0.
    splits; auto.
Qed.   

Lemma veq_vlequiv: 
  forall v1 v2 cd1 cd2,
    get_hd_vl cd1 = Some (v1 :: nil) ->
    get_hd_vl cd2 = Some (v2 :: nil) ->
    v1 = v2 ->
    vl_equiv cd1 cd2. 
Proof.
  introv Hcd1 Hcd2 Hveq.
  unfolds.
  introv Hget1 Hget2 Hnth1 Hnth2.
  rewrite Hcd1 in Hget1; inverts Hget1.
  rewrite Hcd2 in Hget2; inverts Hget2.
  destruct i.
  - simpl in Hnth1, Hnth2.
    congruence. 
  - simpl in Hnth1, Hnth2.
    rewrite nth_error_nil in Hnth1.
    rewrite nth_error_nil in Hnth2. 
    tryfalse. 
Qed.

Lemma vlequiv_veq: 
  forall cd1 cd2 i1 i2, 
    vl_equiv cd1 cd2 ->
    get_hd_vl cd1 = Some (Vint32 i1 :: nil) ->
    get_hd_vl cd2 = Some (Vint32 i2 :: nil) ->
    i1 = i2.
Proof.
  introv Hvleq Hget1 Hget2.
  unfolds in Hvleq.
  lets H_: Hvleq Hget1 Hget2. 
  cut (Vint32 i1 = Vint32 i2).
  introv Heq; inverts Heq; auto. 
  eapply H_; eauto.
  instantiate (1:=0%nat). simpl. auto. simpl. auto. 
Qed.

Lemma vlequiv_veq': 
  forall cd1 cd2 i1 i2, 
    vl_equiv cd1 cd2 ->
    get_hd_vl cd1 = Some (Vint32 i1 :: nil) ->
    get_hd_vl cd2 = Some (Vint32 i2 :: nil) ->
    Vint32 i1 = Vint32 i2. 
Proof.
  introv Hvleq Hget1 Hget2.
  unfolds in Hvleq.
  lets H_: Hvleq Hget1 Hget2. 
  eapply H_; eauto.
  instantiate (1:=0%nat). simpl. auto. simpl. auto. 
Qed.

Lemma vl_equiv_end:
  vl_equiv (END Some (Vint32 Int.mone)) (END Some (Vint32 Int.mone)).
Proof.
  unfolds.
  introv Hg1 Hg2 Hn1 Hn2.
  simpl in Hg1. 
  tryfalse. 
Qed.

Lemma stmt_equiv_end:
  stmt_equiv (END Some (Vint32 Int.mone)) (END Some (Vint32 Int.mone)).
Proof.
  unfolds.
  left. 
  eexists; split; eauto. 
Qed. 

Lemma vl_equiv_nil: 
  forall c1 c2, 
    get_hd_vl c1 = Some nil -> 
    vl_equiv c1 c2.  
Proof.
  introv Hnil.
  introv Hg.
  rewrite Hnil in Hg.
  inverts Hg.
  introv _ Hf.
  rewrite nth_error_nil in Hf. 
  false. 
Qed.   

Lemma vlequiv_veq_ext: 
  forall (cd1 cd2 : spec_code) v1 v2, 
    vl_equiv cd1 cd2 ->
    get_hd_vl cd1 = Some (v1 :: nil) ->
    get_hd_vl cd2 = Some (v2 :: nil) ->
    v1 = v2.
Proof.
  introv Hve Hgv1 Hgv2.
  unfolds in Hve.
  lets H__: Hve Hgv1 Hgv2; eauto.
  eapply (H__ 0%nat); eauto.
Qed.       

Lemma join_upd_get_same: 
  forall (O O0 Of O0' O': osabst) x y, 
    get O x = Some y ->
    join O0 Of O ->
    get O0 x = get O0' x ->
    join O0' Of O' ->
    get O' x = Some y. 
Proof.
  introv Hg Hjo Hupd Hjo'.
  assert (Hcs: (exists z, get Of x = Some z) \/ get Of x = None).
  {
    destruct (get Of x) eqn: E.
    left; eexists; eauto.
    right; auto. 
  }
  destruct Hcs as [Hsome | Hnone].
  -
    simpljoin.
    assert (get O x = Some x0). { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O x).
    clear -Hjo' H.
    eapply join_get_get_r; eauto.  
  -
    assert (Hor: get O0 x = Some y \/ get Of x = Some y).
    { eapply join_get_or; eauto. }
    destruct Hor as [Ht | Hf].
    2: { rewrite Hf in Hnone. false. }
    rewrite Hupd in Ht.
    eapply join_get_get_l; eauto. 
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

Lemma tpi_upd_frm_preserved:
  forall O O' Of pr t O0 O0', 
    task_prio_id O pr t ->
    join O0 Of O -> 
    get O0 abstcblsid = get O0' abstcblsid ->
    join O0' Of O' -> 
    task_prio_id O' pr t.
Proof.
  introv Htpi Hjo Hupd Hjo'.
  unfold task_prio_id in *.
  simpljoin.
  lets H__: join_upd_get_same H.
  specializes H__; eauto.
  do 5 eexists.
  split; eauto. 
Qed. 

Lemma tpi_frm_ext: 
  forall O0 O Of t pr, 
    task_prio_id O0 pr t ->
    join O0 Of O ->
    task_prio_id O pr t. 
Proof.
  introv Htpi Hjo.
  unfold task_prio_id in *.
  simpljoin.
  do 5 eexists.
  split; eauto.
  eapply join_get_get_l; eauto. 
Qed.     

Lemma cde_prio_preserved_preserve2:
  forall td cst1 cst2 O1 O2 O1' O2', 
    client_data_equiv td cst1 cst2 O1 O2 -> 
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    client_data_equiv td cst1 cst2 O1' O2'. 
Proof.
  introv Hcde Hpp1 Hpp2.
  unfold client_data_equiv in *.
  simpljoin.
  do 6 eexists.
  splits; eauto.
  unfold local_envs_equiv in *.
  introv Hd Htpi1' Htpi2'.
  unfold prio_preserved in *.
  specialize (Hpp1 td).
  specialize (Hpp2 td).
  unfold prio_preserved_d in *.
  lets Heq1: Hpp1 t1 Hd. 
  lets Heq2: Hpp2 t2 Hd.
  apply Heq1 in Htpi1'.
  apply Heq2 in Htpi2'.
  eauto. 
Qed. 

Lemma knl_tsk_equiv_same_tls_preserve2:
  forall td O1 O2 O1' O2', 
    kernel_task_equiv td O1 O2 -> 
    get O1 abstcblsid = get O1' abstcblsid ->
    get O2 abstcblsid = get O2' abstcblsid -> 
    kernel_task_equiv td O1' O2'. 
Proof.
  introv Hkte Hgeq1 Hgeq2.
  unfold kernel_task_equiv in *.
  simpljoin.
  rewrite H in Hgeq1. 
  rewrite H0 in Hgeq2.
  symmetry in Hgeq1, Hgeq2.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  specializes H1; eauto.
  simpljoin.
  split.
  - 
    match goal with H: _ <-> _ |- _ => destruct H as (Hlr & Hrl) end.
    split.
    + introv Hex.
      destruct Hex as (t & Htpi1').
      assert (Htpi1: exists t, task_prio_id O1 pr t).
      {
        unfold task_prio_id in Htpi1'.
        unfold task_prio_id.
        simpljoin.
        l_rew21_inv1 (get O1' abstcblsid).
        do 6 eexists. split; eauto. 
      }
      apply Hlr in Htpi1.
      unfold task_prio_id in Htpi1.
      simpljoin.
      l_rew21_inv1 (get O2 abstcblsid).
      unfold task_prio_id.
      do 6 eexists.
      split; eauto. 
    + introv Hex.
      destruct Hex as (t & Htpi2').
      assert (Htpi2: exists t, task_prio_id O2 pr t).
      {
        unfold task_prio_id in Htpi2'.
        unfold task_prio_id.
        simpljoin.
        l_rew21_inv1 (get O2' abstcblsid).
        do 6 eexists. split; eauto. 
      }
      apply Hrl in Htpi2.
      unfold task_prio_id in Htpi2.
      simpljoin.
      l_rew21_inv1 (get O1 abstcblsid).
      unfold task_prio_id.
      do 6 eexists.
      split; eauto. 
  -
    introv Hg1 Hg2.
    eapply H2; eauto. 
Qed.                    

Lemma tidls_equiv_pp_preserve2: 
  forall tls1 tls2 O1 O2 O1' O2', 
    tidls_equiv tls1 tls2 O1 O2 ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    tidls_equiv tls1 tls2 O1' O2'.
Proof.
  introv Hte Hpp1 Hpp2.
  unfold tidls_equiv in *.
  unfold prio_preserved in *.
  unfold prio_preserved_d in *.
  simpljoin.
  split; auto.
  intro pr.
  specialize (H0 pr).
  destruct H0 as (Htpi1 & Htpi2).
  specialize (Hpp1 (dom_for_prio pr) pr).
  specialize (Hpp2 (dom_for_prio pr) pr).
  split.
  - introv Htpi1'.
    destruct Htpi1' as (t & Hin1 & Htpi1'_).
    specialize (Hpp1 t (eq_refl _)). apply Hpp1 in Htpi1'_.
    assert (Hex1: exists t, In t tls1 /\ task_prio_id O1 pr t).
    { eexists; split; eauto. }
    apply Htpi1 in Hex1.
    destruct Hex1 as (t_ & Hin2 & Htpi2_).
    eexists; split; eauto.
    specialize (Hpp2 t_ (eq_refl _)).
    apply Hpp2 in Htpi2_.
    auto. 
  - introv Htpi2'.
    destruct Htpi2' as (t & Hin2 & Htpi2'_).
    specialize (Hpp2 t (eq_refl _)). apply Hpp2 in Htpi2'_.
    assert (Hex2: exists t, In t tls2 /\ task_prio_id O2 pr t).
    { eexists; split; eauto. }
    apply Htpi2 in Hex2.
    destruct Hex2 as (t_ & Hin1 & Htpi1_).
    eexists; split; eauto.
    specialize (Hpp1 t_ (eq_refl _)).
    apply Hpp1 in Htpi1_.
    auto. 
Qed.      

Lemma cont_equiv_hsat_preserve: 
  forall pr ks1 ks2 O1 O2 O1' O2', 
    cont_equiv pr ks1 ks2 O1 O2 ->
    (forall ke1 ke2 ks1_ ks2_ cd1 cd2, 
        ks1 = kevent (curs (hapi_code cd1)) ke1 ks1_ ->
        ks2 = kevent (curs (hapi_code cd2)) ke2 ks2_ ->                             
        (head_asrt_sat pr cd1 O1' /\
           head_asrt_sat pr cd2 O2')) ->
    cont_equiv pr ks1 ks2 O1' O2'.
Proof.
  introv Hcnte Hall. 
  unfolds. unfolds in Hcnte.
  destruct Hcnte as [Hnev | Hev].
  left. auto.
  right. simpljoin. do 4 eexists. splits; eauto.
  unfolds.
  unfolds in H1.
  destruct H1 as [Hnknl | Hknl].
  -
    left. auto.
  -
    simpljoin.
    right.
    specializes Hall; eauto.     
    simpljoin.
    do 2 eexists.
    splits; eauto.
Qed.

Lemma tidls_equiv_rm_preserve2:
  forall ws1 ws2 O1 O2 pr0 t1 t2 O1' O2', 
    tidls_equiv ws1 ws2 O1 O2 ->
    In t1 ws1 ->
    In t2 ws2 -> 
    task_prio_id O1 pr0 t1 -> 
    task_prio_id O2 pr0 t2 ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' -> 
    distinct ws1 ->
    distinct ws2 ->
    tidls_equiv (remove_tid t1 ws1) (remove_tid t2 ws2) O1' O2'. 
Proof.
  introv Hte Hin1 Hin2 Htpi1 Htpi2 Hpp1 Hpp2 Hdt1 Hdt2.
  unfold tidls_equiv in *.
  destruct Hte as (Heqlen & Hallpr).
  split.
  - rewrite rm_len; auto.
    rewrite rm_len; auto.
  -
    intros. specialize (Hallpr pr).
    destruct Hallpr as (Hlr & Hrl).
    split; introv Hit.
    + 
      destruct Hit as (t & Hin1' & Htpi1').
      lets Hin1_: in_remove_in Hin1'; eauto.
      assert (Hex: exists t, In t ws1 /\ task_prio_id O1 pr t).
      {
        exists t. split; auto.
        eapply prio_preserved_tpi; eauto. 
      }
      apply Hlr in Hex. 
      destruct Hex as (t_ & Hin2_ & Htpi2_).
      exists t_.
      split.
      2: {
        apply prio_preserved_sym in Hpp2.
        eapply prio_preserved_tpi; eauto.
      }
      casetac t t1 Ht Hf.
      * subst.
        apply in_remove_tid_false in Hin1'. false.
      * casetac pr pr0 Htt Hff.
        ** subst.
           assert (task_prio_id O1 pr0 t).
           { eapply prio_preserved_tpi; eauto. }
           apply2 (task_prio_id O1) (task_prio_id O1) tid_unique.
           false.
        ** assert (Hneq: t_ <> t2).
           {
             introv Hf_. subst.
             apply2 (task_prio_id O2) (task_prio_id O2) prio_unique.
             tryfalse. 
           }
           eapply in_remove_tid'; eauto.
    +
      destruct Hit as (t & Hin2' & Htpi2').
      lets Hin2_: in_remove_in Hin2'; eauto.
      assert (Hex: exists t, In t ws2 /\ task_prio_id O2 pr t).
      {
        exists t. split; auto.
        eapply prio_preserved_tpi; eauto. 
      }
      apply Hrl in Hex. 
      destruct Hex as (t_ & Hin1_ & Htpi1_).
      exists t_.
      split.
      2: {
        apply prio_preserved_sym in Hpp1.
        eapply prio_preserved_tpi; eauto.
      }
      casetac t t2 Ht Hf.
      * subst.
        apply in_remove_tid_false in Hin2'. false.
      * casetac pr pr0 Htt Hff.
        ** subst.
           assert (task_prio_id O2 pr0 t).
           { eapply prio_preserved_tpi; eauto. }
           apply2 (task_prio_id O2) (task_prio_id O2) tid_unique.
           false.
        ** assert (Hneq: t_ <> t1).
           {
             introv Hf_. subst.
             apply2 (task_prio_id O1) (task_prio_id O1) prio_unique.
             tryfalse. 
           }
           eapply in_remove_tid'; eauto.                   
Qed.               

Lemma prio_preserved_tpieq_impl: 
  forall O1 O2 O1' O2' pr0, 
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    ((exists t, task_prio_id O1 pr0 t) <-> (exists t, task_prio_id O2 pr0 t)) ->
    ((exists t, task_prio_id O1' pr0 t) <-> (exists t, task_prio_id O2' pr0 t)). 
Proof.
  introv Hpp1 Hpp2 Htpieq.
  destruct Htpieq as (Hlr & Hrl).
  split.
  -
    introv Htpi1'.
    destruct Htpi1' as (t & Htpi1').
    assert (Hex: exists t, task_prio_id O1 pr0 t).
    { eexists. eapply prio_preserved_tpi; eauto.  }
    apply Hlr in Hex. 
    destruct Hex as (t_ & Htpi2).
    exists t_.
    eapply prio_preserved_tpi; eauto. 
    apply prio_preserved_sym; auto.
  -
    introv Htpi2'.
    destruct Htpi2' as (t & Htpi2').
    assert (Hex: exists t, task_prio_id O2 pr0 t).
    { eexists. eapply prio_preserved_tpi; eauto.  }
    apply Hrl in Hex. 
    destruct Hex as (t_ & Htpi1).
    exists t_.
    eapply prio_preserved_tpi; eauto. 
    apply prio_preserved_sym; auto.
Qed.             

Lemma tidls_equiv_cons_preserve2:
  forall ts1 ts2 t1 t2 O1 O2 O1' O2' pr, 
    tidls_equiv ts1 ts2 O1 O2 ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    tidls_equiv (t1::ts1) (t2::ts2) O1' O2'. 
Proof.
  introv Hte Hpp1 Hpp2 Htpi1 Htpi2.
  unfold tidls_equiv in *.
  destruct Hte as (Hleneq & Hall).
  split.
  simpl.
  congruence.
  intro pr0.
  specialize (Hall pr0).
  destruct Hall as (Hex1 & Hex2).
  split.
  -
    introv Hex1_.
    destruct Hex1_ as (t & Hin1 & Htpi1').
    simpl in Hin1.
    destruct Hin1 as [Hhd | Hintl].
    + subst t. 
      exists t2.
      split.
      simpl. left; auto.
      assert (task_prio_id O1 pr0 t1).
      { eapply prio_preserved_tpi; eauto. } 
      apply2 (task_prio_id O1) (task_prio_id O1) prio_unique.
      apply prio_preserved_sym in Hpp2.
      eapply prio_preserved_tpi; eauto.
    +
      assert (Hex: exists t, In t ts1 /\ task_prio_id O1 pr0 t).
      {
        exists t. split; auto.
        eapply prio_preserved_tpi; eauto. 
      }
      apply Hex1 in Hex.
      destruct Hex as (t_ & Hin2 & Htpi2_).
      exists t_.
      split.
      right. auto.
      apply prio_preserved_sym in Hpp2.
      eapply prio_preserved_tpi; eauto.
  -
    introv Hex2_.
    destruct Hex2_ as (t & Hin2 & Htpi2').
    simpl in Hin2.
    destruct Hin2 as [Hhd | Hintl].
    + subst t. 
      exists t1.
      split.
      simpl. left; auto.
      assert (task_prio_id O2 pr0 t2).
      { eapply prio_preserved_tpi; eauto. }
      apply2 (task_prio_id O2) (task_prio_id O2) prio_unique.
      apply prio_preserved_sym in Hpp1.
      eapply prio_preserved_tpi; eauto.
    +
      assert (Hex: exists t, In t ts2 /\ task_prio_id O2 pr0 t).
      {
        exists t. split; auto.
        eapply prio_preserved_tpi; eauto. 
      }
      apply Hex2 in Hex.
      destruct Hex as (t_ & Hin1 & Htpi1_).
      exists t_.
      split.
      right. auto.
      apply prio_preserved_sym in Hpp1.
      eapply prio_preserved_tpi; eauto.
Qed.

Lemma rv_Oeq: 
  forall vl O act v O', 
    ret_val vl O act (v, Some O') -> O = O'. 
Proof.
  introv Hrv.
  unfolds in Hrv.
  simpljoin.
  congruence. 
Qed. 
  
Lemma rv_veq:
  forall v O act v' O', 
    ret_val (v::nil) O act (v', Some O') -> v' = Some v. 
Proof.
  introv Hrv.
  unfolds in Hrv.
  simpljoin.
  congruence. 
Qed. 

Lemma cont_equiv_qref_preserve: 
  forall pr ks1 ks2 O1 O2 O1' O2', 
    cont_equiv pr ks1 ks2 O1 O2 ->
    mq_ref_preserved O1 O1' ->
    mq_ref_preserved O2 O2' ->
    qprt_preserved O1 O1' ->
    qprt_preserved O2 O2' -> 
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    get O1 cspaceid = get O1' cspaceid ->
    get O2 cspaceid = get O2' cspaceid -> 
    cont_equiv pr ks1 ks2 O1' O2'.
Proof.
  introv Hcnte Href1 Href2 Hqp1 Hqp2 Hdi1 Hdi2.
  introv Hpp1 Hpp2 Hcspeq1 Hcspeq2.
  eapply cont_equiv_hsat_preserve; eauto.
  introv Hks1_ Hks2_.
  subst ks1.
  subst ks2.
  unfolds in  Hcnte.
  destruct Hcnte as [Hnevt | Hevt].
  -
    simpljoin.
    false.
    apply H. do 3 eexists. eauto.
  -
    destruct Hevt as (c1 & c2 & ke & ks' & Hevt1 & Hevt2 & Hcmde).
    inverts Hevt1.
    inverts Hevt2.
    unfolds in Hcmde.
    destruct Hcmde as [Hf | Ht].
    +
      simpljoin.
      apply knl_api in H. tryfalse. 
    +
      simpljoin.
      inverts H. inverts H0.
      rename x into cd1. rename x0 into cd2.
      unfold stmt_equiv in *.
      destruct H4 as [Hend | Hnend].
      * simpljoin. split; simpl; auto.
      * destruct Hnend as
          (Hnn & [Hsend | [Hrecv | [Htrecv |
                                     [Hpost | [Hpend | [Hspost | [Haccept |
                                                [Hbufpost | [Hbufacc | [Hbufpend |
                                                                         [Hintr | Habt]]]]]]]]]]]).
        **
          unfold mqsend_equiv in *.
          simpljoin.
          split.                      
          eapply mqsend_qref_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply mqsend_qref_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.
        **
          unfold mqrecv_equiv in *.
          simpljoin.
          split.
          eapply mqrecv_qref_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply mqrecv_qref_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.
        **
          unfold mqtimedrecv_equiv in *.
          simpljoin.
          split.
          eapply mqtimedrecv_qref_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply mqtimedrecv_qref_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.
        **
          unfold qprtpost_equiv in *.
          simpljoin.
          split.
          eapply qprtpost_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply qprtpost_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.
        **
          unfold qprtpend_equiv in *.
          simpljoin.
          split.
          eapply qprtpend_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply qprtpend_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.
        **
          unfold sprtpost_equiv in *.
          simpljoin.
          split.
          eapply sprtpost_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply sprtpost_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.          
        **
          unfold prtaccept_equiv in *.
          simpljoin.
          split.
          eapply prtaccept_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply prtaccept_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.                    
        **
          unfold bufferpost_equiv in *.
          simpljoin.
          split.
          eapply bufferpost_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply bufferpost_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.
        **
          unfold bufferaccept_equiv in *.
          simpljoin.
          split.
          eapply bufferaccept_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply bufferaccept_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.
        **
          unfold bufferpend_equiv in *.
          simpljoin.
          split.
          eapply bufferpend_asrt_preserve; eauto.
          exists x x0. eexists. splits; eauto.
          eapply bufferpend_asrt_preserve; eauto.
          exists x x1. eexists. splits; eauto.
        **
          unfold intr_equiv in *.
          simpljoin.
          split.
          eapply intr_asrt_preserve; eauto.
          eapply intr_asrt_preserve; eauto.
        **
          simpljoin. split; simpl; auto. 
Qed.

Lemma stmt_equiv_qref_preserve:
  forall cd1 cd2 O1 O1' pr,
    stmt_equiv cd1 cd2 ->
    mq_ref_preserved O1 O1' ->
    qprt_preserved O1 O1' -> 
    dom_impl O1 O1' ->
    prio_preserved O1 O1' -> 
    get O1 cspaceid = get O1' cspaceid -> 
    head_asrt_sat pr cd1 O1 ->
    head_asrt_sat pr cd1 O1'. 
Proof.
  introv Hse Hmp Hqp Hdi Hpp Hcpideq Hhsat.
  unfolds in Hse.
  destruct Hse as [Hend | Hnend].
  - simpljoin. simpl; auto. 
  - destruct Hnend as
      (Hnn & [Hsend | [Hrecv | [Htrecv |
                                 [Hpost | [Hpend | [Hspost | [Haccept | 
                                            [Hbufpost | [Hbufacc | [Hbufpend | [Hintr | Habt]]]]]]]]]]]).
    + 
      unfold mqsend_equiv in *.
      simpljoin.
      eapply mqsend_qref_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +
      unfold mqrecv_equiv in *.
      simpljoin.
      eapply mqrecv_qref_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +
      unfold mqtimedrecv_equiv in *.
      simpljoin.
      eapply mqtimedrecv_qref_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +      
      unfold qprtpost_equiv in *.
      simpljoin.
      eapply qprtpost_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +
      unfold qprtpend_equiv in *.
      simpljoin.
      eapply qprtpend_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +
      unfold sprtpost_equiv in *.
      simpljoin.
      eapply sprtpost_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +
      unfold prtaccept_equiv in *.
      simpljoin.
      eapply prtaccept_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.      
    +
      unfold bufferpost_equiv in *.
      simpljoin.
      eapply bufferpost_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +
      unfold bufferaccept_equiv in *.
      simpljoin.
      eapply bufferaccept_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +
      unfold bufferpend_equiv in *.
      simpljoin.
      eapply bufferpend_asrt_preserve; eauto.
      exists x x0. eexists. splits; eauto.
    +      
      unfold intr_equiv in *.
      simpljoin.                    
      eapply intr_asrt_preserve; eauto.
    +
      simpljoin.
      simpl. auto. 
Qed.                     

Lemma eqdom_frm_domimpl:
  forall O10 O20 Of O1 O2,
    eqdomO O10 O20 ->
    join O10 Of O1 ->
    join O20 Of O2 ->
    dom_impl O1 O2.
Proof.
  introv Heqd Hjo1 Hjo2.
  unfolds in Heqd.
  destruct Heqd as (Heqd & Hall).
  unfolds in Heqd.
  destruct Heqd as (Himpl1 & Himpl2).
  unfold dom_impl in Himpl1.
  unfold dom_impl.
  intros.
  specialize (Himpl1 x).
  destruct (get O1 x) eqn: E.
  2: {
    assert (E0: get O10 x = None).
    { eapply join_get_none_rev1; eauto. }  
    rewrite E0 in Himpl1.
    assert (E0': get Of x = None).
    { clear Hjo2. eapply join_get_none_rev2; eauto. }
    assert (get O2 x = get Of x).
    eapply map_join_get_none; eauto.
    congruence. 
  }
  destruct a; 
    try (
        match type of E with
          get _ _ = Some ?e => 
            assert (Hor: get O10 x = Some e \/ get Of x = Some e)
            by (eapply join_get_or; eauto)
        end; 
        destruct Hor as [Hget1 | Hget2];
        [
          rewrite Hget1 in Himpl1;
          destruct Himpl1 as (y & Hget20); 
          eexists;
          eapply join_get_get_l; eauto |
          eexists;
          eapply join_get_get_r; eauto
      ]).
Qed.                

Lemma code_equiv_hsat_neq_st':
  forall pr td T1 T2 O1 O2 O1' O2' t1 t2, 
    code_equiv_tskd td T1 T2 O1 O2 ->
    mq_ref_preserved O1 O1' ->
    mq_ref_preserved O2 O2' ->
    qprt_preserved O1 O1' ->
    qprt_preserved O2 O2' -> 
    dom_impl O1 O1' ->
    dom_impl O2 O2' ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    get O1 cspaceid = get O1' cspaceid ->
    get O2 cspaceid = get O2' cspaceid -> 
    hasrtsat_neq td T1 T2 O1' O2' t1 t2.
Proof.
  introv Hce Hmr1 Hmr2 Hqp1 Hqp2 Hdi1 Hdi2 Htpi1 Htpi2.
  introv Hpp1 Hpp2 Hcspceq1 Hcspceq2.
  unfolds.
  introv Hneq1 Hneq2 Hg1 Hg2 Hd Htpi1' Htpi2'.
  lets Htpi1_: prio_preserved_tpi Htpi1' Hpp1; eauto.
  lets Htpi2_: prio_preserved_tpi Htpi2' Hpp2; eauto.
  unfolds in Hce.
  split.
  -
    introv Hc1 Hc2.
    lets H__: Hce Hd Htpi1_ Htpi2_.
    simpljoin.
    unfold get in *. unfold TasksMap in *.
    l_rew21_inv1 (TasksMod.get T1 t1').
    l_rew21_inv1 (TasksMod.get T2 t2').
    unfold cmd_equiv in *.
    match goal with H: _ \/ _ |- _ => inverts H end.
    + simpljoin.
      false. eapply knl_api; eauto.
    + simpljoin.
      do 2 (match goal with H: curs _ = curs _ |- _ => inverts H end).
      split.
      eapply stmt_equiv_qref_preserve; eauto.
      match goal with H: stmt_equiv _ _ |- _ => apply stmt_equiv_sym in H end.
      eapply stmt_equiv_qref_preserve; eauto. 
  -
    cut (cont_equiv pr' ks1' ks2' O1' O2').
    2: {
      lets H__: Hce Hd Htpi1_ Htpi2_.
      simpljoin.
      unfold get in *. unfold TasksMap in *.
      l_rew21_inv1 (TasksMod.get T1 t1').
      l_rew21_inv1 (TasksMod.get T2 t2').
      eapply cont_equiv_qref_preserve; eauto.
    }
    introv Hce'.
    unfolds in Hce'.
    introv Hks1' Hks2'.
    destruct Hce' as [Hf | Ht].
    +
      simpljoin.
      false.
      match goal with H: ~(_) |- _ => apply H; eexists; eauto end.
    +
      simpljoin.
      inverts Hks1'.  inverts Hks2'.
      unfold cmd_equiv in *.
      match goal with H: _ \/ _ |- _ => inverts H end.
      *
        simpljoin.
        false. eapply knl_api; eauto.
      *
        simpljoin.
        do 2 (match goal with H: curs _ = curs _ |- _ => inverts H end).
        split; auto. 
Qed. 

Lemma cap_equiv_preserve2: 
  forall td O1 O2 O1' O2', 
    cap_equiv td O1 O2 -> 
    get O1 cspaceid = get O1' cspaceid ->
    get O2 cspaceid = get O2' cspaceid -> 
    (forall idx objp, mq_ptr O1' idx objp <-> mq_ptr O1 idx objp) ->
    (forall idx objp, mq_ptr O2' idx objp <-> mq_ptr O2 idx objp) ->
    cap_equiv td O1' O2'. 
Proof.
  introv Hce Hgeq1 Hgeq2 Hio1 Hio2.
  unfold cap_equiv in *.
  simpljoin.
  rewrite H in Hgeq1. symmetry in Hgeq1.
  rewrite H0 in Hgeq2. symmetry in Hgeq2.
  do 2 eexists.
  splits; eauto.
  introv Hd.
  lets H__: H1 Hd.
  destruct H__ as (Hcc & Hoc).
  split; auto.
  introv Hid.
  lets H__: Hoc Hid; eauto.
  simpljoin.
  split.
  -
    split.
    + 
      introv Hex1'.
      destruct Hex1' as (p & Hmp1').
      eapply Hio1 in Hmp1'; eauto.
      assert (Hex1: exists p, mq_ptr O1 idx p).
      { eexists. eauto. }
      assert (Hex2: exists p, mq_ptr O2 idx p).
      { match goal with H1: ?P <-> _, Hex1: ?P |- _ =>  apply H1 in Hex1 end. auto. }
      destruct Hex2 as (p2 & Hp2).
      exists p2.
      eapply Hio2; eauto. 
    +
      introv Hex2'.
      destruct Hex2' as (p & Hmp2').
      eapply Hio2 in Hmp2'; eauto.
      assert (Hex2: exists p, mq_ptr O2 idx p).
      { eexists; eauto. }
      assert (Hex1: exists p, mq_ptr O1 idx p).
      { match goal with H1: _ <-> ?P, Hex2: ?P |- _ =>  apply H1 in Hex2 end. auto. }
      destruct Hex1 as (p1 & Hp1).
      exists p1.
      eapply Hio1; eauto.
  -    
    introv Hmp1' Hmp2'.
    eapply Hio1 in Hmp1'. eapply Hio2 in Hmp2'.
    eapply Hoc; eauto.
Qed.                 

Lemma kte_tidls_eq_gethwait_eq: 
  forall td O1 O2 tcbs1 tcbs2 wl1 wl2 t1 t2, 
    kernel_task_equiv td O1 O2 ->
    get O1 abstcblsid = Some (abstcblist tcbs1) ->
    get O2 abstcblsid = Some (abstcblist tcbs2) -> 
    GetHWait tcbs1 wl1 t1 ->
    GetHWait tcbs2 wl2 t2 ->
    (forall t, In t wl1 -> exists pr, task_prio_id O1 pr t /\ dom_for_prio pr = td) ->
    (forall t, In t wl2 -> exists pr, task_prio_id O2 pr t /\ dom_for_prio pr = td) ->
    tidls_equiv wl1 wl2 O1 O2 -> 
    (exists pr0, task_prio_id O1 pr0 t1 /\ task_prio_id O2 pr0 t2 /\ dom_for_prio pr0 = td).
Proof.
  introv Hkte Hgt1 Hgt2 Hgw1 Hgw2 Hid1 Hid2 Hte.
  unfold GetHWait in *.
  simpljoin.
  unfolds in Hkte.
  simpljoin.
  l_rew12_inv2 (get O1 abstcblsid).
  l_rew12_inv2 (get O2 abstcblsid).
  match goal with
    H: get tcbs1 t1 = Some (_, ?x1) |- _ => rename x1 into pr1
  end.
  match goal with
    H: get tcbs2 t2 = Some (_, ?x2) |- _ => rename x2 into pr2
  end.
  assert (Hor: pr1 = pr2 \/ Int.ltu pr1 pr2 = true \/ Int.ltu pr2 pr1 = true).
  {
    int auto.
    assert (Int.unsigned pr1 = Int.unsigned pr2)
      by auto with zarith.
    left.
    apply unsigned_inj; auto.
  }
  destruct Hor as [Heqp | [Hlt1 | Hlt2]].
  -
    subst pr2.
    exists pr1.
    split. unfolds. do 5 eexists; eauto.
    split. unfolds. do 5 eexists; eauto.
    specializes Hid1; eauto.
    unfold task_prio_id in *.
    simpljoin.
    l_rew12_inv2 (get O1 abstcblsid).
    match goal with
      H1: get _ t1 = _, H2: get _ t1 = _ |- _ => rewrite H1 in H2; inverts H2
    end.
    auto. 
  -
    destruct Hte as (Heqlen & Hallpr).
    assert (H__: exists t, In t wl2 /\ task_prio_id O2 pr1 t).
    {
      apply Hallpr. exists t1. split. auto. unfolds. do 5 eexists; eauto. 
    }
    destruct H__ as (t2' & Hin2 & Htpi2').
    casetac t2 t2' Ht Hf.
    + subst. 
      assert (Htpi2_: task_prio_id O2 pr2 t2').
      { unfolds. do 5 eexists; eauto. }
      apply2 (task_prio_id O2) (task_prio_id O2) prio_unique.
      false. int auto.
    + lets H__: H1 Hf Hin2.
      simpljoin.
      unfolds in Htpi2'.
      simpljoin.
      l_rew21_inv1 (get O2 abstcblsid).
      unfold get in *. unfold TcbMap in *.
      l_rew21_inv1 (TcbMod.get tcbs2 t2').
      false. int auto. 
  -
    destruct Hte as (Heqlen & Hallpr).
    assert (H__: exists t, In t wl1 /\ task_prio_id O1 pr2 t).
    {
      apply Hallpr. exists t2. split. auto. do 5 eexists; eauto. 
    }
    destruct H__ as (t1' & Hin1 & Htpi1').
    casetac t1 t1' Ht Hf.
    + subst. 
      assert (Htpi2_: task_prio_id O1 pr1 t1').
      { do 5 eexists; eauto. }
      apply2 (task_prio_id O1) (task_prio_id O1) prio_unique.
      false. int auto.
    + lets H__: H4 Hf Hin1.
      simpljoin.
      unfolds in Htpi1'.
      simpljoin.
      l_rew21_inv1 (get O1 abstcblsid).
      unfold get in *. unfold TcbMap in *.
      l_rew21_inv1 (TcbMod.get tcbs1 t1').
      false. int auto. 
Qed.             

Definition mq_ecbs_preserved O O' :=
  forall els els', 
    get O absecblsid = Some (absecblist els) ->
    get O' absecblsid = Some (absecblist els') ->
    (forall eid ms ml ts wl,
        get els eid = Some (absmsgq ms ml ts, wl) ->
        get els' eid = Some (absmsgq ms ml ts, wl)). 

Lemma knl_mq_equiv_preserve2: 
  forall td O1 O2 O1' O2', 
    kernel_mq_equiv td O1 O2 -> 
    get O1 absmqattrid = get O1' absmqattrid ->
    get O2 absmqattrid = get O2' absmqattrid ->  
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' -> 
    mq_ecbs_preserved O1 O1' -> 
    mq_ecbs_preserved O2 O2' ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    kernel_mq_equiv td O1' O2'. 
Proof.
  introv Hkme Hg1 Hg2 Hpp1 Hpp2 Hmp1 Hmp2.
  introv Hdi1 Hdi2.
  unfold kernel_mq_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O1 absmqattrid).
  l_rew21_inv1 (get O2 absmqattrid). 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hid.
  match goal with H: forall _, _ |- _ => lets H__: H Hid end.
  simpljoin. 
  split.
  - auto.
  - 
    introv Hg1' Hg2'.
    symmetry in Hg1.
    symmetry in Hg2.
    l_rew21_inv1 (get O1' absmqattrid).
    l_rew21_inv1 (get O2' absmqattrid).
    match goal with H: forall _, _ |- _ => lets H_: H Hg1' Hg2' end.
    unfold mq_equiv in *.
    simpljoin.
    do 8 eexists.
    split; eauto.
    split; eauto.
    match goal with H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]] end.
    + simpljoin. left. split; auto.
    + simpljoin. right; left. split; auto.
    + right; right.
      simpljoin.
      unfolds in Hdi1. specialize (Hdi1 absecblsid).
      match goal with H: get O1 absecblsid = _ |- _ => rewrite H in Hdi1 end.
      destruct Hdi1 as (els1' & Hge1').
      unfolds in Hdi2. specialize (Hdi2 absecblsid).
      match goal with H: get O2 absecblsid = _ |- _ => rewrite H in Hdi2 end.
      destruct Hdi2 as (els2' & Hge2').
      unfold mq_ed_equiv in *.
      simpljoin.
      match goal with
        H1: get O1 absecblsid = _, H2: get O1' absecblsid = _ |- _ =>
          lets H1_: Hmp1 H1 H2
      end.
      specializes H1_; eauto. 
      match goal with
        H1: get O2 absecblsid = _, H2: get O2' absecblsid = _ |- _ =>
          lets H2_: Hmp2 H1 H2
      end.
      specializes H2_; eauto. 
      do 7 eexists.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split.
      * do 4 eexists.
        split; eauto.
        split; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
      * eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma ibufs_equiv_preserve2: 
  forall td O1 O2 O1' O2', 
    ibufs_equiv td O1 O2 ->
    get O1' ibufsid = get O1 ibufsid ->
    get O2' ibufsid = get O2 ibufsid ->
    ibufs_equiv td O1' O2'.
Proof.
  introv Hibe Hg1 Hg2.
  unfolds.
  unfolds in Hibe.
  simpljoin. 
  do 2 eexists.
  splits; eauto.
  congruence.
  congruence. 
Qed. 

Lemma obufs_equiv_preserve2: 
  forall td O1 O2 O1' O2', 
    obufs_equiv td O1 O2 ->
    get O1' obufsid = get O1 obufsid ->
    get O2' obufsid = get O2 obufsid ->
    obufs_equiv td O1' O2'.
Proof.
  introv Hobe Hg1 Hg2.
  unfolds.
  unfolds in Hobe.
  simpljoin. 
  do 2 eexists.
  splits; eauto.
  congruence.
  congruence. 
Qed. 

Lemma bufs_equiv_preserve2: 
  forall td O1 O2 O1' O2', 
    bufs_equiv td O1 O2 ->
    get O1' ibufsid = get O1 ibufsid ->
    get O2' ibufsid = get O2 ibufsid ->
    get O1' obufsid = get O1 obufsid ->
    get O2' obufsid = get O2 obufsid ->
    bufs_equiv td O1' O2'.
Proof.
  intros.
  unfold bufs_equiv in *.
  simpljoin. 
  split.
  eapply ibufs_equiv_preserve2; eauto.
  eapply obufs_equiv_preserve2; eauto.          
Qed.


Lemma buffer_equiv_nupd_preserve2: 
  forall O1 O2 O1' O2' els1 els1' els2 els2' td, 
    buffer_equiv td O1 O2 -> 
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    get O1 absecblsid = Some (absecblist els1) ->
    get O1' absecblsid = Some (absecblist els1') ->
    get O2 absecblsid = Some (absecblist els2) ->
    get O2' absecblsid = Some (absecblist els2') -> 
    (forall eid, buf_in_dom eid td = true -> get els1' eid = get els1 eid) ->
    (forall eid, buf_in_dom eid td = true -> get els2' eid = get els2 eid) -> 
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hpp1 Hpp2 Hg1 Hg1' Hg2 Hg2' Hg11' Hg22'.
  unfold buffer_equiv in *.
  simpljoin.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  lets H__: H1 Hd; eauto.
  lets H1_: Hg11' Hd; eauto.
  lets H2_: Hg22' Hd; eauto.
  destruct H__ as (Hiff & Ha).
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  split.
  - rewrite H1_. rewrite H2_.
    auto.
  - introv Hge1' Hge2'.
    rewrite H1_ in Hge1'.
    rewrite H2_ in Hge2'.
    specializes Ha; eauto.
    destruct Ha as (Hmee & Hte).
    split.
    + unfold mq_ed_equiv in *.
      simpljoin.
      do 4 eexists.
      split; eauto. split; eauto.
      eapply tidls_equiv_pp_preserve2; eauto.
    + eapply tidls_equiv_pp_preserve2; eauto.
Qed.         

Lemma buffer_equiv_same_els_preserve2: 
  forall O1 O2 O1' O2' td, 
    buffer_equiv td O1 O2 -> 
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    get O1 absecblsid = get O1' absecblsid ->
    get O2 absecblsid = get O2' absecblsid ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hpp1 Hpp2 Hge11' Hge22'.
  unfold buffer_equiv in *.
  simpljoin.
  rewrite <- Hge11'.
  rewrite <- Hge22'.
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Hd.
  match goal with H: forall _, _ |- _ => lets Ha: H Hd end.
  destruct Ha as (Hiff & Ha).
  split.
  auto.
  introv Hg1 Hg2.
  lets Hb: Ha Hg1 Hg2; eauto.
  simpljoin.
  split.
  - unfold mq_ed_equiv in *.
    simpljoin.
    do 4 eexists.
    split; eauto.
    split; eauto.
    eapply tidls_equiv_pp_preserve2; eauto.
  - eapply tidls_equiv_pp_preserve2; eauto.
Qed.           

