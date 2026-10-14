Require Import base_tac. 
Require Import FunctionalExtensionality.
Require Import memory. 
Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import prt_apispecs. 
Require Import buffer_apispecs. 
Require Import osspecs. 
Require Import properties.
Require Import if_assms.
Require Import sem_prop.
Require Import equiv_sem_prop.
Require Import if_succ_gen.
Require Import if_common_lemmas.
Require Import mqsend_cproof.
Require Import mqrecv_cproof.
Require Import qprtpost_cproof.
Require Import sprtpost_cproof.
Require Import prtaccept_cproof.
Require Import qprtpend_cproof.
Require Import bufferpost_cproof.
Require Import bufferpend_cproof.
Require Import bufferaccept_cproof.
Require Import mqtdrecv_cproof.
Require Import confidentiality_lemmas.
Require Import equiv_prop. 
Require Import confidentiality_sched_proof.
Require Import nfl_obsr_equiv_lemmas.

Set Keyed Unification.

Ltac clr_redundant hyp1 hyp2 := 
  match type of hyp1 with
  | ?t1 => (
           match type of hyp2 with
           | ?t2 => unify t1 t2; clear hyp2 
           end
         )
  end.    

Lemma cstep_apistep_contra:
  forall pc spc d C C' C'' ge le M ge' le' M' O O' act,     
    no_common_fid pc spc -> 
    cstep pc d C (ge, le, M) C' (ge', le', M') ->
    hapistep spc C O C'' O' act ->
    False. 
Proof.
  introv Hncf Hcstep Hapistep.
  destruct C as (c & ke & ks).
  destruct C' as (c' & ke' & ks').
  lets Hnknl: cstep_not_knl_eval Hcstep.
  inverts Hapistep.
  inverts H1.
  inverts Hcstep.
  inverts H9.
  inverts H10.
  inverts H9.
  inverts H10.
  eapply Hncf. erewrite H8. introv Hf; tryfalse.
  eauto.
  rewrite H3. introv Hf; tryfalse.
  apply knl_api in Hnknl. tryfalse.
  apply knl_api in Hnknl. tryfalse.
  apply knl_api in Hnknl. tryfalse.
Qed.   

Lemma cstep_apistep_contra_ext:
  forall pc spc d c ke ks ke' ks' C' C'' ge le M ge' le' M' O O' act,     
    no_common_fid pc spc -> 
    cstep pc d (c, (ke, ks)) (ge, le, M) C' (ge', le', M') ->
    hapistep spc (c, (ke', ks')) O C'' O' act ->
    False. 
Proof.
  introv Hncf Hcstep Hapistep.
  destruct C' as (c'_ & ke'_ & ks'_).
  lets Hnknl: cstep_not_knl_eval Hcstep.
  inverts Hapistep.
  inverts H1.
  inverts Hcstep.
  inverts H9.
  inverts H10.
  inverts H9.
  inverts H10.
  eapply Hncf. erewrite H8. introv Hf; tryfalse.
  eauto.
  rewrite H3. introv Hf; tryfalse.
  apply knl_api in Hnknl. tryfalse.
  apply knl_api in Hnknl. tryfalse.
  apply knl_api in Hnknl. tryfalse.
Qed.   
  
Lemma cs_estep_nsstep: 
  forall c ks d c' ke' m m' pu c'' ks'' m'' m''', 
    ctrl_state_cond (c, (kenil, ks)) -> 
    estep d c kenil m c' ke' m' ->
    sstep pu d c ks m'' c'' ks'' m''' ->
    False. 
Proof.
  introv Hcs Hestep Hsstep.  
  unfolds in Hcs.
  destruct Hcs as (Hce & Hks).
  unfolds in Hce.
  destruct c.
  -
    inverts Hsstep.
  -
    destruct s;
      try (
          let hyp := fresh "h" in 
          match goal with
            H: ?P -> ?Q |- _ =>
              assert (h: P); [eapply nknl_cstmt; intro; simpljoin; tryfalse | idtac]
          end;
          apply Hce in hyp; 
          inverts Hestep; fail).
    inverts Hestep.
Qed.     

Lemma loadbytes_eq:
  forall n m1 m2 d b o, 
    get_dom_mem m1 d = get_dom_mem m2 d ->
    addr_in_dom (b, 0) d = true ->
    loadbytes m1 (b, o) n = loadbytes m2 (b, o) n.
Proof.
  induction n.
  -
    intros. simpl. auto.
  -
    introv Hdmeq Hindm.
    specialize (IHn m1 m2 d b (o+1) Hdmeq Hindm).
    unfold loadbytes.
    fold loadbytes.
    unfold get_dom_mem in Hdmeq.
    match type of Hdmeq with
      ?f = ?g => remember f as X; remember g as Y
    end.
    assert (Heq_: X (b, o) = Y (b, o)).
    { rewrite Hdmeq. auto. }
    rewrite HeqX in Heq_. rewrite HeqY in Heq_.
    assert (H_: addr_in_dom (b, 0) d = addr_in_dom (b, o) d) 
      by (eapply n_block_cross_part; eauto).
    rewrite <- H_ in *.
    rewrite Hindm in Heq_.
    rewrite Heq_.
    destruct (get m2 (b, o)) eqn: E.
    + 
      rewrite E. destruct p. 
      rewrite E.
      rewrite IHn.
      auto.
    +
      rewrite E. rewrite E.
      auto.
Qed.   

Lemma load_pt_eq: 
  forall m1 m2 t b o v1 v2 d, 
    get_dom_mem m1 d = get_dom_mem m2 d -> 
    load_pt t m1 (b, o) d = Some v1 -> 
    load_pt t m2 (b, o) d = Some v2 ->
    v1 = v2.
Proof.
  introv Hmeq Hld1 Hld2. 
  unfold load_pt in *.
  destruct (addr_in_dom (b, o) d) eqn: E.
  2: { tryfalse. }
  destruct t;
    try(
        unfold loadm in *; 
        assert (Hidm: addr_in_dom (b, 0) d = true) 
          by (erewrite n_block_cross_part; eauto); 
        lets H_: loadbytes_eq Hmeq Hidm; 
        rewrite H_ in Hld1; 
        rewrite Hld1 in Hld2; 
        inverts Hld2; 
        auto; fail).
  congruence.
Qed. 

Lemma local_envs_equiv_local_preserve:
  forall d ces1 ces2 t1 t2 le1 le2 O1 O2, 
    local_envs_equiv d ces1 ces2 O1 O2 ->
    get ces1 t1 = Some le1 -> 
    get ces2 t2 = Some le2 ->
    local_envs_equiv d (set ces1 t1 le1) (set ces2 t2 le2) O1 O2. 
Proof.
  introv Heq Hget1 Hget2.
  unfold local_envs_equiv in *.
  introv Hd Htpi1 Htpi2.
  lets H_: Heq Hd Htpi1 Htpi2.
  asserts_rewrite (set ces1 t1 le1 = ces1).
  { eapply get_set_same; eauto. }
  asserts_rewrite (set ces2 t2 le2 = ces2).
  { eapply get_set_same; eauto. }
  auto.
Qed.   
  
Lemma client_data_equiv_local_preserve: 
  forall d ges1 ges2 ces1 ces2 m1 m2 O1 O2 le1 le2 t1 t2, 
    client_data_equiv d (ges1, ces1, m1) (ges2, ces2, m2) O1 O2 ->
    get ces1 t1 = Some le1 ->
    get ces2 t2 = Some le2 ->
    client_data_equiv d (ges1, set ces1 t1 le1, m1) (ges2, set ces2 t2 le2, m2) O1 O2.
Proof.
  introv Hcde Hget1 Hget2.
  unfold client_data_equiv in *.
  simpljoin.
  repeat eexists; auto.
  unfold local_envs_equiv in *.
  introv Hd Htpi1 Htpi2.
  lets H_: H2 Hd Htpi1 Htpi2.
  assert (Heq1: set x1 t1 le1 = x1). { eapply get_set_same; eauto. }
  assert (Heq2: set x2 t2 le2 = x2). { eapply get_set_same; eauto. } 
  rewrite Heq1. rewrite Heq2. 
  auto.
Qed.   

Lemma client_data_equiv_same_le_upd_preserve:
  forall d ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 pr t1 t2 le', 
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 -> 
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 -> 
    dom_for_prio pr = d -> 
    client_data_equiv d (ges1, set cenvs1 t1 le', M1) (ges2, set cenvs2 t2 le', M2) O1 O2. 
Proof.
  introv Hcde Htpi1 Htpi2 Hd.
  unfold client_data_equiv in *.
  simpljoin.
  repeat eexists; eauto.
  unfold local_envs_equiv in *.
  introv Hdeq Htpi1' Htpi2'.
  lets H_: H2 Hdeq Htpi1' Htpi2'.
  casetac t1 t0 Heq Hneq.
  -
    subst.
    lets Hteq1: prio_unique Htpi1 Htpi1'.
    subst.
    lets Hteq2:  tid_unique Htpi2 Htpi2'.
    subst.
    rewrite set_a_get_a. rewrite set_a_get_a.
    auto.
  -
    assert (Hneq': t2 <> t3). 
    {
      casetac pr pr0 Hpeq Hnpeq.
      - subst.
        lets Hf: tid_unique Htpi1 Htpi1'. tryfalse.
      - casetac t2 t3 Ht Hf.
        + subst.  lets Hff: prio_unique Htpi2 Htpi2'. tryfalse.
        + auto.
    }
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto.
Qed.      

Lemma prio_tid_corr:              
  forall O1 O2 t1 t2 pr t1' t2' pr', 
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    task_prio_id O1 pr' t1' ->
    task_prio_id O2 pr' t2' ->
    (t1 = t1' /\ t2 = t2' \/ t1 <> t1' /\ t2 <> t2').
Proof.
  introv Htpi1 Htpi2 Htpi1' Htpi2'.
  casetac t1 t1' Ht Hf.
  - subst. 
    assert (t2 = t2').
    {
      casetac t2 t2' Ht Hf.
      - auto.
      - casetac pr pr' He Hne.
        + subst. 
          lets H'_: tid_unique Htpi2 Htpi2'.
          tryfalse.
        + lets Hf_: prio_unique Htpi1 Htpi1'.
          tryfalse.
    }
    subst.
    left; auto.
  -
    casetac pr pr' He Hne.
    + subst.
      lets H_: tid_unique Htpi1 Htpi1'. tryfalse.
    + 
      casetac t2 t2' Ht_ Hf_.
      * subst.
        lets Hf_: prio_unique Htpi2 Htpi2'.
        tryfalse.
      * right. split; auto.
Qed.       

Lemma local_envs_same_upd_eq:
  forall d ces1 ces2 O1 O2 t1 t2 pr le, 
    local_envs_equiv d ces1 ces2 O1 O2 ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    local_envs_equiv d (set ces1 t1 le) (set ces2 t2 le) O1 O2. 
Proof.
  introv Hlee Htpi1 Htpi2.
  unfold local_envs_equiv in *.
  introv Hd' Htpi1' Htpi2'.
  lets H_: Hlee Hd' Htpi1' Htpi2'.
  lets Htc: prio_tid_corr Htpi1 Htpi2 Htpi1' Htpi2'.
  destruct Htc.
  - simpljoin.
    rewrite set_a_get_a. rewrite set_a_get_a.
    auto.
  - simpljoin.
    rewrite set_a_get_a'; eauto. 
    rewrite set_a_get_a'; eauto.
Qed.     

Lemma client_data_equiv_same_le_upd_preserve_ext: 
  forall (d d0: taskdom) (ges1 ges2: taskdom -> env) (cenvs1 cenvs2: cltenvs)
         (M1 M2: mem) (O1 O2: osabst) (pr: priority) (t1 t2: tid) (le': env),  
    client_data_equiv d0 (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d ->
    client_data_equiv d0 (ges1, set cenvs1 t1 le', M1) (ges2, set cenvs2 t2 le', M2) O1 O2. 
Proof.
  introv Hcde0 Htpi1 Htpi2 Hd.
  unfold client_data_equiv.
  do 6 eexists. split; eauto. split; eauto.
  unfolds in Hcde0.
  destruct Hcde0 as (ges1_ & ges2_ & ces1_ & ces2_ & m1_ & m2_ & Hcj).
  destructs Hcj.
  inverts H. inverts H0.
  split; auto.
  split. eapply local_envs_same_upd_eq; eauto.
  auto.
Qed.   

Lemma client_data_equiv_alloc_preserve: 
  forall d ges1 ges2 cenvs1 cenvs2 pr M1 M2 O1 O2 le1 le2 le1' le2' M1' M2' t1 t2 x tp, 
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    dom_for_prio pr = d -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    alloc_pt x tp le1 M1 le1' M1' d ->
    alloc_pt x tp le2 M2 le2' M2' d ->
    client_data_equiv d (ges1, set cenvs1 t1 le1', M1') (ges2, set cenvs2 t2 le2', M2') O1 O2.  
Proof.
  introv Hcde Hd Htpi1 Htpi2 Hget1 Hget2 Halc1 Halc2.
  unfold client_data_equiv in *.
  simpljoin.
  assert (le1 = le2).
  {
    unfold local_envs_equiv in H2. 
    lets H_: H2 Htpi1 Htpi2. auto.
    congruence.
  }
  subst.
  lets H_: alloc_det H3 Halc1 Halc2.
  destruct H_ as (Heqle & Hdmeq).
  repeat eexists; eauto.
  {
  subst.
  unfold local_envs_equiv in *.
  introv Hdeq Htpi1' Htpi2'.
  casetac t1 t0 Heq1 Hneq1.
  -  subst.
     lets Hpreq: prio_unique Htpi1 Htpi1'.
     subst.
     casetac t2 t3 Heq2 Hneq2.
     + subst.
       rewrite set_a_get_a. rewrite set_a_get_a.
       auto.
     + lets Hf: tid_unique Htpi2 Htpi2'.
       tryfalse.
  - casetac pr pr0 Hpreq Hprneq.
    + subst.
      lets Hf: tid_unique Htpi1 Htpi1'.
      tryfalse.
    + casetac t2 t3 Heq2 Hneq2.
      * subst.  lets Hf: prio_unique Htpi2 Htpi2'. tryfalse.
      * rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.
  }
Qed. 

Lemma get_dom_mem_allocb_eq:
  forall n b i d d0 m m',
    addr_in_dom (b, i) d = true ->
    allocb m b i n = m' ->
    d <> d0 ->
    get_dom_mem m d0 = get_dom_mem m' d0.
Proof.
  induction n;
    introv Haid Halc Hneq.
  -
    simpl in Halc.
    subst. auto.
  -
    simpl in Halc.
    remember (allocb m b (i + 1) n) as m''.
    symmetry in Heqm''.
    assert (Haid': addr_in_dom (b, i+1) d = true).
    { erewrite n_block_cross_part in Haid. eauto. }
    lets H_: IHn Haid' Heqm'' Hneq.
    assert (get_dom_mem m'' d0 = get_dom_mem m' d0).
    {
      unfolds.
      eapply functional_extensionality.
      intro a.
      destruct (addr_in_dom a d0) eqn: E.
      - rewrite <- Halc.
        casetac (b, i) a He Hne.
        + subst.
          lets Hf: dom_disj_addrs Hneq Haid E.
          tryfalse.
        + rewrite set_a_get_a'; eauto.
      - auto.
    }
    congruence.
Qed.

Lemma get_dom_mem_alloc_eq:
  forall x tp le M le' M' d d0,
    alloc_pt x tp le M le' M' d ->
    d <> d0 ->
    get_dom_mem M d0 = get_dom_mem M' d0.
Proof.
  introv Halcp Hneq.
  unfolds in Halcp.
  simpljoin.
  remember (allocb M x0 0 (typelen tp)) as m'.
  eapply get_dom_mem_allocb_eq; eauto.
Qed.


Lemma client_data_equiv_alloc_preserve_ext: 
  forall d d0 ges1 ges2 cenvs1 cenvs2 pr M1 M2 O1 O2 le1 le2 le1' le2' M1' M2' t1 t2 x tp,     
    client_data_equiv d0 (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->

    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 -> 
    dom_for_prio pr = d -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    alloc_pt x tp le1 M1 le1' M1' d ->
    alloc_pt x tp le2 M2 le2' M2' d ->

    client_data_equiv d0 (ges1, set cenvs1 t1 le1', M1') (ges2, set cenvs2 t2 le2', M2') O1 O2.  
Proof.
  introv Hcde0 Hcde Hd Htpi1 Htpi2 Hget1 Hget2 Halc1 Halc2.
  casetac d d0 Ht Hf.
  - subst. 
    eapply client_data_equiv_alloc_preserve; eauto.
  -
    unfold client_data_equiv.
    do 6 eexists.
    split; eauto.
    split; eauto.
    splits.
    +
      unfold client_data_equiv in Hcde0.
      simpljoin.
      auto.
    +
      assert (le1 = le2).
      {
        unfolds in Hcde. simpljoin.
        unfold local_envs_equiv in H2.
        lets H_: H2 Htpi1 Htpi2. auto.
        congruence.
      }
      subst.
      unfolds in Hcde. simpljoin.
      lets H'_: alloc_det H3 Halc1 Halc2.
      destruct H'_ as (Heqle & Hdmeq).
      subst.
      clear -Hcde0 Htpi1 Htpi2.
      unfolds in Hcde0. simpljoin.
      eapply local_envs_same_upd_eq; eauto.
    +
      lets H1_: get_dom_mem_alloc_eq Halc1 Hf.
      lets H2_: get_dom_mem_alloc_eq Halc2 Hf.
      unfolds in Hcde0.
      simpljoin.
      congruence.
Qed.          
  
Lemma cde_alloc_le'_eq: 
  forall d ges1 ges2 cenvs1 cenvs2 pr M1 M2 O1 O2 le1 le2 le1' le2' M1' M2' t1 t2 x tp, 
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    dom_for_prio pr = d -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    alloc_pt x tp le1 M1 le1' M1' d ->
    alloc_pt x tp le2 M2 le2' M2' d ->
    le1' = le2'.
Proof.
  introv Hcde Hd Htpi1 Htpi2 Hget1 Hget2 Halc1 Halc2. 
  unfold client_data_equiv in *.
  simpljoin.
  assert (le1 = le2).
  {
    unfold local_envs_equiv in H2. 
    lets H_: H2 Htpi1 Htpi2. auto.
    congruence.
  }
  subst.
  lets H_: alloc_det H3 Halc1 Halc2.
  destruct H_; auto.
Qed.   

Lemma cde_lenv_eq:
  forall ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 pr d t1 t2 le1 le2,  
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    le1 = le2.
Proof.   
  introv Hcde Htpi1 Htpi2 Hd Hget1 Hget2.
  unfold client_data_equiv in Hcde.
  simpljoin.
  unfold local_envs_equiv in H2.
  specialize (H2 pr (eq_refl _) t1 t2 Htpi1 Htpi2).
  congruence.
Qed. 
  
Lemma cde_lenv_get_var_eq:
  forall ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 pr d t1 t2 le1 le2 x,  
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    get le1 x = get le2 x.
Proof.
  introv Hcde Htpi1 Htpi2 Hd Hget1 Hget2.
  unfold client_data_equiv in Hcde.
  simpljoin.
  unfold local_envs_equiv in H2.
  specialize (H2 pr (eq_refl _) t1 t2 Htpi1 Htpi2).
  congruence.
Qed. 

Lemma cde_evalval_eq:
  forall x ge t1 t2 ces1 ces2 le1 le2 m1 m2 v1 v2 d pr O1 O2, 
    local_envs_equiv d ces1 ces2 O1 O2 -> 
    get_dom_mem m1 d = get_dom_mem m2 d -> 
    get ces1 t1 = Some le1 ->
    get ces2 t2 = Some le2 ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    evalval (evar x) (ge, le1, m1) d = Some v1 ->
    evalval (evar x) (ge, le2, m2) d = Some v2 ->
    v1 = v2.
Proof.
  introv Hleq Hdomeq Hle1 Hle2 Htpi1 Htpi2 Hd Hv1 Hv2.
  unfold local_envs_equiv in Hleq.
  lets H_: Hleq Hd Htpi1 Htpi2.
  rewrite Hle1 in H_.
  rewrite Hle2 in H_. 
  inverts H_.
  unfold evalval in *.
  simpl in Hv1.
  simpl in Hv2.
  destruct (get le2 x) eqn: E1.
  - 
    destruct p.
    eapply load_pt_eq; eauto.
  - 
    destruct (get ge x) eqn: E.
    destruct p.
    eapply load_pt_eq; eauto.
    tryfalse.
Qed.     

Lemma cde_var_addr_eq: 
  forall ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 pr d t1 t2 le1 le2 x v1 v2,  
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    evalval (eaddrof (evar x)) (ges1 d, le1, M1) d = Some v1 -> 
    evalval (eaddrof (evar x)) (ges2 d, le2, M2) d = Some v2 ->
    v1 = v2.
Proof.
  introv Hcde Htpi1 Htpi2 Hd Hget1 Hget2.
  introv Hval1 Hval2. 
  simpl in Hval1.
  simpl in Hval2.
  lets Hleeq_: cde_lenv_get_var_eq Hcde Htpi1 Htpi2 Hd.
  lets Hleeq: Hleeq_ Hget1 Hget2. clear Hleeq_.
  rewrite Hleeq in Hval1.
  destruct (get le2 x) eqn: E.
  + 
    rewrite E in Hval1. destruct p. inverts Hval1. inverts Hval2. 
    auto. 
  +
    rewrite E in Hval1.
    assert (Hgeq: get (ges1 d) x = get (ges2 d) x).
    { unfold client_data_equiv in Hcde. simpljoin. congruence. }
    rewrite Hgeq in Hval1.
    destruct (get (ges2 d) x) eqn: E'.
    *  destruct p.
       inverts Hval1; inverts Hval2; auto.
    * tryfalse. 
Qed.

Lemma cde_evaltype_eq: 
  forall e d ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 pr t1 t2 le1 le2 tp1 tp2, 
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    evaltype e (ges1 d, le1, M1) = Some tp1 ->
    evaltype e (ges2 d, le2, M2) = Some tp2 ->
    tp1 = tp2. 
Proof.
  induction e;
    introv Hcde Htpi1 Htpi2 Hd Hget1 Hget2 Het1 Het2; 
    try (simpl evaltype in *; tryfalse; congruence; fail).
  - 
    simpl evaltype in *.
    assert (Heq: get le1 v = get le2 v).
    { eapply cde_lenv_get_var_eq; eauto. }
    rewrite Heq in Het1.
    destruct (get le2 v) eqn: E.
    destruct p.
    inverts Het1; inverts Het2; auto.
    assert (Heq_: get (ges1 d) v = get (ges2 d) v).
    { unfold client_data_equiv in Hcde; simpljoin; congruence. }
    rewrite Heq_ in Het1.
    destruct (get (ges2 d) v) eqn: E'.
    destruct p. 
    congruence. 
    tryfalse. 
  -
    simpl evaltype in *.
    destruct (evaltype e (ges1 d, le1, M1)) eqn: E1; tryfalse. 
    + destruct (evaltype e (ges2 d, le2, M2)) eqn: E2; tryfalse. 
      rename t into tp1'. rename t0 into tp2'.
      assert (tp1' = tp2'). { eapply IHe; eauto. }
      congruence.
  -
    simpl evaltype in *.
    destruct (evaltype e1 (ges1 d, le1, M1)) eqn: E1; tryfalse.
    + destruct (evaltype e1 (ges2 d, le2, M2)) eqn: E2; tryfalse. 
      destruct (evaltype e2 (ges1 d, le1, M1)) eqn: E1'; tryfalse.
      destruct (evaltype e2 (ges2 d, le2, M2)) eqn: E2'; tryfalse.
      assert (t = t0). { eapply IHe1; eauto. }
      assert (t3 = t4). { eapply IHe2; eauto. }
      congruence.
  -
    simpl evaltype in *.
    destruct (evaltype e (ges1 d, le1, M1)) eqn: E1; tryfalse.
    destruct (evaltype e (ges2 d, le2, M2)) eqn: E2; tryfalse.
    destruct t eqn: E1'; tryfalse.
    destruct t0 eqn: E2'; tryfalse.
    inverts Het1. inverts Het2. 
    assert (Tptr tp1 = Tptr tp2).
    { eapply IHe; eauto. }
    inverts H. auto.
  -
    simpl evaltype in *.
    destruct e eqn: E; tryfalse.
    +
      destruct (evaltype (evar v) (ges1 d, le1, M1)) eqn: E1; tryfalse.
      destruct (evaltype (evar v) (ges2 d, le2, M2)) eqn: E2; tryfalse.
      inverts Het1. inverts Het2.
      assert (t = t0). { eapply IHe; eauto. }
      congruence.
    +
      destruct (evaltype (ederef e0) (ges1 d, le1, M1)) eqn: E1; tryfalse.
      destruct (evaltype (ederef e0) (ges2 d, le2, M2)) eqn: E2; tryfalse.
      * 
        assert (t = t0). { eapply IHe; eauto. }
        subst.
        simpl in E1. simpl in E2.
        destruct (evaltype e0 (ges1 (dom_for_prio pr), le1, M1)) eqn: E1'; tryfalse.
        destruct (evaltype e0 (ges2 (dom_for_prio pr), le2, M2)) eqn: E2'; tryfalse.
        destruct t eqn: E1''; tryfalse. 
        destruct t3 eqn: E2''; tryfalse.
        inverts E1; inverts E2.
        rewrite Het1 in Het2. inverts Het2; auto.
      *
        simpl in E2. 
        destruct (evaltype e0 (ges2 d, le2, M2)) eqn: E2'; tryfalse. 
        destruct t0 eqn: E2''; tryfalse. 
      *
        simpl in E1.
        destruct (evaltype e0 (ges1 d, le1, M1)) eqn: E1'; tryfalse.
        destruct t eqn: E1''; tryfalse.
    +
      destruct (evaltype (efield e0 i) (ges1 d, le1, M1)) eqn: E1; tryfalse.
      destruct (evaltype (efield e0 i) (ges2 d, le2, M2)) eqn: E2; tryfalse.
      inverts Het1; inverts Het2.
      assert (t = t0). { eapply IHe; eauto. }
      congruence.
    +
      destruct (evaltype (earrayelem e0_1 e0_2) (ges1 d, le1, M1)) eqn: E1; tryfalse.
      destruct (evaltype (earrayelem e0_1 e0_2) (ges2 d, le2, M2)) eqn: E2; tryfalse.
      inverts Het1; inverts Het2.
      assert (t = t0). { eapply IHe; eauto. }
      congruence.
  -
    simpl in Het1, Het2.
    destruct (evaltype e (ges1 d, le1, M1)) eqn: E1; tryfalse. 
    destruct (evaltype e (ges2 d, le2, M2)) eqn: E2; tryfalse.
    destruct t; destruct t0; tryfalse.
    assert (Hteq: Tstruct i0 d0 = Tstruct i1 d1).
    { eapply IHe; eauto. }
    inverts Hteq.
    congruence.
  -
    simpl in Het1, Het2.
    destruct (evaltype e (ges1 d, le1, M1)) eqn: E1; tryfalse. 
    destruct (evaltype e (ges2 d, le2, M2)) eqn: E2; tryfalse.
    destruct t0; tryfalse; 
    destruct t; tryfalse; 
      destruct t3; tryfalse;
      try (inverts Het1; inverts Het2; auto; fail). 
  -
    simpl in Het1, Het2. 
    destruct (evaltype e1 (ges1 d, le1, M1)) eqn: E1;
      destruct (evaltype e1 (ges2 d, le2, M2)) eqn: E1'; tryfalse. 
    destruct t; destruct t0; tryfalse;
    destruct (evaltype e2 (ges1 d, le1, M1)) eqn: E2;
      destruct (evaltype e2 (ges2 d, le2, M2)) eqn: E2'; tryfalse.
    destruct t3; destruct t4; tryfalse; 
      try (assert (Heq: Tptr t = Tptr t0) by (eapply IHe1; eauto); inverts Heq; congruence; fail). 
    destruct t3; destruct t4; tryfalse;
      try (assert (Hf: Tptr t = Tarray t0 n) by (eapply IHe1; eauto); tryfalse; fail).
    destruct t4; tryfalse; 
      try (assert (Hf: Tarray t n = Tptr t0) by (eapply IHe1; eauto); tryfalse; fail). 
    assert (He: Tarray t n = Tarray t0 n0) by (eapply IHe1; eauto).
    inverts He.
    destruct t3; destruct t4; tryfalse; try congruence.
Qed. 

Lemma expr_no_cross_read: 
  forall d pr ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 t1 t2 c ke le1 le2 c1' c2' ke1' ke2' le1' le2' M1' M2', 
    estep d c ke (ges1 d, le1, M1) c1' ke1' (ges1 d, le1', M1') ->
    estep d c ke (ges2 d, le2, M2) c2' ke2' (ges2 d, le2', M2') ->
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    (c1' = c2' /\ ke1' = ke2' /\ 
       client_data_equiv d
         (ges1, set cenvs1 t1 le1', M1') (ges2, set cenvs2 t2 le2', M2') O1 O2).
Proof.
  introv Hstep1 Hstep2 Hce Htpi1 Htpi2 Hdom Hct1 Hct2. 
  inverts Hstep1; inverts Hstep2; 
    try (
        splits; auto; 
        assert (Heq1: set cenvs1 t1 le1' = cenvs1) by (eapply get_set_same; eauto);
        assert (Heq2: set cenvs2 t2 le2' = cenvs2) by (eapply get_set_same; eauto); 
        rewrite Heq1; rewrite Heq2; 
        auto; fail);
    try (
        splits; auto; 
        [ match goal with
            H1: evaltype _ (ges1 _, _, _) = Some ?t1, H2: evaltype _ (ges2 _, _, _) = Some ?t2 |- _ =>
              assert (Heqt: t1 = t2) by (eapply cde_evaltype_eq; eauto)
          end; 
          inverts Heqt; 
          solve  [congruence | auto] |
          eapply client_data_equiv_local_preserve; eauto]; fail); 
    try (
        match goal with H: is_int_type (Tptr _) = _ |- _ => simpl in H; tryfalse end
      ).
  -
    assert (Hce_ := Hce). 
    unfold client_data_equiv in Hce_. 
    destruct Hce_ as
      (ges1_ & ges2_ & ces1_ & ces2_ & m1_ & m2_ &
         Heq1 & Heq2 & Hgesdeq & Hleq & Hmeq). 
    inverts Heq1. inverts Heq2.
    rewrite <- Hgesdeq in H7.    
    splits; auto.
    assert (v = v0). eapply cde_evalval_eq; eauto. congruence.
    eapply client_data_equiv_local_preserve; eauto.
  -
    splits; auto.
    assert (v = v0) by (eapply cde_var_addr_eq; eauto).
    congruence. 
    eapply client_data_equiv_local_preserve; eauto. 
  -
    splits; auto.
    assert (Heq1: t0 = t4) by (eapply cde_evaltype_eq; eauto).
    assert (Heq2: t3 = t5) by (eapply cde_evaltype_eq; eauto).
    subst. auto.
    eapply client_data_equiv_local_preserve; eauto.
  -
    rewrite H6 in H8. inverts H8.
    splits; auto.
    eapply client_data_equiv_local_preserve; eauto.
  -
    inverts H7. inverts H9.
    rename M into M1. rename M0 into M2.
    splits; auto.
    unfold client_data_equiv in Hce.    
    simpljoin.
    destruct (addrval_to_addr a) eqn: E. 
    assert (v = v0). 
    { eapply load_pt_eq; eauto. }
    subst.
    auto.
    eapply client_data_equiv_local_preserve; eauto.
  -
    inverts H8.
    splits; auto.
    eapply client_data_equiv_local_preserve; eauto.
  -
    rewrite H6 in H8.
    inverts H8.
    splits; auto.
    eapply client_data_equiv_local_preserve; eauto.
  -
    rewrite H6 in H10.
    inverts H10.
    splits; auto.
    eapply client_data_equiv_local_preserve; eauto.
Qed.     


Lemma expr_no_cross_read_ext: 
  forall d d0 pr ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 t1 t2 c ke le1 le2 c1' c2' ke1' ke2' le1' le2' M1' M2', 
    estep d c ke (ges1 d, le1, M1) c1' ke1' (ges1 d, le1', M1') ->
    estep d c ke (ges2 d, le2, M2) c2' ke2' (ges2 d, le2', M2') ->
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    client_data_equiv d0 (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    (c1' = c2' /\ ke1' = ke2' /\ 
       client_data_equiv d0
         (ges1, set cenvs1 t1 le1', M1') (ges2, set cenvs2 t2 le2', M2') O1 O2).
Proof.
  introv Hstep1 Hstep2 Hce Hce0 Htpi1 Htpi2 Hdom Hct1 Hct2. 
  inverts Hstep1; inverts Hstep2; 
    try (splits; auto; 
         assert (Heq1: set cenvs1 t1 le1' = cenvs1) by (eapply get_set_same; eauto);
         assert (Heq2: set cenvs2 t2 le2' = cenvs2) by (eapply get_set_same; eauto); 
         rewrite Heq1; rewrite Heq2; 
         auto; fail);
    try (splits; auto; 
         [ repeat (
             match goal with
             H1: evaltype ?e (ges1 _, _, _) = Some ?t1, H2: evaltype ?e (ges2 _, _, _) = Some ?t2 |- _ =>
               assert (Heqt: t1 = t2) by (clear Hce0; eapply cde_evaltype_eq; eauto);
               subst; clear H1; clear H2
           end); 
           solve  [congruence | auto] |
           eapply client_data_equiv_local_preserve; eauto]; fail); 
    try (
        repeat (
            match goal with
              H: is_int_type _ = true |- _ => simpl in H; tryfalse; clear H
            end); fail). 
  -
    splits; auto.
    2: { eapply client_data_equiv_local_preserve; eauto. }
    assert (v = v0).
    {
      unfolds in Hce. simpljoin.
      match goal with H: _ (dom_for_prio _) = _ (dom_for_prio _) |- _ => rewrite H in * end.
      eapply cde_evalval_eq; eauto.
    }
    congruence.
  -
    splits; auto.
    2: { eapply client_data_equiv_local_preserve; eauto. }    
    assert (v = v0).
    { clear Hce0. eapply cde_var_addr_eq; eauto. }
    congruence.
  -
    splits; auto.
    2: { eapply client_data_equiv_local_preserve; eauto. }
    inverts H7. inverts H9.
    clear Hce0.
    unfolds in Hce. simpljoin.
    destruct (addrval_to_addr a).
    assert (v = v0). 
    { eapply load_pt_eq; eauto. }
    congruence.
Qed.

Lemma storebytes_get_new: 
  forall (vl: list memval) m m' b (i: Z) o (v: memval),  
    storebytes m (b, i) vl = Some m' ->
    (0 <= o < Z_of_nat (length vl))%Z -> 
    List.nth_error vl (Z.to_nat o) = Some v -> 
    get m' (b, i+o) = Some (true, v). 
Proof.
  induction vl.
  - 
    intros.
    simpl in H0. inverts H0. 
    apply Zlt_not_le in H2; auto.
    inverts H2. 
  -
    introv Hsb Hrgn Hnth.
    simpl in Hsb.
    destruct (get m (b, i)) eqn: E.
    2: { rewrite E in Hsb. tryfalse. }

    rewrite E in Hsb.
    destruct p as (tf, mv).
    destruct tf.
    2: { tryfalse. }
    destruct (storebytes m (b, i + 1) vl) eqn: Esb.
    2: { tryfalse. }
    inverts Hsb.
    assert (Hcs: o = 0 \/ 1 <= o < Z.of_nat (length (a::vl))).
    {
      destruct o. left; auto.
      auto with zarith.
      auto with zarith.
    }
    destruct Hcs as [Hz | Hnz].
    + subst.
      rewrite Z.add_0_r.
      simpl in Hnth. inverts Hnth. rewrite set_a_get_a. auto.
    + assert (Hmone: 0 <= o-1 < Z.of_nat (length vl)).
      {
        clear -Hnz.
        destruct Hnz. split.
        auto with zarith.
        simpl in H0; auto with zarith. 
      }
      assert (Hnth': nth_error vl (Z.to_nat (o-1)) = Some v).
      {
        assert (Hlsteq: nth_error ((a::nil)++vl) (Z.to_nat o)= nth_error vl ((Z.to_nat o)-(length (a::nil)))).
        { eapply nth_error_app2; eauto. simpl. auto with zarith. }
        rewrite Hnth in Hlsteq.
        simpl in Hlsteq.
        assert (Ha: ((Z.to_nat o) - 1 = Z.to_nat (o - 1))%nat).
        { auto with zarith. }
        congruence.
      }
      lets Hget: IHvl Esb Hmone Hnth'. 
      assert (Ham: i + 1 + (o - 1) = i + o). 
      { auto with zarith. }
      rewrite Ham in Hget.
      rewrite set_a_get_a'; auto. 
      introv Hf.
      inverts Hf. auto with zarith.
Qed.

Lemma storebytes_get_old_l: 
  forall (vl: list memval) m m' b (i: Z) o,  
    storebytes m (b, i) vl = Some m' ->
    (o < 0)%Z -> 
    get m' (b, i+o) = get m (b, i+o). 
Proof.
  induction vl; introv Hsb Hlt.
  - simpl in Hsb.
    inverts Hsb.
    auto.
  - simpl in Hsb.
    destruct (get m (b, i)) eqn: E.
    + rewrite E in Hsb.
      destruct p as (tf, mv).
      destruct tf; tryfalse.
      destruct (storebytes m (b, i + 1) vl) eqn: E'; tryfalse.
      inverts Hsb.
      rewrite set_a_get_a'; eauto.
      2: { introv Hf. inverts Hf. auto with zarith. }
      assert (o - 1 < 0). { auto with zarith. }
      lets H_: IHvl E' H.
      assert (Heq: i+1+(o-1) = i+o). { auto with zarith. }
      rewrite Heq in H_.
      auto.
    + rewrite E in Hsb. tryfalse.
Qed.       

Lemma storebytes_get_old_r: 
  forall (vl: list memval) m m' b (i: Z) o,  
    storebytes m (b, i) vl = Some m' ->
    (o >= Z.of_nat (length vl))%Z ->  
    get m' (b, i+o) = get m (b, i+o). 
Proof.
  induction vl; introv Hsb Hlt.
  - simpl in Hsb.
    inverts Hsb.
    auto.
  - simpl in Hsb.
    assert (o > 0). { simpl in Hlt. auto with zarith. }
    destruct (get m (b, i)) eqn: E.
    + rewrite E in Hsb.
      destruct p as (tf, mv).
      destruct tf; tryfalse.
      destruct (storebytes m (b, i + 1) vl) eqn: E'; tryfalse.
      inverts Hsb.
      rewrite set_a_get_a'; eauto.      
      2: { introv Hf. inverts Hf. auto with zarith. }
      assert (Hmone: o - 1 >= Z.of_nat (length vl)).
      { simpl in Hlt. auto with zarith. }
      lets H_: IHvl E' Hmone.
      assert (Heq: i+1+(o-1) = i+o). { auto with zarith. }
      rewrite Heq in H_.
      auto.
    + rewrite E in Hsb. tryfalse.
Qed.

Lemma storebytes_get_old_blk':
  forall (vl: list memval) m m' b b' (i i': Z),
    storebytes m (b, i) vl = Some m' ->
    b <> b' ->
    get m' (b', i') = get m (b', i').
Proof.
  induction vl; introv Hsb Hneq.
  - simpl in Hsb.
    inverts Hsb.
    auto.
  - simpl in Hsb.
    destruct (get m (b, i)) eqn: E.
    + rewrite E in Hsb.
      destruct p as (tf, mv).
      destruct tf; tryfalse.
      destruct (storebytes m (b, i + 1) vl) eqn: E'; tryfalse.
      inverts Hsb.
      rewrite set_a_get_a'; eauto.
      introv Hf.
      inverts Hf.
      apply Hneq; auto.
    + rewrite E in Hsb.
      tryfalse.
Qed.

Lemma freeb_get_new: 
  forall n m b i m' o, 
    freeb m b i n = Some m' ->
    0 <= o < (Z_of_nat n) -> 
    get m' (b, (i+o)) = None.
Proof.
  induction n.
  - 
    introv Hfr Hrgn.
    simpl in Hrgn. 
    false. auto with zarith.
  -
    introv Hfr Hrgn.
    simpl in Hfr.
    destruct (get m (b, i)) eqn: E; tryfalse. 
    destruct p as (rw, mv).
    destruct rw eqn: E'; tryfalse.
    destruct (freeb m b (i + 1) n) eqn: E''; tryfalse.
    inverts Hfr.
    assert (Hcs: o = 0 \/ 0 < o < Z.of_nat (S n)).
    { clear -Hrgn. destruct o.
      left; auto. auto with zarith. auto with zarith. }
    destruct Hcs as [Hz | Hnz].
    + subst.
      rewrite (Z.add_0_r).
      rewrite del_get; eauto.
    +
      clear Hrgn.
      assert (Hrgn': 0 <= o - 1 < Z.of_nat n).
      { auto with zarith. }
      lets H_: IHn E'' Hrgn'.
      assert (Hr: i + 1 + (o - 1) = i + o).
      { auto with zarith. }
      rewrite Hr in H_.
      rewrite mem_del_get_neq'; eauto.
      introv Hf. inverts Hf.
      auto with zarith.
Qed.

Lemma freeb_get_old_l: 
  forall n m b i m' o, 
    freeb m b i n = Some m' ->
    o < 0 -> 
    get m' (b, (i+o)) = get m (b, (i+o)).
Proof.
  induction n.
  -
    introv Hfr Hrgn.
    simpl in Hfr. inverts Hfr. auto.
  -
    introv Hfr Hrgn.
    simpl in Hfr.
    destruct (get m (b, i)) eqn: E; tryfalse. 
    destruct p as (rw, mv).
    destruct rw eqn: E'; tryfalse.
    destruct (freeb m b (i + 1) n) eqn: E''; tryfalse.
    inverts Hfr.
    assert (Hlt: o - 1 < 0). { auto with zarith. }
    lets H_: IHn E'' Hlt. 
    assert (Hr: i + 1 + (o - 1) = i + o).
    { auto with zarith. }
    rewrite Hr in H_.
    rewrite mem_del_get_neq'; eauto.
    introv Hf. inverts Hf. auto with zarith.
Qed.     

Lemma freeb_get_old_r: 
  forall n m b i m' o, 
    freeb m b i n = Some m' ->
    o >= Z_of_nat n -> 
    get m' (b, (i+o)) = get m (b, (i+o)).
Proof.
  induction n.
  -
    introv Hfr Hrgn.
    simpl in Hfr. inverts Hfr. auto.
  -
    introv Hfr Hrgn.
    simpl in Hfr.
    destruct (get m (b, i)) eqn: E; tryfalse. 
    destruct p as (rw, mv).
    destruct rw eqn: E'; tryfalse.
    destruct (freeb m b (i + 1) n) eqn: E''; tryfalse.
    inverts Hfr.
    assert (Hge: o - 1 >= Z_of_nat n). { auto with zarith. }
    lets H_: IHn E'' Hge. 
    assert (Hr: i + 1 + (o - 1) = i + o).
    { auto with zarith. }
    rewrite Hr in H_.
    rewrite mem_del_get_neq'; eauto.
    introv Hf. inverts Hf. auto with zarith.
Qed.     

Lemma freeb_get_old_blk':
  forall n m b i b' i' m',
    freeb m b i n = Some m' ->
    b <> b' ->
    get m' (b', i') = get m (b', i'). 
Proof.
  induction n.
  - introv Hfr Hneq.
    simpl in Hfr.
    inverts Hfr.
    auto.
  - introv Hfr Hneq.
    simpl in Hfr.
    destruct (get m (b, i)) eqn: E; tryfalse. 
    destruct p as (rw, mv).
    destruct rw eqn: E'; tryfalse.
    destruct (freeb m b (i + 1) n) eqn: E''; tryfalse.
    inverts Hfr.
    lets H_: IHn E'' Hneq.
    rewrite mem_del_get_neq'; eauto.
    introv Hf.
    inverts Hf.
    apply Hneq; auto.
Qed.

Lemma offset_cases:
  forall (o: Z) n, 
    o < 0 \/ o >= Z.of_nat n \/ 0 <= o < Z.of_nat n.
Proof.
  intros.
  assert (Hcs1: o < 0 \/ o >= 0).
  {
    lets H_: Z.lt_ge_cases o 0.
    destruct H_. left; auto. right. auto with zarith.
  }
  destruct Hcs1.
  left; auto.
  right.
  assert (Hcs2: o < Z.of_nat n \/ Z.of_nat n <= o).
  { eapply Z.lt_ge_cases; eauto. }
  destruct Hcs2.
  right. split; auto with zarith.
  left. auto with zarith.
Qed.

Lemma client_data_equiv_mem_store_preserve: 
  forall ges1 ges2 cenvs1 cenvs2 tp M1 M2 O1 O2 a d v M1' M2', 
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    store tp M1 (addrval_to_addr a) v = Some M1' ->
    store tp M2 (addrval_to_addr a) v = Some M2' -> 
    client_data_equiv d (ges1, cenvs1, M1') (ges2, cenvs2, M2') O1 O2. 
Proof.
  introv Hcde Hst1 Hst2.
  unfold client_data_equiv in *.
  simpljoin.
  repeat eexists; eauto.
  unfold get_dom_mem in *.
  apply functional_extensionality.
  intros.
  destruct (addr_in_dom x5 d) eqn: E; auto.
  rename H3 into Hfeq.
  match type of Hfeq with
    ?f1 = ?f2 => remember f1 as X1; remember f2 as X2
  end.
  assert (Haeq: X1 x5 = X2 x5) by congruence.
  rewrite HeqX1 in Haeq. rewrite HeqX2 in Haeq.
  rewrite E in Haeq. 
  destruct (addrval_to_addr a) as (b, i) eqn: E'.
  destruct x5 as (b', i') eqn: E''.
  casetac b b' Heq Hneq.
  -
    subst b'.
    simpl in Hst1. simpl in Hst2.
    assert (Hext: i' = i + (i' - i)). { rewrite Zplus_minus. auto. }
    rewrite Hext.
    remember (i' - i) as o.
    assert (Hcs: 
        i' - i < 0 \/ i' - i >= Z_of_nat (length (encode_val tp v))
        \/ 0 <= i' - i < Z_of_nat (length (encode_val tp v))).
    { eapply offset_cases; eauto. }
    rewrite <- Heqo in *.
    rewrite Hext in Haeq.
    destruct Hcs as [Hlt | [Hge | Hmid]].
    + lets H_: storebytes_get_old_l Hst1 Hlt.
      rewrite H_.
      lets H'_: storebytes_get_old_l Hst2 Hlt.
      rewrite H'_.
      auto.
    + lets H_: storebytes_get_old_r Hst1 Hge.
      rewrite H_.
      lets H'_: storebytes_get_old_r Hst2 Hge.
      rewrite H'_.
      auto.
    + lets H_: storebytes_get_new Hst1 Hmid.
      lets H'_: storebytes_get_new Hst2 Hmid.
      rewrite H_.
      rewrite H'_. 
      eauto.
      eapply nth_error_nth'.
      clear -Hmid. 
      destruct Hmid.
      auto with zarith.
      eapply nth_error_nth'.
      clear -Hmid. 
      destruct Hmid.
      auto with zarith.
  - simpl in Hst1. 
    lets H_: storebytes_get_old_blk' Hst1 Hneq.
    lets H'_: storebytes_get_old_blk' Hst2 Hneq.
    rewrite H_.
    rewrite H'_.
    eauto.

    Unshelve.
    exact Undef. 
Qed.       

Lemma mem_free_eq:  
  forall m1 m2 d b i m1' m2' n, 
    get_dom_mem m1 d = get_dom_mem m2 d -> 
    freeb m1 b i n = Some m1' ->
    freeb m2 b i n = Some m2' ->
    get_dom_mem m1' d = get_dom_mem m2' d. 
Proof.
  introv Hdeq Hfr1 Hfr2.
  unfold get_dom_mem in *.
  apply functional_extensionality.
  intro a.
  destruct (addr_in_dom a d) eqn: E; auto.
  destruct a as (b' & i').
  casetac b b' Heq Hneq.
  - subst. 
    remember (i' - i) as o.
    assert (Hsimp: i+o = i'). { auto with zarith. }
    assert (Hcs: o < 0 \/ o >= Z.of_nat n \/ 0 <= o < Z.of_nat n).
    { eapply offset_cases; eauto. }
    destruct Hcs as [Hltz | [Hge | Hmid]].
    + match type of Hdeq with
        ?f1 = ?f2 => remember f1 as X1; remember f2 as X2
      end.
      assert (Hxeq: X1 (b', i') = X2 (b', i')). { congruence. }
      subst X1. subst X2.
      rewrite E in Hxeq.
      lets Hgeq1: freeb_get_old_l Hfr1 Hltz.
      lets Hgeq2: freeb_get_old_l Hfr2 Hltz.
      rewrite Hsimp in *. 
      rewrite Hgeq1; rewrite Hgeq2.
      auto.
    + match type of Hdeq with
        ?f1 = ?f2 => remember f1 as X1; remember f2 as X2
      end.
      assert (Hxeq: X1 (b', i') = X2 (b', i')). { congruence. }
      subst X1. subst X2.
      rewrite E in Hxeq.
      lets Hgeq1: freeb_get_old_r Hfr1 Hge.
      lets Hgeq2: freeb_get_old_r Hfr2 Hge.
      rewrite Hsimp in *. 
      rewrite Hgeq1; rewrite Hgeq2.
      auto.
    + assert (Hn1: get m1' (b', i+o) = None).
      { eapply freeb_get_new; eauto. }
      assert (Hn2: get m2' (b', i+o) = None).
      { eapply freeb_get_new; eauto. }
      rewrite Hsimp in *.
      rewrite Hn1; rewrite Hn2; auto.
  - match type of Hdeq with
      ?f1 = ?f2 => remember f1 as X1; remember f2 as X2
    end.
    assert (Hxeq: X1 (b', i') = X2 (b', i')). { congruence. }
    subst X1. subst X2.
    rewrite E in Hxeq.
    lets Hgeq1: freeb_get_old_blk' Hfr1 Hneq.
    lets Hgeq2: freeb_get_old_blk' Hfr2 Hneq.
    rewrite Hgeq1. rewrite Hgeq2.
    auto.
Qed.     

Lemma get_dom_mem_freeb_eq:
  forall n m b i m' d d0, 
    freeb m b i n = Some m' ->
    addr_in_dom (b, i) d = true ->
    d <> d0 ->
    get_dom_mem m d0 = get_dom_mem m' d0.
Proof.
  induction n; 
    introv Hfrb Haid Hneq.
  -
    simpl in Hfrb. inverts Hfrb.
    auto.
  -
    simpl in Hfrb.
    destruct (get m (b, i)) eqn: E; tryfalse.
    destruct p.
    destruct b0; tryfalse.
    destruct (freeb m b (i + 1) n) eqn: E'; tryfalse.
    inverts Hfrb.
    assert (Haid': addr_in_dom (b, i+1) d = true).
    { erewrite n_block_cross_part in Haid. eauto. }
    lets H_: IHn E' Haid' Hneq.
    rewrite H_.
    unfolds.
    apply functional_extensionality. intro a.
    destruct (addr_in_dom a d0) eqn: E''.
    + 
      erewrite mem_del_get_neq'; eauto.
      introv Heq. subst.
      lets Hf: dom_disj_addrs Hneq Haid E''.
      auto.
    + 
      auto.
Qed.

Lemma get_dom_mem_free_eq:
  forall tp m b m' d d0, 
    free tp b m = Some m' ->
    addr_in_dom (b, 0) d = true ->
    d <> d0 ->
    get_dom_mem m d0 = get_dom_mem m' d0.
Proof.
  introv Hfr Hai Hne.
  unfolds in Hfr.
  eapply get_dom_mem_freeb_eq; eauto.
Qed. 

Lemma stmt_no_cross_read: 
  forall d pu pr ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 t1 t2 c ks le1 le2 c1' c2' ks1' ks2' le1' le2' M1' M2', 
    sstep pu d c ks (ges1 d, le1, M1) c1' ks1' (ges1 d, le1', M1') ->
    sstep pu d c ks (ges2 d, le2, M2) c2' ks2' (ges2 d, le2', M2') ->
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    (c1' = c2' /\ ks1' = ks2' /\ 
       client_data_equiv d
         (ges1, set cenvs1 t1 le1', M1') (ges2, set cenvs2 t2 le2', M2') O1 O2).
Proof.
  introv Hstep1 Hstep2 Hcde Htpi1 Htpi2 Hd Hget1 Hget2.
  inverts Hstep1; inverts Hstep2; 
    try (repeat (
             match goal with
               H1: (evaltype ?e _ = Some ?t1), H2: (evaltype ?e _ = Some ?t2) |- _ =>
                 (assert (t1 = t2) by (eapply cde_evaltype_eq; eauto)); clear H1; clear H2
             end);
         subst;
         splits; auto; 
         eapply client_data_equiv_local_preserve; eauto;
         fail);
    repeat (match goal with H: (ges1 d, _, _) = _ |- _ => inverts H end); 
    repeat (match goal with H: (ges2 d, _, _) = _ |- _ => inverts H end). 
  -
    splits; auto.
    assert (Heq1: set cenvs1 t1 le = cenvs1).
    { eapply get_set_same; eauto. }
    assert (Heq2: set cenvs2 t2 le0 = cenvs2).
    { eapply get_set_same; eauto. }
    rewrite Heq1. rewrite Heq2.
    eapply client_data_equiv_mem_store_preserve; eauto.
  -
    match goal with
      H1: pu f = Some _, H2: pu f = Some _ |- _ => rewrite H1 in H2; inverts H2
    end.
    split; auto.
    split.
    unfold client_data_equiv in Hcde.
    simpljoin.
    unfold local_envs_equiv in H5.
    assert (get x1 t1 = get x2 t2) by (eapply H5; eauto).
    congruence.
    eapply client_data_equiv_same_le_upd_preserve; eauto.
  - 
    splits; auto. 
    assert (le' = le'0).  
    { eapply cde_alloc_le'_eq; eauto. }
    subst le'0.
    assert (H_: client_data_equiv d (ges1, set cenvs1 t1 le', M') (ges2, set cenvs2 t2 le', M'0) O1 O2).
    { eapply client_data_equiv_alloc_preserve; eauto. }
    assert (b = b0) by congruence.
    subst b0.
    clear Hcde.
    assert (Heq_: (b, 0) = addrval_to_addr (b, Int.zero)). 
    { simpl. rewrite Int.unsigned_zero; auto. }
    rewrite Heq_ in *.
    eapply client_data_equiv_mem_store_preserve; eauto. 
  -
    splits; auto.
    eapply client_data_equiv_alloc_preserve; eauto.
  - 
    match goal with
      H1: get cenvs1 _ = Some ?le1, H2: get cenvs2 _ = Some ?le2 |- _ =>
        assert (le1 = le2) by (eapply cde_lenv_eq; eauto)
    end.
    subst.
    splits; auto.
    eapply client_data_equiv_local_preserve; eauto.
  - 
    match goal with
      H1: get cenvs1 _ = Some ?le1, H2: get cenvs2 _ = Some ?le2 |- _ =>
        assert (le1 = le2) by (eapply cde_lenv_eq; eauto)
    end.
    subst.
    splits; auto.
    eapply client_data_equiv_local_preserve; eauto.
  -
    splits; auto.
    unfold client_data_equiv in *.
    simpljoin.
    do 6 eexists.
    split; eauto. split; eauto. split; eauto.
    split. eapply local_envs_equiv_local_preserve; eauto.
    eapply mem_free_eq; eauto.
  -
    split; auto.
    split. congruence.
    assert (le' = le'0). { congruence. }
    subst.
    eapply client_data_equiv_same_le_upd_preserve; eauto.
  - match goal with
      H1: istrue _ = _, H2: istrue _ = _ |- _ => rewrite H1 in H2; tryfalse
    end.
  - match goal with
      H1: istrue _ = _, H2: istrue _ = _ |- _ => rewrite H1 in H2; tryfalse
    end.
  - match goal with
      H1: istrue _ = _, H2: istrue _ = _ |- _ => rewrite H1 in H2; tryfalse
    end.
  - match goal with
      H1: istrue _ = _, H2: istrue _ = _ |- _ => rewrite H1 in H2; tryfalse
    end.
Qed. 

Lemma stmt_no_cross_read_ext: 
  forall d d0 pu pr ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 t1 t2 c ks le1 le2 c1' c2' ks1' ks2' le1' le2' M1' M2', 
    sstep pu d c ks (ges1 d, le1, M1) c1' ks1' (ges1 d, le1', M1') ->
    sstep pu d c ks (ges2 d, le2, M2) c2' ks2' (ges2 d, le2', M2') ->
    client_data_equiv d (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 -> 
    client_data_equiv d0 (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    dom_for_prio pr = d -> 
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    (c1' = c2' /\ ks1' = ks2' /\ 
       client_data_equiv d0
         (ges1, set cenvs1 t1 le1', M1') (ges2, set cenvs2 t2 le2', M2') O1 O2).
Proof.
  introv Hstep1 Hstep2 Hcde Hcde0 Htpi1 Htpi2 Hd Hget1 Hget2.
  inverts Hstep1; inverts Hstep2; 
    repeat (match goal with H: (ges1 d, _, _) = _ |- _ => inverts H end);
    repeat (match goal with H: (ges2 d, _, _) = _ |- _ => inverts H end); 
    try (
        repeat (
            match goal with
              H1: (evaltype ?e _ = Some ?t1), H2: (evaltype ?e _ = Some ?t2) |- _ =>
                (assert (t1 = t2) by (clear Hcde0; eapply cde_evaltype_eq; eauto)); clear H1; clear H2
            end); subst; 
        splits; auto; 
        eapply client_data_equiv_local_preserve; eauto; fail);
    try (match goal with
           H1: istrue _ = _, H2: istrue _ = _ |- _ => rewrite H1 in H2; tryfalse
         end; fail).
  -
    splits; auto.
    assert (Heq1: set cenvs1 t1 le = cenvs1).
    { eapply get_set_same; eauto. }
    assert (Heq2: set cenvs2 t2 le0 = cenvs2).
    { eapply get_set_same; eauto. }
    rewrite Heq1. rewrite Heq2.
    eapply client_data_equiv_mem_store_preserve; eauto.
  -
    match goal with
      H1: pu f = Some _, H2: pu f = Some _ |- _ => rewrite H1 in H2; inverts H2
    end.
    split; auto.
    split.
    unfold client_data_equiv in Hcde.
    simpljoin.
    unfold local_envs_equiv in H5.
    assert (get x1 t1 = get x2 t2) by (eapply H5; eauto).
    congruence.
    lets H_: client_data_equiv_same_le_upd_preserve_ext
               Hcde0 Htpi1 Htpi2 Hd.
    eauto.
  -
    splits; eauto.
    assert (le' = le'0).  
    { clear Hcde0. eapply cde_alloc_le'_eq; eauto. }
    subst le'0.
    assert (H_: client_data_equiv d0
                  (ges1, set cenvs1 t1 le', M') (ges2, set cenvs2 t2 le', M'0) O1 O2). 
    { lets H0_: client_data_equiv_alloc_preserve_ext Hcde0 Hcde Hd Htpi1 Htpi2.
      lets H__: H0_ Hget1 Hget2. eapply H__; eauto. }
    assert (b = b0) by congruence.
    subst b0.
    clear Hcde.
    assert (Heq_: (b, 0) = addrval_to_addr (b, Int.zero)). 
    { simpl. rewrite Int.unsigned_zero; auto. }
    rewrite Heq_ in *.
    eapply client_data_equiv_mem_store_preserve; eauto. 
  -
    splits; eauto.
    lets H_: client_data_equiv_alloc_preserve_ext Hcde0 Hcde Hd Htpi1 Htpi2.
    lets H0_: H_ Hget1 Hget2.
    eapply H0_; eauto.
  -
    match goal with
      H1: get cenvs1 _ = Some ?le1, H2: get cenvs2 _ = Some ?le2 |- _ =>
        assert (le1 = le2) by (clear Hcde0; eapply cde_lenv_eq; eauto)
    end.
    subst.
    splits; eauto.
    clear Hcde.
    eapply client_data_equiv_local_preserve; eauto.
  -
    match goal with
      H1: get cenvs1 _ = Some ?le1, H2: get cenvs2 _ = Some ?le2 |- _ =>
        assert (le1 = le2) by (clear Hcde0; eapply cde_lenv_eq; eauto)
    end.
    subst.
    splits; eauto.
    eapply client_data_equiv_local_preserve; eauto.
  -
    match goal with
      H1: get cenvs1 _ = Some ?le1, H2: get cenvs2 _ = Some ?le2 |- _ =>
        assert (le1 = le2) by (clear Hcde0; eapply cde_lenv_eq; eauto)
    end.
    subst. 
    splits; eauto.
    unfolds.
    do 6 eexists. split; auto. split; auto.
    unfolds in Hcde0. simpljoin.
    splits; eauto.
    eapply local_envs_same_upd_eq; eauto.
    casetac (dom_for_prio pr) d0 Ht Hf.
    +
      subst. eapply mem_free_eq; eauto.
    +
      assert (get_dom_mem x3 d0 = get_dom_mem M' d0). 
      { eapply get_dom_mem_free_eq; eauto. }
      assert (get_dom_mem x4 d0 = get_dom_mem M'0 d0).
      { eapply get_dom_mem_free_eq; eauto. }
      congruence.
  -
    split; auto.
    split. congruence.
    assert (le' = le'0). { congruence. }
    subst.
    eapply client_data_equiv_same_le_upd_preserve_ext; eauto.
Qed.     

Lemma cli_no_cross_part_read:
  forall pc osspc T1 T2 C t1 t2 ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 le1 le2 pr C1' C2' le1' le2' M1' M2', 
    reachable (pc, osspc) T1 (ges1, cenvs1, M1) O1 -> 
    reachable (pc, osspc) T2 (ges2, cenvs2, M2) O2 -> 
    client_data_equiv (dom_for_prio pr) (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    get T1 t1 = Some C ->
    get T2 t2 = Some C ->
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    cstep pc (dom_for_prio pr) C (ges1 (dom_for_prio pr), le1, M1)
      C1' (ges1 (dom_for_prio pr), le1', M1') ->
    cstep pc (dom_for_prio pr) C (ges2 (dom_for_prio pr), le2, M2)
      C2' (ges2 (dom_for_prio pr), le2', M2') ->
    (C1' = C2' /\ 
       client_data_equiv (dom_for_prio pr)
         (ges1, set cenvs1 t1 le1', M1') (ges2, set cenvs2 t2 le2', M2') O1 O2). 
Proof. 
  introv Hrch1 Hrch2 Hce Htpi1 Htpi2 Htt1 Htt2.
  introv Hct1 Hct2 Hstep1 Hstep2.

  inverts Hstep1.
  - (* estep for left system *)
    inverts Hstep2.
    inverts H.
    2: { (* sstep for right system --- impossible *) 
      inverts H.
      apply reachable_ctrl_state_cond in Hrch1.
      unfolds in Hrch1.
      lets Hr1: Hrch1 Htt1.
      lets Hf: cs_estep_nsstep Hr1 H0 H1.
      tryfalse.
    }
    rename c0 into c.
    rename ke0 into ke.
    rename ks0 into ks.
    rename ke' into ke1'. rename ke'0 into ke2'.
    rename c' into c1'. rename c'0 into c2'.
    lets H_: expr_no_cross_read H0 H1 Hce Htpi1 Htpi2.
    specialize (H_ (eq_refl _) Hct1 Hct2).
    simpljoin; subst.
    splits; auto.
  -
    inverts Hstep2.
    * (* estep by right system --- impossible *)
      inverts H.
      apply reachable_ctrl_state_cond in Hrch1.
      unfolds in Hrch1.
      lets Hr1: Hrch1 Htt1.
      lets Hf: cs_estep_nsstep Hr1 H1 H0.
      inverts Hf.
    * (* sstep by right system *)
      inverts H.
      lets H_: stmt_no_cross_read H0 H1 Hce Htpi1 Htpi2.
      specialize (H_ (eq_refl _) Hct1 Hct2).
      simpljoin.
      splits; eauto.
Qed. 

Lemma cli_no_cross_part_read_ext:
  forall pc osspc d0 T1 T2 C t1 t2 ges1 ges2 cenvs1 cenvs2 M1 M2 O1 O2 le1 le2 pr C1' C2' le1' le2' M1' M2', 
    reachable (pc, osspc) T1 (ges1, cenvs1, M1) O1 -> 
    reachable (pc, osspc) T2 (ges2, cenvs2, M2) O2 ->
    client_data_equiv d0 (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    client_data_equiv (dom_for_prio pr) (ges1, cenvs1, M1) (ges2, cenvs2, M2) O1 O2 ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    get T1 t1 = Some C ->
    get T2 t2 = Some C ->
    get cenvs1 t1 = Some le1 ->
    get cenvs2 t2 = Some le2 ->
    cstep pc (dom_for_prio pr) C (ges1 (dom_for_prio pr), le1, M1)
      C1' (ges1 (dom_for_prio pr), le1', M1') ->
    cstep pc (dom_for_prio pr) C (ges2 (dom_for_prio pr), le2, M2)
      C2' (ges2 (dom_for_prio pr), le2', M2') ->
    (C1' = C2' /\ 
       client_data_equiv d0
         (ges1, set cenvs1 t1 le1', M1') (ges2, set cenvs2 t2 le2', M2') O1 O2). 
Proof.
  introv Hrc1 Hrc2 Hcde0 Hcde Htpi1 Htpi2.
  introv Hget1 Hget2 Hle1 Hle2 Hstep1 Hstep2.

  inverts Hstep1. 
  - (* estep for left system *)
    inverts Hstep2.
    inverts H.
    2: { (* sstep for right system --- impossible *) 
      inverts H.
      apply reachable_ctrl_state_cond in Hrc1.
      unfolds in Hrc1.
      lets Hr1: Hrc1 Hget1.
      lets Hf: cs_estep_nsstep Hr1 H0 H1.
      tryfalse.
    }
    rename c0 into c.
    rename ke0 into ke.
    rename ks0 into ks.
    rename ke' into ke1'. rename ke'0 into ke2'.
    rename c' into c1'. rename c'0 into c2'.
    lets H_: expr_no_cross_read_ext H0 H1 Hcde Hcde0 Htpi1 Htpi2.
    specialize (H_ (eq_refl _) Hle1 Hle2).
    simpljoin; subst.
    splits; auto.
  -
    inverts Hstep2.
    * (* estep by right system --- impossible *)
      inverts H.
      apply reachable_ctrl_state_cond in Hrc1.
      unfolds in Hrc1.
      lets Hr1: Hrc1 Hget1.
      lets Hf: cs_estep_nsstep Hr1 H1 H0.
      inverts Hf.
    * (* sstep by right system *)
      inverts H.
      lets H_: stmt_no_cross_read_ext H0 H1 Hcde Hcde0 Htpi1 Htpi2.
      specialize (H_ (eq_refl _) Hle1 Hle2).
      simpljoin.
      splits; eauto.
Qed.   

Lemma hapistep_knl:
  forall aspc ispc sch C O C' O' act c ke ks, 
    hapistep (aspc, ispc, sch) C O C' O' act ->
    C = (c, (ke, ks)) -> 
    (exists f vl tl, c = curs (sfexec f (rev vl) (rev tl))) \/ ~not_knl_stmt c. 
Proof.
  introv Hstep HC.
  subst C.
  inverts Hstep.
  inverts H1.
  left. repeat eexists.
  
  right. introv Hknl. unfolds in Hknl.
  destruct Hknl. simpljoin. tryfalse.
  simpljoin.
  inverts H. apply H0. eexists; eauto.
  
  right. introv Hknl. unfolds in Hknl.
  destruct Hknl. simpljoin. tryfalse.
  simpljoin.
  inverts H. apply H0. eexists; eauto. 
  
  right. introv Hknl. unfolds in Hknl.
  destruct Hknl. simpljoin. tryfalse.
  simpljoin.
  inverts H. apply H0. eexists; eauto.
Qed.   
    
Lemma hapistep_tau_or_knl:
  forall aspc ispc sch C O C' O' act c ke ks, 
    hapistep (aspc, ispc, sch) C O C' O' act ->
    C = (c, (ke, ks)) -> 
    (act = TauAct \/ ~not_knl_stmt c). 
Proof.
  introv Hstep HC.
  lets H_: hapistep_knl Hstep HC.  
  inverts Hstep.
  left; auto.
  inverts H0.
  destruct H_. simpljoin; tryfalse.
  right; auto.
  left; auto.
  left; auto.
Qed.  

Lemma mqsend_succs_ex_end_imp:
  forall i vl vl' vl'' cd v,
  length vl = 4%nat ->
  length vl' = 4%nat ->
  length vl'' = 4%nat ->
  nth_error (get_all_succs (mqsend (vl ++ vl'))) i = Some cd ->
  nth_error (get_all_succs (mqsend (vl ++ vl''))) i = Some (END v) ->
  exists v, cd = END v.
Proof.
  introv Hlen Hlen1 Hlen2 Hnth1 Hnth2.
  do 5 try destruct vl; simpl length in Hlen; tryfalse. 
  do 5 try destruct vl''; simpl length in Hlen2; tryfalse.
  simpl in Hnth2. 
  destruct v0; destruct v2; destruct v4;
    destruct v6; destruct v7; tryfalse; 
    try (apply abt_succs_contra in Hnth2; tryfalse). 
  repeat try (destruct i; simpl in Hnth2; tryfalse). 
Qed. 

Lemma mqrecv_succs_ex_end_imp:
  forall i vl vl' vl'' cd v,
  length vl = 4%nat ->
  length vl' = 4%nat ->
  length vl'' = 4%nat ->
  nth_error (get_all_succs (mqreceive (vl ++ vl'))) i = Some cd ->
  nth_error (get_all_succs (mqreceive (vl ++ vl''))) i = Some (END v) ->
  exists v, cd = END v.
Proof.
  introv Hlen Hlen1 Hlen2 Hnth1 Hnth2.
  do 5 try destruct vl; simpl length in Hlen; tryfalse. 
  do 5 try destruct vl''; simpl length in Hlen2; tryfalse.
  simpl in Hnth2. 
  destruct v0; destruct v2; destruct v4; destruct v6; tryfalse; 
    try (apply abt_succs_contra in Hnth2; tryfalse). 
  repeat try (destruct i; simpl in Hnth2; tryfalse). 
Qed.   

Lemma mqtimedrecv_succs_ex_end_imp:
  forall i vl vl' vl'' cd v,
  length vl = 5%nat ->
  length vl' = 4%nat ->
  length vl'' = 4%nat ->
  nth_error (get_all_succs (mqtimedreceive (vl ++ vl'))) i = Some cd ->
  nth_error (get_all_succs (mqtimedreceive (vl ++ vl''))) i = Some (END v) ->
  exists v, cd = END v.
Proof.
  introv Hlen Hlen1 Hlen2 Hnth1 Hnth2.
  do 6 try destruct vl; simpl length in Hlen; tryfalse. 
  do 5 try destruct vl''; simpl length in Hlen2; tryfalse.
  simpl in Hnth2. 
  destruct v0; destruct v2; destruct v4; destruct v5; destruct v7; tryfalse; 
    try (apply abt_succs_contra in Hnth2; tryfalse). 
  repeat try (destruct i; simpl in Hnth2; tryfalse). 
Qed.   

Lemma qportpost_succ_end_false:
  forall x x1 x2 v, 
    length x = 1%nat ->
    length x1 = 2%nat ->
    nth_error (get_all_succs (qportpost (x ++ x1))) x2 = Some (END v) ->
    False.
Proof.
  introv Hlen Hlen1 Hf.
  do 2 try destruct x; tryfalse.
  do 3 try destruct x1; tryfalse.
  destruct x2; simpl in Hf; tryfalse.
  destruct v1; simpl in Hf; tryfalse.
  destruct v1; try destruct x2; simpl in Hf; tryfalse.
  repeat (destruct x2; simpl in Hf; tryfalse). 
Qed. 
  
Lemma qprtpost_equiv_end_false: 
  forall cd v, qprtpost_equiv cd (END v) -> False. 
Proof.
  introv Hpe.
  unfolds in Hpe.
  simpljoin.
  eapply qportpost_succ_end_false; eauto.
Qed.

Lemma qportpend_succ_end_false:
  forall x x1 x2 v, 
    length x = 2%nat -> 
    length x1 = 2%nat -> 
    nth_error (get_all_succs (qportpend (x ++ x1))) x2 = Some (END v) ->
    False. 
Proof.
  introv Hlen Hlen1 Hf.
  do 3 try destruct x; tryfalse.
  do 3 try destruct x1; tryfalse.
  destruct x2; simpl in Hf; tryfalse.
  destruct v2;simpl in Hf; tryfalse.
  destruct v2;destruct x2; simpl in Hf; tryfalse.
  repeat (destruct x2; simpl in Hf; tryfalse). 
Qed.   
  
Lemma qprtpend_equiv_end_false: 
  forall cd v, qprtpend_equiv cd (END v) -> False. 
Proof.
  introv Hpe.
  unfolds in Hpe.
  simpljoin.
  eapply qportpend_succ_end_false in H3; eauto.
Qed.   

Ltac des_vl_absprog := 
  match goal with
    vl: vallist, H: nth_error (get_all_succs (match ?vl with _ => _ end)) _ = _ |- _ =>
      destruct vl; inverts H; tryfalse
  | H: nth_error (get_all_succs (ABORT)) _ = Some _ |- _ => 
      apply abt_succs_contra in H; subst; simpl; auto; tryfalse
  | H: nth_error (get_all_succs (match ?v with _ => _ end)) _ = _ |- _ =>
      destruct v; simpl in H;  
      try (apply abt_succs_contra in H; subst; simpl; auto; tryfalse)   
  end.

Lemma sprtpost_succ_end_false:
  forall x x1 x2 v, 
    length x = 1%nat -> 
    length x1 = 2%nat -> 
    nth_error (get_all_succs (sampleportpost (x ++ x1))) x2 = Some (END v) ->
    False. 
Proof.
  introv Hlen Hlen1 Hf.
  unfold sampleportpost in Hf.
  repeat des_vl_absprog.
  repeat (destruct x2; simpl in Hf; tryfalse).
Qed.   
  
Lemma sprtpost_equiv_end_false: 
  forall cd v, sprtpost_equiv cd (END v) -> False. 
Proof.
  introv Hpe.
  unfolds in Hpe.
  simpljoin.
  eapply sprtpost_succ_end_false in H3; eauto.
Qed.   

Lemma prtacc_succ_end_false:
  forall x x1 x2 v, 
    length x = 1%nat -> 
    length x1 = 2%nat -> 
    nth_error (get_all_succs (portaccept (x ++ x1))) x2 = Some (END v) ->
    False. 
Proof.
  introv Hlen Hlen1 Hf.
  unfold portaccept in Hf.
  repeat des_vl_absprog.
  repeat (destruct x2; simpl in Hf; tryfalse).
Qed.   
  
Lemma prtaccept_equiv_end_false: 
  forall cd v, prtaccept_equiv cd (END v) -> False. 
Proof.
  introv Hpe.
  unfolds in Hpe.
  simpljoin.
  eapply prtacc_succ_end_false in H3; eauto.
Qed.   

Lemma bufferpost_succ_end_false:
  forall x x1 x2 v, 
    length x = 2%nat -> 
    length x1 = 1%nat -> 
    nth_error (get_all_succs (bufferpost (x ++ x1))) x2 = Some (END v) ->
    False. 
Proof.
  introv Hlen Hlen1 Hf.
  do 3 try destruct x; tryfalse.
  do 2 try destruct x1; tryfalse.
  destruct x2; simpl in Hf; tryfalse.
  destruct v2; simpl in Hf; tryfalse.
  destruct v2; destruct x2; simpl in Hf; tryfalse.
  repeat (destruct x2; simpl in Hf; tryfalse). 
Qed.

Lemma bufferpost_equiv_end_false: 
  forall cd v, bufferpost_equiv cd (END v) -> False. 
Proof.
  introv Hbp.
  unfolds in Hbp.
  simpljoin.
  eapply bufferpost_succ_end_false in H3; eauto.
Qed.   

Lemma bufferaccept_succ_end_false:
  forall x x1 x2 v, 
    length x = 1%nat -> 
    length x1 = 1%nat -> 
    nth_error (get_all_succs (bufferaccept (x ++ x1))) x2 = Some (END v) ->
    False. 
Proof.
  introv Hlen Hlen1 Hf.
  do 2 try destruct x; tryfalse.
  do 2 try destruct x1; tryfalse.
  destruct x2; simpl in Hf; tryfalse.
  destruct v1; simpl in Hf; tryfalse.

  repeat (destruct x2; simpl in Hf; tryfalse). 
  repeat (destruct x2; simpl in Hf; tryfalse). 
  repeat (destruct x2; simpl in Hf; tryfalse). 
  repeat (destruct x2; simpl in Hf; tryfalse). 
Qed.

Lemma bufferaccept_equiv_end_false: 
  forall cd v, bufferaccept_equiv cd (END v) -> False. 
Proof.
  introv Hba.
  unfolds in Hba.
  simpljoin.
  eapply bufferaccept_succ_end_false in H3; eauto.
Qed.   

Lemma bufferpend_succ_end_false:
  forall x x1 x2 v, 
    length x = 2%nat -> 
    length x1 = 1%nat -> 
    nth_error (get_all_succs (bufferpend (x ++ x1))) x2 = Some (END v) ->
    False. 
Proof.
  introv Hlen Hlen1 Hf.
  do 3 try destruct x; tryfalse.
  do 2 try destruct x1; tryfalse.
  destruct x2; simpl in Hf; tryfalse.
  destruct v1; destruct v2; simpl in Hf; tryfalse.
  destruct v1; destruct v2; destruct x2; simpl in Hf; tryfalse.
  repeat (destruct x2; simpl in Hf; tryfalse). 
  repeat (destruct x2; simpl in Hf; tryfalse). 
  repeat (destruct x2; simpl in Hf; tryfalse). 
  repeat (destruct x2; simpl in Hf; tryfalse). 
Qed.

Lemma bufferpend_equiv_end_false: 
  forall cd v, bufferpend_equiv cd (END v) -> False. 
Proof.
  introv Hba.
  unfolds in Hba.
  simpljoin.
  eapply bufferpend_succ_end_false in H3; eauto.
Qed.   


Lemma hapienterstep_hapistep_lemma:
  forall
  (pc0 : progunit) (pr pr0 : priority) (t1 t2 : addrval) (T1 T2 : tasks) 
  (C'0 C2: code) (cst1' cst2' : clientst) 
  (O1 O2 : osabst) (O1' O2' : osabst)
  (B : osapispec) (C : osintspec) (D : ossched) (tp : type)
  (f : fid) (tl : typelist) (r : list val -> spec_code) (vl' : list val) (vl : vallist)
  (ks0 ks: stmtcont) (i : taskdom),
  no_common_fid pc0 (api_spec, int_spec, get_hprio_d) ->
  pu_noabs pc0 -> 
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2 ->
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1' ->
  obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1' O2 ->
  obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1' O2 ->
  obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1' O2 ->
  (flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
          obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1' O2) ->
  (TauAct = TauAct \/ TauAct = SendAct \/ TauAct = RecvAct) -> 
  task_prio_id O1' pr t1 ->
  get O1' curtid = Some (oscurt t1) ->
  ~ in_intr T1 O1' ->
  nabt (set T1 t1 (curs (hapi_code (r (vl ++ vl'))), (kenil, ks))) ->
  get O2 curtid = Some (oscurt t2) ->
  dom_for_prio pr = dom_for_prio pr ->
  task_prio_id O2 pr t2 ->
  nabt (set T2 t2 C'0) ->
  ~ in_intr T2 O2 ->
  get T1 t1 = Some (curs (sfexec f (rev vl) (rev tl)), (kenil, ks)) ->
  obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1' O2 ->
  (forall (pr0 : priority) (t1 t2 : tid),
       dom_for_prio pr0 = dom_for_prio pr ->
       task_prio_id O1' pr0 t1 ->
       task_prio_id O2 pr0 t2 ->
       exists c1 c2 ke ks1 ks2,
       get T1 t1 = Some (c1, (ke, ks1)) /\
       get T2 t2 = Some (c2, (ke, ks2)) /\ cmd_equiv pr0 c1 c2 O1' O2 /\ cont_equiv pr0 ks1 ks2 O1' O2) ->
  flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
  (forall pr1 pr2 : priority,
      task_prio_id O1' pr1 t1 ->
      task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) ->
  get O1' curtid = Some (oscurt t1) ->
  bufs_equiv (dom_for_prio pr) O1' O2 ->
  kernel_data_equiv (dom_for_prio pr) O1' O2 ->
  client_data_equiv (dom_for_prio pr) cst1' cst2' O1' O2 ->
  kernel_task_equiv (dom_for_prio pr) O1' O2 ->
  kernel_mq_equiv (dom_for_prio pr) O1' O2 ->
  ports_equiv (dom_for_prio pr) O1' O2 ->
  ctid_equiv (dom_for_prio pr) O1' O2 ->
  get T2 t2 = Some C2 ->
  task_prio_id O2 pr t2 ->
  hapistep (api_spec, int_spec, get_hprio_d) C2 O2 C'0 O2' TauAct ->
  (api_spec, int_spec, get_hprio_d) = (B, C, D) ->
  tl_vl_match tl vl = true ->
  B f = Some (r, (tp, tl)) ->
  obsr_equiv_tskd get_hprio_d i
  (set T1 t1 (curs (hapi_code (r (vl ++ vl'))), (kenil, ks))) 
  (set T2 t2 C'0) cst1' cst2' O1' O2'.
Proof.
  intros.
  rename H into Hncfid. rename H0 into Hpu. rename H1 into Hrch2.
  rename H2 into Hrch1. rename H3 into Hsceq. rename H4 into Htmeq.
  rename H5 into Htdeq. rename H6 into Hfloweq. rename H7 into Hact.
  rename H8 into Htpi1. rename H9 into Hcurt1. rename H10 into Hnint1.
  rename H11 into Hnabt1. rename H12 into Hcurt2. rename H13 into Hdomeq.
  rename H14 into Htpi2. rename H15 into Hnabt2. rename H16 into Hnint2.
  rename H17 into HC1. rename H18 into Hd'eq. rename H19 into Hceq.
  rename H20 into Hstepdm. rename H21 into Hfa. rename H22 into Ht1_.
  rename H23 into Hbufe. rename H24 into Hkde. rename H25 into Hcde.
  rename H26 into Hkte. rename H27 into Hkqe. rename H28 into Hprte.
  rename H29 into Hctide_.
  rename H30 into HC2.
  rename H31 into H0. rename H32 into H2. rename H33 into H.
  rename H34 into H3. rename H35 into H6.

  (* hapienter_step for the left system *)
  inverts H2.

  (* hapienter_step for the right system --- possible *)
  unfold obsr_equiv_tskd.
  split.
  2:{ (* show data_equiv_tskd *)
     unfold obsr_equiv_tskd in Htdeq.
     destruct Htdeq as (Hcdeq_tskd & Hdteq_tskd).
     unfolds in Hdteq_tskd.
     destruct Hdteq_tskd as (Hctideq & Hbufseq & Hkdeq & Hcdeq).
     unfold data_equiv_tskd.
     splits; eauto. 
  }
  (* show code_equiv_tskd *)
  unfold code_equiv_tskd.
  introv Hd Htpi1' Htpi2'. 
  specialize (Hceq pr t1 t2 (eq_refl _)). 
  lets H__: Hceq Htpi1 Htpi2.
  destruct H__ as (c1 & c2 & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC1_. inverts HC2_. 
  assert (f = f0 /\ vl = vl0 /\ tl = tl0). 
  {
   destruct Hcmd as [Ha | Hb].
   destruct Ha as ((Hnk1 & Hnk2) & Hseq).  
   inverts Hseq.
   lets Heq: rev_eq_app vl (rev vl0) (nil: vallist).
   rewrite app_nil_r in Heq.
   rewrite rev_involutive in Heq.
   apply Heq in H7. 
   simpl in H7. 
   lets Heq_: rev_eq_app tl (rev tl0) (nil: list type).
   rewrite app_nil_r in Heq_.
   rewrite rev_involutive in Heq_.
   apply Heq_ in H9. 
   simpl in H9. 
   splits; auto.

   destruct Hb as (cd1 & cd2 & Hf & _). 
   inverts Hf. 
  }
  destruct H2. destruct H5.
  subst f0. subst vl. subst tl.

  casetac t1 t0 Heq1 Hneq1.
  2:{ (* t1 <> t0 ---- false*)
     casetac pr pr1 He Hne.
     subst pr1.
     lets Hf: tid_unique Htpi1 Htpi1'. 
     subst. tryfalse.
     casetac t2 t3 He' Hne'.
     subst t3. 
     lets Hf: prio_unique Htpi2 Htpi2'. 
     tryfalse.
     rewrite set_a_get_a'; eauto.
     rewrite set_a_get_a'; eauto.
     destruct Htdeq as (Hce0 & Hde0).
     unfolds in Hce0.
     gen Hce0. introv Hce0.
     lets H_: Hce0 Htpi1' Htpi2'.
     auto. eauto. 
  }
  subst t0.

  assert (t2 = t3).
  { 
   lets Hpp: prio_tid_corr Htpi1 Htpi2  Htpi1' Htpi2'.
   destruct Hpp; simpljoin; tryfalse. 
  }
  subst t3.
  rewrite set_a_get_a. rewrite set_a_get_a.
  subst.   

  match goal with H: (api_spec, _, _) = (_) |- _ => inverts H end.
  match goal with H: (api_spec, _, _) = (_) |- _ => inverts H end.
  unfold api_spec in H6, H8.
  unfold api_spec_list in H6, H8. 
  simpl in H6, H8. 
  destruct (Zeq_bool mq_send f) eqn: Ef1;
    destruct (Zeq_bool mq_recv f ) eqn: Ef2;
    destruct (Zeq_bool mq_timedrecv f) eqn: Ef2'; 
    destruct (Zeq_bool q_port_post f) eqn: Ef3;
    destruct (Zeq_bool q_port_pend f) eqn: Ef4; 
    destruct (Zeq_bool sample_port_post f) eqn: Ef4_;
    destruct (Zeq_bool port_accept f) eqn: Ef4__; 
    destruct (Zeq_bool buffer_post f) eqn: Ef5;
    destruct (Zeq_bool buffer_accept f) eqn: Ef6;
    destruct (Zeq_bool buffer_pend f) eqn: Ef7; 
    tryfalse;
    try eapply Zeq_bool_eq in Ef1;
    try eapply Zeq_bool_eq in Ef2;
    try apply Zeq_bool_eq in Ef2'; 
    try eapply Zeq_bool_eq in Ef3;
    try eapply Zeq_bool_eq in Ef4;
    try eapply Zeq_bool_eq in Ef4_; 
    try eapply Zeq_bool_eq in Ef4__; 
    try eapply Zeq_bool_eq in Ef5; 
    try eapply Zeq_bool_eq in Ef6; 
    try eapply Zeq_bool_eq in Ef7; 
    subst;
    inverts H6;
    inverts H8; 
    tryfalse.

  (* mqsend *)

  do 5 eexists. split; eauto. split; eauto.
  split.
  unfold cmd_equiv.
  right. 
  do 2 eexists.
  split; auto. split; auto.
  splits. 
  unfold head_asrt_sat.
  unfold mqsend. simpl. 
  destruct (vl0 ++ vl') eqn: eq1; simpl; auto. 
  destruct v; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v0; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v2; simpl; auto. 
  do 2 (destruct l; simpl; auto).
  destruct v2; simpl; auto.
  destruct v2; simpl; auto.

  unfold head_asrt_sat.
  unfold mqsend. simpl.
  destruct (vl0 ++ vl'0) eqn: eq2; simpl; auto. 
  destruct v; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v0; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v2; simpl; auto.
  destruct l; simpl; auto.
  destruct v2; simpl; auto.
  destruct l; simpl; auto.

  unfold vl_equiv. 
  unfold mqsend.
  destruct (vl0 ++ vl')eqn: eq3; simpl; auto.
  intros; tryfalse.
  destruct (vl0 ++ vl'0)eqn: eq4; simpl; eauto. 
  intros; tryfalse.
  destruct v; simpl; intros; tryfalse;
  try solve [destruct l; simpl in H; tryfalse].
  do 2 (destruct l; simpl in H; tryfalse). 
  destruct v3; simpl in H; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v4; simpl in H; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v5; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v5; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  inverts H. 
  rewrite nth_error_nil in H2; tryfalse.

  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1).
  rewrite set_a_get_a in Hnabt1.
  unfold mqsend; simpl. 
  destruct (vl0 ++ vl' ); simpl. 
  unfold mqsend in Hnabt1; simpl in Hnabt1.
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold mqsend in H.
  destruct v; simpl in H; simpljoin; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v0; simpl in H; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v1; simpl in H; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v2; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v2; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.

  left. unfold mqsend_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen:length vl0 = 4%nat).
  {
   clear -H4. simpl in H4.
   do 5 try destruct vl0; 
   try destruct v;
   try destruct v0;
   try destruct v1;
   try destruct v2;
   try destruct v3;
   simpl in H4; tryfalse.
   simpl; auto.
   simpl;auto.
  }
  splits; auto.

  (* show length vl' = 4%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 5 try destruct vl0; simpl in Hlen; tryfalse.
  do 5 try destruct vl'; simpl in Hnabt1; 
  try destruct v; try destruct v1; tryfalse;
  try destruct v3; try destruct v5; tryfalse;
  try destruct v6; try destruct v7; tryfalse.
  simpl. auto.

  (* show length vl'0 = 4%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  do 5 try destruct vl0; simpl in Hlen; tryfalse. 
  do 5 try destruct vl'0; simpl in Hnabt2; 
  try destruct v; try destruct v1; tryfalse; 
  try destruct v3; try destruct v4; tryfalse;
  try destruct v5; try destruct v6; try destruct v7; tryfalse; 
  simpl; auto.
  
  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.

  (* mqreceive *)

  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto.  split; auto.
  splits. 
  unfold head_asrt_sat.
  unfold mqreceive. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto. 
  destruct v; simpl; auto. 
  do 2 (destruct l; simpl; auto).
  destruct v0; simpl; auto. 
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v2; simpl; auto.
  do 2 (destruct l; simpl; auto).

  unfold head_asrt_sat.
  unfold mqreceive. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct v; simpl; auto. 
  do 2 (destruct l; simpl; auto).
  destruct v0; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v2; simpl; auto.
  do 2 (destruct l; simpl; auto).
  
  unfold vl_equiv.  
  unfold mqreceive.
  destruct (vl0 ++ vl') eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0) eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  destruct v; simpl; intros; tryfalse;
  try solve [destruct l; simpl in H; tryfalse].
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v3; simpl in H; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v4; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v5; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  inverts H.
  rewrite nth_error_nil in  H2; tryfalse.

  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  unfold mqreceive; simpl. 
  destruct (vl0 ++ vl' ); simpl. 
  unfold mqreceive in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold mqreceive in H.
  destruct v; simpl in H; simpljoin; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v0; simpl in H; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v1; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v2; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  
  right. left.
  unfold mqrecv_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen:length vl0 = 4%nat).
  {
   clear -H3. simpl in H3.
   do 5 try destruct vl0; 
   try destruct v;
   try destruct v0;
   try destruct v1;
   try destruct v2;
   try destruct v3;
   try destruct vl0 ;
   simpl in H3; tryfalse.
   simpl; auto.
   simpl;auto.
   simpl; auto.
   simpl;auto.
  }
  splits; auto.

  (* show length vl' = 4%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 5 try destruct vl0; simpl in Hlen; tryfalse.  
  do 5 try destruct vl'; simpl in Hnabt1; 
  try destruct v; try destruct v1; tryfalse;  
  try destruct v3; try destruct v4; tryfalse; 
  try destruct v5; try destruct v6; try destruct v7; tryfalse; 
  simpl; auto.

  (* show length vl'0 = 4%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  do 5 try destruct vl0; simpl in Hlen; tryfalse.  
  do 5 try destruct vl'0; simpl in Hnabt2; 
  try destruct v; try destruct v1; tryfalse; 
  try destruct v3; try destruct v4; tryfalse; 
  try destruct v5; try destruct v6; try destruct v7; tryfalse; 
  simpl; auto.

  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.
  
  (* mqtimedreceive *)

  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto. split; auto.
  splits. 
  unfold head_asrt_sat.
  unfold mqtimedreceive. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto.
  destruct v; simpl; auto. 
  do 2 (destruct l; simpl; auto).
  destruct v0; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.  
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).  

  unfold head_asrt_sat.
  unfold mqtimedreceive. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct v; simpl; auto. 
  do 2 (destruct l; simpl; auto).
  destruct v0; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  destruct v1; simpl; auto.
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  
  unfold vl_equiv.  
  unfold mqtimedreceive.
  destruct (vl0 ++ vl') eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0) eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  destruct v; simpl; intros; tryfalse;
  try solve [destruct l; simpl in H; tryfalse].
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v3; simpl in H; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v4; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v4; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v5; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  inverts H.
  rewrite nth_error_nil in  H2; tryfalse.

  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  unfold mqreceive; simpl. 
  destruct (vl0 ++ vl' ); simpl. 
  unfold mqreceive in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold mqtimedreceive in H. 
  destruct v; simpl in H; simpljoin; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v0; simpl in H; tryfalse.
  do 2 (destruct l; simpl in H; tryfalse).
  destruct v1; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v1; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v2; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  
  right. right. left.
  unfold mqtimedrecv_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen: length vl0 = 5%nat).
  {
    clear -H3. rename H3 into Htvm.
    do 5 try destruct vl0; 
    (simpl in Htvm; tryfalse).
    destruct v; tryfalse.
    destruct v; destruct v0; tryfalse. 
    destruct v; destruct v0; destruct v1; tryfalse.
    destruct v; destruct v0; destruct v1; destruct v2; tryfalse.
    destruct vl0; tryfalse.
    simpl; auto.
    destruct v; destruct v0; destruct v1; destruct v2; destruct v3; 
      simpl in Htvm; tryfalse; 
      match type of Htvm with
        (if ?e then _ else _) = _ => destruct e; tryfalse
      end.
  }
  splits; auto.

  (* show length vl' = 4%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 6 try destruct vl0; simpl in Hlen; tryfalse.  
  do 5 try destruct vl'; simpl in Hnabt1; 
  try destruct v; try destruct v1; tryfalse;  
  try destruct v3; try destruct v4; tryfalse; 
  try destruct v5; try destruct v6; try destruct v7; tryfalse; 
  simpl; auto.

  (* show length vl'0 = 4%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  do 6 try destruct vl0; simpl in Hlen; tryfalse.  
  do 5 try destruct vl'0; simpl in Hnabt2; 
  try destruct v; try destruct v1; tryfalse; 
  try destruct v3; try destruct v4; tryfalse; 
  try destruct v5; try destruct v6; try destruct v7; tryfalse; 
  simpl; auto.

  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.


  (* QPortPost *)

  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto.  split; auto.
  splits.
  unfold head_asrt_sat.
  unfold qportpost. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto. 
  destruct l; simpl; auto.
  destruct v0; simpl; auto.
  do 2 (destruct l; simpl; auto).
  
  unfold head_asrt_sat.
  unfold qportpost. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct l; simpl; auto. 
  destruct v0; simpl; auto.  
  do 2 (destruct l; simpl; auto).
  
  unfold vl_equiv.  
  unfold qportpost.
  destruct (vl0 ++ vl')eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0)eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  simpl; intros; tryfalse;
    try solve [destruct l; simpl in H; tryfalse].
  destruct l; simpl in H; tryfalse.
  destruct v3; simpl in H; tryfalse. 
  do 2 (destruct l; tryfalse).  
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  
  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  unfold mqreceive; simpl. 
  destruct (vl0 ++ vl' ); simpl. 
  unfold mqreceive in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold mqreceive in H. simpljoin. 
  destruct v; destruct l; tryfalse. 
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.

  right. right. right. left.
  unfold qprtpost_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen:length vl0 = 1%nat). 
  {
   clear -H3. simpl in H3.
   try destruct vl0; 
     try destruct v;
     try destruct vl0; 
     simpl in H3; tryfalse. 
   simpl; auto.
   simpl; auto. 
  }
  splits; auto.

  (* show length vl' = 2%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 2 try destruct vl0; simpl in Hlen; tryfalse.
  destruct vl'.
  simpl in Hnabt1. false.
  destruct vl'. destruct v0; simpl in Hnabt1; try solve [false]. 
  destruct vl'; try (simpl; auto).
  simpl in Hnabt1.
  destruct v0; simpl in Hnabt1; try solve [false]. 
    
  (* show length vl'0 = 2%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  destruct vl0; destruct vl'0; simpl in Hnabt2; try solve [false].
  destruct vl0. 
  destruct v; simpl in Hnabt2; try solve [false].
  simpl in Hlen. tryfalse.
  destruct vl0.
  destruct v0; simpl in Hnabt2; try solve [false].
  destruct vl'0; try solve [false].
  destruct vl'0; try solve [false].
  simpl; auto.
  simpl in Hlen. tryfalse. 

  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.

  (* QPortPend *)

  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto.  split; auto.
  splits.
  unfold head_asrt_sat.
  unfold qportpend. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto. 
  destruct l; simpl; auto.
  destruct l; simpl; auto.
  destruct v1; simpl; auto.
  destruct l; simpl; auto.
  destruct l; simpl; auto.
  
  unfold head_asrt_sat.
  unfold qportpend. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct l; simpl; auto. 
  destruct l; simpl; auto.
  destruct v1; simpl; auto.
  destruct l; simpl; auto.
  destruct l; simpl; auto.
  
  unfold vl_equiv.  
  unfold qportpend.
  destruct (vl0 ++ vl')eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0)eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  simpl; intros; tryfalse;
    try solve [destruct l; simpl in H; tryfalse].
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v4; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.  
  destruct l; simpl in H; tryfalse.  
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  
  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  destruct (vl0 ++ vl' ); simpl. 
  unfold qportpend in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold qportpend in H. simpljoin. 
  destruct l; tryfalse. 
  destruct l; tryfalse.
  destruct v1; destruct l; tryfalse.
  destruct l; tryfalse.

  right. right. right. right. left.
  unfold qprtpend_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen:length vl0 = 2%nat). 
  {
   clear -H3. simpl in H3.
   try destruct vl0; 
     try destruct v;
     try destruct vl0; 
     try destruct v;
     try destruct vl0;
     simpl in H3; tryfalse. 
   simpl; auto.
   simpl; auto. 
  }
  splits; auto.

  (* show length vl' = 2%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 3 try destruct vl0; simpl in Hlen; tryfalse.
  destruct vl'; simpl in Hnabt1; try solve [false].
  destruct vl'; destruct v1; simpl in Hnabt1; try solve [false]. 
  destruct vl'; try (simpl; auto). false. 
    
  (* show length vl'0 = 2%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  do 3 try destruct vl0; simpl in Hlen; tryfalse. 
  destruct vl'0; simpl in Hnabt2; try solve [false].
  destruct v1; destruct vl'0; simpl in Hnabt2; try solve [false]. 
  destruct vl'0; try (simpl; auto). false.

  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.

  (* sample_port_post *)

  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto.  split; auto.
  splits.
  unfold head_asrt_sat.
  unfold sampleportpost. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto. 
  destruct l; simpl; auto.
  destruct v0; simpl; auto.
  do 2 (destruct l; simpl; auto).
  
  unfold head_asrt_sat.
  unfold qportpost. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct l; simpl; auto. 
  destruct v0; simpl; auto.  
  do 2 (destruct l; simpl; auto).
  
  unfold vl_equiv.  
  unfold sampleportpost.
  destruct (vl0 ++ vl')eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0)eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  simpl; intros; tryfalse;
    try solve [destruct l; simpl in H; tryfalse].
  destruct l; simpl in H; tryfalse.
  destruct v3; simpl in H; tryfalse. 
  do 2 (destruct l; tryfalse).  
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  
  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  destruct (vl0 ++ vl' ); simpl. 
  unfold sampleportpost in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold sampleportpost in H. simpljoin. 
  destruct v; destruct l; tryfalse. 
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.

  right. right. right. right. right. left.
  unfold sprtpost_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen:length vl0 = 1%nat). 
  {
   clear -H3. simpl in H3.
   try destruct vl0; 
     try destruct v;
     try destruct vl0; 
     simpl in H3; tryfalse. 
   simpl; auto.
   simpl; auto. 
  }
  splits; auto.

  (* show length vl' = 2%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 2 try destruct vl0; simpl in Hlen; tryfalse.
  destruct vl'.
  simpl in Hnabt1. false.
  destruct vl'. destruct v0; simpl in Hnabt1; try solve [false]. 
  destruct vl'; try (simpl; auto).
  simpl in Hnabt1.
  destruct v0; simpl in Hnabt1; try solve [false]. 
    
  (* show length vl'0 = 2%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  destruct vl0; destruct vl'0; simpl in Hnabt2; try solve [false].
  destruct vl0. 
  destruct v; simpl in Hnabt2; try solve [false].
  simpl in Hlen. tryfalse.
  destruct vl0.
  destruct v0; simpl in Hnabt2; try solve [false].
  destruct vl'0; try solve [false].
  destruct vl'0; try solve [false].
  simpl; auto.
  simpl in Hlen. tryfalse. 

  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.

  (* port_accept *)
  
  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto.  split; auto.
  splits.
  unfold head_asrt_sat.
  unfold portaccept. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto. 
  destruct l; simpl; auto.
  destruct v0; simpl; auto.
  do 2 (destruct l; simpl; auto).
  
  unfold head_asrt_sat.
  unfold qportpost. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct l; simpl; auto. 
  destruct v0; simpl; auto.  
  do 2 (destruct l; simpl; auto).
  
  unfold vl_equiv.  
  unfold sampleportpost.
  destruct (vl0 ++ vl')eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0)eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  simpl; intros; tryfalse;
    try solve [destruct l; simpl in H; tryfalse].
  destruct l; simpl in H; tryfalse.
  destruct v3; simpl in H; tryfalse. 
  do 2 (destruct l; tryfalse).  
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  
  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  destruct (vl0 ++ vl' ); simpl. 
  unfold sampleportpost in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold portaccept in H. simpljoin. 
  destruct v; destruct l; tryfalse. 
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.
  destruct v; destruct l; tryfalse.

  right. right. right. right. right. right. left.
  unfold sprtpost_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen:length vl0 = 1%nat). 
  {
   clear -H3. simpl in H3.
   try destruct vl0; 
     try destruct v;
     try destruct vl0; 
     simpl in H3; tryfalse. 
   simpl; auto.
   simpl; auto. 
  }
  splits; auto.

  (* show length vl' = 2%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 2 try destruct vl0; simpl in Hlen; tryfalse.
  destruct vl'.
  simpl in Hnabt1. false.
  destruct vl'. destruct v0; simpl in Hnabt1; try solve [false]. 
  destruct vl'; try (simpl; auto).
  simpl in Hnabt1.
  destruct v0; simpl in Hnabt1; try solve [false]. 
    
  (* show length vl'0 = 2%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  destruct vl0; destruct vl'0; simpl in Hnabt2; try solve [false].
  destruct vl0. 
  destruct v; simpl in Hnabt2; try solve [false].
  simpl in Hlen. tryfalse.
  destruct vl0.
  destruct v0; simpl in Hnabt2; try solve [false].
  destruct vl'0; try solve [false].
  destruct vl'0; try solve [false].
  simpl; auto.
  simpl in Hlen. tryfalse. 

  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.
  
  (* buffer_post *)
  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto.  split; auto.
  splits.
  unfold head_asrt_sat.
  unfold bufferpost. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto. 
  destruct l; simpl; auto.
  destruct l; simpl; auto. 
  destruct v1; simpl; auto.
  do 2 (destruct l; simpl; auto).
  
  unfold head_asrt_sat.
  unfold bufferpost. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct l; simpl; auto. 
  destruct l; simpl; auto. 
  destruct v1; simpl; auto.  
  do 2 (destruct l; simpl; auto).
  
  unfold vl_equiv.  
  unfold bufferpost.
  destruct (vl0 ++ vl')eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0)eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  simpl; intros; tryfalse;
    try solve [destruct l; simpl in H; tryfalse].
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  destruct v4; simpl in H; tryfalse. 
  destruct l; simpl in H; tryfalse.
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  
  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  destruct (vl0 ++ vl' ); simpl. 
  unfold bufferpost in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold bufferpost in H. simpljoin. 
  destruct l; tryfalse. 
  destruct l; tryfalse. 
  destruct v1; tryfalse.
  destruct l; tryfalse. 

  right. right. right. right. right. right. right. left.
  unfold bufferpost_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen:length vl0 = 2%nat). 
  {
   clear -H3. simpl in H3.
   try destruct vl0; 
     try destruct vl'; 
     simpl in H3; tryfalse.
   destruct v; destruct vl0; tryfalse.
   destruct v; destruct vl0; tryfalse.
   simpl; auto.
   simpl; auto.
   destruct v; destruct vl0; tryfalse.
   simpl; auto.
   simpl; auto.
  }
  splits; auto.

  (* show length vl' = 1%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 3 try destruct vl0; simpl in Hlen; tryfalse.
  destruct vl'.
  simpl in Hnabt1. false.
  destruct vl'; simpl; auto. 
  destruct v1; simpl in Hnabt1; try solve [false].
    
  (* show length vl'0 = 1%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  do 3 try destruct vl0; simpl in Hlen; tryfalse. 
  destruct vl'0.
  simpl in Hnabt2. false.
  destruct vl'0; simpl; auto.
  destruct v1; simpl in Hnabt2; try solve [false].

  (* cont_equiv *)
  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.
  
  (* buffer_accept *)
  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto.  split; auto.
  splits.
  unfold head_asrt_sat.
  unfold bufferaccept. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto. 
  destruct l; simpl; auto.
  destruct l; simpl; auto. 
  
  unfold head_asrt_sat.
  unfold bufferaccept. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct l; simpl; auto. 
  destruct l; simpl; auto. 
  
  unfold vl_equiv.  
  unfold bufferaccept.
  destruct (vl0 ++ vl')eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0)eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  simpl; intros; tryfalse;
    try solve [destruct l; simpl in H; tryfalse].
  destruct l; simpl in H; tryfalse.
  destruct v3; simpl in H; tryfalse. 
  destruct l; simpl in H; tryfalse.
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  destruct l0;simpl in H; tryfalse.
  destruct l;simpl in H; tryfalse.
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  destruct l;simpl in H; tryfalse.
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  destruct l;simpl in H; tryfalse.
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  destruct (vl0 ++ vl' ); simpl. 
  unfold bufferaccept in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold bufferaccept in H. simpljoin. 

  destruct l; tryfalse. 
  destruct l; tryfalse. 

  right. right. right. right. right. right. right. right. left.
  unfold bufferaccept_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error.
  assert (Hlen:length vl0 = 1%nat). 
  {
   clear -H3. simpl in H3.
   try destruct vl0; 
     simpl in H3; tryfalse.
   try destruct v; try destruct vl0; tryfalse.
   simpl; auto.
   simpl; auto. 
  }
  splits; auto.

  (* show length vl' = 1%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 2 try destruct vl0; simpl in Hlen; tryfalse.
  destruct vl'.
  simpl in Hnabt1. false.
  destruct vl'; simpl; auto. 
  destruct v0; simpl in Hnabt1; try solve [false].
    
  (* show length vl'0 = 1%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  do 2 try destruct vl0; simpl in Hlen; tryfalse. 
  destruct vl'0.
  simpl in Hnabt2. false.
  destruct vl'0; simpl; auto.
  destruct v0; simpl in Hnabt2; try solve [false].

  (* cont_equiv *)
  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.

  (* buffer_pend *)
  do 5 eexists. split; eauto. split; eauto. split.
  unfold cmd_equiv.
  right. 
  do 2 eexists. split; auto.  split; auto.
  splits.
  unfold head_asrt_sat.
  unfold bufferpend. simpl. 
  destruct (vl0 ++ vl') eqn: eq2 ; simpl; auto. 
  destruct l; simpl; auto.
  destruct v0; simpl; auto.
  destruct l; simpl; auto.
  destruct l; simpl; auto.
  
  unfold head_asrt_sat.
  unfold bufferpend. simpl.
  destruct (vl0 ++ vl'0) eqn: eq3; simpl; auto. 
  destruct l; simpl; auto. 
  destruct v0; simpl; auto.  
  destruct l; simpl; auto. 
  destruct l; simpl; auto. 
  
  unfold vl_equiv.  
  unfold bufferpend.
  destruct (vl0 ++ vl')eqn: eq4; simpl; auto.  
  intros; tryfalse. 
  destruct (vl0 ++ vl'0)eqn: eq5; simpl; eauto. 
  intros; tryfalse.
  simpl; intros; tryfalse;
    try solve [destruct l; simpl in H; tryfalse].
  destruct l; simpl in H; tryfalse.
  destruct v3; simpl in H; tryfalse. 
  destruct l; simpl in H; tryfalse.
  destruct l; simpl in H; tryfalse.
  inverts H.
  rewrite nth_error_nil in H2; tryfalse.
  
  unfold stmt_equiv. 
  right. simpl. splits. 
  intro.

  unfold nabt in Hnabt1. 
  specialize (Hnabt1 t1).  
  rewrite set_a_get_a in Hnabt1.
  destruct (vl0 ++ vl' ); simpl. 
  unfold bufferpend in Hnabt1; simpl in Hnabt1.  
  specialize (Hnabt1 (curs (hapi_code (ABORT))) kenil ks1_ ).
  destruct Hnabt1; eauto; tryfalse.
  unfold bufferpend in H. simpljoin. 
  destruct l; tryfalse. 
  destruct v0; tryfalse.
  destruct l; tryfalse. 
  destruct l; tryfalse. 

  right. right. right. right. right. right. right. right. right. left.
  unfold bufferpend_equiv.
  exists vl0 vl' vl'0 0%nat.
  unfold get_all_succs.
  simpl nth_error. 
  assert (Hlen:length vl0 = 2%nat). 
  {
   clear -H3. simpl in H3.
   try destruct vl0; simpl in H3; tryfalse.
   destruct v; destruct vl0; tryfalse.
   destruct v; destruct vl0; tryfalse.
   simpl; auto.
   destruct (Int.unsigned i <=? Int16.max_unsigned); tryfalse.
   destruct v; tryfalse.
   destruct (Int.unsigned i <=? Int16.max_unsigned); tryfalse. 
   destruct vl0; tryfalse. 
   simpl; auto.
  }
  splits; auto.

  (* show length vl' = 1%nat *)
  clear -Hnabt1 Hlen.
  unfold nabt in Hnabt1.
  specialize (Hnabt1 t1). 
  rewrite set_a_get_a in Hnabt1.
  specialize (Hnabt1 _ _ _ (eq_refl _)).
  do 3 try destruct vl0; simpl in Hlen; tryfalse.
  destruct vl'.
  simpl in Hnabt1. destruct v0; tryfalse. 
  destruct vl'; simpl; tryfalse.
  auto.
  destruct v0; destruct v1; simpl in Hnabt1; try solve [false].
    
  (* show length vl'0 = 1%nat *)
  clear -Hnabt2 Hlen.
  unfold nabt in Hnabt2.
  specialize (Hnabt2 t2). 
  rewrite set_a_get_a in Hnabt2.
  specialize (Hnabt2 _ _ _ (eq_refl _)).
  do 3 try destruct vl0; simpl in Hlen; tryfalse. 
  destruct vl'0.
  simpl in Hnabt2. destruct v0; tryfalse. 
  destruct vl'0; simpl; auto.
  destruct v0; destruct v1; simpl in Hnabt2; try solve [false].

  (* cont_equiv *)
  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.  
  
  (* hidapi_step for the right system --- impossible *)
  unfold snd in H1.
  match goal with H: (api_spec, _, _) = (_) |- _ => inverts H end.
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  destruct Hnknl as (Hnknl12 & Hc1eqc2). 
  tryfalse.
  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
  tryfalse.

  (* hapiexit_step for the right system --- impossible *)
  match goal with H: (api_spec, _, _) = (_) |- _ => inverts H end.
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  destruct Hnknl as (Hnknl12 & Hc1eqc2). 
  tryfalse.
  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
  tryfalse.

  (* hintex_step for the right system --- impossible *)
  match goal with H: (api_spec, _, _) = (_) |- _ => inverts H end.
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  destruct Hnknl as (Hnknl12 & Hc1eqc2). 
  tryfalse.
  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
  tryfalse.
  
Qed.
   
Lemma intr_equiv_end_false:
  forall cd vo, intr_equiv cd (END vo) -> False. 
Proof.
  introv Hf.
  unfolds in Hf.
  simpljoin.
  repeat (destruct x; simpl in H0; tryfalse).
Qed. 
    
Require Import sem_prop_2.
Require Import api_intr_succs_prop. 

Lemma not_in_intr_intcont_none:
  forall T O t c ke ks, 
    ~ in_intr T O ->
    get O curtid = Some (oscurt t) ->
    get T t = Some (c, (ke, ks)) ->
    absintcont ks = None.
Proof.
  introv Hnin Hct Hgt.
  destruct (absintcont ks) eqn: E.
  - 
    false.
    apply Hnin.
    unfolds.
    unfold code_cur_task.  
    do 3 eexists.
    rewrite Hct.
    rewrite Hgt.
    split; eauto.
    introv Hf. rewrite E in Hf. false.
  -
    auto.
Qed.     

Lemma hidapistep_hapistep_lemma:
  forall
  (pc0 : progunit) (pr pr0 : priority) (t1 t2 : addrval) (T1 T2 : tasks) 
  (C' C'0 : code) (C1 C2 : code) (cst1' cst2' : clientst) 
  (O1 O2 : osabst) (O1' O2' : osabst) (act : action)
  (r : list val -> spec_code) (cd cd' : spec_code)
  (ke : exprcont) (ks0 ks: stmtcont) (i : taskdom),
  no_common_fid pc0 (api_spec, int_spec, get_hprio_d) ->
  pu_noabs pc0 -> 
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2 ->
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1 ->
  (flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
  obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2) ->
  obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1 O2 ->
  obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1 O2 ->
  obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1 O2 ->
  (act = TauAct \/ act = SendAct \/ act = RecvAct) ->
  ~ in_intr T1 O1 ->
  get O1 curtid = Some (oscurt t1) ->
  task_prio_id O1 pr t1 ->
  nabt (set T1 t1 (curs (hapi_code cd'), (ke, ks))) ->
  ~ in_intr T2 O2 ->
  get O2 curtid = Some (oscurt t2) ->
  dom_for_prio pr = dom_for_prio pr ->
  task_prio_id O2 pr t2 ->
  nabt (set T2 t2 C'0) ->
  get T1 t1 = Some (curs (hapi_code cd), (ke, ks)) ->
  (forall (pr0 : priority) (t1 t2 : tid),
       dom_for_prio pr0 = dom_for_prio pr ->
       task_prio_id O1 pr0 t1 ->
       task_prio_id O2 pr0 t2 ->
       exists c1 c2 ke ks1 ks2,
       get T1 t1 = Some (c1, (ke, ks1)) /\
       get T2 t2 = Some (c2, (ke, ks2)) /\ cmd_equiv pr0 c1 c2 O1 O2 /\ cont_equiv pr0 ks1 ks2 O1 O2) ->
  obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2 ->
  flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
  (forall pr1 pr2 : priority,
      task_prio_id O1 pr1 t1 ->
      task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) ->
  get O1 curtid = Some (oscurt t1) ->
  get O2 curtid = Some (oscurt t2) ->
  bufs_equiv (dom_for_prio pr) O1 O2 ->
  kernel_data_equiv (dom_for_prio pr) O1 O2 ->
  client_data_equiv (dom_for_prio pr) cst1' cst2' O1 O2 ->
  kernel_task_equiv (dom_for_prio pr) O1 O2 ->
  kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
  ports_equiv (dom_for_prio pr) O1 O2 ->
  buffer_equiv (dom_for_prio pr) O1 O2 -> 
  ctid_equiv (dom_for_prio pr) O1 O2 ->
  get T2 t2 = Some C2 ->
  hapistep (api_spec, int_spec, get_hprio_d) C2 O2 C'0 O2' act ->
  spec_step (snd (api_spec, int_spec, get_hprio_d)) cd O1 cd' O1' act ->
  cap_equiv (dom_for_prio pr) O1 O2 -> 
  obsr_equiv_tskd get_hprio_d i (set T1 t1 (curs (hapi_code cd'), (ke, ks)))
  (set T2 t2 C'0) cst1' cst2' O1' O2'.
Proof.
  (* hidapi_step for the left system *)
  intros.
  rename H into Hncfid. rename H0 into Hpu. rename H1 into Hrch2. 
  rename H2 into Hrch1. rename H3 into Hfloweq. rename H4 into Hsceq. 
  rename H5 into Htmeq. rename H6 into Htdeq. rename H7 into Hact. 
  rename H8 into Hnint1. rename H9 into Hcurt1. rename H10 into Htpi1. 
  rename H11 into Hnabt1. rename H12 into Hnint2. rename H13 into Hcurt2. 
  rename H14 into Hdomeq. rename H15 into Htpi2. rename H16 into Hnabt2. 
  rename H17 into HC1. rename H18 into Hceq. rename H19 into Hd'eq. 
  rename H20 into Hstepdm. rename H21 into Hfa. rename H22 into Ht1_.
  rename H23 into Ht2_. rename H24 into Hbufe. 
  rename H25 into Hkde. rename H26 into Hcde. rename H27 into Hkte.
  rename H28 into Hkme. rename H29 into Hprte. rename H30 into Hbfe.
  rename H31 into Hctide_. 
  rename H32 into HC2. rename H33 into H2. rename H34 into H.
  rename H35 into Hcpe. 

  lets Hrapistep: H2.
  inverts Hrapistep.

  (* hapienter_step for the right system --- impossible *)
  unfold snd in H.
  match goal with H: (api_spec, _, _) = (_) |- _ => inverts H end.
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  destruct Hnknl as (Hnknl12 & Hc1eqc2). 
  tryfalse.
  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
  tryfalse.
 
  2:{ (* hapiexit_step for the right system --- impossible *)
     unfold snd in H.
     lets H_: Hceq Hdomeq Htpi1 Htpi2.
     destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
     rewrite HC1 in HC1_.
     inverts HC1_. 
     rewrite HC2 in HC2_. 
     inverts HC2_.
     destruct Hcmd as [Hnknl | Hknl].
     destruct Hnknl as (Hnknl12 & Hc1eqc2). 

     destruct Hnknl12.
     lets Hc: hapistep_knl H2. 
     specialize (Hc (eq_refl _)).
     destruct Hc; tryfalse.
     simpljoin. tryfalse.

     destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
     assert(Hcd: ~(exists v, cd = END v)).
     { introv Hf.
       destruct Hf as (v_ & Hf).
       subst.
       inverts H.
     }
     assert(Hcd_nabt: (cd <> ABORT)).
     { introv Hf.
       subst.
       inverts H.
     }
     false.
     inverts Hcd1; inverts Hcd2.
     destruct H' as (Hsat & _ & _ & Hf).
     destruct Hf as [Hf | Hf].
     simpljoin.
     eapply Hcd; eauto.
     
     destruct Hf as (Hf & Hcase).
     apply Hf.
     
     destruct Hcase as [Hsend | [Hrecv | [Htrecv |
                                           [Hpost | [Hpend | [Hspost | [Hpacc | 
                                                      [Hbpost | [Hbacc | [Hbpend |
                                                                           [Hintr | Habt]]]]]]]]]]]. 

     (* Hsend *)
     unfolds in Hsend.
     simpljoin.     
     false. eapply Hcd.
     eapply mqsend_succs_ex_end_imp with (vl:=x) (vl':=x0) (vl'':= x1); eauto.
     (* Hrecv *)
     unfolds in Hrecv.
     simpljoin.
     false. eapply Hcd.
     eapply mqrecv_succs_ex_end_imp with (vl:=x) (vl':=x0) (vl'':= x1); eauto.
     (* Htrecv *)
     unfolds in Htrecv.
     simpljoin.
     false. eapply Hcd.
     eapply mqtimedrecv_succs_ex_end_imp with (vl:=x) (vl':=x0) (vl'':= x1); eauto.     
     (* Hpost *)
     eapply qprtpost_equiv_end_false in Hpost; tryfalse. 
     (* Hpend *)
     eapply qprtpend_equiv_end_false in Hpend; tryfalse.
     (* Hspost *)
     eapply sprtpost_equiv_end_false in Hspost; tryfalse. 
     (* Hpacc *)
     eapply prtaccept_equiv_end_false in Hpacc; tryfalse. 
     (* Hbpost *)
     eapply bufferpost_equiv_end_false in Hbpost; tryfalse.
     (* Hbacc *)
     eapply bufferaccept_equiv_end_false in Hbacc; tryfalse.
     (* Hbpend*)
     eapply bufferpend_equiv_end_false in Hbpend; tryfalse.
     (* Hintr *)
     eapply intr_equiv_end_false in Hintr; tryfalse. 
     (* Habt *)
     simpljoin. tryfalse.
  }

  2:{ (* hintex_step for the right system --- impossible *)
     unfold snd in H.
     lets H_: Hceq Hdomeq Htpi1 Htpi2.
     destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
     rewrite HC1 in HC1_.
     inverts HC1_. 
     rewrite HC2 in HC2_. 
     inverts HC2_.
     destruct Hcmd as [Hnknl | Hknl].
     destruct Hnknl as (Hnknl12 & Hc1eqc2). 

     destruct Hnknl12.
     lets Hc: hapistep_knl H2. 
     specialize (Hc (eq_refl _)).
     destruct Hc; tryfalse.
     simpljoin. tryfalse.

     destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
     assert(Hcd: ~(exists v, cd = END v)).
     { introv Hf.
       destruct Hf as (v_ & Hf).
       subst.
       inverts H.
     }
     assert(Hcd_nabt: (cd <> ABORT)).
     { introv Hf.
       subst.
       inverts H.
     }
     false.
     inverts Hcd1; inverts Hcd2.
     destruct H' as (Hsat & _ & _ & Hf).
     destruct Hf as [Hf | Hf].
     simpljoin.
     eapply Hcd; eauto.
     destruct Hf as (Hf & Hcase).
     destruct Hcase as [Hsend | [Hrecv | [Htrecv |
                                           [Hpost | [Hpend | [Hspost | [Hpacc | 
                                                      [Hbpost | [Hbacc | [Hbpend |
                                                                           [ Hintr | Habt ]]]]]]]]]]].
     (* Hsend *)
     unfolds in Hsend.
     simpljoin.
     eapply Hcd.
     eapply mqsend_succs_ex_end_imp with (vl:=x) (vl':=x0) (vl'':= x1); eauto.
     (* Hrecv *)
     unfolds in Hrecv.
     simpljoin.
     eapply Hcd.
     eapply mqrecv_succs_ex_end_imp with (vl:=x) (vl':=x0) (vl'':= x1); eauto.
     (* Htrecv *)
     unfolds in Htrecv.
     simpljoin.
     eapply Hcd.
     eapply mqtimedrecv_succs_ex_end_imp with (vl:=x) (vl':=x0) (vl'':= x1); eauto.     
     (* Hpost *)
     eapply qprtpost_equiv_end_false in Hpost; tryfalse. 
     (* Hpend *)
     eapply qprtpend_equiv_end_false in Hpend; tryfalse.
     (* Hspost *)
     eapply sprtpost_equiv_end_false in Hspost; tryfalse. 
     (* Hpacc *)
     eapply prtaccept_equiv_end_false in Hpacc; tryfalse. 
     (* Hbpost *)
     eapply bufferpost_equiv_end_false in Hbpost; tryfalse.
     (* Hbacc *)
     eapply bufferaccept_equiv_end_false in Hbacc; tryfalse.
     (* Hbpend *)
     eapply bufferpend_equiv_end_false in Hbpend; tryfalse. 
     (* Hintr *)
     eapply intr_equiv_end_false in Hintr; tryfalse. 
     (* Habt *)
     simpljoin. tryfalse.
  }

  (* hidapi_step for the right system --- possible *)
  unfold obsr_equiv_tskd.
  unfold snd in H0. unfold snd in H.

  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_.
  rewrite HC2_ in HC2. inverts HC2.
  destruct Hcmd as [Hnknl | Hknl].

  destruct Hnknl as (Hnknl12 & Hc1eqc2). 
  destruct Hnknl12.  apply knl_api in H1; tryfalse.
  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H'). subst.
  destruct H' as (Hhsat1 & Hhsat2 & Hvleq & Hsteq).
  unfold stmt_equiv in Hsteq.
  inverts Hcd1.
  inverts Hcd2.
  destruct Hsteq as [ (v & Hcd1 & Hcd2) | (Hnex & Hcases) ].  
  subst.
  inverts H.
  destruct Hcases as [Hsend | [Hrecv | [Htrecv |
                                         [Hpost | [Hpend | [Hspost | [Hbacc | 
                                                    [Hbpost | [Hbacc | [Hbpend |
                                                                         [Hintr | Habt]]]]]]]]]]].
  - 
    (* mq_send --- proof completed *)
    eapply hidapistep_hidapistep_mqsend_lemma; eauto.
  -
    (* mq_receive --- proof completed *)
    eapply hidapistep_hidapistep_mqreceive_lemma; eauto. 
  -
    (* mq_timedreceive --- proof completed *)
    eapply hidapistep_hidapistep_mqtdreceive_lemma; eauto. 
  -
    (* QPortPost --- proof completed *)
    eapply hidapistep_hidapistep_qprtpost_lemma; eauto. 
  -
    (* QPortPend --- proof completed *)
    eapply hidapistep_hidapistep_qprtpend_lemma; eauto.
  -
    (* Hspost *)
    eapply hidapistep_hidapistep_sprtpost_lemma; eauto. 
  -
    (* Hpacc *)
    eapply hidapistep_hidapistep_prtaccept_lemma; eauto. 
  -
    (* OSBufferPost --- proof completed *)
    eapply hidapistep_hidapistep_bufferpost_lemma; eauto. 
  -
    (* OSBufferAccept --- proofcompleted *)
    eapply hidapistep_hidapistep_bufferaccept_lemma; eauto.
  -
    (* OSBufferPend --- proof completed *) 
    eapply hidapistep_hidapistep_bufferpend_lemma; eauto. 
  -
    (* Hintr *)
    lets H1_: reachable_ks_noint_apicode Hpu Hrch1; eauto.
    lets H2_: reachable_ks_noint_apicode Hpu Hrch2; eauto.
    lets H1__: H1_ HC1. clear H1_.
    lets H2__: H2_ HC2_. clear H2_.
    simpl in H1__. destruct H1__ as (Hna1 & _).
    simpl in H2__. destruct H2__ as (Hna2 & _).
    specializes Hna1; eauto.
    { lets H__: not_in_intr_intcont_none Hnint1 Ht1_ HC1; eauto. }
    specializes Hna2; eauto.
    { lets H__: not_in_intr_intcont_none Hnint2 Ht2_ HC2_; eauto. }
    destruct Hna1 as [Ha1 | [Habt1 | Hend1]].
    2: {
      subst cd1.
      match goal with H: spec_step _ (ABORT) _ _ _ _ |- _ => inverts H end.
    }
    2: {
      destruct Hend1; subst cd1.
      match goal with H: spec_step _ (END _) _ _ _ _ |- _ => inverts H end.
    }
    destruct Hna2 as [Ha2 | [Habt2 | Hend2]].
    2: {
      subst cd2.
      match goal with H: spec_step _ (ABORT) _ _ _ _ |- _ => inverts H end.
    }
    2: {
      destruct Hend2; subst cd2.
      match goal with H: spec_step _ (END _) _ _ _ _ |- _ => inverts H end.
    }
    lets Hni1_: api_succs_not_tickisr_succ Ha1.
    lets Hni2_: api_succs_not_tickisr_succ Ha2.
    unfolds in Hintr.
    destruct Hintr as (k & Hf1 & Hf2).
    false.
    apply Hni1_. eexists; eauto.
    
  -
    (* Habt *)
    simpljoin.
    inverts H.
    
Qed.


Lemma hapiexitstep_hapistep_lemma:
  forall
  (pc0 : progunit) (pr pr0 : priority) (t1 t2 : addrval) (T1 T2 : tasks) 
  (C' C'0 : code) (C1 C2 : code) (cst1' cst2' : clientst) 
  (O1 O2 : osabst) (O1' O2' : osabst)
  (ke : exprcont) (v : option val) (ks0 ks: stmtcont) (i : taskdom),
  no_common_fid pc0 (api_spec, int_spec, get_hprio_d) ->
  pu_noabs pc0 -> 
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2 ->
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1' ->
  obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1' O2 ->
  obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1' O2 ->
  obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1' O2 ->
  (flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
          obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1' O2) ->
  (TauAct = TauAct \/ TauAct = SendAct \/ TauAct = RecvAct) ->
  task_prio_id O1' pr t1 ->
  get O1' curtid = Some (oscurt t1) ->
  ~ in_intr T1 O1' ->
  nabt (set T1 t1 (curs (sskip v), (ke, ks))) ->
  get O2 curtid = Some (oscurt t2) ->
  dom_for_prio pr = dom_for_prio pr ->
  task_prio_id O2 pr t2 ->
  nabt (set T2 t2 C'0) ->
  ~ in_intr T2 O2 ->
  get T1 t1 = Some (curs (hapi_code (END v)), (ke, ks)) ->
  obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1' O2 ->
  (forall (pr0 : priority) (t1 t2 : tid),
       dom_for_prio pr0 = dom_for_prio pr ->
       task_prio_id O1' pr0 t1 ->
       task_prio_id O2 pr0 t2 ->
       exists c1 c2 ke ks1 ks2,
       get T1 t1 = Some (c1, (ke, ks1)) /\
       get T2 t2 = Some (c2, (ke, ks2)) /\ cmd_equiv pr0 c1 c2 O1' O2 /\ cont_equiv pr0 ks1 ks2 O1' O2) ->
  flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
  (forall pr1 pr2 : priority,
      task_prio_id O1' pr1 t1 ->
      task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) ->
  get O1' curtid = Some (oscurt t1) ->
  get O2 curtid = Some (oscurt t2) ->
  bufs_equiv (dom_for_prio pr) O1' O2 ->
  kernel_data_equiv (dom_for_prio pr) O1' O2 ->
  client_data_equiv (dom_for_prio pr) cst1' cst2' O1' O2 ->
  kernel_task_equiv (dom_for_prio pr) O1' O2 ->
  kernel_mq_equiv (dom_for_prio pr) O1' O2 ->
  ports_equiv (dom_for_prio pr) O1' O2 ->
  ctid_equiv (dom_for_prio pr) O1' O2 ->
  get T2 t2 = Some C2 ->
  task_prio_id O2 pr t2 ->
  hapistep (api_spec, int_spec, get_hprio_d) C2 O2 C'0 O2' TauAct ->
  absintcont ks = None ->
  obsr_equiv_tskd get_hprio_d i (set T1 t1 (curs (sskip v), (ke, ks))) 
  (set T2 t2 C'0) cst1' cst2' O1' O2'.
Proof.
  (* hidapi_step for the left system *)
  intros.
  rename H into Hncfid. rename H0 into Hpu. rename H1 into Hrch2.
  rename H2 into Hrch1. rename H3 into Hsceq. rename H4 into Htmeq.
  rename H5 into Htdeq. rename H6 into Hfloweq. rename H7 into Hact.
  rename H8 into Htpi1. rename H9 into Hcurt1. rename H10 into Hnint1.
  rename H11 into Hnabt1. rename H12 into Hcurt2. rename H13 into Hdomeq.
  rename H14 into Htpi2. rename H15 into Hnabt2. rename H16 into Hnint2.
  rename H17 into HC1. rename H18 into Hd'eq. rename H19 into Hceq.
  rename H20 into Hstepdm. rename H21 into Hfa. rename H22 into Ht1_.
  rename H23 into Ht2_. rename H24 into Hbufe. rename H25 into Hkde. rename H26 into Hcde.
  rename H27 into Hkte. rename H28 into Hkqe. rename H29 into Hprte.
  (* rename H30 into Hkprte. *)
  rename H30 into Hctide_. rename H31 into HC2.
  rename H32 into H0. rename H33 into H2. rename H34 into H.

  (* hapienter_step for the left system *)
  lets Hrapistep: H2.
  inverts Hrapistep.

  (* hapienter_step for the right system --- impossible *)
  match goal with H: (api_spec, _, _) = (_) |- _ => inverts H end.
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  destruct Hnknl as (Hnknl12 & Hc1eqc2). 
  tryfalse.
  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
  tryfalse.

  (* hidapi_step for the right system --- impossible *)
  unfold snd in H1.
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  destruct Hnknl as (Hnknl12 & Hc1eqc2). 

  destruct Hnknl12.
  lets Hc: hapistep_knl H2. 
  specialize (Hc (eq_refl _)).
  destruct Hc; tryfalse.
  simpljoin. tryfalse.

  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
  assert(Hcd: ~(exists v, cd = END v)).
  { introv Hf.
    destruct Hf as (v_ & Hf).
    subst.
    inverts H1.
  }
  assert(Hcd_nabt: (cd <> ABORT)).
  { introv Hf.
    subst.
    inverts H1.
  }
  false.
  inverts Hcd1; inverts Hcd2.
  destruct H' as (Hsat & _ & _ & Hf).
  destruct Hf as [Hf | Hf].
  simpljoin.
  eapply Hcd; eauto.
  destruct Hf as (Hf & Hcase).
  destruct Hcase as [Hsend | [Hrecv | [Htrecv |
                                        [Hpost | [Hpend | [Hspost | [Hpacc | 
                                                   [Hbpost | [Hbacc | [Hbpend |
                                                                        [Hintr | Habt]]]]]]]]]]]. 
  (* Hsend *)
  unfolds in Hsend.
  simpljoin.
  eapply Hcd.
  eapply mqsend_succs_ex_end_imp with (vl:=x) (vl':=x1) (vl'':= x0); eauto.
  (* Hrecv *)
  unfolds in Hrecv.
  simpljoin.
  eapply Hcd.
  eapply mqrecv_succs_ex_end_imp with (vl:=x) (vl':=x1) (vl'':= x0); eauto.
  (* Htrecv *)
  unfolds in Htrecv.
  simpljoin.
  eapply Hcd.
  eapply mqtimedrecv_succs_ex_end_imp with (vl:=x) (vl':=x1) (vl'':= x0); eauto.  
  (* Hpost *)
  unfold qprtpost_equiv in Hpost.
  simpljoin.
  match goal with H: _ = Some (END _) |- _ => eapply qportpost_succ_end_false in H; eauto end.
  (* Hpend *)
  unfold qprtpend_equiv in Hpend.
  simpljoin.
  match goal with H: _ = Some (END _) |- _ => eapply qportpend_succ_end_false in H; eauto end.
  (* Hspost *)
  unfold sprtpost_equiv in Hspost.
  simpljoin.
  match goal with H: _ = Some (END _) |- _ => eapply sprtpost_succ_end_false in H; eauto end.
  (* Hpacc *)
  unfold prtaccept_equiv in Hpacc.
  simpljoin.
  match goal with H: _ = Some (END _) |- _ => eapply prtacc_succ_end_false in H; eauto end.  
  (* Hbpost *)
  unfold bufferpost_equiv in Hbpost.
  simpljoin.
  match goal with H: _ = Some (END _) |- _ => eapply bufferpost_succ_end_false in H; eauto end.  
  (* Hbacc *)
  unfold bufferaccept_equiv in Hbacc.
  simpljoin.
  match goal with H: _ = Some (END _) |- _ => eapply bufferaccept_succ_end_false in H; eauto end.    
  (* Hbpend *)
  unfold bufferpend_equiv in Hbpend.
  simpljoin.
  match goal with H: _ = Some (END _) |- _ => eapply bufferpend_succ_end_false in H; eauto end.  
  (* Hintr *)
  unfolds in Hintr.
  destruct Hintr as (k & Hf' & _).
  repeat (destruct k; simpl in Hf'; tryfalse).  
  (* Habt *)
  simpljoin. tryfalse.

  (* hintex_step for the right system --- impossible *)
  2:{
     lets H_: Hceq Hdomeq Htpi1 Htpi2.
     destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
     rewrite HC1 in HC1_.
     inverts HC1_. 
     rewrite HC2 in HC2_. 
     inverts HC2_.
     unfold cont_equiv in Hcont.
     destruct Hcont as [Hcont1 | Hcont2].
     destruct Hcont1 as (Hks1_ & Hks2_ & Hkseq).
     unfold absintcont in H.
     rewrite Hkseq in H.
     tryfalse.
     destruct Hcont2 as (c1 & c2 & ke & ks' & Hks1_ & Hkseq & Hcmd1).
     unfold absintcont in H.
     rewrite Hks1_ in H.
     tryfalse. 
  }
  
  (* hapiexit_step for the right system --- impossible *)
  unfold obsr_equiv_tskd.
  split.
  2:{ (* show data_equiv_tskd *)
     unfold obsr_equiv_tskd in Htdeq.
     destruct Htdeq as (Hcdeq_tskd & Hdteq_tskd).
     unfolds in Hdteq_tskd.
     destruct Hdteq_tskd as (Hctideq & Hbufseq & Hkdeq & Hcdeq).
     unfold data_equiv_tskd.
     splits; eauto. 
  }
  
  (* show code_equiv_tskd *)
  unfold code_equiv_tskd.
  introv Hd Htpi1' Htpi2'. 
  specialize (Hceq pr t1 t2 (eq_refl _)). 
  lets H__: Hceq Htpi1 Htpi2.
  destruct H__ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC1_. inverts HC2_. 

  assert (v = v0).
  {
   destruct Hcmd as [Ha | Hb].
   destruct Ha as ((Hnk1 & Hnk2) & Hseq).  
   inverts Hseq; eauto.

   destruct Hb as (cd1 & cd2 & Hendv & Hendv0 & Hhcd1 & Hhcd2 & Hvl & Hstmt). 
   unfold stmt_equiv in Hstmt.
   destruct Hstmt as [ Hend | Hendno ].
   inverts Hendv.
   inverts Hendv0.
   destruct Hend.
   inverts H3.
   rewrite <- H4 in H5.
   inverts H5; eauto.

   inverts Hendv.
   inverts Hendv0.
   destruct Hendno.
   false.
   match goal with H: ~_ |- _ => apply H end. 
   eexists; eauto. 
  }
  subst.

  casetac t1 t0 Heq1 Hneq1.

  2:{ 
     casetac pr pr1 He Hne.
     subst pr1. 
     lets Hf: tid_unique Htpi1 Htpi1'. 
     subst. tryfalse.
     casetac t2 t3 He' Hne'.
     subst t3. 
     lets Hf: prio_unique Htpi2 Htpi2'. 
     tryfalse.
     rewrite set_a_get_a'; eauto.
     rewrite set_a_get_a'; eauto.
     destruct Htdeq as (Hce0 & Hde0).
     unfolds in Hce0.
     gen Hce0. introv Hce0.
     lets H_: Hce0 Htpi1' Htpi2'.
     auto. eauto. 
  }

  subst t0.
  assert (t2 = t3).
  { 
   lets Hpp: prio_tid_corr Htpi1 Htpi2  Htpi1' Htpi2'.
   destruct Hpp; simpljoin; tryfalse. 
  }
  subst t3.
  rewrite set_a_get_a. 
  rewrite set_a_get_a.
  subst. 

  do 5 eexists. split; eauto. split; eauto.
  split.
  unfold cmd_equiv in *.
  destruct Hcmd as [Hnkel | Hkel].
  destruct Hnkel as ((Hnk1 & Hnk2) & Hseq).
  apply knl_api in Hnk1; tryfalse.

  left.
  splits; eauto.
  split.
  unfold not_knl_stmt.
  right.
  exists (sskip v0).
  split; eauto.
  introv Hf.
  inverts Hf; tryfalse.
  unfold not_knl_stmt.
  right.
  exists (sskip v0).
  split; eauto.
  introv Hf.
  inverts Hf; tryfalse.

  asserts_rewrite (pr1 = pr).
  { eapply prio_unique; eauto. }
  eauto.

Qed.

 
Lemma hintexstep_hapistep_lemma:
  forall
  (pc0 : progunit) (pr pr0 : priority) (t1 t2 : addrval) (T1 T2 : tasks) 
  (C' C'0 : code) (C1 C2 : code) (cst1' cst2' : clientst) 
  (O1 O2 : osabst) (O1' O2' : osabst) (c : cureval)
  (ke : exprcont) (ks0 ks: stmtcont) (i : taskdom),
  no_common_fid pc0 (api_spec, int_spec, get_hprio_d) ->
  pu_noabs pc0 -> 
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2 ->
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1' ->
  obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1' O2 ->
  obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1' O2 ->
  obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1' O2 ->
  (flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
          obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1' O2) ->
  (TauAct = TauAct \/ TauAct = SendAct \/ TauAct = RecvAct) ->
  task_prio_id O1' pr t1 ->
  get O1' curtid = Some (oscurt t1) ->
  ~ in_intr T1 O1' ->
  nabt (set T1 t1 (c, (ke, ks))) ->
  get O2 curtid = Some (oscurt t2) ->
  dom_for_prio pr = dom_for_prio pr ->
  task_prio_id O2 pr t2 ->
  nabt (set T2 t2 C'0) ->
  ~ in_intr T2 O2 ->
  get T1 t1 = Some (curs (hapi_code (END None)), (kenil, kevent c ke ks)) ->
  obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1' O2 ->
  (forall (pr0 : priority) (t1 t2 : tid),
       dom_for_prio pr0 = dom_for_prio pr ->
       task_prio_id O1' pr0 t1 ->
       task_prio_id O2 pr0 t2 ->
       exists c1 c2 ke ks1 ks2,
       get T1 t1 = Some (c1, (ke, ks1)) /\
       get T2 t2 = Some (c2, (ke, ks2)) /\ cmd_equiv pr0 c1 c2 O1' O2 /\ cont_equiv pr0 ks1 ks2 O1' O2) ->
  flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
  (forall pr1 pr2 : priority,
      task_prio_id O1' pr1 t1 ->
      task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) ->
  bufs_equiv (dom_for_prio pr) O1' O2 ->
  kernel_data_equiv (dom_for_prio pr) O1' O2 ->
  client_data_equiv (dom_for_prio pr) cst1' cst2' O1' O2 ->
  kernel_task_equiv (dom_for_prio pr) O1' O2 ->
  kernel_mq_equiv (dom_for_prio pr) O1' O2 ->
  ports_equiv (dom_for_prio pr) O1' O2 ->
  ctid_equiv (dom_for_prio pr) O1' O2 ->
  get T2 t2 = Some C2 ->
  task_prio_id O2 pr t2 ->
  hapistep (api_spec, int_spec, get_hprio_d) C2 O2 C'0 O2' TauAct ->
  obsr_equiv_tskd get_hprio_d i (set T1 t1 (c, (ke, ks))) (set T2 t2 C'0) cst1' cst2'
  O1' O2'. 
Proof.
  (* hintex_step for the left system *)
  intros.
  rename H into Hncfid. rename H0 into Hpu. rename H1 into Hrch2.
  rename H2 into Hrch1. rename H3 into Hsceq. rename H4 into Htmeq.
  rename H5 into Htdeq. rename H6 into Hfloweq. rename H7 into Hact.
  rename H8 into Htpi1. rename H9 into Hcurt1. rename H10 into Hnint1.
  rename H11 into Hnabt1. rename H12 into Hcurt2. rename H13 into Hdomeq.
  rename H14 into Htpi2. rename H15 into Hnabt2. rename H16 into Hnint2.
  rename H17 into HC1. rename H18 into Hd'eq. rename H19 into Hceq.
  rename H20 into Hstepdm. rename H21 into Hfa. rename H22 into Hbufe. 
  rename H23 into Hkde. rename H24 into Hcde.
  rename H25 into Hkte. rename H26 into Hkqe. 
  rename H27 into Hkprte. rename H28 into Hctide_.
  rename H29 into HC2.
  rename H30 into H0. rename H31 into H2.

  lets Hrapistep: H2.
  inverts Hrapistep.
  
  (* hapienter_step for the right system --- impossible *)
  match goal with H: (api_spec, _, _) = (_) |- _ => inverts H end.
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  destruct Hnknl as (Hnknl12 & Hc1eqc2). 
  tryfalse.
  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
  tryfalse.

  (* hidapi_step for the right system --- impossible *)
  unfold snd in H.
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  destruct Hnknl as (Hnknl12 & Hc1eqc2). 

  destruct Hnknl12.
  lets Hc: hapistep_knl H2. 
  specialize (Hc (eq_refl _)).
  destruct Hc; tryfalse.
  simpljoin. tryfalse.

  destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
  assert(Hcd: ~(exists v, cd = END v)).
  { introv Hf.
    destruct Hf as (v_ & Hf).
    subst.
    inverts H.
  }
  assert(Hcd_nabt: (cd <> ABORT)).
  { introv Hf.
    subst.
    inverts H.
  }
  false.
  inverts Hcd1; inverts Hcd2.
  destruct H' as (Hsat & _ & _ & Hf).
  destruct Hf as [Hf | Hf].
  simpljoin.
  eapply Hcd; eauto.
  destruct Hf as (Hf & Hcase).
  destruct Hcase as [Hsend | [Hrecv | [Htrecv |
                                        [Hpost | [Hpend | [Hspost | [Hpacc |
                                                   [Hbpost | [Hbacc | [Hbpend |
                                                                        [Hintr | Habt]]]]]]]]]]].
  (* Hsend *)
  unfolds in Hsend.
  simpljoin.
  eapply Hcd.
  eapply mqsend_succs_ex_end_imp with (vl:=x) (vl':=x1) (vl'':= x0); eauto.
  (* Hrecv *)
  unfolds in Hrecv.
  simpljoin.
  eapply Hcd.
  eapply mqrecv_succs_ex_end_imp with (vl:=x) (vl':=x1) (vl'':= x0); eauto.
  (* Htrecv *)
  unfolds in Htrecv.
  simpljoin.
  eapply Hcd.
  eapply mqtimedrecv_succs_ex_end_imp with (vl:=x) (vl':=x1) (vl'':= x0); eauto.  
  (* Hpost *)
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ = Some (END None) |- _ => eapply qportpost_succ_end_false in H; eauto end.
  (* Hpend *)
  unfolds in Hpend.
  simpljoin.
  match goal with H: _ = Some (END None) |- _ => eapply qportpend_succ_end_false in H; eauto end.
  (* Hspost *)
  unfolds in Hspost.
  simpljoin.
  match goal with H: _ = Some (END None) |- _ => eapply sprtpost_succ_end_false in H; eauto end.
  (* Hpacc *)
  unfolds in Hpacc.
  simpljoin.
  match goal with H: _ = Some (END None) |- _ => eapply prtacc_succ_end_false in H; eauto end.
  (* Hbpost *)
  unfolds in Hbpost.
  simpljoin.
  match goal with H: _ = Some (END None) |- _ => eapply bufferpost_succ_end_false in H; eauto end.
  (* Hbacc *)
  unfolds in Hbacc.
  simpljoin.
  match goal with H: _ = Some (END None) |- _ => eapply bufferaccept_succ_end_false in H; eauto end.
  (* Hbpend *)
  unfolds in Hbpend.  
  simpljoin.
  match goal with H: _ = Some (END None) |- _ => eapply bufferpend_succ_end_false in H; eauto end.
  (* Hintr *)
  unfolds in Hintr.
  destruct Hintr as (k & Hf' & _). repeat (destruct k; simpl in Hf'; tryfalse). 
  (* Habt *)
  simpljoin. tryfalse.  
  
  (* hapiexit_step for the right system --- impossible *)
  lets H_: Hceq Hdomeq Htpi1 Htpi2.
  destruct H_ as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_. 
  rewrite HC2 in HC2_. 
  inverts HC2_.

  unfold cont_equiv in Hcont.
  destruct Hcont as [Hcont1 | Hcont2].
  destruct Hcont1 as (Hks1_ & Hks2_ & Hkseq).
  unfold absintcont in H.
  rewrite <- Hkseq in H.
  tryfalse.
  destruct Hcont2 as (c1 & c2 & ke0 & ks' & Hks1_ & Hkseq & Hcmd1).
  unfold absintcont in H.
  rewrite Hkseq in H.
  tryfalse.

  (* hintex_step for the right system --- possible *)
  unfold obsr_equiv_tskd.
  split.
  (*            data_equiv_tskd  *)
  2:{
    unfold obsr_equiv_tskd in Htdeq.
    destruct Htdeq as (Hcdeq_tskd & Hdteq_tskd).
    unfolds in Hdteq_tskd.
    destruct Hdteq_tskd as (Hctideq & Hbufseq & Hkdeq & Hcdeq).
    unfold data_equiv_tskd.
    splits; eauto. 
  }
  (*           code_equiv_tskd   *)
  {
    unfold code_equiv_tskd.
    introv Hd Htpi1' Htpi2'.
    specialize (Hceq pr t1 t2 (eq_refl _)). 
    lets H__: Hceq Htpi1 Htpi2.
    destruct H__ as (c1 & c2 & ke_ & ks1_ &ks2_ & HC1_ & HC2_ & Hcmde & Hconte).
    eapply reachable_kevt_nnest in Hrch1.
    eapply reachable_kevt_nnest in Hrch2.
    unfold pool_kevt_no_nest in Hrch2.
    unfold pool_kevt_no_nest in Hrch1.
    specialize (Hrch1 t1 c1 ke_ ks1_ ). 
    specialize (Hrch2 t2 c2 ke_ ks2_ ). 
    lets Hkevnet1: Hrch1 HC1_.
    lets Hkevnet2: Hrch2 HC2_.
    rewrite HC1 in HC1_.
    rewrite HC2 in HC2_.
    unfold cont_equiv in Hconte.
    destruct Hconte as [Hcontke|Hcontkne].
    destruct Hcontke as(Hcontke1 & Hcontke2 & Hcontke3).
    ---inverts HC1_. inverts HC2_.
       casetac t1 t0 Heq1 Hneq1.
       2:{ 
         casetac pr pr1 He Hne.
         subst pr1.
         lets Hf: tid_unique Htpi1 Htpi1'.
         subst. tryfalse.
         casetac t2 t3 He' Hne'.
         subst t3.
         lets Hf: prio_unique Htpi2 Htpi2'.
         tryfalse.
         rewrite set_a_get_a'; eauto.
         rewrite set_a_get_a'; eauto.
         destruct Htdeq as (Hce0 & Hde0).
         unfolds in Hce0.
         gen Hce0. introv Hce0.
         lets H_: Hce0 Htpi1' Htpi2'.
         auto. eauto. 
       }
       subst t0.
       assert (t2 = t3).
       { lets H_: prio_tid_corr Htpi1 Htpi2  Htpi1' Htpi2'.
         destruct H_. simpljoin. destruct H. tryfalse. }
       subst t3.
       rewrite set_a_get_a. rewrite set_a_get_a.
       subst.
       inverts H1.
       do 5 eexists. split; eauto. split; eauto. 
       split.
       unfold cmd_equiv.
       assert(Hcases: not_knl_stmt c \/ ~(not_knl_stmt c)) by tauto.
       destruct Hcases as [Hnk | Hk].
       auto.
       right.
       unfold not_knl_stmt in Hk.
       eapply Decidable.not_or in Hk.
       destruct Hk.
       destruct c.
       destruct H.
       eexists.
       eauto.
       destruct H1.
       eexists.
       split.
       eauto.
       destruct s;destruct Hcontke1;do 3 eexists;eauto.
       unfold cont_equiv.
       left.
       split.
       destruct Hcontke1.
       do 3 eexists.
       eauto.
       split.
       destruct Hcontke1.
       do 3 eexists.
       eauto.
       eauto.
    --- inverts HC1_.
        inverts HC2_.
        casetac t1 t0 Heq1 Hneq1.
        2:{ 
          casetac pr pr1 He Hne.
          subst pr1.
          lets Hf: tid_unique Htpi1 Htpi1'.
          subst. tryfalse.
          casetac t2 t3 He' Hne'.
          subst t3.
          lets Hf: prio_unique Htpi2 Htpi2'.
          tryfalse.
          rewrite set_a_get_a'; eauto.
          rewrite set_a_get_a'; eauto.
          destruct Htdeq as (Hce0 & Hde0).
          unfolds in Hce0.
          gen Hce0. introv Hce0.
          lets H_: Hce0 Htpi1' Htpi2'.
          auto. eauto. 
        }
        subst t0.
        assert (t2 = t3).
        {
          lets H_: prio_tid_corr Htpi1 Htpi2  Htpi1' Htpi2'.
          destruct H_. simpljoin. destruct H. tryfalse.
        }
        subst t3.
        rewrite set_a_get_a. rewrite set_a_get_a.
        subst.
        destruct Hcontkne.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H1.
        inverts H.
        inverts H1.
        do 5 eexists.
        split;eauto.
        split;eauto.
        split;eauto.

        asserts_rewrite (pr1 = pr).
        { eapply prio_unique; eauto. }
        auto. 
        
        unfold cont_equiv. 
        destruct x2. 
        11: {
          simpl in Hkevnet1.
          tryfalse.
        }
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
        left.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        split.
        intro.
        do 3 destruct H.
        tryfalse.
        auto.
  }
Qed.

Lemma cstep_hapistep_lemma:
  forall
    (pc pc0 : progunit) (T1 T2 : tasks) (O1 O2 O2': osabst) (cst2' : clientst) 
    (i : taskdom) (cenvs1 : cltenvs) (M1 M1' : mem) (ges1 : taskdom -> env) 
    (pr pr0 : priority) (t1 t2 : addrval) (c' c1 c c1': cureval) (ke1' ke_: exprcont) 
    (ks1' ks1_ ks2_: stmtcont) (C' C : code) (t : tid) (le1' le1 : env) (A : osspec)
    (Hpu : pu_noabs pc)
    (Hncfid : no_common_fid pc (api_spec, int_spec, get_hprio_d)) 
    (Hrch2 : reachable (pc, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2)
    (Hrch1 : reachable (pc, (api_spec, int_spec, get_hprio_d)) T1 (ges1, cenvs1, M1) O1) 
    (Hsceq : obsr_equiv get_hprio_d SchedDom T1 T2 (ges1, cenvs1, M1) cst2' O1 O2) 
    (Htmeq : obsr_equiv get_hprio_d TransDom T1 T2 (ges1, cenvs1, M1) cst2' O1 O2) 
    (Htdeq : obsr_equiv_tskd get_hprio_d i T1 T2 (ges1, cenvs1, M1) cst2' O1 O2) 
    (Hfloweq : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
               obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 (ges1, cenvs1, M1) cst2' O1 O2)
    (Hact : TauAct = TauAct \/ TauAct = SendAct \/ TauAct = RecvAct) 
    (Htpi1 : task_prio_id O1 pr t1) 
    (Hcurt1 : get O1 curtid = Some (oscurt t1)) 
    (Hnint1 : ~ in_intr T1 O1)
    (Hnabt1 : nabt (set T1 t1 (c1', (ke1', ks1')))) 
    (Hnint2 : ~ in_intr T2 O2) 
    (Hcurt2 : get O2 curtid = Some (oscurt t2)) 
    (Hdomeq : dom_for_prio pr = dom_for_prio pr) 
    (Htpi2 : task_prio_id O2 pr t2) 
    (Hnabt2 : nabt (set T2 t C')) 
    (Heqc : c = c1) 
    (HC1 : get T1 t1 = Some (c, (ke_, ks1_))) 
    (Hd'eq : obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 (ges1, cenvs1, M1) cst2' O1 O2) 
    (Hceq : forall (pr0 : priority) (t1 t2 : tid),
        dom_for_prio pr0 = dom_for_prio pr ->
        task_prio_id O1 pr0 t1 ->
        task_prio_id O2 pr0 t2 ->
        exists c1 c2 ke ks1 ks2,
          get T1 t1 = Some (c1, (ke, ks1)) /\
            get T2 t2 = Some (c2, (ke, ks2)) /\ cmd_equiv pr0 c1 c2 O1 O2 /\ cont_equiv pr0 ks1 ks2 O1 O2)
    (Hstepdm : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)) 
    (Hfa : forall pr1 pr2 : priority,
        task_prio_id O1 pr1 t1 ->
        task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) 
    (Ht1_ : get O1 curtid = Some (oscurt t1))
    (Ht2_ : get O2 curtid = Some (oscurt t2)) 
    (Hbufe : bufs_equiv (dom_for_prio pr) O1 O2) 
    (Hkde : kernel_data_equiv (dom_for_prio pr) O1 O2) 
    (Hcde : client_data_equiv (dom_for_prio pr) (ges1, cenvs1, M1) cst2' O1 O2) 
    (Hkte : kernel_task_equiv (dom_for_prio pr) O1 O2) 
    (Hkqe : kernel_mq_equiv (dom_for_prio pr) O1 O2) 
    (Hprte : ports_equiv (dom_for_prio pr) O1 O2) 
    (Hctide_ : ctid_equiv (dom_for_prio pr) O1 O2) 
    (Hcstep1 : cstep pc (dom_for_prio pr)
                 (c, (ke_, ks1_)) (ges1 (dom_for_prio pr), le1, M1) (c1', (ke1', ks1')) (ges1 (dom_for_prio pr), le1', M1')) 
    (Hle1 : get cenvs1 t1 = Some le1) 
    (HC2_ : get T2 t2 = Some (c, (ke_, ks2_))) 
    (Hnknl1_ Hnknl2_ :  not_knl_stmt c) 
    (Hcont : cont_equiv pr0 ks1_ ks2_ O1 O2) 
    (H : get O2 curtid = Some (oscurt t)) 
    (H0 : task_prio_id O2 pr0 t) 
    (H4 : get T2 t = Some C) 
    (Hsyseq : (pc, (api_spec, int_spec, get_hprio_d)) = (pc0, A)) 
    (Hstep2 : hapistep A C O2 C' O2' TauAct),  
    
    obsr_equiv_tskd get_hprio_d i (set T1 t1 (c1', (ke1', ks1'))) (set T2 t C')
      (ges1, set cenvs1 t1 le1', M1') cst2' O1 O2'.

Proof.
  intros.
  match goal with
    H: get T2 _ = Some ?C |- _ => rename C into C2; rename H into HC2
  end.
  match goal with
    H1: get O2 curtid = _, H2: get O2 curtid = _ |- _ =>
      rewrite H1 in H2; symmetry in H2; inverts H2
  end.
  assert (pr0 = pr). { eapply prio_unique; eauto. }
  subst.
  
  (* rewrite Ht2_ in HC2. inverts HC2. *)
  rewrite HC2_ in HC2. inverts HC2.
  inverts Hsyseq.
  
  (* lets Hnknl2: cstep_not_knl_eval Hcstep1. *)
  lets Hceqcs: Hceq Hdomeq Htpi1 Htpi2.
  destruct Hceqcs as (c1_ & c2_ & ke__ & ks1__ & ks2__ & HC1__ & HC2__ & Hcmd & Hcont_).
  unfold cmd_equiv in Hcmd.
  rewrite HC1 in HC1__.
  inverts HC1__.
  rename c1_ into c1.
  rewrite HC2__ in HC2_. inverts HC2_.
  destruct Hcmd as [Hnknl | Hknl].
  -
    (* not kernel statements *)
    destruct Hnknl as (Hnknl12 & Hc1eqc2). subst.
    lets Hf: cstep_apistep_contra_ext Hncfid Hcstep1 Hstep2.
    inverts Hf.
  -    
    (* kernel statements *)
    destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
    rewrite Hcd2 in Hnknl2_. inverts Hnknl2_.
    simpljoin. tryfalse.
    simpljoin.
    match goal with H: curs _ = curs _ |- _ => inverts H end.
    false.
    match goal with H: ~_ |- _ => apply H end.
    eexists; eauto.
Qed.         

Lemma hapistep_cstep_lemma:
  forall
  (pc pc0 : progunit) (T1 T2 : tasks) (cst1' : clientst) (O1 O1' O2' : osabst) 
  (i : taskdom) (cenvs : cltenvs) (M M': mem) (ges : taskdom -> env) 
  (pr pr0 : priority) (t1 t2 : addrval) (C1 C' C2 C'0 : code) (le' : env) 
  (A : osspec) (le : env)
  (Hpu : pu_noabs pc) 
  (Hncfid : no_common_fid pc (api_spec, int_spec, get_hprio_d)) 
  (Hrch1 : reachable (pc, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1) 
  (Hrch2 : reachable (pc, (api_spec, int_spec, get_hprio_d)) T2 (ges, cenvs, M) O2') 
  (Hsceq : obsr_equiv get_hprio_d SchedDom T1 T2 cst1' (ges, cenvs, M) O1 O2') 
  (Htmeq : obsr_equiv get_hprio_d TransDom T1 T2 cst1' (ges, cenvs, M) O1 O2') 
  (Htdeq : obsr_equiv_tskd get_hprio_d i T1 T2 cst1' (ges, cenvs, M) O1 O2') 
  (Hfloweq :
    flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
    obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' (ges, cenvs, M) O1 O2')
  (Hact :  TauAct = TauAct \/ TauAct = SendAct \/ TauAct = RecvAct)
  (Hnint1 : ~ in_intr T1 O1) 
  (Hcurt1 : get O1 curtid = Some (oscurt t1)) 
  (Htpi1 : task_prio_id O1 pr t1) 
  (Hnabt1 : nabt (set T1 t1 C')) 
  (Hcurt2 : get O2' curtid = Some (oscurt t2)) 
  (Hnint2 : ~ in_intr T2 O2') 
  (Hdomeq : dom_for_prio pr = dom_for_prio pr) 
  (Htpi2 : task_prio_id O2' pr t2) 
  (Hnabt2 : nabt (set T2 t2 C'0)) 
  (HC1 : get T1 t1 = Some C1) 
  (Hd'eq : obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' (ges, cenvs, M) O1 O2') 
  (Hceq : code_equiv_tskd (dom_for_prio pr) T1 T2 O1 O2') 
  (Hstepdm : flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)) 
  (Ht1_ : get O1 curtid = Some (oscurt t1)) 
  (Hbufe : bufs_equiv (dom_for_prio pr) O1 O2') 
  (Hkde : kernel_data_equiv (dom_for_prio pr) O1 O2') 
  (Hcde : client_data_equiv (dom_for_prio pr) cst1' (ges, cenvs, M) O1 O2') 
  (Hkte : kernel_task_equiv (dom_for_prio pr) O1 O2') 
  (Hkqe : kernel_mq_equiv (dom_for_prio pr) O1 O2') 
  (Hprte : ports_equiv (dom_for_prio pr) O1 O2') 
  (Hctide_ : ctid_equiv (dom_for_prio pr) O1 O2') 
  (Ht2_ : get O2' curtid = Some (oscurt t2)) 
  (Hfa : forall pr1 pr2 : priority,
      task_prio_id O1 pr1 t1 ->
      task_prio_id O2' pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) 
  (Hstep1 : hapistep (api_spec, int_spec, get_hprio_d) C1 O1 C' O1' TauAct) 
  (HC2 : get T2 t2 = Some C2) 
  (H0 : task_prio_id O2' pr t2) 
  (H : (pc, (api_spec, int_spec, get_hprio_d)) = (pc0, A)) 
  (H2 : task_prio_id O2' pr0 t2) 
  (H4 : dom_for_prio pr0 = dom_for_prio pr) 
  (Hstep2 : cstep pc0 (dom_for_prio pr) C2 (ges (dom_for_prio pr), le, M) C'0 (ges (dom_for_prio pr), le', M')) 
  (H9 : get cenvs t2 = Some le),
    
    obsr_equiv_tskd get_hprio_d i (set T1 t1 C') (set T2 t2 C'0) cst1' (ges, set cenvs t2 le', M') O1' O2'.

Proof.
  intros.
  match goal with H: (_, (api_spec, _, _)) = (_, _) |- _ => inverts H end.
  destruct C1 as (c1 & ke1 & ks1).
  destruct C2 as (c2 & ke2 & ks2).
  destruct C'0 as (c2' & ke2' & ks2'). 
  lets Hnknl2: cstep_not_knl_eval Hstep2. 
  unfold code_equiv_tskd in Hceq.
  lets Hceqcs: Hceq Hdomeq Htpi1 Htpi2.
  destruct Hceqcs as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hcmd & Hcont).
  rewrite HC1 in HC1_.
  inverts HC1_.
  rename c1_ into c1.
  rewrite HC2_ in HC2. inverts HC2.
  destruct Hcmd as [Hnknl | Hknl].
  -
    (* not kernel statements *)
    destruct Hnknl as (Hnknl12 & Hc1eqc2). subst.
    lets Hf: cstep_apistep_contra_ext Hncfid Hstep2 Hstep1.
    inverts Hf.
  -
    (* kernel statements *)
    destruct Hknl as (cd1 & cd2 & Hcd1 & Hcd2 & H').
    rewrite Hcd2 in Hnknl2. inverts Hnknl2.
    simpljoin. tryfalse.
    simpljoin.
    match goal with H: curs _ = curs _ |- _ => inverts H end. 
    false.
    match goal with H: ~_ |- _ => apply H end.
    eexists; eauto.
Qed. 

Lemma cont_equiv_nkevt_eq: 
  forall ks1 ks2 O1 O2 pr, 
    absintcont ks1 = None -> 
    cont_equiv pr ks1 ks2 O1 O2 -> 
    ks1 = ks2. 
Proof.
  introv Hnk Hce.
  inverts Hce.
  simpljoin.
  simpljoin.
  simpl in Hnk.
  tryfalse. 
Qed.   

Lemma callcont_absintcont_none:
  forall ks f s E ks',
    absintcont ks = None ->
    callcont ks = Some (kcall f s E ks') ->
    absintcont ks' = None. 
Proof.
  induction ks; introv Hk Hcc;
    try (simpl in Hcc; tryfalse; fail); 
    try (simpl in Hk; simpl in Hcc; eapply IHks; eauto; fail). 
  simpl in Hk. simpl in Hcc. inverts Hcc.
  auto. 
Qed.   
        
Lemma ks_nkevt_cstep_preserve: 
  forall pc td c ke ks ge le M c' ke' ks' ge' le' M', 
    cstep pc td (c, (ke, ks)) (ge, le, M) (c', (ke', ks')) (ge', le', M') -> 
    absintcont ks = None ->
    ~exists c_ ke_ ks_, ks' = kevent c_ ke_ ks_. 
Proof.
  introv Hcs Hn Hex.
  inverts Hcs; try (simpljoin; tryfalse; fail).
  inverts H7.
  match goal with
    H: sstep _ _ _ _ _ _ _ _ |- _ => inverts H; try (simpljoin; tryfalse; fail)
  end.
  inverts H. inverts H0. 
  lets H_: callcont_absintcont_none Hn H1; eauto.
  simpljoin.
  simpl in H_. tryfalse. 
Qed.     

Lemma obsr_equiv_tskd_sym_: 
  forall sc td T1 T2 cst1 cst2 O1 O2, 
    ct_ex_prio_dom_eq O1 O2 ->
    obsr_equiv_tskd sc td T1 T2 cst1 cst2 O1 O2 ->
    obsr_equiv_tskd sc td T2 T1 cst2 cst1 O2 O1. 
Proof.
  introv cep Hoe.
  unfold obsr_equiv_tskd in *.
  destruct Hoe as (Hcet & Hdet).
  split.
  -
    eapply code_equiv_tskd_sym; eauto.
  -
    unfold data_equiv_tskd in *.
    simpljoin.
    splits.
    + eapply ctid_equiv_sym_; eauto.
    + eapply bufs_equiv_sym; eauto.
    + eapply kernel_data_equiv_sym; eauto. 
    + eapply client_data_equiv_sym; eauto. 
Qed.       

Require Import ct_pp_lemmas.
Require Import if_good_code. 
Require Import confidentiality_tactics. 

Require Import data_invs.

Lemma reachable_get_ctid: 
  forall hp T cst O,
    reachable hp T cst O ->
    exists t, get O curtid = Some (oscurt t).               
Proof.
  introv Hrc.
  unfolds in Hrc.
  simpljoin.
  lets H_: hpstepokstar_eqdomO0 H1.
  unfold init in H0.
  destruct H0 as (Hinittsk & Hinitst).
  unfolds in Hinitst.
  simpljoin.
  unfold init_tsk_st in *.
  simpljoin.

  unfold eqdomO0 in H_.
  destruct H_ as (H1_2 & _).
  unfolds in H1_2.
  specialize (H1_2 curtid).
  match goal with H: get _ curtid = _ |- _ => rewrite H in H1_2 end.
  auto.
Qed. 


Lemma reachable_htstep_ct_same_pp: 
  forall pu T cst O t d cst' O' C C' act, 
    good_client_code pu -> 
    reachable (pu, (api_spec, int_spec, get_hprio_d)) T cst O ->
    ~ in_intr T O ->
    get O curtid = Some (oscurt t) -> 
    get T t = Some C -> 
    htstep (pu, (api_spec, int_spec, get_hprio_d)) t d C cst O C' cst' O' act ->
    ((exists t, get O curtid = Some (oscurt t)) /\
       get O curtid = get O' curtid /\ 
       prio_preserved O O').  
Proof.
  introv Hgoodcli Hrc Hnintr Hct HC Hsp. 
  lets Hpu: good_client_code_impl_noabs Hgoodcli. 
  lets Hgc: reachable_get_ctid Hrc; eauto.
  split; auto. 
  inverts Hsp.
  - (* cstep *)
    match goal with H: (_, _) = _ |- _ => inverts H end.
    split; auto.
    eapply prio_preserved_refl. 
 - (*  hapistep *)
    match goal with H: (_, _) = _ |- _ => inverts H end.
    match goal with H: context [hapistep] |- _ => inverts H end.
    + split; auto.
      apply prio_preserved_refl.
    + split.
      eapply spec_step_ctid_eq; eauto.
      destruct Hgc as (t_ & Hgct).
      l_rew12_inv2 (get O curtid).
      lets H__: reachable_ks_noint_apicode Hpu Hrc.
      lets H_: H__ HC; eauto. 
      lets Hni: nintr_absintcont_none HC; eauto.
      specializes Hni; eauto.
      simpl in H_.
      destruct H_ as (Hna & _).
      unfolds in Hna.
      specializes Hna; eauto.
      destruct Hna as [Hcd | [Habt | Hend]].
      *
        destruct Hcd as (fid & ac & ft & vl & Hgf & Hin).
        eapply spec_step_prio_preserved; eauto. 
      *
        subst.
        match goal with H: context [spec_step] |- _ => inverts H end.
      *
        simpljoin.
        match goal with H: context [spec_step] |- _ => inverts H end.
    + split; auto.
      apply prio_preserved_refl.
    + split; auto.
      apply prio_preserved_refl.
Qed.      


Lemma reachable_htstep_ct_ex_prio_dom_eq:
  forall pu T cst O t d cst' O' C C' act, 
    good_client_code pu -> 
    reachable (pu, (api_spec, int_spec, get_hprio_d)) T cst O ->
    ~ in_intr T O ->
    get O curtid = Some (oscurt t) -> 
    get T t = Some C -> 
    htstep (pu, (api_spec, int_spec, get_hprio_d)) t d C cst O C' cst' O' act ->
    ct_ex_prio_dom_eq O O'. 
Proof.
  introv Hgoodcli Hrc Hnintr Hgct HC Hsp.
  lets H__: reachable_htstep_ct_same_pp Hgoodcli Hrc Hnintr; eauto.
  specializes H__; eauto.
  simpljoin.  
  eapply ctid_same_prio_preserved_dest; eauto. 
Qed. 








Theorem confidentiality_u_holds:
  forall cliprogs,
    good_client_code cliprogs -> 
    no_common_fid cliprogs (api_spec, int_spec, get_hprio_d) ->
    confidentiality_u (cliprogs, (api_spec, int_spec, get_hprio_d)).
Proof.
  introv Hgoodcli (* Hpu *) Hncfid.
  lets Hpu: good_client_code_impl_noabs Hgoodcli.
  unfold confidentiality_u.
  introv Hhp Hrch1 Hrch2 Hsceq Htmeq Htdeq Hfloweq.
  introv Hstep1 Hstep2.

  inverts Hhp.

  rename td into i.

  (************************** obsr. equiv. for task domain  **************************)

  unfold obsr_equiv. unfold obsr_equiv in Htdeq.
  inverts Hstep1; subst.
  -  (* task step (as opposed to sched step) by left system *)
    rename t into t1.
    rename pr into pr1.
    match goal with H: hpstep _ T1 _ _ _ _ _ _ |- _ => rename H into Hstep1 end.
    match goal with H: get O1 curtid = _ |- _ => rename H into Hcurt1 end.
    match goal with H: task_prio_id O1 _ _ |- _ => rename H into Htpi1 end.
    match goal with H: ~in_intr T1 _ |- _ => rename H into Hnint1 end.
    match goal with H: nabt T1' |- _ => rename H into Hnabt1 end.
    match goal with H: (act = _ \/ _) |- _ => rename H into Hact end.

    inverts Hstep2; subst.
    rename t into t2.
    rename pr into pr2.

    match goal with H: hpstep _ T2 _ _ _ _ _ _ |- _ => rename H into Hstep2 end.
    match goal with H: get O2 curtid = _ |- _ => rename H into Hcurt2 end.
    match goal with H: task_prio_id O2 _ _ |- _ => rename H into Htpi2 end.
    match goal with H: ~in_intr T2 _ |- _ => rename H into Hnint2 end.
    match goal with H: nabt T2' |- _ => rename H into Hnabt2 end.

    match goal with H: dom_for_prio _ = dom_for_prio _ |- _ => rename H into Hdomeq end.

    inverts Hstep1.
    +  (* htstep by left system *)
      assert (t = t1) by congruence. subst.
      match goal with H: htstep _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hhtstep1 end.
      match goal with
        H: get T1 _ = Some ?C |- _ => rename H into HC1; rename C into C1
      end.
      lets Hpreq: prio_unique Htpi1 H0. subst pr.
      clr_redundant Htpi1 H0.
      clr_redundant Hcurt1 H.

      remember (dom_for_prio pr1) as d1.

      assert (Hflcs: flowsTo (TaskDom d1) (TaskDom i)
                     \/ ~flowsTo (TaskDom d1) (TaskDom i)) by tauto.
      destruct Hflcs as [Hstepdm | Hstepdm'].
      * (* flowsTo (TaskDom d1) (TaskDom i) *)
        (* (dom for step) flows to (dom for obsr. equiv.) *)
        lets Hd'eq: Hfloweq Hstepdm.
        assert (Hd'eq_ := Hd'eq).
        unfolds in Hd'eq_.
        unfold obsr_equiv_tskd in Hd'eq_.
        destruct Hd'eq_ as (Hceq & Hdeq).
        unfold data_equiv_tskd in Hdeq.
        destruct Hdeq as (Hctide & Hbufe & Hkde & Hcde).
        assert (Hkde_ := Hkde).
        unfold kernel_data_equiv in Hkde_.
        destruct Hkde_ as (Hkte & Hkqe & Hprte & Hbfe & Hcape).
        
        assert (Hctide_ := Hctide).
        destruct Hctide as (t1_ & t2_ & Ht1_ & Ht2_ & Hfa).
        assert (Ht1eq: t1_ = t1) by congruence.
        subst t1_.
        assert (Ht2eq: t2_ = t2) by congruence.
        subst t2_.
        assert (pr1 = pr2). { eapply Hfa; eauto. }
        remember pr1 as pr. subst pr1. subst pr2.

        inverts Hhtstep1. (* htstep ... *)
        -- (* cstep by left system *)
          match goal with H: (pu, (api_spec, _, _)) = (_, _) |- _ => inverts H end.
          
          rename O1' into O1. 
          rename le into le1. 
          rename M into M1. 
          rename M' into M1'. 
          rename C' into C1'. 
          rename ges into ges1. 
          rename cenvs into cenvs1. 
          rename le' into le1'. 
          match goal with H: get cenvs1 t1 = _ |- _ => rename H into Hle1 end. 
          match goal with H: cstep _ _ _ _ _ _ |- _ => rename H into Hcstep1 end. 

          assert (pr0 = pr). { eapply prio_unique; eauto. }
          subst pr0.
          clr_redundant Htpi1 H0.
          clr_redundant Hdomeq H2.

          destruct C1 as (c1 & ke1 & ks1).
          destruct C1' as (c1' & ke1' & ks1').

          lets Hnknl1: cstep_not_knl_eval Hcstep1. 
          unfold code_equiv_tskd in Hceq.
          lets Hceqcs: Hceq Hdomeq Htpi1 Htpi2.

          destruct Hceqcs as (c1_ & c2_ & ke_ & ks1_ & ks2_ & HC1_ & HC2_ & Hor & Hcont).
          rewrite HC1 in HC1_.
          inverts HC1_.
          rename c1_ into c1.
          destruct Hor as [Hnknl | Hknl].
          2: { (* the statement executed by the left system is a kernel statement --- impossible *) 
            destruct Hknl as (cd1 & cd2 & Hapicode1 & Hapicode2 & Hsat1 & Hsa2 & Hvleq & Hstmte).
            rewrite Hapicode1 in Hnknl1.
            apply knl_api in Hnknl1.
            tryfalse.
          }

          (* the statement executed by the left system is not a kernel statement *) 
          destruct Hnknl as ((Hnknl1_ & Hnknl2_) & Hceq12).
          remember c1 as c.
          subst c2_.
          
          inverts Hstep2. 
          match goal with H: htstep _ _ _ _ _ _ _ _ _ _ |- _ => inverts H end.

          2: { (* hapistep for right system *)
            assert (t2 = t) by congruence. subst t.
            eapply cstep_hapistep_lemma; eauto.
          }

          (* cstep for the right system *)
          match goal with H: (pc, (api_spec, _, _)) = (?pc, _) |- _ => inverts H end.
          match goal with Hcstep1: _, H: cstep _ _ _ _ _ _ |- _ => rename H into Hcstep2 end.
          assert (t2 = t) by congruence. subst t.
          match goal with H: get T2 t2 = _ |- _ => rewrite HC2_ in H; inverts H end.
          rename ges into ges2.
          rename cenvs into cenvs2.
          rename le into le2.
          rename le' into le2'.
          rename M into M2.
          rename M' into M2'.
          rename O2' into O2.
          destruct C'  as (c2' & ke2' & ks2').

          assert (pr0 = pr). { eapply prio_unique; eauto. }
          subst pr0.

          lets Hnkev: reachable_nknl_nkevt Hrch1 HC1 Hnknl1.
          lets Hkeq: cont_equiv_nkevt_eq Hnkev Hcont.

          unfold obsr_equiv_tskd.
          split.
          2: { (* show data_equiv_tskd *)
            unfold obsr_equiv_tskd in Htdeq.
            destruct Htdeq as (Hcdeq_tskd & Hdteq_tskd).
            unfolds in Hdteq_tskd.
            destruct Hdteq_tskd as (Hctideq & Hbufseq & Hkdeq & Hcdeq). 
            
            unfold data_equiv_tskd.
            splits; eauto.
            casetac (dom_for_prio pr) i Hdeq Hndeq.
            - subst. 
              eapply cli_no_cross_part_read; eauto.
            - subst. 
              eapply cli_no_cross_part_read_ext; eauto.
          }
          (* show code_equiv_tskd *) 
          unfold code_equiv_tskd.
          introv Hd Htpi1' Htpi2'.
          casetac t1 t0 Heq1 Hneq1.
          ---
            subst t0.
            assert (t2 = t3).
            { lets H_: prio_tid_corr Htpi1 Htpi2  Htpi1' Htpi2'.
              destruct H_; simpljoin; tryfalse. }
            subst t3.
            rewrite set_a_get_a. rewrite set_a_get_a.
            subst. 
            lets H_: cli_no_cross_part_read Hrch1 Hrch2 Hcde Htpi1 Htpi2.
            lets H__: H_ HC1 HC2_ Hle1 H11. clear H_.
            lets H_: H__ Hcstep1 Hcstep2. clear H__.
            destruct H_ as (Hceq' & Hcde').
            inverts Hceq'.
            do 5 eexists. split; eauto. split; eauto.
            split.
            (* cmd_equiv *) 
            left. split; auto.
            lets Hnknl: (cstep_not_knl_eval' (pc0, (api_spec, int_spec, get_hprio_d))) Hpu; eauto.
            (* cont_equiv *)
            left. splits; auto.
            eapply ks_nkevt_cstep_preserve; eauto.
            eapply ks_nkevt_cstep_preserve; eauto.
            
          ---
            casetac pr pr0 He Hne.
            subst pr0. lets Hf: tid_unique Htpi1 Htpi1'. subst. tryfalse.
            casetac t2 t3 He' Hne'.
            subst t3. lets Hf: prio_unique Htpi2 Htpi2'. tryfalse.
            (* t1 <> t0 /\ t2 <> t3 *)
            rewrite set_a_get_a'; eauto.
            rewrite set_a_get_a'; eauto.
            destruct Htdeq as (Hce0 & Hde0).
            unfolds in Hce0.
            gen Hce0. introv Hce0.
            lets H_: Hce0 Hd Htpi1' Htpi2'.
            auto.

        -- (* hapistep by left system *)
          inverts H.
          match goal with H: hapistep _ C1 _ _ _ _ |- _ => rename H0 into Hstep1 end.
          inverts Hstep2.
          --- (* htstep for right system *) 
            match goal with
              H: get T2 t = Some ?C |- _ => rename C into C2; rename H into HC2
            end.
            match goal with
              H1: get O2 curtid = _, H2: get O2 curtid = _ |- _ =>
                rewrite H1 in H2; symmetry in H2; inverts H2
            end.
            assert (pr0 = pr). { eapply prio_unique; eauto. }
            subst.
            match goal with H: htstep _ _ _ _ _ _ _ _ _ _ |- _ => inverts H end.
            ---- (* cstep for right system -- impossible *) 
              eapply hapistep_cstep_lemma; eauto.
              
            ---- (* hapistep for the right system *)
              match goal with H: (_, (api_spec, _, _)) = (_, _) |- _ => inverts H end.
              unfold code_equiv_tskd in Hceq. 
              inverts Hstep1.
              match goal with
                H1: get O2 curtid = _, H2: get O2 curtid = _ |- _ =>
                  rewrite H1 in H2; symmetry in H2; inverts H2
              end.
              
              (* hapienter_step for the left system --- complete*)
              eapply hapienterstep_hapistep_lemma; eauto.

              (* hidapi_step for the left system --- complete*)
              eapply hidapistep_hapistep_lemma; eauto.

              (* hapiexit_step for the left system --- complete*)
              eapply hapiexitstep_hapistep_lemma; eauto.

              (* hintex_step for the left system --- complete*)
              eapply hintexstep_hapistep_lemma; eauto.

          --- (* htistep for right system -- impossible *)
            match goal with H: (_, (api_spec, _, _)) = (_, _) |- _ => inverts H end.
            unfold code_equiv_tskd in Hceq.
            lets H_: Hceq Hdomeq Htpi1 Htpi2.
            rewrite HC1 in H_.
            assert (t = t2) by congruence.
            subst t. 
            rewrite H2 in H_.
            destruct C1 as (c1, (ke1, ks1)). 
            lets Hc: hapistep_tau_or_knl Hstep1. 
            specialize (Hc (eq_refl _)).
            destruct Hc; tryfalse.  
            simpljoin.
            unfold cmd_equiv in H6.
            destruct H6. simpljoin. tryfalse.
            simpljoin.
            inverts H3.
            lets H'_ : hapistep_not_eni_act H12 Hstep1.
            eauto.
            false. 
          --- (* sched for right system -- impossible *) 
            match goal with H: (_, (api_spec, _, _)) = (_, _) |- _ => inverts H end.
            unfold code_equiv_tskd in Hceq.
            lets H_: Hceq Hdomeq Htpi1 Htpi2.
            rewrite HC1 in H_.
            assert (t = t2) by congruence.
            subst t.
            rewrite H3 in H_.
            destruct C1 as (c1, (ke1, ks1)). 
            lets Hc: hapistep_tau_or_knl Hstep1. 
            specialize (Hc (eq_refl _)).
            destruct Hc; tryfalse.
            simpljoin.
            unfold cmd_equiv in H6.
            destruct H6. simpljoin. tryfalse.
            simpljoin.
            inverts H4.
            lets H'_ : hapistep_not_sch_act H12 Hstep1.
            eauto.
            false.

      * (* ~flowsTo (TaskDom d1) (TaskDom i) *)
        inverts Hstep2.
        2: { (* step for right system is entrance to interrupt handler --- impossible *)
          match goal with
            H: EniAct = TauAct \/ _ \/ _ |- _ =>
              destruct H as [Hf | [Hf | Hf]]; tryfalse
          end.
        }
        2: { 
          match goal with
            H: SchAct = TauAct \/ _ \/ _ |- _ =>
              destruct H as [Hf | [Hf | Hf]]; tryfalse
          end.
        }
        l_rew21_inv1 (get O2 curtid).
        match goal with
          H: get T2 t2 = Some ?C |- _ => rename C into C2
        end.
        match goal with H: nabt (set T1 t1 ?C) |- _ => rename C into C1' end.
        match goal with H: nabt (set T2 t2 ?C) |- _ => rename C into C2' end.
        lets H__: prio_unique Htpi2; eauto.
        specializes H__; eauto.
        rewrite <- H__ in *. clear H__.
        rewrite Hdomeq in *.
        assert (Hce12: ct_ex_prio_dom_eq O1 O2).
        {
          apply data_equiv_schd_impl_pdeq; auto.
          unfolds in Hsceq; unfolds in Hsceq; simpljoin; auto.
        }
        assert (Hce21: ct_ex_prio_dom_eq O2 O1).
        {
          apply ct_ex_prio_dom_eq_sym. auto.
        }
        lets Heq11': nfl_htstep_obsr_equiv_tskd Hstepdm' Hhtstep1; eauto.
        lets Heqsym: obsr_equiv_tskd_sym Htdeq; eauto. 
        { unfolds in Hsceq; unfolds in Hsceq; simpljoin; auto. }
        lets Heq21': obsr_equiv_tskd_trans_ Heqsym Heq11'; eauto.
        lets Hce11': reachable_htstep_ct_ex_prio_dom_eq 
                       Hgoodcli Hrch1 Hnint1; eauto.
        specializes Hce11'; eauto.
        assert (Hce1'2: ct_ex_prio_dom_eq O1' O2).
        {
          apply ct_ex_prio_dom_eq_sym.
          eapply ct_ex_prio_dom_eq_trans; eauto. 
        }
        
        lets Heq1'2: obsr_equiv_tskd_sym_ Heq21'; eauto. 
        { eapply ct_ex_prio_dom_eq_sym; eauto. }
        match goal with
          H: htstep _ t2 _ _ _ _ _ _ _ _ |- _ => 
            lets Heq22': nfl_htstep_obsr_equiv_tskd Hstepdm' H Hnabt2; eauto
        end.
        eapply obsr_equiv_tskd_trans_; eauto. 
        
    + (* htistep for left system *)
      (*hpstep for right system  impossible *)
      inverts H4.
      inverts Hstep2. 
      --inverts H8.
        inverts H10.
        (*hidapistep for right system impossible*)
        destruct Hact.
        tryfalse.
        destruct H10. 
        tryfalse.
        tryfalse.
      (*htistep for right system possible*)
      --inverts H9.
        unfold obsr_equiv_tskd.
        assert (t = t1) by congruence. subst.
        assert (t0 = t2) by congruence. subst.
        remember (dom_for_prio pr1) as d1.
        assert (Hflcs: flowsTo (TaskDom d1) (TaskDom i)
                       \/ ~flowsTo (TaskDom d1) (TaskDom i)) by tauto.
        destruct Hflcs as [Hstepdm | Hstepdm'].
        lets Hd'eq: Hfloweq Hstepdm.
        assert (Hd'eq_ := Hd'eq).
        unfolds in Hd'eq_.
        unfold obsr_equiv_tskd in Hd'eq_.
        destruct Hd'eq_ as (Hceq & Hdeq).
        unfold data_equiv_tskd in Hdeq.
        destruct Hdeq as (Hctide & Hbufe & Hkde & Hcde).
        assert (Hkde_ := Hkde).
        unfold kernel_data_equiv in Hkde_.
        destruct Hkde_ as (Hkte & Hkqe & Hprte & Hkprte).
        
        assert (Hctide_ := Hctide).
        destruct Hctide as (t1_ & t2_ & Ht1_ & Ht2_ & Hfa).
        assert (Ht1eq: t1_ = t1) by congruence.
        subst t1_.
        assert (Ht2eq: t2_ = t2) by congruence.
        subst t2_.
        assert (pr1 = pr2). { eapply Hfa; eauto. }
        remember pr1 as pr. subst pr1. subst pr2.
        unfold code_equiv_tskd in Hceq.
      (*        flowsTo (TaskDom d1) (TaskDom i)      *)
      *
        split.
        (*        data equiv     *)
        2:{
          unfold data_equiv_tskd.
          unfold obsr_equiv_tskd in Htdeq.
          destruct Htdeq as (Htcde & Htdae).
          unfold data_equiv_tskd in Htdae.
          eauto.
        }
        (*        code equiv     *)
        unfold code_equiv_tskd.
        introv Hd Htpi1' Htpi2'.
        
        (* inverts Hd. *)
        specialize (Hceq pr t1 t2).
        lets H__: Hceq Hdomeq Htpi1 Htpi2.
        destruct H__ as (c1 & c2 & ke_ & ks1_ &ks2_ & HC1_ & HC2_ & Hcmde & Hconte).
        rename H2 into HC1.
        rename H7 into HC2.
        rewrite HC1_ in HC1.
        rewrite HC2_ in HC2.
        inverts HC1.
        inverts HC2.
        casetac t1 t0 Heq1 Hneq1.
        2:{ 
          casetac pr pr0 He Hne.
          subst pr0.
          lets Hf: tid_unique Htpi1 Htpi1'.
          subst. tryfalse.
          casetac t2 t3 He' Hne'.
          subst t3.
          lets Hf: prio_unique Htpi2 Htpi2'.
          tryfalse.
          rewrite set_a_get_a'; eauto.
          rewrite set_a_get_a'; eauto.
          destruct Htdeq as (Hce0 & Hde0).
          unfolds in Hce0.
          gen Hce0. introv Hce0.
          lets H_: Hce0 Htpi1' Htpi2'.
          auto. eauto. 
        }
        subst t0.
        assert (t2 = t3).
        { lets H_: prio_tid_corr Htpi1 Htpi2  Htpi1' Htpi2'.
          destruct H_. simpljoin. destruct H2. tryfalse. }
        subst t3.
        rewrite set_a_get_a. rewrite set_a_get_a.
        do 5 eexists.
        split;eauto.
        split;eauto.
        split.
        (*    cmd_equiv   *)
        unfold cmd_equiv.
        unfold cmd_equiv in Hcmde.
        inverts H.
        inverts H4.
        destruct Hact.
        tryfalse.
        destruct H.
        tryfalse.
        tryfalse.
        destruct Hact.
        tryfalse.
        destruct H2.
        tryfalse.
        tryfalse.
      *  
        (*   ~ flowsTo (TaskDom d1) (TaskDom i)   *)
        destruct Hact.
        tryfalse.
        destruct H9.

        tryfalse.
        tryfalse.
    + (* sched for left system --- impossible because it is not SchedDom executing *) 
      inverts Hact as [Hf1 | Hf2]; tryfalse. 
      
  - (* sched step (as opposed to task step) by left system *) 
    eapply confidentiality_sched_proof.
    eapply Hpu. eapply Hncfid.
    eauto. eapply Hrch2. eapply Hrch1.
    eapply Hfloweq. eauto. eauto. eauto. eauto.
    eauto. eauto. eauto.
Qed.

