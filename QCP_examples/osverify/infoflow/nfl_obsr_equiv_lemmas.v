
Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs.
Require Import prt_apispecs.
Require Import intspecs.
Require Import osspecs.
Require Import properties.

Require Import data_invs.
Require Import equiv_prop.
Require Import if_assms.
Require Import if_succ_gen.
Require Import if_good_code.

Require Import sem_prop. 
Require Import sem_prop_2. 

Require Import FunctionalExtensionality.

Require Import if_common_lemmas.

Require Import integrity_proof.
Require Import integrity_lemma.
Set Keyed Unification.

Lemma estep_dom_intact:
  forall d d' c m c' m' ge le M ge' le' M' ke ke', 
    estep d c ke m c' ke' m' ->
    m = (ge, le, M) ->
    m' = (ge', le', M') ->
    d <> d' -> 
    get_dom_mem M d' = get_dom_mem M' d'. 
Proof.
  introv Hestep Hm Hm' Hdd'.
  subst.
  inverts Hestep; try auto.
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

Lemma store_intact0: 
  forall t M a0 a v M' d, 
    store t M a0 v = Some M' -> 
    addr_in_dom a0 d = true ->
    addr_in_dom a d = false ->
    get M a = get M' a. 
Proof.
  introv Hstore Hin Hnotin.
  unfolds in Hstore.
  destruct a0 as (b0, o0).
  destruct a as (b, o).
  assert (b <> b0).
  {
    casetac b b0 Ht Hf.
    subst.
    erewrite n_block_cross_part in Hin. rewrite Hnotin in Hin. tryfalse.
    auto.
  }
  symmetry.
  eapply storebytes_get_old_blk'; eauto.
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

Lemma sstep_dom_intact: 
  forall d d' pu c m c' m' ge le M ge' le' M' ks ks', 
    sstep pu d c ks m c' ks' m' ->
    m = (ge, le, M) ->
    m' = (ge', le', M') ->
    d <> d' -> 
    get_dom_mem M d' = get_dom_mem M' d'.
Proof.
  introv Hsstep Hm Hm' Hindom.
  subst.
  inverts Hsstep; auto; 
    (repeat match goal with H: (_, _, _) = (_, _, _) |- _ => inverts H end);
    auto. 
  - unfolds.
    apply functional_extensionality.
    intro a'.
    destruct (addr_in_dom a' d') eqn: E.
    + 
      destruct (addr_in_dom a' d) eqn: E'.
      lets Hf: dom_disj_addrs E' E. auto. tryfalse.    
      eapply store_intact0; eauto.
      unfolds in H1.
      destruct a. simpl.
      destruct i. simpl in H1. simpl. auto.
    +
      auto. 
  -
    lets H_: get_dom_mem_alloc_eq H1 Hindom.
    rewrite H_.
    unfold alloc_pt in H1.
    simpljoin.
    rewrite set_a_get_a in H2.
    inverts H2.
    remember (allocb M0 b 0 (typelen t)) as M_.
    unfolds. 
    apply functional_extensionality.
    intro a'.
    destruct (addr_in_dom a' d') eqn: E.
    + 
      destruct (addr_in_dom a' d) eqn: E'.
      lets Hf: dom_disj_addrs E' E. auto. tryfalse.    
      eapply store_intact0; eauto.
    +
      auto. 
  -
    lets H_: get_dom_mem_alloc_eq H1 Hindom.
    auto.
  -
    eapply get_dom_mem_freeb_eq; eauto.
Qed. 

Lemma cstep_dom_intact:
  forall d d' p C m C' m' ge le M ge' le' M', 
    cstep p d C m C' m' ->
    m = (ge, le, M) ->
    m' = (ge', le', M') ->
    d <> d' -> 
    get_dom_mem M d' = get_dom_mem M' d'.
Proof.
  introv Hcstep Hm Hm' Hnin.
  subst.
  inverts Hcstep.
  - eapply estep_dom_intact; eauto.
  - eapply sstep_dom_intact; eauto.
Qed.     

Lemma GoodStmt_noabs: 
  forall s, GoodStmt_h s -> stmt_noabs s.
Proof.
  inductions s; 
    introv HGS;
    try (simpl; auto).
  - 
    simpl in HGS.
    simpljoin.
    split; eauto.
  -
    simpl in HGS.
    simpljoin.
    split; eauto.
Qed. 

Lemma good_client_code_impl_noabs:
  forall cliprogs, 
    good_client_code cliprogs ->
    pu_noabs cliprogs.
Proof.
  introv Hgcc.
  unfolds in Hgcc.
  unfolds.
  introv Hcf.
  lets H__: Hgcc Hcf.
  apply GoodStmt_noabs; auto. 
Qed. 

Lemma abst_eq_code_equiv_tskd_preserve:
  forall O pr t d d0 T C', 
    task_prio_id O pr t ->
    dom_for_prio pr = d ->
    ~flowsTo (TaskDom d) (TaskDom d0) ->
    code_equiv_tskd' d0 T (set T t C') O O. 
Proof.
  introv Htpi Hd Hnfl.
  unfolds.
  introv Hd0 Htpi1 Htpi2.
  assert (t1 = t2).
  { eapply tid_unique; eauto. }
  subst.
  casetac t t2 He Hne.
  -
    subst.
    assert (pr = pr0).
    { eapply prio_unique; eauto. }
    subst.
    false. apply Hnfl. apply flows_to_refl.
  -
    rewrite set_a_get_a'; eauto.
    split; auto.
    introv Hget.
    assert (Hor: not_knl_stmt c \/ ~not_knl_stmt c) by tauto.
    split.
    +
      destruct Hor as [Hnknl | Hknl].
      *
        left; auto.
      *
        right.
        lets H_: knl_hapicode Hknl.
        destruct H_ as (ss & Hc).
        exists ss. split; auto.
        split; intros; auto.
    +
      intros.
      split; auto. 
Qed.

Definition cstep_code_equiv_tskd_preserve := abst_eq_code_equiv_tskd_preserve.

Lemma client_data_equiv_local_upd_preserve:           
  forall O pr t d d0 ges cenvs le' M M', 
    task_prio_id O pr t -> 
    dom_for_prio pr = d -> 
    ~flowsTo (TaskDom d) (TaskDom d0) -> 
    get_dom_mem M d0 = get_dom_mem M' d0 ->           
    client_data_equiv d0 (ges, cenvs, M) (ges, set cenvs t le', M') O O. 
Proof.
  introv Htpi Hd Hfl Hgd.
  unfold client_data_equiv.
  do 6 eexists. 
  splits; eauto.
  unfold local_envs_equiv.
  introv Hd' Htpi1 Htpi2.
  assert (t1 = t2).
  { eapply tid_unique; eauto. }
  subst.
  casetac t t2 He Hne.
  - subst.
    assert (pr = pr0).
    { eapply prio_unique; eauto. }
    subst.
    false. apply Hfl. apply flows_to_refl.
  - rewrite set_a_get_a'; eauto. 
Qed.     

Lemma cstep_data_equiv_tskd_presesrve:
  forall td' td pr' O T t C C' le le' M M' ges cenvs pc, 
    ~ flowsTo (TaskDom td') (TaskDom td) ->
    reachable (pc, (api_spec, int_spec, get_hprio_d)) T (ges, cenvs, M) O -> 
    cstep pc td' C (ges td', le, M) C' (ges td', le', M') ->
    get O curtid = Some (oscurt t) ->
    get T t = Some C ->
    get cenvs t = Some le ->
    task_prio_id O pr' t ->
    dom_for_prio pr' = td' ->
    data_equiv_tskd td (ges, cenvs, M) (ges, set cenvs t le', M') O O. 
Proof.
  introv Hnfl Hrch Hcs Hct Hgc Hgle Htpi Hd.
  unfold data_equiv_tskd.
  splits.
  -
    eapply ctid_equiv_refl; eauto.
  - 
    apply reachable_get_bufsid in Hrch.
    destruct Hrch as (x & y & Hgetx & Hgety).
    eapply bufs_equiv_refl; eauto.
  -
    apply reachable_get_knldataid in Hrch.
    simpljoin.
    eapply kernel_data_equiv_refl; eauto.
  -              
    eapply client_data_equiv_local_upd_preserve; eauto.
    eapply cstep_dom_intact; eauto. 
    introv Hf. subst td.
    false. apply Hnfl. apply flows_to_refl.
Qed. 

Lemma  local_envs_equiv_same_preserve:
  forall i ces O, local_envs_equiv i ces ces O O.
Proof.
  unfold local_envs_equiv.
  intros.
  lets Heq: tid_unique H0 H1.
  subst.
  auto.
Qed.

Lemma  client_data_equiv_same_preserve:
  forall i cst O, client_data_equiv i cst cst O O.
Proof.
  unfold client_data_equiv.
  intros.
  destruct cst as ((ges & ces) & m).
  repeat eexists; eauto.
  eapply local_envs_equiv_same_preserve.
Qed.

Lemma data_equiv_tskd_same_preserve:
  forall i cst O t hp T,
    reachable hp T cst O ->
    get O curtid = Some (oscurt t) ->
    data_equiv_tskd i cst cst O O.
Proof.
  unfold data_equiv_tskd.
  introv Hrch Hget.
  split. eapply ctid_equiv_refl; eauto.
  split. apply reachable_get_bufsid in Hrch.
  destruct Hrch as (x & y & Hgetx & Hgety).
  eapply bufs_equiv_refl; eauto.
  split. apply reachable_get_knldataid in Hrch.
  simpljoin. eapply kernel_data_equiv_refl; eauto.
  eapply client_data_equiv_same_preserve.
Qed.

Lemma nintr_absintcont_none: 
  forall O T t cd ke ks, 
    get O curtid = Some (oscurt t) ->
    get T t = Some (curs (hapi_code cd), (ke, ks)) ->
    ~ in_intr T O ->
    absintcont ks = None.
Proof.
  introv Hgct Hgt Hnintr.
  unfolds in Hnintr.
  unfold in_intr in Hnintr.
  destruct (absintcont ks) eqn: E.
  - false.
    eapply Hnintr.
    unfold code_cur_task.
    rewrite Hgct.
    rewrite Hgt.
    do 3 eexists.
    split; eauto.
    rewrite E.
    introv Hf; false.
  - auto.
Qed. 



Lemma nfl_htstep_obsr_equiv_tskd:
  forall d i pu T cst O t pr cst' O' act C C',
    good_client_code pu -> 
    ~ flowsTo (TaskDom d) (TaskDom i) -> 
    reachable (pu, (api_spec, int_spec, get_hprio_d)) T cst O ->
    get O curtid = Some (oscurt t) ->
    task_prio_id O pr t ->
    dom_for_prio pr = d -> 
    get T t = Some C -> 
    ~ in_intr T O -> 
    htstep (pu, (api_spec, int_spec, get_hprio_d)) t d C cst O C' cst' O' act -> 
    nabt (set T t C') -> 
    obsr_equiv_tskd' get_hprio_d i T (set T t C') cst cst' O O'.  
Proof.
  introv Hgoodcli (* Hpu *) Hnfl Hrc Hgc Htpi Hd. 
  introv HC Hni Hsp Hnabt.
  lets Hpu: good_client_code_impl_noabs Hgoodcli. 
  inverts Hsp; 
    try match goal with H: (_, _) = _ |- _ => inverts H end.
  - (* cstep *)
    unfolds.
    split.
    + (* code_equiv *)
      lets H__: cstep_code_equiv_tskd_preserve Hnfl; eauto.
    + (* data_equiv *)
      lets H__: cstep_data_equiv_tskd_presesrve Hnfl Hrc; eauto.
  - (* hapistep *)
    match goal with H: context [hapistep] |- _ => inverts H end.
    + (* hapienter_step *)
      match goal with H: (_, _, _) = _ |- _ => inverts H end.
      unfolds.
      split.
      * lets H__: abst_eq_code_equiv_tskd_preserve Hnfl; eauto. 
      * eapply data_equiv_tskd_same_preserve; eauto.  
    +(* hidapistep *)
      casetac O O' Hoeq Hone.
      * subst.
        split.
        ** eapply abst_eq_code_equiv_tskd_preserve; eauto.
        ** eapply data_equiv_tskd_same_preserve; eauto.
      *  
        assert (Hna: cd' <> ABORT).
        {
          unfolds in Hnabt.
          specialize (Hnabt t).
          rewrite set_a_get_a in Hnabt.
          specializes Hnabt; eauto.
          introv Hf. apply Hnabt. congruence.
        }
        lets H__: reachable_ks_noint_apicode Hpu Hrc.
        lets H_: H__ HC; eauto. 
        lets Hnintr: nintr_absintcont_none Hgc HC; eauto.
        specializes Hnintr; eauto.
        simpl in H_.
        destruct H_ as (Hnaapi & _).
        unfolds in Hnaapi.
        specializes Hnaapi; eauto. 
        destruct Hnaapi as [Hcd | [Hat | Hend]].
        ** 
          assert (Hdiffd: i <> dom_for_prio pr).
          {
            introv Hdeq.
            apply Hnfl.
            subst i.
            subst d.
            apply flows_to_refl.
          }
          lets Hgtc: reachable_good_tasks Hgoodcli Hrc; eauto.    
          simpljoin. 
          split.
          ***
            lets H_: api_spec_step_code_equiv_tskd'_preserve Hgtc Htpi Hgc HC; eauto.
          ***
            lets H_: api_spec_step_data_equiv_tskd_preserve Hgtc Hrc; eauto.
        **
          subst cd.
          match goal with H: context [spec_step] |- _ => inverts H end.
        **
          simpljoin.
          match goal with H: context [spec_step] |- _ => inverts H end.
    + (* hapiexit_step *)
      split.
      * lets H__: abst_eq_code_equiv_tskd_preserve Hnfl; eauto. 
      * eapply data_equiv_tskd_same_preserve; eauto.  
    + (* hintexit_step *)
      split.
      * lets H__: abst_eq_code_equiv_tskd_preserve Hnfl; eauto. 
      * eapply data_equiv_tskd_same_preserve; eauto.  
Qed.

