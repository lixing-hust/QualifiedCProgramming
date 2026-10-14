Require Import ucos_include.
Require Import Lia.
Require Import aux_pureLib.
Require Import gjb_common.

Lemma if_zero_rule: forall Spec sd I r ri p e s1 s2 q pa t,
  (p ==> Rv e @ Tint32 ==  Vint32 Int.zero) ->
  InfRules Spec sd pa I r ri p s2 q t ->
  InfRules Spec sd pa I r ri p (sif e s1 s2) q t.
Proof.
  intros.
  eapply if_rule; eauto.
  eexists. eauto.
  eapply backward_rule1.
  apply sep_aconj_r_aistrue_to_astar with (t:=Tint32). eauto.
  apply pure_split_rule. intros. destruct H1. congruence.
  eapply backward_rule1.
  apply sep_aconj_r_aisfalse_to_astar with (t:=Tint32). eauto.
  apply pure_split_rule. intros. auto.
Qed.

Lemma if_one_rule: forall Spec sd I r ri p e s1 s2 q pa t,
  (p ==> Rv e @ Tint32 == Vint32 Int.one) ->
  InfRules Spec sd pa I r ri p s1 q t ->
  InfRules Spec sd pa I r ri p (sif e s1 s2) q t.
Proof.
  intros. 
  eapply if_rule; eauto.
  + intros. apply H in H1. sep auto.
  + eapply backward_rule1.
    apply sep_aconj_r_aistrue_to_astar with (t:=Tint32).
    intros. apply H in H1. sep destruct H1. sep split in H1. eauto.
    apply pure_split_rule. intros. auto. 
  + eapply backward_rule1.
    apply sep_aconj_r_aisfalse_to_astar with (t:=Tint32). eauto.
    apply pure_split_rule. intros. auto. destruct H1. inversion H1. discriminate.
Qed.

Lemma nth_val_update_nth_val_diff:
  forall n m v vl,
    m <> n ->
    nth_val n (update_nth_val m vl v) = nth_val n vl.
Proof.
  induction n; destruct m; destruct vl; simpl; intros; tryfalse; auto.
Qed.

Lemma pptr_in_dportls1:
  forall otherppl otherpl othermsgll dportls1 dportls2 dportls pptr p0 p1 d p2 p3 p4 p5,
    RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 ->
    join dportls1 dportls2 dportls ->
    get dportls pptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) ->
    get dportls1 pptr = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5).
Proof.
  induction otherppl; destruct otherpl; destruct othermsgll; simpl; intros; tryfalse.
  { subst dportls2; apply map_join_emp' in H0; subst dportls1; auto. }
  simpljoin1.
  assert (a = pptr \/ a <> pptr) by tauto.
  destruct H4; subst.
  {
    apply join_sig_get in H; auto.
    unfold OtherPortNode_P in H2; destruct H2 as [? [? ?]].
    destruct x as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
    unfold OtherPort_nat_P in H2; simpljoin1.
    assert (get dportls pptr =
    Some (∘ (Int.unsigned x), ∘ (Int.unsigned x1),
      ∘ (Int.unsigned x2), d0, ∘ (Int.unsigned x3),
      ∘ (Int.unsigned x4), ∘ (Int.unsigned x5), p11)).
    { eapply join_get_r; eauto. }
    unfold port_domain, port_id, port_status, port_intick, port_outick in H1.
    rewrite H6 in H1; inverts H1.
    exfalso; clear - H7 H11.
    unfold nat_of_Z in H11.
    apply Z2Nat.inj in H11; [lia| apply Int.unsigned_range| apply dnum_range].
  }
  assert (join dportls1 x0 (merge dportls1 x0)).
  {
    apply join_sem; auto.
    apply join_disjoint_eq_merge in H; simpljoin1.
    eapply disjoint_merge_disjoint.
    2: eapply disj_sym; eauto.
    apply disjoint_merge_sym in H.
    rewrite <- H; eauto.
  }
  assert (get (merge dportls1 x0) pptr = Some
    (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5)).
  {
    pose proof join_disjoint_eq_merge H; simpljoin1.
    pose proof join_disjoint_eq_merge H0; simpljoin1.
    apply disj_sym in H6.
    pose proof disjoint_merge_sym H6.
    rewrite <- H8 in H0, H1.
    pose proof join_merge_disjoint H0 H6.
    rewrite <- H1.
    assert (get (merge dportls1 (merge x0 (sig a x))) pptr = get (merge dportls1 x0) pptr); auto.
    eapply map_join_get_none.
    2:{
      instantiate (1:=(sig a x)).
      apply get_a_sig_a'; auto.
    }
    apply join_comm; auto.
  }
  lets IH: IHotherppl H3 H5 H6; auto.
Qed.

Lemma RLH_Domainportl_abs_getsome : forall (p_v: addrval) dportlptr dportl dportmsgll dportls dpptrl port,
    RL_PortPtrList dportlptr dportl dpptrl ->
    RLH_Domainportl dportlptr dportl dportmsgll dportls ->
    get dportls p_v = Some port ->
    exists n dport msgl,
    nth_error dportl n = Some dport /\
    nth_error dportmsgll n = Some msgl /\ 
    nth_error dpptrl n = Some p_v /\
    DomainportNode_P dport port msgl.
Proof.
  intros ? ? ?.
  revert p_v dportlptr.
  induction dportl;intros.
  - simpl in H. 
    destruct dportmsgll;tryfalse.
    inverts H0.
    rewrite map_emp_get in H1.
    inverts H1.
  - intros.
    simpl in H, H0.
    destruct dportmsgll, dpptrl;tryfalse.
    simpljoin1.
    destruct (addrval_eq_dec x p_v).
    + subst.
      exists 0%nat a l.
      cbn;splits;auto.
      inverts H0. auto.
      assert (get dportls p_v = Some x0).
      { eapply join_sig_get;eauto. }
      rewrite H in H1. inverts H1.
      auto.
    + assert (get x1 p_v = Some port).
      { eapply perm_map_lemmas_part4.join_sig_get_r;eauto. }
      inverts H0.
      clear H1.
      rewrite H4 in H6. inverts H6.
      lets IH: IHdportl H7 H5 H.
      simpljoin1.
      exists (S x2).
      do 2 eexists.
      cbn. splits;eauto.
Qed.

Fixpoint RL_ECBPtrList (v tl: val) (ectrls:list EventCtr) (eptrls: list addrval) : Prop :=
  match ectrls, eptrls with
  | nil, nil =>  v = tl
  | ectr :: ectrls', eptr :: eptrls' =>  
      v = Vptr eptr /\
      match ectr with
        | (osevent, etbl, petbl) =>
          exists  v', 
            V_OSEventListPtr osevent = Some v' /\
            RL_ECBPtrList v' tl ectrls' eptrls' 
      end
  | _, _ => False
  end.

Lemma ECBList_P_abs_getPtrList :
  forall headptr tailptr ectrls edatals ecbls tcbls,
    ECBList_P headptr tailptr ectrls edatals ecbls tcbls ->
    exists (eptrls: list addrval),
      RL_ECBPtrList headptr tailptr ectrls eptrls.
Proof.
  intros ? ? ?.
  revert headptr tailptr.
  induction ectrls; intros.
  {
    simpl in H; destruct H as [? [? ?]]; subst.
    simpl; exists (@nil addrval); auto.
  }
  simpl in H.
  destruct H as [? [? [? [? ?]]]].
  destruct edatals; tryfalse.
  destruct a, p; simpljoin1.
  lets IH: IHectrls H5.
  destruct IH as [eptrls ?].
  exists (x :: eptrls).
  simpl; split; eauto.
Qed.

Lemma ECBList_P_abs_getsome :
  forall headptr tailptr ectrls edatals ecbls tcbls pptr absport wt eptrls,
    ECBList_P headptr tailptr ectrls edatals ecbls tcbls ->
    RL_ECBPtrList headptr tailptr ectrls eptrls ->
    get ecbls pptr = Some (absport, wt) -> 
    exists n ectr edata,
      nth_error ectrls n = Some ectr /\
      nth_error edatals n = Some edata /\
      nth_error eptrls n = Some pptr /\
      RLH_ECBData_P edata (absport, wt).
Proof.
  intros ? ? ?.
  revert headptr tailptr.
  induction ectrls; intros.
  {
    simpl in H; destruct H as [? [? ?]]; subst.
    rewrite map_emp_get in H1.
    inverts H1.
  }
  {
    simpl in H, H0.
    destruct H as [qid [? [? [? ?]]]].
    destruct edatals; tryfalse.
    destruct eptrls; tryfalse.
    destruct a, p.
    simpljoin1.
    inversion H0; subst; clear H0.
    destruct (addrval_eq_dec a0 pptr).
    {
      subst.
      exists 0%nat (v0, v1, v) e.
      splits; auto.
      assert (get ecbls pptr = Some x).
      { eapply join_sig_get; eauto. }
      unfold absecb.B in H.
      rewrite H1 in H.
      inverts H; auto.
    }
    {
      assert (get x0 pptr = Some (absport, wt)).
      { eapply perm_map_lemmas_part4.join_sig_get_r; eauto. }
      clear H1.
      rewrite H4 in H5.
      inversion H5; subst; clear H5.
      lets IH: IHectrls H9 H6 H.
      simpljoin1.
      exists (S x1).
      do 2 eexists.
      cbn; splits; eauto.
    }
  }
Qed.

Lemma RL_PortAttr_dir_SOURCE : forall dpptrl dportl n p_v dport pcn pd pid pst pintick poutick pt msgl,
  RL_PortAttr dpptrl dportl ->
  nth_error dpptrl n = Some p_v ->
  nth_error dportl n = Some dport ->
  DomainportNode_P dport (pcn, pd, pid, SourceP, pst, pintick, poutick, pt) msgl -> 
  OSPortAttrTblDir p_v = (V$ SOURCE).
Proof.
  intros.
  assert (Some (OSPortAttrTblDir p_v) = Some (V$ SOURCE)).
  { destruct H.
  apply map_nth_error with (f:= OSPortAttrTblDir) in H0.
  rewrite <- H0, <- H.
  rewrite list_map_nth.
  rewrite H1.
  simpl.
  destruct H2 as (_ & ? & _ ).
  unfold Domainport_direction_P in H2.
  unfold OS_Port_V_direction, OS_Port_V_direction' in *.
  erewrite nth_val_nth_val'_some_eq;eauto. }
  congruence.
Qed.

Lemma RL_PortAttr_dir_DES : forall dpptrl dportl n p_v dport pcn pd pid pst pintick poutick pt msgl nextdst,
  RL_PortAttr dpptrl dportl ->
  nth_error dpptrl n = Some p_v ->
  nth_error dportl n = Some dport ->
  DomainportNode_P dport (pcn, pd, pid, DestinationP nextdst, pst, pintick, poutick, pt) msgl -> 
  OSPortAttrTblDir p_v = (V$ DESTINATION).
Proof.
  intros.
  assert (Some (OSPortAttrTblDir p_v) = Some (V$ DESTINATION)).
  { destruct H.
  apply map_nth_error with (f:= OSPortAttrTblDir) in H0.
  rewrite <- H0, <- H.
  rewrite list_map_nth.
  rewrite H1.
  simpl.
  destruct H2 as (_ & ? & _ ).
  unfold Domainport_direction_P in H2.
  unfold OS_Port_V_direction, OS_Port_V_direction' in *.
  erewrite nth_val_nth_val'_some_eq;tauto. }
  congruence.
Qed.

Lemma RL_PortAttr_mode_SAMPLE : forall dpptrl dportl n p_v dport pcn pd pid pdir pst pintick poutick pt msgl,
  RL_PortAttr dpptrl dportl ->
  nth_error dpptrl n = Some p_v ->
  nth_error dportl n = Some dport ->
  DomainportNode_P dport (pcn, pd, pid, pdir, pst, pintick, poutick, SamplePort pt) msgl -> 
  OSPortAttrTblMode p_v = (V$ SAMPLE).
Proof.
  intros.
  assert (Some (OSPortAttrTblMode p_v) = Some (V$ SAMPLE)).
  { destruct H.
  apply map_nth_error with (f:= OSPortAttrTblMode) in H0.
  rewrite <- H0, <- H3.
  rewrite list_map_nth.
  rewrite H1.
  simpl.
  destruct H2 as (_ & _ & ? ).
  unfold Domainport_Portt_P in H2.
  destruct H2 as (? & ? & ? & ?).
  unfold OS_Port_V_mode, OS_Port_V_mode' in *.
  erewrite nth_val_nth_val'_some_eq;eauto. }
  congruence.
Qed.

Lemma RL_PortAttr_mode_QUEUE : forall dpptrl dportl n p_v dport pcn pd pid pdir pst pintick poutick sz pl msgl,
  RL_PortAttr dpptrl dportl ->
  nth_error dpptrl n = Some p_v ->
  nth_error dportl n = Some dport ->
  DomainportNode_P dport (pcn, pd, pid, pdir, pst, pintick, poutick, QueuePort sz pl) msgl -> 
  OSPortAttrTblMode p_v = (V$ QUEUE).
Proof.
  intros.
  assert (Some (OSPortAttrTblMode p_v) = Some (V$ QUEUE)).
  { destruct H.
  apply map_nth_error with (f:= OSPortAttrTblMode) in H0.
  rewrite <- H0, <- H3.
  rewrite list_map_nth.
  rewrite H1.
  simpl.
  destruct H2 as (_ & _ & ? ).
  unfold Domainport_Portt_P in H2.
  destruct H2 as (? & ? & ?).
  unfold OS_Port_V_mode, OS_Port_V_mode' in *.
  erewrite nth_val_nth_val'_some_eq;eauto. }
  congruence.
Qed.

Lemma R_Kernelport_DomainPort_abs_getsome:
  forall kportvl kportl dportl1 dport dportl2 dpptrl pptr,
    R_Kernelport_DomainPort kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl ->
    nth_error dpptrl (length dportl1) = Some pptr ->
    exists id kportptr kport,
        OS_Port_V_portID dport = Some (Vint32 id) /\
        nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vptr kportptr) /\ 
        nth_error kportl (nat_of_Z (Int.unsigned id)) = Some kport /\
        struct_type_vallist_match OS_K_Port kport /\
        OS_K_Port_V_portID kport = Some (Vint32 id) /\
        OS_K_Port_V_dmport kport = Some (Vptr pptr) /\
        OS_K_Port_V_coreNum kport = OS_Port_V_coreNum dport.
Proof.
  intros ? ? ?; revert kportvl kportl; induction dportl1; intros.
  {
    destruct dpptrl; tryfalse.
    simpl in H0. inverts H0.
    simpl in H; simpljoin1; simpl.
    do 3 eexists; do 2 (split; eauto). 
  }
  destruct dpptrl; tryfalse.
  cbn in H; simpljoin1.
  eapply IHdportl1; eauto.
Qed.


Lemma RLH_Kernelport_abs_getsome :
  forall kportvl1 kpptr kportvl2 kportl1 kport kportl2 kportls,
    RLH_Kernelport (kportvl1 ++ (Vptr kpptr) :: kportvl2) (kportl1 ++ kport :: kportl2) kportls ->
    length kportvl1 = length kportl1 ->
    (forall (id1 id2 : nat) (p1 p2 : addrval),
      id1 <> id2 ->
      nth_val id1 (kportvl1 ++ (Vptr kpptr) :: kportvl2) = Some (Vptr p1) ->
      nth_val id2 (kportvl1 ++ (Vptr kpptr) :: kportvl2) = Some (Vptr p2) -> p1 <> p2) ->
    exists kporth,
      KernelportNode_P kport kporth /\ get kportls kpptr = Some kporth.
Proof.
  intro; induction kportvl1; intros.
  {
    destruct kportl1; tryfalse.
    simpl in H.
    destruct H; simpljoin1; tryfalse.
    inverts H; exists x0.
    split; auto.
    eapply join_sig_get; eauto.
  }
  destruct kportl1; tryfalse.
  simpl in H0; simpl in H; destruct H; simpljoin1.
  { eapply IHkportvl1; eauto. }
  apply Nat.succ_inj in H0.
  assert ( (forall (id1 id2 : nat) (p1 p2 : addrval),
    id1 <> id2 ->
    nth_val id1 (kportvl1 ++ Vptr kpptr :: kportvl2) = Some (Vptr p1) ->
    nth_val id2 (kportvl1 ++ Vptr kpptr :: kportvl2) = Some (Vptr p2) -> p1 <> p2)).
  intros; eapply H1 with (id1:=S id1)(id2:=S id2); auto.
  lets IH: IHkportvl1 H4 H0 H; simpljoin1; clear H.
  exists x2; split; eauto.
  specialize (H1 0%nat (S (length (kportvl1)))); simpl in H1.
  assert (x <> kpptr).
  { apply H1; auto. apply nth_val_middle. }
  eapply map_tactics.join_merge in H2; subst.
  eapply merge_sem_none1; auto.
  eapply get_a_sig_a'; auto.
Qed.

Lemma RLH_Kernelport_abs_getsome':
  forall kportvl kportl kportls kportp pid dmportp chanp pcn kpst,
    get kportls kportp =
      Some (pid, Some dmportp, Some chanp, pcn, kpst) ->
    RLH_Kernelport kportvl kportl kportls ->
    exists n kport,
      nth_error kportvl n = Some (Vptr kportp) /\
      nth_error kportl n = Some kport /\
      KernelportNode_P kport (pid, Some dmportp, Some chanp, pcn, kpst).
Proof.
  intro; induction kportvl; simpl; intros;
  destruct kportl; subst; tryfalse.
  destruct H0; simpljoin1.
  {
    lets IH: IHkportvl H H2.
    simpljoin1.
    exists (S x) x0.
    simpl; splits; auto.
  }
  assert (x = kportp \/ x <> kportp) by tauto.
  destruct H0; subst.
  {
    exists 0%nat v.
    simpl; splits; auto.
    apply join_sig_get in H1; auto.
    unfold KPort in H1.
    rewrite H in H1.
    inverts H1; auto.
  }
  assert (get x1 kportp = Some (pid, Some dmportp, Some chanp, pcn, kpst)).
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
  lets IH: IHkportvl H4 H3.
  simpljoin1.
  exists (S x2) x3.
  simpl; splits; auto.
Qed.

Lemma R_KernelPortIDTbl_ChannelIDTbl_abs_getsome:
  forall  kportvl1 kpptr kportvl2 kportl1 kport kportl2
          chanvl chanl chandstportll chanptr kportls dportls1 dportls2,
    length kportvl1 = length kportl1 ->
    OS_K_Port_V_channel kport = Some (Vptr chanptr) ->
    R_KernelPortIDTbl_ChannelIDTbl (kportvl1 ++ Vptr kpptr :: kportvl2)
      (kportl1 ++ kport :: kportl2) chanvl chanl chandstportll kportls dportls1 dportls2 ->
    R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr kpptr kport chanvl chanl chandstportll kportls dportls1 dportls2.
Proof.
  intro; induction kportvl1; intros; destruct kportl1; tryfalse.
  {
    do 2 rewrite app_nil_l in H1.
    cbn [R_KernelPortIDTbl_ChannelIDTbl] in H1.
    destruct H1; destruct H1.
    destruct H1; tryfalse.
    destruct H1 as [? [? [? ?]]]; inverts H1.
    destruct H4.
    destruct H1; rewrite H0 in H4; inverts H4.
    auto.
  }
  do 2 rewrite <- app_comm_cons in H1.
  cbn [R_KernelPortIDTbl_ChannelIDTbl] in H1.
  destruct H1.
  simpl in H; apply Nat.succ_inj in H.
  eapply IHkportvl1; eauto.
Qed.


Lemma RLH_Channel_app_cons : forall oppl n chanvl1 chanvl2 chanptr chanl1 chanl2 chan  chandstportll1 
chandstportll2 dstportl chanls kportls dportls1 dportls2,
  length chanvl1 = n ->
  length chanl1 = n -> 
  length chandstportll1 = n ->
  (forall (id1 id2 : nat) (p1 p2 : addrval),
  id1 <> id2 ->
  nth_val id1 (chanvl1 ++ Vptr chanptr :: chanvl2) = Some (Vptr p1) ->
  nth_val id2 (chanvl1 ++ Vptr chanptr :: chanvl2) = Some (Vptr p2) -> p1 <> p2) ->
  RLH_Channel oppl (chanvl1 ++ Vptr chanptr :: chanvl2)  (chanl1 ++ chan :: chanl2) 
              (chandstportll1 ++ dstportl :: chandstportll2) chanls kportls dportls1 dportls2 ->
  exists channel,
    ChannelNode_P oppl chan channel chanptr dstportl kportls dportls1 dportls2 /\ 
    get chanls chanptr = Some channel.
Proof.
  induction n;intros;simpl.
  - destruct chanvl1, chanl1, chandstportll1;tryfalse.
    simpl in H3.
    destruct H3 as [[? ?] | ];[ tryfalse | ].
    simpljoin1.
    inverts H3.
    exists x0.
    split;auto.
    eapply join_sig_get;eauto.
  - destruct chanvl1, chanl1, chandstportll1;tryfalse.
    simpl ((_ :: _) ++ _ ) in *.
    cbn [length RLH_Channel] in *.
    destruct H3.
    + simpljoin1.
      eapply IHn. 5: exact H6.
      1,2,3: lia.
      intros.
      eapply H2 with (id1 := S id1) (id2 := S id2);eauto.
    + simpljoin1.
      assert (x <> chanptr).
      { eapply H2 with (id1 := 0%nat) (id2 := S (length chanvl1));eauto.
        simpl.
        eapply nth_val_middle.  }
      assert (exists channel,
      ChannelNode_P oppl chan channel chanptr dstportl kportls dportls1 dportls2 /\
      get x1 chanptr = Some channel).
      { eapply IHn;eauto. }
      simpljoin1.
      exists x2.
      split;eauto.
      eapply join_get_get_r;eauto.
Qed.

Lemma RLH_OtherPortPtrList_abs_getsome:
  forall otherppl otherpl othermsgll dportls2 p port,
    RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 ->
    get dportls2 p = Some port ->
    exists n dport msgl,
    nth_error otherpl n = Some dport /\
    nth_error othermsgll n = Some msgl /\ 
    nth_error otherppl n = Some p /\
    OtherPortNode_P dport port msgl.
Proof.
  induction otherppl; destruct otherpl; destruct othermsgll;
  simpl; intros; tryfalse.
  - subst.
    rewrite map_emp_get in H0.
    inverts H0.
  - simpljoin1.
    destruct (addrval_eq_dec a p).
    + subst.
      exists 0%nat v l.
      cbn;splits;auto.
      assert (get dportls2 p = Some x).
      { eapply join_sig_get;eauto. }
      rewrite H0 in H3. inverts H3.
      auto.
    + assert (get x0 p = Some port).
      { eapply perm_map_lemmas_part4.join_sig_get_r;eauto. }
      clear H0.
      lets IH: IHotherppl H2 H3.
      simpljoin1.
      exists (S x1).
      do 2 eexists.
      cbn. splits;eauto.
Qed.

Lemma dstkportpl_get_and_upd_list_Sample_Outcore:
  forall dstkportpl chanptr otherppl kportls dportls2 otherpl othermsgll pin tm msg,
  Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportpl kportls dportls2 ->
  RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 ->
  (Forall (struct_type_vallist_match' OS_Port_Seg_dls) otherpl) ->
  (exists dstportpl dstpptrnl dstportupdl dstportupdhl,
    length dstportpl = length dstkportpl /\
    length dstpptrnl = length dstkportpl /\
    length dstportupdl = length dstkportpl /\
    length dstportupdhl = length dstkportpl /\
    forall n, (n < length dstkportpl)%nat ->
      exists dstkportp dstportp dstpptrn dstpid dstkpst
          dstpd dstpst dstpin dstpout dstpm,
      exists dstpcn dstportupd dstport dstportupdh nextdst,
        nth_error dstkportpl n = Some dstkportp /\
        nth_error dstportpl n = Some dstportp /\
        nth_error dstportupdl n = Some dstportupd /\
        nth_error dstportupdhl n = Some dstportupdh /\
        nth_error dstpptrnl n = Some dstpptrn /\
        nth_error otherppl dstpptrn = Some dstportp /\
        nth_error otherpl dstpptrn = Some dstport /\
        get kportls dstkportp =
          Some (dstpid, Some dstportp, Some chanptr, dstpcn, dstkpst) /\
        get dportls2 dstportp = 
          Some (dstpcn, dstpd, dstpid,
            DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
        struct_type_vallist_match' OS_Port_Seg_dls dstportupd /\
        OS_Port_V_msgInTick dstportupd = Some (Vint32 pin) /\
        OS_Port_V_msgOutTick dstportupd = Some (Vint32 tm) /\
        (forall (m:nat), (m < 18)%nat -> (m <> 8)%nat -> (m <> 9)%nat -> 
          nth_val m dstportupd = nth_val m dstport) /\
        dstportupdh = (dstpcn, dstpd, dstpid,
          DestinationP nextdst, dstpst, Z.to_nat (Int.unsigned pin),
          Z.to_nat (Int.unsigned tm), SamplePort msg)).
Proof.
  induction dstkportpl; simpl; intros; simpljoin1.
  {
    exists (@nil addrval) (@nil nat) (@nil vallist) (@nil absdomainport.B).
    splits; eauto. lia.
  }
  lets IH: IHdstkportpl H2 H0 H1. simpljoin1.
  instantiate (1:=msg) in H10.
  instantiate (1:=tm) in H10.
  instantiate (1:=pin) in H10.
  pose proof RLH_OtherPortPtrList_abs_getsome _ _ _ _ _ _ H0 H3.
  simpljoin1.

  exists (x0::x9) (x13::x10)
          ((update_nth_val 9 (update_nth_val 8 x14 (Vint32 pin)) (Vint32 tm)) :: x11)
          ((x1, x3, x, DestinationP x8, x4, Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm), SamplePort msg) :: x12); simpl.
  splits; try lia.
  destruct n.
  2: intros; apply H10; lia.
  simpl; intros.
  do 15 eexists; splits; eauto.
  eapply Forall_forall in H1.
  instantiate (1:=x14) in H1.
  2: eapply nth_error_In; eapply H11.
  splits; eauto.
  {
    clear - H1.
    unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
    destruct x14; tryfalse.
    do 18 (destruct H1 as [? H1]; destruct x14; tryfalse).
    simpl; pauto.
  }
  {
    unfold OS_Port_V_msgInTick.
    erewrite nth_upd_neqrev; eauto.
    erewrite update_nth; eauto.
    rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; eauto.
    clear - H1.
    unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
    destruct x14; tryfalse.
    do 8 (destruct H1 as [? H1]; destruct x14; tryfalse).
    simpl; lia.
  }
  {
    unfold OS_Port_V_msgOutTick.
    erewrite update_nth; eauto.
    erewrite nth_upd_neqrev; eauto.
    rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; eauto.
    clear - H1.
    unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
    destruct x14; tryfalse.
    do 9 (destruct H1 as [? H1]; destruct x14; tryfalse).
    simpl; lia.
  }
  {
    intros.
    erewrite nth_upd_neqrev; eauto.
    {
      rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; eauto.
      clear - H1 H16.
      unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
      destruct x14; tryfalse.
      do 18 (destruct H1 as [? H1]; destruct x14; tryfalse).
      simpl; lia.
    }
    erewrite nth_upd_neqrev; eauto.
    {
      rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; eauto.
      clear - H1 H16.
      unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
      destruct x14; tryfalse.
      do 18 (destruct H1 as [? H1]; destruct x14; tryfalse).
      simpl; lia.
    }
  }
Qed.

Lemma dstkportpl_get_and_upd_list_Sample_Incore:
  forall  dstkportpl kportls chanptr otherppl
          dportptr dportl dportmsgll dpptrl dportls
          pin tm newmsg,
  Channel_dstkport_Sample_IncoreC otherppl chanptr dstkportpl kportls dportls ->
  RL_PortPtrList dportptr dportl dpptrl ->
  RLH_Domainportl dportptr dportl dportmsgll dportls ->
  (Forall (struct_type_vallist_match' OS_Port_Seg_dls) dportl) ->
  (exists dstportpl dstpptrnl dstportupdl dstportupdhl,
    length dstportpl = length dstkportpl /\
    length dstpptrnl = length dstkportpl /\
    length dstportupdl = length dstkportpl /\
    length dstportupdhl = length dstkportpl /\
    forall n, (n < length dstkportpl)%nat ->
      exists dstkportp dstportp dstpptrn dstpid dstkpst
          dstpd dstpst dstpin dstpout dstpm,
      exists dstpcn dstportupd dstport dstportupdh nextdst,
        nth_error dstkportpl n = Some dstkportp /\
        nth_error dstportpl n = Some dstportp /\
        nth_error dstportupdl n = Some dstportupd /\
        nth_error dstportupdhl n = Some dstportupdh /\
        nth_error dstpptrnl n = Some dstpptrn /\
        nth_error dpptrl dstpptrn = Some dstportp /\
        nth_error dportl dstpptrn = Some dstport /\
        get kportls dstkportp =
          Some (dstpid, Some dstportp, Some chanptr, dstpcn, dstkpst) /\
        get dportls dstportp = 
          Some (dstpcn, dstpd, dstpid,
            DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
        struct_type_vallist_match' OS_Port_Seg_dls dstportupd /\
        OS_Port_V_msgInTick dstportupd = Some (Vint32 pin) /\
        OS_Port_V_msgOutTick dstportupd = Some (Vint32 tm) /\
        (forall (m:nat), (m < 18)%nat ->
          (m <> 8)%nat -> (m <> 9)%nat -> 
          nth_val m dstportupd = nth_val m dstport) /\
        dstportupdh = (dstpcn, dstpd, dstpid,
          DestinationP nextdst, dstpst, Z.to_nat (Int.unsigned pin),
          Z.to_nat (Int.unsigned tm), SamplePort newmsg)).
Proof.
  induction dstkportpl; simpl; intros; simpljoin1.
  {
    exists (@nil addrval) (@nil nat) (@nil vallist) (@nil absdomainport.B).
    splits; eauto. lia.
  }
  lets IH: IHdstkportpl H3 H0 H1 H2. simpljoin1.
  instantiate (1:=newmsg) in H10.
  instantiate (1:=tm) in H10.
  instantiate (1:=pin) in H10.
  pose proof RLH_Domainportl_abs_getsome _ _ _ _ _ _ _ H0 H1 H4.
  simpljoin1.
  exists (x0 :: x8) (x12 :: x9)
         ((update_nth_val 9 (update_nth_val 8 x13 (Vint32 pin)) (Vint32 tm)) :: x10)
         ((∘ DNUM, x2, x, DestinationP x7, x3, Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm), SamplePort newmsg) :: x11); simpl.
  splits; try lia.
  destruct n.
  2: intros; apply H10; lia.
  simpl; intros.
  do 15 eexists; splits; eauto.
  eapply Forall_forall in H2.
  2: eapply nth_error_In; eapply H11.
  splits.
  { unfold port_coreNum; rewrite H; eauto. }
  { unfold port_coreNum; rewrite H4; eauto. }
  {
    clear - H2.
    unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
    destruct x13; tryfalse.
    do 18 (destruct H2 as [? H2]; destruct x13; tryfalse).
    simpl; pauto.
  }
  {
    unfold OS_Port_V_msgInTick.
    erewrite nth_upd_neqrev; eauto.
    erewrite update_nth; eauto.
    rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; eauto.
    clear - H2.
    unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
    destruct x13; tryfalse.
    do 8 (destruct H2 as [? H2]; destruct x13; tryfalse).
    simpl; lia.
  }
  {
    unfold OS_Port_V_msgOutTick.
    erewrite update_nth; eauto.
    erewrite nth_upd_neqrev; eauto.
    rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; eauto.
    clear - H2.
    unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
    destruct x13; tryfalse.
    do 9 (destruct H2 as [? H2]; destruct x13; tryfalse).
    simpl; lia.
  }
  {
    intros.
    erewrite nth_upd_neqrev; eauto.
    {
      rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; eauto.
      clear - H2 H16.
      unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
      destruct x13; tryfalse.
      do 18 (destruct H2 as [? H2]; destruct x13; tryfalse).
      simpl; lia.
    }
    erewrite nth_upd_neqrev; eauto.
    {
      rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; eauto.
      clear - H2 H16.
      unfold struct_type_vallist_match', OS_Port_Seg_dls in *.
      destruct x13; tryfalse.
      do 18 (destruct H2 as [? H2]; destruct x13; tryfalse).
      simpl; lia.
    }
  }
  { auto. }
Qed.

Lemma dstkportpl_get_Queue_Outcore_lemma:
  forall dstkportpl chanptr otherppl kportls dportls2 otherpl othermsgll,
  Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportpl kportls dportls2 ->
  RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 ->
  (Forall (struct_type_vallist_match' OS_Port_Seg_dls) otherpl) ->
  (exists dstportpl dstpptrnl,
    length dstportpl = length dstkportpl /\
    length dstpptrnl = length dstkportpl /\
    forall n, (n < length dstkportpl)%nat ->
      exists dstkportp dstportp dstpptrn dstpid dstkpst
          dstpd dstpst dstpin dstpout dstsz,
      exists dstpm dstpcn dstport nextdst,
        nth_error dstkportpl n = Some dstkportp /\
        nth_error dstportpl n = Some dstportp /\
        nth_error dstpptrnl n = Some dstpptrn /\
        nth_error otherppl dstpptrn = Some dstportp /\
        nth_error otherpl dstpptrn = Some dstport /\
        get kportls dstkportp =
          Some (dstpid, Some dstportp, Some chanptr, dstpcn, dstkpst) /\
        get dportls2 dstportp = 
          Some (dstpcn, dstpd, dstpid,
            DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm)).
Proof.
  induction dstkportpl; simpl; intros; simpljoin1.
  {
    exists (@nil addrval) (@nil nat).
    splits; eauto. lia.
  }
  lets IH: IHdstkportpl H2 H0 H1. simpljoin1.
  pose proof RLH_OtherPortPtrList_abs_getsome _ _ _ _ _ _ H0 H3.
  simpljoin1.

  exists (x0::x10) (x12::x11);simpl.
  splits; try lia.
  destruct n.
  2: intros; apply H8; lia.
  simpl; intros.
  do 14 eexists; splits; eauto.
Qed.

Lemma Channel_dstkport_Queue_OutcoreC_not_DNUM: forall  dstkportpl otherppl chanptr kportls dportls2
  n p a b c d e, 
  Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportpl kportls dportls2 ->
  nth_error dstkportpl n = Some p ->
  get kportls p = Some (a,b,c,d,e) ->
  Z.of_nat d <> DNUM.
Proof.
  induction dstkportpl; intros.
  + rewrite nth_error_nil in H0. discriminate.
  + simpl in H. simpljoin.
    induction n; intros.
    - simpl in H0. inverts H0. rewrite H in H1. inverts H1. 
      unfold Coqlib.nat_of_Z in H4. lia.
    - simpl in H0. lets Hnew: IHdstkportpl H2 H0 H1. auto.
Qed.

Lemma dstkportpl_get_Queue_Outcore:
  forall dstkportpl chanptr otherppl kportls dportls dportls2 vsdstcl otherpl othermsgll,
  Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportpl kportls dportls2 ->
  RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 ->
  (Forall (struct_type_vallist_match' OS_Port_Seg_dls) otherpl) ->
  (forall n : nat,
         (n < length dstkportpl)%nat ->
         exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout
         dstsz dstpm dstkpaddr,
         exists dstkpst nextdst,
         nth_error dstkportpl n = Some dstkpaddr /\
         get kportls dstkpaddr =
         Some
           (dstpid, Some dstpaddr, Some chanptr, dstpcn,
           dstkpst) /\
         get dportls dstpaddr =
         Some
           (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin,
           dstpout, QueuePort dstsz dstpm) /\
         (Z.of_nat dstpcn <> DNUM ->
          nth_error vsdstcl n = Some (V$ Z.of_nat dstpcn))) ->
  (forall n, (n < length dstkportpl)%nat ->
      exists dstkportp dstportp dstpptrn dstpid dstkpst
          dstpd dstpst dstpin dstpout dstsz,
      exists dstpm dstpcn dstport nextdst,
        nth_error dstkportpl n = Some dstkportp /\
        nth_error otherppl dstpptrn = Some dstportp /\
        nth_error otherpl dstpptrn = Some dstport /\
        get kportls dstkportp =
          Some (dstpid, Some dstportp, Some chanptr, dstpcn, dstkpst) /\
        get dportls2 dstportp = 
          Some (dstpcn, dstpd, dstpid,
            DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\
            nth_error vsdstcl n = Some (V$ Z.of_nat dstpcn) /\ 
            Z.of_nat dstpcn <> DNUM).
Proof.
  intros. lets Hnew: dstkportpl_get_Queue_Outcore_lemma H H0 H1.
  simpljoin. lets H7: H6 H3.
  simpljoin1. do 14 eexists. splits; eauto.
  apply H2 in H3. simpljoin.
  rewrite H3 in H7. inverts H7.
  setoid_rewrite H14 in H12. inverts H12. apply H16.
  cut (Z.of_nat x12 <> DNUM). tauto.
  eapply Channel_dstkport_Queue_OutcoreC_not_DNUM; eauto.
  eapply Channel_dstkport_Queue_OutcoreC_not_DNUM; eauto.
Qed.

Lemma dstkportpl_get_Queue_Incore:
  forall  dstkportpl kportls chanptr otherppl
          dportptr dportl dportmsgll dpptrl dportls,
  Channel_dstkport_Queue_IncoreC otherppl chanptr dstkportpl kportls dportls ->
  RL_PortPtrList dportptr dportl dpptrl ->
  RLH_Domainportl dportptr dportl dportmsgll dportls ->
  (Forall (struct_type_vallist_match' OS_Port_Seg_dls) dportl) ->
  (
    forall n, (n < length dstkportpl)%nat ->
      exists dstkportp dstportp dstpptrn dstpid dstkpst
          dstpd dstpst dstpin dstpout dstsz,
      exists dstpm dstport nextdst,
        nth_error dstkportpl n = Some dstkportp /\
        nth_error dpptrl dstpptrn = Some dstportp /\
        nth_error dportl dstpptrn = Some dstport /\
        get kportls dstkportp =
          Some (dstpid, Some dstportp, Some chanptr, nat_of_Z DNUM, dstkpst) /\
        get dportls dstportp = 
          Some (nat_of_Z DNUM, dstpd, dstpid,
            DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) 
    ).
Proof.
  induction dstkportpl; simpl; intros; simpljoin1.
  {
     lia.
  }
  lets IH: IHdstkportpl H4 H0 H1 H2. simpljoin1.
  
  destruct n.
  - pose proof RLH_Domainportl_abs_getsome _ _ _ _ _ _ _ H0 H1 H5.
    simpljoin1. do 13 eexists; splits; eauto. reflexivity.
  - 
    assert (n< length dstkportpl)%nat by lia.
    apply IH in H7. simpljoin. do 13 eexists; splits.  simpl.  all: eauto.
Qed.


Fixpoint set_dportls_n_times (dportls: DomainPortMod.map) (n: nat) (dportpl: list addrval) (dporthl: list (absdomainport.B)):=
  match n, dportpl, dporthl with
  | 0%nat, _, _ => dportls 
  | S n', dportp::dportpl', dporth::dporthl' =>
      set_dportls_n_times (set dportls dportp dporth) n' dportpl' dporthl'
  | _, _, _ => empenv
  end.

Fixpoint set_dportl_n_times (dportl: list vallist) (n: nat) (nl: list nat) (updl: list vallist):=
  match n, nl, updl with
  | 0%nat, _, _ => dportl
  | S n', m::nl', upd::updl' =>
      set_dportl_n_times (ifun_spec.update_nth vallist m dportl upd) n' nl' updl'
  | _, _, _ => nil
  end.

Fixpoint set_dportmsgll_n_times (dportmsgll: list (list vallist)) (n: nat) (nl: list nat) (msgl: list vallist):=
  match n, nl with
  | 0%nat, _=> dportmsgll
  | S n', m::nl' =>
      set_dportmsgll_n_times (ifun_spec.update_nth (list vallist) m dportmsgll msgl) n' nl' msgl
  | _, _ => nil
  end.

Lemma nth_error_update_nth_same: forall [A:Type] dportl x0 x2,
  (x2 < length dportl)%nat ->
  nth_error (ifun_spec.update_nth A x2 dportl x0) x2 = Some x0.
Proof.
  induction dportl; destruct x2; simpl; intros; try lia; auto.
  apply IHdportl; lia.
Qed.

Lemma nth_error_update_nth_dif: forall [A:Type] dportl x0 x2 x x4,
  x <> x2 ->
  (x < length dportl)%nat ->
  (x2 < length dportl)%nat ->
  nth_error dportl x2 = Some x4 ->
  nth_error (ifun_spec.update_nth A x dportl x0) x2 = Some x4.
Proof.
  induction dportl; destruct x; destruct x2; simpl; intros; try lia; auto.
  apply IHdportl; try lia; auto.
Qed.

Lemma set_dportl_n_times_upd_same_elements: forall dstpptrnl dstportupdl n dportl dportl' ndstportupd ndstpptrn ndstport,
  (n < length dstpptrnl)%nat ->
  length dstpptrnl = length dstportupdl ->
  (forall m, (m < length dstpptrnl)%nat ->
    exists dstpptrn dstportupd dstport,
      nth_error dstportupdl m = Some dstportupd /\
      nth_error dstpptrnl m = Some dstpptrn /\
      nth_error dportl dstpptrn = Some dstport /\
      (forall k : nat, (k < 18)%nat -> k <> 8%nat ->
       k <> 9%nat -> nth_val k dstportupd = nth_val k dstport)) ->
  nth_error dstportupdl n = Some ndstportupd ->
  nth_error dstpptrnl n = Some ndstpptrn ->
  nth_error dportl ndstpptrn = Some ndstport ->
  dportl' = set_dportl_n_times dportl n dstpptrnl dstportupdl ->
  exists ndstport',
    nth_error dportl' ndstpptrn = Some ndstport' /\
    forall m : nat,
      (m < 18)%nat -> m <> 8%nat -> m <> 9%nat ->
      nth_val m ndstportupd = nth_val m ndstport'.
Proof.
  induction dstpptrnl; destruct dstportupdl; destruct n; simpl; intros; tryfalse; subst.
  {
    exists ndstport.
    split; auto.
    inverts H2; inverts H3.
    assert ((0 < S (length dstpptrnl))%nat) by lia.
    specialize (H1 _ H2).
    simpl in H1; simpljoin1.
    inverts H1; inverts H3.
    rewrite H5 in H4; inverts H4.
    apply H6; auto.
  }
  assert ((ndstpptrn = a)%nat \/ (a <> ndstpptrn)%nat) by lia.
  destruct H5; subst.
  {
    assert ((n < length dstpptrnl)%nat) by lia.
    assert (length dstpptrnl = length dstportupdl) by lia.
    assert ((forall m : nat,
            (m < length dstpptrnl)%nat ->
            exists dstpptrn dstportupd dstport,
            nth_error dstportupdl m = Some dstportupd /\
            nth_error dstpptrnl m = Some dstpptrn /\
            nth_error (ifun_spec.update_nth vallist a dportl v) dstpptrn = Some dstport /\
            (forall k : nat, (k < 18)%nat -> k <> 8%nat -> k <> 9%nat ->
            nth_val k dstportupd = nth_val k dstport))).
    {
      intros.
      assert ((S m < S (length dstpptrnl))%nat) by lia.
      assert ((0 < S (length dstpptrnl))%nat) by lia.
      pose proof H1 _ H8.
      pose proof H1 _ H9.
      simpl in H10; simpl in H11; simpljoin1.
      inverts H11; inverts H12.
      assert ((x = x2)%nat \/ (x <> x2)%nat) by lia.
      destruct H11; subst.
      {
        rewrite H13 in H16; inverts H16.
        exists x2 x3 x0; splits; auto.
        {
          eapply nth_error_update_nth_same.
          eapply nth_error_Some.
          rewrite H13; auto.
        }
        intros.
        rewrite H14; auto.
      }
      exists x2 x3 x4; splits; auto.
      eapply nth_error_update_nth_dif; auto.
      eapply nth_error_Some; rewrite H13; auto.
      eapply nth_error_Some; rewrite H16; auto.
    }
    assert (nth_error (ifun_spec.update_nth vallist a dportl v) a = Some v).
    {
      eapply nth_error_update_nth_same.
      eapply nth_error_Some.
      rewrite H4; auto.
    }
    assert (set_dportl_n_times (ifun_spec.update_nth vallist a dportl v) n dstpptrnl dstportupdl =
            set_dportl_n_times (ifun_spec.update_nth vallist a dportl v) n dstpptrnl dstportupdl) by auto.
    specialize (IHdstpptrnl dstportupdl n (ifun_spec.update_nth vallist a dportl v)
        (set_dportl_n_times (ifun_spec.update_nth vallist a dportl v) n dstpptrnl dstportupdl)
        ndstportupd a v H5 H6 H7 H2 H3 H8 H9).
    apply IHdstpptrnl; auto.
  }
  {
    assert ((n < length dstpptrnl)%nat) by lia.
    assert (length dstpptrnl = length dstportupdl) by lia.
    assert ((forall m : nat,
            (m < length dstpptrnl)%nat ->
            exists dstpptrn dstportupd dstport,
            nth_error dstportupdl m = Some dstportupd /\
            nth_error dstpptrnl m = Some dstpptrn /\
            nth_error (ifun_spec.update_nth vallist a dportl v) dstpptrn = Some dstport /\
            (forall k : nat, (k < 18)%nat -> k <> 8%nat -> k <> 9%nat ->
              nth_val k dstportupd = nth_val k dstport))).
    {
      intros.
      assert ((S m < S (length dstpptrnl))%nat) by lia.
      assert ((0 < S (length dstpptrnl))%nat) by lia.
      pose proof H1 _ H9.
      pose proof H1 _ H10.
      simpl in H11; simpl in H12; simpljoin1.
      inverts H12; inverts H13.
      assert ((x = x2)%nat \/ (x <> x2)%nat) by lia.
      destruct H12; subst.
      {
        rewrite H14 in H17; inverts H17.
        exists x2 x3 x0; splits; auto.
        {
          eapply nth_error_update_nth_same.
          eapply nth_error_Some.
          rewrite H14; auto.
        }
        intros.
        rewrite H15; auto.
      }
      exists x2 x3 x4; splits; auto.
      eapply nth_error_update_nth_dif; auto.
      eapply nth_error_Some. rewrite H14; auto.
      eapply nth_error_Some. rewrite H17; auto.
    }
    assert (nth_error (ifun_spec.update_nth vallist a dportl v) ndstpptrn = Some ndstport).
    {
      eapply nth_error_update_nth_dif; auto.
      2: eapply nth_error_Some; rewrite H4; auto.
      assert ((0 < S (length dstpptrnl))%nat) by lia.
      pose proof H1 _ H9.
      simpl in H10; simpljoin1.
      inverts H10; inverts H11.
      eapply nth_error_Some; rewrite H12; auto.
    }
    assert (set_dportl_n_times (ifun_spec.update_nth vallist a dportl v) n dstpptrnl dstportupdl =
            set_dportl_n_times (ifun_spec.update_nth vallist a dportl v) n dstpptrnl dstportupdl) by auto.
    specialize (IHdstpptrnl dstportupdl n (ifun_spec.update_nth vallist a dportl v)
        (set_dportl_n_times (ifun_spec.update_nth vallist a dportl v) n dstpptrnl dstportupdl)
        ndstportupd ndstpptrn ndstport H6 H7 H8 H2 H3 H9 H10).
    apply IHdstpptrnl; auto.
  }
Qed.

Lemma dpptrl_in_dportls:
  forall dportl headptr dpptrl dportmsgll dportls n x,
    RL_PortPtrList headptr dportl dpptrl ->
    RLH_Domainportl headptr dportl dportmsgll dportls ->
    nth_error dpptrl n = Some x ->
    exists y dportls', join (sig x y) dportls' dportls.
Proof.
  induction dportl; destruct dpptrl; destruct dportmsgll; simpl; intros; tryfalse.
  { rewrite nth_error_nil in *; tryfalse. }
  simpl in *; simpljoin1.
  rewrite H6 in H4; inverts H0; inverts H4.
  destruct n; simpl in *.
  { inverts H1; exists x1 x2; auto. }
  specialize (IHdportl _ _ _ _ _ _ H7 H5 H1).
  simpljoin1.
  exists x4 (merge (sig x0 x1) x5).
  pose proof join_merge H; subst x2.
  pose proof join_merge H2; subst dportls.
  apply join_sem.
  {
    eapply invariant_prop.invariant_prop_map3.
    2: apply map_join_comm in H; eauto.
    apply map_join_comm in H2.
    apply map_tactics.join_disj in H2.
    auto.
  }
  eapply perm_map_lemmas_part2.mem_join_join_merge_eq'; eauto.
Qed.

Lemma dpptrl_not_same_elements:
  forall dportl dpptrl dportmsgll dportls n1 n2 x headptr,
    RL_PortPtrList headptr dportl dpptrl ->
    RLH_Domainportl headptr dportl dportmsgll dportls ->
    nth_error dpptrl n1 = Some x ->
    nth_error dpptrl n2 = Some x -> n1 = n2.
Proof.
  induction dportl; destruct dpptrl; destruct dportmsgll; simpl; intros; tryfalse.
  { rewrite nth_error_nil in *; tryfalse. }
  destruct n1; destruct n2; auto; simpl in *; simpljoin1.
  {
    inverts H1; inverts H0.
    rewrite H7 in H5; inverts H5.
    pose proof dpptrl_in_dportls _ _ _ _ _ _ _ H8 H6 H2.
    simpljoin1. exfalso.
    eapply map_join_get_some in H3; auto.
    eapply join_sig_get; eauto.
    eapply map_join_emp.
    eapply join_sig_get; eauto.
  }
  {
    inverts H2; inverts H0.
    rewrite H7 in H5; inverts H5.
    pose proof dpptrl_in_dportls _ _ _ _ _ _ _ H8 H6 H1.
    simpljoin1. exfalso.
    eapply map_join_get_some in H3; auto.
    eapply join_sig_get; eauto.
    eapply map_join_emp.
    eapply join_sig_get; eauto.
  }
  rewrite H7 in H5; inverts H5.
  specialize (IHdportl _ _ _ _ _ _ _ H8 H6 H1 H2).
  lia.
Qed.

Lemma otherppl_in_dportls:
  forall otherppl otherpl othermsgll dportls n x,
    RLH_OtherPortPtrList otherppl otherpl othermsgll dportls ->
    nth_error otherppl n = Some x ->
    exists y dportls', join (sig x y) dportls' dportls.
Proof.
  induction otherppl; destruct otherpl; destruct othermsgll; simpl; intros; tryfalse.
  { rewrite nth_error_nil in *; tryfalse. }
  simpl in *; simpljoin1.
  destruct n; simpl in *.
  { inverts H0. exists x0 x1; auto. }
  specialize (IHotherppl _ _ _ _ _ H2 H0).
  simpljoin1.
  exists x2 (merge (sig a x0) x3).
  pose proof join_merge H3; subst x1.
  pose proof join_merge H; subst dportls.
  apply join_sem.
  {
    eapply invariant_prop.invariant_prop_map3.
    2: apply map_join_comm in H3; eauto.
    apply map_join_comm in H.
    apply map_tactics.join_disj in H.
    auto.
  }
  eapply perm_map_lemmas_part2.mem_join_join_merge_eq'; eauto.
Qed.

Lemma otherppl_not_same_elements:
  forall otherppl otherpl othermsgll dportls n1 n2 x,
    RLH_OtherPortPtrList otherppl otherpl othermsgll dportls ->
    nth_error otherppl n1 = Some x ->
    nth_error otherppl n2 = Some x -> n1 = n2.
Proof.
  induction otherppl; destruct otherpl; destruct othermsgll; simpl; intros; tryfalse.
  { rewrite nth_error_nil in *; tryfalse. }
  destruct n1; destruct n2; auto; simpl in *; simpljoin1.
  {
    inverts H0.
    pose proof otherppl_in_dportls _ _ _ _ _ _ H3 H1.
    simpljoin1. exfalso.
    eapply map_join_get_some in H; auto.
    eapply join_sig_get; eauto.
    eapply map_join_emp.
    eapply join_sig_get; eauto.
  }
  {
    inverts H1.
    pose proof otherppl_in_dportls _ _ _ _ _ _ H3 H0.
    simpljoin1. exfalso.
    eapply map_join_get_some in H; auto.
    eapply join_sig_get; eauto.
    eapply map_join_emp.
    eapply join_sig_get; eauto.
  }
  specialize (IHotherppl _ _ _ _ _ _ H3 H0 H1).
  lia.
Qed.

Lemma set_dportls_n_times_upd_same_elements:
  forall dstpptrnl dstportpl dstportupdhl dpptrl n
        ndstportupdh ndstportp ndstpptrn ndstpcn ndstpd ndstpid
        ndstpst ndstpin ndstpout ndstpm dportls' dportls nextdst,
    (n < length dstpptrnl)%nat ->
    length dstpptrnl = length dstportupdhl ->
    length dstpptrnl = length dstportpl ->
    (forall m, (m < length dstpptrnl)%nat ->
      (exists dstpptrn dstportupdh dstportp dstpcn dstpd dstpid 
             dstpst dstpin dstpout, exists dstpm dstpin' dstpout' dstpm' nextdst,
        nth_error dstportupdhl m = Some dstportupdh /\
        nth_error dstportpl m = Some dstportp /\
        nth_error dstpptrnl m = Some dstpptrn /\
        nth_error dpptrl dstpptrn = Some dstportp /\
        get dportls dstportp = Some (dstpcn, dstpd, dstpid,
          DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
        dstportupdh = (dstpcn, dstpd, dstpid,
          DestinationP nextdst, dstpst, dstpin', dstpout', SamplePort dstpm'))) ->
    nth_error dstportupdhl n = Some ndstportupdh ->
    nth_error dstportpl n = Some ndstportp ->
    nth_error dstpptrnl n = Some ndstpptrn ->
    nth_error dpptrl ndstpptrn = Some ndstportp ->
    get dportls ndstportp = Some (ndstpcn, ndstpd, ndstpid,
      DestinationP nextdst, ndstpst, ndstpin, ndstpout, SamplePort ndstpm) ->
    dportls' = set_dportls_n_times dportls n dstportpl dstportupdhl ->
    exists ndstpin' ndstpout' ndstpm',
      get dportls' ndstportp = Some (ndstpcn, ndstpd, ndstpid,
        DestinationP nextdst, ndstpst, ndstpin', ndstpout', SamplePort ndstpm').
Proof.
  induction dstpptrnl; destruct dstportupdhl; destruct dstportpl; destruct n; simpl; intros; tryfalse; subst.
  { rewrite H7; eauto. }
  assert ((0 < S (length dstpptrnl))%nat) by lia.
  pose proof H2 _ H8.
  pose proof H2 _ H.
  simpl in H9; simpl in H10; simpljoin1.
  inverts H9; inverts H16; inverts H17.
  rewrite H3 in H10; inverts H10.
  rewrite H4 in H11; inverts H11.
  rewrite H5 in H12; inverts H12.
  rewrite H7 in H14; inverts H14.
  clear H13.

  assert (x15 = x1 \/ x15 <> x1) by tauto.
  destruct H9; subst.
  {
    eapply IHdstpptrnl.
    10: eauto.
    all: eauto.
    lia.
    2:{
      instantiate (1:=x25).
      instantiate (1:=x24).
      instantiate (1:=x23).
      rewrite H19 in H7; inverts H7.
      apply set_a_get_a.
    }
    intros.
    assert (((S m) < (S (length dstpptrnl)))%nat) by lia.
    pose proof H2 _ H10.
    simpl in H11; simpljoin1.
    assert (x15 = x1 \/ x15 <> x1) by tauto.
    destruct H16; subst.
    {
      rewrite H19 in H15; inverts H15.
      do 14 eexists; splits; eauto.
      apply set_a_get_a.
    }
    do 14 eexists; splits; eauto.
    eapply get_set_neq; eauto.
  }
  eapply IHdstpptrnl.
  10: eauto.
  all: eauto.
  lia.
  2: eapply get_set_neq; eauto.
  intros.
  assert (((S m) < (S (length dstpptrnl)))%nat) by lia.
  pose proof H2 _ H11.
  simpl in H12; simpljoin1.
  assert (x27 = x1 \/ x27 <> x1) by tauto.
  destruct H17; subst.
  {
    rewrite H7 in H16; inverts H16.
    do 14 eexists; splits; eauto.
    eapply get_set_neq; eauto.
  }
  assert (x27 = x15 \/ x27 <> x15) by tauto.
  destruct H20; subst.
  {
    rewrite H19 in H16; inverts H16.
    do 14 eexists; splits; eauto.
    eapply set_a_get_a.
  }
  do 14 eexists; splits; eauto.
  eapply get_set_neq; eauto.
Qed.

Lemma nodup_cheapl_get_msg:
  forall  cheapl1 cheapl2 msgptr ori_msgn ori_len_v ori_msg_vl ori_msg_vl2
          cheapl mlen msg,
    cheapl = (cheapl1 ++
                (msgptr, ori_msgn,
                  (ori_len_v :: ori_msg_vl) ++ ori_msg_vl2) :: cheapl2) ->
    NoDup (map fst (map fst cheapl)) ->
    Get_heapl_addrval cheapl msgptr (S (length ori_msg_vl)) (Vint32 mlen :: msg) ->
    S (length ori_msg_vl) = Z.to_nat (Int.unsigned mlen + 1) -> 
    ori_len_v = Vint32 mlen /\ msg = ori_msg_vl.
Proof.
  intros.
  assert ((map fst (map fst (cheapl1 ++ (msgptr, ori_msgn,
      ori_len_v :: ori_msg_vl ++ ori_msg_vl2) :: cheapl2))) = 
    (map fst (map fst cheapl1)) ++ msgptr :: (map fst (map fst cheapl2))).
  {
    clear; revert cheapl2.
    induction cheapl1; simpl; auto; intros.
    specialize (IHcheapl1 cheapl2); simpl in IHcheapl1.
    rewrite IHcheapl1; auto.
  }
  simpljoin1; simpl in *; rewrite H3 in  H0; clear H3.
  induction cheapl1; simpl; auto; intros.
  {
    unfold Get_heapl_addrval in H1; simpljoin1.
    rewrite app_nil_l in *.
    destruct H.
    {
      inverts H; simpl in H3.
      rewrite firstn_app in H3.
      rewrite firstn_all in H3.
      assert ((length ori_msg_vl - length ori_msg_vl)%nat = 0%nat) by lia.
      rewrite H, firstn_O in H3.
      inverts H3.
      rewrite app_nil_r; auto.
    }
    apply NoDup_cons_iff in H0; destruct H0.
    exfalso; destruct H0.
    assert (msgptr = (fst (fst (msgptr, x, x0)))) by auto.
    rewrite H0; apply in_map; apply in_map; auto.
  }
  unfold Get_heapl_addrval in H1; simpljoin1; simpl in H0.
  apply IHcheapl1; clear IHcheapl1.
  {
    unfold Get_heapl_addrval; exists x x0; splits; auto.
    clear - H0 H; destruct H; auto.
    subst; simpl in H0; exfalso.
    apply NoDup_cons_iff in H0; destruct H0.
    destruct H; apply in_elt.
  }
  clear - H0.
  apply NoDup_cons_iff in H0; destruct H0; auto.
Qed.

Lemma RH_CorePortPtrList_upd_dportls: forall pl p dportls dportls'  portp pcn pd pid d pst pin pout pm
  pcn' pd' pid' pst' pin' pout' pm',
  RH_CorePortPtrList p pl dportls ->
  get dportls portp = Some (pcn, pd, pid, d, pst, pin, pout, pm) ->
  dportls' = set dportls portp (pcn', pd', pid', d, pst', pin', pout', pm') ->
  RH_CorePortPtrList p pl dportls'.
Proof.
  induction pl; intros; simpl RH_CorePortPtrList in *; auto.
  simpljoin1.
  pose proof (addrval_eq_dec portp a).
  destruct H; subst.
  {
    setoid_rewrite H0 in H2; inverts H2.
    do 8 eexists; eauto.
    splits; auto.
    eapply set_a_get_a.
    eauto.
  }
  do 8 eexists. splits; auto.  
  eapply get_set_neq; eauto.
  eauto.
Qed.

Lemma R_KernelPortIDTbl_ChannelIDTbl_upd_dportls1:
  forall kportpl kportl chanpl chanl chandstkportll kportls dportls1 dportls2
        dstkportp dstportp chanp pcn dstkpst pd pid d pst dstpin dstpout pm pin msg tm,
  R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl chandstkportll kportls dportls1 dportls2 ->
  get kportls dstkportp =  Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
  get dportls1 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, pm) ->
  nodup_dport kportls ->
  R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl
    chandstkportll kportls 
    (set dportls1 dstportp
      (pcn, pd, pid, d, pst, pin, tm, msg)) dportls2.
Proof.
  induction kportpl; destruct kportl; simpl; intros; tryfalse; auto; simpljoin1.
  split; eauto.
  destruct H; [left|right]; auto.
  unfold R_KernelPortIDTbl_ChannelIDTbl_kport_Vptr in *; simpljoin1.
  eexists; splits; eauto.
  destruct H5; [left|right]; auto.
  unfold R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr in *; simpljoin1.
  do 9 eexists; splits; eauto.
  instantiate (1:=x8).
  destruct H11; [left|right]; auto.
  {
    unfold R_KernelPortIDTbl_ChannelIDTbl_IncoreC in *; simpljoin1.
    splits; eauto.
    destruct H12; [left|right]; auto.
    {
      unfold R_KernelPortIDTbl_ChannelIDTbl_scr in *; simpljoin1.
      assert (x <> dstkportp \/ x = dstkportp) by tauto.
      destruct H16.
      {
        unfold nodup_dport in H2.
        specialize (H2 x dstkportp H16).
        unfold port_coreNum, port_id, tid in H2, H10, H0.
        rewrite H10, H0 in H2.
        exists x9 x10 x11 x12 x13; splits; eauto.
        rewrite <- H12.
        apply map_tactics.neq_set_get; auto.
      }
      subst x.
      unfold port_coreNum, port_id, tid in H0, H10.
      rewrite H0 in H10; inverts H10.
      unfold port_coreNum, port_id, tid in H1, H12.
      rewrite H12 in H1; inverts H1.
      exists pd pst pin tm msg; splits; eauto.
      eapply set_a_get_a.
    }
    unfold R_KernelPortIDTbl_ChannelIDTbl_dst in *; simpljoin1.
    assert (x <> dstkportp \/ x = dstkportp) by tauto.
    destruct H17.
    {
      unfold nodup_dport in H2.
      specialize (H2 x dstkportp H17).
      rewrite H0 in H2.
      unfold port_coreNum, port_id, tid in H2, H10.
      rewrite H10 in H2.
      exists x9 x10 x11 x12 x13 x14; exists x15; splits; eauto.
      rewrite <- H12.
      apply map_tactics.neq_set_get; auto.
    }
    subst x.
    unfold port_coreNum, port_id, tid in H0, H10.
    rewrite H0 in H10; inverts H10.
    unfold port_coreNum, port_id, tid in H1, H12.
    rewrite H12 in H1; inverts H1.
    exists x9 pd pst pin tm msg; exists x15; splits; eauto.
    eapply set_a_get_a.
  }
  unfold R_KernelPortIDTbl_ChannelIDTbl_OutcoreC in *; simpljoin1.
  eexists; splits; eauto.
  destruct H13; [left|right]; auto.
  unfold R_KernelPortIDTbl_ChannelIDTbl_scr in *; simpljoin1.
  assert (x <> dstkportp \/ x = dstkportp) by tauto.
  destruct H17.
  {
    unfold nodup_dport in H2.
    specialize (H2 x dstkportp H17).
    rewrite H0 in H2.
    unfold port_coreNum, port_id, tid in H2, H10.
    rewrite H10 in H2.
    exists x10 x11 x12 x13 x14; splits; eauto.
    rewrite <- H13.
    apply map_tactics.neq_set_get; auto.
  }
  subst x.
  unfold port_coreNum, port_id, tid in H0, H10.
  rewrite H0 in H10; inverts H10.
  unfold port_coreNum, port_id, tid in H1, H13.
  rewrite H13 in H1; inverts H1.
  exists pd pst pin tm msg; splits; eauto.
  eapply set_a_get_a.
Qed.

Lemma R_KernelPortIDTbl_ChannelIDTbl_upd_dportls2:
  forall kportpl kportl chanpl chanl chandstkportll kportls dportls1 dportls2
        dstkportp dstportp chanp pcn dstkpst pd pid d pst dstpin dstpout pm pin msg tm,
  R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl chandstkportll kportls dportls1 dportls2 ->
  get kportls dstkportp =  Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
  get dportls2 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, pm) ->
  nodup_dport kportls ->
  R_KernelPortIDTbl_ChannelIDTbl kportpl kportl chanpl chanl
    chandstkportll kportls dportls1
    (set dportls2 dstportp
      (pcn, pd, pid, d, pst, pin, tm, msg)).
Proof.
  induction kportpl; destruct kportl; simpl; intros; tryfalse; auto; simpljoin1.
  split; eauto.
  destruct H; [left|right]; auto.
  unfold R_KernelPortIDTbl_ChannelIDTbl_kport_Vptr in *; simpljoin1.
  eexists; splits; eauto.
  destruct H5; [left|right]; auto.
  unfold R_KernelPortIDTbl_ChannelIDTbl_chan_Vptr in *; simpljoin1.
  do 9 eexists; splits; eauto.
  instantiate (1:=x8).
  destruct H11; [left|right]; auto.
  unfold R_KernelPortIDTbl_ChannelIDTbl_OutcoreC in *; simpljoin1.
  eexists; splits; eauto.
  destruct H13; [left|right]; auto.
  unfold R_KernelPortIDTbl_ChannelIDTbl_dst in *; simpljoin1.
  assert (x <> dstkportp \/ x = dstkportp) by tauto.
  destruct H18.
  {
    unfold nodup_dport in H2.
    specialize (H2 x dstkportp H18).
    rewrite H0 in H2.
    unfold port_coreNum, port_id, tid in H2, H10.
    rewrite H10 in H2.
    exists x10 x11 x12 x13 x14 x15; exists x16; splits; eauto.
    rewrite <- H13.
    apply map_tactics.neq_set_get; auto.
  }
  subst x.
  unfold port_coreNum, port_id, tid in H0, H10.
  rewrite H0 in H10; inverts H10.
  unfold port_coreNum, port_id, tid in H1, H13.
  rewrite H13 in H1; inverts H1.
  exists x10 pd pst pin tm msg; exists x16; splits; eauto.
  eapply set_a_get_a.
Qed.

Lemma Channel_dstkport_Sample_OutcoreC_upd_dportls2_Sample:
  forall dstkportl otherppl chanptr kportls dportls2 dstportp dstkportp pid chanp pcn dstkpst pd d pst dstpin dstpout pm pin tm msg,
    Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportl kportls dportls2 ->
    (* nth_error otherppl n = Some dstportp -> *)
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls2 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, SamplePort pm) ->
    nodup_dport kportls ->
    Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportl kportls
      (set dportls2 dstportp (pcn, pd, pid, d, pst, pin, tm, SamplePort msg)).
Proof.
  induction dstkportl; simpl; intros; auto; simpljoin1; splits; eauto.
  assert (a <> dstkportp \/ a = dstkportp) by tauto.
  destruct H7.
  {
    unfold nodup_dport in H2.
    specialize (H2 _ _ H7).
    unfold port_coreNum, port_id, tid in H0, H, H2.
    rewrite H, H0 in H2.
    exists x x0 x1 x2 x3 x4; exists x5 x6 x7 x8; splits; eauto.
    rewrite <- H4.
    apply map_tactics.neq_set_get; auto.
  }
  subst a.
  unfold port_coreNum, port_id, tid in H, H0.
  rewrite H in H0; inverts H0.
  unfold port_coreNum, port_id, tid in H1, H4.
  rewrite H1 in H4; inverts H4.
  exists pid dstportp pcn dstkpst x3 x4; exists pin tm msg x8; splits; eauto.
  eapply set_a_get_a.
Qed.

Lemma Channel_dstkport_Queue_OutcoreC_upd_dportls2_Sample:
  forall dstkportl otherppl chanptr kportls dportls2 dstportp dstkportp pid chanp pcn dstkpst pd pst d dstpin dstpout pm pin tm msg,
  Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportl kportls dportls2 ->
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls2 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, SamplePort pm) ->
    nodup_dport kportls ->
    Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportl kportls
      (set dportls2 dstportp (pcn, pd, pid, d, pst, pin, tm, SamplePort msg)).
Proof.
  induction dstkportl; simpl; intros; auto; simpljoin1; splits; eauto.
  assert (a <> dstkportp \/ a = dstkportp) by tauto.
  destruct H7.
  {
    unfold nodup_dport in H2.
    specialize (H2 _ _ H7).
    unfold port_coreNum, port_id, tid in H0, H, H2.
    rewrite H, H0 in H2.
    exists x x0 x1 x2 x3 x4; exists x5 x6 x7 x8 x9; splits; eauto.
    rewrite <- H4.
    apply map_tactics.neq_set_get; auto.
  }
  subst a.
  unfold port_coreNum, port_id, tid in H, H0.
  rewrite H in H0; inverts H0.
  unfold port_coreNum, port_id, tid in H1, H4.
  rewrite H1 in H4; inverts H4.
Qed.

Lemma Channel_dstkport_Sample_IncoreC_upd_dportls1:
  forall dstkportl otherppl chanptr kportls dportls1 dstportp dstkportp pid chanp pcn dstkpst pd pst d dstpin dstpout pm pin tm msg,
    Channel_dstkport_Sample_IncoreC otherppl chanptr dstkportl kportls dportls1 ->
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls1 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, pm) ->
    nodup_dport kportls ->
    (exists u v, pm = SamplePort u /\ msg = SamplePort v) \/
     (exists u v x y, pm = QueuePort u v /\ msg = QueuePort x y) ->
    Channel_dstkport_Sample_IncoreC otherppl chanptr dstkportl kportls
      (set dportls1 dstportp (pcn, pd, pid, d, pst, pin, tm, msg)).
Proof.
  induction dstkportl; simpl; intros; auto; simpljoin1; splits; eauto.
  assert (a <> dstkportp \/ a = dstkportp) by tauto.
  destruct H7.
  {
    unfold nodup_dport in H2.
    specialize (H2 _ _ H7).
    unfold port_coreNum, port_id, tid in H0, H, H2.
    rewrite H, H0 in H2.
    exists x x0 x1 x2 x3 x4; exists x5 x6 x7; splits; eauto.
    rewrite <- H5.
    apply map_tactics.neq_set_get; auto.
  }
  subst a.
  unfold port_coreNum, port_id, tid in H, H0.
  rewrite H in H0; inverts H0.
  unfold port_coreNum, port_id, tid in H1, H5.
  rewrite H1 in H5; inverts H5.
  destruct H3; simpljoin1.
  exists pid dstportp dstkpst x2 x3; exists pin tm x0 x7; splits; eauto.
  eapply set_a_get_a.
  inverts H0.
Qed.

Lemma Channel_dstkport_Queue_IncoreC_upd_dportls1:
  forall dstkportl otherppl chanptr kportls dportls1 dstportp dstkportp pid chanp pcn dstkpst pd d pst dstpin dstpout pm pin tm msg,
    Channel_dstkport_Queue_IncoreC otherppl chanptr dstkportl kportls dportls1 ->
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls1 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, pm) ->
    nodup_dport kportls ->
    (exists u v, pm = SamplePort u /\ msg = SamplePort v) \/
     (exists u v x y, pm = QueuePort u v /\ msg = QueuePort x y) ->
    Channel_dstkport_Queue_IncoreC otherppl chanptr dstkportl kportls
      (set dportls1 dstportp (pcn, pd, pid, d, pst, pin, tm, msg)).
Proof.
  induction dstkportl; simpl; intros; auto; simpljoin1; splits; eauto.
  assert (a <> dstkportp \/ a = dstkportp) by tauto.
  destruct H7.
  {
    unfold nodup_dport in H2.
    specialize (H2 _ _ H7).
    unfold port_coreNum, port_id, tid in H0, H, H2.
    rewrite H, H0 in H2.
    exists x x0 x1 x2 x3 x4; exists x5 x6 x7 x8; splits; eauto.
    rewrite <- H5.
    apply map_tactics.neq_set_get; auto.
  }
  subst a.
  unfold port_coreNum, port_id, tid in H, H0.
  rewrite H in H0; inverts H0.
  unfold port_coreNum, port_id, tid in H1, H5.
  rewrite H1 in H5; inverts H5.
  destruct H3; simpljoin1.
  inverts H0.
  exists pid dstportp dstkpst x2 x3; exists pin tm x1 x9 x8; splits; eauto.
  eapply set_a_get_a.
Qed.

Lemma Channel_srckport_Sample_upd_dportls1:
  forall dstkportl chanptr kportls dportls1 dstportp dstkportp pid chanp pcn dstkpst pd d pst dstpin dstpout pm pin tm msg,
  Channel_srckport_Sample chanptr dstkportl kportls dportls1 ->
  get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
  get dportls1 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, pm) ->
  nodup_dport kportls ->
  (exists u v, pm = SamplePort u /\ msg = SamplePort v) \/
     (exists u v x y, pm = QueuePort u v /\ msg = QueuePort x y) ->
  Channel_srckport_Sample chanptr dstkportl kportls
    (set dportls1 dstportp (pcn, pd, pid, d, pst, pin, tm, msg)).
Proof.
  intros.
  unfold Channel_srckport_Sample in *.
  destruct H; [left;splits|right]; simpljoin1; auto.
  exists x; splits; eauto.
  assert (x <> dstkportp \/ x = dstkportp) by tauto.
  destruct H7.
  {
    unfold nodup_dport in H2.
    specialize (H2 _ _ H7).
    unfold port_coreNum, port_id, tid in H0, H5, H2.
    rewrite H5, H0 in H2.
    exists x0 x1 x2 x3 x4; exists x5 x6 x7; splits; eauto.
    rewrite <- H6.
    apply map_tactics.neq_set_get; auto.
  }
  subst x.
  unfold port_coreNum, port_id, tid in H5, H0.
  rewrite H5 in H0; inverts H0.
  unfold port_coreNum, port_id, tid in H1, H6.
  rewrite H1 in H6; inverts H6.
  destruct H3; simpljoin1.
  exists pid dstportp dstkpst x3 x4; exists pin tm x0; splits; eauto.
  eapply set_a_get_a.
  inverts H0.
Qed.

Lemma Channel_srckport_Queue_upd_dportls1:
  forall dstkportl chanptr kportls dportls1 dstportp dstkportp pid chanp pcn dstkpst pd d pst dstpin dstpout pm pin tm msg,
  Channel_srckport_Queue chanptr dstkportl kportls dportls1 ->
  get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
  get dportls1 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, pm) ->
  nodup_dport kportls ->
  (exists u v, pm = SamplePort u /\ msg = SamplePort v) \/
     (exists u v x y, pm = QueuePort u v /\ msg = QueuePort x y) ->
  Channel_srckport_Queue chanptr dstkportl kportls
    (set dportls1 dstportp (pcn, pd, pid, d, pst, pin, tm, msg)).
Proof.
  intros.
  unfold Channel_srckport_Queue in *.
  destruct H; [left;splits|right]; simpljoin1; auto.
  exists x; splits; eauto.
  assert (x <> dstkportp \/ x = dstkportp) by tauto.
  destruct H7.
  {
    unfold nodup_dport in H2.
    specialize (H2 _ _ H7).
    unfold port_coreNum, port_id, tid in H0, H5, H2.
    rewrite H5, H0 in H2.
    exists x0 x1 x2 x3 x4; exists x5 x6 x7 x8; splits; eauto.
    rewrite <- H6.
    apply map_tactics.neq_set_get; auto.
  }
  subst x.
  unfold port_coreNum, port_id, tid in H5, H0.
  rewrite H5 in H0; inverts H0.
  unfold port_coreNum, port_id, tid in H1, H6.
  rewrite H1 in H6; inverts H6.
  destruct H3; simpljoin1.
  inverts H0.
  exists pid dstportp dstkpst x3 x4; exists pin tm x1 x2; splits; eauto.
  eapply set_a_get_a.
Qed.

Lemma RLH_Channel_upd_dportls1:
  forall chanpl chanl chandstkportll otherppl chanls kportls dportls1 dportls2
        dstportp dstkportp pid chanp pcn dstkpst pd d pst dstpin dstpout pm pin tm msg,
    RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1 dportls2 ->
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls1 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, pm) ->
    nodup_dport kportls ->
    (exists u v, pm = SamplePort u /\ msg = SamplePort v) \/
     (exists u v x y, pm = QueuePort u v /\ msg = QueuePort x y) ->
    RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls
    (set dportls1 dstportp (pcn, pd, pid, d, pst, pin, tm, msg)) dportls2.
Proof.
  induction chanpl; destruct chanl; destruct chandstkportll; simpl; intros; tryfalse; auto; simpljoin1.
  destruct H; [left;splits|right]; simpljoin1; eauto.
  do 3 eexists; splits; eauto.
  unfold ChannelNode_P in *; simpljoin1; splits; eauto.
  unfold Channel_type_P in *. destruct x0. destruct p. destruct p.
  destruct c; simpljoin1; eauto.
  { 
    splits; eauto.
    destruct H9; [left|right]; simpljoin1; splits; eauto.
    { eapply Channel_dstkport_Sample_IncoreC_upd_dportls1; eauto. }
    { eapply Channel_srckport_Sample_upd_dportls1; eauto. }
    { eapply Channel_dstkport_Queue_IncoreC_upd_dportls1; eauto. }
    { eapply Channel_srckport_Queue_upd_dportls1; eauto. }
  }
  splits; eauto.
  destruct H10; [left|right]; simpljoin1; splits; eauto.
  { eapply Channel_srckport_Sample_upd_dportls1; eauto. }
  eapply Channel_srckport_Queue_upd_dportls1; eauto.
Qed.

Lemma RLH_Channel_upd_dportls2_Sample:
  forall chanpl chanl chandstkportll otherppl chanls kportls dportls1 dportls2
        dstportp dstkportp pid chanp pcn dstkpst pd d pst dstpin dstpout pm pin tm msg,
    RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1 dportls2 ->
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls2 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, SamplePort pm) ->
    nodup_dport kportls ->
    RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1
    (set dportls2 dstportp (pcn, pd, pid, d, pst, pin, tm, SamplePort msg)).
Proof.
  induction chanpl; destruct chanl; destruct chandstkportll; simpl; intros; tryfalse; auto; simpljoin1.
  destruct H; [left;splits|right]; simpljoin1; eauto.
  do 3 eexists; splits; eauto.
  unfold ChannelNode_P in *; simpljoin1; splits; eauto.
  unfold Channel_type_P in *. destruct x0. destruct p. destruct p.
  destruct c; simpljoin1; eauto.
  splits; eauto.
  destruct H9; [left|right]; simpljoin1; splits; eauto.
  { eapply Channel_dstkport_Sample_OutcoreC_upd_dportls2_Sample; eauto. }
  eapply Channel_dstkport_Queue_OutcoreC_upd_dportls2_Sample; eauto.
Qed.

Lemma Channel_dstkport_Queue_OutcoreC_upd_dportls2_Queue:
  forall dstkportl otherppl chanptr kportls dportls2 dstportp dstkportp pid chanp pcn dstkpst pd pst d dstpin dstpout sz pm msg,
  Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportl kportls dportls2 ->
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls2 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, QueuePort sz pm) ->
    nodup_dport kportls ->
    Channel_dstkport_Queue_OutcoreC otherppl chanptr dstkportl kportls
      (set dportls2 dstportp (pcn, pd, pid, d, pst, dstpin, dstpout , QueuePort sz msg)).
Proof.
  induction dstkportl; simpl; intros; auto; simpljoin1; splits; eauto.
  assert (a <> dstkportp \/ a = dstkportp) by tauto.
  destruct H7.
  {
    unfold nodup_dport in H2.
    specialize (H2 _ _ H7).
    unfold port_coreNum, port_id, tid in H0, H, H2.
    rewrite H, H0 in H2.
    exists x x0 x1 x2 x3 x4; exists x5 x6 x7 x8 x9; splits; eauto.
    rewrite <- H4.
    apply map_tactics.neq_set_get; auto.
  }
  subst a.
  unfold port_coreNum, port_id, tid in H, H0.
  rewrite H in H0; inverts H0.
  unfold port_coreNum, port_id, tid in H1, H4.
  rewrite H1 in H4; inverts H4.
  do 11 eexists; splits; eauto.
  eapply set_a_get_a.
Qed.


Lemma Channel_dstkport_Sample_OutcoreC_upd_dportls2_Queue:
  forall dstkportl otherppl chanptr kportls dportls2 dstportp dstkportp pid chanp pcn dstkpst pd pst d dstpin dstpout sz pm  msg,
  Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportl kportls dportls2 ->
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls2 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, QueuePort sz pm) ->
    nodup_dport kportls ->
    Channel_dstkport_Sample_OutcoreC otherppl chanptr dstkportl kportls
      (set dportls2 dstportp (pcn, pd, pid, d, pst, dstpin, dstpout, QueuePort sz msg)).
Proof.
  induction dstkportl; simpl; intros; auto; simpljoin1; splits; eauto.
  assert (a <> dstkportp \/ a = dstkportp) by tauto.
  destruct H7.
  {
    unfold nodup_dport in H2.
    specialize (H2 _ _ H7).
    unfold port_coreNum, port_id, tid in H0, H, H2.
    rewrite H, H0 in H2.
    exists x x0 x1 x2 x3 x4; exists x5 x6 x7 x8; splits; eauto.
    rewrite <- H4.
    apply map_tactics.neq_set_get; auto.
  }
  subst a.
  unfold port_coreNum, port_id, tid in H, H0.
  rewrite H in H0; inverts H0.
  unfold port_coreNum, port_id, tid in H1, H4.
  rewrite H1 in H4; inverts H4.
Qed.


Lemma RLH_Channel_upd_dportls2_Queue:
  forall chanpl chanl chandstkportll otherppl chanls kportls dportls1 dportls2
        dstportp dstkportp pid chanp pcn dstkpst pd d pst dstpin dstpout sz pm pm',
    RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1 dportls2 ->
    get kportls dstkportp = Some (pid, Some dstportp, chanp, pcn, dstkpst) ->
    get dportls2 dstportp = Some (pcn, pd, pid, d, pst, dstpin, dstpout, QueuePort sz pm) ->
    nodup_dport kportls ->
    RLH_Channel otherppl chanpl chanl chandstkportll chanls kportls dportls1
    (set dportls2 dstportp (pcn, pd, pid, d, pst, dstpin, dstpout, QueuePort sz pm')).
Proof.
  induction chanpl; destruct chanl; destruct chandstkportll; simpl; intros; tryfalse; auto; simpljoin1.
  destruct H; [left;splits|right]; simpljoin1; eauto.
  do 3 eexists; splits; eauto.
  unfold ChannelNode_P in *; simpljoin1; splits; eauto.
  unfold Channel_type_P in *. destruct x0. destruct p. destruct p.
  destruct c; simpljoin1; eauto.
  splits; eauto.
  destruct H9; [left|right]; simpljoin1; splits; eauto.
  { eapply Channel_dstkport_Sample_OutcoreC_upd_dportls2_Queue; eauto. }
  eapply Channel_dstkport_Queue_OutcoreC_upd_dportls2_Queue; eauto.
Qed.

Lemma R_Kernelport_DomainPort_upd:
  forall dportl1 ndstport dportl2 dpptrl1 dstportp dpptrl2 kportpl kportl dportupd,
  R_Kernelport_DomainPort kportpl kportl (dportl1 ++ ndstport :: dportl2) (dpptrl1 ++ dstportp :: dpptrl2) ->
  length dportl1 = length dpptrl1 ->
  struct_type_vallist_match' OS_Port_Seg_dls ndstport ->
  OS_Port_V_portID dportupd = OS_Port_V_portID ndstport ->
  OS_Port_V_coreNum dportupd = OS_Port_V_coreNum ndstport ->
  R_Kernelport_DomainPort kportpl kportl
  (dportl1 ++ dportupd :: dportl2) (dpptrl1 ++ dstportp :: dpptrl2).
Proof.
  induction dportl1; destruct dpptrl1; simpl; intros; tryfalse; simpljoin1.
  {
    exists x x0 x1; splits; eauto.
    rewrite H2; apply H.
    rewrite H3; apply H9.
  }
  exists x x0 x1; splits; eauto.
Qed.

Lemma RLH_Domainportl_upd_Sample:
  forall dportl1 ndstport dportl2 dpptrl1 dstportp dpptrl2 dportmsgll1 v'0 dportmsgll2 dportls1 headptr
         pd pid d pst dstpin dstpout pm pin tm ori_msg_vl upd,
  RL_PortPtrList headptr (dportl1 ++ ndstport :: dportl2)
        (dpptrl1 ++ dstportp :: dpptrl2) ->
  RLH_Domainportl headptr (dportl1 ++ ndstport :: dportl2)
        (dportmsgll1 ++ (v'0 :: nil) :: dportmsgll2) dportls1 ->
  length dportmsgll1 = length dpptrl1 ->
  length dportl1 = length dpptrl1 ->
  get dportls1 dstportp =
      Some
        (Z.to_nat DNUM, pd, pid, d, pst, dstpin,
        dstpout, SamplePort pm) ->
  DomainportNode_P ndstport
        (Z.to_nat DNUM, pd, pid, d, pst, dstpin,
        dstpout, SamplePort pm) (v'0 :: nil) ->
  OS_Port_V_coreNum upd = OS_Port_V_coreNum ndstport ->
  OS_Port_V_domain upd = OS_Port_V_domain ndstport ->
  OS_Port_V_portID upd = OS_Port_V_portID ndstport ->
  OS_Port_V_status upd = OS_Port_V_status ndstport ->
  OS_Port_V_msgInTick upd = Some (Vint32 pin) ->
  OS_Port_V_msgOutTick upd = Some (Vint32 tm) ->
  OS_Port_V_direction upd = OS_Port_V_direction ndstport ->
  OS_Port_V_OSEventPtrPort upd = OS_Port_V_OSEventPtrPort ndstport ->
  OS_Port_V_mode upd = OS_Port_V_mode ndstport ->
  OS_Port_V_nextPort upd = OS_Port_V_nextPort ndstport ->
  RLH_Domainportl headptr
  (dportl1 ++ upd :: dportl2)
  (dportmsgll1 ++ (ori_msg_vl :: nil) :: dportmsgll2)
  (set dportls1 dstportp
     (Z.to_nat DNUM, pd, pid, d, pst,
     Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
     SamplePort (Some ori_msg_vl))).
Proof.
  induction dportl1.
  { destruct dpptrl1; destruct dportmsgll1; simpl; intros; tryfalse; simpljoin1.
    inverts H0.
    rewrite H17 in H19; inverts H19.
    exists x (Z.to_nat DNUM, pd, pid, d, pst,
    Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
    SamplePort (Some ori_msg_vl)) x1; splits; eauto.
    { eapply join_sig_set; eauto. }
    { unfold DomainportNode_P in *; simpljoin1; splits; eauto.
      { unfold Domainport_nat_P in *; simpljoin1.
        do 5 eexists; splits; eauto.
        { rewrite H5; auto. }
        { rewrite H6; auto. }
        { rewrite H7; auto. }
        splits; eauto.
        { rewrite H8; auto. } }
      { unfold Domainport_direction_P in *; simpljoin1.
        destruct d; rewrite H11; auto.
        rewrite H12; auto. }
      { unfold Domainport_Portt_P in *; simpljoin1; eexists; splits; eauto.
        rewrite H13; auto. } }
    exists x3; splits; eauto.
    rewrite H14; auto. }
  intros; destruct dpptrl1; destruct dportmsgll1; tryfalse.
  assert (a0 = dstportp \/ a0 <> dstportp) by tauto.
  destruct H15.
  { subst a0.
    assert (nth_error ((dstportp :: dpptrl1) ++ dstportp :: dpptrl2) 0%nat = Some dstportp).
    { simpl; auto. }
    assert (nth_error ((dstportp :: dpptrl1) ++ dstportp :: dpptrl2) (S (length dpptrl1)) = Some dstportp).
    { simpl.
      erewrite nth_error_app2; eauto.
      assert ((length dpptrl1 - length dpptrl1)%nat = 0%nat) by lia.
      rewrite H16; simpl; auto. }
    pose proof dpptrl_not_same_elements _ _ _ _ _ _ _ _ H H0 H15 H16.
    lia. }
  simpl in *; simpljoin1.
  rewrite H18 in H20; inverts H20.
  inverts H0.
  exists x x0 (set x1 dstportp
        (Z.to_nat DNUM, pd, pid, d, pst,
        Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
        SamplePort (Some ori_msg_vl))); splits; eauto.
  { eapply join_comm.
    eapply join_comm in H16.
    eapply join_set_set; eauto.
    instantiate (1:=(Z.to_nat DNUM, pd, pid, d, pst, dstpin,
    dstpout, SamplePort pm)).
    unfold port_intick, port_outick in *; rewrite <- H3.
    assert (get dportls1 dstportp = get x1 dstportp); auto.
    eapply map_join_get_none.
    { apply join_comm; eauto. }
    apply get_a_sig_a'; auto. }
  exists x3; splits; eauto.
  eapply IHdportl1; eauto.
  unfold port_intick, port_outick in *; rewrite <- H3.
  assert (get dportls1 dstportp = get x1 dstportp); auto.
  eapply map_join_get_none; eauto.
  apply get_a_sig_a'; auto.
Qed.

Lemma RLH_Domainportl_upd_Queue:
  forall dportl1 ndstport dportl2 dpptrl1 dstportp dpptrl2 dportmsgll1 v'0 dportmsgll2 dportls1 headptr
         pd pid d pst dstpin dstpout pm pin tm ori_msg_vl upd sz,
  RL_PortPtrList headptr (dportl1 ++ ndstport :: dportl2)
        (dpptrl1 ++ dstportp :: dpptrl2) ->
  RLH_Domainportl headptr (dportl1 ++ ndstport :: dportl2)
        (dportmsgll1 ++ v'0 :: dportmsgll2) dportls1 ->
  length dportmsgll1 = length dpptrl1 ->
  length dportl1 = length dpptrl1 ->
  get dportls1 dstportp =
      Some
        (Z.to_nat DNUM, pd, pid, d, pst, dstpin,
        dstpout, QueuePort sz pm) ->
  DomainportNode_P ndstport
        (Z.to_nat DNUM, pd, pid, d, pst, dstpin,
        dstpout, QueuePort sz pm) v'0 ->
  OS_Port_V_coreNum upd = OS_Port_V_coreNum ndstport ->
  OS_Port_V_domain upd = OS_Port_V_domain ndstport ->
  OS_Port_V_portID upd = OS_Port_V_portID ndstport ->
  OS_Port_V_status upd = OS_Port_V_status ndstport ->
  OS_Port_V_msgInTick upd = Some (Vint32 pin) ->
  OS_Port_V_msgOutTick upd = Some (Vint32 tm) ->
  OS_Port_V_direction upd = OS_Port_V_direction ndstport ->
  OS_Port_V_OSEventPtrPort upd = OS_Port_V_OSEventPtrPort ndstport ->
  OS_Port_V_mode upd = OS_Port_V_mode ndstport ->
  OS_Port_V_nextPort upd = OS_Port_V_nextPort ndstport ->
  OS_Port_V_OSQSize upd = OS_Port_V_OSQSize ndstport ->
  RLH_Domainportl headptr
  (dportl1 ++ upd :: dportl2)
  (dportmsgll1 ++ ori_msg_vl :: dportmsgll2)
  (set dportls1 dstportp
     (Z.to_nat DNUM, pd, pid, d, pst,
     Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
     QueuePort sz ori_msg_vl)).
Proof.
  induction dportl1.
  { destruct dpptrl1; destruct dportmsgll1; simpl; intros; tryfalse; simpljoin1.
    inverts H0.
    rewrite H18 in H20; inverts H20.
    exists x (Z.to_nat DNUM, pd, pid, d, pst,
    Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
    QueuePort sz ori_msg_vl) x1; splits; eauto.
    { eapply join_sig_set; eauto. }
    { unfold DomainportNode_P in *; simpljoin1; splits; eauto.
      { unfold Domainport_nat_P in *; simpljoin1.
        do 5 eexists; splits; eauto.
        { rewrite H5; auto. }
        { rewrite H6; auto. }
        { rewrite H7; auto. }
        splits; eauto.
        { rewrite H8; auto. } }
      { unfold Domainport_direction_P in *; simpljoin1.
        destruct d; rewrite H11; auto.
        rewrite H12; auto. }
      { unfold Domainport_Portt_P in *; simpljoin1; splits; eauto.
        rewrite H15; auto.
        rewrite H13; auto. } }
    exists x3; splits; eauto.
    rewrite H14; auto. }
  intros; destruct dpptrl1; destruct dportmsgll1; tryfalse.
  assert (a0 = dstportp \/ a0 <> dstportp) by tauto.
  destruct H16.
  { subst a0.
    assert (nth_error ((dstportp :: dpptrl1) ++ dstportp :: dpptrl2) 0%nat = Some dstportp).
    { simpl; auto. }
    assert (nth_error ((dstportp :: dpptrl1) ++ dstportp :: dpptrl2) (S (length dpptrl1)) = Some dstportp).
    { simpl.
      erewrite nth_error_app2; eauto.
      assert ((length dpptrl1 - length dpptrl1)%nat = 0%nat) by lia.
      rewrite H17; simpl; auto. }
    pose proof dpptrl_not_same_elements _ _ _ _ _ _ _ _ H H0 H16 H17.
    lia. }
  simpl in *; simpljoin1.
  rewrite H19 in H21; inverts H21.
  inverts H0.
  exists x x0 (set x1 dstportp
        (Z.to_nat DNUM, pd, pid, d, pst,
        Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
        QueuePort sz ori_msg_vl)); splits; eauto.
  { eapply join_comm.
    eapply join_comm in H17.
    eapply join_set_set; eauto.
    instantiate (1:=(Z.to_nat DNUM, pd, pid, d, pst, dstpin,
    dstpout, QueuePort sz pm)).
    unfold port_intick, port_outick in *; rewrite <- H3.
    assert (get dportls1 dstportp = get x1 dstportp); auto.
    eapply map_join_get_none.
    { apply join_comm; eauto. }
    apply get_a_sig_a'; auto. }
  exists x3; splits; eauto.
  eapply IHdportl1; eauto.
  unfold port_intick, port_outick in *; rewrite <- H3.
  assert (get dportls1 dstportp = get x1 dstportp); auto.
  eapply map_join_get_none; eauto.
  apply get_a_sig_a'; auto.
Qed.

Lemma RLH_OtherPortPtrList_upd_Sample:
  forall otherppl1 dstportp otherppl2 otherpl1 ndstport pin tm otherpl2 
        ori_msg_vl othermsgll1 othermsgll2 dportls2 pcn pd pid pst dstpin
        dstpout pm v'0 upd d,
  RLH_OtherPortPtrList (otherppl1 ++ dstportp :: otherppl2)
  (otherpl1 ++ ndstport :: otherpl2)
  (othermsgll1 ++ (v'0 :: nil) :: othermsgll2) dportls2 ->
  length othermsgll1 = length otherppl1 ->
  length otherpl1 = length otherppl1 ->
  get dportls2 dstportp = Some
    (pcn, pd, pid, d, pst, dstpin, dstpout, SamplePort pm) ->
  OtherPortNode_P ndstport
  (pcn, pd, pid, d, pst, dstpin, dstpout,
  SamplePort pm) (v'0 :: nil) ->
  OS_Port_V_coreNum upd = OS_Port_V_coreNum ndstport ->
  OS_Port_V_domain upd = OS_Port_V_domain ndstport ->
  OS_Port_V_portID upd = OS_Port_V_portID ndstport ->
  OS_Port_V_status upd = OS_Port_V_status ndstport ->
  OS_Port_V_msgInTick upd = Some (Vint32 pin) ->
  OS_Port_V_msgOutTick upd = Some (Vint32 tm) ->
  OS_Port_V_direction upd = OS_Port_V_direction ndstport ->
  OS_Port_V_OSEventPtrPort upd = OS_Port_V_OSEventPtrPort ndstport ->
  OS_Port_V_mode upd = OS_Port_V_mode ndstport ->
  OS_Port_V_nextPort upd = OS_Port_V_nextPort ndstport ->
  RLH_OtherPortPtrList (otherppl1 ++ dstportp :: otherppl2)
  (otherpl1 ++ upd :: otherpl2)
  (othermsgll1 ++ (ori_msg_vl :: nil) :: othermsgll2)
  (set dportls2 dstportp
    (pcn, pd, pid, d, pst, Z.to_nat (Int.unsigned pin),
    Z.to_nat (Int.unsigned tm), SamplePort (Some ori_msg_vl))).
Proof.
  induction otherppl1.
  { destruct otherpl1; destruct othermsgll1; simpl; intros; tryfalse; simpljoin1.
    exists (pcn, pd, pid, d, pst,
    Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
    SamplePort (Some ori_msg_vl)) x0; splits; eauto.
    { eapply join_sig_set; eauto. }
    unfold OtherPortNode_P in *; simpljoin1; splits; eauto.
    { unfold OtherPort_nat_P in *; simpljoin1; do 6 eexists; splits; eauto.
      { rewrite H4; auto. }
      { rewrite H5; auto. }
      { rewrite H6; auto. }
      splits; eauto.
      rewrite H7; auto. }
    { unfold OtherPort_direction_P in *; simpljoin1.
      destruct d; rewrite H10; auto.
      rewrite H11; auto. }
    { unfold OtherPort_Portt_P in *; simpljoin1; eexists; splits; eauto.
      rewrite H12; auto. } }
  intros; destruct otherpl1; destruct othermsgll1; tryfalse.
  assert (a = dstportp \/ a <> dstportp) by tauto.
  destruct H14.
  { subst a.
    assert (nth_error ((dstportp :: otherppl1) ++ dstportp :: otherppl2) 0%nat = Some dstportp).
    { simpl; auto. }
    assert (nth_error ((dstportp :: otherppl1) ++ dstportp :: otherppl2) (S (length otherppl1)) = Some dstportp).
    { simpl.
      erewrite nth_error_app2; eauto.
      assert ((length otherppl1 - length otherppl1)%nat = 0%nat) by lia.
      rewrite H15; simpl; auto. }
    pose proof otherppl_not_same_elements _ _ _ _ _ _ _ H H14 H15.
    lia. }
  simpl in *; simpljoin1.
  exists x (set x0 dstportp
            (pcn, pd, pid, d, pst,
            Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
            SamplePort (Some ori_msg_vl))); splits; eauto.
  { eapply join_comm.
    eapply join_comm in H.
    eapply join_set_set; eauto.
    instantiate (1:=(pcn, pd, pid, d, pst, dstpin, dstpout, SamplePort pm)).
    unfold port_intick, port_outick in *; rewrite <- H2.
    assert (get dportls2 dstportp = get x0 dstportp); auto.
    eapply map_join_get_none.
    { apply join_comm; eauto. }
    apply get_a_sig_a'; auto. }
  eapply IHotherppl1; eauto.
  unfold port_intick, port_outick in *; rewrite <- H2.
  assert (get dportls2 dstportp = get x0 dstportp); auto.
  eapply map_join_get_none; eauto.
  apply get_a_sig_a'; auto.
Qed.


Lemma RLH_OtherPortPtrList_upd_Queue:
  forall otherppl1 dstportp otherppl2 otherpl1 dstportmsgl otherpl2 
        ori_msg_vl othermsgll1 othermsgll2 dportls2 pcn pd pid pst dstpin
        dstpout sz pm dstport d qentries newpin,
  RLH_OtherPortPtrList (otherppl1 ++ dstportp :: otherppl2)
  (otherpl1 ++ dstport :: otherpl2)
  (othermsgll1 ++ dstportmsgl :: othermsgll2) dportls2 ->
  OS_Port_V_OSQEntries dstport = Some (Vint32 qentries) ->
  length othermsgll1 = length otherppl1 ->
  length otherpl1 = length otherppl1 ->
  get dportls2 dstportp = Some
    (pcn, pd, pid, d, pst, dstpin, dstpout, QueuePort sz pm) ->
  OtherPortNode_P dstport
  (pcn, pd, pid, d, pst, dstpin, dstpout,
  QueuePort sz pm) dstportmsgl ->
  RLH_OtherPortPtrList (otherppl1 ++ dstportp :: otherppl2)
  (otherpl1 ++ update_nth_val 17%nat (update_nth_val 14%nat dstport 
  (Vptr newpin)) (Vint32 (qentries +ᵢ  $ 1)) :: otherpl2)
  (othermsgll1 ++ (dstportmsgl ++ ori_msg_vl :: nil) :: othermsgll2)
  (set dportls2 dstportp
    (pcn, pd, pid, d, pst, dstpin,
    dstpout, QueuePort sz (pm++ori_msg_vl::nil))).
Proof.
  induction otherppl1.
  { destruct otherpl1; destruct othermsgll1; simpl; intros; tryfalse; simpljoin1.
    exists (pcn, pd, pid, d, pst,
    dstpin, dstpout,
    QueuePort sz (pm++ori_msg_vl::nil)) x0; splits; eauto.
    { eapply join_sig_set; eauto. }
    unfold OtherPortNode_P in *; simpljoin1; splits; eauto.
    { unfold OtherPort_nat_P in *; simpljoin1; do 6 eexists; splits; eauto.
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
      splits; eauto.
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. } }
    { unfold OtherPort_direction_P in *; simpljoin1.
      destruct d.
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
      { destruct H2; split.
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
        destruct next.
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. } } }
    { unfold OtherPort_Portt_P in *; simpljoin1. splits; eauto.
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
      { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. } } }
  intros; destruct otherpl1; destruct othermsgll1; tryfalse.
  assert (a = dstportp \/ a <> dstportp) by tauto.
  destruct H5.
  { subst a.
    assert (nth_error ((dstportp :: otherppl1) ++ dstportp :: otherppl2) 0%nat = Some dstportp).
    { simpl; auto. }
    assert (nth_error ((dstportp :: otherppl1) ++ dstportp :: otherppl2) (S (length otherppl1)) = Some dstportp).
    { simpl.
      erewrite nth_error_app2; eauto.
      assert ((length otherppl1 - length otherppl1)%nat = 0%nat) by lia.
      rewrite H6; simpl; auto. }
    lets Hnew: otherppl_not_same_elements H H5 H6.
    lia. }
  simpl in *; simpljoin1.
  exists x (set x0 dstportp
            (pcn, pd, pid, d, pst,
            dstpin, dstpout,
            QueuePort sz (pm ++ ori_msg_vl :: nil))); splits; eauto.
  { eapply join_comm.
    eapply join_comm in H.
    eapply join_set_set; eauto.
    instantiate (1:=(pcn, pd, pid, d, pst, dstpin, dstpout, QueuePort sz pm)).
    erewrite <- map_join_get_none.
    eauto. apply join_comm; eauto.
    apply get_a_sig_a'; auto. }
  eapply IHotherppl1; eauto.
  erewrite <- map_join_get_none.
  eauto. eauto.
  apply get_a_sig_a'; auto.
Qed.

Lemma RLH_Domainportl_upd_Queue':
  forall dportl1 dstport dportl2 dpptrl1 dstportp dpptrl2 dportmsgll1 v'0 dportmsgll2 dportls1 headptr
         pd pid d pst dstpin dstpout pm ori_msg_vl sz qentries newpin,
  RL_PortPtrList headptr (dportl1 ++ dstport :: dportl2)
        (dpptrl1 ++ dstportp :: dpptrl2) ->
  RLH_Domainportl headptr (dportl1 ++ dstport :: dportl2)
        (dportmsgll1 ++ v'0 :: dportmsgll2) dportls1 ->
  length dportmsgll1 = length dpptrl1 ->
  length dportl1 = length dpptrl1 ->
  get dportls1 dstportp =
      Some
        (Z.to_nat DNUM, pd, pid, d, pst, dstpin,
        dstpout, QueuePort sz pm) ->
  DomainportNode_P dstport 
        (Z.to_nat DNUM, pd, pid, d, pst, dstpin,
        dstpout, QueuePort sz pm) v'0 ->
  RLH_Domainportl headptr
  (dportl1 ++ (update_nth_val 17%nat (update_nth_val 14%nat dstport newpin) (Vint32 (qentries +ᵢ  $ 1))) :: dportl2)
  (dportmsgll1 ++ (v'0++ori_msg_vl::nil) :: dportmsgll2)
  (set dportls1 dstportp
     (Z.to_nat DNUM, pd, pid, d, pst,
     dstpin, dstpout,
     QueuePort sz (pm++ori_msg_vl::nil))).
Proof.
  induction dportl1.
  { destruct dpptrl1; destruct dportmsgll1; simpl; intros; tryfalse; simpljoin1.
    inverts H0.
    rewrite H7 in H9; inverts H9.
    exists x (Z.to_nat DNUM, pd, pid, d, pst,
    dstpin, dstpout,
    QueuePort sz (pm++ori_msg_vl::nil)) x1; splits; eauto.
    { eapply join_sig_set; eauto. }
    { unfold DomainportNode_P in *; simpljoin1; splits; eauto.
      { unfold Domainport_nat_P in *; simpljoin1.
        do 5 eexists; splits; eauto.
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. } 
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
        splits; eauto.
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. } }
      { unfold Domainport_direction_P in *; simpljoin1.
        destruct d. 
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
        { destruct H0; split.
          { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
          destruct next.
          { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
          { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. } } }
      { unfold Domainport_Portt_P in *; simpljoin1; splits; eauto.
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
        { eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. } } }
    exists x3; splits; eauto.
    eapply nth_upd_neqrev. lia. eapply nth_upd_neqrev. lia. auto. }
  intros; destruct dpptrl1; destruct dportmsgll1; tryfalse.
  assert (a0 = dstportp \/ a0 <> dstportp) by tauto.
  destruct H5.
  { subst a0.
    assert (nth_error ((dstportp :: dpptrl1) ++ dstportp :: dpptrl2) 0%nat = Some dstportp).
    { simpl; auto. }
    assert (nth_error ((dstportp :: dpptrl1) ++ dstportp :: dpptrl2) (S (length dpptrl1)) = Some dstportp).
    { simpl.
      erewrite nth_error_app2; eauto.
      assert ((length dpptrl1 - length dpptrl1)%nat = 0%nat) by lia.
      rewrite H6; simpl; auto. }
    lets Hnew: dpptrl_not_same_elements H H0 H5 H6.
    lia. }
  simpl in *; simpljoin1.
  rewrite H8 in H10; inverts H10.
  inverts H0.
  exists x x0 (set x1 dstportp
        (Z.to_nat DNUM, pd, pid, d, pst,
        dstpin, dstpout,
        QueuePort sz (pm++ori_msg_vl::nil))); splits; eauto.
  { eapply join_comm.
    eapply join_comm in H6.
    eapply join_set_set; eauto.
    erewrite <- map_join_get_none.
    eauto. apply join_comm; eauto.
    apply get_a_sig_a'; auto. }
  exists x3; splits; eauto.
  eapply IHdportl1; eauto.
  erewrite <- map_join_get_none.
  eauto. eauto.
  apply get_a_sig_a'; auto.
Qed.

Lemma tcb_linked_list_same_next_set_node: forall l t p vl vl' v rtbl tcbls,
  TCBList_P v l rtbl tcbls ->
  tcblist_get (Vptr t) p l = Some vl ->
  same_prev_next vl vl' ->
  tcb_linked_list_same_next l (set_node (Vptr t) vl' p l).
Proof.
  induction l; intros;tryfalse.
  simpl in *. destruct p; try congruence.
  destruct (V_OSTCBNext a) eqn:Ea. splits; auto.
  destruct a; subst. discriminate.
  inverts Ea. 
  simpljoin.
  eapply IHl; eauto.
  discriminate.
  destruct (V_OSTCBNext a) eqn:Ea; try discriminate. splits; auto.
  destruct a; subst. discriminate.
  inverts Ea. simpljoin. eapply IHl; eauto.
  destruct (V_OSTCBNext a) eqn:Ea; try discriminate. splits; auto.
  destruct a; subst. discriminate.
  inverts Ea. simpljoin. eapply IHl; eauto.
  destruct (os_inv.beq_addrval t a0) eqn: Eb.
  - inverts H0. unfold same_prev_next in H1.
    destruct (V_OSTCBNext vl); destruct (V_OSTCBNext vl'); tryfalse.
    splits; auto. tauto.
    simpljoin.
    eapply tcb_linked_list_same_next_self; eauto.
  - destruct (V_OSTCBNext a) eqn:Ea; try discriminate. splits; auto.
    destruct a; subst. discriminate.
    inverts Ea. simpljoin. eapply IHl; eauto.
Qed. 

Lemma RL_PortAttr_upd:
  forall dportl1 dpptrl1 dstportp dpptrl2 ndstport dportl2 upd,
  RL_PortAttr (dpptrl1 ++ dstportp :: dpptrl2) (dportl1 ++ ndstport :: dportl2) ->
  length dportl1 = length dpptrl1 ->
  struct_type_vallist_match' OS_Port_Seg_dls ndstport ->
  OS_Port_V_direction upd = OS_Port_V_direction ndstport ->
  OS_Port_V_mode upd = OS_Port_V_mode ndstport ->
  RL_PortAttr (dpptrl1 ++ dstportp :: dpptrl2) (dportl1 ++ upd :: dportl2).
Proof.
  induction dportl1; destruct dpptrl1; simpl; intros; tryfalse.
  {
    unfold RL_PortAttr in *; simpljoin1; split.
    {
      rewrite ! map_cons in *.
      assert (OS_Port_V_direction' upd = OS_Port_V_direction' ndstport).
      {
        unfold OS_Port_V_direction', OS_Port_V_direction in *.
        rewrite ! nth_val'_and_nth_val.
        rewrite H2; auto.
      }
      rewrite H0; auto.
    }
    {
      rewrite ! map_cons in *.
      assert (OS_Port_V_mode' upd = OS_Port_V_mode' ndstport).
      {
        unfold OS_Port_V_mode', OS_Port_V_mode in *.
        rewrite ! nth_val'_and_nth_val.
        rewrite H3; auto.
      }
      rewrite H0; auto.
    }
  }
  unfold RL_PortAttr in *.
  rewrite ! map_cons in *.
  simpljoin1.
  inversion H; inversion H4.
  assert (map OS_Port_V_direction' (dportl1 ++ upd :: dportl2) =
          map OSPortAttrTblDir (dpptrl1 ++ dstportp :: dpptrl2) /\
          map OS_Port_V_mode' (dportl1 ++ upd :: dportl2) =
          map OSPortAttrTblMode (dpptrl1 ++ dstportp :: dpptrl2)).
  { eapply IHdportl1; eauto. }
  simpljoin1.
  rewrite H7, H9, H5, H10.
  auto.
Qed.

Lemma RL_PortPtrList_upd:
  forall dportl1 ndstport dportl2 headptr dpptrl1 dstportp dpptrl2 upd,
  RL_PortPtrList headptr
  (dportl1 ++ ndstport :: dportl2) (dpptrl1 ++ dstportp :: dpptrl2) ->
  length dportl1 = length dpptrl1 ->
  struct_type_vallist_match' OS_Port_Seg_dls ndstport ->
  OS_Port_V_nextPort upd = OS_Port_V_nextPort ndstport ->
  RL_PortPtrList headptr
  (dportl1 ++ upd :: dportl2) (dpptrl1 ++ dstportp :: dpptrl2).
Proof.
  induction dportl1; destruct dpptrl1; simpl; intros; tryfalse; simpljoin1; eauto.
  split; eauto.
  exists x; split; eauto.
  rewrite H2; auto.
Qed.

Lemma set_dportl_S_n_times:
  forall n dstpptrnl ndstpptrn dstportupdl ndstportupd pl,
  nth_error dstpptrnl n = Some ndstpptrn ->
  nth_error dstportupdl n = Some ndstportupd ->
  (ifun_spec.update_nth vallist ndstpptrn
    (set_dportl_n_times pl n dstpptrnl dstportupdl) ndstportupd) =
  (set_dportl_n_times pl (S n) dstpptrnl dstportupdl).
Proof.
  induction n; destruct dstpptrnl; destruct dstportupdl; cbn; intros; tryfalse.
  { inverts H; inverts H0; auto. }
  erewrite IHn; eauto.
Qed.

Lemma set_dportmsgll_S_n_times:
  forall n dstpptrnl ndstpptrn pl msg,
  nth_error dstpptrnl n = Some ndstpptrn ->
  ifun_spec.update_nth (list vallist) ndstpptrn
  (set_dportmsgll_n_times pl n dstpptrnl msg) msg =
  set_dportmsgll_n_times pl (S n) dstpptrnl msg.
Proof.
  induction n; destruct dstpptrnl; cbn; intros; tryfalse.
  { inverts H; auto. }
  erewrite IHn; eauto.
Qed.

Lemma set_dportls_S_n_times:
  forall n dstportpl ndstportp dp dstportupdhl ndstportupdh,
  nth_error dstportpl n = Some ndstportp ->
  nth_error dstportupdhl n = Some ndstportupdh ->
  set (set_dportls_n_times dp n dstportpl dstportupdhl) ndstportp ndstportupdh =
  (set_dportls_n_times dp (S n) dstportpl dstportupdhl).
Proof.
  induction n; destruct dstportpl; destruct dstportupdhl; cbn; intros; tryfalse.
  { inverts H; inverts H0; auto. }
  erewrite IHn; eauto.
Qed.

Lemma set_dportls_n_times_get_pptr_SourceP:
  forall n dstportpl dstportupdhl dportls pptr p p0 p1 p2 p3 p4 p5,
  (n <= length dstportpl)%nat ->
  (length dstportpl = length dstportupdhl)%nat ->
  (
    forall m ,
      (m < length dstportpl)%nat ->
      exists dstportp dstportupdh p6 p7 p8 p9 p10 p11 p12 p13,
      exists p14 p15 p16 p17 p18 p19 nextdst1 nextdst2,
      nth_error dstportpl m = Some dstportp /\
      nth_error dstportupdhl m = Some dstportupdh /\
      get dportls dstportp = Some (p6, p7, p8, DestinationP nextdst1, p9, p10, p11, p12) /\
      dstportupdh = (p13, p14, p15, DestinationP nextdst2, p16, p17, p18, p19)
  ) ->
  get dportls pptr = Some (p, p0, p1, SourceP, p2, p3, p4, p5) ->
  get (set_dportls_n_times dportls n dstportpl dstportupdhl) pptr
    = Some (p, p0, p1, SourceP, p2, p3, p4, p5).
Proof.
  induction n; destruct dstportpl; destruct dstportupdhl; cbn; intros; tryfalse; try lia; auto.
  eapply IHn; auto.
  lia.
  {
    intros.
    assert ((S m < S (length dstportpl))%nat) by lia.
    pose proof H1 _ H4. simpl in H5; simpljoin1.
    assert ((0%nat < S (length dstportpl))%nat) by lia.
    pose proof H1 _ H8. simpl in H9; simpljoin1.
    inverts H9; inverts H10.
    assert (x = x0 \/ x <> x0) by tauto.
    destruct H9; subst.
    {
      do 18 eexists; splits; eauto.
      eapply set_a_get_a.
    }
    do 18 eexists; splits; eauto.
    erewrite set_a_get_a'; eauto.
  }
  assert ((0%nat < S (length dstportpl))%nat) by lia.
  pose proof H1 _ H3. simpl in H4; simpljoin1.
  inverts H4; inverts H5.
  assert (x = pptr \/ x <> pptr) by tauto.
  destruct H4; subst.
  { unfold tid in H2; rewrite H2 in H6; inverts H6. }
  erewrite set_a_get_a'; eauto.
Qed.

Lemma Int_add_one_Sn: forall n,
  Int.unsigned n < 4294967295 ->
  Z.to_nat(Int.unsigned (n +ᵢ  $ 1)) = S (Z.to_nat(Int.unsigned n)).
Proof.
  intros.
  pose proof Int.unsigned_add_either n ($1). destruct H0.
  rewrite H0. rewrite Int.unsigned_repr. rewrite Z2Nat.inj_add. lia.
  mauto. lia. split. lia. cbv. intros. discriminate.
  rewrite Int.unsigned_repr in H0.
  2: split. 2:lia. 2: cbv. 2: intros; discriminate.
  pose proof Int.unsigned_range (n +ᵢ  $ 1). unfold Int.modulus in H0.
  unfold two_power_nat in H0. simpl in H0. lia.
Qed.

Lemma Int_add_one_Sn': forall n,
  Int.unsigned n < 4294967295 ->
 (Int.unsigned (n +ᵢ  $ 1)) = (Int.unsigned n)+1.
Proof.
  intros.
  pose proof Int.unsigned_add_either n ($1). destruct H0.
  rewrite H0. f_equal. 
  rewrite Int.unsigned_repr in H0.
  2: split. 2:lia. 2: cbv. 2: intros; discriminate.
  pose proof Int.unsigned_range (n +ᵢ  $ 1). unfold Int.modulus in H0.
  unfold two_power_nat in H0. simpl in H0. lia.
Qed.

Lemma Int_add_one_Sn'': forall n,
  0<= n <= 4294967295 ->
  Int.repr (n + 1) = Int.add (Int.repr n) Int.one.
Proof.
  intros.
  rewrite Int.add_unsigned.
  f_equal. rewrite Int.unsigned_one. f_equal.
  rewrite Int.unsigned_repr. auto.
  rewrite max_unsigned_val. auto.
Qed.

Lemma Nodup_nth_err_neq:
  forall [A : Type] (l : list A),
  (forall a b:A,{a=b}+{a<>b})->
  NoDup l ->
  (forall i j x y,
  i<> j ->
  nth_error l i = Some x ->
  nth_error l j = Some y ->
  x <> y).
Proof.
  induction l; intros.
  + rewrite nth_error_nil in H1. discriminate.
  + destruct i; destruct j.
    - simpl in *. inverts H1. inverts H2. lia.
    - simpl in H1. inverts H1. inverts H. simpl in H2.
     apply nth_error_In in H2.
     destruct (X x y). subst. tauto. auto.
    - simpl in H2. inverts H2. inverts H. simpl in H1.
    apply nth_error_In in H1.
    destruct (X x y). subst. tauto. auto.
    - simpl in *. inverts H. jauto.
Qed.

Lemma addrval_Nodup_nth_err_neq:
  forall (l : list addrval),
  NoDup l ->
  (forall i j x y,
  i<> j ->
  nth_error l i = Some x ->
  nth_error l j = Some y ->
  x <> y).
Proof.
  intros. eapply Nodup_nth_err_neq; eauto.
  apply addrval_eq_dec.
Qed.

Lemma receivePortMsg_tcbls_ecbls_trans_true: 
  forall pl1 pl2 tcbls ecbls tcbls' tcbls'',
    receivePortMsg_tcbls_ecbls pl1 ecbls tcbls tcbls' true ->
    receivePortMsg_tcbls_ecbls pl2 ecbls tcbls' tcbls'' true ->
    receivePortMsg_tcbls_ecbls (pl1++pl2) ecbls tcbls tcbls'' true.
Proof.
  inductions pl1; intros.
  simpl in H. simpl; auto.
  inverts H. auto.
  inverts H.
  simpl. econstructor 2; eauto.
  simpl. econstructor 3; eauto.
Qed.

Lemma receivePortMsg_tcbls_ecbls_trans_false: 
  forall pl1 pl2 tcbls ecbls tcbls' tcbls'' b,
    receivePortMsg_tcbls_ecbls pl1 ecbls tcbls tcbls' b ->
    receivePortMsg_tcbls_ecbls pl2 ecbls tcbls' tcbls'' false ->
    receivePortMsg_tcbls_ecbls (pl1++pl2) ecbls tcbls tcbls'' false.
Proof.
  inductions pl1; intros.
  simpl in H. simpl; auto.
  inverts H. auto.
  inverts H.
  simpl. econstructor 2; eauto.
  simpl. econstructor 3; eauto.
  simpl. econstructor 4; eauto.
Qed.

Lemma nth_upd_neqrev':
  forall (vl : vallist) (n m : nat) (x : val),
    n <> m ->
    nth_val n (update_nth_val m vl x) = nth_val n vl.
Proof.
  inductions vl.
  - intros.
  simpl in *.
  auto.
  - intros; simpl in *.
  destruct n.
  simpl.
  destruct m.
  tryfalse.
  simpl ; auto.
  destruct m.
  simpl.
  auto.
  cbn.
  eapply IHvl.
  lia.
Qed.

Lemma nthval'_has_value_ptr : 
  forall l len n t, array_type_vallist_match (Tptr t) l ->
                  length l = len -> 
                  (n < len)%nat ->
                  exists x, nth_val' n l = x /\ true = rule_type_val_match (Tptr t) x.
Proof.
  intro.
  induction l.
  intros.
  simpl in H0.
  rewrite <- H0 in H1.
  inversion H1.

  intros.
  induction n.
  inversion H.
  simpl in H2.
  destruct a; try inversion H2.
  exists Vnull.
  split ; auto.
  exists (Vptr a).
  split; auto.

  simpl nth_val'.
  apply (IHl (pred len)).
  inversion H;  auto.
  simpl in H0.
  lia.
  lia.
Qed.

Lemma RL_PortPtrList_snd:
  forall dportl1 dport dportl2 dpptrl1 pptr dpptrl2 p,
    length dportl1 = length dpptrl1 ->
    RL_PortPtrList p (dportl1 ++ dport :: dportl2) (dpptrl1 ++ pptr :: dpptrl2) ->
    RL_PortPtrList (Vptr pptr) (dport :: dportl2) (pptr :: dpptrl2).
Proof.
  induction dportl1; destruct dpptrl1; simpl; intros; tryfalse.
  { simpljoin1; split; auto. eexists; eauto. }
  simpljoin1.
  assert (length dportl1 = length dpptrl1) by lia.
  specialize (IHdportl1 _ _ _ _ _ _ H0 H2).
  simpl in IHdportl1. auto.
Qed.