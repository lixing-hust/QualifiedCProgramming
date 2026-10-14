Require Import if_assms.
Require Import base_tac.
Require Import ct_pp_lemmas.
Require Import confidentiality_tactics.
Require Import confidentiality_lemmas. 
Require Import if_common_lemmas.
Require Import hasrt_sat_preserve. 
Require Import if_language.
Require Import if_opsem.
Require Import memory.
Require Import mq_apispecs.
Require Import sem_prop_2.
Require Import osspecs.
Require Import properties.
Require Import protect.
Require Import seplog_lemmas.
Require Import spec_aux_defs.
Require Import if_succ_gen.

Set Keyed Unification.

Ltac sinverts H := symmetry in H; inverts H.

Ltac efalse H := false; eapply H; eauto.

Lemma nabt_abt_false:
  forall T t ke ks, 
    nabt (set T t (curs (hapi_code (ABORT)), (ke, ks))) -> False. 
Proof.
  intros.
  specialize (H t (curs (hapi_code (ABORT))) ke ks).
  rewrite set_a_get_a in H.
  apply H; reflexivity.
Qed.

Definition Step1 p : Prop := p.
Lemma step1_lemma : forall (p : Prop), p -> Step1 p. Proof. auto. Qed.
Definition Step2 p : Prop := p.
Lemma step2_lemma : forall (p : Prop), p -> Step2 p. Proof. auto. Qed.
Lemma spec_assume_step_false:
  forall O O' s1' act,
    spec_step get_hprio_d (ASSUME (fun O => False)) O s1' O' act -> False.
Proof. intros. inverts H. auto. Qed.
Lemma spec_assert_step_false:
  forall (O O' : osabst) (v : option val) (act : action),
    spec_step get_hprio_d (ASSERT (fun O => False)) O (END v) O' act -> False.
Proof. intros. inverts H. auto. Qed.
Ltac step S l :=
  match goal with H: S (spec_step _ _ _ _ _ _) |- _ => inverts H end;
  match goal with
    _: nabt (set _ _ (curs (hapi_code (ABORT)), _)) |- _ =>
    efalse nabt_abt_false
  | _: spec_step get_hprio_d (ASSUME (fun _ : osabst => False)) _ _ _ _ |- _ =>
    efalse spec_assume_step_false
  | _: spec_step get_hprio_d (ASSERT (fun _ : osabst => False)) _ (END _) _ _ |- _ =>
    efalse spec_assert_step_false
  | H: ~(exists _, END _ = END _) /\ _ |- _ => destruct H as (H & _); false; apply H; eauto
  | H: _ /\ (ABORT <> ABORT) |- _ => destruct H as (_ & H); congruence
  | _ => idtac
  end;
  match goal with
  | H: spec_step _ _ _ _ _ _ |- _ => apply l in H
  | _ => idtac
  end.
Ltac step1 := step Step1 step1_lemma.
Ltac step2 := step Step2 step2_lemma.

Ltac start k :=
  destruct k;
  [
    match goal with
      Hnth1: nth_error (get_all_succs _) _ = Some _, 
      Hnth2: nth_error (get_all_succs _) _ = Some _,
      Hhsat1: head_asrt_sat _ _ _, Hhsat2: head_asrt_sat _ _ _ |- _ => 
        inverts Hnth1; inverts Hnth2; simpl in Hhsat1;
        simpl in Hhsat2
    end
  | ].

Definition bind_all (vl vl1 vl2: list val) (cd1 cd2 : spec_code) : Prop :=
  forall i1 i2 b d, addr_in_dom (b, i1) d = addr_in_dom (b, i2) d.

Lemma vl_equiv_refl: forall sc, vl_equiv sc sc.
Proof.
  intros; unfolds.
  introv Hghv1 Hghv2 Hne1 Hne2.
  rewrite Hghv1 in Hghv2; inverts Hghv2.
  rewrite Hne1 in Hne2; inverts Hne2.
  reflexivity.
Qed.

Lemma skip_Oeq:
  forall vl OO OO' act v, spec_skip_step vl OO act (v, Some OO') -> OO = OO'. 
Proof. intros; unfolds in H; simpljoin; congruence. Qed.

Lemma aar_Oeq:
  forall vl OO OO' act v, asrt_and_ret vl OO act (v, Some OO') -> OO' = OO.
Proof.
  intros.
  destruct H as (_ & _ & _ & _ & _ & [(_ & H) | (_ & H)]); congruence.
Qed.

Lemma aar_veq: 
  forall v1 v2 OO act v OO', 
    asrt_and_ret (v1 :: v2 :: nil) OO act (v, Some OO') -> v1 = v2. 
Proof.
  intros; unfolds in H.
  destruct H as (v3 & v4 & H1 & _ & _ & [(H2 & _) | (_ & H)]); congruence.
Qed.

Lemma rv_ptr_no_null_equiv:
  forall i ptr1 ptr2 O1 O2 pr,
    ptr1 <> Vnull ->
    mqdes_dom_qptr i ptr1 O1 pr ->
    mqdes_dom_qptr i ptr2 O2 pr ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    exists eid ecbs1 ecbs2 ed1 ed2 ws1 ws2,
      ptr1 = Vptr eid /\
      ptr2 = Vptr eid /\
      get O1 absecblsid = Some (absecblist ecbs1) /\
      get O2 absecblsid = Some (absecblist ecbs2) /\
      get ecbs1 eid = Some (ed1, ws1) /\
      get ecbs2 eid = Some (ed2, ws2) /\
      mq_ed_equiv ed1 ed2 O1 O2 /\ tidls_equiv ws1 ws2 O1 O2.
Proof.
  introv Hnn Hmdq1 Hmdq2 Hkmeq.
  destruct Hmdq1 as (Hmid & Hmp1); destruct Hmdq2 as (_ & Hmp2).
  destruct Hmp1 as (mqatts1 & eo1 & wtp1 & qflg1 & mmsg1 & msz1
    & cmsgs1 & sltidxs1 & Hget_qattr_map1 & Hget_qattr1 & [(_ & H) | (p1 & Heo1 & Hptr1)]).
  - congruence.
  - subst.
  destruct Hmp2 as (mqatts2 & eo2 & wtp2 & qflg2 & mmsg2 & msz2
      & cmsgs2 & sltidxs2 & Hget_qattr_map2 & Hget_qattr2& Hptr2).
  destruct Hkmeq as (mqatts1_ & mqatts2_ & Hget_qattr_map1_ & Hget_qattr_map2_ & H).
  l_rew21_inv1 (get O1 absmqattrid); l_rew21_inv1 (get O2 absmqattrid).
  specializes H; eauto.
  destruct H as (_ & H).
  specializes H; eauto.
  destruct H as (eo1_ & eo2_ & wtp & flgs & mms & msz & cms & csltidxs & Hmq1 & Hmq2 & H).
  inverts Hmq1; inverts Hmq2.
  destruct H as [(H & _) | [(H & _) |
    (ecbs1 & ecbs2 & eid & ed1 & ed2 & ws1 & ws2 & H1 & H2 & H)]].
  + congruence.
  + congruence.
  + destruct Hptr2 as [(Heo2 & _) | (p2 & Heo2 & Hptr2)]. 
    * congruence.
    * subst; inverts H1; inverts H2.
      exists eid ecbs1 ecbs2; exists ed1 ed2 ws1 ws2. auto.
Qed.

Lemma mq_equiv_null_false: 
  forall pr i O1 O2 v1 v2, 
    v1 <> Vnull ->
    v2 = Vnull ->
    mqdes_dom_qptr i v1 O1 pr ->
    mqdes_dom_qptr i v2 O2 pr -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    False.
Proof.
  introv Ht Hf Hmdq1 Hmdq2 Hkmeq.
  lets H : rv_ptr_no_null_equiv Ht Hmdq1 Hmdq2 Hkmeq.
  destruct H as (eid & _ & _ & _ & _ & _ & _ & _ & H & _).
  congruence.
Qed.

Lemma qid_unique_lemma:
  forall i ptr1 ptr2 O1 O2 pr,
    ptr1 <> Vnull ->
    mqdes_dom_qptr i ptr1 O1 pr ->
    mqdes_dom_qptr i ptr2 O2 pr ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    exists qid, ptr1 = Vptr qid /\ ptr2 = Vptr qid.
Proof.
  introv Hnn Hmdq1 Hmdq2 Hkmeq.
  lets H : rv_ptr_no_null_equiv Hnn Hmdq1 Hmdq2 Hkmeq.
  destruct H as (eid & _ & _ & _ & _ & _ & _ & H1 & H2 & _).
  exists eid; auto.
Qed.
Ltac qid_unique q :=
  match goal with
    Hkmeq: kernel_mq_equiv _ _ _ |- _ => 
    let H := fresh in lets H : qid_unique_lemma Hkmeq; eauto;
    destruct H as (q & H); destruct H; subst
  end.

Lemma mq_equiv_unfolded:
  forall i qid O1 O2 pr,
    mqdes_dom_qptr i (Vptr qid) O1 pr ->
    mqdes_dom_qptr i (Vptr qid) O2 pr ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    exists ecbs1 ecbs2 ed1 ed2 ws1 ws2,
      get O1 absecblsid = Some (absecblist ecbs1) /\
      get O2 absecblsid = Some (absecblist ecbs2) /\
      get ecbs1 qid = Some (ed1, ws1) /\
      get ecbs2 qid = Some (ed2, ws2) /\
      mq_ed_equiv ed1 ed2 O1 O2 /\ tidls_equiv ws1 ws2 O1 O2.
Proof.
  introv Hmdq1 Hmdq2 Hkmeq.
  assert (Hnn : Vptr qid <> Vnull). { congruence. }
  lets H : rv_ptr_no_null_equiv Hnn Hmdq1 Hmdq2 Hkmeq.
  destruct H as (eid & ecbs1 & ecbs2 & ed1 & ed2 & ws1 & ws2 & _ & H1 & H).
  inverts H1.
  exists ecbs1 ecbs2 ed1 ed2 ws1 ws2; auto.
Qed.

Ltac vl_equiv_subst :=
  match goal with Hvleq: vl_equiv _ _ |- _ => 
  let H := fresh in lets H: vlequiv_veq Hvleq; 
    specialize (H (eq_refl _) (eq_refl _)); subst; tryfalse
  end.

Lemma join_Oeq_lemma: 
  forall (OO Of O O' : osabst), join OO Of O -> join OO Of O' -> O' = O.
Proof. join auto. Qed.
Ltac join_Oeq :=
  match goal with
    H1: join _ _ _, H2: join _ _ _,
    H3: join _ _ _, H4: join _ _ _ |- _ => 
    let Hoeq1 := fresh in lets Hoeq1 : join_Oeq_lemma H1 H2;
    let Hoeq2 := fresh in lets Hoeq2 : join_Oeq_lemma H3 H4; subst
  | _ => idtac
  end.

Lemma rv_equal_end_lemma:
  forall i pr act T1 T2 t1 t2 c1 c2 ke ks1 ks2 cst1' cst2'
  v v1 v2 O1 O2 O1' O2' Of1 Of2 OO1 OO1' OO2 OO2', 
  data_equiv_tskd i cst1' cst2' O1 O2 ->
  join OO1 Of1 O1 ->
  join OO1' Of1 O1' -> 
  join OO2 Of2 O2-> 
  join OO2' Of2 O2'->
  ret_val (v::nil) OO1 act (v1, Some OO1')->
  ret_val (v::nil) OO2 act (v2, Some OO2')->
  code_equiv_tskd i T1 T2 O1 O2 ->
  get T1 t1 = Some (c1, (ke, ks1)) ->
  get T2 t2 = Some (c2, (ke, ks2)) ->
  task_prio_id O1 pr t1 ->
  task_prio_id O2 pr t2 ->
  cont_equiv pr ks1 ks2 O1 O2 ->
  code_equiv_tskd i (set T1 t1 (curs (hapi_code (END v1)), (ke, ks1)))
    (set T2 t2 (curs (hapi_code (END v2)), (ke, ks2))) O1' O2' /\
  data_equiv_tskd i cst1' cst2' O1' O2'. 
Proof.
  introv Hdeqt Hjo1 Hjo2 Hjo1' Hjo2' Hrv1 Hrv2 Hde; intros.
  lets H1_: rv_Oeq Hrv1; lets H2_: rv_Oeq Hrv2; symmetry in H1_; symmetry in H2_. subst.
  join_Oeq.
  split.
  - eapply code_equiv_upd2_preserve'; eauto.
    apply rv_veq in Hrv1; apply rv_veq in Hrv2. subst.
    apply cmd_equiv_end.
  - auto.
Qed.
Ltac rv_equal_end := eapply rv_equal_end_lemma; eauto.

Lemma dct_mid_false :
    forall O1 O2 i,
    (forall td : taskdom, dom_cur_tsk O1 td -> mqidx_in_dom i td = false) ->
    ~ (forall td : taskdom, dom_cur_tsk O2 td -> mqidx_in_dom i td = false) ->
    data_equiv_schd O1 O2 ->
    False.
Proof.
  introv Ht Hf Hdes.
  apply Hf; introv Hdct.
  lets H: data_equiv_schd_dom_equiv Hdes td.
  destruct H as (_ & H); auto.
Qed.

Lemma mqd_in_cdom_holds: 
  forall O idx t pr, 
    ~(forall td : taskdom, dom_cur_tsk O td -> mqidx_in_dom idx td = false) ->
    get O curtid = Some (oscurt t) ->
    task_prio_id O pr t -> 
    mqd_in_dom idx O pr.
Proof.
  introv H Hcurt Htpi. unfolds.
  apply Classical_Pred_Type.not_all_ex_not in H.
  destruct H as (td & H).
  apply Classical_Prop.imply_to_and in H.
  destruct H as ((t_ & pr_ & Hcurt_ & Htpi_ & Hdfp) & Hne).
  l_rew12_inv2 (get O curtid).
  lets H: prio_unique Htpi_ Htpi; subst.
  destruct (mqidx_in_dom idx (dom_for_prio pr)); eauto. 
Qed.

Lemma get_msize_Oeq:
  forall vl OO OO' act v, 
    mqrecv_get_msgsize vl OO act (Some v, Some OO') -> OO' = OO. 
Proof.
  introv H; unfolds in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & [(_ & H) | (_ & H)]); congruence.
Qed.

Lemma mqequiv_get_msize_veq: 
  forall mqd pr act v1 v2 vo1 vo2 O1 O2 Of1 Of2 OO1 OO2, 
    mqrecv_get_msgsize (Vint32 mqd :: v1 :: nil) OO1 act (vo1, Some OO1) ->
    mqrecv_get_msgsize (Vint32 mqd :: v2 :: nil) OO2 act (vo2, Some OO2) ->
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqd_in_dom mqd O1 pr ->
    mqd_in_dom mqd O2 pr ->
    v1 = v2.
Proof.
  introv Hmgm1 Hmgm2 Hjoin1 Hjoin2 Hkmeq Hmid1 Hmid2.
  destruct Hkmeq as (att1 & att2 & Hatt1 & Hatt2 & Hall).
  unfolds in Hmgm1; unfolds in Hmgm2.
  simpljoin.
  match goal with H: (_ :: _ :: nil) = (_ :: _ :: nil) |- _ => inverts H end.
  match goal with H: (_ :: _ :: nil) = (_ :: _ :: nil) |- _ => inverts H end.
  rename x8 into i.
  unfolds in Hmid1.
  assert (Hget': get O1 absmqattrid = Some (absmqattr x10)).
  { eapply join_sem1; eauto. }
  rewrite Hatt1 in Hget'.
  symmetry in Hget'. inverts Hget'.
  assert (Hget': get O2 absmqattrid = Some (absmqattr x1)).
  { eapply join_sem1; eauto. }
  rewrite Hatt2 in Hget'.
  symmetry in Hget'. inverts Hget'.
  lets H_: Hall Hmid2.
  destruct H_ as (_ & H__).
  lets H_ : H__ H6 H2.
  unfold mq_equiv in H_.
  destruct H_ as (eo1 & eo2 & wtp & flgs & mms & msz & cms & csltidxs & Heq1 & Heq2 & _).
  inverts Heq1. inverts Heq2.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
Qed.

Lemma ms_getep_Oeq: 
  forall vl OO OO' act v, mqrecv_get_ecb_ptr vl OO act (v, Some OO') -> OO' = OO. 
Proof.
  intros. unfolds in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ &_ & _ & _ & [(_ & H) | (_ & H)]); congruence.
Qed.

Lemma idm_getep_dom_qptr: 
  forall i0 O v act vo Of O0 O0' pr, 
    mqd_in_dom i0 O pr -> 
    mqrecv_get_ecb_ptr (Vint32 i0 :: v :: nil) O0 act (vo, Some O0') -> 
    join O0 Of O -> 
    mqdes_dom_qptr i0 v O pr. 
Proof.
  introv Hmid Hgp Hjo.
  unfolds in Hgp.
  unfolds in Hmid.
  unfolds.
  split; eauto.
  simpljoin.
  match goal with H: _ :: _ :: _ = _ :: _ :: _ |- _ => inverts H end.
  match goal with H: _ \/ _ |- _ => inverts H3; simpljoin; tryfalse end.
  inverts H2.
  unfolds.
  do 8 eexists.
  splits; eauto.
  eapply join_get_get_l; eauto.
  inverts H.
  - right; auto. 
  - left; auto. 
Qed.

Lemma mqgf_Oeq: 
  forall vl OO OO' act v, mqrecv_get_mqflags vl OO act (v, Some OO') -> OO' = OO. 
Proof.
  intros; unfolds in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ &_ & _ &  _ & [(_ & H) | (_ & H)]); congruence.
Qed.

Lemma mq_equiv_flg_veq:
  forall mqd pr act rv_flag1 rv_flag2 O1 O2 Of1 Of2 OO1 OO2 v1 v2 v1_ v2_,
    mqrecv_get_mqflags (Vint32 mqd :: Vint32 rv_flag1 :: nil) OO1 act (v1, Some OO1) ->
    mqrecv_get_mqflags (Vint32 mqd :: Vint32 rv_flag2 :: nil) OO2 act (v2, Some OO2) -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    mqdes_dom_qptr mqd v1_ O1 pr ->
    mqdes_dom_qptr mqd v2_ O1 pr ->
    Vint32 rv_flag1 = Vint32 rv_flag2. 
Proof.
  introv Hm1 Hm2 Hjo1 Hjo2 Hkme Hd1 Hd2.
  destruct Hd1 as (Hd1 & _). destruct Hd2 as (Hd2 & _).
  unfold kernel_mq_equiv in Hkme.
  destruct Hkme as (att1 & att2 & Hg1 & Hg2 & Hall).
  unfolds in Hm1.
  unfolds in Hm2.
  simpljoin.
  do 2 (match goal with H: _ :: _ :: _ = _ |- _ => inverts H end).
  assert (get O1 absmqattrid = Some (absmqattr x10)).
  { eapply join_sem1; eauto. }
  l_rew21_inv1 (get O1 absmqattrid).
  assert (get O2 absmqattrid = Some (absmqattr x1)).
  { eapply join_sem1; eauto. }  
  l_rew21_inv1 (get O2 absmqattrid).
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  do 4 (match goal with H: _ _ = _ _ |- _ => inverts H end). 
  specializes Hall; eauto.
  destruct Hall as (_ & Hall).
  specializes Hall; eauto.
  unfolds in Hall.
  simpljoin.
Qed.

Lemma cap_equiv_recvcap_equiv: 
  forall i pr rv_flag rv_ptr1 rv_ptr2 O1 O2 t1 t2,
    has_no_cap_recv O1 rv_flag rv_ptr1 ->
    ~ has_no_cap_recv O2 rv_flag rv_ptr2 ->
    cap_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) -> 
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    mqdes_dom_qptr i rv_ptr1 O1 pr ->
    mqdes_dom_qptr i rv_ptr2 O2 pr -> 
    False.
Proof.
  introv Ht Hf Hce Hcurt1 Hcurt2 Htpi1 Htpi2 Hmdq1 Hmdq2.
  apply Hf.
  destruct Hce as (cspc1 & cspc2 & Hget_cspc1 & Hget_cspc2 & H).
  destruct Ht as (t1_ & pr1 & cspc1_ & Hcurt1_ & Htpi1_ & Hget_cspc1_ & H1).
  l_rew12_inv2 (get O1 curtid).
  l_rew12_inv2 (get O1 cspaceid).
  apply2 (task_prio_id O1) (task_prio_id O1) prio_unique.
  specialize (H pr (eq_refl)).
  destruct H as (Hcc & Hoc).
  destruct Hmdq1 as (Hmid & Hmp1); destruct Hmdq2 as (_ & Hmp2).
  specializes Hoc; eauto.
  destruct Hoc as (_ & Hoc).
  specializes Hoc; eauto.
  rewrite Hcc in H1. 
  rewrite Hcc in H1. 
  rewrite Hoc in H1.
  do 3 eexists. splits; eauto.
Qed.

Lemma mq_equiv_noque_false: 
  forall i0 vp1 vp2 v0 O1 O2 pr, 
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    (exists els qid,
        vp1 = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist els) /\
          ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))) ->
    False.
Proof.
  introv Hmd1 Hmd2 Hkme Hex.
  unfolds in Hkme.
  simpljoin.
  unfolds in Hmd1.
  unfolds in Hmd2.
  unfold mq_ptr in *.
  simpljoin.
  l_rew21_inv1 (get O1 absmqattrid).
  l_rew21_inv1 (get O2 absmqattrid). 
  match goal with H: _ /\ Vptr _ = Vnull \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  match goal with H: forall _, _ |- _ => rename H into Hall; specializes Hall; eauto end.
  destruct Hall as (_ & Hall).
  specializes Hall; eauto. 
  unfold mq_equiv in Hall.
  simpljoin.
  match goal with H: _ \/ _ |- _ => destruct H as [Hf | [Hf | H']] end; simpljoin; tryfalse. 
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  do 2 (match goal with H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H end).
  l_rew21_inv1 (get O1 absecblsid). 
  unfold mq_ed_equiv in *.
  simpljoin.
   match goal with H: ~_ |- _ => apply H end.
   do 4 eexists; eauto. 
Qed.

Lemma absmsgq_false:
  forall i qid O1 O2 pr,
    (exists qls qid0,
      Vptr qid = Vptr qid0 /\
      get O1 absecblsid = Some (absecblist qls) /\
      ~ (exists x y pwls wls, get qls qid0 = Some (absmsgq x y pwls, wls))) ->
    ~ (exists qls qid0,
       Vptr qid = Vptr qid0 /\
       get O2 absecblsid = Some (absecblist qls) /\
       ~ (exists x y pwls wls, get qls qid0 = Some (absmsgq x y pwls, wls))) ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqdes_dom_qptr i (Vptr qid) O1 pr ->
    mqdes_dom_qptr i (Vptr qid) O2 pr ->
    False.
Proof.
  introv Ht Hf Hkmeq Hmdq1 Hmdq2.
  apply Hf.
  destruct Ht as (qls1 & qid0 & H & Hget_ecb_map & Hnexists).
  sinverts H.
  lets H: mq_equiv_unfolded Hmdq1 Hmdq2 Hkmeq.
  destruct H as (ecbs1 & ecbs2 & ed1 & _ & ws1 & _ & Hget_ecb_map1 &
    Hget_ecb_map2 & Hget_ecb1 & _ & (ms & mlen & pws1 & _ & Hed1 & _) & _).
  exists ecbs2 qid. splits; eauto.
  introv Hexists; apply Hnexists.
  l_rew12_inv2 (get O1 absecblsid).
  rewrite Hget_ecb1.
  subst. eauto.
Qed.

Lemma absmsgq2_false:
  forall i qid O1 O2 pr,
    (exists qid0 qls msg0 ml n wl,
      Vptr qid = Vptr qid0 /\
      get O1 absecblsid = Some (absecblist qls) /\
      get qls qid0 = Some (absmsgq (msg0 :: ml) n nil, wl)) ->
    ~ (exists qid0 qls msg0 ml n wl,
      Vptr qid = Vptr qid0 /\
      get O2 absecblsid = Some (absecblist qls) /\
      get qls qid0 = Some (absmsgq (msg0 :: ml) n nil, wl)) ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqdes_dom_qptr i (Vptr qid) O1 pr ->
    mqdes_dom_qptr i (Vptr qid) O2 pr ->
    False.
Proof.
  introv Ht Hf Hkmeq Hmdq1 Hmdq2.
  apply Hf.
  destruct Ht as (qid0 & qls1 & msg0 & ml & n & wl & H & Hget_ecb_map & Hget_ecb).
  sinverts H.
  lets H: mq_equiv_unfolded Hmdq1 Hmdq2 Hkmeq.
  destruct H as (ecbs1 & ecbs2 & ed1 & ed2 & ws1 & ws2 & Hget_ecb_map1 &
    Hget_ecb_map2 & Hget_ecb1 & Hget_ecb2 & (ms & mlen & pws1 & pws2 & Hed1 & Hed2 & Hteq) & _).
  subst.
  l_rew12_inv2 (get O1 absecblsid).
  rewrite Hget_ecb1 in Hget_ecb; inverts Hget_ecb.
  destruct Hteq as (Hleq & _).
  symmetry in Hleq. apply length_zero_iff_nil in Hleq. subst.
  do 6 eexists. splits; eauto.
Qed.

Lemma absmsgq3_false:
  forall i qid O1 O2 pr,
    (exists qid0 qls msg0 ml n pwl wl,
      Vptr qid = Vptr qid0 /\
      get O1 absecblsid = Some (absecblist qls) /\
      get qls qid0 = Some (absmsgq (msg0 :: ml) n pwl, wl) /\ pwl <> nil) ->
    ~ (exists qid0 qls msg0 ml n pwl wl,
      Vptr qid = Vptr qid0 /\
      get O2 absecblsid = Some (absecblist qls) /\
      get qls qid0 = Some (absmsgq (msg0 :: ml) n pwl, wl) /\ pwl <> nil) ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqdes_dom_qptr i (Vptr qid) O1 pr ->
    mqdes_dom_qptr i (Vptr qid) O2 pr ->
    False.
Proof.
  introv Ht Hf Hkmeq Hmdq1 Hmdq2.
  apply Hf.
  destruct Ht as (qid0 & qls1 & msg0 & ml & n & pwl & wl & H & Hget_ecb_map & Hget_ecb &Hnn).
  sinverts H.
  lets H: mq_equiv_unfolded Hmdq1 Hmdq2 Hkmeq.
  destruct H as (ecbs1 & ecbs2 & ed1 & ed2 & ws1 & ws2 & Hget_ecb_map1 &
    Hget_ecb_map2 & Hget_ecb1 & Hget_ecb2 & (ms & mlen & pws1 & pws2 & Hed1 & Hed2 & Hteq) & _).
  subst.
  l_rew12_inv2 (get O1 absecblsid).
  rewrite Hget_ecb1 in Hget_ecb; inverts Hget_ecb.
  destruct Hteq as (Hleq & _).
  casetac pws2 (nil: list tid) Ht_ Hf_.
  - subst. apply length_zero_iff_nil in Hleq. congruence.
  - do 7 eexists. splits; eauto.
Qed.

Lemma qst_Oeq: forall vl O O' act v, qpend_assm_stat vl O act (v, Some O') -> O' = O.
Proof.
  intros.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _  & _ & [(_ & H) | (_ & H)]).
  - inverts H; auto.
  - congruence.
Qed.

Lemma os_stat_q_false:
  forall rv_ptr1 rv_ptr2 pr i O1 O2 t1 t2,
    (exists tls prio t qid sus pr,
      rv_ptr1 = Vptr qid /\
      get O1 curtid = Some (oscurt t) /\
      get O1 abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (prio, wait (os_stat_q qid) (Some Int.zero), Vnull, sus, pr)) ->
    ~ (exists tls prio t qid sus pr,
      rv_ptr2 = Vptr qid /\
      get O2 curtid = Some (oscurt t) /\
      get O2 abstcblsid = Some (abstcblist tls) /\
      get tls t = Some (prio, wait (os_stat_q qid) (Some Int.zero), Vnull, sus, pr)) ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqdes_dom_qptr i rv_ptr1 O1 pr ->
    mqdes_dom_qptr i rv_ptr2 O2 pr ->
    False.
Proof.
  introv Ht Hf Hkteq Hcurt1 Hcurt2 Htpi1 Htpi2 Hkmeq Hmdq1 Hmdq2.
  apply Hf.
  destruct Ht as (tls1 & prio1 & t & qid1 & sus1 & pr1 &
    H & Hcurt1_ & Hget_tcb_map1 & Hget_tcb1).
  subst.
  assert (Hnnull: Vptr qid1 <> Vnull) by congruence.
  lets H: qid_unique_lemma Hnnull Hmdq1 Hmdq2 Hkmeq.
  destruct H as (qid & H1 & H2); inverts H1; subst.
  l_rew12_inv2 (get O1 curtid).
  assert (Htpi1_: task_prio_id O1 pr1 t1) by (unfolds; do 5 eexists; split; eauto).
  assert (pr1 = pr) by (eapply prio_unique; eauto); subst.
  destruct Htpi2 as (pr'2 & tcbs2 & st2 & msg2 & sus2 & Hget_tcb_map2 & Hget_tcb2).
  destruct Hkteq as (tcbs1_ & tcbs2_ & Hget_tcb_map1_ & Hget_tcb_map2_ & H).
  specialize(H pr ltac:(tauto)); destruct H as (_ & H).
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew12_inv2 (get O2 abstcblsid).
  lets H_: H Hget_tcb1 Hget_tcb2.
  simpljoin; subst.
  do 6 eexists. splits; eauto.
Qed.

Lemma absmsgq4_false:
  forall i qid O1 O2 pr,
    (exists qid0 qls,
      Vptr qid = Vptr qid0 /\
      get O1 absecblsid = Some (absecblist qls) /\
      ~ (exists x y pwl wls, get qls qid0 = Some (absmsgq x y pwl, wls))) ->
    ~ (exists qid0 qls,
      Vptr qid = Vptr qid0 /\
      get O2 absecblsid = Some (absecblist qls) /\
      ~ (exists x y pwl wls, get qls qid0 = Some (absmsgq x y pwl, wls))) ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqdes_dom_qptr i (Vptr qid) O1 pr ->
    mqdes_dom_qptr i (Vptr qid) O2 pr ->
    False.
Proof.
  introv Ht Hf Hkmeq Hmdq1 Hmdq2.
  apply Hf.
  destruct Ht as (qid0 & qls1 & H & Hget_ecb_map & Hnexists).
  sinverts H.
  lets H: mq_equiv_unfolded Hmdq1 Hmdq2 Hkmeq.
  destruct H as (ecbs1 & ecbs2 & ed1 & _ & ws1 & _ & Hget_ecb_map1 &
    Hget_ecb_map2 & Hget_ecb1 & _ & (ms & mlen & pws1 & _ & Hed1 & _) & _).
  exists qid ecbs2. splits; eauto.
  introv Hexists; apply Hnexists.
  l_rew12_inv2 (get O1 absecblsid).
  rewrite Hget_ecb1.
  subst. eauto.
Qed.

Lemma absmsgq5_false:
  forall i qid O1 O2 pr,
    (exists qid0 qls,
      Vptr qid = Vptr qid0 /\
      get O1 absecblsid = Some (absecblist qls) /\
      (exists wls n pwl, get qls qid0 = Some (absmsgq nil n pwl, wls))) ->
    ~ (exists qid0 qls,
      Vptr qid = Vptr qid0 /\
      get O2 absecblsid = Some (absecblist qls) /\
      (exists wls n pwl, get qls qid0 = Some (absmsgq nil n pwl, wls))) ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqdes_dom_qptr i (Vptr qid) O1 pr ->
    mqdes_dom_qptr i (Vptr qid) O2 pr ->
    False.
Proof.
  introv Ht Hf Hkmeq Hmdq1 Hmdq2.
  apply Hf.
  destruct Ht as (qid0 & qls1 & H & Hget_ecb_map & (wls1 & n & pwl & Hget_ecb)).
  sinverts H.
  lets H: mq_equiv_unfolded Hmdq1 Hmdq2 Hkmeq.
  destruct H as (ecbs1 & ecbs2 & ed1 & ed2 & ws1 & ws2 & Hget_ecb_map1 &
    Hget_ecb_map2 & Hget_ecb1 & Hget_ecb2 & (ms & mlen & pws1 & pws2 & Hed1 & Hed2 &_) & _).
  subst.
  l_rew12_inv2 (get O1 absecblsid).
  rewrite Hget_ecb in Hget_ecb1; inverts Hget_ecb1.
  exists qid ecbs2. splits; eauto.
Qed.

Lemma rv_post_null_false: 
  forall rv_post msg_ptr msg_len,
    rv_post <> Vnull ->
    vl_equiv (mqrecv_res msg_ptr msg_len rv_post)
      (mqrecv_res msg_ptr msg_len Vnull) ->
    False.
Proof.
  introv Hf Hvleq.
  specialize (Hvleq (rv_post :: nil) (Vnull :: nil) ltac:(tauto)
    ltac:(tauto) 0%nat rv_post Vnull ltac:(tauto) ltac:(tauto)).
  congruence.
Qed.

Lemma me_Oeq: forall vl O O' act v, memcpy_empty vl O act (v, Some O') -> O' = O.
Proof. intros; unfolds in H; simpljoin; congruence. Qed.

Lemma prio_preserved_ctid_eq_preserved:
  forall i O1 O2 O1' O2',  
    ctid_equiv i O1 O2 ->
    get O1 curtid = get O1' curtid ->
    get O2 curtid = get O2' curtid -> 
    prio_preserved O1 O1' -> 
    prio_preserved O2 O2' -> 
    ctid_equiv i O1' O2'. 
Proof.
  introv Hce Hsc1 Hsc2 Hpp1 Hpp2.
  unfold ctid_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).                
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Hd.
  eapply H1; auto. 
  eapply prio_preserved_tpi; eauto.
  eapply prio_preserved_tpi; eauto.
Qed.    

Definition same_prt_ecbs O O' := 
  forall els els',
    get O absecblsid = Some (absecblist els) ->
    get O' absecblsid = Some (absecblist els') ->
    (forall eid tls, get els eid = Some (absport, tls) <-> get els' eid = Some (absport, tls)). 

Lemma kme_kte_gethwait_eq: 
  forall O1 O2 i0 x1 x2 pr tcbs1 tcbs2 ecbs1 ecbs2
         ms1 ms2 ml1 ml2 pwl1 pwl2 wl1 wl2 t1 t2,
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    (* tidls_equiv ws1 ws2 O1 O2 -> *)
    mqdes_dom_qptr i0 (Vptr x1) O1 pr ->
    mqdes_dom_qptr i0 (Vptr x2) O2 pr ->
    get O1 abstcblsid = Some (abstcblist tcbs1) ->
    get O1 absecblsid = Some (absecblist ecbs1) ->
    get O2 abstcblsid = Some (abstcblist tcbs2) ->
    get O2 absecblsid = Some (absecblist ecbs2) ->
    get ecbs1 x1 = Some (absmsgq ms1 ml1 pwl1, wl1) ->
    get ecbs2 x2 = Some (absmsgq ms2 ml2 pwl2, wl2) -> 
    GetHWait tcbs1 pwl1 t1 ->
    GetHWait tcbs2 pwl2 t2 ->
    (exists pr0,
        task_prio_id O1 pr0 t1 /\ task_prio_id O2 pr0 t2
        /\ dom_for_prio pr0 = dom_for_prio pr). 
Proof.
  introv Hkte Hkme Hmd1 Hmd2 Hgt1 Hge1 Hgt2 Hge2.
  introv He1 He2 Hgw1 Hgw2.
  unfolds in Hkme.
  unfolds in Hmd1. unfolds in Hmd2.
  unfold mq_ptr in *.
  simpljoin.
  l_rew21_inv1 (get O1 absmqattrid).
  l_rew21_inv1 (get O2 absmqattrid).
  do 2 match goal with
      H: _/\Vptr _=Vnull \/ _ |- _ => inverts H; simpljoin; tryfalse
    end.
  do 2 match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  lets H_: H9 H0.
  destruct H_ as (_ & H_). 
  specializes H_; eauto.
  unfold mq_equiv in H_.
  simpljoin.
  match goal with
    H: _\/_\/_ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin; tryfalse
  end.
  unfolds in H12. simpljoin.
  do 2 match goal with H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H end.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  rewrite H10 in He1. inverts He1.
  rewrite H11 in He2. inverts He2.
  lets H__: kte_tidls_eq_gethwait_eq Hkte Hgt1 Hgt2 Hgw1 Hgw2.
  specializes H__; eauto.
  introv Hin.
  lets H__: mq_part_consistent O1 ecbs1 wl1 pwl1. 
  specializes H__; eauto. 
  introv Hin.
  lets H__: mq_part_consistent O2 ecbs2 wl2 pwl2. 
  specializes H__; eauto. 
Qed. 

Lemma ports_equiv_same_prts_preserve2: 
  forall td O1 O2 O1' O2', 
    ports_equiv td O1 O2 ->
    get O1 osdomainportid = get O1' osdomainportid ->
    get O2 osdomainportid = get O2' osdomainportid ->
    get O1 oskportid = get O1' oskportid ->
    get O2 oskportid = get O2' oskportid ->
    same_prt_ecbs O1 O1' ->
    same_prt_ecbs O2 O2' ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' -> 
    ports_equiv td O1' O2'. 
Proof.
  introv Hpe Hgeq1 Hgeq2 Hkpe1 Hkpe2 Hsp1 Hsp2 Hdi1 Hdi2.
  introv Hpp1 Hpp2.
  unfold ports_equiv in *.
  simpljoin.
  rewrite H in Hgeq1; symmetry in Hgeq1.
  rewrite H0 in Hgeq2; symmetry in Hgeq2.
  unfold same_prt_ecbs in *.
  unfolds in Hdi1.
  specialize (Hdi1 absecblsid). 
  rewrite H1 in Hdi1.
  destruct Hdi1 as (els1' & Hgels1').
  unfolds in Hdi2.
  specialize (Hdi2 absecblsid).
  rewrite H2 in Hdi2.
  destruct Hdi2 as (els2' & Hgels2').
  do 4 eexists.
  splits; eauto.
  introv Hid.
  match goal with H: forall _, _ |- _ => specialize (H _ Hid); rename H into Ha end.
  destruct Ha as (Hgeq & Hiff & Hwteq). 
  split; auto.
  split.
  {
    specializes Hsp1 a; eauto.
    specializes Hsp2 a; eauto.
    split.
    - 
      introv Hex1.
      destruct Hex1 as (tls1 & Hiff1).
      eapply Hsp1 in Hiff1; eauto.
      assert (Hex: exists tls, get x1 a = Some (absport, tls)).
      { eexists; eauto. }
      apply Hiff in Hex.
      destruct Hex as (tls & Hg2).
      eapply Hsp2 in Hg2; eauto.
    -
      introv Hex2.
      destruct Hex2 as (tls2 & Hiff2).
      eapply Hsp2 in Hiff2; eauto. 
      assert (Hex: exists tls, get x2 a = Some (absport, tls)).
      { eexists; eauto. }
      apply Hiff in Hex.
      destruct Hex as (tls & Hg1).
      eapply Hsp1 in Hg1; eauto.
  }
  (* forall ..., ... -> tidls_equiv *)
  introv (* Hgx *) Hge1 Hge2. 
  lets Hgeqv1: Hsp1 H1 Hgels1' a. 
  lets Hgeqv2: Hsp2 H2 Hgels2' a. 
  eapply Hgeqv1 in Hge1.
  eapply Hgeqv2 in Hge2.
  lets H__: Hwteq (* Hgx *) Hge1 Hge2.
  eapply tidls_equiv_pp_preserve2; eauto. 
Qed. 

Lemma mqd_eq_dest: 
  forall i0 x1 x2 O1 O2 pr mqa1 mqa2 mq1 mq2 td, 
    mqdes_dom_qptr i0 (Vptr x1) O1 pr ->
    mqdes_dom_qptr i0 (Vptr x2) O2 pr ->
    get O1 absmqattrid = Some (absmqattr mqa1) -> 
    get O2 absmqattrid = Some (absmqattr mqa2) -> 
    get mqa1 i0 = Some mq1 ->
    get mqa2 i0 = Some mq2 ->
    mq_equiv td mq1 mq2 O1 O2 ->
    exists x y2 y3 y4 y5 y6 y7,
      x = x1 /\ x = x2 /\ 
      mq1 = (Valid_Addr x, y2, y3, y4, y5, y6, y7) /\
        mq2 = (Valid_Addr x, y2, y3, y4, y5, y6, y7) /\ 
        exists ecbs1 ecbs2 ed1 ed2 ws1 ws2,
        get O1 absecblsid = Some (absecblist ecbs1) /\
        get O2 absecblsid = Some (absecblist ecbs2) /\
        get ecbs1 x1 = Some (ed1, ws1) /\
        get ecbs2 x2 = Some (ed2, ws2) /\
        mq_ed_equiv ed1 ed2 O1 O2 /\ tidls_equiv ws1 ws2 O1 O2. 
Proof.
  introv Hmd1 Hmd2 Hg1 Hg2 Hq1 Hq2 Heqv.
  unfold mqdes_dom_qptr in *.
  unfold mq_ptr in *.
  simpljoin.
  do 2 match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  do 2 match goal with H: Vptr _ = _ |- _ => inverts H end.
  unfold mq_equiv in *.
  simpljoin.
  l_rew21_inv1 (get O1 absmqattrid).
  l_rew21_inv1 (get O2 absmqattrid).
  rewrite H5 in Hq1. inverts Hq1.
  rewrite H1 in Hq2. inverts Hq2.
  match goal with
    H: _ \/ _ \/ _ |- _ =>
      destruct H as [Hf1 | [Hf2 | Ht]]; simpljoin; tryfalse
  end.
  do 2 match goal with H: Valid_Addr _ = _ |- _ => inverts H end.
  do 7 eexists. split; eauto. split; eauto.
  split; eauto. split; eauto. 
  do 6 eexists. 
  splits; eauto. 
Qed.

Lemma kme_eptreq: 
  forall pr O1 O2 x1 x2 i0, 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqdes_dom_qptr i0 (Vptr x1) O1 pr ->
    mqdes_dom_qptr i0 (Vptr x2) O2 pr ->
    x1 = x2.
Proof.
  introv Hkme Hd1 Hd2.
  unfolds in Hkme.
  unfold mqdes_dom_qptr in *.
  simpljoin.
  unfold mq_ptr in *.
  simpljoin.
  l_rew21_inv1 (get O1 absmqattrid).
  l_rew21_inv1 (get O2 absmqattrid).
  do 2 (match goal with
          H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse
        end).
  do 2 match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  match goal with
    H: forall _, _ |- _ => rename H into Ha; specializes Ha; eauto
  end.
  destruct Ha as (Hiff & Ha).
  specializes Ha; eauto.
  unfolds in Ha.
  simpljoin.
  match goal with
    H: _ \/ _ \/ _ |- _ =>
      destruct H as [Hnull | [Hholder | Hptr]]; simpljoin; try congruence
  end.
Qed.

Lemma mq_ed_equiv_pp_preserve2:
  forall ed1 ed2 O1 O2 O1' O2', 
    mq_ed_equiv ed1 ed2 O1 O2 ->
    prio_preserved O1 O1' ->
    prio_preserved O2 O2' ->
    mq_ed_equiv ed1 ed2 O1' O2'. 
Proof.
  introv Hmee Hpp1 Hpp2.
  unfold mq_ed_equiv in *.
  simpljoin.
  do 4 eexists.
  splits; eauto.
  eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma pr_diff_dom_tid_neq: 
  forall O O' pr pr' t t', 
    task_prio_id O pr t ->
    task_prio_id O' pr' t' ->
    prio_preserved O O' ->
    dom_for_prio pr <> dom_for_prio pr' ->
    t <> t'. 
Proof.
  introv Htpi Htpi' Hpp Hdiff.
  casetac pr pr' Ht Hf.
  - subst.
    false.
  - introv Hteq.
    subst.
    eapply prio_preserved_tpi in Htpi'; eauto.
    apply2 task_prio_id task_prio_id prio_unique.
    apply Hf. auto.
Qed.

Ltac sp_forall1' hypname :=
  match goal with
    H: forall _, _ |- _ => rename H into hypname; specializes hypname; eauto
  end. 

Ltac solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heq1 Heq2 k :=
  unfolds;
  match type of Hlenvl with length ?vl = _ => exists vl end; 
  match type of Hlenvl1 with length ?vl = _ => exists vl end; 
  match type of Hlenvl2 with length ?vl = _ => exists vl end; 
  unprotect Heq1;  unprotect Heq2; subst; 
  exists k%nat; 
  split; [simpl; auto | 
           split; [ simpl; auto | 
                    split;  [ simpl; auto | 
                              split;  [ simpl; auto | 
                                        simpl; auto]]]].

Ltac solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 k :=
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

Lemma qpend_get_no_pwl_succ_cpid_same:
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    get O cspaceid = get O' cspaceid.  
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpend_get_no_pwl_succ_ctid_same:
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    get O curtid = get O' curtid. 
Proof.
  introv Hjo Hjo' Hovf.
  inverts Hovf.
  simpljoin.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with
    H: ?f _ = ?f _ |- _ => inverts H
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  rewrite set_a_get_a'; eauto. introv Htemp. congruence.
Qed.

Lemma qpend_get_no_pwl_succ_bufs_same:
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hjo Hjo' Hovf.
  inverts Hovf.
  simpljoin.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  split.
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
Qed.

Lemma qpend_get_no_pwl_succ_mqref_preserve: 
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' -> 
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    mq_ref_preserved O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get OO absmqattrid = Some (absmqattr mqs)
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

Lemma qpend_get_no_pwl_succ_qprt_preserve: 
  forall qid rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' -> 
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    qprt_preserved O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get OO osdomainportid = Some (osdomainport dpl)
               \/ get Of osdomainportid = Some (osdomainport dpl)).
  {
    eapply join_get_or with (m:=O); eauto.
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

Lemma qpend_get_no_pwl_succ_dpid_same: 
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' -> 
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpend_get_no_pwl_succ_kpid_same:
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpend_get_no_pwl_succ_same_prt_ecbs:
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    same_prt_ecbs O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds.
  introv Hg Hg'.
  intros.
  inverts Hpost.
  simpljoin. 
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  split.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x2)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context[ (set OO absecblsid (absecblist ?els')) ] =>
        assert (H__: get (set OO absecblsid (absecblist els')) absecblsid = Some (absecblist els'))
    end.
    rewrite set_a_get_a. auto.
    match type of H__ with
      context [Some (absecblist ?els')] => 
        assert (Hge': get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    clear H__.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite Hge in H3. tryfalse. 
    + rewrite set_a_get_a'; eauto. 
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x2)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context[ (set OO absecblsid (absecblist ?els')) ] =>
        assert (H__: get (set OO absecblsid (absecblist els')) absecblsid = Some (absecblist els'))
    end.
    rewrite set_a_get_a. auto.
    match type of H__ with
      context [Some (absecblist ?els')] => 
        assert (Hge': get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    clear H__.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite set_a_get_a in Hge. inverts Hge.
    + rewrite set_a_get_a' in Hge; eauto. 
Qed. 

Lemma qpend_get_no_pwl_succ_dom_impl:
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    dom_impl O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds.
  intro x.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  destruct (get O x) eqn: E.
  2: {                    
    assert (get OO x = None).
    { eapply join_get_none_rev1; eauto. }
    assert (get Of x = None).
    { clear -Hjo E. eapply join_get_none_rev2; eauto. }
    eapply map_join_get_none'''; eauto.
    casetac absecblsid x Ht Hf.
    - subst. l_rew21_inv1 (get OO absecblsid).
    - rewrite set_a_get_a'; eauto. 
  }
  destruct a eqn: E'; 
    try (
        assert (Heq: get O x = get O' x)
        by
        (lets H__: join_get_same_l Hjo Hjo'; eauto; 
         casetac absecblsid x Ht Hf; 
         [ subst; 
           eapply join_get_get_l with (m:=O) in H1; eauto; 
           l_rew21_inv1 (get O absecblsid)
         |
           rewrite set_a_get_a'; eauto]); 
        rewrite E in Heq; 
        eexists; symmetry; eauto;
        fail).
  assert (Hor: get OO x = Some (absecblist m) \/ get Of x = Some (absecblist m)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  2: {
    eexists; eapply join_get_get_r; eauto.
  }
  casetac absecblsid x Ht Hf.
  -
    subst. eexists. 
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a; eauto.
  -
    exists m.
    eapply join_get_get_l; eauto. 
    rewrite set_a_get_a'; eauto.
Qed.   

Lemma qpend_get_no_pwl_succ_mqptr_impl: 
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hjo Hjo' Hpost Hmp'.
  unfold mq_ptr in *.
  inverts Hpost.
  simpljoin.
  match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
  inverts Hsome.
  2: { simpljoin; tryfalse. }
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpend_get_no_pwl_succ_mqptr_iff: 
  forall qid rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) OO act (v, Some OO') ->
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp.
Proof.
  introv Hjo Hjo' Hpost.
  intros.
  split.
  - eapply qpend_get_no_pwl_succ_mqptr_impl; eauto.
  - introv Hmp.
    unfold mq_ptr in *.
    inverts Hpost.
    simpljoin.
    match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
    inverts Hsome.
    2: { simpljoin; tryfalse. }
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf. 
    }
    l_rew12_inv2 (get O absmqattrid). 
    do 8 eexists; eauto.
Qed.

Lemma qpend_get_no_pwl_succ_body_get_tcbid_eq:
  forall qid rv_post v act O O', 
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post :: nil) O act (v, Some O') ->
    get O abstcblsid = get O' abstcblsid. 
Proof.
  introv Hr.
  inverts Hr.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  inverts H5.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed.

Lemma  qpend_get_no_pwl_succ_body_ctid_equiv_preserve2:
  forall qid rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' -> 
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2.
  unfold ctid_equiv in *.
  unfold qpend_get_no_pwl_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get OO1 curtid = get OO1' curtid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  } 
  lets Hct1': join_upd_get_same H1. 
  specializes Hct1'; eauto.
  assert (Hupd2: get OO2 curtid = get OO2' curtid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hct2': join_upd_get_same H18. 
  specializes Hct2'; eauto. 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Htd.
  assert (Hupd1': get OO1' abstcblsid = get OO1 abstcblsid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Htpi1: tpi_upd_frm_preserved Htpi1' Hjo1' Hupd1' Hjo1.
  assert (Hupd2': get OO2' abstcblsid = get OO2 abstcblsid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Htpi2: tpi_upd_frm_preserved Htpi2' Hjo2' Hupd2' Hjo2.
  lets H__: H19 Htpi1 Htpi2. eapply H__; eauto.
Qed. 

Lemma qpend_get_no_pwl_succ_body_ibufs_equiv_preserve2:
  forall qid rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    ibufs_equiv td O1 O2 ->
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    ibufs_equiv td O1' O2'.
Proof.
  introv Hibfe Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2. 
  unfold ibufs_equiv in *. 
  unfold qpend_get_no_pwl_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get OO1 ibufsid = get OO1' ibufsid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf1': join_upd_get_same H1. 
  specializes Hbf1'; eauto.
  assert (Hupd2: get OO2 ibufsid = get OO2' ibufsid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf2': join_upd_get_same H18. 
  specializes Hbf2'; eauto.
Qed. 

Lemma qpend_get_no_pwl_succ_body_obufs_equiv_preserve2:
  forall qid rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    obufs_equiv td O1 O2 ->
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    obufs_equiv td O1' O2'.
Proof.
  introv Hobfe Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2. 
  unfold obufs_equiv in *. 
  unfold qpend_get_no_pwl_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get OO1 obufsid = get OO1' obufsid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf1': join_upd_get_same H1. 
  specializes Hbf1'; eauto.
  assert (Hupd2: get OO2 obufsid = get OO2' obufsid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf2': join_upd_get_same H18. 
  specializes Hbf2'; eauto.
Qed.                

Lemma qpend_get_no_pwl_succ_body_bufs_equiv_preserve2:
  forall qid rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    bufs_equiv td O1 O2 ->
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    bufs_equiv td O1' O2'.
Proof.
  introv Hbfe Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2.
  unfolds in Hbfe.
  destruct Hbfe as (Hibe & Hobe).
  split.
  eapply qpend_get_no_pwl_succ_body_ibufs_equiv_preserve2; eauto.
  eapply qpend_get_no_pwl_succ_body_obufs_equiv_preserve2; eauto. 
Qed. 

Lemma qpend_get_no_pwl_succ_knl_mq_equiv_preserve2:
  forall vp1 vp2 pr i0 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    kernel_mq_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_no_pwl_succ_body (vp1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_get_no_pwl_succ_body (vp2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    kernel_mq_equiv td O1' O2'.
Proof.
  introv Hkme Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2 Hmdp1 Hmdp2.
  unfold kernel_mq_equiv in *.
  assert (Hpost1_:= Hpost1).
  assert (Hpost2_ := Hpost2). 
  inverts Hpost1. 
  inverts Hpost2. 
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inversion H; clear H end.
  match goal with H: Some _ = Some _ |- _ => inversion H; clear H end.
  assert (Hgeq1: get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l absmqattrid Hjo1 Hjo1'; eauto.
    subst OO1'.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.                    
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l absmqattrid Hjo2 Hjo2'; eauto.
    subst OO2'.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.  
  }
  rewrite <- Hgeq1. rewrite <- Hgeq2.
  do 2 eexists.
  splits; eauto.
  introv Hd.
  split.
  {
    match goal with H: forall _, _ |- _ => rename H into Ha; specializes Ha; eauto end.
    destruct Ha. auto.
  }
  (* mq_equiv *)
  introv Hget1 Hget2.
  assert (Hmqe0: mq_equiv td mq1 mq2 O1 O2).
  { eapply H19; eauto. }
  unfold mq_equiv in *.
  simpljoin.
  do 8 eexists. splits; eauto.
  match goal with H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]] end.
  - left. auto.
  - right. left. auto.
  -
    right; right.
    simpljoin. 
    match type of Hjo1' with context [absecblist ?els'] => exists els' end.
    match type of Hjo2' with context [absecblist ?els'] => exists els' end.
    assert (Hget1_: get O1 absecblsid = Some (absecblist x14)).
    {
      eapply join_get_get_l; eauto.
    }
    assert (Hget2_: get O2 absecblsid = Some (absecblist x6)).
    {
      eapply join_get_get_l; eauto. 
    }
    l_rew21_inv1 (get O1 absecblsid).
    l_rew21_inv1 (get O2 absecblsid).

    unfolds in Hmdp1. unfolds in Hmdp2.
    destruct Hmdp1 as (Hmid1 & Hmp1).
    destruct Hmdp2 as (Hmid2 & Hmp2).
    unfolds in Hmp1.  
    unfolds in Hmp2.
    simpljoin.
    protect Hgeq1.
    protect Hgeq2.
    l_rew21_inv1 (get O1 absmqattrid). 
    l_rew21_inv1 (get O2 absmqattrid).
    do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).                    
    do 2 (match goal with H: Vptr _ = Vptr _ |- _ => inverts H end). 
    (* do 2 (match goal with H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H end). *)

    casetac i i0 Ht Hf.
    +
      subst.
      rewrite H16 in Hget1. inverts Hget1.
      rewrite H6 in Hget2. inverts Hget2.
      rewrite H5 in H9. inverts H9.
      rewrite H13 in H8. inverts H8.
      do 5 eexists. 
      splits; eauto.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a; auto.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a; auto.
      rewrite set_a_get_a; eauto.
      rewrite set_a_get_a; eauto.
      unfold mq_ed_equiv in *.
      simpljoin.
      do 2 (match goal with H: absmsgq _ _ _  = absmsgq _ _ _ |- _ => inverts H end).
      do 4 eexists. 
      splits; eauto.
      unfolds. split; auto.
      intros. split; introv Hf; simpljoin; tryfalse.
      eapply tidls_equiv_pp_preserve2; eauto.
      lets H__: qpend_nopwl_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: qpend_nopwl_succ_prio_preserved Hjo2 Hjo2'; eauto. 
    +                      
      lets H1_: mq_ecb_ref_distinct Hf Hget1.
      specializes H1_; eauto.
      lets H2_: mq_ecb_ref_distinct Hf Hget2.
      specializes H2_; eauto.
      do 6 eexists. 
      split; eauto.
      split; eauto.
      split. eapply join_get_get_l; eauto. rewrite set_a_get_a; auto.
      split. eapply join_get_get_l; eauto. rewrite set_a_get_a; auto.
      split. rewrite set_a_get_a'; eauto.
      split. rewrite set_a_get_a'; eauto.
      split.
      unfold mq_ed_equiv in *.
      simpljoin.
      do 4 eexists. 
      splits; eauto.
      eapply tidls_equiv_pp_preserve2; eauto.
      lets H__: qpend_nopwl_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: qpend_nopwl_succ_prio_preserved Hjo2 Hjo2'; eauto. 
      eapply tidls_equiv_pp_preserve2; eauto.
      lets H__: qpend_nopwl_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: qpend_nopwl_succ_prio_preserved Hjo2 Hjo2'; eauto.                       
Qed.

Lemma mq_buffer_eid_diff:
  forall i eid eid' O pr td, 
    mqdes_dom_qptr i (Vptr eid) O pr -> 
    buf_in_dom eid' td = true ->
    eid <> eid'. 
Proof.
  introv Hmd Hbid Heq.
  subst.
  unfolds in Hmd.
  destruct Hmd as (Hmi & Hmp).
  unfolds in Hmp.
  simpljoin. 
  rem_dis.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  lets H_: not_both_mq_and_buffer.
  specializes H_; eauto.
Qed.

Lemma qpend_get_no_pwl_succ_buffer_equiv_succ_preserve2:
  forall vp1 vp2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2' i0 pr, 
    buffer_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_no_pwl_succ_body (vp1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_get_no_pwl_succ_body (vp2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hjo1' Hjo2' Hqn1 Hqn2 Hmd1 Hmd2. 
  lets Hpp1: qpend_nopwl_succ_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpend_nopwl_succ_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  rem_dis.
  rem_dis.
  inv_some.
  inv_some.
  inv_lst.
  inv_lst. 
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext OO1 absecblsid O1.
  kvext OO2 absecblsid O2.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  eapply buffer_equiv_nupd_preserve2; eauto.
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
Qed.

Lemma qpend_get_no_pwl_succ_body_dteq_preserve2:
  forall qid rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2' i0 pr  cst1 cst2, 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_get_no_pwl_succ_body (Vptr qid :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    (* ctid_equiv td O1 O2 ->  *)
    (* kernel_task_equiv (dom_for_prio pr) O1 O2 ->  *)
    (* kernel_mq_equiv (dom_for_prio pr) O1 O2 ->  *)
    mqdes_dom_qptr i0 (Vptr qid) O1 pr ->
    mqdes_dom_qptr i0 (Vptr qid) O2 pr ->
    data_equiv_tskd td cst1 cst2 O1' O2'.   
Proof.
  introv Hde Hkme Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2  Hmd1 Hmd2. 
  unfold data_equiv_tskd in *.
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  split.
  eapply qpend_get_no_pwl_succ_body_ctid_equiv_preserve2; eauto.
  split.
  eapply qpend_get_no_pwl_succ_body_bufs_equiv_preserve2; eauto.
  split.
  2: {
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: qpend_nopwl_succ_prio_preserved Hpost1; eauto. 
    lets H__: qpend_nopwl_succ_prio_preserved Hpost2; eauto. 
  }
  unfold kernel_data_equiv.

  split.
  { (* kernel_task_equiv *)
    destructs Hkde.
    eapply knl_tsk_equiv_same_tls_preserve2; eauto.
    lets H__: join_get_same_l abstcblsid Hjo1 Hjo1'.
    eapply qpend_get_no_pwl_succ_body_get_tcbid_eq; eauto. 
    auto.
    lets H__: join_get_same_l abstcblsid Hjo2 Hjo2'. 
    eapply qpend_get_no_pwl_succ_body_get_tcbid_eq; eauto.
    auto. 
  }
  split.
  {
    (* kernel_mq_equiv *)

    clear Hkme.
    destructs Hkde.
    eapply qpend_get_no_pwl_succ_knl_mq_equiv_preserve2; eauto. 
  }
  split.
  { (* ports_equiv *)
    destructs Hkde. 
    eapply ports_equiv_same_prts_preserve2; eauto.                     
    
    lets H__: qpend_get_no_pwl_succ_dpid_same Hjo1 Hjo1'; eauto. 
    lets H__: qpend_get_no_pwl_succ_dpid_same Hjo2 Hjo2'; eauto. 
    lets H__: qpend_get_no_pwl_succ_kpid_same Hjo1 Hjo1'; eauto.
    lets H__: qpend_get_no_pwl_succ_kpid_same Hjo2 Hjo2'; eauto.
    lets H__: qpend_get_no_pwl_succ_same_prt_ecbs Hjo1 Hjo1'; eauto.
    lets H__: qpend_get_no_pwl_succ_same_prt_ecbs Hjo2 Hjo2'; eauto.
    lets H__: qpend_get_no_pwl_succ_dom_impl Hjo1 Hjo1'; eauto.
    lets H__: qpend_get_no_pwl_succ_dom_impl Hjo2 Hjo2'; eauto.
    lets H__: qpend_nopwl_succ_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpend_nopwl_succ_prio_preserved Hjo2 Hjo2'; eauto.
  }

  (* split.  *)
  (* { (* kports_equiv *) *)
  (*   destructs Hkde. *)
  (*   eapply kprts_equiv_same_prts_preserve2; eauto. *)
  (*   lets H__: qtimedpost_nowt_succ_kpid_same Hjo1 Hjo1'; eauto. *)
  (*   lets H__: qtimedpost_nowt_succ_kpid_same Hjo2 Hjo2'; eauto. *)
  (*   lets H__: qtimedpost_nowt_succ_dpid_same Hjo1 Hjo1'; eauto. *)
  (*   lets H__: qtimedpost_nowt_succ_dpid_same Hjo2 Hjo2'; eauto.    *)
  (* } *)

  destructs Hkde.
  split. eapply qpend_get_no_pwl_succ_buffer_equiv_succ_preserve2; eauto.

  (* cap_equiv *)
  eapply cap_equiv_preserve2; eauto.
  lets H__: qpend_get_no_pwl_succ_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_get_no_pwl_succ_cpid_same Hjo2 Hjo2'; eauto.

  lets H__: qpend_get_no_pwl_succ_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qpend_get_no_pwl_succ_mqptr_iff Hjo2 Hjo2'; eauto.
Qed.

Lemma qpend_get_ex_pwl_before_sched_cpid_same:
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    get O cspaceid = get O' cspaceid.  
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed.

Lemma qpend_get_ex_pwl_before_sched_mqref_preserve:
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get OO absmqattrid = Some (absmqattr mqs)
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

Lemma qpend_get_ex_pwl_before_sched_qprt_preserve: 
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    qprt_preserved O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get OO osdomainportid = Some (osdomainport dpl)
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

Lemma qpend_get_ex_pwl_before_sched_mqattr_same:
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    get O absmqattrid = get O' absmqattrid.  
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed.

Lemma qpend_get_ex_pwl_before_sched_bufs_same:
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hjo Hjo' Hpost.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
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

Lemma qpend_get_ex_pwl_before_sched_dpid_same: 
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed. 

Lemma qpend_get_ex_pwl_before_sched_kpid_same:
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    get O oskportid = get O' oskportid.  
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpend_get_ex_pwl_before_sched_same_prt_ecbs:
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    same_prt_ecbs O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds.
  introv Hg Hg'.
  intros.
  inverts Hpost.
  simpljoin. 
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  split.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x1)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with 
      context[ absecblist ?els' ] => assert (H__: get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a.
    auto. 
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. unfold get in *. unfold EcbMap in *.
      l_rew21_inv1 (EcbMod.get els eid).
    + rewrite set_a_get_a'; eauto. 
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x1)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context [ absecblist ?els' ] => assert (get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a. auto.            
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite set_a_get_a in Hge. inverts Hge.
    + rewrite set_a_get_a' in Hge; eauto. 
Qed. 

Lemma qpend_get_ex_pwl_before_sched_dom_impl:
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    dom_impl O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds.
  intro x.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  destruct (get O x) eqn: E.
  2: {                    
    assert (get OO x = None).
    { eapply join_get_none_rev1; eauto. }
    assert (get Of x = None).
    { clear -Hjo E. eapply join_get_none_rev2; eauto. }
    eapply map_join_get_none'''; eauto.
    casetac absecblsid x Ht Hf.
    - subst. l_rew21_inv1 (get OO absecblsid).
    - rewrite set_a_get_a'; eauto.
      casetac abstcblsid x Ht_ Hf_.
      + subst.
        assert (get OO abstcblsid = None).
        { eapply join_get_none_rev1; eauto. }
        l_rew21_inv1 (get OO abstcblsid).
        tryfalse.
      + rewrite set_a_get_a'; eauto. 
  }
  destruct a eqn: E';
    try (
        assert (Heq: get O x = get O' x) by
        (lets H__: join_get_same_l Hjo Hjo'; eauto; 
         casetac absecblsid x Ht Hf;
         [ subst; 
           eapply join_get_get_l with (m:=O) in H0; eauto; 
           l_rew21_inv1 (get O absecblsid) |
           rewrite set_a_get_a'; eauto; 
           casetac abstcblsid x Ht_ Hf_;
           [ subst; 
             eapply join_get_get_l with (m:=O) in H1; eauto; 
             l_rew21_inv1 (get O abstcblsid) | 
             rewrite set_a_get_a'; eauto ]]); 
        rewrite E in Heq; 
        eexists; symmetry; eauto; fail).             
  {
    assert (Hor: get OO x = Some (abstcblist m) \/ get Of x = Some (abstcblist m)).
    { eapply join_get_or; eauto. }
    destruct Hor as [Hl | Hr].
    2: { eexists; eapply join_get_get_r; eauto. }
    casetac absecblsid x Ht Hf.
    -
      subst.
      l_rew21_inv1 (get OO absecblsid).
    -
      casetac abstcblsid x Ht_ Hf_.
      +
        subst. eexists.
        eapply join_get_get_l; eauto. 
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a. eauto.
      +
        eexists.
        eapply join_get_get_l; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.
  }
  {
    assert (Hor: get OO x = Some (absecblist m) \/ get Of x = Some (absecblist m)).
    { eapply join_get_or; eauto. }
    destruct Hor as [Hl | Hr].
    2: { eexists; eapply join_get_get_r; eauto. }
    casetac absecblsid x Ht Hf.
    -
      subst.
      l_rew21_inv1 (get OO absecblsid).
      eexists. eapply join_get_get_l; eauto.
      rewrite set_a_get_a. eauto. 
    -
      casetac abstcblsid x Ht_ Hf_.
      +
        subst.
        l_rew21_inv1 (get OO abstcblsid).
      +
        eexists.
        eapply join_get_get_l; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.            
  }          
Qed.    

Lemma qpend_get_ex_pwl_before_sched_mqptr_impl: 
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hjo Hjo' Hpost Hmp'.
  unfold mq_ptr in *.
  assert (Hp := Hpost).
  inverts Hpost.
  simpljoin.
  match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
  inverts Hsome.
  2: { simpljoin; tryfalse. }
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qpend_get_ex_pwl_before_sched_mqattr_same Hjo Hjo'; eauto.   
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpend_get_ex_pwl_before_sched_mqptr_iff: 
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp.  
Proof.
  introv Hjo Hjo' Hpost.
  intros.
  split.
  - eapply qpend_get_ex_pwl_before_sched_mqptr_impl; eauto. 
  -  
    introv Hmp'.
    unfold mq_ptr in *.
    assert (Hp := Hpost).
    inverts Hpost.
    simpljoin.
    match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
    inverts Hsome.
    2: { simpljoin; tryfalse. }
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: qpend_get_ex_pwl_before_sched_mqattr_same Hjo Hjo'; eauto.   
    }
    rewrite H0 in H.
    do 8 eexists; eauto.
Qed.

Lemma mq_idx_neq_ptr_neq:
  forall i i' eid O pr eid' x1 x2 x3 x4 x5 x6 mq, 
    mqdes_dom_qptr i (Vptr eid) O pr ->
    i <> i' ->
    get O absmqattrid = Some (absmqattr mq) -> 
    get mq i' = Some (Valid_Addr eid', x1, x2, x3, x4, x5, x6) ->
    eid <> eid'. 
Proof.
  introv Hmqd Hneq Hg Hgi.
  unfolds in Hmqd.
  unfold mq_ptr in *.
  simpljoin.
  l_rew21_inv1 (get O absmqattrid).
  match goal with H: _\/_ |- _ => inverts H; simpljoin; tryfalse end.
  inverts H2.
  eapply mq_ecb_ref_distinct; eauto. 
Qed.

Lemma qpend_get_ex_pwl_before_sched_knl_mq_equiv_preserve2:
  forall pr i rv_ptr1 rv_ptr2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    kernel_data_equiv td O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    mqdes_dom_qptr i rv_ptr1 O1 pr ->
    mqdes_dom_qptr i rv_ptr2 O2 pr ->
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') -> 
    qpend_get_ex_pwl_before_sched_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') -> 
    (kernel_task_equiv td O1' O2' /\ kernel_mq_equiv td O1' O2').       
Proof.
  introv Hkde Hkte Hkme Hmdp1 Hmdp2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2.
  assert (Hkte_ := Hkte).
  unfolds in Hkte.
  (* unfolds in Hkme. *)
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
    lets H__: join_get_same_l absmqattrid Hjo1 Hjo1'; eauto.
    subst.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf. 
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l absmqattrid Hjo2 Hjo2'; eauto.
    subst.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf. 
  }
  match goal with
    H: get OO1 abstcblsid = ?otcbs |- _ => assert (Hg1: get O1 abstcblsid = otcbs)
  end.
  eapply join_get_get_l; eauto. 
  match goal with
    H: get OO2 abstcblsid = ?otcbs |- _ => assert (Hg2: get O2 abstcblsid = otcbs)
  end.
  eapply join_get_get_l; eauto.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).

  match goal with
    H: context [set OO1 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O1' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto.
    subst OO1'.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a.
    auto. 
  }
  match goal with
    H: context [set OO2 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O2' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto.
    subst OO2'.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a.
    auto. 
  }
    
  split.
  -
    unfolds in Hkde.
    destruct Hkde as (Hkte & Hkme_ & _ & _ & _).
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
          eapply qpend_get_expwl_before_sched_prio_preserved; eauto. 
        }
        apply Htpi12 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto. 
      *
        introv Htpi2'.
        assert (Hex: exists t, task_prio_id O2 pr0 t).
        {
          destruct Htpi2' as (t_ & Htpi2').
          eexists.
          eapply prio_preserved_tpi; eauto. 
          lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto. 
        }
        apply Htpi21 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo1 Hjo1'; eauto. 
    + 
      introv Hg1' Hg2'.
      assert (Htpi1': task_prio_id O1' pr0 t1).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi2': task_prio_id O2' pr0 t2).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi1_: task_prio_id O1 pr0 t1).
      {
        eapply prio_preserved_tpi; eauto.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo1 Hjo1'; eauto.
      }
      assert (Htpi2_: task_prio_id O2 pr0 t2).
      {
        eapply prio_preserved_tpi; eauto.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto.
      }
      unfolds in Htpi1_. unfolds in Htpi2_.
      simpljoin.
      do 2 l_rew21_inv1 (get O1 abstcblsid).
      do 2 l_rew21_inv1 (get O2 abstcblsid).
      lets H__: kme_kte_gethwait_eq Hkte_ Hkme Hmdp1 Hmdp2. 
      specializes H__; eauto. eauto. eauto. eauto. eauto. eauto.
      eapply join_get_get_l; eauto.
      eapply join_get_get_l; eauto.
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
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto.
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
  -
    unfolds in Hkde.
    destruct Hkde as (Hkte & Hkme_ & _ & _ & _).
    destruct Hkme_ as (mqa1 & mqa2 & Hgm1 & Hgm2 & Hall).
    lets Hmqeq1: qpend_get_ex_pwl_before_sched_mqattr_same Hjo1 Hjo1'; eauto. 
    lets Hmqeq2: qpend_get_ex_pwl_before_sched_mqattr_same Hjo2 Hjo2'; eauto. 
    unfold kernel_mq_equiv.
    exists mqa1. exists mqa2.
    split. congruence.
    split. congruence.
    introv Hmd_.
    split.
    {
      lets H__: Hall Hmd_; eauto.
      destruct H__. auto.
    }
    (* mq_equiv *) 
    introv Hgm1_ Hgm2_.    
    specializes Hall; eauto.
    casetac i0 i Ht Hf.
    + (* i0 = i*)
      subst. 
      lets H__: mqd_eq_dest Hmdp1 Hmdp2 Hall; eauto.
      clear Hall. 
      destruct H__ as (
          x_ & y2 & y3 & y4 & y5 & y6 & y7 & 
            Heq1 & Heq2 & Hmq1 & Hmq2 & 
            ecbs1 & ecbs2 & ed1 & ed2 & ws1 & ws2 &
            Hge1 & Hge2 & Hged1 & Hged2 & Hmede & Hte).
      subst x1. subst x2. 
      match goal with
        H: get OO1 absecblsid = ?e |- _ => assert (get O1 absecblsid = e)
      end.
      { eapply join_get_get_l; eauto.  }
      match goal with
        H: get OO2 absecblsid = ?e |- _ => assert (get O2 absecblsid = e)
      end.
      { eapply join_get_get_l; eauto. }
      l_rew21_inv1 (get O1 absecblsid).
      l_rew21_inv1 (get O2 absecblsid).
      rewrite H16 in Hged1. inverts Hged1.
      rewrite H6 in Hged2. inverts Hged2.
      match type of Hjo1' with
        context [absecblist ?els] => assert (get O1' absecblsid = Some (absecblist els))
      end.
      { eapply join_get_get_l; eauto. rewrite set_a_get_a. auto. }
      match type of Hjo2' with
        context [absecblist ?els] => assert (get O2' absecblsid = Some (absecblist els))
      end.
      { eapply join_get_get_l; eauto. rewrite set_a_get_a. auto. }
      unfolds.
      do 8 eexists.
      split; eauto. split; eauto.
      right. right.
      do 8 eexists.
      split; eauto. split; eauto.
      split; eauto.
      split; eauto.
      rewrite set_a_get_a. rewrite set_a_get_a.
      split; eauto.
      split; eauto. 
      
      lets H__: kme_kte_gethwait_eq Hkte_ Hkme Hmdp1 Hmdp2. 
      specializes H__; eauto.
      split.
      * (* mq_ed_equiv *)
        unfold mq_ed_equiv. unfold mq_ed_equiv in Hmede.
        destruct Hmede as (ms & mlen & pws1 & pwl2 & Hq1 & Hq2 & Heq).
        inverts Hq1. inverts Hq2.
        destruct H__ as (pr0 & H1__ & H2__ & H3__).
        assert (task_prio_id O1 x34 x31) by (unfolds; do 5 eexists; split; eauto).
        assert (task_prio_id O2 x19 x16) by (unfolds; do 5 eexists; split; eauto).
        assert (x34 = pr0) by (eapply prio_unique; eauto).
        assert (x19 = pr0) by (eapply prio_unique; eauto).
        subst.
        do 4 eexists. split; eauto. split; eauto.
        apply H1 in H3__. destruct H3__ as (_ & H3__).
        subst.
        lets H4__: H3__ H19 H9.
        destruct H4__ as (_ & _ & H4__ & _); subst.
        auto.
        eapply tidls_equiv_rm_preserve2; eauto.
        destruct H18; auto.
        destruct H8; auto.
        lets H___: qpend_get_expwl_before_sched_prio_preserved Hjo1 Hjo1'; eauto.
        lets H___: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto.
        lets H___: distinct_wait_tids H2 H16. destruct H___; auto.
        lets H___: distinct_wait_tids H3 H6. destruct H___; auto. 
      * match goal with
          H: get ecbs1 x_ = _ |- _ => lets H1_: distinct_wait_tids H; eauto
        end.
        match goal with
          H: get ecbs2 x_ = _ |- _ => lets H2_: distinct_wait_tids H; eauto
        end.
        simpljoin.
        eapply tidls_equiv_pp_preserve2; eauto.
        lets H___: qpend_get_expwl_before_sched_prio_preserved Hjo1 Hjo1'; eauto.
        lets H___: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto.
    + (* i0 <> i *)
      destruct Hall as (Hiff & Hall).
      specializes Hall; eauto.
      unfolds in Hall.
      simpljoin.
      match goal with
        H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
      end.
      * 
        unfolds. do 8 eexists. splits; eauto.
      *
        unfolds. do 8 eexists. splits; eauto.
      *
        unfolds.
        do 8 eexists. split; eauto. split; eauto. 
        right. right.
        match goal with
          H1: context [Valid_Addr ?a1], H2: context [Valid_Addr ?a2] |- _ =>
            rename a1 into eid'
        end.
        assert (Hn1: x1 <> eid').
        { eapply mq_idx_neq_ptr_neq; eauto. }
        assert (Hn2: x2 <> eid').
        { eapply mq_idx_neq_ptr_neq; eauto. }
        match type of Hjo1' with
          context [absecblist ?els'] =>
            assert (He1': get O1' absecblsid = Some (absecblist els'))
        end.
        {
          eapply join_get_get_l; eauto.
          rewrite set_a_get_a. auto.
        }
        match type of Hjo2' with
          context [absecblist ?els'] =>
            assert (He2': get O2' absecblsid = Some (absecblist els'))
        end.
        {
          eapply join_get_get_l; eauto.
          rewrite set_a_get_a. auto.
        }
        assert (get O1 absecblsid = Some (absecblist x20)).
        { eapply join_get_get_l; eauto. }
        assert (get O2 absecblsid = Some (absecblist x5)).
        { eapply join_get_get_l; eauto. }
        l_rew21_inv1 (get O1 absecblsid).
        l_rew21_inv1 (get O2 absecblsid).
        do 7 eexists.
        do 4 (split; eauto).
        rewrite set_a_get_a'; eauto. 
        rewrite set_a_get_a'; eauto.
        split; eauto. split; eauto. 
        split. 
        eapply mq_ed_equiv_pp_preserve2; eauto.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto.
    Unshelve.
    trivial.
    trivial.  
    exact TauAct.
    exact None.
    trivial.
    trivial.  
    exact TauAct.
    exact None.
Qed.

Lemma qpend_get_ex_pwl_before_sched_ctid_equiv_preserve2:
  forall rv_ptr1 rv_ptr2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') -> 
    qpend_get_ex_pwl_before_sched_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2.
  lets H1_: qpend_get_expwl_before_sched_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: qpend_get_expwl_before_sched_prio_preserved Hjo2 Hjo2'; eauto. 
  
  unfold ctid_equiv in *.
  unfold qpend_get_ex_pwl_before_sched_body in *.
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end). 
  assert (Hupd1: get OO1 curtid = get OO1' curtid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto. 
    introv Hf; inverts Hf.
    introv Hf; inverts Hf.
  } 
  lets Hct1': join_upd_get_same H1. 
  specializes Hct1'; eauto.
  assert (Hupd2: get OO2 curtid = get OO2' curtid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
    introv Hf; inverts Hf.
  }
  lets Hct2': join_upd_get_same H22. 
  specializes Hct2'; eauto. 
  do 2 eexists.
  split; eauto.
  split; eauto.
  do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
  introv Htpi1' Htpi2' Htd.

  lets Htpi1_: prio_preserved_tpi Htpi1' H1_.
  lets Htpi2_: prio_preserved_tpi Htpi2' H2_.
  lets H__: H23 Htpi1_ Htpi2_ Htd.
  auto.
  
Qed.

Lemma qpend_get_ex_pwl_before_sched_buffer_equiv_succ_preserve2:
  forall rv_ptr1 rv_ptr2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2' i0 pr, 
    buffer_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_get_ex_pwl_before_sched_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') -> 
    qpend_get_ex_pwl_before_sched_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') -> 
    mqdes_dom_qptr i0 rv_ptr1 O1 pr ->
    mqdes_dom_qptr i0 rv_ptr2 O2 pr ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hjo1' Hjo2' Hqn1 Hqn2 Hmd1 Hmd2. 
  lets Hpp1: qpend_get_expwl_before_sched_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpend_get_expwl_before_sched_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  rem_dis.
  rem_dis.
  inv_some.
  inv_some.
  inv_lst.
  inv_lst. 
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext OO1 absecblsid O1.
  kvext OO2 absecblsid O2.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  eapply buffer_equiv_nupd_preserve2; eauto.
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
Qed.

Lemma qpend_get_ex_pwl_before_sched_dteq_preserve2:
  forall td pr i act rv_ptr1 rv_ptr2 rv_post1 rv_post2 cst1 cst2 v1 v2 O1 O2 O1' O2' Of1 Of2 OO1 OO2 OO1' OO2', 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    mqdes_dom_qptr i rv_ptr1 O1 pr ->
    mqdes_dom_qptr i rv_ptr2 O2 pr -> 
    qpend_get_ex_pwl_before_sched_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') -> 
    qpend_get_ex_pwl_before_sched_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hde Hkte Hkme Hjo1 Hjo2 Hjo1' Hjo2'. 
  introv Hmd1 Hmd2 Hpost1 Hpost2. 
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  lets H__: qpend_get_ex_pwl_before_sched_knl_mq_equiv_preserve2 Hkde Hkte Hkme Hmd1 Hmd2.
  lets H_: H__ Hpost1 Hpost2; eauto.
  splits.
  -
    eapply qpend_get_ex_pwl_before_sched_ctid_equiv_preserve2; eauto.
  -
    lets H1__: qpend_get_ex_pwl_before_sched_bufs_same Hjo1 Hjo1' Hpost1.
    lets H2__: qpend_get_ex_pwl_before_sched_bufs_same Hjo2 Hjo2' Hpost2.
    simpljoin. 
    eapply bufs_equiv_preserve2; eauto.
  -
    unfold kernel_data_equiv.
    splits.
    + (* kernel_task_equiv *) 
      destruct H_. auto. 
    + (* kernel_mq_equiv *)
      destruct H_. auto. 
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

    (* + (* kports_equiv *)  *)
    (*   destructs Hkde. *)
    (*   eapply kprts_equiv_same_prts_preserve2; eauto. *)
    (*   eapply qtimedpost_exwt_succ_kpid_same; eauto. *)
    (*   eapply qtimedpost_exwt_succ_kpid_same; eauto. *)
    (*   eapply qtimedpost_exwt_succ_dpid_same; eauto. *)
    (*   eapply qtimedpost_exwt_succ_dpid_same; eauto. *)

    + (* cap_equiv *)
      destructs Hkde.

      eapply qpend_get_ex_pwl_before_sched_buffer_equiv_succ_preserve2; eauto.
    + destructs Hkde.
      eapply cap_equiv_preserve2; eauto.
      eapply qpend_get_ex_pwl_before_sched_cpid_same; eauto.
      eapply qpend_get_ex_pwl_before_sched_cpid_same; eauto.

      eapply qpend_get_ex_pwl_before_sched_mqptr_iff; eauto.
      eapply qpend_get_ex_pwl_before_sched_mqptr_iff; eauto.
      
  -
    eapply cde_prio_preserved_preserve2; eauto.
    eapply qpend_get_expwl_before_sched_prio_preserved with (O0:=OO1); eauto.
    eapply qpend_get_expwl_before_sched_prio_preserved; eauto.
Qed.

Lemma qpend_block_bufs_same:
  forall vp v O0 act v' O0' Of O O',
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hovf Hjo Hjo'.
  inverts Hovf.
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

Lemma qpend_block_dpid_same: 
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hovf Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hovf. simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpend_block_kpid_same: 
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->  
    join O0 Of O ->
    join O0' Of O' ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpend_block_same_prt_ecbs:
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    same_prt_ecbs O O'. 
Proof.
  introv Hovf Hjo Hjo'.
  unfolds.
  introv Hg Hg'.
  intros.
  inverts Hovf.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  split.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x5)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context[ absecblist ?els' ] => assert (H__: get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a.
    auto.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. unfold get in *. unfold EcbMap in *.
      l_rew21_inv1 (EcbMod.get els eid).
    + rewrite set_a_get_a'; eauto.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x5)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context [ absecblist ?els' ] => assert (get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a. auto.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite set_a_get_a in Hge. inverts Hge.
    + rewrite set_a_get_a' in Hge; eauto.
Qed.

Lemma qpend_block_cpid_same:
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O cspaceid = get O' cspaceid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpend_block_same:
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O absmqattrid = get O' absmqattrid.  
Proof.
  introv Hovf Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hovf. simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed. 

Lemma qpend_block_mqptr_impl: 
  forall vp v O act v' O' O0 O0' Of, 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hovf Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  assert (Hovf':=Hovf).
  inverts Hovf.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qpend_block_same Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpend_block_mqptr_iff: 
  forall vp v O act v' O' O0 O0' Of, 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hovf Hjo Hjo'.
  intros.
  split.
  - eapply qpend_block_mqptr_impl; eauto.
  -
    introv Hmp'.
    unfold mq_ptr in *.
    assert (Hovf':=Hovf).
    inverts Hovf.
    simpljoin.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: qpend_block_same Hjo Hjo'; eauto. 
    }
    rewrite H0 in H.
    do 8 eexists; eauto.
Qed.

Lemma qpend_block_mqref_preserve: 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hovfb Hjo Hjo'.
  unfolds in Hovfb.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
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

Lemma qpend_block_qprt_preserve: 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
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

Lemma q_dom_diff_eid_neq: 
  forall i0 eid O pr mqs i td eid' x2 x3 x4 x5 x6 x7, 
    mqdes_dom_qptr i0 (Vptr eid) O pr ->
    mqidx_in_dom i td = true ->
    dom_for_prio pr <> td -> 
    get O absmqattrid = Some (absmqattr mqs) -> 
    get mqs i = Some (Valid_Addr eid', x2, x3, x4, x5, x6, x7) ->
    eid <> eid'.
Proof.
  introv Hdqp Hid Hne Hgmqs Hgq.
  unfolds in Hdqp.
  destruct Hdqp as (Hid' & Hqp).
  unfold mq_ptr in *.
  simpljoin.
  l_rew21_inv1 (get O absmqattrid).
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  lets H_: mq_ecb_ref_distinct H0 Hgq; eauto. 
  casetac i0 i Ht Hf.
  - subst.            
    lets Hf: mqidx_diff_dom Hid Hid'; eauto. 
  - auto. 
Qed. 
  
Lemma qpend_block_knl_mq_equiv_preserve2:
  forall td O1 O2 vp1 vp2 O10 O20 act v v1 v2 O10' O20' Of1 Of2 O1' O2' i0 pr t1 t2, 
    kernel_data_equiv td O1 O2 -> 
    (* ctid_equiv td O1 O2 ->  *)
    (* kernel_task_equiv (dom_for_prio pr) O1 O2 ->  *)
    (* kernel_mq_equiv (dom_for_prio pr) O1 O2 ->  *)
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    qpend_block_body (vp1 :: v :: nil) O10 act (v1, Some O10') ->
    qpend_block_body (vp2 :: v :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    (kernel_task_equiv td O1' O2' /\ kernel_mq_equiv td O1' O2').       
Proof.
  introv Hkde Hd1 Hd2 Hct1 Hct2 Htpi1 Htpi2.
  introv Hovf1 Hovf2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfolds in Hkde.
  destruct Hkde as (Hkte & Hkme & Hpe & Hkpe & Hcpe).
  unfolds in Hkte.
  destruct Hkte as (tcbs1 & tcbs2 & Hgt1 & Hgt2 & Hall).
  casetac (dom_for_prio pr) td Ht Hf.
  -
    subst.
    split.
    + 
      unfolds.
      assert (Hovf1_ := Hovf1).
      assert (Hovf2_ := Hovf2).
      inverts Hovf1. inverts Hovf2. simpljoin.
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      kvext0 O10 abstcblsid O1.
      kvext0 O20 abstcblsid O2. 
        
      l_rew21_inv1 (get O1 abstcblsid).
      l_rew21_inv1 (get O2 abstcblsid).
      kvext0 O10 absecblsid O1.
      kvext0 O20 absecblsid O2.
      kvext0 O10 curtid O1.
      kvext0 O20 curtid O2. 
      l_rew21_inv1 (get O1 curtid).
      l_rew21_inv1 (get O2 curtid).

      match type of Hjo1' with context [ abstcblist ?tcbs] => exists tcbs end.
      match type of Hjo2' with context [ abstcblist ?tcbs] => exists tcbs end.
      split.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a'; auto.
      2: introv Hf; inverts Hf.
      rewrite set_a_get_a. auto.
      split.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a'; auto.
      2: introv Hf; inverts Hf.
      rewrite set_a_get_a. auto.
      introv Hdeq.
      lets Hteq0: Hall pr0 Hdeq.
      destruct Hteq0 as (Htpieq & Htcbeq).
      split.
      *
        eapply prio_preserved_tpieq_impl; eauto.
        lets H__: qpend_block_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpend_block_prio_preserved Hjo2 Hjo2'; eauto.
      *
        intros t1_ t2_.
        introv Hgett1 Hgett2.
        assert (Htpi1_: task_prio_id O1 x30 t1).
        { unfolds. do 5 eexists. split; eauto. }
        assert (Htpi2_: task_prio_id O2 x18 t2).
        { unfolds. do 5 eexists. split; eauto. }
        apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
        apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
        
        kvext_h Hjo1' abstcblsid O1'.
        kvext_h Hjo2' abstcblsid O2'.
      
        assert (Htcs: t1=t1_ /\ t2=t2_ \/ t1<>t1_ /\ t2<>t2_).
        {
          eapply prio_tid_corr_ext with (O1:=O1) (O2:=O2) (O1':=O1') (O2':=O2') (pr':=pr0); eauto.
          unfolds.
          do 5 eexists.
          split; eauto.  
          unfolds.
          do 5 eexists.
          split; eauto.
          lets H__: qpend_block_prio_preserved Hjo1 Hjo1'; eauto. 
          lets H__: qpend_block_prio_preserved Hjo2 Hjo2'; eauto. 
        }
        destruct Htcs as [Hteq | Htne].
        **
          destruct Hteq; subst.
          rewrite set_a_get_a in Hgett1. inverts Hgett1.
          rewrite set_a_get_a in Hgett2. inverts Hgett2.

          lets Heideq: kme_eptreq Hkme Hd1 Hd2; eauto.
          subst.
          specializes Htcbeq; eauto.
          simpljoin.
          splits; auto.
          destruct H18; destruct H7; simpljoin; tryfalse.
        **
          destruct Htne as (Htne1 & Htne2).
          rewrite set_a_get_a' in Hgett1; eauto.
          rewrite set_a_get_a' in Hgett2; eauto.
    +
      assert (Hkme_:=Hkme).
      unfold kernel_mq_equiv in Hkme.
      destruct Hkme as (mqs1 & mqs2 & H').
      simpljoin.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      lets H1_: qpend_block_same Hovf1' Hjo1 Hjo1'; eauto.
      lets H2_: qpend_block_same Hovf2' Hjo2 Hjo2'; eauto.
      rewrite H in H1_. symmetry in H1_.
      rewrite H0 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hid.
      sp_forall1' Ha. sp_forall1' Hb.
      split.
      {        
        destruct Hb. eauto.
      }
      (* mq_equiv *) 
      introv Hgetm1 Hgetm2.
      destruct Hb as (Hiff & Hb).
      lets H__: Hb Hgetm1 Hgetm2.
      unfold mq_equiv in *.
      simpljoin.
      do 8 eexists.
      split; eauto.
      split; eauto.
      match goal with
        H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
      end.
      * left; split; auto.
      * right; left; split; auto.
      * 
        lets Heideq: kme_eptreq Hkme_ Hd1 Hd2; eauto.
        subst.
        right; right.
        kvext_h Hjo1' absecblsid O1'.
        kvext_h Hjo2' absecblsid O2'. 
        match type of Hgetm1 with
          context [Valid_Addr ?eptr] => rename eptr into eid'
        end.
        kvext0 O10 absecblsid O1. 
        kvext0 O20 absecblsid O2. 
        l_rew12_inv2 (get O1 absecblsid).
        l_rew12_inv2 (get O2 absecblsid).
        lets Hpp1_: qpend_block_prio_preserved Hjo1 Hjo1'; eauto.
        lets Hpp2_: qpend_block_prio_preserved Hjo2 Hjo2'; eauto. 

        casetac x0 eid' Ht Hf.
        **
          subst. 
          do 7 eexists.
          split; eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          do 2 (rewrite set_a_get_a).
          split; eauto. 
          split; eauto. 

          do 2 (match goal with
                  H1: get ?x1 eid' = _, H2: get ?x2 eid' = _ |- _ =>
                    unify x1 x2; rewrite H1 in H2; inverts H2
                end).
          kvext0 O10 curtid O1.           
          l_rew21_inv1 (get O1 curtid).
          kvext0 O20 curtid O2. 
          l_rew21_inv1 (get O2 curtid). 

          split.
          unfold mq_ed_equiv in *.
          simpljoin.
          do 2 (match goal with H: absmsgq _ _ _ = _ |- _ => inverts H end).
          do 4 eexists.
          split; eauto. split; eauto.  
          eapply tidls_equiv_pp_preserve2; eauto.
          eapply tidls_equiv_cons_preserve2; eauto. 
          
        **
          do 7 eexists.
          split; eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          do 2 (rewrite set_a_get_a'; eauto).
          split; eauto.
          split; eauto.
          split. 
          eapply mq_ed_equiv_pp_preserve2; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
  -
    lets Hpp1: qpend_block_prio_preserved Hjo1 Hjo1'; eauto.
    lets Hpp2: qpend_block_prio_preserved Hjo2 Hjo2'; eauto.
    split.
    +
      unfold kernel_task_equiv in *.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      kvext_h Hjo1' abstcblsid O1'.
      kvext_h Hjo2' abstcblsid O2'. 
      do 2 eexists.
      split; eauto.
      split; eauto.
      
      introv Hd'.
      specialize (Hall pr0 Hd').
      destruct Hall as (Htpieq & Htcbeq).
      split.
      *
        split.
        **
          eapply prio_preserved_tpieq_impl with (O1:=O1) (O2:=O2) (O1':=O1') (O2':=O2'); eauto.
        **
          eapply prio_preserved_tpieq_impl; eauto.
      *
        kvext0 O10 curtid O1.
        kvext0 O20 curtid O2. 
        l_rew21_inv1 (get O1 curtid).
        l_rew21_inv1 (get O2 curtid).
        intros t1_ t2_. 
        introv Hgett1 Hgett2.
        assert (Htpi1_: task_prio_id O1' pr0 t1_).
        { unfolds. do 5 eexists. split; eauto. }
        assert (Htpi2_: task_prio_id O2' pr0 t2_).
        { unfolds. do 5 eexists. split; eauto. }
        lets Htne1: pr_diff_dom_tid_neq Htpi1 Htpi1_; eauto.
        specializes Htne1; eauto.
        rewrite <- Hd' in Hf; auto.
        lets Htne2: pr_diff_dom_tid_neq Htpi2 Htpi2_; eauto.
        specializes Htne2; eauto.
        rewrite <- Hd' in Hf; auto.
        rewrite set_a_get_a' in Hgett1; eauto.
        rewrite set_a_get_a' in Hgett2; eauto.
        kvext0 O10 abstcblsid O1.
        kvext0 O20 abstcblsid O2. 
        l_rew21_inv1 (get O1 abstcblsid).
        l_rew21_inv1 (get O2 abstcblsid).
        lets H__: Htcbeq Hgett1 Hgett2.
        auto. 
    +
      assert (Hkme_:=Hkme).
      unfold kernel_mq_equiv in Hkme.
      destruct Hkme as (mqs1 & mqs2 & H').
      simpljoin.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      lets H1_: qpend_block_same Hovf1' Hjo1 Hjo1'; eauto.
      lets H2_: qpend_block_same Hovf2' Hjo2 Hjo2'; eauto.
      rewrite H in H1_. symmetry in H1_.
      rewrite H0 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hd'.      
      match goal with
        H: forall (i:int32), _ |- _ => lets Hc: H Hd'; eauto
      end.        
      destruct Hc as (Hiff & Hc).
      split.
      {
        auto.
      }
      introv Hgm1 Hgm2.      
      lets H__: Hc Hgm1 Hgm2.      
      unfold mq_equiv in *.
      simpljoin.
      do 8 eexists.
      split; eauto.
      split; eauto.
      match goal with
        H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
      end.
      * left; auto.
      * right; left; auto.
      * right; right.
        match type of Hgm1 with context [Valid_Addr ?eid] => rename eid into eid' end.
        kvext0 O10 absecblsid O1.
        kvext0 O20 absecblsid O2. 
        l_rew21_inv1 (get O1 absecblsid).
        l_rew21_inv1 (get O2 absecblsid).
        
        do 7 eexists.
        split; eauto.
        split; eauto.
        kvext_h Hjo1' absecblsid O1'. 
        kvext_h Hjo2' absecblsid O2'. 
        split; eauto.
        split; eauto.
        
        lets H1__: q_dom_diff_eid_neq Hd1 Hd'; eauto.  
        specializes H1__; eauto.
        lets H2__: q_dom_diff_eid_neq Hd2 Hd'; eauto.
        specializes H2__; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.

        split; eauto.
        split; eauto.
        split.
        eapply mq_ed_equiv_pp_preserve2; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
Qed.

Lemma qpend_block_ctid_same:
  forall vp v O0 act O0' v' Of O O', 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    get O curtid = get O' curtid. 
Proof.
  introv Hovf Hjo Hjo'.
  inverts Hovf.
  simpljoin.
  match goal with
    H: ?f _ = ?f _ |- _ => inverts H
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  rewrite set_a_get_a'; eauto.
  2: {introv Hf; inverts Hf. }
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpend_block_buffer_equiv_succ_preserve2:
  forall rv_ptr1 rv_ptr2 rv_post td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2' i0 pr, 
    buffer_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_block_body (rv_ptr1 :: rv_post :: nil) OO1 act (v1, Some OO1') ->
    qpend_block_body (rv_ptr2 :: rv_post :: nil) OO2 act (v2, Some OO2') ->
    mqdes_dom_qptr i0 rv_ptr1 O1 pr ->
    mqdes_dom_qptr i0 rv_ptr2 O2 pr ->
    buffer_equiv td O1' O2'.
Proof.
  introv Hbe Hjo1 Hjo2 Hjo1' Hjo2' Hqn1 Hqn2 Hmd1 Hmd2. 
  lets Hpp1: qpend_block_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpend_block_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  rem_dis.
  {rem_dis.
  inv_some.
  inv_some.
  inv_lst.
  inv_lst. 
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext OO1 absecblsid O1.
  kvext OO2 absecblsid O2.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  eapply buffer_equiv_nupd_preserve2; eauto.
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto.
  }}
  {rem_dis.
  inv_some.
  inv_some.
  inv_lst.
  inv_lst. 
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext OO1 absecblsid O1.
  kvext OO2 absecblsid O2.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  eapply buffer_equiv_nupd_preserve2; eauto.
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto.
  }}
Qed.

Lemma qpend_block_dteq_preserve2:  
  forall i cst1 cst2 O1 O2 i0 vp1 vp2 pr v O10 O20 act v1 v2 O10' O20' O1' O2' Of1 Of2 t1 t2, 
    data_equiv_tskd i cst1 cst2 O1 O2 ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    qpend_block_body (vp1 :: v :: nil) O10 act (v1, Some O10') ->
    qpend_block_body (vp2 :: v :: nil) O20 act (v2, Some O20') ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    data_equiv_tskd i cst1 cst2 O1' O2'.
Proof.
  introv Hde Hd1 Hd2 Hgct1 Hgct2 Htpi1 Htpi2 Hovf1 Hovf2. 
  introv Hdi1 Hdi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  splits.

  (* ctid_equiv *) 
  eapply prio_preserved_ctid_eq_preserved; eauto.
  lets H__: qpend_block_ctid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_ctid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_block_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_prio_preserved Hjo2 Hjo2'; eauto.                           

  (* bufs_equiv *) 
  lets H1_: qpend_block_bufs_same Hjo1 Hjo1'; eauto.
  lets H2_: qpend_block_bufs_same Hjo2 Hjo2'; eauto. 
  destruct H1_. destruct H2_. 
  eapply bufs_equiv_preserve2; eauto.

  (* kernel_data_equiv *)
  lets H__: qpend_block_knl_mq_equiv_preserve2 Hovf1 Hovf2 Hjo1 Hjo2 Hjo1' Hjo2'; eauto.
  destruct H__.
  destructs Hkde.
  unfolds.
  splits; auto. 

  (* ports_equiv *) 
  eapply ports_equiv_same_prts_preserve2; eauto.          
  lets H__: qpend_block_dpid_same Hjo1 Hjo1'; eauto. 
  lets H__: qpend_block_dpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_block_kpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_kpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_block_same_prt_ecbs Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_same_prt_ecbs Hjo2 Hjo2'; eauto. 
  lets H__: qpend_block_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_prio_preserved Hjo2 Hjo2'; eauto.

  (* (* kports_equiv *)  *)
  (* eapply kprts_equiv_same_prts_preserve2 with (O1:=O1) (O2:=O2); eauto. *)
  (* lets H__: qpend_block_kpid_same Hjo1 Hjo1'; eauto. *)
  (* lets H__: qpend_block_kpid_same Hjo2 Hjo2'; eauto. *)
  (* lets H__: qpend_block_dpid_same Hjo1 Hjo1'; eauto. *)
  (* lets H__: qpend_block_dpid_same Hjo2 Hjo2'; eauto. *)

  eapply qpend_block_buffer_equiv_succ_preserve2; eauto.
  (* cap_equiv *) 
  eapply cap_equiv_preserve2; eauto. 
  lets H__: qpend_block_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_cpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_block_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_mqptr_iff Hjo2 Hjo2'; eauto.

  (* client_data_equiv *) 
  eapply cde_prio_preserved_preserve2; eauto. 
  lets H__: qpend_block_prio_preserved Hjo1 Hjo1'; eauto. 
  lets H__: qpend_block_prio_preserved Hjo2 Hjo2'; eauto. 
  
Qed.

Lemma qpend_block_mqptr_impl': 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O idx objp -> mq_ptr O' idx objp. 
Proof.
  introv Hovf Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  assert (Hovf':=Hovf).
  inverts Hovf.
  simpljoin.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qpend_block_same Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpend_block_mqd_impl: 
  forall vp v O v' O' O0 O0' Of act pr, 
    qpend_block_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val),
      mqdes_dom_qptr idx objp O pr -> mqdes_dom_qptr idx objp O' pr.
Proof.
  introv Hovf Hjo Hjo' Hd.
  unfold mqdes_dom_qptr in *.
  simpljoin.
  split; auto.
  eapply qpend_block_mqptr_impl'; eauto. 
Qed.

Lemma qpend_to_bufs_same:
  forall vp v O0 act v' O0' Of O O',
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hovf Hjo Hjo'.
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
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

Lemma qpend_to_dpid_same: 
  forall vp v O0 act v' O0' Of O O', 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hovf Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hovf. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpend_to_kpid_same: 
  forall vp v O0 act v' O0' Of O O', 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->  
    join O0 Of O ->
    join O0' Of O' ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpend_to_same_prt_ecbs:
  forall vp v O0 act v' O0' Of O O', 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    same_prt_ecbs O O'. 
Proof.
  introv Hovf Hjo Hjo'.
  unfolds.
  introv Hg Hg'.
  intros.
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  split.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x4)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context[ absecblist ?els' ] => assert (H__: get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a.
    auto.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. unfold get in *. unfold EcbMap in *.
      l_rew21_inv1 (EcbMod.get els eid).
    + rewrite set_a_get_a'; eauto.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x4)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context [ absecblist ?els' ] => assert (get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a. auto.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite set_a_get_a in Hge. inverts Hge.
    + rewrite set_a_get_a' in Hge; eauto.
Qed.

Lemma qpend_to_cpid_same:
  forall vp v O0 act v' O0' Of O O', 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') -> 
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

Lemma qpend_to_same:
  forall vp v O0 act v' O0' Of O O', 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O absmqattrid = get O' absmqattrid.  
Proof.
  introv Hovf Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hovf. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed. 

Lemma qpend_to_mqptr_impl: 
  forall vp v O act v' O' O0 O0' Of, 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hovf Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  assert (Hovf':=Hovf).
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qpend_to_same Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpend_to_mqptr_iff: 
  forall vp v O act v' O' O0 O0' Of, 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hovf Hjo Hjo'.
  intros.
  split.
  - eapply qpend_to_mqptr_impl; eauto.
  -
    introv Hmp'.
    unfold mq_ptr in *.
    assert (Hovf':=Hovf).
    inverts Hovf.
    simpljoin.
    match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: qpend_to_same Hjo Hjo'; eauto. 
    }
    rewrite H0 in H.
    do 8 eexists; eauto.
Qed.

Lemma qpend_to_mqref_preserve: 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hovfb Hjo Hjo'.
  unfolds in Hovfb.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
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

Lemma qpend_to_qprt_preserve: 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
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

Lemma qpend_to_knl_mq_equiv_preserve2:
  forall td O1 O2 vp1 vp2 O10 O20 act v1 v2 v1' v2' O10' O20' Of1 Of2 O1' O2' i0 pr t1 t2, 
    kernel_data_equiv td O1 O2 -> 
    (* ctid_equiv td O1 O2 ->  *)
    (* kernel_task_equiv (dom_for_prio pr) O1 O2 ->  *)
    (* kernel_mq_equiv (dom_for_prio pr) O1 O2 ->  *)
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    qpend_to_body (vp1 :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_to_body (vp2 :: v2 :: nil) O20 act (v2', Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    (kernel_task_equiv td O1' O2' /\ kernel_mq_equiv td O1' O2').       
Proof.
  introv Hkde Hd1 Hd2 Hct1 Hct2 Htpi1 Htpi2.
  introv Hovf1 Hovf2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfolds in Hkde.
  destruct Hkde as (Hkte & Hkme & Hpe & Hkpe & Hcpe).
  unfolds in Hkte.
  destruct Hkte as (tcbs1 & tcbs2 & Hgt1 & Hgt2 & Hall).
  casetac (dom_for_prio pr) td Ht Hf.
  -
    subst.
    split.
    + 
      unfolds.
      assert (Hovf1_ := Hovf1).
      assert (Hovf2_ := Hovf2).
      inverts Hovf1. inverts Hovf2. simpljoin.
      do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      kvext0 O10 abstcblsid O1.
      kvext0 O20 abstcblsid O2. 
        
      l_rew21_inv1 (get O1 abstcblsid).
      l_rew21_inv1 (get O2 abstcblsid).
      kvext0 O10 absecblsid O1.
      kvext0 O20 absecblsid O2.
      kvext0 O10 curtid O1.
      kvext0 O20 curtid O2. 
      l_rew21_inv1 (get O1 curtid).
      l_rew21_inv1 (get O2 curtid).

      match type of Hjo1' with context [ abstcblist ?tcbs] => exists tcbs end.
      match type of Hjo2' with context [ abstcblist ?tcbs] => exists tcbs end.
      split.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a'; auto.
      2: introv Hf; inverts Hf.
      rewrite set_a_get_a. auto.
      split.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a'; auto.
      2: introv Hf; inverts Hf.
      rewrite set_a_get_a. auto.
      introv Hdeq.
      lets Hteq0: Hall pr0 Hdeq.
      destruct Hteq0 as (Htpieq & Htcbeq).
      split.
      *
        eapply prio_preserved_tpieq_impl; eauto.
        lets H__: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto.
      *
        intros t1_ t2_.
        introv Hgett1 Hgett2.
        assert (Htpi1_: task_prio_id O1 x24 t1).
        { unfolds. do 5 eexists. split; eauto. }
        assert (Htpi2_: task_prio_id O2 x13 t2).
        { unfolds. do 5 eexists. split; eauto. }
        apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
        apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
        
        kvext_h Hjo1' abstcblsid O1'.
        kvext_h Hjo2' abstcblsid O2'.
      
        assert (Htcs: t1=t1_ /\ t2=t2_ \/ t1<>t1_ /\ t2<>t2_).
        {
          eapply prio_tid_corr_ext with (O1:=O1) (O2:=O2) (O1':=O1') (O2':=O2') (pr':=pr0); eauto.
          unfolds.
          do 5 eexists.
          split; eauto.  
          unfolds.
          do 5 eexists.
          split; eauto.
          lets H__: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto. 
          lets H__: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto. 
        }
        destruct Htcs as [Hteq | Htne].
        **
          destruct Hteq; subst.
          rewrite set_a_get_a in Hgett1. inverts Hgett1.
          rewrite set_a_get_a in Hgett2. inverts Hgett2.

          lets Heideq: kme_eptreq Hkme Hd1 Hd2; eauto.
          subst.
          specializes Htcbeq; eauto.
          simpljoin.
          splits; auto.
        **
          destruct Htne as (Htne1 & Htne2).
          rewrite set_a_get_a' in Hgett1; eauto.
          rewrite set_a_get_a' in Hgett2; eauto.
    +
      assert (Hkme_:=Hkme).
      unfold kernel_mq_equiv in Hkme.
      destruct Hkme as (mqs1 & mqs2 & H').
      simpljoin.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      lets H1_: qpend_to_same Hovf1' Hjo1 Hjo1'; eauto.
      lets H2_: qpend_to_same Hovf2' Hjo2 Hjo2'; eauto.
      rewrite H in H1_. symmetry in H1_.
      rewrite H0 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hid.
      sp_forall1' Ha. sp_forall1' Hb.
      split.
      {        
        destruct Hb. eauto.
      }
      (* mq_equiv *) 
      introv Hgetm1 Hgetm2.
      destruct Hb as (Hiff & Hb).
      lets H__: Hb Hgetm1 Hgetm2.
      unfold mq_equiv in *.
      simpljoin.
      do 8 eexists.
      split; eauto.
      split; eauto.
      match goal with
        H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
      end.
      * left; split; auto.
      * right; left; split; auto.
      * 
        lets Heideq: kme_eptreq Hkme_ Hd1 Hd2; eauto.
        subst.
        right; right.
        kvext_h Hjo1' absecblsid O1'.
        kvext_h Hjo2' absecblsid O2'. 
        match type of Hgetm1 with
          context [Valid_Addr ?eptr] => rename eptr into eid'
        end.
        kvext0 O10 absecblsid O1. 
        kvext0 O20 absecblsid O2. 
        l_rew12_inv2 (get O1 absecblsid).
        l_rew12_inv2 (get O2 absecblsid).
        lets Hpp1_: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto.
        lets Hpp2_: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto. 

        casetac x0 eid' Ht Hf.
        **
          subst. 
          do 7 eexists.
          split; eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          do 2 (rewrite set_a_get_a).
          split; eauto. 
          split; eauto. 

          do 2 (match goal with
                  H1: get ?x1 eid' = _, H2: get ?x2 eid' = _ |- _ =>
                    unify x1 x2; rewrite H1 in H2; inverts H2
                end).
          kvext0 O10 curtid O1.           
          l_rew21_inv1 (get O1 curtid).
          kvext0 O20 curtid O2. 
          l_rew21_inv1 (get O2 curtid). 

          split.
          unfold mq_ed_equiv in *.
          simpljoin.
          do 2 (match goal with H: absmsgq _ _ _ = _ |- _ => inverts H end).
          do 4 eexists.
          split; eauto. split; eauto.  
          eapply tidls_equiv_pp_preserve2; eauto.
          eapply tidls_equiv_rm_preserve2; eauto.
          lets H_: distinct_wait_tids H3 H17. destruct H_. auto.
          lets H_: distinct_wait_tids H12 H8. destruct H_. auto.
        **
          do 7 eexists.
          split; eauto.
          split; eauto.
          split; eauto.
          split; eauto.
          do 2 (rewrite set_a_get_a'; eauto).
          split; eauto.
          split; eauto.
          split. 
          eapply mq_ed_equiv_pp_preserve2; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
  -
    lets Hpp1: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto.
    lets Hpp2: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto.
    split.
    +
      unfold kernel_task_equiv in *.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      kvext_h Hjo1' abstcblsid O1'.
      kvext_h Hjo2' abstcblsid O2'. 
      do 2 eexists.
      split; eauto.
      split; eauto.
      
      introv Hd'.
      specialize (Hall pr0 Hd').
      destruct Hall as (Htpieq & Htcbeq).
      split.
      *
        split.
        **
          eapply prio_preserved_tpieq_impl with (O1:=O1) (O2:=O2) (O1':=O1') (O2':=O2'); eauto.
        **
          eapply prio_preserved_tpieq_impl; eauto.
      *
        kvext0 O10 curtid O1.
        kvext0 O20 curtid O2. 
        l_rew21_inv1 (get O1 curtid).
        l_rew21_inv1 (get O2 curtid).
        intros t1_ t2_. 
        introv Hgett1 Hgett2.
        assert (Htpi1_: task_prio_id O1' pr0 t1_).
        { unfolds. do 5 eexists. split; eauto. }
        assert (Htpi2_: task_prio_id O2' pr0 t2_).
        { unfolds. do 5 eexists. split; eauto. }
        lets Htne1: pr_diff_dom_tid_neq Htpi1 Htpi1_; eauto.
        specializes Htne1; eauto.
        rewrite <- Hd' in Hf; auto.
        lets Htne2: pr_diff_dom_tid_neq Htpi2 Htpi2_; eauto.
        specializes Htne2; eauto.
        rewrite <- Hd' in Hf; auto.
        rewrite set_a_get_a' in Hgett1; eauto.
        rewrite set_a_get_a' in Hgett2; eauto.
        kvext0 O10 abstcblsid O1.
        kvext0 O20 abstcblsid O2. 
        l_rew21_inv1 (get O1 abstcblsid).
        l_rew21_inv1 (get O2 abstcblsid).
        lets H__: Htcbeq Hgett1 Hgett2.
        auto. 
    +
      assert (Hkme_:=Hkme).
      unfold kernel_mq_equiv in Hkme.
      destruct Hkme as (mqs1 & mqs2 & H').
      simpljoin.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      lets H1_: qpend_to_same Hovf1' Hjo1 Hjo1'; eauto.
      lets H2_: qpend_to_same Hovf2' Hjo2 Hjo2'; eauto.
      rewrite H in H1_. symmetry in H1_.
      rewrite H0 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hd'.      
      match goal with
        H: forall (i:int32), _ |- _ => lets Hc: H Hd'; eauto
      end.        
      destruct Hc as (Hiff & Hc).
      split.
      {
        auto.
      }
      introv Hgm1 Hgm2.      
      lets H__: Hc Hgm1 Hgm2.      
      unfold mq_equiv in *.
      simpljoin.
      do 8 eexists.
      split; eauto.
      split; eauto.
      match goal with
        H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
      end.
      * left; auto.
      * right; left; auto.
      * right; right.
        match type of Hgm1 with context [Valid_Addr ?eid] => rename eid into eid' end.
        kvext0 O10 absecblsid O1.
        kvext0 O20 absecblsid O2. 
        l_rew21_inv1 (get O1 absecblsid).
        l_rew21_inv1 (get O2 absecblsid).
        
        do 7 eexists.
        split; eauto.
        split; eauto.
        kvext_h Hjo1' absecblsid O1'. 
        kvext_h Hjo2' absecblsid O2'. 
        split; eauto.
        split; eauto.
        
        lets H1__: q_dom_diff_eid_neq Hd1 Hd'; eauto.  
        specializes H1__; eauto.
        lets H2__: q_dom_diff_eid_neq Hd2 Hd'; eauto.
        specializes H2__; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.

        split; eauto.
        split; eauto.
        split.
        eapply mq_ed_equiv_pp_preserve2; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.        
Qed.

Lemma qpend_to_ctid_same:
  forall vp v O0 act O0' v' Of O O', 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    get O curtid = get O' curtid. 
Proof.
  introv Hovf Hjo Hjo'.
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with
    H: ?f _ = ?f _ |- _ => inverts H
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  rewrite set_a_get_a'; eauto.
  2: {introv Hf; inverts Hf. }
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpend_to_buffer_equiv_preserve2:
  forall rv_ptr1 rv_ptr2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2' i0 pr, 
    buffer_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_to_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_to_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    mqdes_dom_qptr i0 rv_ptr1 O1 pr ->
    mqdes_dom_qptr i0 rv_ptr2 O2 pr ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hjo1' Hjo2' Hqn1 Hqn2 Hmd1 Hmd2. 
  lets Hpp1: qpend_to_body_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpend_to_body_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  rem_dis.
  rem_dis.
  inv_some.
  inv_some.
  inv_lst.
  inv_lst. 
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext OO1 absecblsid O1.
  kvext OO2 absecblsid O2.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  eapply buffer_equiv_nupd_preserve2; eauto.
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
Qed.

Lemma qpend_to_dteq_preserve2:  
  forall i cst1 cst2 O1 O2 i0 vp1 vp2 pr v1 v2 O10 O20 act v1' v2' O10' O20' O1' O2' Of1 Of2 t1 t2, 
    data_equiv_tskd i cst1 cst2 O1 O2 ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    qpend_to_body (vp1 :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_to_body (vp2 :: v2 :: nil) O20 act (v2', Some O20') ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    data_equiv_tskd i cst1 cst2 O1' O2'.
Proof.
  introv Hde Hd1 Hd2 Hgct1 Hgct2 Htpi1 Htpi2 Hovf1 Hovf2. 
  introv Hdi1 Hdi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  splits.

  (* ctid_equiv *) 
  eapply prio_preserved_ctid_eq_preserved; eauto.
  lets H__: qpend_to_ctid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_to_ctid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto.                           

  (* bufs_equiv *) 
  lets H1_: qpend_to_bufs_same Hjo1 Hjo1'; eauto.
  lets H2_: qpend_to_bufs_same Hjo2 Hjo2'; eauto. 
  destruct H1_. destruct H2_. 
  eapply bufs_equiv_preserve2; eauto.

  (* kernel_data_equiv *)
  lets H__: qpend_to_knl_mq_equiv_preserve2 Hovf1 Hovf2 Hjo1 Hjo2 Hjo1' Hjo2'; eauto.
  destruct H__.
  destructs Hkde.
  unfolds.
  splits; auto. 

  (* ports_equiv *) 
  eapply ports_equiv_same_prts_preserve2; eauto.          
  lets H__: qpend_to_dpid_same Hjo1 Hjo1'; eauto. 
  lets H__: qpend_to_dpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_to_kpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_to_kpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_to_same_prt_ecbs Hjo1 Hjo1'; eauto.
  lets H__: qpend_to_same_prt_ecbs Hjo2 Hjo2'; eauto. 
  lets H__: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto.

  (* (* kports_equiv *)  *)
  (* eapply kprts_equiv_same_prts_preserve2 with (O1:=O1) (O2:=O2); eauto. *)
  (* lets H__: qpend_to_kpid_same Hjo1 Hjo1'; eauto. *)
  (* lets H__: qpend_to_kpid_same Hjo2 Hjo2'; eauto. *)
  (* lets H__: qpend_to_dpid_same Hjo1 Hjo1'; eauto. *)
  (* lets H__: qpend_to_dpid_same Hjo2 Hjo2'; eauto. *)

  eapply qpend_to_buffer_equiv_preserve2; eauto. 
  (* cap_equiv *) 
  eapply cap_equiv_preserve2; eauto. 
  lets H__: qpend_to_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_to_cpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_to_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qpend_to_mqptr_iff Hjo2 Hjo2'; eauto.

  (* client_data_equiv *) 
  eapply cde_prio_preserved_preserve2; eauto. 
  lets H__: qpend_to_body_prio_preserved Hjo1 Hjo1'; eauto. 
  lets H__: qpend_to_body_prio_preserved Hjo2 Hjo2'; eauto. 
Qed.

Lemma qpend_to_mqptr_impl': 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O idx objp -> mq_ptr O' idx objp. 
Proof.
  introv Hovf Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  assert (Hovf':=Hovf).
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qpend_to_same Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpend_to_mqd_impl: 
  forall vp v O v' O' O0 O0' Of act pr, 
    qpend_to_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val),
      mqdes_dom_qptr idx objp O pr -> mqdes_dom_qptr idx objp O' pr.
Proof.
  introv Hovf Hjo Hjo' Hd.
  unfold mqdes_dom_qptr in *.
  simpljoin.
  split; auto.
  eapply qpend_to_mqptr_impl'; eauto. 
Qed.

Lemma qpend_block_get_bufs_same:
  forall vp v O0 act v' O0' Of O O',
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hovf Hjo Hjo'.
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  split.
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
Qed.

Lemma qpend_block_get_dpid_same: 
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hovf Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hovf. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpend_block_get_kpid_same: 
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->  
    join O0 Of O ->
    join O0' Of O' ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpend_block_get_same_prt_ecbs:
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    same_prt_ecbs O O'. 
Proof.
  introv Hovf Hjo Hjo'.
  assert (get O absecblsid = get O' absecblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    inverts Hovf. simpljoin.
    match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
  }
  unfolds.
  intros.
  rewrite H in H0. rewrite H0 in H1.
  inverts H1.
  split; auto.
Qed.

Lemma qpend_block_get_cpid_same:
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') -> 
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
  introv Hf; inverts Hf.
Qed.

Lemma qpend_block_get_same:
  forall vp v O0 act v' O0' Of O O', 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O absmqattrid = get O' absmqattrid.  
Proof.
  introv Hovf Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hovf. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpend_block_get_mqptr_impl: 
  forall vp v O act v' O' O0 O0' Of, 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hovf Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  assert (Hovf':=Hovf).
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qpend_block_get_same Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpend_block_get_mqptr_iff: 
  forall vp v O act v' O' O0 O0' Of, 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hovf Hjo Hjo'.
  intros.
  split.
  - eapply qpend_block_get_mqptr_impl; eauto.
  -
    introv Hmp'.
    unfold mq_ptr in *.
    assert (Hovf':=Hovf).
    inverts Hovf.
    simpljoin.
    match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: qpend_block_get_same Hjo Hjo'; eauto. 
    }
    rewrite H0 in H.
    do 8 eexists; eauto.
Qed.

Lemma qpend_block_get_mqref_preserve: 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hovfb Hjo Hjo'.
  unfolds in Hovfb.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
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

Lemma qpend_block_get_qprt_preserve: 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
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

Lemma qpend_block_get_knl_mq_equiv_preserve2:
  forall td O1 O2 vp1 vp2 O10 O20 act v1 v2 v1' v2' O10' O20' Of1 Of2 O1' O2' i0 pr t1 t2, 
    kernel_data_equiv td O1 O2 -> 
    (* ctid_equiv td O1 O2 ->  *)
    (* kernel_task_equiv (dom_for_prio pr) O1 O2 ->  *)
    (* kernel_mq_equiv (dom_for_prio pr) O1 O2 ->  *)
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    qpend_block_get_body (vp1 :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_block_get_body (vp2 :: v2 :: nil) O20 act (v2', Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    (kernel_task_equiv td O1' O2' /\ kernel_mq_equiv td O1' O2').       
Proof.
  introv Hkde Hd1 Hd2 Hct1 Hct2 Htpi1 Htpi2.
  introv Hovf1 Hovf2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfolds in Hkde.
  destruct Hkde as (Hkte & Hkme & Hpe & Hkpe & Hcpe).
  unfolds in Hkte.
  destruct Hkte as (tcbs1 & tcbs2 & Hgt1 & Hgt2 & Hall).
  casetac (dom_for_prio pr) td Ht Hf.
  -
    subst.
    split.
    + 
      unfolds.
      assert (Hovf1_ := Hovf1).
      assert (Hovf2_ := Hovf2).
      inverts Hovf1. inverts Hovf2. simpljoin.
      do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      kvext0 O10 abstcblsid O1.
      kvext0 O20 abstcblsid O2. 
        
      l_rew21_inv1 (get O1 abstcblsid).
      l_rew21_inv1 (get O2 abstcblsid).
      kvext0 O10 curtid O1.
      kvext0 O20 curtid O2. 
      l_rew21_inv1 (get O1 curtid).
      l_rew21_inv1 (get O2 curtid).

      match type of Hjo1' with context [ abstcblist ?tcbs] => exists tcbs end.
      match type of Hjo2' with context [ abstcblist ?tcbs] => exists tcbs end.
      split.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a; auto.
      split.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a; auto.
      introv Hdeq.
      lets Hteq0: Hall pr0 Hdeq.
      destruct Hteq0 as (Htpieq & Htcbeq).
      split.
      *
        eapply prio_preserved_tpieq_impl; eauto.
        lets H__: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.
      *
        intros t1_ t2_.
        introv Hgett1 Hgett2.
        assert (Htpi1_: task_prio_id O1 x18 t1).
        { unfolds. do 5 eexists. split; eauto. }
        assert (Htpi2_: task_prio_id O2 x10 t2).
        { unfolds. do 5 eexists. split; eauto. }
        apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
        apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
        
        kvext_h Hjo1' abstcblsid O1'.
        kvext_h Hjo2' abstcblsid O2'.
      
        assert (Htcs: t1=t1_ /\ t2=t2_ \/ t1<>t1_ /\ t2<>t2_).
        {
          eapply prio_tid_corr_ext with (O1:=O1) (O2:=O2) (O1':=O1') (O2':=O2') (pr':=pr0); eauto.
          unfolds.
          do 5 eexists.
          split; eauto.  
          unfolds.
          do 5 eexists.
          split; eauto.
          lets H__: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto. 
          lets H__: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto. 
        }
        destruct Htcs as [Hteq | Htne].
        **
          destruct Hteq; subst.
          rewrite set_a_get_a in Hgett1. inverts Hgett1.
          rewrite set_a_get_a in Hgett2. inverts Hgett2.

          lets Heideq: kme_eptreq Hkme Hd1 Hd2; eauto.
          subst.
          specializes Htcbeq; eauto.
          simpljoin.
          splits; auto.
        **
          destruct Htne as (Htne1 & Htne2).
          rewrite set_a_get_a' in Hgett1; eauto.
          rewrite set_a_get_a' in Hgett2; eauto.
    +
      assert (Hkme_:=Hkme).
      unfold kernel_mq_equiv in Hkme.
      destruct Hkme as (mqs1 & mqs2 & H').
      simpljoin.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      lets H1_: qpend_block_get_same Hovf1' Hjo1 Hjo1'; eauto.
      lets H2_: qpend_block_get_same Hovf2' Hjo2 Hjo2'; eauto.
      rewrite H in H1_. symmetry in H1_.
      rewrite H0 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hid.
      sp_forall1' Ha. sp_forall1' Hb.
      split.
      {        
        destruct Hb. eauto.
      }
      (* mq_equiv *) 
      introv Hgetm1 Hgetm2.
      destruct Hb as (Hiff & Hb).
      lets H__: Hb Hgetm1 Hgetm2.
      unfold mq_equiv in *.
      simpljoin.
      do 8 eexists.
      split; eauto.
      split; eauto.
      match goal with
        H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
      end.
      * left; split; auto.
      * right; left; split; auto.
      * 
        lets Heideq: kme_eptreq Hkme_ Hd1 Hd2; eauto.
        subst.
        right; right.
        match type of Hgetm1 with
          context [Valid_Addr ?eptr] => rename eptr into eid'
        end.
        lets Hpp1_: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
        lets Hpp2_: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto. 

        casetac x0 eid' Ht Hf.
        **
          subst. 
          do 7 eexists.
          split; eauto.
          split; eauto.
          split; eauto.
          assert (get O1 absecblsid = get O1' absecblsid).
          {
            lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
            rewrite set_a_get_a'; eauto.
            introv Hf; inverts Hf.
          }
          inverts H1; eauto.
          split; eauto.
          assert (get O2 absecblsid = get O2' absecblsid).
          {
            lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
            rewrite set_a_get_a'; eauto.
            introv Hf; inverts Hf.
          }
          inverts H1; eauto.
          split; eauto. 
          split; eauto. 
          split; eauto. 

          kvext0 O10 curtid O1.           
          l_rew21_inv1 (get O1 curtid).
          kvext0 O20 curtid O2. 
          l_rew21_inv1 (get O2 curtid). 

          unfold mq_ed_equiv in *.
          simpljoin.
          do 4 eexists.
          split; eauto. split; eauto.  
          eapply tidls_equiv_pp_preserve2; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
          
        **
          do 7 eexists.
          split; eauto.
          split; eauto.
          split; eauto.
          assert (get O1 absecblsid = get O1' absecblsid).
          {
            lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
            rewrite set_a_get_a'; eauto.
            introv Hf'; inverts Hf'.
          }
          inverts H1; eauto.
          split; eauto.
          assert (get O2 absecblsid = get O2' absecblsid).
          {
            lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
            rewrite set_a_get_a'; eauto.
            introv Hf'; inverts Hf'.
          }
          inverts H1; eauto.
          split; eauto.
          split; eauto.
          split.
          eapply mq_ed_equiv_pp_preserve2; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
  -
    lets Hpp1: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
    lets Hpp2: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.
    split.
    +
      unfold kernel_task_equiv in *.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      kvext_h Hjo1' abstcblsid O1'.
      kvext_h Hjo2' abstcblsid O2'. 
      do 2 eexists.
      split; eauto.
      split; eauto.
      
      introv Hd'.
      specialize (Hall pr0 Hd').
      destruct Hall as (Htpieq & Htcbeq).
      split.
      *
        split.
        **
          eapply prio_preserved_tpieq_impl with (O1:=O1) (O2:=O2) (O1':=O1') (O2':=O2'); eauto.
        **
          eapply prio_preserved_tpieq_impl; eauto.
      *
        kvext0 O10 curtid O1.
        kvext0 O20 curtid O2. 
        l_rew21_inv1 (get O1 curtid).
        l_rew21_inv1 (get O2 curtid).
        intros t1_ t2_. 
        introv Hgett1 Hgett2.
        assert (Htpi1_: task_prio_id O1' pr0 t1_).
        { unfolds. do 5 eexists. split; eauto. }
        assert (Htpi2_: task_prio_id O2' pr0 t2_).
        { unfolds. do 5 eexists. split; eauto. }
        lets Htne1: pr_diff_dom_tid_neq Htpi1 Htpi1_; eauto.
        specializes Htne1; eauto.
        rewrite <- Hd' in Hf; auto.
        lets Htne2: pr_diff_dom_tid_neq Htpi2 Htpi2_; eauto.
        specializes Htne2; eauto.
        rewrite <- Hd' in Hf; auto.
        rewrite set_a_get_a' in Hgett1; eauto.
        rewrite set_a_get_a' in Hgett2; eauto.
        kvext0 O10 abstcblsid O1.
        kvext0 O20 abstcblsid O2. 
        l_rew21_inv1 (get O1 abstcblsid).
        l_rew21_inv1 (get O2 abstcblsid).
        lets H__: Htcbeq Hgett1 Hgett2.
        auto. 
    +
      assert (Hkme_:=Hkme).
      unfold kernel_mq_equiv in Hkme.
      destruct Hkme as (mqs1 & mqs2 & H').
      simpljoin.
      assert (Hovf1':=Hovf1).
      assert (Hovf2':=Hovf2).
      inverts Hovf1. inverts Hovf2.
      simpljoin.
      do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
      do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
      do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).
      
      lets H1_: qpend_block_get_same Hovf1' Hjo1 Hjo1'; eauto.
      lets H2_: qpend_block_get_same Hovf2' Hjo2 Hjo2'; eauto.
      rewrite H in H1_. symmetry in H1_.
      rewrite H0 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hd'.      
      match goal with
        H: forall (i:int32), _ |- _ => lets Hc: H Hd'; eauto
      end.        
      destruct Hc as (Hiff & Hc).
      split.
      {
        auto.
      }
      introv Hgm1 Hgm2.      
      lets H__: Hc Hgm1 Hgm2.      
      unfold mq_equiv in *.
      simpljoin.
      do 8 eexists.
      split; eauto.
      split; eauto.
      match goal with
        H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
      end.
      * left; auto.
      * right; left; auto.
      * right; right.
        match type of Hgm1 with context [Valid_Addr ?eid] => rename eid into eid' end.
        
        do 7 eexists.
        split; eauto.
        split; eauto. 
        split; eauto.
        assert (get O1 absecblsid = get O1' absecblsid).
        {
          lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
          rewrite set_a_get_a'; eauto.
          introv Hf'; inverts Hf'.
        }
        inverts H2; eauto.
        split; eauto.
        assert (get O2 absecblsid = get O2' absecblsid).
        {
          lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
          rewrite set_a_get_a'; eauto.
          introv Hf'; inverts Hf'.
        }
        inverts H2; eauto.
        split; eauto.
        split; eauto.
        split.
        eapply mq_ed_equiv_pp_preserve2; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.        
Qed.

Lemma qpend_block_get_ctid_same:
  forall vp v O0 act O0' v' Of O O', 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    get O curtid = get O' curtid. 
Proof.
  introv Hovf Hjo Hjo'.
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with
    H: ?f _ = ?f _ |- _ => inverts H
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qpend_block_get_buffer_equiv_preserve2:
  forall vp1 vp2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2' i0 pr, 
    buffer_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qpend_block_get_body (vp1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qpend_block_get_body (vp2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hjo1' Hjo2' Hqn1 Hqn2 Hmd1 Hmd2. 
  lets Hpp1: qpend_block_get_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpend_block_get_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  rem_dis.
  rem_dis.
  inv_some.
  inv_some.
  inv_lst.
  inv_lst. 
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  eapply buffer_equiv_nupd_preserve2; eauto.
  assert (get O1 absecblsid = get O1' absecblsid).
  {
    lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
  }
  inverts H5. auto.
  assert (get O2 absecblsid = get O2' absecblsid).
  {
    lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
  }
  inverts H5. auto.
Qed.

Lemma qpend_block_get_dteq_preserve2:  
  forall i cst1 cst2 O1 O2 i0 vp1 vp2 pr v1 v2 O10 O20 act v1' v2' O10' O20' O1' O2' Of1 Of2 t1 t2, 
    data_equiv_tskd i cst1 cst2 O1 O2 ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    qpend_block_get_body (vp1 :: v1 :: nil) O10 act (v1', Some O10') ->
    qpend_block_get_body (vp2 :: v2 :: nil) O20 act (v2', Some O20') ->
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    data_equiv_tskd i cst1 cst2 O1' O2'.
Proof.
  introv Hde Hd1 Hd2 Hgct1 Hgct2 Htpi1 Htpi2 Hovf1 Hovf2. 
  introv Hdi1 Hdi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  splits.

  (* ctid_equiv *) 
  eapply prio_preserved_ctid_eq_preserved; eauto.
  lets H__: qpend_block_get_ctid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_get_ctid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.                           

  (* bufs_equiv *) 
  lets H1_: qpend_block_get_bufs_same Hjo1 Hjo1'; eauto.
  lets H2_: qpend_block_get_bufs_same Hjo2 Hjo2'; eauto. 
  destruct H1_. destruct H2_. 
  eapply bufs_equiv_preserve2; eauto.

  (* kernel_data_equiv *)
  lets H__: qpend_block_get_knl_mq_equiv_preserve2 Hovf1 Hovf2 Hjo1 Hjo2 Hjo1' Hjo2'; eauto.
  destruct H__.
  destructs Hkde.
  unfolds.
  splits; auto. 

  (* ports_equiv *) 
  eapply ports_equiv_same_prts_preserve2; eauto.          
  lets H__: qpend_block_get_dpid_same Hjo1 Hjo1'; eauto. 
  lets H__: qpend_block_get_dpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_block_get_kpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_get_kpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_block_get_same_prt_ecbs Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_get_same_prt_ecbs Hjo2 Hjo2'; eauto. 
  lets H__: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto.

  (* (* kports_equiv *)  *)
  (* eapply kprts_equiv_same_prts_preserve2 with (O1:=O1) (O2:=O2); eauto. *)
  (* lets H__: qpend_block_get_kpid_same Hjo1 Hjo1'; eauto. *)
  (* lets H__: qpend_block_get_kpid_same Hjo2 Hjo2'; eauto. *)
  (* lets H__: qpend_block_get_dpid_same Hjo1 Hjo1'; eauto. *)
  (* lets H__: qpend_block_get_dpid_same Hjo2 Hjo2'; eauto. *)

  (* cap_equiv *) 
  eapply qpend_block_get_buffer_equiv_preserve2; eauto.
  eapply cap_equiv_preserve2; eauto. 
  lets H__: qpend_block_get_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_get_cpid_same Hjo2 Hjo2'; eauto.
  lets H__: qpend_block_get_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qpend_block_get_mqptr_iff Hjo2 Hjo2'; eauto.

  (* client_data_equiv *) 
  eapply cde_prio_preserved_preserve2; eauto. 
  lets H__: qpend_block_get_prio_preserved Hjo1 Hjo1'; eauto. 
  lets H__: qpend_block_get_prio_preserved Hjo2 Hjo2'; eauto. 
  
Qed.

Lemma qpend_block_get_mqptr_impl': 
  forall vp v O v' O' O0 O0' Of act, 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O idx objp -> mq_ptr O' idx objp. 
Proof.
  introv Hovf Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  assert (Hovf':=Hovf).
  inverts Hovf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qpend_block_get_same Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpend_block_get_mqd_impl: 
  forall vp v O v' O' O0 O0' Of act pr, 
    qpend_block_get_body (vp :: v :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val),
      mqdes_dom_qptr idx objp O pr -> mqdes_dom_qptr idx objp O' pr.
Proof.
  introv Hovf Hjo Hjo' Hd.
  unfold mqdes_dom_qptr in *.
  simpljoin.
  split; auto.
  eapply qpend_block_get_mqptr_impl'; eauto. 
Qed.

Lemma qacc_succ_cpid_same:
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    get O cspaceid = get O' cspaceid.  
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qacc_succ_ctid_same:
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    get O curtid = get O' curtid. 
Proof.
  introv Hjo Hjo' Hovf.
  inverts Hovf.
  simpljoin.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with
    H: ?f _ = ?f _ |- _ => inverts H
  end.
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  rewrite set_a_get_a'; eauto. introv Htemp. congruence.
Qed.

Lemma qacc_succ_bufs_same:
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hjo Hjo' Hovf.
  inverts Hovf.
  simpljoin.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  split.
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
  -
    symmetry.
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.
Qed.

Lemma qacc_succ_mqref_preserve: 
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' -> 
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    mq_ref_preserved O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get OO absmqattrid = Some (absmqattr mqs)
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

Lemma qacc_succ_qprt_preserve: 
  forall rv_ptr rv_post act v OO OO' Of O O',
    join OO Of O ->
    join OO' Of O' -> 
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    qprt_preserved O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  assert (Hor: get OO osdomainportid = Some (osdomainport dpl)
               \/ get Of osdomainportid = Some (osdomainport dpl)).
  {
    eapply join_get_or with (m:=O); eauto.
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

Lemma qacc_succ_dpid_same: 
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' -> 
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qacc_succ_kpid_same:
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hjo Hjo' Hpost.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qacc_succ_same_prt_ecbs:
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    same_prt_ecbs O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds.
  introv Hg Hg'.
  intros.
  inverts Hpost.
  simpljoin. 
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  split.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x1)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context[ (set OO absecblsid (absecblist ?els')) ] =>
        assert (H__: get (set OO absecblsid (absecblist els')) absecblsid = Some (absecblist els'))
    end.
    rewrite set_a_get_a. auto.
    match type of H__ with
      context [Some (absecblist ?els')] => 
        assert (Hge': get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    clear H__.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite Hge in H3. tryfalse. 
    + rewrite set_a_get_a'; eauto. 
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x1)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    match type of Hjo' with
      context[ (set OO absecblsid (absecblist ?els')) ] =>
        assert (H__: get (set OO absecblsid (absecblist els')) absecblsid = Some (absecblist els'))
    end.
    rewrite set_a_get_a. auto.
    match type of H__ with
      context [Some (absecblist ?els')] => 
        assert (Hge': get O' absecblsid = Some (absecblist els'))
    end.
    eapply join_get_get_l; eauto.
    clear H__.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite set_a_get_a in Hge. inverts Hge.
    + rewrite set_a_get_a' in Hge; eauto. 
Qed. 

Lemma qacc_succ_dom_impl:
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    dom_impl O O'. 
Proof.
  introv Hjo Hjo' Hpost.
  unfolds.
  intro x.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  destruct (get O x) eqn: E.
  2: {                    
    assert (get OO x = None).
    { eapply join_get_none_rev1; eauto. }
    assert (get Of x = None).
    { clear -Hjo E. eapply join_get_none_rev2; eauto. }
    eapply map_join_get_none'''; eauto.
    casetac absecblsid x Ht Hf.
    - subst. l_rew21_inv1 (get OO absecblsid).
    - rewrite set_a_get_a'; eauto. 
  }
  destruct a eqn: E'; 
    try (
        assert (Heq: get O x = get O' x)
        by
        (lets H__: join_get_same_l Hjo Hjo'; eauto; 
         casetac absecblsid x Ht Hf; 
         [ subst; 
           eapply join_get_get_l with (m:=O) in H2; eauto; 
           l_rew21_inv1 (get O absecblsid)
         |
           rewrite set_a_get_a'; eauto]); 
        rewrite E in Heq; 
        eexists; symmetry; eauto;
        fail).
  assert (Hor: get OO x = Some (absecblist m) \/ get Of x = Some (absecblist m)).
  {
    eapply join_get_or; eauto. 
  }
  destruct Hor as [Hl | Hr].
  2: {
    eexists; eapply join_get_get_r; eauto.
  }
  casetac absecblsid x Ht Hf.
  -
    subst. eexists. 
    eapply join_get_get_l; eauto.
    rewrite set_a_get_a; eauto.
  -
    exists m.
    eapply join_get_get_l; eauto. 
    rewrite set_a_get_a'; eauto.
Qed.   

Lemma qacc_succ_mqptr_impl: 
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hjo Hjo' Hpost Hmp'.
  unfold mq_ptr in *.
  inverts Hpost.
  simpljoin.
  match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
  inverts Hsome.
  2: { simpljoin; tryfalse. }
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qacc_succ_mqptr_iff: 
  forall rv_ptr rv_post act v OO OO' Of O O', 
    join OO Of O ->
    join OO' Of O' ->
    qacc_succ_body (rv_ptr :: rv_post :: nil) OO act (v, Some OO') ->
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp.
Proof.
  introv Hjo Hjo' Hpost.
  intros.
  split.
  - eapply qacc_succ_mqptr_impl; eauto.
  - introv Hmp.
    unfold mq_ptr in *.
    inverts Hpost.
    simpljoin.
    match goal with H: _ = _ /\ Some _ = Some _ \/ _ |- _ => destruct H as [(Heq & Hsome) | Hf] end.
    inverts Hsome.
    2: { simpljoin; tryfalse. }
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: join_get_same_l Hjo Hjo'; eauto.
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf. 
    }
    l_rew12_inv2 (get O absmqattrid). 
    do 8 eexists; eauto.
Qed.

Lemma qacc_succ_body_get_tcbid_eq:
  forall rv_ptr rv_post v act O O', 
    qacc_succ_body (rv_ptr :: rv_post :: nil) O act (v, Some O') ->
    get O abstcblsid = get O' abstcblsid. 
Proof.
  introv Hr.
  inverts Hr.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  inverts H1.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed.

Lemma  qacc_succ_body_ctid_equiv_preserve2:
  forall rv_ptr1 rv_ptr2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' -> 
    qacc_succ_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qacc_succ_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2.
  unfold ctid_equiv in *.
  unfold qacc_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get OO1 curtid = get OO1' curtid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  } 
  lets Hct1': join_upd_get_same H1. 
  specializes Hct1'; eauto.
  assert (Hupd2: get OO2 curtid = get OO2' curtid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hct2': join_upd_get_same H12. 
  specializes Hct2'; eauto. 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Htd.
  assert (Hupd1': get OO1' abstcblsid = get OO1 abstcblsid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Htpi1: tpi_upd_frm_preserved Htpi1' Hjo1' Hupd1' Hjo1.
  assert (Hupd2': get OO2' abstcblsid = get OO2 abstcblsid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Htpi2: tpi_upd_frm_preserved Htpi2' Hjo2' Hupd2' Hjo2.
  lets H__: H13 Htpi1 Htpi2. eapply H__; eauto.
Qed. 

Lemma qacc_succ_body_ibufs_equiv_preserve2:
  forall rv_ptr1 rv_ptr2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    ibufs_equiv td O1 O2 ->
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qacc_succ_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qacc_succ_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    ibufs_equiv td O1' O2'.
Proof.
  introv Hibfe Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2. 
  unfold ibufs_equiv in *. 
  unfold qacc_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get OO1 ibufsid = get OO1' ibufsid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf1': join_upd_get_same H1. 
  specializes Hbf1'; eauto.
  assert (Hupd2: get OO2 ibufsid = get OO2' ibufsid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf2': join_upd_get_same H12. 
  specializes Hbf2'; eauto.
Qed. 

Lemma qacc_succ_body_obufs_equiv_preserve2:
  forall rv_ptr1 rv_ptr2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    obufs_equiv td O1 O2 ->
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qacc_succ_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qacc_succ_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    obufs_equiv td O1' O2'.
Proof.
  introv Hobfe Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2. 
  unfold obufs_equiv in *. 
  unfold qacc_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get OO1 obufsid = get OO1' obufsid).
  {
    match goal with H: Some OO1' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf1': join_upd_get_same H1. 
  specializes Hbf1'; eauto.
  assert (Hupd2: get OO2 obufsid = get OO2' obufsid).
  {
    match goal with H: Some OO2' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf2': join_upd_get_same H12. 
  specializes Hbf2'; eauto.
Qed.                

Lemma qacc_succ_body_bufs_equiv_preserve2:
  forall rv_ptr1 rv_ptr2 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    bufs_equiv td O1 O2 ->
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qacc_succ_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qacc_succ_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    bufs_equiv td O1' O2'.
Proof.
  introv Hbfe Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2.
  unfolds in Hbfe.
  destruct Hbfe as (Hibe & Hobe).
  split.
  eapply qacc_succ_body_ibufs_equiv_preserve2; eauto.
  eapply qacc_succ_body_obufs_equiv_preserve2; eauto. 
Qed. 

Lemma qacc_succ_knl_mq_equiv_preserve2:
  forall rv_ptr1 rv_ptr2 pr i0 rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2', 
    kernel_mq_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qacc_succ_body (rv_ptr1 :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qacc_succ_body (rv_ptr2 :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    mqdes_dom_qptr i0 rv_ptr1 O1 pr ->
    mqdes_dom_qptr i0 rv_ptr2 O2 pr ->
    kernel_mq_equiv td O1' O2'.
Proof.
  introv Hkme Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2 Hmdp1 Hmdp2.
  unfold kernel_mq_equiv in *.
  assert (Hpost1_:= Hpost1).
  assert (Hpost2_ := Hpost2). 
  inverts Hpost1. 
  inverts Hpost2. 
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: Some _ = Some _ |- _ => inversion H; clear H end.
  match goal with H: Some _ = Some _ |- _ => inversion H; clear H end.
  assert (Hgeq1: get O1 absmqattrid = get O1' absmqattrid).
  {
    lets H__: join_get_same_l absmqattrid Hjo1 Hjo1'; eauto.
    subst OO1'.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.                    
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l absmqattrid Hjo2 Hjo2'; eauto.
    subst OO2'.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.  
  }
  rewrite <- Hgeq1. rewrite <- Hgeq2.
  do 2 eexists.
  splits; eauto.
  introv Hd.
  split.
  {
    match goal with H: forall _, _ |- _ => rename H into Ha; specializes Ha; eauto end.
    destruct Ha. auto.
  }
  (* mq_equiv *)
  introv Hget1 Hget2.
  assert (Hmqe0: mq_equiv td mq1 mq2 O1 O2).
  { eapply H13; eauto. }
  unfold mq_equiv in *.
  simpljoin.
  do 8 eexists. splits; eauto.
  match goal with H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]] end.
  - left. auto.
  - right. left. auto.
  -
    right; right.
    simpljoin. 
    match type of Hjo1' with context [absecblist ?els'] => exists els' end.
    match type of Hjo2' with context [absecblist ?els'] => exists els' end.
    assert (Hget1_: get O1 absecblsid = Some (absecblist x11)).
    {
      eapply join_get_get_l; eauto.
    }
    assert (Hget2_: get O2 absecblsid = Some (absecblist x5)).
    {
      eapply join_get_get_l; eauto. 
    }
    l_rew21_inv1 (get O1 absecblsid).
    l_rew21_inv1 (get O2 absecblsid).

    unfolds in Hmdp1. unfolds in Hmdp2.
    destruct Hmdp1 as (Hmid1 & Hmp1).
    destruct Hmdp2 as (Hmid2 & Hmp2).
    unfolds in Hmp1.  
    unfolds in Hmp2.
    simpljoin.
    protect Hgeq1.
    protect Hgeq2.
    l_rew21_inv1 (get O1 absmqattrid). 
    l_rew21_inv1 (get O2 absmqattrid).
    do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).                    
    do 2 (match goal with H: Vptr _ = Vptr _ |- _ => inverts H end). 
    (* do 2 (match goal with H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H end). *)

    casetac i i0 Ht Hf.
    +
      subst.
      rewrite H14 in Hget1. inverts Hget1.
      rewrite H2 in Hget2. inverts Hget2.
      rewrite H5 in H7. inverts H7.
      rewrite H10 in H6. inverts H6.
      do 5 eexists. 
      splits; eauto.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a; auto.
      eapply join_get_get_l; eauto.
      rewrite set_a_get_a; auto.
      rewrite set_a_get_a; eauto.
      rewrite set_a_get_a; eauto.
      unfold mq_ed_equiv in *.
      simpljoin.
      do 2 (match goal with H: absmsgq _ _ _  = absmsgq _ _ _ |- _ => inverts H end).
      do 4 eexists. 
      splits; eauto.
      eapply tidls_equiv_pp_preserve2; eauto.
      lets H'_: aqcc_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H'_: aqcc_succ_prio_preserved Hjo2 Hjo2'; eauto. 
      eapply tidls_equiv_pp_preserve2; eauto.
      lets H__: aqcc_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: aqcc_succ_prio_preserved Hjo2 Hjo2'; eauto. 
    +                      
      lets H1_: mq_ecb_ref_distinct Hf Hget1.
      specializes H1_; eauto.
      lets H2_: mq_ecb_ref_distinct Hf Hget2.
      specializes H2_; eauto.
      do 6 eexists. 
      split; eauto.
      split; eauto.
      split. eapply join_get_get_l; eauto. rewrite set_a_get_a; auto.
      split. eapply join_get_get_l; eauto. rewrite set_a_get_a; auto.
      split. rewrite set_a_get_a'; eauto.
      split. rewrite set_a_get_a'; eauto.
      split.
      unfold mq_ed_equiv in *.
      simpljoin.
      do 4 eexists. 
      splits; eauto.
      eapply tidls_equiv_pp_preserve2; eauto.
      lets H__: aqcc_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: aqcc_succ_prio_preserved Hjo2 Hjo2'; eauto. 
      eapply tidls_equiv_pp_preserve2; eauto.
      lets H__: aqcc_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: aqcc_succ_prio_preserved Hjo2 Hjo2'; eauto.
Qed.

Lemma qacc_succ_body_buffer_equiv_preserve2:
  forall vp rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2' i0 pr, 
    buffer_equiv td O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qacc_succ_body (vp :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qacc_succ_body (vp :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    mqdes_dom_qptr i0 vp O1 pr ->
    mqdes_dom_qptr i0 vp O2 pr ->
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hjo1' Hjo2' Hqn1 Hqn2 Hmd1 Hmd2. 
  lets Hpp1: aqcc_succ_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: aqcc_succ_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  rem_dis.
  rem_dis.
  inv_some.
  inv_some.
  inv_lst.
  inv_lst. 
  assert (Hbe_:=Hbe).
  unfolds in Hbe.
  simpljoin.
  kvext_h Hjo1' absecblsid O1'.
  kvext_h Hjo2' absecblsid O2'.
  kvext OO1 absecblsid O1.
  kvext OO2 absecblsid O2.
  l_rew21_inv1 (get O1 absecblsid).
  l_rew21_inv1 (get O2 absecblsid).
  eapply buffer_equiv_nupd_preserve2; eauto.
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
  {
    introv Hd. rewrite set_a_get_a'; eauto. 
    eapply mq_buffer_eid_diff; eauto. 
  }
Qed.

Lemma qacc_succ_body_dteq_preserve2:
  forall qid rv_post1 rv_post2 td O1 O2 OO1 OO2 act v1 v2 OO1' OO2' Of1 Of2 O1' O2' i0 pr  cst1 cst2, 
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    join OO1 Of1 O1 ->
    join OO2 Of2 O2 ->
    join OO1' Of1 O1' ->
    join OO2' Of2 O2' ->
    qacc_succ_body (Vptr qid :: rv_post1 :: nil) OO1 act (v1, Some OO1') ->
    qacc_succ_body (Vptr qid :: rv_post2 :: nil) OO2 act (v2, Some OO2') ->
    (* ctid_equiv td O1 O2 ->  *)
    (* kernel_task_equiv (dom_for_prio pr) O1 O2 ->  *)
    (* kernel_mq_equiv (dom_for_prio pr) O1 O2 ->  *)
    mqdes_dom_qptr i0 (Vptr qid) O1 pr ->
    mqdes_dom_qptr i0 (Vptr qid) O2 pr ->
    data_equiv_tskd td cst1 cst2 O1' O2'.   
Proof.
  introv Hde Hkme Hjo1 Hjo2 Hjo1' Hjo2' Hpost1 Hpost2  Hmd1 Hmd2. 
  unfold data_equiv_tskd in *.
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  split.
  eapply qacc_succ_body_ctid_equiv_preserve2; eauto.
  split.
  eapply qacc_succ_body_bufs_equiv_preserve2; eauto.
  split.
  2: {
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: aqcc_succ_prio_preserved Hpost1; eauto. 
    lets H__: aqcc_succ_prio_preserved Hpost2; eauto. 
  }
  unfold kernel_data_equiv.

  split.
  { (* kernel_task_equiv *)
    destructs Hkde.
    eapply knl_tsk_equiv_same_tls_preserve2; eauto.
    lets H__: join_get_same_l abstcblsid Hjo1 Hjo1'.
    eapply qacc_succ_body_get_tcbid_eq; eauto. 
    auto.
    lets H__: join_get_same_l abstcblsid Hjo2 Hjo2'. 
    eapply qacc_succ_body_get_tcbid_eq; eauto.
    auto. 
  }
  split.
  {
    (* kernel_mq_equiv *)

    clear Hkme.
    destructs Hkde.
    eapply qacc_succ_knl_mq_equiv_preserve2; eauto. 
  }
  split.
  { (* ports_equiv *)
    destructs Hkde. 
    eapply ports_equiv_same_prts_preserve2; eauto.                     
    
    lets H__: qacc_succ_dpid_same Hjo1 Hjo1'; eauto. 
    lets H__: qacc_succ_dpid_same Hjo2 Hjo2'; eauto. 
    lets H__: qacc_succ_kpid_same Hjo1 Hjo1'; eauto.
    lets H__: qacc_succ_kpid_same Hjo2 Hjo2'; eauto.
    lets H__: qacc_succ_same_prt_ecbs Hjo1 Hjo1'; eauto.
    lets H__: qacc_succ_same_prt_ecbs Hjo2 Hjo2'; eauto.
    lets H__: qacc_succ_dom_impl Hjo1 Hjo1'; eauto.
    lets H__: qacc_succ_dom_impl Hjo2 Hjo2'; eauto.
    lets H__: aqcc_succ_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: aqcc_succ_prio_preserved Hjo2 Hjo2'; eauto.
  }

  (* split.  *)
  (* { (* kports_equiv *) *)
  (*   destructs Hkde. *)
  (*   eapply kprts_equiv_same_prts_preserve2; eauto. *)
  (*   lets H__: qtimedpost_nowt_succ_kpid_same Hjo1 Hjo1'; eauto. *)
  (*   lets H__: qtimedpost_nowt_succ_kpid_same Hjo2 Hjo2'; eauto. *)
  (*   lets H__: qtimedpost_nowt_succ_dpid_same Hjo1 Hjo1'; eauto. *)
  (*   lets H__: qtimedpost_nowt_succ_dpid_same Hjo2 Hjo2'; eauto.    *)
  (* } *)

  (* cap_equiv *)
  destructs Hkde. split.
  eapply qacc_succ_body_buffer_equiv_preserve2; eauto.
  eapply cap_equiv_preserve2; eauto.
  lets H__: qacc_succ_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qacc_succ_cpid_same Hjo2 Hjo2'; eauto.

  lets H__: qacc_succ_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qacc_succ_mqptr_iff Hjo2 Hjo2'; eauto.
Qed.
