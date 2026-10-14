
Require Import base_tac. 
Require Import memory. 
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

Require Import FunctionalExtensionality.

Require Import math_auto. 
Require Import seplog_lemmas. 

Require Import ct_pp_lemmas. 

Set Keyed Unification.  

Ltac rmbprog hyp c :=
  match type of hyp with
    get _ _ = Some ((curs (hapi_code ?p)), (_, _)) => remember p as c
  end.

Ltac rmbprog' hyp c :=
  match type of hyp with
    nabt (set _ _ ((curs (hapi_code ?p)), (_, _))) => remember p as c
  end.

(* solve goals of the forms
     H: ~ (exists vo, END ... = END vo) /\ ... |- _
     and 
     H: ... /\ ABORT <> ABORT |- _ *)
Ltac solve_endabt :=
  simpljoin; solve
               [ tryfalse
               | false;
                 match goal with
                   H: ~(exists _, END _ = END _) |- _ => apply H; eexists; eauto 
                 | H: ABORT <> ABORT |- _ => apply H; auto
                 end]. 

Lemma aar_Oeq:
  forall vl O O' act v, asrt_and_ret vl O act (v, Some O') -> O = O'.
Proof.
  introv Haar.
  unfolds in Haar.
  simpljoin.
  inverts H2; simpljoin.
  inverts H0. auto.
  tryfalse. 
Qed.   

Lemma aar_veq:
  forall v1 v2 O O' act v, asrt_and_ret (v1::v2::nil) O act (v, Some O') -> v = Some v2.
Proof.
  introv Haar.
  unfolds in Haar.
  simpljoin.
  inverts H.
  auto. 
Qed. 

Lemma aar_veq12: 
  forall v1 v2 O act v O', 
    asrt_and_ret (v1 :: v2 :: nil) O act (v, Some O') ->
    v1 = v2. 
Proof.
  introv Haar.
  unfolds in Haar.
  simpljoin.
  match goal with H: _ :: _ :: nil = _ |- _ => inverts H end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
Qed.

Lemma skip_Oeq:
  forall vl O act v O', 
    spec_skip_step vl O act (v, Some O') ->
    O = O'. 
Proof.
  introv Hstep. 
  inverts Hstep.
  simpljoin.
  congruence.
Qed. 

Lemma get_msize_Oeq:
  forall vl O act v O', 
    mqsend_get_msgsize vl O act (Some v, Some O') ->
    O = O'. 
Proof.
  introv Hgs.
  unfolds in Hgs.
  simpljoin.
  inverts H3.
  simpljoin.
  congruence.
  simpljoin.
  tryfalse. 
Qed.

Lemma mqequiv_get_msize_veq: 
  forall pr O1 O2 i0 v1 v2 O10 O20 Of1 Of2 vo1 vo2 O10' O20' act, 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    mqd_in_dom i0 O1 pr ->
    mqd_in_dom i0 O2 pr ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    mqsend_get_msgsize (Vint32 i0 :: v1 :: nil) O10 act (vo1, Some O10') ->
    mqsend_get_msgsize (Vint32 i0 :: v2 :: nil) O20 act (vo2, Some O20') ->
    v1 = v2.
Proof.
  introv Hkme Hd1 Hd2 Hjo1 Hjo2 Hgs1 Hgs2.
  unfolds in Hkme.
  destruct Hkme as (att1 & att2 & Hatt1 & Hatt2 & Hall).
  unfolds in Hgs1.
  unfolds in Hgs2.
  simpljoin.
  match goal with H: (_ :: _ :: nil) = (_ :: _ :: nil) |- _ => inverts H end.
  match goal with H: (_ :: _ :: nil) = (_ :: _ :: nil) |- _ => inverts H end.
  rename x8 into i.
  unfolds in Hd1.
  assert (Hget': get O1 absmqattrid = Some (absmqattr x10)).
  { eapply join_sem1; eauto. }
  rewrite Hatt1 in Hget'.
  symmetry in Hget'. inverts Hget'.
  assert (Hget': get O2 absmqattrid = Some (absmqattr x1)).
  { eapply join_sem1; eauto. }
  rewrite Hatt2 in Hget'.
  symmetry in Hget'. inverts Hget'.
  lets H_: Hall Hd1.
  destruct H_ as (Hiff & Hall_).
  specializes Hall_; eauto. 
  unfold mq_equiv in Hall_.
  destruct Hall_ as (eo1 & eo2 & wtp & flgs & mms & msz & cms & csltidxs & Heq1 & Heq2 & _).
  inverts Heq1. inverts Heq2.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
Qed.   

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


Lemma mqd_in_cdom_holds: 
  forall O idx t pr, 
    ~(forall td : taskdom, dom_cur_tsk O td -> mqidx_in_dom idx td = false) ->
    get O curtid = Some (oscurt t) ->
    task_prio_id O pr t -> 
    mqd_in_dom idx O pr.
Proof.
  introv Hn Hct Htpi.
  apply Classical_Pred_Type.not_all_ex_not in Hn.
  unfolds.
  destruct Hn as (d & Himpl).
  apply Classical_Prop.imply_to_and in Himpl.
  destruct Himpl as (Hdct & Hne).
  unfold dom_cur_tsk in Hdct.
  simpljoin. 
  l_rew12_inv2 (get O curtid).
  apply2 (task_prio_id O) (task_prio_id O) prio_unique.
  destruct (mqidx_in_dom idx (dom_for_prio pr)); eauto. 
Qed.   


Lemma spec_skip_none_false: 
  forall vl O act vo, 
    spec_skip_step vl O act (vo, None) -> False.
Proof.
  introv Hf.
  inverts Hf.
  simpljoin.
  tryfalse.
Qed.

Lemma ms_getep_Oeq: 
  forall vl O act v' O', 
    mqsend_get_ecb_ptr vl O act (v', Some O') ->
    O = O'. 
Proof.
  introv Hgep.
  inverts Hgep.
  simpljoin.
  inverts H3.
  simpljoin.
  congruence.
  simpljoin. 
  tryfalse. 
Qed. 

Lemma mqgf_Oeq: 
  forall vl O act v O', 
    mqsend_get_mqflags vl O act (v, Some O') ->
    O = O'. 
Proof.
  introv Hmf.
  inverts Hmf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; solve [congruence | false] end.
Qed.

Lemma qtimedpost_after_sched_Oeq: 
  forall O act v0 v1 v' i O', 
    qtimedpost_after_sched (v0 :: v1 :: Vint32 i :: nil) O act (v', Some O') -> 
    O = O'. 
Proof.
  introv Hmf.
  inverts Hmf.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; solve [congruence | false] end.
Qed.

Lemma idm_getep_dom_qptr: 
  forall i0 O v act vo Of O0 O0' pr, 
    mqd_in_dom i0 O pr -> 
    mqsend_get_ecb_ptr (Vint32 i0 :: v :: nil) O0 act (vo, Some O0') -> 
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

Lemma mq_equiv_flg_veq:
  forall i0 i1 i2 pr O1 O2 Of1 Of2 O10 O20 act1 act2 O1' O2' v1 v2,
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    mqd_in_dom i0 O1 pr ->
    mqd_in_dom i0 O2 pr ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 -> 
    mqsend_get_mqflags (Vint32 i0 :: Vint32 i1 :: nil) O10 act1 (v1, Some O1') ->
    mqsend_get_mqflags (Vint32 i0 :: Vint32 i2 :: nil) O20 act2 (v2, Some O2') -> 
    i1 = i2. 
Proof.
  introv Hkme Hd1 Hd2 Hjo1 Hjo2 Hm1 Hm2.
  unfold mqd_in_dom in *.
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
  destruct Hall as (Hiff & Hall).
  specializes Hall; eauto. 
  unfolds in Hall.
  simpljoin.
Qed.   

Lemma mqdes_domqp_mqidm: 
  forall i v O pr, 
    mqdes_dom_qptr i v O pr -> mqd_in_dom i O pr.  
Proof.
  introv Hmd.
  unfold mqdes_dom_qptr in Hmd.
  unfolds.
  simpljoin.
  auto.
Qed.   

Lemma cap_equiv_sendcap_equiv: 
  forall pr O1 O2 i0 vp1 vp2 t1 t2, 
    cap_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) -> 
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    has_no_cap_send O1 vp1 ->
    has_no_cap_send O2 vp2. 
Proof. 
  introv Hce Hct1 Hct2 Htpi1 Htpi2 Hmd1 Hmd2 Hcs1.
  unfold cap_equiv in Hce.
  unfold mqdes_dom_qptr in *.
  unfold has_no_cap_send in *.
  simpljoin.
  specialize (H9 pr (eq_refl)).
  destruct H9 as (Hcc & Hoc).
  do 3 eexists.
  splits; eauto.
  l_rew21_inv1 (get O1 cspaceid).
  l_rew21_inv1 (get O1 curtid).
  apply2 (task_prio_id O1) (task_prio_id O1) prio_unique.
  specializes Hoc; eauto.
  destruct Hoc as (_ & Hoc).
  specializes Hoc; eauto. 
  rewrite Hcc in H3. 
  rewrite Hoc in H3.
  auto.
Qed.   

Lemma ceq_send_res:
  forall i1 i2 O1 O2 i0 i v1 v3 d1 d2 vp1 vp2 i1_ i2_ pr, 
    length (Vint32 i0 :: v1 :: Vint32 i :: v3 :: nil) = 4%nat -> 
    length (Vint32 d1 :: vp1 :: Vint32 i1_ :: Vint32 i1 :: nil) = 4%nat -> 
    length (Vint32 d2 :: vp2 :: Vint32 i2_ :: Vint32 i2 :: nil) = 4%nat ->  
    i1 = i2 ->
    cmd_equiv pr (curs (hapi_code (mqsend_res i1))) (curs (hapi_code (mqsend_res i2))) O1 O2. 
Proof.
  introv Hlenvl Hlenvl1 Hlenvl2 Heq.
  unfolds.
  right.
  do 2 eexists.
  split; eauto.
  split; eauto.
  split.
  unfolds. simpl; auto.
  split.
  unfolds. simpl; auto.
  split.
  eapply veq_vlequiv; eauto.
  simpl; eauto.
  simpl; eauto.
  subst. auto.
  (* stmt_equiv *)
  unfolds.
  right.
  split. introv Hf; simpljoin; tryfalse.
  left.
  (* mqsend_equiv *)
  unfolds. 
  match type of Hlenvl with length ?vl = _ => exists vl end. 
  match type of Hlenvl1 with length ?vl = _ => exists vl end.
  match type of Hlenvl2 with length ?vl = _ => exists vl end.
  exists 19%nat.
  split. simpl; auto.
  split. simpl; auto.
  split. simpl; auto.
  split.
  simpl. auto. 
  simpl. auto.     
Qed.     

Lemma mq_equiv_noque_false: 
  forall i0 vp1 vp2 v0 O1 O2 pr, 
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    (exists qid els,
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

Lemma mq_equiv_wls_impl:
  forall i0 vp1 vp2 O1 O2 pr v0, 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    (exists qid els,
        vp1 = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist els) /\
          (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls) /\ wls <> nil)) ->
    (exists qid els,
        vp2 = Vptr qid /\
          v0 <> Vnull /\
          get O2 absecblsid = Some (absecblist els) /\
          (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls) /\ wls <> nil)). 
Proof.
  introv Hmd1 Hmd2 Hkqe Hwl1.
  destruct Hwl1 as (qid & els & Hvp1 & Hne & Hget & Hnex).
  unfold kernel_mq_equiv in Hkqe. 
  unfold mqdes_dom_qptr in *.
  unfold mq_ptr in *.
  simpljoin. 
  l_rew12_inv2 (get O1 absmqattrid).
  l_rew12_inv2 (get O2 absmqattrid).
  match goal with H: (_ /\ Vptr _ = Vnull \/ _) |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  rename H3 into Hmqe.
  specializes Hmqe; eauto. (* obtain mq_equiv *)
  unfold mq_equiv in Hmqe.
  destruct Hmqe as (_ & Hmqe).
  specializes Hmqe; eauto.
  simpljoin.
  match goal with H: _ \/ _ \/ _ |- _ => destruct H as [Hf | [Hf | Ht]] end.
  - simpljoin; tryfalse.
  - simpljoin; tryfalse.
  - simpljoin.
    match goal with
      H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H
    end.
    l_rew21_inv1 (get O1 absecblsid).
    match goal with H: _ \/ (exists _, _) |- _ => inverts H; simpljoin; tryfalse end.
    match goal with
      H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H
    end.
    do 2 eexists.
    splits; eauto. 
    unfold mq_ed_equiv in *.
    simpljoin.
    rewrite H12 in H. inverts H.
    do 4 eexists. splits; eauto.
    unfold tidls_equiv in *.
    simpljoin.
    match goal with
      H: _ <> nil |- _ => introv Hn; apply H
    end.
    eapply length_zero_iff_nil; eauto. 
    apply length_zero_iff_nil in Hn.
    congruence.
Qed.     

Lemma mq_equiv_qlen_impl: 
  forall i0 vp1 vp2 O1 O2 pr v0, 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    (exists qid qls ml n pwl wl,
        vp1 = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, wl) /\
          Z.of_nat (length ml) >= Int.unsigned n) ->
    (exists qid qls ml n pwl wl,
        vp2 = Vptr qid /\
          v0 <> Vnull /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, wl) /\
          Z.of_nat (length ml) >= Int.unsigned n). 
Proof.
  introv Hmd1 Hmd2 Hkqe Hlen1.
  destruct Hlen1 as (qid & qls & ml & n & pwl & wl & Hvp1 & Hne & Hget & Hgetq & Hlge).
  unfold kernel_mq_equiv in Hkqe. 
  unfold mqdes_dom_qptr in *.
  simpljoin.
  unfold mq_ptr in *. 
  simpljoin.
  l_rew12_inv2 (get O1 absmqattrid).
  l_rew12_inv2 (get O2 absmqattrid).
  rename H1 into Hmqe.
  specializes Hmqe; eauto. (* obtain mq_equiv *)
  unfold mq_equiv in Hmqe.
  destruct Hmqe as (_ & Hmqe).
  specializes Hmqe; eauto.
  simpljoin. 
  match goal with H: (_ /\ Vptr _ = Vnull \/ _) |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  match goal with H: _ \/ _ \/ _ |- _ => destruct H as [Hf | [Hf | Ht]] end.
  - simpljoin; tryfalse.
  - simpljoin; tryfalse.
  - simpljoin.
    match goal with
      H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H
    end.
    l_rew21_inv1 (get O1 absecblsid).
    match goal with H: _ \/ (exists _, _) |- _ => inverts H; simpljoin; tryfalse end.
    match goal with
      H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H
    end.
    unfold mq_ed_equiv in *.
    simpljoin.
    do 6 eexists.
    splits; eauto.
    rewrite H10 in Hgetq. inverts Hgetq.
    auto. 
Qed.   

Lemma mq_equiv_qptr_veq: 
  forall pr O1 O2 i v1 v2, 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    mqdes_dom_qptr i v1 O1 pr ->
    mqdes_dom_qptr i v2 O2 pr -> 
    ((v1 = Vnull <-> v2 = Vnull)
     /\ ((exists eid, v1 = Vptr eid) <-> (exists eid, v2 = Vptr eid))).
Proof.
  introv Hkme Hmd1 Hmd2.
  unfolds in Hkme.
  unfolds in Hmd1.
  unfolds in Hmd2.
  unfold mq_ptr in *.
  simpljoin.
  l_rew21_inv1 (get O1 absmqattrid).
  l_rew21_inv1 (get O2 absmqattrid).
  match goal with
    H: forall _, _ |- _ => rename H into Ha; specializes Ha; eauto
  end.
  destruct Ha as (_ & Ha).
  specializes Ha; eauto.
  unfold mq_equiv in Ha.
  simpljoin.
  match goal with
    H: _ \/ _ |- _ =>
      destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
  end.  
  - split; 
    do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end); 
    split; auto.
  - do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end). 
  - do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end). 
    split.
    split; intro; tryfalse.
    split; intros; eexists; eauto.
Qed.

Lemma qpost_nowt_succ_body_ctid_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold ctid_equiv in *.
  unfold qpost_nowt_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get O10 curtid = get O10' curtid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  } 
  lets Hct1': join_upd_get_same H1. 
  specializes Hct1'; eauto.
  assert (Hupd2: get O20 curtid = get O20' curtid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hct2': join_upd_get_same H14. 
  specializes Hct2'; eauto. 
  do 2 eexists.
  split; eauto.
  split; eauto.
  introv Htpi1' Htpi2' Htd.
  assert (Hupd1': get O10' abstcblsid = get O10 abstcblsid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Htpi1: tpi_upd_frm_preserved Htpi1' Hjo1' Hupd1' Hjo1.
  assert (Hupd2': get O20' abstcblsid = get O20 abstcblsid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Htpi2: tpi_upd_frm_preserved Htpi2' Hjo2' Hupd2' Hjo2.
  lets H__: H15 Htpi1 Htpi2. eapply H__; eauto.
Qed. 

Lemma qpost_nowt_succ_body_ibufs_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2',
    ibufs_equiv td O1 O2 ->
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    ibufs_equiv td O1' O2'.
Proof.
  introv Hibfe Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'. 
  unfold ibufs_equiv in *. 
  unfold qpost_nowt_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get O10 ibufsid = get O10' ibufsid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf1': join_upd_get_same H1. 
  specializes Hbf1'; eauto.
  assert (Hupd2: get O20 ibufsid = get O20' ibufsid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf2': join_upd_get_same H14. 
  specializes Hbf2'; eauto.
Qed. 

Lemma qpost_nowt_succ_body_obufs_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2',
    obufs_equiv td O1 O2 ->
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    obufs_equiv td O1' O2'.
Proof.
  introv Hobfe Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'. 
  unfold obufs_equiv in *. 
  unfold qpost_nowt_succ_body in *.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end. 
  match goal with H: _ :: _ :: _ = _ |- _ => inverts H end.
  assert (Hupd1: get O10 obufsid = get O10' obufsid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf1': join_upd_get_same H1. 
  specializes Hbf1'; eauto.
  assert (Hupd2: get O20 obufsid = get O20' obufsid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    introv Hf. inverts Hf.
  }
  lets Hbf2': join_upd_get_same H14. 
  specializes Hbf2'; eauto.
Qed.                          

Lemma qpost_nowt_succ_body_bufs_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2',
    bufs_equiv td O1 O2 ->
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    bufs_equiv td O1' O2'.
Proof.
  introv Hbfe Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfolds in Hbfe.
  destruct Hbfe as (Hibe & Hobe).
  split.
  lets H1_: qpost_nowt_succ_body_ibufs_equiv_preserve2
              Hibe Hpost1 Hpost2.
  specializes H1_; eauto.
  lets H2_: qpost_nowt_succ_body_obufs_equiv_preserve2 
              Hobe Hpost1 Hpost2. 
  specializes H2_; eauto. 
Qed. 

Lemma qpost_nowt_succ_body_get_tcbid_eq:
  forall vp v i act v' O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O act (v', Some O') ->
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

Definition same_prt_ecbs O O' := 
  forall els els',
    get O absecblsid = Some (absecblist els) ->
    get O' absecblsid = Some (absecblist els') ->
    (forall eid tls, get els eid = Some (absport, tls) <-> get els' eid = Some (absport, tls)). 

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

Lemma qpost_nowt_succ_dpid_same: 
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpost_nowt_succ_kpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hpost Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hpost. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end. 
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qpost_nowt_succ_same_prt_ecbs:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    same_prt_ecbs O O'. 
Proof.
  introv Hpost Hjo Hjo'.
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
      context[ (set O0 absecblsid (absecblist ?els')) ] =>
        assert (H__: get (set O0 absecblsid (absecblist els')) absecblsid = Some (absecblist els'))
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
      context[ (set O0 absecblsid (absecblist ?els')) ] =>
        assert (H__: get (set O0 absecblsid (absecblist els')) absecblsid = Some (absecblist els'))
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

Lemma qpost_nowt_succ_dom_impl:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds.
  intro x.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  destruct (get O x) eqn: E.
  2: {                    
    assert (get O0 x = None).
    { eapply join_get_none_rev1; eauto. }
    assert (get Of x = None).
    { clear -Hjo E. eapply join_get_none_rev2; eauto. }
    eapply map_join_get_none'''; eauto.
    casetac absecblsid x Ht Hf.
    - subst. l_rew21_inv1 (get O0 absecblsid).
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
  assert (Hor: get O0 x = Some (absecblist m) \/ get Of x = Some (absecblist m)).
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

Lemma qpost_nowt_succ_cpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
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

Lemma qpost_nowt_succ_mqptr_impl: 
  forall vp v i O act v' O' O0 O0' Of, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hpost Hjo Hjo' Hmp'.
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

Lemma qpost_nowt_succ_mqptr_iff: 
  forall vp v i O act v' O' O0 O0' Of, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp.
Proof.
  introv Hpost Hjo Hjo'.
  intros.
  split.
  - eapply qpost_nowt_succ_mqptr_impl; eauto.
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
  

Require Import protect.

Lemma knl_mq_equiv_postnwt_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' i0 pr, 
    kernel_mq_equiv td O1 O2 -> 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    kernel_mq_equiv td O1' O2'.
Proof.
  introv Hkme Hmdp1 Hmdp2 Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'.
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
    subst O10'.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf.                    
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l absmqattrid Hjo2 Hjo2'; eauto.
    subst O20'.
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
  { eapply H15; eauto. }
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
    assert (Hget2_: get O2 absecblsid = Some (absecblist x7)).
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
      rewrite H2 in Hget2. inverts Hget2.
      rewrite H5 in H8. inverts H8.
      rewrite H11 in H7. inverts H7.
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
      lets H__: qpost_nowt_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: qpost_nowt_succ_prio_preserved Hjo2 Hjo2'; eauto. 
      unfolds. split; auto.
      intros. split; introv Hf; simpljoin; tryfalse.
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
      lets H__: qpost_nowt_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: qpost_nowt_succ_prio_preserved Hjo2 Hjo2'; eauto. 
      eapply tidls_equiv_pp_preserve2; eauto.
      lets H__: qpost_nowt_succ_prio_preserved Hjo1 Hjo1'; eauto. 
      lets H__: qpost_nowt_succ_prio_preserved Hjo2 Hjo2'; eauto.                       
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

Lemma buffer_equiv_qpost_nowt_succ_preserve2:
  forall vp1 vp2 v0 i1 i2 O10 O20 O10' O20' O1 O2 act v1 v2 td i0 pr Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr ->     
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hmd1 Hmd2. 
  lets Hpp1: qpost_nowt_succ_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpost_nowt_succ_prio_preserved Hqn2; eauto.
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
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.
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

Lemma qpost_nowt_succ_body_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr i0 vp1 vp2 v0 i1 i2 v1 v2 O10 O20 O10' O20' O1' O2' act Of1 Of2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    qpost_nowt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_nowt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    data_equiv_tskd td cst1 cst2 O1' O2'. 
Proof.
  introv Hde Hkme Hmd1 Hmd2 Hpost1 Hpost2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold data_equiv_tskd in *.
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  split.
  lets H__: qpost_nowt_succ_body_ctid_equiv_preserve2 Hctide Hpost1 Hpost2.
  specializes H__; eauto.
  split.
  lets H__: qpost_nowt_succ_body_bufs_equiv_preserve2 Hbfe Hpost1 Hpost2.
  specializes H__; eauto.                              
  split.
  2: {
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: qpost_nowt_succ_prio_preserved Hpost1; eauto. 
    lets H__: qpost_nowt_succ_prio_preserved Hpost2; eauto. 
  }
  unfold kernel_data_equiv.

  split.
  { (* kernel_task_equiv *)
    destructs Hkde.
    eapply knl_tsk_equiv_same_tls_preserve2; eauto.
    lets H__: join_get_same_l abstcblsid Hjo1 Hjo1'.
    eapply qpost_nowt_succ_body_get_tcbid_eq; eauto. 
    auto.
    lets H__: join_get_same_l abstcblsid Hjo2 Hjo2'. 
    eapply qpost_nowt_succ_body_get_tcbid_eq; eauto.
    auto. 
  }
  split.
  {
    (* kernel_mq_equiv *)

    clear Hkme.
    destructs Hkde.
    lets H__: knl_mq_equiv_postnwt_preserve2 Hmd1 Hmd2; eauto. 
  }
  split.
  { (* ports_equiv *)
    destructs Hkde. 
    eapply ports_equiv_same_prts_preserve2; eauto.                     
    
    lets H__: qpost_nowt_succ_dpid_same Hjo1 Hjo1'; eauto. 
    lets H__: qpost_nowt_succ_dpid_same Hjo2 Hjo2'; eauto. 
    lets H__: qpost_nowt_succ_kpid_same Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_kpid_same Hjo2 Hjo2'; eauto.
    lets H__: qpost_nowt_succ_same_prt_ecbs Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_same_prt_ecbs Hjo2 Hjo2'; eauto.
    lets H__: qpost_nowt_succ_dom_impl Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_dom_impl Hjo2 Hjo2'; eauto.
    lets H__: qpost_nowt_succ_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpost_nowt_succ_prio_preserved Hjo2 Hjo2'; eauto.
  }

  split. 
  (* buffer_equiv *)
  destructs Hkde.
  eapply buffer_equiv_qpost_nowt_succ_preserve2; eauto. 
  
  (* cap_equiv *)
  destructs Hkde.
  eapply cap_equiv_preserve2; eauto.
  lets H__: qpost_nowt_succ_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qpost_nowt_succ_cpid_same Hjo2 Hjo2'; eauto.

  lets H__: qpost_nowt_succ_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qpost_nowt_succ_mqptr_iff Hjo2 Hjo2'; eauto.
Qed. 
                
Lemma qpost_nowt_succ_ret: 
  forall vp v i O act v' O', 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O act (v', Some O') ->
    i = $OS_NO_ERR.
Proof. 
  introv Hpost.
  inverts Hpost.
  inverts H.
  simpljoin.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ = _ |- _ => inverts H end. 
  auto.
Qed. 

Lemma vlequiv_mqsend_res:
  vl_equiv (mqsend_res ($ OS_NO_ERR)) (mqsend_res ($ OS_NO_ERR)). 
Proof.
  eapply veq_vlequiv; eauto.
  simpl. eauto.
  simpl. auto.
Qed. 

Require Import hasrt_sat_preserve.

Lemma qpost_nowt_succ_mqref_preserve0: 
  forall vp v i O v' O' act, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O act (v', Some O') ->
    mq_ref_preserved O O'. 
Proof.
  introv Hpost.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
  unfolds.
  introv Hget Hget'.
  rewrite set_a_get_a' in Hget'; eauto.
  2: { introv Hf; inverts Hf. }
  l_rew21_inv1 (get O absmqattrid).
  introv Hg.
  simpljoin.
  do 6 eexists; eauto. 
Qed.

Lemma qpost_nowt_succ_mqref_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
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

Lemma qpost_nowt_succ_qprt_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qpost_nowt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
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
      rewrite set_a_get_a'; eauto.
      introv Hf; inverts Hf. 
    }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
  -
    assert (get O' osdomainportid = Some (osdomainport dpl)).
    { eapply join_get_get_r; eauto. }
    l_rew21_inv1 (get O' osdomainportid).
    introv Hg. auto. 
Qed.

(* eapply cont_equiv_hsat_preserve; eauto. *)

Require Import equiv_prop.  

Lemma qpost_exwt_succ_dom_impl:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds.
  intro x.
  inverts Hpost.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  destruct (get O x) eqn: E.
  2: {                    
    assert (get O0 x = None).
    { eapply join_get_none_rev1; eauto. }
    assert (get Of x = None).
    { clear -Hjo E. eapply join_get_none_rev2; eauto. }
    eapply map_join_get_none'''; eauto.
    casetac absecblsid x Ht Hf.
    - subst. l_rew21_inv1 (get O0 absecblsid).
    - rewrite set_a_get_a'; eauto.
      casetac abstcblsid x Ht_ Hf_.
      + subst.
        assert (get O0 abstcblsid = None).
        { eapply join_get_none_rev1; eauto. }
        l_rew21_inv1 (get O0 abstcblsid).
        tryfalse.
      + rewrite set_a_get_a'; eauto. 
  }
  destruct a eqn: E';
    try (
        assert (Heq: get O x = get O' x) by
        (lets H__: join_get_same_l Hjo Hjo'; eauto; 
         casetac absecblsid x Ht Hf;
         [ subst; 
           eapply join_get_get_l with (m:=O) in H3; eauto; 
           l_rew21_inv1 (get O absecblsid) |
           rewrite set_a_get_a'; eauto; 
           casetac abstcblsid x Ht_ Hf_;
           [ subst; 
             eapply join_get_get_l with (m:=O) in H2; eauto; 
             l_rew21_inv1 (get O abstcblsid) | 
             rewrite set_a_get_a'; eauto ]]); 
        rewrite E in Heq; 
        eexists; symmetry; eauto; fail).             
  {
    assert (Hor: get O0 x = Some (abstcblist m) \/ get Of x = Some (abstcblist m)).
    { eapply join_get_or; eauto. }
    destruct Hor as [Hl | Hr].
    2: { eexists; eapply join_get_get_r; eauto. }
    casetac absecblsid x Ht Hf.
    -
      subst.
      l_rew21_inv1 (get O0 absecblsid).
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
    assert (Hor: get O0 x = Some (absecblist m) \/ get Of x = Some (absecblist m)).
    { eapply join_get_or; eauto. }
    destruct Hor as [Hl | Hr].
    2: { eexists; eapply join_get_get_r; eauto. }
    casetac absecblsid x Ht Hf.
    -
      subst.
      l_rew21_inv1 (get O0 absecblsid).
      eexists. eapply join_get_get_l; eauto.
      rewrite set_a_get_a. eauto. 
    -
      casetac abstcblsid x Ht_ Hf_.
      +
        subst.
        l_rew21_inv1 (get O0 abstcblsid).
      +
        eexists.
        eapply join_get_get_l; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.            
  }          
Qed.    

Lemma qpost_exwt_succ_dpid_same: 
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O osdomainportid = get O' osdomainportid. 
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

Lemma qpost_exwt_succ_kpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O oskportid = get O' oskportid.  
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

Lemma qpost_exwt_succ_same_prt_ecbs:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    same_prt_ecbs O O'. 
Proof.
  introv Hpost Hjo Hjo'.
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
    assert (Hget0: get O absecblsid = Some (absecblist x2)).
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

Lemma qpost_exwt_succ_cpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
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

Lemma qpost_exwt_succ_mqattr_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
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

Lemma qpost_exwt_succ_mqptr_impl: 
  forall vp v i O act v' O' O0 O0' Of, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hpost Hjo Hjo' Hmp'.
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
    lets H__: qpost_exwt_succ_mqattr_same Hjo Hjo'; eauto.   
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qpost_exwt_succ_mqptr_iff: 
  forall vp v i O act v' O' O0 O0' Of, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp.  
Proof.
  introv Hpost Hjo Hjo'.
  intros.
  split.
  - eapply qpost_exwt_succ_mqptr_impl; eauto. 
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
      lets H__: qpost_exwt_succ_mqattr_same Hjo Hjo'; eauto.   
    }
    rewrite H0 in H.
    do 8 eexists; eauto.
Qed.

Lemma qpost_exwt_succ_mqref_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
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

Lemma qpost_exwt_succ_qprt_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: ?f _ = ?f _ |- _ => inverts H end.
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

Lemma qpost_exwt_succ_ctid_equiv_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2', 
    ctid_equiv td O1 O2 -> 
    qpost_exwt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_exwt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    ctid_equiv td O1' O2'. 
Proof.
  introv Hctide Hpost1 Hpost2 Hjo1 Hjo2 Hjo1' Hjo2'.
  lets H1_: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
  lets H2_: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto. 
  
  unfold ctid_equiv in *.
  unfold qpost_exwt_succ_body in *.
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  do 2 (match goal with H: _ :: _ = _ |- _ => inverts H end). 
  assert (Hupd1: get O10 curtid = get O10' curtid).
  {
    match goal with H: Some O10' = _ |- _ => inverts H end.
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a'; eauto. 
    introv Hf; inverts Hf.
    introv Hf; inverts Hf.
  } 
  lets Hct1': join_upd_get_same H1. 
  specializes Hct1'; eauto.
  assert (Hupd2: get O20 curtid = get O20' curtid).
  {
    match goal with H: Some O20' = _ |- _ => inverts H end.
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

Lemma qpost_exwt_succ_bufs_same:
  forall vp v i O0 act v' O0' Of O O', 
    qpost_exwt_succ_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hpost Hjo Hjo'.
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
    GetHWait tcbs1 wl1 t1 ->
    GetHWait tcbs2 wl2 t2 ->
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

Lemma knl_mq_equiv_postexwt_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' i0 pr, 
    kernel_data_equiv td O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    qpost_exwt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qpost_exwt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    (kernel_task_equiv td O1' O2' /\ kernel_mq_equiv td O1' O2').       
Proof.
  introv Hkde Hkte Hkme Hmdp1 Hmdp2 Hpost1 Hpost2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
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
    subst O10'.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf. 
  }
  assert (Hgeq2: get O2 absmqattrid = get O2' absmqattrid).
  {
    lets H__: join_get_same_l absmqattrid Hjo2 Hjo2'; eauto.
    subst O20'.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a'; eauto.
    introv Hf; inverts Hf. 
  }
  match goal with
    H: get O10 abstcblsid = ?otcbs |- _ => assert (Hg1: get O1 abstcblsid = otcbs)
  end.
  eapply join_get_get_l; eauto. 
  match goal with
    H: get O20 abstcblsid = ?otcbs |- _ => assert (Hg2: get O2 abstcblsid = otcbs)
  end.
  eapply join_get_get_l; eauto.
  l_rew21_inv1 (get O1 abstcblsid).
  l_rew21_inv1 (get O2 abstcblsid).

  match goal with
    H: context [set O10 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O1' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto.
    subst O10'.
    rewrite set_a_get_a'; eauto.
    2: introv Hf; inverts Hf.
    rewrite set_a_get_a.
    auto. 
  }
  match goal with
    H: context [set O20 _ (abstcblist ?tcbs)] |- _ =>
      assert (get O2' abstcblsid = Some (abstcblist tcbs))
  end.
  {
    eapply join_get_get_l; eauto.
    subst O20'.
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
          eapply qpost_exwt_succ_prio_preserved; eauto. 
        }
        apply Htpi12 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym.
        lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto. 
      *
        introv Htpi2'.
        assert (Hex: exists t, task_prio_id O2 pr0 t).
        {
          destruct Htpi2' as (t_ & Htpi2').
          eexists.
          eapply prio_preserved_tpi; eauto. 
          lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto. 
        }
        apply Htpi21 in Hex.
        destruct Hex as (t_ & Htpi_). 
        eexists. eapply prio_preserved_tpi; eauto. 
        apply prio_preserved_sym.
        lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto. 
    + 
      introv Hg1' Hg2'.
      assert (Htpi1': task_prio_id O1' pr0 t1).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi2': task_prio_id O2' pr0 t2).
      { unfolds. do 5 eexists. split; eauto. }
      assert (Htpi1_: task_prio_id O1 pr0 t1).
      {
        eapply prio_preserved_tpi; eauto.
        lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
      }
      assert (Htpi2_: task_prio_id O2 pr0 t2).
      {
        eapply prio_preserved_tpi; eauto.
        lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.
      }
      unfolds in Htpi1_. unfolds in Htpi2_.
      simpljoin.
      do 2 l_rew21_inv1 (get O1 abstcblsid).
      do 2 l_rew21_inv1 (get O2 abstcblsid).
      lets H__: kme_kte_gethwait_eq Hkte_ Hkme Hmdp1 Hmdp2. 
      specializes H__; eauto.
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
        lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.
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
    lets Hmqeq1: qpost_exwt_succ_mqattr_same Hjo1 Hjo1'; eauto. 
    lets Hmqeq2: qpost_exwt_succ_mqattr_same Hjo2 Hjo2'; eauto. 
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
        H: get O10 absecblsid = ?e |- _ => assert (get O1 absecblsid = e)
      end.
      { eapply join_get_get_l; eauto.  }
      match goal with
        H: get O20 absecblsid = ?e |- _ => assert (get O2 absecblsid = e)
      end.
      { eapply join_get_get_l; eauto. }
      l_rew21_inv1 (get O1 absecblsid).
      l_rew21_inv1 (get O2 absecblsid).
      rewrite H18 in Hged1. inverts Hged1.
      rewrite H8 in Hged2. inverts Hged2.
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
        do 4 eexists. split; eauto. split; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
        lets H'_: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto. 
        lets H'_: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto. 
      * (* tidls_equiv *) 

        match goal with
          H: get ecbs1 x_ = _ |- _ => lets H1_: distinct_wait_tids H; eauto
        end.
        match goal with
          H: get ecbs2 x_ = _ |- _ => lets H2_: distinct_wait_tids H; eauto
        end.
        simpljoin.
        eapply tidls_equiv_rm_preserve2; eauto.
        eapply gethwait_in; eauto.
        eapply gethwait_in; eauto.
        lets H'_: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto. 
        lets H'_: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.
      
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
        assert (get O1 absecblsid = Some (absecblist x21)).
        { eapply join_get_get_l; eauto. }
        assert (get O2 absecblsid = Some (absecblist x7)).
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
        lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
        lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.
          
Qed. 

Lemma buffer_equiv_qpost_exwt_succ_preserve2:
  forall vp1 vp2 v0 i1 i2 O10 O20 O10' O20' O1 O2 act v1 v2 td i0 pr Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qpost_exwt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') -> 
    qpost_exwt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr ->     
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hmd1 Hmd2. 
  lets Hpp1: qpost_exwt_succ_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qpost_exwt_succ_prio_preserved Hqn2; eauto.
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
  kvext O10 absecblsid O1.
  kvext O20 absecblsid O2.
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
      
Lemma qpost_exwt_succ_dteq_preserve2:
  forall td cst1 cst2 O1 O2 pr i0 vp1 vp2 v0 i1 i2 v1 v2 O10 O20 O10' O20' O1' O2' act Of1 Of2, 
    data_equiv_tskd td cst1 cst2 O1 O2 -> 
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    kernel_mq_equiv (dom_for_prio pr) O1 O2 -> 
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    qpost_exwt_succ_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') -> 
    qpost_exwt_succ_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    data_equiv_tskd td cst1 cst2 O1' O2'.
Proof.
  introv Hde Hkte Hkme Hmd1 Hmd2 Hpost1 Hpost2. 
  introv Hjo1 Hjo2 Hjo1' Hjo2'. 
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  lets H__: knl_mq_equiv_postexwt_preserve2 Hkde Hkte Hkme Hmd1 Hmd2.
  lets H_: H__ Hpost1 Hpost2. clear H__.
  specializes H_; eauto. 
  splits.
  -
    lets H__: qpost_exwt_succ_ctid_equiv_preserve2 Hctide Hpost1 Hpost2; eauto.
  -
    lets H1__: qpost_exwt_succ_bufs_same Hpost1 Hjo1 Hjo1'.
    lets H2__: qpost_exwt_succ_bufs_same Hpost2 Hjo2 Hjo2'.
    simpljoin. 
    lets H__: bufs_equiv_preserve2 O1 O2 O1' O2' Hbfe.
    specializes H__; eauto. 
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
      lets H__: qpost_exwt_succ_dpid_same Hjo1 Hjo1'; eauto. 
      lets H__: qpost_exwt_succ_dpid_same Hjo2 Hjo2'; eauto. 
      lets H__: qpost_exwt_succ_kpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_kpid_same Hjo2 Hjo2'; eauto.
      lets H__: qpost_exwt_succ_same_prt_ecbs Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_same_prt_ecbs Hjo2 Hjo2'; eauto.
      lets H__: qpost_exwt_succ_dom_impl Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_dom_impl Hjo2 Hjo2'; eauto.
      lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.

    + (* buffer_equiv *) 
      destructs Hkde.
      eapply buffer_equiv_qpost_exwt_succ_preserve2; eauto.

    + (* cap_equiv *)
      destructs Hkde.
      eapply cap_equiv_preserve2; eauto.
      lets H__: qpost_exwt_succ_cpid_same Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_cpid_same Hjo2 Hjo2'; eauto.

      lets H__: qpost_exwt_succ_mqptr_iff Hjo1 Hjo1'; eauto.
      lets H__: qpost_exwt_succ_mqptr_iff Hjo2 Hjo2'; eauto.
      
  -
    eapply cde_prio_preserved_preserve2; eauto.
    lets H__: qpost_exwt_succ_prio_preserved Hjo1 Hjo1'; eauto.
    lets H__: qpost_exwt_succ_prio_preserved Hjo2 Hjo2'; eauto.
    
Qed. 
          
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


Lemma qtimedpost_ovf_block_bufs_same:
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
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

Lemma qtimedpost_ovf_block_dpid_same: 
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
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

Lemma qtimedpost_ovf_block_kpid_same: 
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->  
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

Lemma qtimedpost_ovf_block_same_prt_ecbs:
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
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
    assert (Hget0: get O absecblsid = Some (absecblist x7)).
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
    assert (Hget0: get O absecblsid = Some (absecblist x7)).
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

Lemma qtimedpost_ovf_block_cpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
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

Lemma qtimedpost_ovf_block_same:
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
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

Lemma qtimedpost_ovf_block_mqptr_impl: 
  forall vp v i O act v' O' O0 O0' Of, 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
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
    lets H__: qtimedpost_ovf_block_same Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qtimedpost_ovf_block_mqptr_iff: 
  forall vp v i O act v' O' O0 O0' Of, 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hovf Hjo Hjo'.
  intros.
  split.
  - eapply qtimedpost_ovf_block_mqptr_impl; eauto.
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
      lets H__: qtimedpost_ovf_block_same Hjo Hjo'; eauto. 
    }
    rewrite H0 in H.
    do 8 eexists; eauto.
Qed.

Lemma qtimedpost_ovf_block_mqref_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
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

Lemma qtimedpost_ovf_block_qprt_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
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

Ltac sp_forall1 :=
  match goal with
    H: forall _, _ |- _ => specializes H; eauto
  end.

Ltac sp_forall1' hypname :=
  match goal with
    H: forall _, _ |- _ => rename H into hypname; specializes hypname; eauto
  end. 
       
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
        
Ltac autospcz :=
  match goal with
    H: ?P1, H': ?P2 -> ?Q |- _ => specialize (H' H)
  end.
  
Lemma knl_mq_equiv_ovf_block_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' i0 pr t1 t2, 
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
    qtimedpost_ovf_block_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qtimedpost_ovf_block_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    (kernel_task_equiv td O1' O2' /\ kernel_mq_equiv td O1' O2').       
Proof.
  introv Hkde Hd1 Hd2 Hct1 Hct2 Htpi1 Htpi2.
  introv Hovf1 Hovf2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfolds in Hkde.
  destruct Hkde as (Hkte & Hkme & Hpe & Hbufe & Hcpe).
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
        lets H__: qtimedpost_ovf_block_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qtimedpost_ovf_block_prio_preserved Hjo2 Hjo2'; eauto.
      *
        intros t1_ t2_.
        introv Hgett1 Hgett2.
        match goal with
          H: get tcbs1 t1 = Some (_, ?x) |- _ => 
            assert (Htpi1_: task_prio_id O1 x t1) 
        end.
        { unfolds. do 5 eexists. split; eauto. }
        match goal with
          H: get tcbs2 t2 = Some (_, ?x) |- _ => 
            assert (Htpi2_: task_prio_id O2 x t2)
        end.
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
          lets H__: qtimedpost_ovf_block_prio_preserved Hjo1 Hjo1'; eauto. 
          lets H__: qtimedpost_ovf_block_prio_preserved Hjo2 Hjo2'; eauto. 
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
      unfolds in Hcpe.
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
      
      lets H1_: qtimedpost_ovf_block_same Hovf1' Hjo1 Hjo1'; eauto.
      lets H2_: qtimedpost_ovf_block_same Hovf2' Hjo2 Hjo2'; eauto.
      rewrite H0 in H1_. symmetry in H1_.
      rewrite H1 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hid.
      sp_forall1' Ha. sp_forall1' Hb. sp_forall1' Hc.
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
        lets Hpp1_: qtimedpost_ovf_block_prio_preserved Hjo1 Hjo1'; eauto.
        lets Hpp2_: qtimedpost_ovf_block_prio_preserved Hjo2 Hjo2'; eauto. 

        casetac x2 eid' Ht Hf.
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
          eapply tidls_equiv_cons_preserve2; eauto. 
          eapply tidls_equiv_pp_preserve2; eauto.
          
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
    lets Hpp1: qtimedpost_ovf_block_prio_preserved Hjo1 Hjo1'; eauto.
    lets Hpp2: qtimedpost_ovf_block_prio_preserved Hjo2 Hjo2'; eauto.
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
      unfolds in Hcpe. 
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
      
      lets H1_: qtimedpost_ovf_block_same Hovf1' Hjo1 Hjo1'; eauto.
      lets H2_: qtimedpost_ovf_block_same Hovf2' Hjo2 Hjo2'; eauto.
      rewrite H2 in H1_. symmetry in H1_.
      rewrite H3 in H2_. symmetry in H2_.
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

Lemma buffer_equiv_qtimedpost_ovf_block_preserve2:
  forall vp1 vp2 v0 i1 i2 O10 O20 O10' O20' O1 O2 act v1 v2 td i0 pr Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qtimedpost_ovf_block_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') -> 
    qtimedpost_ovf_block_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->  
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr ->     
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hmd1 Hmd2. 
  lets Hpp1: qtimedpost_ovf_block_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qtimedpost_ovf_block_prio_preserved Hqn2; eauto.
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
  
Lemma qtimedpost_ovf_block_dteq_preserve2:  
  forall i cst1 cst2 O1 O2 i0 vp1 vp2 pr v0 i1 i2 O10 O20 act v1 v2 O10' O20' O1' O2' Of1 Of2 t1 t2, 
    data_equiv_tskd i cst1 cst2 O1 O2 ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    qtimedpost_ovf_block_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qtimedpost_ovf_block_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
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
  lets H__: qtimedpost_ovf_block_ctid_same Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_ovf_block_ctid_same Hjo2 Hjo2'; eauto.
  lets H__: qtimedpost_ovf_block_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_ovf_block_prio_preserved Hjo2 Hjo2'; eauto.                           

  (* bufs_equiv *) 
  lets H1_: qtimedpost_ovf_block_bufs_same Hjo1 Hjo1'; eauto.
  lets H2_: qtimedpost_ovf_block_bufs_same Hjo2 Hjo2'; eauto. 
  destruct H1_. destruct H2_. 
  eapply bufs_equiv_preserve2; eauto.

  (* kernel_data_equiv *)
  lets H__: knl_mq_equiv_ovf_block_preserve2 Hovf1 Hovf2 Hjo1 Hjo2 Hjo1' Hjo2'; eauto.
  destruct H__.
  destructs Hkde.
  unfolds.
  splits; auto. 

  (* ports_equiv *) 
  eapply ports_equiv_same_prts_preserve2; eauto.          
  lets H__: qtimedpost_ovf_block_dpid_same Hjo1 Hjo1'; eauto. 
  lets H__: qtimedpost_ovf_block_dpid_same Hjo2 Hjo2'; eauto.
  lets H__: qtimedpost_ovf_block_kpid_same Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_ovf_block_kpid_same Hjo2 Hjo2'; eauto.
  lets H__: qtimedpost_ovf_block_same_prt_ecbs Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_ovf_block_same_prt_ecbs Hjo2 Hjo2'; eauto. 
  lets H__: qtimedpost_ovf_block_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_ovf_block_prio_preserved Hjo2 Hjo2'; eauto.

  (* (* buffer_equiv *)  *)
  eapply buffer_equiv_qtimedpost_ovf_block_preserve2; eauto. 
  
  (* cap_equiv *) 
  eapply cap_equiv_preserve2; eauto. 
  lets H__: qtimedpost_ovf_block_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_ovf_block_cpid_same Hjo2 Hjo2'; eauto.
  lets H__: qtimedpost_ovf_block_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_ovf_block_mqptr_iff Hjo2 Hjo2'; eauto.

  (* client_data_equiv *) 
  eapply cde_prio_preserved_preserve2; eauto. 
  lets H__: qtimedpost_ovf_block_prio_preserved Hjo1 Hjo1'; eauto. 
  lets H__: qtimedpost_ovf_block_prio_preserved Hjo2 Hjo2'; eauto. 
  
Qed.

Lemma qtimedpost_ovf_block_mqptr_impl': 
  forall vp v i O act v' O' O0 O0' Of, 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
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
    lets H__: qtimedpost_ovf_block_same Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qtimedpost_ovf_block_mqd_impl: 
  forall vp v i O act v' O' O0 O0' Of pr, 
    qtimedpost_ovf_block_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val),
      mqdes_dom_qptr idx objp O pr -> mqdes_dom_qptr idx objp O' pr.
Proof.
  introv Hovf Hjo Hjo' Hd.
  unfold mqdes_dom_qptr in *.
  simpljoin.
  split; auto.
  eapply qtimedpost_ovf_block_mqptr_impl'; eauto. 
Qed.

Lemma mq_equiv_post_to_impl:
  forall i0 vp1 vp2 O1 O2 pr v0 t1, 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    ctid_equiv (dom_for_prio pr) O1 O2 -> 
    data_equiv_schd O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    task_prio_id O1 pr t1 -> 
    (exists qid pr t tls p m sus,
        vp1 = Vptr qid /\
          v0 <> Vnull /\
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (p, wait (os_stat_postq qid) None, m, sus, pr)) -> 
    (exists qid pr t tls p m sus,
        vp2 = Vptr qid /\
          v0 <> Vnull /\
          get O2 curtid = Some (oscurt t) /\
          get O2 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (p, wait (os_stat_postq qid) None, m, sus, pr)).
Proof.
  introv Hd1 Hd2 Hkme Hkte Hcte Hsche Hgct1 Htpi1_ Hex.
  assert (Hkme_ := Hkme).
  unfolds in Hkme.
  unfolds in Hkte.
  simpljoin.
  l_rew21_inv1 (get O1 abstcblsid).
  assert (Hd1_:=Hd1).
  assert (Hd2_:=Hd2).
  unfolds in Hd1.
  unfolds in Hd2.
  unfold mq_ptr in Hd1, Hd2.
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  l_rew21_inv1 (get O1 absmqattrid).
  l_rew21_inv1 (get O2 absmqattrid).
  sp_forall1' Ha. sp_forall1' Hb.
  destruct Hb as (Hiff & Hb).
  specializes Hb; eauto.
  (* lets H__: Hb H14 H10; eauto.   *)
  unfolds in Hb.
  simpljoin.
  match goal with
    H: _ \/ _ \/ _ |- _ => destruct H as [Hf | [Hf | Ht]]; simpljoin; tryfalse
  end.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  sp_forall1' Ha.
  (* rename H7 into Hall.  *)
  (* specialize (Ha pr (eq_refl _)). *)
  destruct Ha as (_ & Heq).
  unfolds in Hsche. 
  simpljoin.
  l_rew12_inv2 (get O1 curtid).
  l_rew12_inv2 (get O1 curtid).
  match goal with
    H: get O1 curtid = Some (oscurt ?t) |- _ => 
      assert (Hex: exists pr, task_prio_id O1 pr t)
  end.
  { eexists. unfolds. do 5 eexists. split; eauto. }
  assert (Hex_:=Hex).
  match goal with H: _ <-> _ |- _ => apply H in Hex end.
  destruct Hex as (pr2 & Htpi2).
  destruct Hex_ as (pr1 & Htpi1).
  unfolds in Hcte.
  simpljoin.
  l_rew12_inv2 (get O1 curtid).
  l_rew12_inv2 (get O2 curtid).
  apply2 (task_prio_id O1) (task_prio_id O1) prio_unique.
  assert (pr1 = pr2).
  { eapply H26; eauto. }
  subst.
  unfolds in Htpi2.
  simpljoin.
  l_rew12_inv2 (get O2 abstcblsid).
  unfolds in Htpi1.
  simpljoin.
  l_rew12_inv2 (get O1 abstcblsid).
  rewrite H5 in H27. inverts H27.
  lets H__: Heq H5 H18.
  simpljoin. 
  lets H__: kme_eptreq Hkme_ Hd1_ Hd2_; eauto. subst. 
  do 7 eexists.
  split; eauto.
Qed. 

Lemma mq_equiv_post_rdy_impl:
  forall i0 vp1 vp2 O1 O2 pr v0 t1, 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    kernel_task_equiv (dom_for_prio pr) O1 O2 -> 
    ctid_equiv (dom_for_prio pr) O1 O2 -> 
    data_equiv_schd O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    task_prio_id O1 pr t1 -> 
    (exists qid t tls p st m sus pr,
        vp1 = Vptr qid /\
          v0 <> Vnull /\
          get O1 curtid = Some (oscurt t) /\
          get O1 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (p, st, m, sus, pr) /\ st = rdy /\ sus = false) -> 
    (exists qid t tls p st m sus pr,
        vp2 = Vptr qid /\
          v0 <> Vnull /\
          get O2 curtid = Some (oscurt t) /\
          get O2 abstcblsid = Some (abstcblist tls) /\
          get tls t = Some (p, st, m, sus, pr) /\ st = rdy /\ sus = false).
Proof.
  introv Hd1 Hd2 Hkme Hkte Hcte Hsche Hg1 Htpi1_ Hex.
  assert (Hkme_ := Hkme).
  unfolds in Hkme.
  unfolds in Hkte.
  simpljoin.
  l_rew21_inv1 (get O1 abstcblsid).
  assert (Hd1_:=Hd1).
  assert (Hd2_:=Hd2).
  unfolds in Hd1.
  unfolds in Hd2.
  unfold mq_ptr in Hd1, Hd2.
  simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end).
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  l_rew21_inv1 (get O1 absmqattrid).
  l_rew21_inv1 (get O2 absmqattrid).
  sp_forall1' Ha. sp_forall1' Hb.
  specializes Hb.
  (* lets H__: H11 H14 H6; eauto.  *)
  destruct Hb as (_ & Hb).
  specializes Hb; eauto.
  unfolds in Hb.
  simpljoin.
  match goal with
    H: _ \/ _ \/ _ |- _ => destruct H as [Hf | [Hf | Ht]]; simpljoin; tryfalse
  end.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  rename H9 into Hall. 
  specialize (Hall pr (eq_refl _)).
  destruct Hall as (_ & Heq).
  unfolds in Hsche. 
  simpljoin.
  l_rew12_inv2 (get O1 curtid).
  l_rew12_inv2 (get O1 curtid).
  match goal with
    H: get O1 curtid = Some (oscurt ?t) |- _ => 
      assert (Hex: exists pr, task_prio_id O1 pr t)
  end.
  { eexists. unfolds. do 5 eexists. split; eauto. }
  assert (Hex_:=Hex).
  match goal with H: _ <-> _ |- _ => apply H in Hex end.
  destruct Hex as (pr2 & Htpi2).
  destruct Hex_ as (pr1 & Htpi1).
  unfolds in Hcte.
  simpljoin.
  l_rew12_inv2 (get O1 curtid).
  l_rew12_inv2 (get O2 curtid).
  apply2 (task_prio_id O1) (task_prio_id O1) prio_unique.
  assert (pr1 = pr2).
  { eapply H26; eauto. }
  subst.
  unfolds in Htpi2.
  simpljoin.
  l_rew12_inv2 (get O2 abstcblsid).
  unfolds in Htpi1.
  simpljoin.
  l_rew12_inv2 (get O1 abstcblsid).
  rewrite H5 in H27. inverts H27.
  lets H__: Heq H5 H18.
  simpljoin. 
  lets H__: kme_eptreq Hkme_ Hd1_ Hd2_; eauto. subst. 
  do 8 eexists.
  split; eauto.
  split; eauto.  
Qed.

Lemma mq_equiv_qlen_lt_impl: 
  forall i0 vp1 vp2 O1 O2 pr v0, 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
    (exists qls qid ml n pwl,
        vp1 = Vptr qid /\
          v0 <> Vnull /\
          get O1 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, nil) /\
          Z.of_nat (length ml) < Int.unsigned n) ->
    (exists qls qid ml n pwl,
        vp2 = Vptr qid /\
          v0 <> Vnull /\
          get O2 absecblsid = Some (absecblist qls) /\
          get qls qid = Some (absmsgq ml n pwl, nil) /\
          Z.of_nat (length ml) < Int.unsigned n). 
Proof.
  introv Hmd1 Hmd2 Hkqe Hlen1.
  destruct Hlen1 as (qls & qid & ml & n & pwl & Hvp1 & Hne & Hget & Hgetq & Hlt).
  unfold kernel_mq_equiv in Hkqe. 
  unfold mqdes_dom_qptr in *.
  simpljoin.
  unfold mq_ptr in *. 
  simpljoin.
  l_rew12_inv2 (get O1 absmqattrid).
  l_rew12_inv2 (get O2 absmqattrid).
  rename H1 into Hmqe.
  specializes Hmqe; eauto. (* obtain mq_equiv *)
  unfold mq_equiv in Hmqe.
  destruct Hmqe as (_ & Hmqe).
  specializes Hmqe; eauto.
  simpljoin. 
  match goal with H: (_ /\ Vptr _ = Vnull \/ _) |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: (Vptr _ = Vptr _)  |- _ => inverts H end.
  match goal with H: _ \/ _ \/ _ |- _ => destruct H as [Hf | [Hf | Ht]] end.
  - simpljoin; tryfalse.
  - simpljoin; tryfalse.
  - simpljoin.
    match goal with
      H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H
    end.
    l_rew21_inv1 (get O1 absecblsid).
    match goal with H: _ \/ (exists _, _) |- _ => inverts H; simpljoin; tryfalse end.
    match goal with
      H: Valid_Addr _ = Valid_Addr _ |- _ => inverts H
    end.
    unfold mq_ed_equiv in *.
    simpljoin.
    rewrite H10 in Hgetq. inverts Hgetq.
    match goal with H: tidls_equiv nil _ O1 O2 |- _ => unfolds in H; destruct H as (Hlen & _) end.
    simpl in Hlen.
    symmetry in Hlen.
    apply length_zero_iff_nil in Hlen.
    rewrite Hlen in *.
    do 5 eexists. 
    splits; eauto.
Qed.   

Lemma qtimedpost_timeout_err_ret: 
  forall vp v i O act v' O', 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O act (v', Some O') ->
    i = $OS_TIMEOUT. 
Proof. 
  introv Hpost.
  inverts Hpost.
  inverts H.
  simpljoin.
  match goal with H: _ /\ _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  auto.
Qed.

Lemma qtimedpost_timeout_err_mqref_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    mq_ref_preserved O O'. 
Proof.
  introv Herr Hjo Hjo'.
  unfolds in Herr.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
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

Lemma qtimedpost_timeout_err_bufs_same:
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    (get O' ibufsid = get O ibufsid /\ get O' obufsid = get O obufsid). 
Proof.
  introv Hto Hjo Hjo'.
  inverts Hto.
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

Lemma qtimedpost_timeout_err_same_q:
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O absmqattrid = get O' absmqattrid.  
Proof.
  introv Hto Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hto. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end. 
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf. 
Qed. 

Lemma knl_mq_equiv_timeout_err_preserve2:
  forall td O1 O2 vp1 vp2 v0 i1 i2 O10 O20 act v1 v2 O10' O20' Of1 Of2 O1' O2' i0 pr t1 t2, 
    kernel_data_equiv td O1 O2 -> 
    mqdes_dom_qptr i0 vp1 O1 pr ->
    mqdes_dom_qptr i0 vp2 O2 pr ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    qtimedpost_timeout_err_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') ->
    qtimedpost_timeout_err_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    (kernel_task_equiv td O1' O2' /\ kernel_mq_equiv td O1' O2').       
Proof.
  introv Hkde Hd1 Hd2 Hct1 Hct2 Htpi1 Htpi2.
  introv Hto1 Hto2 Hjo1 Hjo2 Hjo1' Hjo2'.
  unfolds in Hkde.
  destruct Hkde as (Hkte & Hkme & Hpe & Hbfe & Hcpe).
  unfolds in Hkte.
  destruct Hkte as (tcbs1 & tcbs2 & Hgt1 & Hgt2 & Hall).
  assert (Hto1_ := Hto1).
  assert (Hto2_ := Hto2).
  inverts Hto1. inverts Hto2. simpljoin.
  do 2 (match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end). 
  do 2 (match goal with H: Some _ = Some _ |- _ => inverts H end).
  do 2 (match goal with H: _ :: _ = _ :: _ |- _ => inverts H end).

  casetac (dom_for_prio pr) td Ht Hf.
  - 
    subst.              
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
    kvext_h Hjo1' abstcblsid O1'.
    kvext_h Hjo2' abstcblsid O2'.
    match goal with
      H: get tcbs1 t1 = Some (_, ?pr) |- _ =>
        assert (Htpi1_: task_prio_id O1 pr t1)
    end.
    { unfolds. do 5 eexists. split; eauto. }
    match goal with
      H: get tcbs2 t2 = Some (_, ?pr) |- _ =>
        assert (Htpi2_: task_prio_id O2 pr t2)
    end.
    { unfolds. do 5 eexists. split; eauto. }
    apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
    apply2_rev (task_prio_id O2) (task_prio_id O2) prio_unique.
    
    split.
    + (* kernel_task_equiv *) 
      unfolds.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hd.
      lets Hand: Hall Hd.
      destruct Hand as (Hiff & Hall_).
      split.
      *
        eapply prio_preserved_tpieq_impl; eauto. 
        lets H__: qtimedpost_timeout_err_prio_preserved Hjo1 Hjo1'; eauto.
        lets H__: qtimedpost_timeout_err_prio_preserved Hjo2 Hjo2'; eauto.
      *
        intros t1_ t2_.
        introv Hgett1 Hgett2.
        assert (Htpi1': task_prio_id O1' pr0 t1_).
        { unfolds. do 5 eexists. split; eauto. }
        assert (Htpi2': task_prio_id O2' pr0 t2_).
        { unfolds. do 5 eexists. split; eauto. }

        assert (Htcs: t1=t1_ /\ t2=t2_ \/ t1<>t1_ /\ t2<>t2_).
        {
          eapply prio_tid_corr_ext with (O1:=O1) (O2:=O2) (O1':=O1') (O2':=O2') (pr':=pr0); eauto.
          lets H__: qtimedpost_timeout_err_prio_preserved Hjo1 Hjo1'; eauto. 
          lets H__: qtimedpost_timeout_err_prio_preserved Hjo2 Hjo2'; eauto. 
        }
        destruct Htcs as [(Hteq1 & Hteq2) | (Htneq1 & Htneq2)].
        **
          subst.
          rewrite set_a_get_a in Hgett1.
          rewrite set_a_get_a in Hgett2.
          inverts Hgett1.
          inverts Hgett2.
          lets H__: Hall_ H14 H4.
          simpljoin. auto.
        **
          rewrite set_a_get_a' in Hgett1; eauto.
          rewrite set_a_get_a' in Hgett2; eauto.
    +      
      assert (Hkme_:=Hkme). 
      unfold kernel_mq_equiv in Hkme.
      destruct Hkme as (mqs1 & mqs2 & H').
      simpljoin.      
      lets H1_: qtimedpost_timeout_err_same_q Hto1_ Hjo1 Hjo1'; eauto.
      lets H2_: qtimedpost_timeout_err_same_q Hto2_ Hjo2 Hjo2'; eauto.
      rewrite H19 in H1_. symmetry in H1_.
      rewrite H20 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hid.
      match goal with H: forall (i: int32), _ |- _ => rename H into Ha; specializes Ha; eauto end.
      destruct Ha as (Hiff & Ha).
      split.
      {
        auto.
      }
      introv Hgetm1 Hgetm2.
      lets H__: Ha Hgetm1 Hgetm2.
      unfold mq_equiv in *.
      simpljoin.
      do 8 eexists.
      split; eauto.
      split; eauto. 
      match goal with
        H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
      end.
      * left. auto.
      * right; left. auto.
      * right; right.
        kvext_h Hjo1' absecblsid O1'.
        kvext_h Hjo2' absecblsid O2'.
        match type of Hgetm1 with context [Valid_Addr ?p] => rename p into eid' end.
        l_rew21_inv1 (get O1 absecblsid).
        l_rew21_inv1 (get O2 absecblsid).
        specialize (Hall pr (eq_refl _)).
        destruct Hall as (_ & Hall').
        lets H__: Hall' H14 H4.
        simpljoin.
        match goal with H: wait _ _ = wait _ _ |- _ => inverts H end.                  
        lets H1__: qtimedpost_timeout_err_prio_preserved Hjo1 Hjo1'; eauto.
        lets H2__: qtimedpost_timeout_err_prio_preserved Hjo2 Hjo2'; eauto.
        casetac x0 eid' Htrue Hfalse.
        ** subst.
           do 2 (match goal with
                   H1: get ?mp1 eid' = _, H2: get ?mp2 eid' = _ |- _ =>
                     unify mp1 mp2; rewrite H1 in H2; inverts H2
                 end).
           do 7 eexists.
           split; eauto. split; auto.
           split; eauto. split; eauto.
           do 2 rewrite set_a_get_a.
           split; eauto.
           split; eauto.
           match goal with
             H1: get O1 absecblsid = Some (absecblist ?e), H2: get ?e' eid' = Some (absmsgq _ _ ?pl, ?l) |- _ =>
               unify e e'; lets Hdis1: distinct_wait_tids H1 H2
           end.
           match goal with
             H1: get O2 absecblsid = Some (absecblist ?e), H2: get ?e' eid' = Some (absmsgq _ _ ?pl, ?l) |- _ =>
               unify e e'; lets Hdis2: distinct_wait_tids H1 H2
           end.
           split.
           *** (*mq_ed_equiv *)
             unfold mq_ed_equiv in *.
             simpljoin.
             do 2 (match goal with H: ?f _ _ _ = ?f _ _ _ |- _ => inverts H end).
             do 4 eexists.
             split; eauto.
             split; eauto.
             eapply tidls_equiv_rm_preserve2; eauto.
           *** (* tidls_equiv *)
             eapply tidls_equiv_pp_preserve2; eauto.
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
    lets Hpp1: qtimedpost_timeout_err_prio_preserved Hjo1 Hjo1'; eauto.
    lets Hpp2: qtimedpost_timeout_err_prio_preserved Hjo2 Hjo2'; eauto.
    split.
    +
      unfold kernel_task_equiv in *. 
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
      lets H1_: qtimedpost_timeout_err_same_q Hto1_ Hjo1 Hjo1'; eauto.
      lets H2_: qtimedpost_timeout_err_same_q Hto2_ Hjo2 Hjo2'; eauto.
      rewrite H in H1_. symmetry in H1_.
      rewrite H0 in H2_. symmetry in H2_.
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hid'.
      match goal with H: forall (i: int32), _ |- _ => rename H into Ha; specializes Ha; eauto end.
      destruct Ha as (Hiff & Ha). 
      split.
      { auto. }
      (* mq_equiv *) 
      introv Hgm1 Hgm2.      
      lets H__: Ha Hgm1 Hgm2.
      
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
        
        lets H1__: q_dom_diff_eid_neq Hd1 Hid'; eauto.  
        specializes H1__; eauto.
        lets H2__: q_dom_diff_eid_neq Hd2 Hid'; eauto.
        specializes H2__; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.

        split; eauto.
        split; eauto.
        split.
        eapply mq_ed_equiv_pp_preserve2; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.        
Qed.                

Lemma qtimedpost_timeout_err_dpid_same: 
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O osdomainportid = get O' osdomainportid. 
Proof.
  introv Hto Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hto. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qtimedpost_timeout_err_kpid_same: 
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->  
    join O0 Of O ->
    join O0' Of O' ->
    get O oskportid = get O' oskportid.  
Proof.
  introv Hto Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hto. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.            
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ :: _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed. 

Lemma qtimedpost_timeout_err_same_prt_ecbs:
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    same_prt_ecbs O O'. 
Proof.
  introv Hto Hjo Hjo'.
  unfolds.
  introv Hg Hg'.
  intros.
  inverts Hto.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.                  
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  split.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x7)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    kvext_h Hjo' absecblsid O'.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. unfold get in *. unfold EcbMap in *.
      l_rew21_inv1 (EcbMod.get els eid).
    + rewrite set_a_get_a'; eauto.
  -
    introv Hge.
    assert (Hget0: get O absecblsid = Some (absecblist x7)).
    { eapply join_get_get_l; eauto. }
    l_rew21_inv1 (get O absecblsid).
    kvext_h Hjo' absecblsid O'.
    l_rew21_inv1 (get O' absecblsid).
    casetac x eid Ht Hf.
    + subst. rewrite set_a_get_a in Hge. inverts Hge.
    + rewrite set_a_get_a' in Hge; eauto.
Qed.

Lemma qtimedpost_timeout_err_cpid_same:
  forall vp v i O0 act v' O0' Of O O', 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    get O cspaceid = get O' cspaceid.  
Proof.
  introv Hto Hjo Hjo'.
  lets H__: join_get_same_l Hjo Hjo'; eauto.
  inverts Hto. simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end. 
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  rewrite set_a_get_a'; eauto.
  2: introv Hf; inverts Hf.
  rewrite set_a_get_a'; eauto.
  introv Hf; inverts Hf.
Qed.

Lemma qtimedpost_timeout_err_qprt_preserve: 
  forall vp v i O v' O' O0 O0' Of act, 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    qprt_preserved O O'. 
Proof.
  introv Hpost Hjo Hjo'.
  unfolds in Hpost.
  simpljoin.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
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

Lemma qtimedpost_timeout_err_mqptr_impl: 
  forall vp v i O act v' O' O0 O0' Of, 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp -> mq_ptr O idx objp. 
Proof.
  introv Hto Hjo Hjo' Hmp'.
  unfold mq_ptr in *.
  assert (Hto':=Hto).
  inverts Hto.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end. 
  match goal with H: Some _ = Some _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (get O absmqattrid = get O' absmqattrid).
  {
    lets H__: qtimedpost_timeout_err_same_q Hjo Hjo'; eauto. 
  }
  rewrite H0 in H.
  do 8 eexists; eauto.
Qed.

Lemma qtimedpost_timeout_err_mqptr_iff: 
  forall vp v i O act v' O' O0 O0' Of, 
    qtimedpost_timeout_err_body (vp :: v :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' -> 
    forall (idx : int32) (objp : val), mq_ptr O' idx objp <-> mq_ptr O idx objp. 
Proof.
  introv Hto Hjo Hjo'.
  intros.
  split.
  - eapply qtimedpost_timeout_err_mqptr_impl; eauto.
  -    
    introv Hmp'.
    unfold mq_ptr in *.
    assert (Hto':=Hto).
    inverts Hto.
    simpljoin.
    match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end. 
    match goal with H: Some _ = Some _ |- _ => inverts H end.
    match goal with H: _ :: _ = _ |- _ => inverts H end.
    assert (get O absmqattrid = get O' absmqattrid).
    {
      lets H__: qtimedpost_timeout_err_same_q Hjo Hjo'; eauto. 
    }
    rewrite H0 in H.
    do 8 eexists; eauto.
Qed.

Lemma buffer_equiv_qtimedpost_timeout_err_preserve2:
  forall vp1 vp2 v0 i1 i2 O10 O20 O10' O20' O1 O2 act v1 v2 td i0 pr Of1 Of2 O1' O2',
    buffer_equiv td O1 O2 -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    qtimedpost_timeout_err_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') -> 
    qtimedpost_timeout_err_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') -> 
    join O10' Of1 O1' ->
    join O20' Of2 O2' ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr ->     
    buffer_equiv td O1' O2'. 
Proof.
  introv Hbe Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hmd1 Hmd2. 
  lets Hpp1: qtimedpost_timeout_err_prio_preserved Hqn1; eauto.
  specializes Hpp1; eauto.
  lets Hpp2: qtimedpost_timeout_err_prio_preserved Hqn2; eauto.
  specializes Hpp2; eauto.
  inverts Hqn1.
  inverts Hqn2.
  simpljoin.
  do 2rem_dis. 
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

Lemma qtimedpost_timeout_err_dteq_preserve2:  
  forall i cst1 cst2 O1 O2 i0 vp1 vp2 pr v0 i1 i2 O10 O20 act v1 v2 O10' O20' O1' O2' Of1 Of2 t1 t2, 
    data_equiv_tskd i cst1 cst2 O1 O2 ->
    mqdes_dom_qptr i0 vp1 O1 pr -> 
    mqdes_dom_qptr i0 vp2 O2 pr -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    qtimedpost_timeout_err_body (vp1 :: v0 :: Vint32 i1 :: nil) O10 act (v1, Some O10') -> 
    qtimedpost_timeout_err_body (vp2 :: v0 :: Vint32 i2 :: nil) O20 act (v2, Some O20') -> 
    dom_impl O1 O1' ->
    dom_impl O2 O2' -> 
    join O10 Of1 O1 ->
    join O20 Of2 O2 ->
    join O10' Of1 O1' ->
    join O20' Of2 O2' -> 
    data_equiv_tskd i cst1 cst2 O1' O2'.
Proof.
  introv Hde Hd1 Hd2 Hgct1 Hgct2 Htpi1 Htpi2 Hto1 Hto2. 
  introv Hdi1 Hdi2.
  introv Hjo1 Hjo2 Hjo1' Hjo2'.
  unfold data_equiv_tskd in *. 
  destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
  splits.
  
  (* ctid_equiv *) 
  eapply prio_preserved_ctid_eq_preserved; eauto.          
  lets H__: qtimedpost_timeout_err_ctid_same Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_timeout_err_ctid_same Hjo2 Hjo2'; eauto.
  lets H__: qtimedpost_timeout_err_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_timeout_err_prio_preserved Hjo2 Hjo2'; eauto.   

  (* bufs_equiv *) 
  lets H1_: qtimedpost_timeout_err_bufs_same Hjo1 Hjo1'; eauto.
  lets H2_: qtimedpost_timeout_err_bufs_same Hjo2 Hjo2'; eauto. 
  destruct H1_. destruct H2_. 
  eapply bufs_equiv_preserve2; eauto.
  
  lets H__: knl_mq_equiv_timeout_err_preserve2 Hto1 Hto2 Hjo1 Hjo2 Hjo1' Hjo2'; eauto.
  destruct H__.
  destructs Hkde.
  unfolds.
  splits; auto.
  
  (* ports_equiv *) 
  eapply ports_equiv_same_prts_preserve2; eauto.          
  lets H__: qtimedpost_timeout_err_dpid_same Hjo1 Hjo1'; eauto. 
  lets H__: qtimedpost_timeout_err_dpid_same Hjo2 Hjo2'; eauto.
  lets H__: qtimedpost_timeout_err_kpid_same Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_timeout_err_kpid_same Hjo2 Hjo2'; eauto.
  lets H__: qtimedpost_timeout_err_same_prt_ecbs Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_timeout_err_same_prt_ecbs Hjo2 Hjo2'; eauto. 
  lets H__: qtimedpost_timeout_err_prio_preserved Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_timeout_err_prio_preserved Hjo2 Hjo2'; eauto.

  (* (* buffer_equiv *)  *)
  eapply buffer_equiv_qtimedpost_timeout_err_preserve2; eauto. 

  (* cap_equiv *) 
  eapply cap_equiv_preserve2; eauto. 
  lets H__: qtimedpost_timeout_err_cpid_same Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_timeout_err_cpid_same Hjo2 Hjo2'; eauto.
  lets H__: qtimedpost_timeout_err_mqptr_iff Hjo1 Hjo1'; eauto.
  lets H__: qtimedpost_timeout_err_mqptr_iff Hjo2 Hjo2'; eauto.   

  (* client_data_equiv *) 
  eapply cde_prio_preserved_preserve2; eauto. 
  lets H__: qtimedpost_timeout_err_prio_preserved Hjo1 Hjo1'; eauto. 
  lets H__: qtimedpost_timeout_err_prio_preserved Hjo2 Hjo2'; eauto.

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
  | _ => idtac
  end. 
  
Ltac invstep_if :=
  match goal with H: spec_step _ (Aif |_| (_) {_} else {_}) _ _ _ _ |- _ => inverts H end.

Ltac invstep_if1 :=
  match goal with
    H: spec_step _ (Aif |_| (_) {_} else {_}) _ _ _ _,
      H': spec_step _ (Aif |_| (_) {_} else {_}) _ _ _ _ 
    |- _ => inverts H
  end.

Ltac invstep_if2 :=
  match goal with
    H: spec_step _ (Aif |_| (_) {_} else {_}) _ _ _ _,
      H': spec_step _ (Aif |_| (_) {_} else {_}) _ _ _ _ 
    |- _ => inverts H' 
  end.

Ltac invstep_seq :=
  match goal with H: spec_step _ (spec_seq _ _) _ _ _ _ |- _ => inverts H end.

Ltac invstep_seq1 :=
  match goal with
    H: spec_step _ (spec_seq _ _) _ _ _ _,
      H': spec_step _ (spec_seq _ _) _ _ _ _ 
    |- _ => inverts H
  end.

Ltac invstep_seq2 := 
  match goal with
    H: spec_step _ (spec_seq _ _) _ _ _ _,
      H': spec_step _ (spec_seq _ _) _ _ _ _ 
    |- _ => inverts H' 
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

Lemma hidapistep_hidapistep_mqsend_lemma:
forall
  (pc0 : progunit) (T1 T2 : tasks) (O1 O2 : osabst) (O1' O2' : osabst)
  (cst1' cst2' : clientst) (act : action) (i : taskdom) 
  (pr pr1 : priority) (t1 t2 : addrval) (cd1 cd2 cd' cd'0 : spec_code)
  (ke0 : exprcont) (ks1 ks1_ : stmtcont) (t0 t3 : tid),
  no_common_fid pc0 (api_spec, int_spec, get_hprio_d) ->
  pu_noabs pc0 ->
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2 ->
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1 ->
  (flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
          obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2) ->
  obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1 O2 ->
  obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1 O2 ->
  obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1 O2 ->
  (act = TauAct \/ act = SendAct \/ act = RecvAct) ->
  ~ in_intr T1 O1 ->
  get O1 curtid = Some (oscurt t1) ->
  task_prio_id O1 pr t1 ->
  nabt (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_))) ->
  ~ in_intr T2 O2 ->
  get O2 curtid = Some (oscurt t2) ->
  dom_for_prio pr = dom_for_prio pr ->
  task_prio_id O2 pr t2 ->
  nabt (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))) ->
  get T1 t1 = Some (curs (hapi_code cd1), (ke0, ks1_)) ->
  (forall (pr0 : priority) (t1 t2 : tid),
       dom_for_prio pr0 = dom_for_prio pr ->
       task_prio_id O1 pr0 t1 ->
       task_prio_id O2 pr0 t2 ->
       exists c1 c2 ke ks1 ks2,
       get T1 t1 = Some (c1, (ke, ks1)) /\
       get T2 t2 = Some (c2, (ke, ks2)) /\ cmd_equiv pr0 c1 c2 O1 O2 /\ cont_equiv pr0 ks1 ks2 O1 O2) ->
  obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2 ->
  flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
  get O1 curtid = Some (oscurt t1) ->
  (forall pr1 pr2 : priority,
      task_prio_id O1 pr1 t1 ->
      task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) ->
  ctid_equiv (dom_for_prio pr) O1 O2 ->
  (* kports_equiv (dom_for_prio pr) O1 O2 -> *)
  ports_equiv (dom_for_prio pr) O1 O2 ->
  kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
  kernel_task_equiv (dom_for_prio pr) O1 O2 ->
  client_data_equiv (dom_for_prio pr) cst1' cst2' O1 O2 ->
  kernel_data_equiv (dom_for_prio pr) O1 O2 ->
  bufs_equiv (dom_for_prio pr) O1 O2 ->
  cap_equiv (dom_for_prio pr) O1 O2 -> 
  (* hapistep (api_spec, int_spec, get_hprio_d) (curs (hapi_code cd2), (ke0, ks1)) O2 *)
  (*      (curs (hapi_code cd'0), (ke0, ks1)) O2' act -> *)
  spec_step get_hprio_d cd1 O1 cd' O1' act ->
  spec_step get_hprio_d cd2 O2 cd'0 O2' act ->
  head_asrt_sat pr cd1 O1 ->
  head_asrt_sat pr cd2 O2 ->
  vl_equiv cd1 cd2 ->
  ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2) ->
  mqsend_equiv cd1 cd2 ->
  cont_equiv pr ks1_ ks1 O1 O2 ->
  get T2 t2 = Some (curs (hapi_code cd2), (ke0, ks1)) ->
  code_equiv_tskd i (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_)))
    (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))) O1' O2'
  /\ data_equiv_tskd i cst1' cst2' O1' O2'.  
(* dom_for_prio pr1 = i -> *)
(* task_prio_id O1' pr1 t0 -> *)
(* task_prio_id O2' pr1 t3 -> *)
(* (exists c1 c2 ke ks2 ks3, *)
(* get (set T1 t1 (curs (hapi_code cd'), (ke0, ks1_))) t0 = Some (c1, (ke, ks2)) /\ *)
(* get (set T2 t2 (curs (hapi_code cd'0), (ke0, ks1))) t3 = Some (c2, (ke, ks3)) /\ *)
(* cmd_equiv c1 c2 O1' O2' /\ cont_equiv ks2 ks3 O1' O2'). *)
Proof.
  intros.
  rename H into Hncfid. rename H0 into Hpu. rename H1 into Hrch2. 
  rename H2 into Hrch1. rename H3 into Hfloweq. rename H4 into Htdeq. 
  rename H5 into Htmeq. rename H6 into Hsceq. rename H7 into Hact. 
  rename H8 into Hnint1. rename H9 into Hcurt1. rename H10 into Htpi1. 
  rename H11 into Hnabt1. rename H12 into Hnint2. rename H13 into Hcurt2. 
  rename H14 into Hdomeq. rename H15 into Htpi2. rename H16 into Hnabt2. 
  rename H17 into HC1. rename H18 into Hceq. rename H19 into Hd'eq. 
  rename H20 into Hstepdm. rename H21 into Ht1_. rename H22 into Hfa.
  rename H23 into Hctide_.
  (* rename H24 into Hkprte. *)
  rename H24 into Hprte.
  rename H25 into Hkqe. rename H26 into Hkte. rename H27 into Hcde.
  rename H28 into Hkde. rename H29 into Hbufe. rename H30 into Hcpe.
  rename H31 into H. rename H32 into H0.
  rename H33 into Hhsat1.
  rename H34 into Hhsat2.
  rename H35 into Hvleq. rename H36 into Hnex.
  rename H37 into Hsend.  rename H38 into Hcont.
  rename H39 into HC2. 
  (* rename H41 into Hd. rename H42 into Htpi1'. rename H43 into Htpi2'. *)
  match goal with H: spec_step _ cd1 _ ?cd' _ _ |- _ => rename cd' into cd1'; rename H into Hstep1 end.
  match goal with H: spec_step _ cd2 _ ?cd' _ _ |- _ => rename cd' into cd2'; rename H into Hstep2 end.

  unfolds in Hsend.
  destruct Hsend as (vl & vl1 & vl2 & k & Hlenvl & Hlenvl1 & Hlenvl2 & Hnth1 & Hnth2).
  do 5 try destruct vl; tryfalse.
  do 5 try destruct vl1; tryfalse.
  do 5 try destruct vl2; tryfalse.
  simpl in Hnth1. 
  destruct v; destruct v1; simpl in Hnth1;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).  
  destruct v3; destruct v5;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).  
  destruct v6; 
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).

  simpl in Hnth2.
  destruct v7; destruct v9; simpl in Hnth2;
    try (eapply abt_succs_contra in Hnth2; inverts Hstep2; tryfalse; fail).
  destruct v10; simpl in Hnth2;
    try (eapply abt_succs_contra in Hnth2; inverts Hstep2; tryfalse; fail).

  unfold obsr_equiv_tskd in Htdeq. 
  destruct Htdeq as (Hce & Hde).
  unfolds in Hsceq.
  unfolds in Hsceq.
  destruct Hsceq as (Hce_sch & Hde_sch). 

  destruct k.
  
  (* k=0 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe. 

  rmbprog HC1 c1. rmbprog HC2 c2.
  rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.   
  protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
  clear Hnex Hnabt1 Hnabt2.

  {
    split; auto. 
    (** code_equiv_tskd **) 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.    
    unfold cmd_equiv.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split.
    unprotect Heqc1'. subst.
    simpl. auto.
    split.
    unprotect Heqc2'. subst.
    simpl. auto. 
    split.
    introv Hhvl1 Hhvl2.
    unprotect Heqc1'; subst.
    simpl in Hhvl1. 
    inverts Hhvl1. 
    introv Hf. rewrite nth_error_nil in Hf. tryfalse. 
    (* stmt_equiv *)
    unfold stmt_equiv.
    right.
    split.
    introv Hf. 
    unprotect Heqc1'; unprotect Heqc2'; subst.
    simpljoin. tryfalse.
    left.
    (* establish mqsend_equiv *)
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 1%nat. 
  }
  
  destruct k. 
  (* k=1 *)
  simpl in Hnth1; inverts Hnth1. 
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    rmbprog HC1 c1. rmbprog HC2 c2.
    protect Heqc1. protect Heqc2. 
    clear Hnex Hnabt1 Hnabt2.
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_Oeq H1; lets H2_: rv_Oeq H2; subst 
    end.  
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. 
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst 
    end. 
    apply cmd_equiv_end. 
  }
  {
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_Oeq H1; lets H2_: rv_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.    
    eapply H__; eauto.
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst 
    end.    
    apply cmd_equiv_end.
  }
  {
    false.
    match goal with H: ~(forall _, _) |- _ => apply H end.
    introv Hdct.
    eapply H10; eauto. 
    lets Hdct_: data_equiv_schd_dom_equiv Hde_sch td.
    destruct Hdct_ as (Hdct12 & Hdct21).
    apply Hdct12; auto.
  }
  {
    false.
    match goal with H: ~(forall _, _) |- _ => apply H end.
    introv Hdct.
    eapply H17; eauto. 
    lets Hdct_: data_equiv_schd_dom_equiv Hde_sch td.
    destruct Hdct_ as (Hdct12 & Hdct21).
    apply Hdct21; auto.
  }
  {
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.   
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.
    match goal with
      H1: spec_skip_step _ _ _ _, H2: spec_skip_step _ _ _ _ |- _ =>
        lets H1_: skip_Oeq H1; lets H2_: skip_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.    
    eapply H__; eauto.    
    unfold cmd_equiv.
    right.
    do 2 eexists.
    split; eauto.
    split; eauto.
    split. unprotect Heqc1'; subst. simpl; auto.
    eapply mqd_in_cdom_holds; eauto. 
    split. unprotect Heqc2'; subst. simpl; auto.
    eapply mqd_in_cdom_holds; eauto. 
    split.
    unfolds. introv Hc1' Hc2' Hf. 
    unprotect Heqc1'; subst.
    simpl in Hc1'. inverts Hc1'.
    rewrite nth_error_nil in Hf. tryfalse. 
    unfold stmt_equiv.
    right.
    split.
    introv Hf. unprotect Heqc1'; unprotect Heqc2'; subst.
    simpljoin. solve [false].
    left.
    (* mqsend_equiv c1' c2' *)
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 2%nat. 
  }
  
  destruct k.
  (* k=2 *)
  simpl in Hnth1; inverts Hnth1. 
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    match goal with
      H1: mqsend_get_msgsize _ _ _ _, H2: mqsend_get_msgsize _ _ _ _ |- _ =>
        lets H1_: get_msize_Oeq H1; lets H2_: get_msize_Oeq H2; subst  
    end.
    assert (O1' = O1). { join auto. }
    assert (O2' = O2). { join auto. }
    subst.
    assert (Hidm1: mqd_in_dom i0 O1 pr). { simpl in Hhsat1; auto. }
    assert (Hidm2: mqd_in_dom i0 O2 pr). { simpl in Hhsat2; auto. } 
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.
    split; auto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.    
    eapply H__; eauto.    
    unfold cmd_equiv.
    right.
    do 2 eexists.
    split; eauto.
    split; eauto.
    split.
    unprotect Heqc1'; subst. simpl. exact Hidm1. 
    split. 
    unprotect Heqc2'; subst. simpl. exact Hidm2.
    split.
    (* vl_equiv *) 
    unprotect Heqc1'; unprotect Heqc2'; rewrite Heqc1'; rewrite Heqc2'. 
    eapply veq_vlequiv; eauto.
    simpl; eauto.
    simpl; eauto.
    clear Heqc1'. clear Heqc2'. 
    assert (Heqv: Vint32 i5 = Vint32 i2).
    {
      symmetry. eapply mqequiv_get_msize_veq; eauto. 
    }
    rewrite Heqv. auto. 
    (* stmt_equiv *)
    unfolds.
    right.
    split.
    introv Hf. simpljoin. unprotect Heqc1'. solve [false].
    left.
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 3%nat. 
  }

  destruct k.
  (* k=3 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe. 
  {
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_Oeq H1; lets H2_: rv_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst  
    end.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. simpl; auto. split. simpl; auto.
    split. unfolds. introv Hg. simpl in Hg. tryfalse.
    (* stmt_equiv END END *)
    unfolds. left. eexists; split; eauto.
  }
  {
    clear Hnex.   
    lets Hieq_: vlequiv_veq Hvleq.
    simpl in Hieq_.
    specialize (Hieq_ (eq_refl _) (eq_refl _)).
    rewrite Hieq_ in *.
    match goal with H1: Int.ltu _ _ = true,  H2: Int.ltu _ _ <> true |- _ => rewrite H1 in H2; tryfalse end. 
  }
  {
    clear Hnex.
    lets Hieq_: vlequiv_veq Hvleq.
    simpl in Hieq_.
    specialize (Hieq_ (eq_refl _) (eq_refl _)).
    rewrite Hieq_ in *.
    match goal with H1: Int.ltu _ _ = true,  H2: Int.ltu _ _ <> true |- _ => rewrite H1 in H2; tryfalse end. 
  }
  {
    assert (Hidm1: mqd_in_dom i0 O1 pr). { simpl in Hhsat1; auto. }
    assert (Hidm2: mqd_in_dom i0 O2 pr). { simpl in Hhsat1; auto. }
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.
    match goal with
      H1: spec_skip_step _ _ _ _, H2: spec_skip_step _ _ _ _ |- _ =>
        lets H1_: skip_Oeq H1; lets H2_: skip_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    (* cmd_equiv c1' c2' *)
    unfolds.
    right. do 2 eexists. split; eauto. split; eauto.
    split.
    unprotect Heqc1'. subst c1'. simpl. exact Hidm1.
    split.
    unprotect Heqc2'. subst c2'. simpl. exact Hidm2.
    split.
    unfold vl_equiv.
    introv Hg _ Hf. unprotect Heqc1'; subst c1'.
    simpl in Hg; inverts Hg.
    rewrite nth_error_nil in Hf. solve [false].
    (* stmt_equiv *)
    unfolds. right.
    split. introv Hf. simpljoin. unprotect Heqc1'. solve [false].
    left.
    (* mqsend_equiv c1' c2' *)
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 4%nat. 
  }

  destruct k.
  (* k=4 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.      
  symexe. 
  {
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_Oeq H1; lets H2_: rv_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst  
    end.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    (* cmd_equiv END END *)
    eapply cmd_equiv_end; eauto. 
  }
  {    
    assert (Hidm1: mqd_in_dom i0 O1 pr). 
    { simpl in Hhsat1; auto. }
    assert (Hidm2: mqd_in_dom i0 O2 pr). 
    { simpl in Hhsat2; auto. }
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.  
    match goal with
      H1: mqsend_get_ecb_ptr _ _ _ _, H2: mqsend_get_ecb_ptr _ _ _ _ |- _ => 
        lets H1_: ms_getep_Oeq H1; lets H2_: ms_getep_Oeq H2; subst 
    end. 
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto.
    clear H__.
    (* cmd_equiv c1' c2' *)
    unfolds.
    right.
    do 2 eexists.
    split. eauto. split. eauto.
    split. unprotect Heqc1'; subst c1'. simpl. 
    eapply idm_getep_dom_qptr; eauto.
    split. unprotect Heqc2'; subst c2'. simpl.
    eapply idm_getep_dom_qptr; eauto.
    split.
    eapply vl_equiv_nil; eauto. 
    unprotect Heqc1'; subst c1'; simpl; auto.
    (* stmt_equiv c1' c2' *)
    unfolds.
    right.
    split.
    introv Hf. unprotect Heqc1'; subst c1'; simpljoin; solve [false].
    left.
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 5%nat. 
  }

  destruct k. 
  (* k=5 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe. 

  match goal with
    H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
      lets H1_: rv_Oeq H1; lets H2_: rv_Oeq H2; subst  
  end.
  assert (O1 = O1'). { join auto. }
  assert (O2 = O2'). { join auto. }
  subst.
  match goal with
    H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
      lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst  
  end.
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
  eapply H__; eauto.
  eapply cmd_equiv_end; eauto.
  (* apply nabt_abt_false in Hnabt1. solve [false]. *)
  (* step_contra0. *)
  (* step_contra0. *)
  {
    assert (Hdqp1: mqdes_dom_qptr i0 v4 O1 pr). { simpl in Hhsat1; auto. }
    assert (Hdqp2: mqdes_dom_qptr i0 Vnull O2 pr). { simpl in Hhsat2; auto. }  
    lets H__: mq_equiv_qptr_veq Hkqe Hdqp1 Hdqp2.
    destruct H__ as (Hnull & Hptr).
    destruct Hnull as (Hvnull & Hnulleq).
    specialize (Hnulleq (eq_refl _)).
    subst.
    destruct Hptr; simpljoin; tryfalse. 
  }
  {
    assert (Hdqp1: mqdes_dom_qptr i0 Vnull O1 pr). { simpl in Hhsat1; auto. }
    assert (Hdqp2: mqdes_dom_qptr i0 v8 O2 pr). { simpl in Hhsat2; auto. }    
    lets H__: mq_equiv_qptr_veq Hkqe Hdqp1 Hdqp2.
    destruct H__ as (Hnull & Hptr).
    destruct Hnull as (Hvnull & Hnulleq).
    specialize (Hvnull (eq_refl _)).
    subst.
    destruct Hptr; simpljoin; tryfalse. 
  }
  {
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.      
    match goal with
      H1: spec_skip_step _ _ _ _, H2: spec_skip_step _ _ _ _ |- _ =>
        lets H1_: skip_Oeq H1; lets H2_: skip_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    (* cmd_equiv *)
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split.
    unprotect Heqc1; unprotect Heqc1'; subst c1; subst c1'; simpl in Hhsat1; simpl.
    simpl in Hhsat1. auto. 
    (* eapply mqdes_domqp_mqidm; eauto.  *) 
    split. 
    unprotect Heqc2; unprotect Heqc2'; subst c2; subst c2'; simpl in Hhsat2; simpl.
    simpl in Hhsat2. auto. 
    (* eapply mqdes_domqp_mqidm; eauto. *)
    split.
    eapply vl_equiv_nil; eauto. 
    unprotect Heqc1'; subst c1'. simpl; auto. 
    (* stmt_equiv *)
    unfolds.
    right.
    split. introv Hf. unprotect Heqc1'; subst c1'; simpljoin; tryfalse.
    left.
    (* mqsend_equiv c1' c2' *) 
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 6%nat. 
  }

  destruct k.
  (* k=6 *)  
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    assert (Hmd1: mqdes_dom_qptr i0 v4 O1 pr).
    { simpl in Hhsat1. auto. }
    assert (Hmd2: mqdes_dom_qptr i0 v8 O2 pr).
    { simpl in Hhsat2. auto. }
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.      
    match goal with
      H1: mqsend_get_mqflags _ _ _ _, H2: mqsend_get_mqflags _ _ _ _ |- _ =>
        lets H1_: mqgf_Oeq H1; lets H2_: mqgf_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto. 
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    (* cmd_equiv *)
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. unprotect Heqc1'; subst c1'; simpl; auto.
    split. unprotect Heqc2'; subst c2'; simpl; auto.
    assert (Hd1: mqd_in_dom i0 O1' pr).
    { unfolds in Hmd1. simpljoin. auto. } 
    assert (Hd2: mqd_in_dom i0 O2' pr).
    { unfolds in Hmd2. simpljoin. auto. }
    lets Hpre: mq_equiv_flg_veq Hkqe Hd1 Hd2.
    lets H__': Hpre H4 H3; eauto. clear Hpre. 
    subst.
    split.
    eapply veq_vlequiv; eauto.
    unprotect Heqc1'; subst c1'; simpl; eauto.
    unprotect Heqc2'; subst c2'; simpl; eauto.
    (* stmt_equiv *)
    unfolds.
    right.
    split. introv Hf. unprotect Heqc1'; subst c1'; simpljoin; tryfalse.
    left.
    (* mqsend_equiv c1' c2' *) 
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 7%nat. 
  }
  
  destruct k.
  (* k=7 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_Oeq H1; lets H2_: rv_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto.
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst  
    end.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    apply cmd_equiv_end.    
  }  
  {
    lets Heqv: vlequiv_veq Hvleq; eauto.
    simpl in Heqv.
    specialize (Heqv (eq_refl _) (eq_refl _)).
    subst.
    tryfalse.
  }
  {
    lets Heqv: vlequiv_veq Hvleq; eauto.
    simpl in Heqv.
    specialize (Heqv (eq_refl _) (eq_refl _)).
    subst.
    tryfalse.
  }
  {
    assert (Hmd1: mqdes_dom_qptr i0 v4 O1 pr). 
    { simpl in Hhsat1. auto. }
    assert (Hmd2: mqdes_dom_qptr i0 v8 O2 pr). 
    { simpl in Hhsat2. auto. } 
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.      
    match goal with
      H1: spec_skip_step _ _ _ _, H2: spec_skip_step _ _ _ _ |- _ =>
        lets H1_: skip_Oeq H1; lets H2_: skip_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto. 
    split. unprotect Heqc1'; subst c1'. simpl; auto.
    split. unprotect Heqc2'; subst c2'. simpl; auto.
    split.
    unprotect Heqc1'; unprotect Heqc2'; subst c1'; subst c2'. 
    eapply veq_vlequiv; eauto. simpl; eauto.  simpl; eauto.
    symmetry.
    match goal with H: _ |- Some (Vint32 ?i1 :: nil) = Some (Vint32 ?i2 :: nil) => cut (i1 = i2) end.
    intros; subst; auto. 
    eapply vlequiv_veq; eauto. 
    unprotect Heqc1; subst c1; simpl; auto.
    unprotect Heqc2; subst c2; simpl; auto.
    (* stmt_equiv *)
    unfolds.
    right. split. introv Hf. unprotect Heqc1'; subst c1'; simpljoin; tryfalse.
    left.
    (* mqsend_equiv c1' c2' *)
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 8%nat. 
  }

  destruct k.
  (* k=8 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_Oeq H1; lets H2_: rv_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto.
    match goal with
      H1: ret_val _ _ _ _, H2: ret_val _ _ _ _ |- _ =>
        lets H1_: rv_veq H1; lets H2_: rv_veq H2; subst  
    end.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    apply cmd_equiv_end.  
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.
    apply cap_equiv_sym in Hcpe. 
    assert (Hrl: has_no_cap_send O2 v8 -> has_no_cap_send O1 v4).
    { eapply cap_equiv_sendcap_equiv; eauto. }
    specializes Hrl; eauto. 
    solve [false].
  }
  {
    simpl in Hhsat1.
    simpl in Hhsat2.
    assert (Hlr: has_no_cap_send O1 v4 -> has_no_cap_send O2 v8).
    { eapply cap_equiv_sendcap_equiv; eauto. }
    specializes Hlr; eauto.
    solve [false]. 
  }
  {
    assert (Hmd1: mqdes_dom_qptr i0 v4 O1 pr).
    { simpl in Hhsat1; auto. }
    assert (Hmd2: mqdes_dom_qptr i0 v8 O2 pr).
    { simpl in Hhsat2; auto. }    
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.      
    match goal with
      H1: spec_skip_step _ _ _ _, H2: spec_skip_step _ _ _ _ |- _ =>
        lets H1_: skip_Oeq H1; lets H2_: skip_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. unprotect Heqc1'; subst c1'. simpl. auto.
    split. unprotect Heqc2'; subst c2'. simpl. auto.
    split.
    eapply veq_vlequiv; eauto.
    unprotect Heqc1'; subst c1'; simpl; eauto.
    unprotect Heqc2'; subst c2'; simpl; eauto.    
    match goal with H: _ |- Some (?v1 :: nil) = Some (?v2 :: nil) => cut (v1 = v2) end.
    introv Heq; rewrite Heq; auto. 
    symmetry.
    eapply vlequiv_veq'; eauto.    
    unprotect Heqc1; rewrite Heqc1. simpl; auto.
    unprotect Heqc2; rewrite Heqc2. simpl; auto. 
    (* stmt_equiv c1' c2' *) 
    unfolds.
    right.
    split.
    introv Hf. unprotect Heqc1'; subst c1'; simpljoin; solve [false].
    left.
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 9%nat. 
  }
  
  destruct k.
  (* k=9 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  {
    rmbprog HC1 c1. rmbprog HC2 c2.
    rmbprog' Hnabt1 c1'. rmbprog' Hnabt2 c2'.
    protect Heqc1. protect Heqc2. protect Heqc1'. protect Heqc2'.
    clear Hnex Hnabt1 Hnabt2.      
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    (* cmd_equiv c1' c2' *)
    unfolds.
    right.
    do 2 eexists. split; eauto. split; eauto.
    split. 
    unprotect Heqc1'; rewrite Heqc1'; simpl.
    unprotect Heqc1; rewrite Heqc1 in Hhsat1; simpl in Hhsat1; auto.
    split.
    unprotect Heqc2'; rewrite Heqc2'; simpl.
    unprotect Heqc2; rewrite Heqc2 in Hhsat2; simpl in Hhsat2; auto. 
    split.
    eapply vl_equiv_nil; eauto.   
    unprotect Heqc1'; rewrite Heqc1'; simpl; eauto.
    (* stmt_equiv c1' c2' *)
    unfolds.
    right.
    split. introv Hf; unprotect Heqc1'; subst c1'; simpljoin; tryfalse. 
    left.
    (* mqsend_equiv c1' c2' *)
    solve_qsend_equiv Hlenvl Hlenvl1 Hlenvl2 Heqc1' Heqc2' 10%nat. 
  }
  {
    lets Heq_: vlequiv_veq Hvleq; eauto.
    simpl in Heq_.
    specializes Heq_; eauto. 
    subst.
    tryfalse. 
  }
  {
    lets Heq_: vlequiv_veq Hvleq; eauto.
    simpl in Heq_.
    specializes Heq_; eauto. 
    subst.
    tryfalse. 
  }
  {
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    unfolds.
    right. 
    do 2 eexists. split; auto. split; eauto.
    split.
    simpl. simpl in Hhsat1; auto.
    split.
    simpl. simpl in Hhsat2; auto.
    split.
    eapply vl_equiv_nil; eauto.
    (* stmt_equiv *)
    unfolds.
    right.
    split.
    introv Hf; simpljoin; tryfalse. 
    left.
    (* mqsend_equiv *)
    solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 16%nat. 
  }
  
  destruct k. 
  (* k=10 *)  
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  simpl in Hhsat1. simpl in Hhsat2.
  lets Hpeqv: mq_equiv_qptr_veq Hkqe Hhsat1 Hhsat2.
  destruct Hpeqv as ((Hnulleq1 & Hnulleq2) & (Hptreq1 & Hptreq2)).
  inverts Hstep1.
  inverts Hstep2.
  step_contra0.
  invstep_if.
  
  {
    step_contra0.
    step_contra0.
    match goal with
      H1: asrt_and_ret _ _ _ _, H2: asrt_and_ret _ _ _ _ |- _ =>
        lets H1_: aar_Oeq H1; lets H2_: aar_Oeq H2; subst  
    end.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
    eapply H__; eauto. clear H__.
    (* cmd_equiv *)
    eapply ceq_send_res; eauto. 
    match goal with
      H1: asrt_and_ret _ _ _ _, H2: asrt_and_ret _ _ _ _ |- _ =>
        lets H1_: aar_veq12 H1; lets H2_: aar_veq12 H2; subst  
    end.
    congruence. 
  }
  {
    invstep_if. 
    specializes Hnulleq2; auto; solve [false].
    specializes Hnulleq2; auto; solve [false].
  }
  {
    invstep_if1. 
    specializes Hnulleq1; auto; solve [false].
    step_contra0.
    invstep_if.
    {
      step_contra0.
      step_contra0. 
      match goal with
        H1: asrt_and_ret _ _ _ _, H2: asrt_and_ret _ _ _ _ |- _ =>
          lets H1_: aar_Oeq H1; lets H2_: aar_Oeq H2; subst  
      end.
      assert (O1 = O1'). { join auto. }
      assert (O2 = O2'). { join auto. }
      subst.
      split; auto.
      lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
      eapply H__; eauto. clear H__.
      (* cmd_equiv *)
      eapply ceq_send_res; eauto. 
      match goal with
        H1: asrt_and_ret _ _ _ _, H2: asrt_and_ret _ _ _ _ |- _ =>
          lets H1_: aar_veq12 H1; lets H2_: aar_veq12 H2; subst  
      end.
      congruence.       
    }
    {
      simpljoin.
      specializes Hptreq1; eauto.
      simpljoin.
      match goal with
        H: ~(exists _, _ /\ Vnull=Vnull) |- _ => false; apply H; eexists; split; eauto 
      end.
    }
    {      
      invstep_if1.
      - 
        simpljoin. 
        specializes Hptreq2; [ eexists; eauto | idtac ].
        simpljoin.
        match goal with
          H: ~(exists _, _ /\ Vnull=Vnull) |- _ => false; apply H
        end.      
        eexists; split; eauto.
      -
        invstep_if. 
        invstep_if.
        step_contra0.
        step_contra0.
        {
          match goal with
            H1: asrt_and_ret _ _ _ _, H2: asrt_and_ret _ _ _ _ |- _ =>
              lets H1_: aar_Oeq H1; lets H2_: aar_Oeq H2; subst  
          end.
          assert (O1 = O1'). { join auto. }
          assert (O2 = O2'). { join auto. }
          subst.
          split; auto.
          lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2.
          eapply H__; eauto. clear H__.
          eapply ceq_send_res; eauto. 
          match goal with
            H1: asrt_and_ret _ _ _ _, H2: asrt_and_ret _ _ _ _ |- _ =>
              lets H1_: aar_veq12 H1; lets H2_: aar_veq12 H2; subst  
          end.
          congruence.
        }
        {
          apply knl_mq_equiv_sym in Hkqe.
          lets Hf__: mq_equiv_noque_false v0 Hhsat2 Hhsat1 Hkqe.          
          tryfalse. 
        }
        invstep_if1.
        {
          lets Hf__: mq_equiv_noque_false v0 Hhsat1 Hhsat2 Hkqe.
          tryfalse. 
        }
        {
          invstep_if2.
          step_contra0.
          invstep_if1.
          step_contra0.
          invstep_if2.
          step_contra0.
          false.
          invstep_if1.
          step_contra0.
          false. 

          invstep_if2.
          step_contra0.
          invstep_if1.
          step_contra0.

          invstep_if1.
          invstep_if.
          {
            step_contra0.
            step_contra0.              
            split.
            -
              (* code_equiv *)
              lets Hpp1: qpost_nowt_succ_prio_preserved O1 O1' O0 O'0; eauto.
              specializes Hpp1; eauto.
              lets Hpp2: qpost_nowt_succ_prio_preserved O2 O2' O O'; eauto.
              specializes Hpp2; eauto.
              apply11 qpost_nowt_succ_body qpost_nowt_succ_body
                qpost_nowt_succ_cpid_same Hcpeq2 Hcpeq1.
              specializes Hcpeq1; eauto.
              specializes Hcpeq2; eauto. 

              eapply code_equiv_upd2_preserve_st'; eauto.
              {
                (* cmd_equiv *)
                match goal with
                  H: context [qpost_nowt_succ_body] |- _ =>
                    eapply qpost_nowt_succ_ret in H; eauto
                end.
                match goal with
                  H: context [qpost_nowt_succ_body] |- _ =>
                    eapply qpost_nowt_succ_ret in H; eauto
                end.
                eapply ceq_send_res; eauto.
                congruence.
              }
              eapply cont_equiv_qref_preserve; eauto. 
              eapply qpost_nowt_succ_mqref_preserve; eauto.
              eapply qpost_nowt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
              eapply qpost_nowt_succ_qprt_preserve; eauto.
              eapply qpost_nowt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.
              eapply eqdom_frm_domimpl; eauto.
              eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

              lets H__: code_equiv_hsat_neq_st'; eauto.
              eapply H__; eauto.
              eapply qpost_nowt_succ_mqref_preserve; eauto.
              eapply qpost_nowt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
              eapply qpost_nowt_succ_qprt_preserve; eauto.
              eapply qpost_nowt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.              
              eapply eqdom_frm_domimpl; eauto.
              eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
             
            -
              (* data_equiv *)
              eapply qpost_nowt_succ_body_dteq_preserve2; eauto.
          }
          step_contra0. tryfalse.
          step_contra0. tryfalse. 
        }
    }
  }
  {
    apply nabt_abt_false in Hnabt2. solve [false].
  }
  {
    invstep_if2.
    step_contra0; solve_endabt.
    invstep_if1.
    specializes Hnulleq1; [ eauto | idtac ].
    simpljoin. solve [false].
    
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1. 
    simpljoin.
    specializes Hptreq1; [ eauto | idtac ].
    match goal with
      H: ~(exists _, _ /\ Vnull=Vnull) |- _ => false; apply H
    end.      
    simpljoin. eexists; split; eauto. 

    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.
    lets Hf__: mq_equiv_noque_false v0 Hhsat1 Hhsat2 Hkqe.
    tryfalse.  

    invstep_if2.
    step_contra0. 
    invstep_if1.
    apply knl_mq_equiv_sym in Hkqe. 
    lets H__: mq_equiv_wls_impl Hhsat2 Hhsat1 Hkqe.
    specializes H__; [ eauto | idtac ].
    tryfalse. 
    
    invstep_if1.
    step_contra0. false.
    invstep_if1.
    step_contra0. tryfalse. 
    solve_endabt.

    invstep_if1.
    step_contra0.       
    invstep_if1.
    apply knl_mq_equiv_sym in Hkqe.
    lets H__: mq_equiv_qlen_impl Hhsat2 Hhsat1.
    specializes H__; eauto.
    tryfalse. 
    
    invstep_if2.
    step_contra0; solve_endabt.

    step_contra0. false. 
  }
  {
    apply nabt_abt_false in Hnabt1. solve [false].
  }
  {
    inverts Hstep2.
    {
      invstep_if1.  
      step_contra0; solve_endabt.
      invstep_if1.
      specializes Hnulleq2; [ eauto | idtac ].
      simpljoin. solve [false].
      
      invstep_if1.
      step_contra0; solve_endabt.
      invstep_if1. 
      simpljoin.
      specializes Hptreq2; [ eauto | idtac ].
      match goal with
        H: ~(exists _, _ /\ Vnull=Vnull) |- _ => false; apply H
      end.      
      simpljoin. eexists; split; eauto. 

      invstep_if1.
      step_contra0; solve_endabt.
      invstep_if1.
      apply knl_mq_equiv_sym in Hkqe. 
      lets Hf__: mq_equiv_noque_false v0 Hhsat2 Hhsat1.
      specializes Hf__; eauto. 
      tryfalse.  

      invstep_if2.
      step_contra0. 
      invstep_if1.
      lets H__: mq_equiv_wls_impl Hhsat1 Hhsat2. 
      specializes H__; eauto. 
      tryfalse. 
      
      invstep_if1.
      step_contra0. false.
      invstep_if1.
      step_contra0. tryfalse. 
      solve_endabt.

      invstep_if1.
      step_contra0.   
      invstep_if1.
      lets H__: mq_equiv_qlen_impl Hhsat1 Hhsat2.
      specializes H__; eauto.
      tryfalse. 
      
      invstep_if2.
      step_contra0; solve_endabt.

      step_contra0. false. 
    }
    {
      apply nabt_abt_false in Hnabt2; false.
    }
    {
      invstep_if1.
      step_contra0; solve_endabt.
      invstep_if1.
      step_contra0; solve_endabt.
      invstep_if1.
      step_contra0; solve_endabt.
      invstep_if1.
      step_contra0; solve_endabt.
      invstep_if1.
      step_contra0; solve_endabt.
      invstep_if1.
      step_contra0; solve_endabt.
      
      invstep_if1.
      invstep_if.
      2: {
        lets H__: mq_equiv_wls_impl Hhsat1 Hhsat2 Hkqe; eauto.
        specializes H__; eauto.
        tryfalse.
      }
      {
        step_contra0.
        2: solve_endabt.
        2: { step_contra0; solve_endabt. }
        step_contra0.
        step_contra0.
        2: { solve_endabt. }
        2: { step_contra0; solve_endabt. }
        step_contra0.

        split.
        - (* code_equiv  *)
              lets Hpp1: qpost_exwt_succ_prio_preserved O1 O1' O0 O'0; eauto.
              specializes Hpp1; eauto.
              lets Hpp2: qpost_exwt_succ_prio_preserved O2 O2' O O'; eauto.
              specializes Hpp2; eauto. 
              apply11 qpost_exwt_succ_body qpost_exwt_succ_body
                qpost_exwt_succ_cpid_same Hcpeq2 Hcpeq1.
              specializes Hcpeq1; eauto.
              specializes Hcpeq2; eauto. 

              eapply code_equiv_upd2_preserve_st'; eauto.
              {
                (* cmd_equiv *)
                unfolds.
                right.
                do 2 eexists.
                split; eauto. split; eauto.
                split. simpl; auto. split. simpl; auto.
                split.
                eapply vl_equiv_nil; eauto.
                unfolds.
                right.
                split. introv Hf. simpljoin. tryfalse.
                left.
                solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 17%nat. 
              }
              eapply cont_equiv_qref_preserve; eauto. 
              eapply qpost_exwt_succ_mqref_preserve; eauto.
              eapply qpost_exwt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
              eapply qpost_exwt_succ_qprt_preserve; eauto.
              eapply qpost_exwt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.      
              eapply eqdom_frm_domimpl; eauto.
              eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.    

              lets H__: code_equiv_hsat_neq_st'; eauto.
              eapply H__; eauto.
              eapply qpost_exwt_succ_mqref_preserve; eauto.
              eapply qpost_exwt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
              eapply qpost_exwt_succ_qprt_preserve; eauto.
              eapply qpost_exwt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.                    
              eapply eqdom_frm_domimpl; eauto.
              eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
          
        - (* data_equiv *)           
          eapply qpost_exwt_succ_dteq_preserve2; eauto.
      }
      {
        invstep_if1.
        apply knl_mq_equiv_sym in Hkqe.
        lets H__: mq_equiv_wls_impl Hhsat2 Hhsat1 Hkqe; eauto.
        specializes H__; eauto.
        tryfalse.

        invstep_if1.
        step_contra0; solve_endabt.
        invstep_if1.
        step_contra0; solve_endabt.
        
        invstep_if1;
        invstep_if.
        {

          invstep_seq1.
          invstep_seq.
          step_contra0.
          step_contra0. 

          {
          split.
          - (* code_equiv *) 
            lets Hpp1: qtimedpost_ovf_block_prio_preserved O1 O1' O0 O'0; eauto. 
            specializes Hpp1; eauto.
            lets Hpp2: qtimedpost_ovf_block_prio_preserved O2 O2' O O'; eauto.
            specializes Hpp2; eauto. 
            apply11 qtimedpost_ovf_block_body qtimedpost_ovf_block_body
              qtimedpost_ovf_block_cpid_same Hcpeq2 Hcpeq1.
            specializes Hcpeq1; eauto.
            specializes Hcpeq2; eauto. 

            eapply code_equiv_upd2_preserve_st'; eauto.
              
            (* cmd_equiv *)
            unfolds.
            right.
            do 2 eexists.
            split; eauto. split; eauto.
            split. simpl; auto.
            eapply qtimedpost_ovf_block_mqd_impl; eauto. 
            split. simpl; auto.
            eapply qtimedpost_ovf_block_mqd_impl with (O0:=O) (O0':=O'); eauto. 
            split.
            eapply vl_equiv_nil; eauto.
            unfolds.
            right.
            split. introv Hf. simpljoin. tryfalse.
            left.
            solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 13%nat.     
            
            (* cont_equiv *)
            eapply cont_equiv_qref_preserve; eauto.  
            eapply qtimedpost_ovf_block_mqref_preserve; eauto. 
            eapply qtimedpost_ovf_block_mqref_preserve with (O0:=O) (O0':=O'); eauto.
            eapply qtimedpost_ovf_block_qprt_preserve; eauto. 
            eapply qtimedpost_ovf_block_qprt_preserve with (O0:=O) (O0':=O'); eauto.   
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
            
            lets H__: code_equiv_hsat_neq_st'; eauto.
            eapply H__; eauto. 
            eapply qtimedpost_ovf_block_mqref_preserve; eauto.
            eapply qtimedpost_ovf_block_mqref_preserve with (O0:=O) (O0':=O'); eauto. 
            eapply qtimedpost_ovf_block_qprt_preserve; eauto. 
            eapply qtimedpost_ovf_block_qprt_preserve with (O0:=O) (O0':=O'); eauto.   
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

          - (* data_equiv *)
            eapply qtimedpost_ovf_block_dteq_preserve2; eauto.
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
          }

          solve_endabt.
          step_contra0; solve_endabt. 
          solve_endabt.
          step_contra0; solve_endabt. 
        }
        lets H__: mq_equiv_qlen_impl Hkqe; eauto. 
        autospcz.
        false.
        
        step_contra0; solve_endabt. 
        step_contra0. false. 
      }              
    }
  }

  destruct k. 
  (* k=11 *) 
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
  eapply H__; eauto.
  unfolds. 
  right.
  do 2 eexists.
  split; eauto.
  split; eauto.
  split.  simpl; auto. split. simpl; auto.
  split.
  eapply vl_equiv_nil; eauto. 
  unfolds.
  right.
  split. introv Hf. simpljoin. tryfalse.
  left.
  solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 18%nat.    

  destruct k. 
  (* k=12 *) 
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  match goal with
    H1: asrt_and_ret _ _ _ _, H2: asrt_and_ret _ _ _ _ |- _ =>
      lets H1_: aar_Oeq H1; lets H2_: aar_Oeq H2; subst  
  end.
  assert (O1 = O1'). { join auto. }
  assert (O2 = O2'). { join auto. }
  subst.
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
  eapply H__; eauto.
  apply11 asrt_and_ret asrt_and_ret aar_veq12 He1_ He2_.
  inverts He1_.
  inverts He2_. 
  eapply ceq_send_res; eauto. 

  destruct k. 
  (* k=13 *) 
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
  eapply H__; eauto. clear H__.
  unfolds. 
  right.
  do 2 eexists.
  split; eauto.
  split; eauto.
  split. simpl; auto.
  split. simpl; auto.
  split.
  eapply vl_equiv_nil; simpl; auto. 
  unfolds.
  right.
  split. introv Hf. simpljoin; tryfalse.
  left.
  solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 14%nat.    
  
  destruct k. 
  (* k=14 *) 
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.   
  apply11 qtimedpost_after_sched qtimedpost_after_sched
    qtimedpost_after_sched_Oeq H1_ H2_.
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
  split. simpl; auto.
  split. simpl; auto.
  split.
  eapply vl_equiv_nil; simpl; auto. 
  unfolds.
  right.
  split. introv Hf. simpljoin; tryfalse.
  left.
  solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 15%nat.    

  destruct k. 
  (* k=15 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  invstep_seq1.
  {
    invstep_seq.
    
    invstep_if1.
    invstep_if.

    {
      step_contra0.
      step_contra0.
      
      split.
      - (* code_equiv *) 
        lets Hpp1: qtimedpost_timeout_err_prio_preserved O1 O1' O0 O'0; eauto. 
        specializes Hpp1; eauto.
        lets Hpp2: qtimedpost_timeout_err_prio_preserved O2 O2' O O'; eauto.
        specializes Hpp2; eauto.
        apply11 qtimedpost_timeout_err_body qtimedpost_timeout_err_body
          qtimedpost_timeout_err_cpid_same Hcpeq2 Hcpeq1.
        specializes Hcpeq1; eauto.
        specializes Hcpeq2; eauto. 

        eapply code_equiv_upd2_preserve_st'; eauto.

        apply11 qtimedpost_timeout_err_body qtimedpost_timeout_err_body
          qtimedpost_timeout_err_ret H1_ H2_.
        subst.
        
        (* cmd_equiv *)
        unfolds.
        right.
        do 2 eexists.
        split; eauto. split; eauto.
        split. simpl; auto.
        split. simpl; auto.
        split. 
        eapply veq_vlequiv; eauto.
        simpl. eauto.
        simpl. auto.
        unfolds.
        right.
        split. introv Hf. simpljoin; tryfalse.
        left.
        solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 19%nat.    
        
        (* cont_equiv *)
        eapply cont_equiv_qref_preserve; eauto.        
        eapply qtimedpost_timeout_err_mqref_preserve; eauto. 
        eapply qtimedpost_timeout_err_mqref_preserve with (O0:=O) (O0':=O'); eauto.
        eapply qtimedpost_timeout_err_qprt_preserve; eauto. 
        eapply qtimedpost_timeout_err_qprt_preserve with (O0:=O) (O0':=O'); eauto.
        eapply eqdom_frm_domimpl; eauto.
        eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.

        lets H__: code_equiv_hsat_neq_st'; eauto. 
        eapply H__; eauto. 
        eapply qtimedpost_timeout_err_mqref_preserve; eauto.
        eapply qtimedpost_timeout_err_mqref_preserve with (O0:=O) (O0':=O'); eauto.
        eapply qtimedpost_timeout_err_qprt_preserve; eauto.
        eapply qtimedpost_timeout_err_qprt_preserve with (O0:=O) (O0':=O'); eauto.        
        eapply eqdom_frm_domimpl; eauto.
        eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

      - (* data_equiv_tskd *) 
        
        eapply qtimedpost_timeout_err_dteq_preserve2; eauto.
        eapply eqdom_frm_domimpl; eauto.
        eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
    }

    lets H__: mq_equiv_post_to_impl Hkqe; eauto.
    specializes H__; eauto. 
    false.

    invstep_if1.
    apply knl_mq_equiv_sym in Hkqe.
    apply kernel_task_equiv_sym in Hkte.
    apply ctid_equiv_sym in Hctide_; eauto. 
    apply data_equiv_schd_sym in Hde_sch. 
    lets H__: mq_equiv_post_to_impl Hkqe; eauto.
    specializes H__; eauto. 
    false.

    invstep_if1.
    invstep_if.
    {
      step_contra0.
      step_contra0.    
      apply11 asrt_and_ret asrt_and_ret aar_Oeq H1_ H2_.
      subst.
      assert (O1 = O1'). { join auto. }
      assert (O2 = O2'). { join auto. }
      subst.    
      split; auto.
      lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
      eapply H__; eauto. clear H__.
      apply11 asrt_and_ret asrt_and_ret aar_veq12 He1_ He2_.
      inverts He1_. inverts He2_. 
      eapply ceq_send_res; eauto. 
    }
    
    lets H__: mq_equiv_post_rdy_impl Hkqe; eauto.
    specializes H__; eauto. 
    false.

    step_contra0; tryfalse.
    apply nabt_abt_false in Hnabt2; false.
    invstep_if2.
    step_contra0; solve_endabt.
    invstep_if2.
    step_contra0; solve_endabt.
    step_contra0; solve_endabt.
  }
  
  { apply nabt_abt_false in Hnabt1; false. }
  invstep_seq. 
  {
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if2.
    step_contra0; solve_endabt.
    step_contra0; solve_endabt. 
  }
  { apply nabt_abt_false in Hnabt2; false. }
  invstep_if1.
  step_contra0; solve_endabt.
  invstep_if2.
  step_contra0; solve_endabt. 
  step_contra0; solve_endabt. 
  
  destruct k. 
  (* k=16 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
    (* symexe. (* 50 goals *)  *)
  simpl in Hhsat1. simpl in Hhsat2.
  lets Hpeqv: mq_equiv_qptr_veq Hkqe Hhsat1 Hhsat2.
  destruct Hpeqv as ((Hnulleq1 & Hnulleq2) & (Hptreq1 & Hptreq2)).
  inverts Hstep1;  
    inverts Hstep2; 
    try (apply nabt_abt_false in Hnabt2; false; fail);
    try (apply nabt_abt_false in Hnabt1; false; fail). 
  invstep_if2; 
  invstep_if.

  {
    step_contra0.
    step_contra0.
    apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
    inverts H1_. inverts H2_.
    apply11 asrt_and_ret asrt_and_ret aar_Oeq Ha_ Hb_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.    
    eapply ceq_send_res; eauto.
  }
  {
    specializes Hnulleq2; eauto.
    false. (* v4 <> Vnull and v4 = Vnull *)
  }

  invstep_if.
  {
    specializes Hnulleq1; eauto.
    false. (* v8 <> Vnull and v8 = Vnull *)
  }
  invstep_if.
  { 
    step_contra0.
    step_contra0.
    apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
    inverts H1_. inverts H2_.
    apply11 asrt_and_ret asrt_and_ret aar_Oeq Ha_ Hb_.
    subst.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst. 
    split; auto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.    
    eapply ceq_send_res; eauto.   
  }
  {
    specializes Hptreq2; eauto.
    simpljoin; eexists; eauto.
    destruct Hptreq2; subst.
    match goal with H: ~(exists _, _) |- _ => false; apply H end.
    simpljoin; eexists; split; eauto.
  }
  invstep_if1.
  {
    specializes Hnulleq1; eauto.
    false.
  }
  {
    invstep_if2.
    {
      specializes Hptreq1; eauto.
      simpljoin; eexists; eauto.
      destruct Hptreq1; subst.
      match goal with H: ~(exists _, _) |- _ => false; apply H end.
      simpljoin; eexists; split; eauto.
    }
    invstep_if1; 
      invstep_if.
    {
      step_contra0. step_contra0.
      {
        apply11 asrt_and_ret asrt_and_ret aar_Oeq Ha_ Hb_.
        subst.
        assert (O1 = O1'). { join auto. }
        assert (O2 = O2'). { join auto. }
        subst. 
        split; auto.
        apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
        inverts H1_. inverts H2_.    
        lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
        eapply H__; eauto. clear H__.    
        eapply ceq_send_res; eauto.
      }
    }
    {
      apply knl_mq_equiv_sym in Hkqe.
      lets H__: mq_equiv_noque_false Hhsat2 Hhsat1 Hkqe; eauto.
      false; eapply H__; eauto.
    }
    {
      invstep_if.
      {
        lets H__: mq_equiv_noque_false Hhsat1 Hhsat2 Hkqe; eauto.
        false; eapply H__; eauto.
      }
      invstep_if.
      step_contra0. step_contra0.
      {
        apply11 asrt_and_ret asrt_and_ret aar_Oeq Ha_ Hb_.
        subst.
        assert (O1 = O1'). { join auto. }
        assert (O2 = O2'). { join auto. }
        subst. 
        split; auto.
        apply11 asrt_and_ret asrt_and_ret aar_veq12 H1_ H2_.
        inverts H1_. inverts H2_.    
        lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
        eapply H__; eauto. clear H__.    
        eapply ceq_send_res; eauto.        
      }
      {
        apply knl_mq_equiv_sym in Hkqe.
        lets Hf: mq_equiv_qlen_impl v0 Hhsat2 Hhsat1 Hkqe; eauto.
        specializes Hf; eauto.
        false.
      }
    }
    invstep_if1.
    {
      lets H__: mq_equiv_noque_false Hhsat1 Hhsat2 Hkqe; eauto.
      false; eapply H__; eauto.      
    }
    invstep_if2.
    {
      lets Hf: mq_equiv_qlen_impl v0 Hhsat1 Hhsat2 Hkqe; eauto.
      specializes Hf; eauto.
      false.      
    }
    invstep_if2; invstep_if.
    {
      step_contra0.
      step_contra0.
      {
        split.
        -
          (* code_equiv *)
          lets Hpp1: qpost_nowt_succ_prio_preserved O1 O1' O0 O'0; eauto.
          specializes Hpp1; eauto.
          lets Hpp2: qpost_nowt_succ_prio_preserved O2 O2' O O'; eauto.
          specializes Hpp2; eauto.
          apply11 qpost_nowt_succ_body qpost_nowt_succ_body
            qpost_nowt_succ_cpid_same Hcpeq2 Hcpeq1.
          specializes Hcpeq1; eauto.
          specializes Hcpeq2; eauto. 

          eapply code_equiv_upd2_preserve_st'; eauto.
          {
            (* cmd_equiv *)
            match goal with
              H: context [qpost_nowt_succ_body] |- _ =>
                eapply qpost_nowt_succ_ret in H; eauto
            end.
            match goal with
              H: context [qpost_nowt_succ_body] |- _ =>
                eapply qpost_nowt_succ_ret in H; eauto
            end.
            eapply ceq_send_res; eauto.
            congruence.
          }
          eapply cont_equiv_qref_preserve; eauto. 
          eapply qpost_nowt_succ_mqref_preserve; eauto.
          eapply qpost_nowt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
          eapply qpost_nowt_succ_qprt_preserve; eauto.
          eapply qpost_nowt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.
          eapply eqdom_frm_domimpl; eauto.
          eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

          lets H__: code_equiv_hsat_neq_st'; eauto.
          eapply H__; eauto.
          eapply qpost_nowt_succ_mqref_preserve; eauto.
          eapply qpost_nowt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
          eapply qpost_nowt_succ_qprt_preserve; eauto.
          eapply qpost_nowt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.              
          eapply eqdom_frm_domimpl; eauto.
          eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
          
        -
          (* data_equiv *)
          eapply qpost_nowt_succ_body_dteq_preserve2; eauto.        
      }
    }
    {
      lets H__: mq_equiv_qlen_lt_impl Hhsat1 Hhsat2 Hkqe; eauto.
      specializes H__; eauto.
      false.
    }
    {
      invstep_if.
      {
        apply knl_mq_equiv_sym in Hkqe.
        lets H__: mq_equiv_qlen_lt_impl Hhsat2 Hhsat1 Hkqe; eauto.
        specializes H__; eauto.
        false.        
      }
      invstep_if.
      {
        invstep_seq. 
      }
      {
        lets H__: mq_equiv_wls_impl Hhsat1 Hhsat2 Hkqe; eauto.
        specializes H__; eauto.
        false. 
      }
    }
    step_contra0. false.
  }
  {
    invstep_if.
    step_contra0; solve_endabt. 
    invstep_if1.
    {
      specializes Hnulleq1; eauto.
      false. 
    }
    invstep_if1.
    step_contra0; solve_endabt. 
    invstep_if1.
    {
      specializes Hptreq1; eauto.
      simpljoin; eexists; eauto.
      destruct Hptreq1; subst.
      match goal with H: ~(exists _, _) |- _ => false; apply H end.
      simpljoin; eexists; split; eauto.      
    }
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.
    {
      lets H__: mq_equiv_noque_false Hhsat1 Hhsat2 Hkqe; eauto.
      specializes H__; eauto.
      false. 
    }
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.
    {
      lets H__: mq_equiv_qlen_impl Hhsat1 Hhsat2 Hkqe; eauto.
      specializes H__; eauto.
      false. 
    }
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.
    {
      lets H__: mq_equiv_qlen_lt_impl Hhsat1 Hhsat2 Hkqe; eauto.
      specializes H__; eauto.
      false.      
    }
    invstep_if2.
    {
      step_contra0.
    }
    {
      step_contra0. false. 
    }
  }
  {
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.
    {
      specializes Hnulleq2; eauto.
      false. 
    }
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.
    {
      specializes Hptreq2; eauto.
      simpljoin; eexists; eauto.
      destruct Hptreq2; subst.
      match goal with H: ~(exists _, _) |- _ => false; apply H end.
      simpljoin; eexists; split; eauto.
    }
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.    
    {
      apply knl_mq_equiv_sym in Hkqe.
      lets H__: mq_equiv_noque_false Hhsat2 Hhsat1 Hkqe; eauto.
      specializes H__; eauto.
      false.       
    }
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.
    {
      apply knl_mq_equiv_sym in Hkqe.
      lets H__: mq_equiv_qlen_impl Hhsat2 Hhsat1 Hkqe; eauto.
      specializes H__; eauto.
      false.       
    }
    invstep_if1.
    step_contra0; solve_endabt.
    invstep_if1.
    {
      apply knl_mq_equiv_sym in Hkqe.
      lets H__: mq_equiv_qlen_lt_impl Hhsat2 Hhsat1 Hkqe; eauto.
      specializes H__; eauto.
      false.            
    }
    invstep_if2.
    {
      step_contra0.
    }
    {
      step_contra0.
      false.
    }
  }
  {
    invstep_if1.
    {
      step_contra0; solve_endabt. 
    }
    invstep_if1.
    {
      step_contra0; solve_endabt. 
    }
    invstep_if1. 
    {
      step_contra0; solve_endabt. 
    }
    invstep_if1.
    {
      step_contra0; solve_endabt. 
    }
    invstep_if1.
    {
      step_contra0; solve_endabt.
    }
    invstep_if1.
    {
      step_contra0; solve_endabt.      
    }
    invstep_if1.
    {
      step_contra0; solve_endabt.
    }
    invstep_if1.
    {
      step_contra0; solve_endabt.
    }
    invstep_if1.
    {
      step_contra0; solve_endabt.
    }
    invstep_if1.
    {
      step_contra0; solve_endabt.
    }
    invstep_if1.
    {
      invstep_if.
      {
        step_contra0; try solve_endabt.  
        step_contra0; try solve_endabt. 
        step_contra0; try solve_endabt.
        step_contra0; try solve_endabt. 
        {
          split.
          - (* code_equiv  *)
            lets Hpp1: qpost_exwt_succ_prio_preserved O1 O1' O0 O'0; eauto.
            specializes Hpp1; eauto.
            lets Hpp2: qpost_exwt_succ_prio_preserved O2 O2' O O'; eauto.
            specializes Hpp2; eauto. 
            apply11 qpost_exwt_succ_body qpost_exwt_succ_body
              qpost_exwt_succ_cpid_same Hcpeq2 Hcpeq1.
            specializes Hcpeq1; eauto.
            specializes Hcpeq2; eauto. 

            eapply code_equiv_upd2_preserve_st'; eauto.
            {
              (* cmd_equiv *)
              unfolds.
              right.
              do 2 eexists.
              split; eauto. split; eauto.
              split. simpl; auto. split. simpl; auto.
              split.
              eapply vl_equiv_nil; eauto.
              unfolds.
              right.
              split. introv Hf. simpljoin. tryfalse.
              left.
              solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 17%nat. 
            }
            eapply cont_equiv_qref_preserve; eauto. 
            eapply qpost_exwt_succ_mqref_preserve; eauto.
            eapply qpost_exwt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
            eapply qpost_exwt_succ_qprt_preserve; eauto.
            eapply qpost_exwt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.      
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.    

            lets H__: code_equiv_hsat_neq_st'; eauto.
            eapply H__; eauto.
            eapply qpost_exwt_succ_mqref_preserve; eauto.
            eapply qpost_exwt_succ_mqref_preserve with (O0:=O) (O0':=O'); eauto.
            eapply qpost_exwt_succ_qprt_preserve; eauto.
            eapply qpost_exwt_succ_qprt_preserve with (O0:=O) (O0':=O'); eauto.                    
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
            
          - (* data_equiv *)           
            eapply qpost_exwt_succ_dteq_preserve2; eauto.          
        }
        step_contra0; try solve_endabt.
        step_contra0; try solve_endabt. 
      }
      { step_contra0. false. }
    }
    { step_contra0. false. }
  }

  destruct k. 
  (* k=17 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.   
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
  eapply H__; eauto. clear H__.
  unfolds. 
  right.
  do 2 eexists.
  split; eauto.
  split; eauto.
  split. simpl; auto.
  split. simpl; auto.
  split.
  eapply vl_equiv_nil; simpl; auto. 
  unfolds.
  right.
  split. introv Hf. simpljoin; tryfalse.
  left.
  solve_qsend_eq Hlenvl Hlenvl1 Hlenvl2 18%nat.    

  destruct k. 
  (* k=18 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  symexe.   
  apply11 asrt_and_ret asrt_and_ret aar_Oeq H1_ H2_.
  subst.
  assert (O1 = O1'). { join auto. }
  assert (O2 = O2'). { join auto. }
  subst.    
  split; auto.
  lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
  eapply H__; eauto. clear H__.
  apply11 asrt_and_ret asrt_and_ret aar_veq12 He1_ He2_.
  inverts He1_. inverts He2_. 
  eapply ceq_send_res; eauto. 

  destruct k. 
  (* k=19 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.
  lets Hveq: vlequiv_veq Hvleq.
  specializes Hveq.
  simpl. eauto. simpl. eauto.
  subst. 
  symexe.
  {
    apply11 ret_val ret_val rv_veq Hrv1 Hrv2.
    apply11 ret_val ret_val rv_Oeq HO1 HO2.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto.    
  }
  {
    apply11 ret_val ret_val rv_veq Hrv1 Hrv2.
    apply11 ret_val ret_val rv_Oeq HO1 HO2.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto.
  }
  {
    apply11 ret_val ret_val rv_veq Hrv1 Hrv2.
    apply11 ret_val ret_val rv_Oeq HO1 HO2.
    assert (O1 = O1'). { join auto. }
    assert (O2 = O2'). { join auto. }
    subst.
    split; eauto.
    lets H__: code_equiv_upd2_preserve' Hce HC1 HC2 Htpi1 Htpi2. 
    eapply H__; eauto. clear H__.
    eapply cmd_equiv_end; eauto.
  }

  destruct k. 
  (* k=20 *)
  simpl in Hnth1; inverts Hnth1.
  simpl in Hnth2; inverts Hnth2.

  Unshelve.
  trivial.
  trivial. 
  trivial.
  trivial. 
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  trivial. 
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.

Qed.   

