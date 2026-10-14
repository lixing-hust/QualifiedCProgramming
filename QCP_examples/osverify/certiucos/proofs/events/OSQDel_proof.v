Require Import  ucos_include.
Require Import Lia.
Require Import abs_op.
Require Import ifun_spec.
Require Import evt_spec_defs.
Require Import OSQPostPure.
Require Import OSQDelPure.
Require Import tcblist_setnode_lemmas.
Require Import protect.
Require Import symbolic_lemmas.
Require Import OSTimeTickPure. 
Require Import sem_lab.
Require Import sem_common.
Require Import sem_corecommu.

Require Import seplog_trm_tacs.
Require Import OSQPendPure_ext.
Require Import OSQPostPure_ext.
Require Import OSQDelPure_ext.
Require Import gjb_common.
Require Import gjb_q_common.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import evtinv_lemmas.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.


Open Scope code_scope.
Open Scope list_scope.
Open Scope int_scope.

Lemma absinfer_qdel_null_err_return :
  forall P sch s0, 
    can_change_aop P ->
    absinfer sch
             (<|| spec_code_cons (qdel (Vnull :: nil)) s0 ||> ** P)
             ( <|| s0 ||> ** P).
Proof.
  introv Hcop.
  simpl spec_code_cons.  
  infer_solver 0%nat.
Qed.

Lemma absinfer_qdel_succ_ex_wait :
  forall P sch tls tls' tls'' els els' qid pwls wls x y ct ptrmp ptrmp' s0,  
    can_change_aop P ->
    get els qid = Some (absmsgq x y pwls, wls) -> 
    wls <> nil \/ pwls <> nil -> 
    join els' (sig qid (absmsgq x y pwls, wls)) els ->
    tls' = set_tls_rdy wls tls ->
    tls'' = set_tls_rdy0 pwls tls' ->
    ptrmp' = set ptrmp ct (Vnull, Vnull, Vnull) ->  
    absinfer sch
             (<|| spec_code_cons (qdel (Vptr qid :: nil)) s0 ||> ** HECBList els ** HTCBList tls ** HCurTCB ct ** HEvPtr ptrmp ** P)
             ( <|| isched;; qdel_ret (|nil|);; s0 ||> ** HECBList els' ** HTCBList tls'' ** HCurTCB ct ** HEvPtr ptrmp' ** P).  
Proof.
  introv Hcop Hmq Hnnil Hjo Hset' Hset'' Hptrmp'.
  simpl spec_code_cons.
  simpljoin.
  infer_solver 2%nat.
  {
    unfolds.
    unfolds.
    intros.
    split; intros. 
    apply set_tls0_rdy_indom_impl1.
    apply set_tls_rdy_indom_impl1; auto. 
    apply set_tls_rdy0_indom_impl2 in H0.
    apply set_tls_rdy_indom_impl2 in H0; auto.
  }
  unfolds.
  do 3 (rewrite set_a_get_a'; eauto). 
Qed.   

Lemma absinfer_qdel_succ_nex_wait :
  forall P sch els els' qid x y ptrmp ptrmp' ct s0,  
    can_change_aop P ->
    get els qid = Some (absmsgq x y nil, nil) -> 
    join els' (sig qid (absmsgq x y nil, nil)) els ->
    ptrmp' = set ptrmp ct (Vnull, Vnull, Vnull) -> 
    absinfer sch
             (<|| spec_code_cons (qdel (Vptr qid :: nil)) s0 ||> ** HECBList els ** HCurTCB ct ** HEvPtr ptrmp ** P)
             ( <|| qdel_ret (|nil|);; s0 ||> ** HECBList els' ** HCurTCB ct ** HEvPtr ptrmp' ** P).  
Proof.
  introv Hcop Hmq Hjo.
  simpl spec_code_cons.
  infer_solver 3%nat. 
Qed. 

Lemma absinfer_qdel_ret :
  forall P sch s0, 
    can_change_aop P ->
    absinfer sch (<|| qdel_ret (|nil|);; s0 ||> ** P) ( <|| s0 ||> ** P).
Proof.
  introv Hcop.
  infer_solver 0%nat.
Qed.

Lemma OSQDelProof: 
  forall vl p r logicl ct, 
    Some p = BuildPreI os_internal OSQDel vl logicl OSQDelPre ct ->  
    Some r = BuildRetI os_internal OSQDel vl logicl OSQDelPost ct ->  
    exists t d1 d2 s,
      os_internal OSQDel = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv,  I, r, Afalse|}|-ct {{p}}s {{Afalse}}. 
Proof.
  init_spec.
  rename v'6 into er.
  simpl in H0. inverts H0.
  rename H2 into Hnotcore.
  subst logicl.

  (* ENTER_CRITICAL *) 
  hoare forward prim.

  (* If (pevent ′ ==ₑ NULL) ... *)
  hoare forward; pure_auto. 
  hoare unfold pre.
  assert (v'5 = Vnull) by pure_auto.
  subst.

  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_qdel_null_err_return; eauto. 
  go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *) 
  hoare forward prim.
  sep cancel EvtInv.
  sep cancel Aier.
  sep cancel tcbdllflag.
  sep cancel p_local.
  eauto.
  auto.
  go. 
  (* return pevent (NULL) *) 
  hoare forward.

  (******* pevent != NULL *******)
  apply hoare_disj_afalseP_l_pre.
  hoare normal pre.
  hoare_split_pure_all.
  destruct H2 as [Hinjzero | Hinjnull].
  2: {
    simpl in Hinjnull.
    false.
    lets H00: isptr_val_inj_false Hinjnull; eauto. 
  }
  destruct H1.
  subst.
  simpl in Hinjzero.
  inverts Hinjzero.
  simpljoin1. subst.
  (* value of pevent is now "Vptr x" *)
  clear Hinjzero.

  unfold EvtInv.
  hoare unfold.
  hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList, p_local).
  eapply backward_rule1.
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto. 
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  rename v'42 into locmp.
  rename v'43 into ptrmp.
  rename v'37 into semeibs.
  rename v'38 into muxeibs.
  rename v'39 into mqeibs. 
  rename v'14 into els.
  assert (Hevptr: get ptrmp ct = Some (Vnull, Vnull, Vptr x)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hloc: get locmp ct = Some (V$ __EvLoc_ecbdel)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Htle: tsk_loc_ev locmp ptrmp ct __EvLoc_ecbdel x). 
  {
    unfold tsk_loc_ev. splits; auto.
    do 3 eexists. splits; eauto. 
  }
  lets H00: ecb_del H3 H4 H5 Htle.
  destruct H00 as (Hque & Hncre & Hnref).

  assert (Hndel: ~exists t', t' <> ct /\ tsk_loc_ev locmp ptrmp t' __EvLoc_ecbdel x).
  {
    eapply evdel_nodup_del_nodel; eauto. 
  }

  lets Hexecb: Hque.
  destruct Hexecb as (msgs & maxlen & pwl & wl & Hecb).

  unfold AECBList.
  hoare unfold.
  match goal with
    H: ECBList_P _ Vnull _ _ els _ |- _ => rename H into H_elp
  end. 
  lets Hctr: ECBList_P_get_ectr_some Hecb H_elp.
  destruct Hctr as (evl & etbl & petbl & Hgetectr).

  (* assert (H_elp' := H_elp). *)

  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.

  inverts H21.

  hoare_assert_pure (length v'37 = length v'39).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat evsllseg.
    eapply evsllseg_aux in Hsat.
    destruct Hsat.
    eauto.
  }
  eapply pure_split_rule'; introv Heqlen.
  lets H00: ecblist_p_decompose H_elp; eauto.
  destruct H00 as (els1 & els2 & x' & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).
  hoare_assert_pure (x' = Vptr (v'54, Int.zero)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst.

  assert (Hecbl' := Hecbl2).
  do 2 (rewrite ele_lst_cons in Hecbl'). 
  unfold ECBList_P in Hecbl'. 
  fold ECBList_P in Hecbl'.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hecbpetbl & Hex).
  inverts Hqid. 
  destruct Hex as (absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.

  assert (Hgetmq: get els (v'54, Int.zero) = Some absmq).
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    apply get_a_sig_a.
  }
  assert (Hmqeq: absmq = (absmsgq msgs maxlen pwl, wl)).
  {
    unfold get, EcbMap in Hgetmq.
    unfold get, EcbMap in Hecb.
    rewrite Hgetmq in Hecb.
    inverts Hecb; auto. 
  }
  subst absmq. 

  destruct (Int.eq i1 ($ OS_EVENT_TYPE_Q)) eqn: Etp.
  2: {
    (* pevent->OSEventType != OS_EVENT_TYPE_Q *)
    eapply backward_rule1.
    introv Hsat.
    sep_lifts_trms_in Hsat AEventData.
    lets H00: eventtype_neq_q_gen Hsat Hrlh.
    unfold V_OSEventType at 1 in H00.
    unfold nth_val at 1 in H00.
    specialize (H00 (eq_refl _) Etp).
    eauto.
    hoare_split_pure_all.
    false.
    apply H2. repeat eexists; eauto. 
  }

  hoare_assert_pure(array_type_vallist_match char_t petbl).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat AOSPostEventTbl.
    unfold AOSPostEventTbl in Hsat.
    sep split in Hsat. auto. 
  }
  apply pure_split_rule'.
  introv Hmtpetbl.

  hoare_assert_pure(length petbl = ∘ OS_EVENT_TBL_SIZE). 
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat AOSPostEventTbl.
    unfold AOSPostEventTbl in Hsat.
    sep split in Hsat. 
    apply Aarray_vl_len_eq in Hsat.
    auto. 
  }
  apply pure_split_rule'.
  introv Hlenpetbl.

  (* pevent->OSEventType == OS_EVENT_TYPE_Q *)
  (* If (pevent ′ → OSEventType !=ₑ ′ OS_EVENT_TYPE_Q) *)
  lzh_hoare_if.
  pure_auto.
  pure_auto.
  
  (* impossible case: into the body of "If" *)
  rewrite LHift_true in Etp.
  inverts Etp.

  eapply seq_rule.
  (* IF (pevent ′ → OSEventGrp !=ₑ ′ 0){tasks_waiting ′ =ₑ ′ 1}
     ELSE {tasks_waiting ′ =ₑ ′ 0};ₛ *) 
  eapply lzh_if_else_rule.
  introv Hsat.
  sep get rv.
  go.
  pure_auto. 
  pure_auto.
  (* branch with tasks_waiting ′ =ₑ ′ 1 *)
  hoare forward.
  (* branch with tasks_waiting ′ =ₑ ′ 0 *)
  hoare forward.

  eapply backward_rule1.
  introv Hsat.
  destruct Hsat as [Hs1 | Hs2].
  apply sep_pure_split in Hs1; destruct Hs1 as (Hinjs & Hs1). 
  sep_lifts_trms_in Hs1 Apure.
  apply sep_pure_split in Hs1; destruct Hs1 as (Hinjs' & Hs1).   
  match type of Hs1 with
    _ |= <|| ?ss ||> ** LV tasks_waiting @ char_t |-> _ ** ?P =>
    instantiate
      (1:=EX v', [| Int.eq i0 Int.zero = false /\ v' = Vint32 (Int.repr 1)
                    \/ Int.eq i0 Int.zero = true /\ v' = Vint32 Int.zero |]
                   ** <|| ss ||> ** LV tasks_waiting @ char_t |-> v' ** P)
  end.
  destruct Hinjs as (Hinj1 & _ & _).
  destruct (Int.eq i0 ($ 0)) eqn: Ei.
  simpl in Hinj1. 
  change (Int.notbool Int.one) with Int.zero in Hinj1.
  false.
  exists (Vint32 (Int.repr 1)). 
  sep pauto. 
  apply sep_pure_split in Hs2; destruct Hs2 as (Hinjs & Hs2). 
  sep_lifts_trms_in Hs2 Apure.
  apply sep_pure_split in Hs2; destruct Hs2 as (Hinjs' & Hs2).   
  destruct Hinjs as [Hinj1 | Hinj2].
  destruct (Int.eq i0 ($ 0)) eqn: Ei; 
    simpl in Hinj1.
  exists (Vint32 Int.zero).
  sep pauto.
  change (Int.notbool Int.zero) with Int.one in Hinj1.
  inverts Hinj1. 
  clear -Hinj2. false. 
  destruct (Int.eq i0 ($ 0)); simpl in Hinj2.
  change (Int.notbool Int.one) with Int.zero in Hinj2; inverts Hinj2.
  change (Int.notbool Int.zero) with Int.one in Hinj2; inverts Hinj2.

  (* end of if statement on "pevent ′ → OSEventGrp !=ₑ ′ 0" *)  

  hoare_split_pure_all.
  rename H2 into Hcond1.

  eapply seq_rule.
  (* IF (pevent ′ → OSPostEventGrp !=ₑ ′ 0){tasks_post_waiting ′ =ₑ ′ 1}
     ELSE {tasks_post_waiting ′ =ₑ ′ 0};ₛ *) 
  eapply lzh_if_else_rule.
  introv Hsat.
  sep get rv.
  go.
  pure_auto. 
  pure_auto.
  (* branch with tasks_waiting ′ =ₑ ′ 1 *)
  hoare forward. 
  (* branch with tasks_waiting ′ =ₑ ′ 0 *)
  hoare forward.

  eapply backward_rule1.
  introv Hsat.
  destruct Hsat as [Hs1 | Hs2].
  apply sep_pure_split in Hs1; destruct Hs1 as (Hinjs & Hs1). 
  sep_lifts_trms_in Hs1 Apure.
  apply sep_pure_split in Hs1; destruct Hs1 as (Hinjs' & Hs1).   
  match type of Hs1 with
    _ |= <|| ?ss ||> ** LV tasks_post_waiting @ char_t |-> _ ** ?P =>
    instantiate
      (1:=EX v', [| Int.eq i Int.zero = false /\ v' = Vint32 (Int.repr 1)
                    \/ Int.eq i Int.zero = true /\ v' = Vint32 Int.zero |]
                   ** <|| ss ||> ** LV tasks_post_waiting @ char_t |-> v' ** P)
  end.
  destruct Hinjs as (Hinj1 & _ & _).
  destruct (Int.eq i ($ 0)) eqn: Ei.
  simpl in Hinj1. 
  change (Int.notbool Int.one) with Int.zero in Hinj1.
  false.
  exists (Vint32 (Int.repr 1)). 
  sep pauto. 
  apply sep_pure_split in Hs2; destruct Hs2 as (Hinjs & Hs2). 
  sep_lifts_trms_in Hs2 Apure.
  apply sep_pure_split in Hs2; destruct Hs2 as (Hinjs' & Hs2).   
  destruct Hinjs as [Hinj1 | Hinj2].
  destruct (Int.eq i ($ 0)) eqn: Ei; 
    simpl in Hinj1.
  exists (Vint32 Int.zero).
  sep pauto.
  change (Int.notbool Int.zero) with Int.one in Hinj1.
  inverts Hinj1. 
  clear -Hinj2. false. 
  destruct (Int.eq i ($ 0)); simpl in Hinj2.
  change (Int.notbool Int.one) with Int.zero in Hinj2; inverts Hinj2.
  change (Int.notbool Int.zero) with Int.one in Hinj2; inverts Hinj2.

  (* end of if statement on "pevent ′ → OSPostEventGrp !=ₑ ′ 0" *)  

  hoare_split_pure_all.
  rename H2 into Hcond2.

  (* merge evaux_node with second llsegevaux *)
  fold_evaux.
  (* folding of llsegevaux completed *)
  hoare_lifts_trms_pre (Aisr, Ais, aemp_isr_is).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).

  hoare_lifts_trms_pre (
      Aop, Aier, Astruct (v'54, Int.zero), Aarray v'50, AEventData, AOSMapTbl, AOSUnMapTbl, AOSTCBPrioTbl,
      AOSTCBList, AOSRdyTblGrp, tcbdllflag, x, pevent, llsegevaux
    ).
  hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::nil)%nat pre. 
  protect HeqH2.
  unfold AOSTCBList.
  hoare unfold.
  rename v'15 into tcbls.
  rename v'7 into tcb_head.
  rename v'51 into tcb_tail. 
  rename v'9 into tcbvl_l. 
  rename v'10 into tcbvl_ct.
  rename v'11 into tcbvl_r.
  rename v'12 into rtbl.
  rename v'13 into rgrp.
  rename v'54 into eid_b.

  assert (Htp: i1 = ($ OS_EVENT_TYPE_Q)).
  {
    clear -Etp. apply semacc_int_eq_true in Etp. auto. 
  }
  subst i1.
  hoare_assert_pure (exists osq osqblk msgtbl, v'43 = DMsgQ x1 osq osqblk msgtbl).
  {
    get_hsat Hsat. 
    unfold AEventData in Hsat.
    destruct v'43; sep split in Hsat.
    match goal with H: V_OSEventPtr _ = _ |- _ => unfold V_OSEventPtr in H; simpl in H; inverts H end. 
    do 3 eexists; eauto.
    inverts H36. inverts H36. inverts H36. inverts H36.
  }
  hoare_split_pure_all.
  rename x1 into qcb_ptr. 
  rename v'7 into osq.
  rename v'9 into osqblk.
  rename v'10 into msgtbl.
  subst.

  unfolds in Hrlh.
  destruct Hrlh as (Hmt_list & Hmt_len & Hmt_sz & Hrh_ecb).
  simpl in Hrh_ecb.
  destruct Hrh_ecb as (Hwlnil & Hmsgsnil & Hpwlnil & Hmsgsfull).

   eapply backward_rule1 with (
       p := (*below is the loop inv*)
         (EX er etbl' tcbvl_ct' rtbl' rgrp' egrp subwl vx (tcbls_l' tcbls_r': TcbMod.map) tcbvl_l' tcbvl_r' tail1, 
     <|| spec_code_cons (qdel (Vptr (eid_b, Int.zero) :: nil)) v'4 ||>  **
         Aier er ** (* new add *)
         LV x @ Int16u |-> vx **
         AOSMapTbl **
         AOSUnMapTbl ** 
         AOSTCBPrioTbl v'6 rtbl' (set_tls_rdy subwl tcbls) v'20 vhold_addr **
         GV OSTCBList @ OS_TCB ∗ |-> tcb_head **
         tcbdllseg tcb_head Vnull tail1 (Vptr ct) tcbvl_l' **
         GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
         tcbdllseg (Vptr ct) tail1 tcb_tail Vnull (tcbvl_ct' :: tcbvl_r') ** 
         [| TcbMod.join tcbls_l' tcbls_r' (set_tls_rdy subwl tcbls) |] **
         [| TCBList_P tcb_head tcbvl_l' rtbl' tcbls_l' |] **
         [| TCBList_P (Vptr ct) (tcbvl_ct' :: tcbvl_r') rtbl' tcbls_r' |] **
(*          [| is_subl subwl wl |] ** *)
         [| RH_TCBList_ECBList_P (set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, (remove_wls subwl wl)))
                                                         (set_tls_rdy subwl tcbls) ct |] **
         tcbdllflag tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') **  
         AOSRdyTblGrp rtbl' rgrp' ** 
         Astruct (eid_b, Int.zero) OS_EVENT
           (V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i2 :: qcb_ptr :: x2 :: v'' :: Vint32 i :: x5 :: nil) **
         Aarray v'50 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl' **
         AEventData
           (V$ OS_EVENT_TYPE_Q :: Vint32 egrp :: Vint32 i2 :: qcb_ptr :: x2 :: v'' :: Vint32 i :: x5 :: nil) 
           (DMsgQ qcb_ptr osq osqblk msgtbl) ** 
         llsegevaux tcb_head Vnull (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') locmp ptrmp V_OSTCBNext **
         LV pevent @ OS_EVENT ∗ |-> Vptr (eid_b, Int.zero) ** 
         H2 ** 
         [| (RL_Tbl_Grp_P etbl' (Vint32 Int.zero)  /\ array_type_vallist_match Tint8 etbl' /\
              egrp = Int.zero /\
             (( subwl = nil \/ (forall t : Modules.tid, In t subwl -> In t wl)) /\ remove_wls subwl wl = nil) /\
             length etbl' = ∘ OS_EVENT_TBL_SIZE  /\(* egrp = 0, get out of the loop *)
             ECBList_P v'8 Vnull
                           (v'37 ++
                                 ((V$ OS_EVENT_TYPE_Q
                                    :: Vint32 Int.zero :: Vint32 i2 :: qcb_ptr :: x2 :: v'' :: Vint32 i :: x5 :: nil, etbl', petbl) :: nil) ++
                                 v'38) (v'39 ++ (DMsgQ qcb_ptr osq osqblk msgtbl :: nil) ++ v'42) 
                           (set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, nil)) (set_tls_rdy wl tcbls)) \/
        (is_subl subwl wl /\
         RL_Tbl_Grp_P etbl' (Vint32 egrp)  /\ array_type_vallist_match Tint8 etbl' /\
         egrp <> Int.zero /\ Int.unsigned egrp <= 255 /\  length etbl' = ∘ OS_EVENT_TBL_SIZE  /\(* egrp <> 0, still in the loop *)
         ECBList_P v'8 Vnull
                      (v'37 ++
                            ((V$ OS_EVENT_TYPE_Q
                               :: Vint32 egrp :: Vint32 i2 :: qcb_ptr :: x2 :: v'' :: Vint32 i :: x5 :: nil, etbl', petbl) :: nil) ++ 
                            v'38) (v'39 ++ (DMsgQ qcb_ptr osq osqblk msgtbl :: nil) ++ v'42)
                      (set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, (remove_wls subwl wl))) 
                      (set_tls_rdy subwl tcbls)) |])).

  introv Hsat.
  casetac i0 Int.zero Hegrp_zero Hegrp_nzero.
  subst.
  assert (Hwls: wl = nil).
  { clear Hmtpetbl Hlenpetbl. eapply Grp_eq_zero_imp_wl_nil; eauto. }
  subst.
  assert(Hels: set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, nil) = els).
  { eapply EcbMod.get_set_same; eauto. }
  rewrite Hels.
  rewrite set_tls_rdy_nil.
  do 6 eexists. 
  exists (nil: list Modules.tid).
  do 6 eexists.
  rewrite remove_wls_nil.
  rewrite Hels.
  rewrite set_tls_rdy_nil.
  sep pauto; eauto.
  sep cancel AOSTCBPrioTbl.
  sep cancel Aop.
  sep cancel Aier.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg. 
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  unfold V_OSTCBNext; auto.
  left.
  splits; eauto.

  assert (Hwls: wl <> nil).
  { clear Hmtpetbl Hlenpetbl. eapply Grp_eq_nz_imp_wl_not_nil; eauto. } 
  assert(Hels: set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, (remove_wls nil wl)) = els). 
  { apply EcbMod.get_set_same; eauto. }
  do 6 eexists. 
  exists (nil: list Modules.tid).  
  do 6 eexists.
  rewrite Hels.
  rewrite set_tls_rdy_nil. 
  assert (His_subl_nil: is_subl nil wl).
  { eapply nil_is_subl; eauto. }
  sep pauto; eauto. 
  sep cancel AOSTCBPrioTbl. 
  sep cancel Aop.
  sep cancel Aier.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  auto.
  right.
  splits; eauto.

  eapply seq_rule.
  eapply while_rule with (tp := Int32u).
  {
    introv Hsat.
     clear HeqH2.
     sep destruct Hsat.
     eexists.
     sep get rv.
     sep split in Hsat.
     destruct H41; simpljoin.
     go.
     go.
     pure_auto.
     pure_auto.
  }

  (*show "inv /\ cond -> 2nd disjunct of inv" *)
  hoare normal pre.
  apply ex_intro_rule; intro ier. (* new add *)
  repeat (apply ex_intro_rule; intro).
  eapply backward_rule1.
  introv Hsat.
  destruct Hsat as (Hsat & Histrue).
  lets Hcp: aconj_intro Hsat Histrue.
  eapply sep_aconj_r_aistrue_to_astar in Hcp; eauto.
   {
    introv Hsat'.
    clear HeqH2.
    sep get rv.
    sep split in Hsat'.
     destruct H41; simpljoin.
     go.
     go.
     pure_auto.
     pure_auto.
  }
  hoare_split_pure_all.
  destruct (Int.eq v'12 ($ 0)) eqn: if_eq1;
  simpl in H41; destruct H41; try change (Int.notbool Int.one) with Int.zero in H41; tryfalse.
  match goal with
    H: RL_Tbl_Grp_P _ (Vint32 Int.zero) /\ _ \/ _  |- _ =>
    destruct H as [Hcase_z | Hcase_nz];
    [ simpljoin; substs;
      change ($ 0) with Int.zero in *;
       rewrite Int.eq_true in if_eq1; tryfalse  |
     idtac ]
  end.
  clear H41 H42.
  (*
    x ′ =ₑ ′ OS_STAT_Q;ₛ
    OS_EventTaskRdy (­pevent ′, 〈 (Void) ∗ 〉 NULL, x ′­)
   *)
(*   hoare_split_pure_all. *)
  unprotect HeqH2.
  hoare forward.

  unfold AOSTCBPrioTbl.
  hoare unfold.
  fold_AEventNode_r.
  eapply conseq_rule; [eauto | idtac | idtac].
  Focus 2.
  hoare_call.
(*   hoare forward. *)

  get_hsat Hsat.
  sep cancel AOSRdyTblGrp.
  sep cancel AEventNode.
  
  sep_lifts_trms_in Hsat (tcbdllseg tcb_head, tcbdllseg (Vptr ct)).
  eapply tcbdllseg_compose in Hsat; eauto.
  sep cancel tcbdllseg.
  sep cancel p_local.
  eauto.

  splits; eauto.
  go. go. go. go. 
  {
    eapply TCBList_P_Combine. 
    eapply tcbdllseg_get_last_tcb_ptr with (s:=s).
    sep cancel tcbdllseg.
    eauto.
    join auto.
    auto. auto. 
  }

  {  (* R_ECB_ETbl_P *) 
    lets H_elp': H52.
    eapply ecblist_p_decompose in H_elp'; eauto.
    destruct H_elp' as (els1' & els2' & x' & H''). 
    destruct H'' as (Hecbl1'' & Hecbl2'' & Hjo''). 
    assert (Hx_eq: x' = Vptr (eid_b, Int.zero)).
    {
      get_hsat Hsat.
      sep_lifts_trms_in Hsat evsllseg.
      eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
    }
    subst x'. 
    simpl in Hecbl2''.
    mytac.
    inverts H54; auto. 
  }

  eauto. 
  eauto.
  { (* ptr_in_tcblist ... *)
    eapply tcbdllseg_combine_ptr_in_tcblist with (s:=s). 
    sep cancel tcbdllseg.
    sep cancel tcbdllseg.
    eauto.
    auto.
  }

  go. (* GoodFrm *) 

  introv Hsat. sep auto.
  introv Hsat. sep auto.

  introv Hsat.
(*   get_hsat Hsat.  *)
  unfold OS_EventTaskRdyPost in Hsat.
  unfold OS_EventTaskRdyPost' in Hsat.
  unfold getasrt in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep_lifts_trms_in Hsat (Aop, A_dom_lenv, A_isr_is_prop).
  unfold AEventNode in Hsat. 
  unfold AOSEvent in Hsat. 
  unfold node in Hsat. 
  unfold AOSEventTbl in Hsat. 
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  inverts H90. (* logic_val ... = ... *) 
  simpl nth_val in *.
  inverts H81; inverts H82; inverts H83.
  substs.
  rename x11 into egrp.
  rename x12 into egrp'. 
  simpl update_nth_val in *.
  mytac.
  inverts H2. (* Vptr (eid_b, ...) = Vptr (..., ...) *) 
  rename x56 into eid_b.
  inverts H55. (* V_OSEventGrp*)
  rewrite H17 in H54; inverts H54. (* os_inv.id_addrval' OSEventTbl *)
  rewrite H20 in H57; inverts H57. (* os_inv.id_addrval' OSPostEventTbl *)

  rename ct into ctcb.
  rename x50 into htcb_addr.
  rename H63 into Hhtcb.
  rename H84 into Hctcb_in_tcblist.
  rename x21 into tcblist_head.
  (* rename v'7 into tcblist_seg1. (still tcbvl_l) *)
  rename v'9 into ctcb_node. 
  (* rename v'8 into tcblist_seg2. (still tcbvl_r) *) 
  rename H67 into Hrel_et.

  rename x6 into ptbl'.
  rename x7 into rtbl'.
  rename v'13 into subwl.
  rename x13 into etbl'.

  (* remember (tcbvl_l ++ ctcb_node :: tcbvl_r) as tcblist. *)
  rename x45 into hprio.
  assert (Hex: exists hprio', hprio = Vint32 hprio').
  {
    clear - H75. (* struct_type_vallist_match OS_TCB_flag *) 
    rename H75 into H.
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }
  destruct Hex as (hp & H__).
  subst hprio.
  rename hp into hprio.

  rename x39 into hnext.
  rename x46 into htcbx. 
  rename x47 into htcby. 
  rename x48 into hbitx. 
  rename x49 into hbity.

  assert (Hhtcb_get: exists st m sus, get (set_tls_rdy subwl tcbls) (htcb_addr, Int.zero) = Some (hprio, st, m, sus)).
  {
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }
  destruct Hhtcb_get as (st & msg & sus & Hhtcb_get).
  
  assert (Hs1: Int.unsigned x33 <= 7). 
  {
    clear - H50 H68. 
    apply osunmapvallist_prop in H50.
    mytac.
    rewrite H in H68.
    inverts H68.
    auto with zarith.
  }
  assert (Hs2: Int.unsigned x34 <= 255). 
  {
    clear - H69 Hs1 H80 H44. 
    assert (Z.to_nat (Int.unsigned x33) < length etbl')%nat. 
    {
      rewrite H44; unfold OS_EVENT_TBL_SIZE.
      mauto.
    }
    lets Hx: array_int8u_nth_lt_len H80 H.
    mytac.
    rewrite H69 in H0.
    inverts H0.
    auto.
  }
  assert (Hs3: Int.unsigned x32 <= 7). 
  {
    clear - H70 Hs2.
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H70; inverts H70.
    auto with zarith.
  }

  lets H_elp_subwl: H52.
  eapply ecblist_p_decompose in H52; eauto. 
  destruct H52 as (els1_new & els2_new & x' & H'').
  destruct H'' as (Hecbl1_new & Hecbl2_new & Hjo_new).
  assert (Hx': x' = Vptr (eid_b, Int.zero)).
  {
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  subst x'.
  lets Hcp: Hecbl2_new.
  simpl in Hcp.
  mytac.
  inverts H2. (* Vptr (eid_b, ...) = Vptr x *)
  inverts H55.
  assert (Hx0: x0 = (absmsgq msgs maxlen pwl, remove_wls subwl wl)). 
  {
    eapply EcbMod.join_sig_get in H57.
    eapply EcbMod.join_get_r in H57; eauto.
    rewrite EcbMod.map_get_set in H57.
    inverts H57. auto.
  }
  subst x0. 
  destruct H63 as (_ & _ & _ & Hrh_ecb_new). 
  rename H57 into Hjo_sig_new. 
  rename H67 into Hecb_right_new.
  clear H52. (* R_ECB_ETbl_P (eid_b, Int.zero) ... *)

  assert(Hhtcb_join:= Hhtcb_get).
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  remember (remove_wls subwl wl) as pwls.
  assert (Hpre: pwls <> nil /\ GetHWait (set_tls_rdy subwl tcbls) pwls (htcb_addr, Int.zero) /\
                TcbMod.get (set_tls_rdy subwl tcbls) (htcb_addr, Int.zero) = Some (hprio, st, msg, sus) /\
                hprio = ((x33<<ᵢ$ 3) +ᵢ  x32)).  
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    eapply post_exwt_succ_pre'; eauto.
  }
  destruct Hpre as (Hpwls_not_nil & Hhwait & Hhtcb_get' & Hhprio_eq).
  subst hprio.

  rename H89 into Htcblist_p. 
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get. 
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac. 
  inverts H2; inverts H52.
  
  rename H55 into Hh_tcbblk. 
  rename H57 into Hh_tcbstat.
  unfolds in Hh_tcbblk.
  mytac.
  inverts H2. 
  inverts H55 (*V_OSTCBY*);
    inverts H57 (*V_OSTCBBitX*);
    inverts H63 (*V_OSTCBBitY*);
    inverts H67 (*V_OSTCBStat*);
    inverts H52 (*V_OSTCBX*);
    inverts H90 (*V_OSTCBEventPtr*). 

  rename x33 into p1.
  rename x32 into p2.
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio.
  
  (*tcbstat = $ OS_STAT_Q \/ tcbstat = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)*)
  assert (Hx: x8 = $ OS_STAT_Q \/ x8 = Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)). 
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }
  (*subst x8.*)

  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }
  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  } 
  assert (Hs4: Int.unsigned x51 <= 255). 
  {
    clear - Hs1 H60 H66 H65. 
    assert (Z.to_nat (Int.unsigned p1) < length rtbl')%nat.
    {
      rewrite H66.
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H65 H. 
    mytac.
    rewrite H60 in H0. 
    inverts H0.
    auto.
  }
  assert (Htmp: x35 = $ 1 <<ᵢ p2). 
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    mauto.
    auto.
  }
  subst x35.

  assert (Hno_dup: R_Prio_No_Dup (set_tls_rdy subwl tcbls)).
  {
    clear - H87.
    unfolds in H87.
    mytac.
  }

  sep_lifts_trms_in Hsat tcbdllseg. 
  eapply set_node_elim_sus in Hsat; eauto.
  2: {
    eapply TCBNode_P_set_rdy_gen with (row := x51); eauto. 
    rewrite Hp1. 
    eapply nth_val'2nth_val; eauto.
    destruct Hx; subst x8.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
    auto.
  }
  2: {
    destruct sus eqn: eq1; auto.
    unfolds.
    rewrite Hp1.
    rewrite Hp2.
    do 2 eexists.
    splits; eauto.
  }
  2: {
    unfolds. unfold V_OSTCBNext; simpl. auto. 
  }
  sep normal in Hsat. 
  sep destruct Hsat.
  sep split in Hsat.
  rename H2 into Htcblist_new.
  rename H52 into Htcbjoin_new_set.
  rename H55 into Htcblist_p_new_left.
  rename H57 into Htcblist_p_new_right.

  sep_lifts_trms_in Hsat llsegevaux.
  eapply llsegevaux_set_node in Hsat; eauto.
  2: { unfolds. simpl. splits; eauto. }

  assert (Htcbjoin_new_set':
            TcbMod.join x7 x12 (set_tls_rdy ((htcb_addr, Int.zero) :: nil) (set_tls_rdy subwl tcbls))). 
  {
    clear -Htcbjoin_new_set Hhtcb_get.
    simpl set_tls_rdy.
    unfold get in *; unfold TcbMap in *.
    rewrite Hhtcb_get. auto.
  }
  clear Htcbjoin_new_set; rename Htcbjoin_new_set' into Htcbjoin_new_set.
  rewrite set_tls_rdy_succ_eq in Htcbjoin_new_set. 
  assert (Hin_pwls: In (htcb_addr, Int.zero) (remove_wls subwl wl)).
  { clear -Hhwait. funfold Hhwait. mytac. }
  assert (Hst: exists xl, st = wait (os_stat_q (eid_b, Int.zero)) xl). 
  { eapply rh_tcblist_ecblist_p_post_exwt_aux; eauto. } 
  destruct Hst as (st_t & Hst). 
  subst st.

  assert (Hr_ptbl_new:
            R_PrioTbl_P ptbl' (set_tls_rdy ((htcb_addr, Int.zero) :: (subwl: list tid)) tcbls) vhold_addr).
  {
    rewrite <- set_tls_rdy_succ_eq with (wls := (subwl :list tid)) (tls := tcbls). 
    simpl set_tls_rdy at 1. 
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get. 
    rewrite Hhtcb_get. 
    eapply r_priotbl_p_set_hold; eauto. 
  }

  assert (Hrh_tls_els_new:
            RH_TCBList_ECBList_P
              (set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, remove_wls ((htcb_addr, Int.zero) :: subwl) wl))
              (set_tls_rdy ((htcb_addr, Int.zero) :: (subwl: list tid)) tcbls) ctcb).
  {
    rewrite <- remove_wls_succ_set_els_eq with (st' := absmsgq msgs maxlen pwl). 
    rewrite <- set_tls_rdy_succ_eq with (wls:= (subwl :list tid)) (tls := tcbls).
    simpl set_tls_rdy at 1.
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
    rewrite Hhtcb_get.
    eapply rh_tcblist_ecblist_p_post_exwt; eauto.
  }

  assert (H_elp_new:
            ECBList_P v'8 Vnull
                      (v'37 ++
                            ((V$ OS_EVENT_TYPE_Q
                               :: Vint32 egrp' :: Vint32 i2 :: qcb_ptr :: x2 :: x3 :: Vint32 i :: x5 :: nil,  
                              (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
                                              (Vint32 (x34&ᵢInt.not ($ 1<<ᵢp2)))), x15) :: nil) ++
                            v'38) (v'39 ++ (DMsgQ qcb_ptr osq osqblk msgtbl :: nil) ++ v'42) 
                      (set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, (remove_wls ((htcb_addr, Int.zero) :: subwl) wl)))  
                      (set_tls_rdy ((htcb_addr, Int.zero) :: subwl) tcbls)).
  { (* clear -H_elp_subwl Hhtcb_get'. *)
    rewrite <- remove_wls_succ_set_els_eq with (st':= (absmsgq msgs maxlen pwl)). 
    rewrite <- set_tls_rdy_succ_eq with (wls:= (subwl :list tid)) (tls := tcbls).
    simpl set_tls_rdy at 1.
    rewrite Hhtcb_get'.
    eapply ecblist_p_post_exwt_hold; eauto.
        
    eapply rl_etbl_ptbl_p' with (tcbls:=set_tls_rdy subwl tcbls); auto; eauto.
    subst hprio; auto. 
    clear -Hs3. mauto. 
    unfold RLH_ECBData_P. split; auto. 
    introv Hf. destruct Hf as (eid & k & Hf). inverts Hf. 
  }
  
  lets H_elp_cp: H_elp_new.
  eapply ecblist_p_decompose in H_elp_cp; eauto. 
  destruct H_elp_cp as (els1_new' & els2_new' & x' & H'').
  destruct H'' as (Hecbl1_new' & Hecbl2_new' & Hjo_new').
  assert (Hx': x' = Vptr (eid_b, Int.zero)).
  {
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  subst x'.
  lets Hcp: Hecbl2_new'.
  remember ((htcb_addr, Int.zero) :: subwl) as subwl'.
  simpl in Hcp.
  mytac.
  
  inverts H2.
  inverts H57.

  assert (Hx0: x14 = (absmsgq msgs maxlen pwl, remove_wls ((htcb_addr, Int.zero) :: subwl) wl)). 
  {
    eapply EcbMod.join_sig_get in H63.
    eapply EcbMod.join_get_r in H63;eauto.
    rewrite EcbMod.map_get_set in H63.
    inverts H63. auto.
  }
  subst x14.
  destruct H67 as (_ & _ & _ & Hrh_ecb_new').
  rename H63 into Hjo_sig_new'.
  rename H82 into Hecb_right_new'. 
  rename H52 into Hr_ecb_etbl_new'.
  lets Hgete_new: EcbMod.join_sig_get Hjo_sig_new'.
  eapply EcbMod.join_get_r in Hgete_new; eauto.

  assert (His_subl_part:
            (forall t, In t ((htcb_addr,Int.zero) :: subwl) -> In t wl) 
            /\ (forall t, ~(In t wl) -> ~ (In t ((htcb_addr,Int.zero) :: subwl)))
            /\ NoDup ((htcb_addr,Int.zero) :: subwl)).  
  {
    clear - H46 Hin_pwls. 
    unfold is_subl in *.
    mytac.
    splits; intros.
    eapply in_remove_wls in Hin_pwls.
    simpl in H3.
    destruct H3; try subst; auto.
    rewrite not_in_cons.
    assert (t = (htcb_addr, Int.zero) \/ t <> (htcb_addr, Int.zero)) by tauto.
    eapply in_remove_wls in Hin_pwls.
    destruct H4. subst; tryfalse.
    split; auto.
    eapply NoDup_cons; eauto.
    eapply in_remove_wls_nin; eauto.
  }
  destruct His_subl_part as (His_subl_part1 & His_subl_part2 & His_subl_part3).
  (* change tcbdllflag *)
  sep_lifts_trms_in Hsat tcbdllflag. 
  eapply tcbdllflag_set_node in Hsat; eauto.
  2: { unfolds. unfold V_OSTCBNext; simpl. auto. }
  
  assert (Heq_sus: Int.eq (x8&ᵢInt.not ($ OS_STAT_Q)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct Hx; subst x8.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
    auto.
   }
   rewrite Heq_sus in *.
   rewrite negb_if in *.
  (* tcbdllflag changed *)
  eexists. (* Aier *)
  exists (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
               (Vint32 (x34&ᵢInt.not ($ 1<<ᵢp2)))).
  exists x4.
  exists (if sus
          then rtbl'
          else(update_nth_val (Z.to_nat (Int.unsigned p1)) rtbl'
               (Vint32 (Int.or x51 ($ 1<<ᵢp2))))). (* new rtbl *)
  exists x10. (* new rgrp *)
  exists egrp'. (* new egrp *)
  exists ((htcb_addr, Int.zero) :: subwl).
  exists (V$ OS_STAT_Q).
  sep eexists.
  sep auto.
  assert (Hegrp'_case: egrp' = Int.zero \/ egrp' <> Int.zero) by (clear; tauto).
  destruct Hegrp'_case as [Hegrp'_eq | Hegrp'_neq];
  [left | right].
  (* case 1 : exit the loop after OS_EventTaskRdy *) 
  subst egrp'.
  assert (Hpwls'_eq: remove_wls ((htcb_addr, Int.zero) :: subwl) wl = nil). 
  {
    eapply Grp_eq_zero_imp_wl_nil with
        (etbl:= (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
                                (Vint32 (x34&ᵢInt.not ($ 1<<ᵢp2)))) ); eauto. 
    rewrite update_nth_val_len_eq; eauto.
  }
  assert (Hsubwl_eq': set_tls_rdy ((htcb_addr,Int.zero) :: subwl) tcbls = set_tls_rdy wl tcbls).  
  {
    assert (Heq: ((htcb_addr,Int.zero) :: subwl) ++ remove_wls ((htcb_addr, Int.zero) :: subwl) wl
                 = ((htcb_addr,Int.zero) :: subwl)).
    rewrite Hpwls'_eq. rewrite app_nil_end; auto.
    rewrite <- Heq.
    eapply set_tls_rdy_eq_alt_gen; eauto.
  }
  rewrite Hpwls'_eq in *.
  rewrite Hsubwl_eq' in *.
  splits; eauto.
  rewrite update_nth_val_len_eq; eauto.
  (* case 2 : stay in the loop after OS_EventTaskRdy *)
  assert (Hegrp'_range: Int.unsigned egrp' <= 255).
  {
   clear -H77.
  simpl in H77.
  destruct H77 as (_ & H & _).
  eapply int_true_le255; eauto.
   }
   splits; eauto.
   unfold is_subl.
  splits; auto.
  simpl length.
  eapply length_lt_succ; eauto.
   eapply Grp_eq_nz_imp_wl_not_nil with (etbl:= (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
       (Vint32 (x34&ᵢInt.not ($ 1<<ᵢp2)))) ); eauto.
  rewrite update_nth_val_len_eq; eauto.
  rewrite update_nth_val_len_eq; eauto.
  rewrite Hp1 in *; rewrite Hp2 in *; eauto.
  rewrite Hp1 in *; rewrite Hp2 in *; eauto.
  auto.
  (* end of OS_EventTaskRdy *)

  hoare normal pre.
  apply ex_intro_rule; intro ier. (* new add *)
  repeat (apply ex_intro_rule; intro).
  eapply backward_rule1.
  introv Hsat.
  destruct Hsat as (Hsat & Hisfalse).
  lets Hcp: aconj_intro Hsat Hisfalse.
  eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
   {
    introv Hsat'.
    clear HeqH2.
    sep get rv.
    sep split in Hsat'.
     destruct H41; simpljoin.
     go.
     go.
     pure_auto.
     pure_auto.
  }
  hoare_split_pure_all.
  destruct (Int.eq v'12 ($ 0)) eqn: if_eq1;
  simpl in H41; try change (Int.notbool Int.zero) with Int.one in H41; destruct H41; tryfalse.
  change ($ 0) with Int.zero in *.
  eapply semacc_int_eq_true in if_eq1; subst v'12.
  match goal with
    H: RL_Tbl_Grp_P _ (Vint32 Int.zero) /\ _ \/ _  |- _ =>
    destruct H as [Hcase_z | Hcase_nz];
    [ idtac |
      simpljoin; tryfalse ]
  end.
  clear H41.
  destruct Hcase_z as (Htblgrp & Hetblmt & _ & (Hsub & Hrm) & Hlen_etbl' & H_elp').
  assert (Hsubwl_eq':  set_tls_rdy v'13 tcbls 
                                               = set_tls_rdy wl tcbls).
  { assert (Heq: v'13 ++ remove_wls v'13 wl
                                = v'13).
     rewrite Hrm. rewrite app_nil_end; auto.
     assert (Hsubwl: v'13 = nil \/ v'13 <> nil) by tauto.
     destruct Hsubwl.
     subst. rewrite remove_wls_nil in Hrm.
     subst. auto.
     destruct Hsub. subst; tryfalse.
     rewrite <- Heq.
     eapply set_tls_rdy_eq_alt_gen; eauto.
   }
  rewrite Hrm in *.
  rewrite Hsubwl_eq' in *.
  rename v'7 into etbl'.
  clear Hsub Hrm Hsubwl_eq'.
  unprotect HeqH2.
  (* end of while loop with call to OS_EventTaskRdy *)
  remember (set_tls_rdy wl tcbls) as tcbls_wlrdy.
  remember (set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, nil)) as els_wlrdy.
  protect Heqtcbls_wlrdy.
  protect Heqels_wlrdy.

  subst H2.
(*   hoare_split_pure_all. *)

(*   destruct H45 as (Htblgrp & Hetblmt & H_elp'). *)
  lets H00: ecblist_p_decompose H_elp'; eauto.
  rename els1 into els10.
  rename els2 into els20.
  destruct H00 as (els1 & els2 & x' & H'').
  rename Hecbl1 into Hecbl1_.
  rename Hecbl2 into Hecbl2_.
  rename Hjo into Hjo_.
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).      
  hoare_assert_pure (x' = Vptr (eid_b, Int.zero)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst.

  (* TODO: unfold Hecbl2 to obtain further details *)
  assert (Hecbl' := Hecbl2).
  do 2 (rewrite ele_lst_cons in Hecbl'). 
  unfold ECBList_P in Hecbl'. 
  fold ECBList_P in Hecbl'.
  rename Hecbetbl into Hecbetbl_.
  rename Hecbpetbl into Hecbpetbl_.
  destruct Hecbl' as (qid & Hqid & Hecbetbl & Hecbpetbl & Hex).
  inverts Hqid.
  rename mqls' into mqls'_.
  rename v'' into v''_.
  rename Hjo' into Hjo'_.
  rename Hecbl20 into Hecbl20_.
  destruct Hex as (absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
  unfold V_OSEventListPtr in Helptr.
  inverts Helptr.

  rename Hgetmq into Hgetmq_.
  assert (Hgetmq: get els_wlrdy (eid_b, Int.zero) = Some absmq).
  {
    eapply join_get_r; eauto.
    eapply join_get_l; eauto.
    apply get_a_sig_a.
  }
  assert (Hecb_wlrdy: get els_wlrdy (eid_b, Int.zero) = Some (absmsgq msgs maxlen pwl, nil)).
  {
    unprotect Heqels_wlrdy.
    subst. 
    rewrite set_a_get_a; auto. 
  }
  assert (Hmqeq: absmq = (absmsgq msgs maxlen pwl, nil)). 
  {
    unfold get, EcbMap in Hgetmq.
    unfold get, EcbMap in Hecb_wlrdy.
    rewrite Hgetmq in Hecb_wlrdy.
    inverts Hecb_wlrdy; auto. 
  }
  subst absmq.

  (* what can be obtained from Hrlh at this point is already present in the assms *)  
  
  hoare_lifts_trms_pre (
      Aop, Aier,
      Astruct (eid_b, Int.zero), AOSPostEventTbl, AEventData,
      AOSMapTbl, AOSUnMapTbl,
      AOSTCBPrioTbl,
      Agvarmapsto OSTCBList, tcbdllseg tcb_head, Agvarmapsto OSTCBCur, tcbdllseg (Vptr ct),  
      AOSRdyTblGrp, tcbdllflag, x, pevent, llsegevaux
    ).
  hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17 ::nil)%nat pre.    
  protect HeqH2.
  rename tcbvl_l into tcbvl_l0;
    rename v'54 into tcbvl_l. 
  rename tcbvl_ct into tcbvl_ct0;
    rename v'9 into tcbvl_ct.
  rename tcbvl_r into tcbvl_r0;
    rename v'56 into tcbvl_r. 
  rename rtbl into rtbl0;
    rename v'10 into rtbl.
  clear rgrp;
    rename v'11 into rgrp.

  (* change pre-condition to loop inv. *)
  eapply backward_rule1 with (
        p := EX ier petbl' tcbvl_ct' rtbl' rgrp' pegrp subwl vx (tcbls_l' tcbls_r': TcbMod.map) tcbvl_l' tcbvl_r' tail1 
                losqblk osq' msgtbl', 
             <|| spec_code_cons (qdel (Vptr (eid_b, Int.zero) :: nil)) v'4 ||> **
               Aier ier ** (* new add *)
                LV x @ Int16u |-> vx ** 
                AOSMapTbl **
                AOSUnMapTbl ** 
                AOSTCBPrioTbl v'6 rtbl' (set_tls_rdy0 subwl tcbls_wlrdy) v'20 vhold_addr **
                GV OSTCBList @ OS_TCB ∗ |-> tcb_head **
                tcbdllseg tcb_head Vnull tail1 (Vptr ct) tcbvl_l' **
                GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
                tcbdllseg (Vptr ct) tail1 tcb_tail Vnull (tcbvl_ct' :: tcbvl_r') ** 
                [| TcbMod.join tcbls_l' tcbls_r' (set_tls_rdy0 subwl tcbls_wlrdy) |] **
                [| TCBList_P tcb_head tcbvl_l' rtbl' tcbls_l' |] **
                [| TCBList_P (Vptr ct) (tcbvl_ct' :: tcbvl_r') rtbl' tcbls_r' |] **
                [| RH_TCBList_ECBList_P
                     (set els_wlrdy (eid_b, Int.zero) (absmsgq msgs maxlen (remove_wls subwl pwl), nil)) 
                     (set_tls_rdy0 subwl tcbls_wlrdy) ct |] **
                tcbdllflag tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') **  
                AOSRdyTblGrp rtbl' rgrp' ** 
                Astruct (eid_b, Int.zero) OS_EVENT  
                  (V$ OS_EVENT_TYPE_Q :: Vint32 Int.zero :: Vint32 i2 :: qcb_ptr :: x2 :: v'' :: Vint32 pegrp :: x5 :: nil) **
                Aarray v'52 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) petbl' **
                node qcb_ptr osq' OS_Q **
                [| WellformedOSQ0 osq' |] ** 
                [| V_qfreeblk osq' = Some losqblk |] ** 
                AOSQBlk losqblk osqblk msgtbl' ** 
                (* AEventData *)
                (*   (V$ OS_EVENT_TYPE_Q :: Vint32 Int.zero :: Vint32 i2 :: qcb_ptr :: x2 :: v'' :: Vint32 pegrp :: x5 :: nil)  *)
                (*   (DMsgQ qcb_ptr osq osqblk msgtbl') **  *) 
                llsegevaux tcb_head Vnull (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') locmp ptrmp V_OSTCBNext ** 
                LV pevent @ OS_EVENT ∗ |-> Vptr (eid_b, Int.zero) ** 
                H2 ** 
                [| RL_Tbl_Grp_P petbl' (Vint32 pegrp)  /\ array_type_vallist_match Tint8 petbl' /\
                   Int.unsigned pegrp <= 255 /\ 
                   R_ECB_ETbl_P
                     (eid_b, Int.zero)
                     (V$ OS_EVENT_TYPE_Q :: Vint32 Int.zero :: Vint32 i2 :: qcb_ptr :: x2 :: v'' :: Vint32 pegrp :: x5 :: nil, etbl', petbl') 
                     (set_tls_rdy0 subwl tcbls_wlrdy) /\ 
                   R_ECB_PETbl_P
                     (eid_b, Int.zero)
                     (V$ OS_EVENT_TYPE_Q :: Vint32 Int.zero :: Vint32 i2 :: qcb_ptr :: x2 :: v'' :: Vint32 pegrp :: x5 :: nil, etbl', petbl')
                     (set_tls_rdy0 subwl tcbls_wlrdy) /\
                   ECBList_P v'8 (Vptr (eid_b, Int.zero)) v'37 v'39 els1 (set_tls_rdy0 subwl tcbls_wlrdy) /\ 
                   ECBList_P v'' Vnull v'38 v'42 mqls' (set_tls_rdy0 subwl tcbls_wlrdy)  |] ** 
                [| Int.eq pegrp Int.zero = true /\ remove_wls subwl pwl = nil
                     /\ set_tls_rdy0 subwl tcbls_wlrdy = set_tls_rdy0 pwl tcbls_wlrdy \/
                    Int.eq pegrp Int.zero = false /\ is_subl subwl pwl |]
  ).
  introv Hsat.
  assert (Hlen_petbl: length petbl = ∘ OS_EVENT_TBL_SIZE).
  {
    sep_lifts_trms_in Hsat AOSPostEventTbl.
    apply postevttbl_petbl_len in Hsat; auto. 
  }
  assert (Hpmt: array_type_vallist_match char_t petbl).
  {
    sep_lifts_trms_in Hsat AOSPostEventTbl.
    unfold AOSPostEventTbl in Hsat.
    sep split in Hsat; eauto. 
  }
  assert (Hwf0: WellformedOSQ0 osq).
  {
    unfold AEventData in Hsat.
    unfold AMsgData in Hsat.
    sep normal in Hsat. sep destruct Hsat. 
    unfold AOSQCtr in Hsat.
    sep normal in Hsat. sep split in Hsat.
    clear -H40. unfold WellformedOSQ in H40.
    unfold WellformedOSQ0.
    simpljoin1. do 7 eexists. splits; eauto.
    splits; eauto. 
  }

  casetac i Int.zero Hpegrp_zero Hpegrp_nzero.
  (* content of "event group" is zero *)
  subst.
  assert (Hpwls: pwl = nil). 
  {
    lets H00: Grp_eq_zero_imp_pwl_nil Hpmt Hlen_petbl H22 Hecbpetbl H39.
    eapply H00; eauto. 
  }
  subst.

  unfold AEventData in Hsat.
  unfold AMsgData in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  do 6 eexists. exists (nil: list tid). do 9 eexists.
  assert(Hels: set els_wlrdy (eid_b, Int.zero) (absmsgq msgs maxlen (remove_wls nil nil), nil) = els_wlrdy).  
  {
    rewrite remove_wls_nil_eq.
    eapply EcbMod.get_set_same; eauto.
  }
  rewrite Hels.
  rewrite set_tls_rdy0_nil.
  sep pauto; eauto. 
  sep cancel AOSTCBPrioTbl.
  sep cancel Aop.
  sep cancel Aier.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg. 
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSQBlk.
  unfold AOSQCtr, AOSPostEventTbl in Hsat.
  sep pauto.
  splits; auto. 

  (* content of "event group" is non-zero *)       
  assert (Hpwls: pwl <> nil). 
  {
    lets H00: Grp_eq_nz_imp_pwl_not_nil Hpmt Hlen_petbl H22 Hpegrp_nzero Hecbpetbl.
    eapply H00; eauto. 
  }
  unfold AEventData in Hsat.
  unfold AMsgData in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  do 6 eexists. exists (nil: list tid). do 9 eexists.
  assert (Hels: set els_wlrdy (eid_b, Int.zero) (absmsgq msgs maxlen (remove_wls nil pwl), nil) = els_wlrdy).
  {
    rewrite remove_wls_nil.
    apply EcbMod.get_set_same; eauto.     
  }
  rewrite Hels.
  rewrite set_tls_rdy0_nil.
  (* assert (His_subl_nil: is_subl nil wl). *)
  (* { eapply nil_is_subl; eauto. } *)
  sep pauto; eauto. 
  sep cancel AOSTCBPrioTbl. 
  sep cancel Aop.
  sep cancel Aier.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  sep cancel tcbdllflag.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSQBlk.
  sep cancel llsegevaux. 
  unfold AOSPostEventTbl, AOSQCtr in Hsat.
  sep pauto. 
  {
    clear -Hpegrp_nzero Hpwls.
    right.
    split. apply Int.eq_false; auto. apply nil_is_subl; auto.
  }
  splits; auto. 

  eapply seq_rule.
  eapply while_rule with (tp := Int32u).
  {
    introv Hsat.
    sep destruct Hsat.
    sep split in Hsat.
    simpljoin1. 
    eexists. 
    eapply uop_rv; eauto. 
    eapply bop_rv; eauto.
    eapply struct_member_rv''.
    sep cancel pevent.
    sep cancel Astruct.
    eauto. 
    go. go. go. go. go. go. go. go. 
    pure_auto. 
    sep get rv.
    simpl. destruct (Int.eq x6 ($ 0)); simpl; pure_auto.
    go.
    simpl. destruct (Int.eq x6 ($ 0)); simpl; pure_auto.
    go. 
  }

  hoare normal pre.
  apply ex_intro_rule; intro ier'.
  repeat (apply ex_intro_rule; intro).
  eapply backward_rule1.  
  introv Hsat.
  eapply sep_aconj_r_aistrue_to_astar in Hsat; eauto.
  {
    introv Hs; clear Hsat.
    sep split in Hs.
    simpljoin1.
    eapply uop_rv; eauto.
    eapply bop_rv; eauto.
    eapply struct_member_rv'';  auto. 
    sep cancel pevent.
    sep cancel Astruct.
    eauto. 
    go. go. go. go. go. go. go.
    clear -H51. (* Int.unsigned _ <= 255 *)
    pure_auto.
    sep get rv.
    simpl. destruct (Int.eq v'12 ($ 0)); simpl; pure_auto.
    go.
    simpl. destruct (Int.eq v'12 ($ 0)); simpl; pure_auto.
    go. 
  }

  hoare_split_pure_all.
  match goal with
    H: val_inj _ <> _ /\ val_inj _ <> _ /\ val_inj _ <> _ |- _ => rename H into Hinjand
  end.
  assert (Hconj: v'12 <> Int.zero /\ Int.eq v'12 Int.zero = false).
  {
    destruct Hinjand as (Hinj1 & _ & _). 
    simpl in Hinj1.
    destruct (Int.eq v'12 Int.zero) eqn: Epeg; simpl in Hinj1.
    false. apply Hinj1. pure_auto.
    split; auto.
    clear -Epeg. apply semacc_int_eq_false in Epeg; auto.
  }
  clear Hinjand.
  destruct Hconj as (Hpegrp_nzero & Hpegrp_neqz).
  assert (Hsub: is_subl v'54 pwl).
  {
    destruct H47 as [Ht | Hf].
    rewrite Hpegrp_neqz in Ht. simpljoin1; tryfalse.
    simpljoin1. auto. 
  }
  rename Htblgrp into Htblgrp_.
  rename Hecbetbl into Hecbetbl__.
  rename Hecbpetbl into Hecbpetbl__.
  destruct H46 as (Htblgrp & Hmtptbl & Hpegle & Hecbetbl & Hecbpetbl & H_elp1 & H_elp2).

  unprotect HeqH2.
  (* x ′ =ₑ ′ OS_STAT_POSTQ;ₛ *) 
  hoare forward.

  assert (Hqbp: exists p, v'63 = Vptr p). 
  {
    clear -H44 H45.
    unfold WellformedOSQ0 in H44. simpljoin1.
    rewrite H4 in H45. inverts H45.
    eexists; eauto.
  }
  destruct Hqbp as (p & Hqbp).
  subst v'63.

  (* OS_EventTaskPostRdy (-pevent ′, x ′ -) *) 
  unfold AOSTCBPrioTbl.
  hoare unfold pre.
  fold_node.
  hoare_lifts_trms_pre Aop.  
  match goal with |- {|_, _, _, _, _, _|}|- ct {{_}} _ {{?Q}} => remember Q as PP end.
  protect HeqPP.
  eapply conseq_rule; [eauto | idtac | idtac].
  Focus 2.
  hoare_call.
(*   hoare forward. *)

  sep cancel AOSRdyTblGrp.
  sep cancel AOSQBlk.
  get_hsat Hsat. 
  sep_lifts_trms_in Hsat (node qcb_ptr).
  sep cancel node.
  sep_lifts_trms_in Hsat (tcbdllseg tcb_head, tcbdllseg (Vptr ct)).
  eapply tcbdllseg_compose in Hsat; eauto.
  sep cancel tcbdllseg.
  sep cancel p_local.
  
  unfold AOSEvent.
  unfold AOSEventTbl, AOSPostEventTbl.
  sep pauto.
  sep cancel node.
  sep_lifts_trms_in Hsat (Aarray v'50, Aarray v'52).
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  eauto. 

  eauto. (* RL_Tbl_Grp_P ... *)
  go.
  auto. (* id_addrval' (Vptr (eid_b, Int.zero)) OSPostEventTbl OS_EVENT = ... *)
  auto. (* array_type_vallist_match char_t ... *) 
  eauto. (* RL_Tbl_Grp_P ... (for egrp) *) 
  go.
  auto. (* id_addrval' (Vptr (eid_b, Int.zero)) os_code_defs.OSEventTbl OS_EVENT *) 
  auto. (* array_type_vallist_match char_t ... *)
  
  eauto. (* R_ECB_PETbl_P *)
  go.
  splits; eauto.
  go.
  simpl. eauto.
  simpl. auto.
  
  { (* TCBList_P *)
    eapply TCBList_P_Combine. 
    eapply tcbdllseg_get_last_tcb_ptr with (s:=s).
    sep cancel tcbdllseg.
    eauto.
    join auto.
    auto. auto. 
  }
  
  auto. (* R_ECB_ETbl_P *)
  eauto.
  auto.
  
  { (* ptr_in_tcblist ... *)
    eapply tcbdllseg_combine_ptr_in_tcblist with (s:=s). 
    sep cancel tcbdllseg.
    sep cancel tcbdllseg.
    eauto.
    auto.
  }

  go.
  auto.
  go.
  go.  (* GoodFrm *)

  introv Hsat. sep auto.
  introv Hsat. sep auto.
  
  (* show: post-cond of call to OS_EventTaskPostRdyDel -> loop inv. *)
  introv Hsat.
(*   get_hsat Hsat.  *)
  unfold OS_EventTaskPostRdyDelPost in Hsat.
  unfold OS_EventTaskPostRdyDelPost' in Hsat.
  unfold getasrt in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  unfold AOSEvent in Hsat. 
  unfold AOSEventTbl in Hsat.
  unfold AOSPostEventTbl in Hsat. 
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  unprotect HeqPP.
  subst PP.
  inverts H96. (* logic_val ... = ... *) 
  simpl nth_val in *.
  simpl update_nth_val in *.
  inverts H87; inverts H88.
  substs.
  
  inverts H54. (* V_OSEventGrp ... = ... *) 
  inverts H58. (* V_OSPostEventGrp ... = ... *)
  rename x11 into pegrp.
  rename x12 into pegrp'.
  rewrite H17 in H53; inverts H53. (* id_addrval' ... = ... *) 
  rewrite H20 in H57; inverts H57. (* id_addrval' ... = ... *)  
  simpljoin1.

  rename ct into ctcb.
  rename x52 into htcb_addr.
  rename H63 into Hhtcb.
  rename H89 into Hctcb_in_tcblist.
  rename x20 into tcblist_head.
  rename v'9 into ctcb_node.
  
  rename x6 into ptbl'.
  rename x7 into rtbl'.
  rename v'54 into subwl.
  rename x13 into etbl'.
  rename x14 into petbl'.
  
  rename x47 into hprio.
  assert (Hex: exists hprio', hprio = Vint32 hprio').
  {
    clear - H73. (* struct_type_vallist_match OS_TCB_flag *) 
    rename H73 into H.
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }
  destruct Hex as (hp & H__).
  subst hprio.
  rename hp into hprio.  

  rename x42 into hnext. 
  rename x48 into htcbx. 
  rename x49 into htcby. 
  rename x50 into hbitx. 
  rename x51 into hbity. 

  assert (Hhtcb_get: exists st m sus, get (set_tls_rdy0 subwl tcbls_wlrdy) (htcb_addr, Int.zero) = Some (hprio, st, m,sus)). 
  {
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }
  destruct Hhtcb_get as (st & msg & sus & Hhtcb_get).
  
  assert (Hs1: Int.unsigned x36 <= 7).
  {
    clear - Hpegle H68.
    apply osunmapvallist_prop in Hpegle.
    mytac.
    rewrite H in H68.
    inverts H68.
    auto with zarith.    
  }
  assert (Hs2: Int.unsigned x37 <= 255). 
  {
    clear - H69 Hs1 H81 H51.
    assert (Z.to_nat (Int.unsigned x36) < length petbl')%nat. 
    {
      rewrite H51; unfold OS_EVENT_TBL_SIZE.
      mauto.
    }
    lets Hx: array_int8u_nth_lt_len H81 H.
    mytac.
    rewrite H69 in H0.
    inverts H0.
    auto.
  }
  assert (Hs3: Int.unsigned x35 <= 7). 
  {
    clear - H70 Hs2.
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H70; inverts H70.
    auto with zarith.
  }

  remember (remove_wls subwl pwl) as pwlsub. 
  assert (Hjo2:
            TcbJoin (eid_b, Int.zero) (absmsgq msgs maxlen pwlsub, nil) mqls'
                    (set els2 (eid_b, Int.zero) (absmsgq msgs maxlen pwlsub, nil))). 
  {
    unfold TcbJoin.
    asserts_rewrite (
        sig (eid_b, Int.zero) (absmsgq msgs maxlen pwlsub, nil) =
        set (sig (eid_b, Int.zero) (absmsgq msgs maxlen pwl, nil))
            (eid_b, Int.zero) (absmsgq msgs maxlen pwlsub, nil)). 
    { rewrite set_sig; auto. }
    eapply join_set_l; eauto.
    unfold indom. eexists.
    rewrite map_get_sig; eauto.
  }
  assert (Hjonew:
            join els1 (set els2 (eid_b, Int.zero) (absmsgq msgs maxlen pwlsub, nil))
                 (set els_wlrdy (eid_b, Int.zero) (absmsgq msgs maxlen pwlsub, nil))).
  {
    eapply join_set_r; eauto.
    clear -Hjo'.
    unfold TcbJoin in Hjo'.
    eexists. eapply join_get_l; eauto.
    rewrite map_get_sig. eauto.
  }
  
  assert(Hhtcb_join:= Hhtcb_get).
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join). 

  assert (Hpre: pwlsub <> nil /\ GetHWait (set_tls_rdy0 subwl tcbls_wlrdy) pwlsub (htcb_addr, Int.zero) /\ 
                TcbMod.get (set_tls_rdy0 subwl tcbls_wlrdy) (htcb_addr, Int.zero) = Some (hprio, st, msg, sus) /\
                hprio = ((x36<<ᵢ$ 3) +ᵢ  x35)).  
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    eapply post_exwt_succ_pre_pwl with
        (pegrp:=pegrp) (ptbl':=ptbl') (tcbls':=set_tls_rdy0 subwl tcbls_wlrdy) (petbl':=petbl'); 
      eauto.
  }   
  destruct Hpre as (Hpwls_not_nil & Hhwait & Hhtcb_get' & Hhprio_eq).
  subst hprio.

  rename H94 into Htcblist_p. 
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get. 
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H63; inverts H75. 

  rename H76 into Hh_tcbblk. 
  rename H77 into Hh_tcbstat. 
  unfolds in Hh_tcbblk.
  mytac.
  inverts H63.  
  inverts H76 (*V_OSTCBY*);
    inverts H77 (*V_OSTCBBitX*);
    inverts H87 (*V_OSTCBBitY*);
    inverts H88 (*V_OSTCBStat*);
    inverts H75 (*V_OSTCBX*);
    inverts H102 (*V_OSTCBEventPtr*).   

  rename x36 into p1.
  rename x35 into p2. 
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio.

  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }
  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  } 
  assert (Hs4: Int.unsigned x53 <= 255). 
  {
    clear - Hs1 H60 H64 H61.
    assert (Z.to_nat (Int.unsigned p1) < length rtbl')%nat.
    {
      rewrite H64.
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H61 H. 
    mytac.
    rewrite H60 in H0. 
    inverts H0.
    auto.
  }
  assert (Htmp: x38 = $ 1 <<ᵢ p2). 
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    mauto.
    auto.
  }
  subst x38.

  assert (Hno_dup: R_Prio_No_Dup (set_tls_rdy0 subwl tcbls_wlrdy)).
  {
    clear - H92.
    unfolds in H92. 
    mytac.
  }

  sep_lifts_trms_in Hsat tcbdllseg. 
  eapply set_node_elim_sus in Hsat; eauto.
  2: {
    eapply TCBNode_P_set_rdy_gen with (row := x53); eauto. 
    rewrite Hp1. 
    eapply nth_val'2nth_val; eauto.
    destruct H67; subst x6.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_Q) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_Q)) with ($ OS_STAT_SUSPEND).
    auto.
  }
  2: {
    destruct sus eqn: eq1; auto.
    unfolds.
    rewrite Hp1.
    rewrite Hp2.
    do 2 eexists.
    splits; eauto.
  } 
  2: {
    unfolds. unfold V_OSTCBNext; simpl. auto. 
  }
  sep normal in Hsat. 
  sep destruct Hsat.
  sep split in Hsat.
  rename H63 into Htcblist_new.
  rename H75 into Htcbjoin_new_set.
  rename H76 into Htcblist_p_new_left.
  rename H77 into Htcblist_p_new_right.
  sep_lifts_trms_in Hsat llsegevaux.
  eapply llsegevaux_set_node in Hsat; eauto.
  2: { unfolds. simpl. splits; eauto. }
  assert (Htcbjoin_new_set':
            TcbMod.join x4 x8 (set_tls_rdy0 ((htcb_addr, Int.zero) :: nil) (set_tls_rdy0 subwl tcbls_wlrdy))). 
  {
    clear -Htcbjoin_new_set Hhtcb_get.
    simpl set_tls_rdy0. 
    unfold get in *; unfold TcbMap in *.
    rewrite Hhtcb_get. auto.
  }

  clear Htcbjoin_new_set; rename Htcbjoin_new_set' into Htcbjoin_new_set.       
  rewrite set_tls_rdy0_succ_eq in Htcbjoin_new_set. 
  assert (Hin_pwls: In (htcb_addr, Int.zero) (remove_wls subwl pwl)).
  { clear -Hhwait. funfold Hhwait. mytac. }
  assert (Hst: exists xl, st = wait (os_stat_postq (eid_b, Int.zero)) xl). 
  { eapply rh_tcblist_ecblist_p_post_exwt_aux_pwl; eauto. } 
  destruct Hst as (st_t & Hst). 
  subst st. 

  assert (Hr_ptbl_new:
            R_PrioTbl_P ptbl' (set_tls_rdy0 ((htcb_addr, Int.zero) :: (subwl: list tid)) tcbls_wlrdy) vhold_addr). 
  {
    rewrite <- set_tls_rdy0_succ_eq with (wls := (subwl :list tid)) (tls := tcbls_wlrdy).  
    simpl set_tls_rdy0 at 1. 
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get. 
    rewrite Hhtcb_get. 
    eapply r_priotbl_p_set_hold; eauto. 
  }
  
  assert (Hrh_tls_els_new:
            RH_TCBList_ECBList_P
              (set els_wlrdy
                   (eid_b, Int.zero)
                   (absmsgq msgs maxlen (remove_wls ((htcb_addr, Int.zero) :: subwl) pwl), nil)) 
              (set_tls_rdy0 ((htcb_addr, Int.zero) :: (subwl: list tid)) tcbls_wlrdy) ctcb). 
  {
    rewrite <- remove_wls_succ_set_els_eq_pwl with (wl':=nil). 
    rewrite <- set_tls_rdy0_succ_eq with (wls := (subwl: list tid)) (tls := tcbls_wlrdy). 
    simpl set_tls_rdy0 at 1.
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
    rewrite Hhtcb_get.
    eapply rh_tcblist_ecblist_p_post_exwt_pwl; eauto. 
  }

  assert (H_elp_l':
            ECBList_P v'8 (Vptr (eid_b, Int.zero)) v'37 v'39 els1
                     (set_tls_rdy0 ((htcb_addr, Int.zero)::subwl) tcbls_wlrdy)). 
  {
    rewrite <- set_tls_rdy0_succ_eq with (wls := (subwl: list tid)) (tls := tcbls_wlrdy).
    simpl set_tls_rdy0 at 1.
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
    rewrite Hhtcb_get.
    eapply ECBList_P_Set_Post_Rdy_hold; eauto.
    apply join_disj in Hjonew.
    eapply disjoint_sem2 with (t:=(eid_b, Int.zero)) in Hjonew; eauto.
    rewrite set_a_get_a. eauto. 
  }    
  assert (H_elp_r':
            ECBList_P v'' Vnull v'38 v'42 mqls'
                      (set_tls_rdy0 ((htcb_addr, Int.zero)::subwl) tcbls_wlrdy)).  
  {
    rewrite <- set_tls_rdy0_succ_eq with (wls := (subwl: list tid)) (tls := tcbls_wlrdy).
    simpl set_tls_rdy0 at 1.
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
    rewrite Hhtcb_get.    
    eapply ECBList_P_Set_Post_Rdy_hold; eauto.    
    apply join_disj in Hjo2. 
    eapply disjoint_sem1 with (t:=(eid_b, Int.zero)) in Hjo2; eauto.
    rewrite get_a_sig_a. eauto.     
  }

  assert (Hecbetbl': 
            R_ECB_ETbl_P (eid_b, Int.zero)
                         (V$ OS_EVENT_TYPE_Q
                           :: Vint32 Int.zero :: Vint32 i2 :: x29 :: x2 :: v'' :: Vint32 pegrp' :: x5 :: nil, etbl',
                          (update_nth_val (Z.to_nat (Int.unsigned p1)) petbl' (Vint32 (x37 &ᵢ Int.not ($ 1<<ᵢp2)))))  
                         (set_tls_rdy0 ((htcb_addr, Int.zero) :: subwl) tcbls_wlrdy)).
  {
    rewrite <- set_tls_rdy0_succ_eq with (wls := (subwl: list tid)) (tls := tcbls_wlrdy).
    simpl set_tls_rdy0 at 1.
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
    rewrite Hhtcb_get.        
    eapply R_ECB_ETbl_P_waitq_rdy_preserve; eauto.
    introv Hf. destruct Hf as (eid & k & Hf). inverts Hf. 
  }
  assert (Hecbpetbl':
            R_ECB_PETbl_P (eid_b, Int.zero)
                          (V$ OS_EVENT_TYPE_Q
                            :: Vint32 Int.zero :: Vint32 i2 :: x29 :: x2 :: v'' :: Vint32 pegrp' :: x5 :: nil, etbl',
                           (update_nth_val (Z.to_nat (Int.unsigned p1)) petbl' (Vint32 (x37 &ᵢ Int.not ($ 1<<ᵢp2)))))  
                          (set_tls_rdy0 ((htcb_addr, Int.zero) :: subwl) tcbls_wlrdy)).
  {
    rewrite <- set_tls_rdy0_succ_eq with (wls := (subwl: list tid)) (tls := tcbls_wlrdy).
    simpl set_tls_rdy0 at 1.
    unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
    rewrite Hhtcb_get.
    change (V$ OS_EVENT_TYPE_Q
                            :: Vint32 Int.zero :: Vint32 i2 :: x29 :: x2 :: v'' :: Vint32 pegrp' :: x5 :: nil) with
     (update_nth_val 6 (V$ OS_EVENT_TYPE_Q
                            :: Vint32 Int.zero :: Vint32 i2 :: x29 :: x2 :: v'' :: Vint32 pegrp :: x5 :: nil) (Vint32 pegrp')).
    eapply OSQPostPure_ext.R_ECB_PETbl_P_hold_for_update_postq_to_rdy; eauto.
    rewrite <- Hp2. auto.
  }

  assert (His_subl_part: 
            (forall t, In t ((htcb_addr, Int.zero) :: subwl) -> In t pwl) 
            /\ (forall t, ~(In t pwl) -> ~ (In t ((htcb_addr,Int.zero) :: subwl)))
            /\ NoDup ((htcb_addr, Int.zero) :: subwl)).  
  {
    clear - Hsub Hin_pwls. 
    unfold is_subl in *.
    mytac.
    splits; intros.
    eapply in_remove_wls in Hin_pwls.
    simpl in H3.
    destruct H3; try subst; auto.
    rewrite not_in_cons.
    assert (t = (htcb_addr, Int.zero) \/ t <> (htcb_addr, Int.zero)) by tauto.
    eapply in_remove_wls in Hin_pwls.
    destruct H4. subst; tryfalse.
    split; auto.
    eapply NoDup_cons; eauto.
    eapply in_remove_wls_nin; eauto.
  }
  destruct His_subl_part as (His_subl_part1 & His_subl_part2 & His_subl_part3).

  (* change tcbdllflag *)
  sep_lifts_trms_in Hsat tcbdllflag. 
  eapply tcbdllflag_set_node in Hsat; eauto.
  2: { unfolds. unfold V_OSTCBNext; simpl. auto. }
  (* tcbdllflag changed *) 
 
  assert (Heq_sus: Int.eq (x6&ᵢInt.not ($ OS_STAT_POSTQ)) ($ OS_STAT_RDY) = negb sus).
  { change ($ OS_STAT_RDY) with Int.zero.
    destruct H67; subst x6.
    assert (Hsus: sus = false) by
    (eapply oscore_common.tcb_stat_imp_sus_false ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    rewrite Int.and_not_self; auto.
    assert (Hsus: sus = true) by
    (eapply oscore_common.tcb_stat_imp_sus_true ; try solve [unfolds; simpl; eauto]; eauto).
    subst.
    change (Int.or ($ OS_STAT_POSTQ) ($ OS_STAT_SUSPEND)&ᵢInt.not ($ OS_STAT_POSTQ)) with ($ OS_STAT_SUSPEND).
    auto.
   }
   rewrite Heq_sus in *.
   rewrite negb_if in *.
    assert (Hegrp'_range: Int.unsigned pegrp' <= 255).
  {
    sep_lifts_trms_in Hsat (node (Vptr (eid_b, Int.zero))).
    unfold node at 1 in Hsat.
    sep normal in Hsat. sep destruct Hsat. sep split in Hsat.
    simpljoin1.
    clear -H75.
    simpl in H75.
    destruct H75 as (_ & _ & _ & H'). 
    destruct H' as (_ & _ & H' & _). 
    eapply int_true_le255; eauto.
  }

  eexists.
  exists (update_nth_val (Z.to_nat (Int.unsigned p1)) petbl' (Vint32 (x37&ᵢInt.not ($ 1<<ᵢp2)))).
  exists x1.
  exists (if sus
          then rtbl'
          else(update_nth_val (Z.to_nat (Int.unsigned p1)) rtbl'
               (Vint32 (Int.or x53 ($ 1<<ᵢp2))))).
  exists x10.
  exists pegrp'.
  exists ((htcb_addr, Int.zero) :: subwl).
  exists (V$ OS_STAT_POSTQ).
  sep eexists.
  sep auto.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg. 
  sep cancel AOSQBlk.
  unfold node in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  simpljoin1.
  (*inverts H91.*)
  inverts H94.
  (*sep cancel (Astruct (x22, Int.zero)).*)
  sep cancel (Astruct (x24, Int.zero)).
  unfold node.
  sep normal.
  exists x25.
  sep cancel (Astruct (x25, Int.zero)).
  sep split.
  2: { split; auto. }
  sep cancel tcbdllflag.
  sep cancel llsegevaux.

  assert (Hpegrp'_case: pegrp' = Int.zero \/ pegrp' <> Int.zero) by (clear; tauto).  
  destruct Hpegrp'_case as [Hpegrp'_eq | Hpegrp'_neq]; [left | right].
  (* case 1 : exit the loop after OS_EventTaskPostRdy *)  
  subst pegrp'.
  assert (Hpwls'_eq: remove_wls ((htcb_addr, Int.zero) :: subwl) pwl = nil). 
  {
    eapply Grp_eq_zero_imp_pwl_nil with
        (petbl:= (update_nth_val (Z.to_nat (Int.unsigned p1)) petbl'
                                (Vint32 (x37&ᵢInt.not ($ 1<<ᵢp2)))) ); eauto.  
    rewrite update_nth_val_len_eq; eauto.
    rewrite EcbMod.map_get_set.
    eauto. 
  }

  assert (Hsubwl_eq': set_tls_rdy0 ((htcb_addr,Int.zero) :: subwl) tcbls_wlrdy = set_tls_rdy0 pwl tcbls_wlrdy).  
  {
    assert (Heq: ((htcb_addr,Int.zero) :: subwl) ++ remove_wls ((htcb_addr, Int.zero) :: subwl) pwl
                 = ((htcb_addr,Int.zero) :: subwl)).
    rewrite Hpwls'_eq. rewrite app_nil_end; auto.
    rewrite <- Heq.
    eapply set_tls_rdy0_eq_alt_gen; eauto.
  }
  rewrite Hpwls'_eq in *.
  rewrite Hsubwl_eq' in *.
  splits; auto.
   (* case 2 : stay in the loop after OS_EventTaskPostRdy *)
  {
    split.
    -
      clear -Hpegrp'_neq. apply Int.eq_false; auto.
    -
      unfold is_subl.
      splits; auto.
      simpl length.
      eapply length_lt_succ; eauto.
      eapply Grp_eq_nz_imp_pwl_not_nil with
          (petbl:= (update_nth_val (Z.to_nat (Int.unsigned p1)) petbl'
                                   (Vint32 (x37&ᵢInt.not ($ 1<<ᵢp2)))) ); eauto.
      rewrite update_nth_val_len_eq; auto.
      rewrite EcbMod.map_get_set. eauto.
  }
  (* others left to prove *)
  splits; eauto.
  {
    clear -H86.
    unfolds in H86. auto. 
  }
  auto.
  rewrite Hp1 in *; rewrite Hp2 in *; eauto.
  rewrite Hp1 in *; rewrite Hp2 in *; eauto.
  auto.
  (* end of while loop with call to OS_EventTaskPostRdy *)
  unprotect HeqH2.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply sep_aconj_r_aisfalse_to_astar in Hsat; eauto.
  {
    introv Hs.
    clear Hsat.
    eapply uop_rv; eauto. 
    eapply bop_rv; eauto.
    sep get rv.
    sep split in Hs. simpljoin1.
    go.
    sep get rv.
    simpl; pure_auto.
    go.
    simpl; pure_auto.
    go. 
  }
  
  hoare_split_pure_all.
  rename H47 into Hinjor. simpl in Hinjor.
  destruct (Int.eq v'54 Int.zero) eqn: Hpegrpz;
  simpl in Hinjor; try change (Int.notbool Int.zero) with Int.one in Hinjor; destruct Hinjor; tryfalse.
  destruct H46 as [[_ Hrm_settls] | [Hf _]]; tryfalse.
  clear H47.
  destruct Hrm_settls as (Hrmnil & Hsettls).
  rewrite Hrmnil in *.
  rewrite Hsettls in *.
  clear Hrmnil Hsettls.
  eapply semacc_int_eq_true in Hpegrpz.
  simpljoin1.
  substs.

  (* fold AOSEvent in the pre-condition *) 
  fold_node.
  hoare_lifts_trms_pre (node (Vptr (eid_b, Int.zero)), Aarray v'50, Aarray v'52).
  eapply backward_rule1.
  introv Hsat.
  match goal with
    H: _ |= node ?levt ?evt _ ** _ ** _ ** ?Q |- _ =>
    instantiate (1 := AOSEvent levt evt etbl' v'9 ** Q) 
  end.
  unfold AOSEvent.
  sep normal. sep eexists.
  sep cancel (node (Vptr (eid_b, Int.zero))).
  unfold AOSEventTbl, AOSPostEventTbl.
  sep normal. sep eexists.
  sep cancel Aarray.
  sep cancel Aarray.
  sep pauto.
  eauto.
  go.
  eauto.
  go.
  (*  *)

  (* OS_EventRemoveDel (­ pevent ′­);ₛ *)
  hoare forward.
  sep cancel evsllseg.
  sep cancel AOSEvent.
  sep cancel p_local.
  eauto.
  go.
  go.
  introv Hsat. sep auto.
  introv Hsat. sep auto.
  
  (* unfold post-condition of OS_EventRemove *)
  hoare unfold pre.
  rename v'84 into eid_b. 
  inverts H52. (* eq. for logic_val ... *)

  (* pq ′ =ₑ pevent ′ → OSEventPtr;ₛ *)
  hoare forward.
  go.

  (* pqblk ′ =ₑ pq ′ → qfreeblk;ₛ *)
  hoare forward. 
  go.

  (* pqblk ′ → nextblk =ₑ OSQFreeBlk ′;ₛ *)
  hoare unfold pre.
  hoare forward.
  { (* match v'5 with ... = true *)
    destruct H44. (* isptr v'5 *)
    subst. auto.
    simpljoin1.
  }

  (* OSQFreeBlk ′ =ₑ pq ′ → qfreeblk;ₛ *)
  hoare unfold pre.
  hoare forward. 
  go.

  (* pq ′ → OSQPtr =ₑ OSQFreeList ′;ₛ *)
  hoare unfold pre.
  hoare forward.
  { (* match v'12 with ... = true *)
    destruct H52. (* isptr v'12 *)
    subst. auto.
    simpljoin1.
  }

  (* OSQFreeList ′ =ₑ pq ′;ₛ *)
  hoare forward.
  
  (* pevent ′ → OSEventType =ₑ ′ OS_EVENT_TYPE_UNUSED;ₛ *)
  hoare forward.

  (* pevent ′ → OSEventListPtr =ₑ OSEventFreeList ′;ₛ *)
  hoare unfold pre. 
  hoare forward. 
  pure_auto. 

  (* OSEventFreeList ′ =ₑ pevent ′;ₛ *)
  hoare forward.

  (* fold AOSTCBList *)
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (OSTCBList, tcbdllseg tcb_head, OSTCBCur, tcbdllseg (Vptr ct)).
  match goal with
    H: _ |= GV OSTCBList @ OS_TCB ∗ |-> ?p1 **
                tcbdllseg ?p1 _ _ (Vptr ct) ?l1 **
                GV OSTCBCur @ OS_TCB ∗ |-r-> (Vptr ct) **
                tcbdllseg (Vptr ct) _ _ _ ?l2 ** ?Q |- _ =>
      instantiate (1:=AOSTCBList p1 (Vptr ct) l1 l2 v'11 ct (set_tls_rdy0 pwl tcbls_wlrdy) ** Q)
  end.
  unfold AOSTCBList.
  sep pauto.
  eauto.
  eauto.
  eauto.
  (* end of fold AOSTCBList *)

  hoare_lifts_trms_pre (llsegevaux, AOSTCBList, p_local).
  eapply backward_rule1. 
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto. 
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.

  assert (Hjomg: join els1 mqls' (merge els1 mqls')).
  {
    apply join_merge_disj.
    apply disj_sym.
    apply EcbMod.join_comm in Hjo.
    clear -Hjo Hjo'. 
    eapply join_join_disj_r; eauto. 
  }

  assert (H_elp_new:
            ECBList_P v'71 Vnull (v'69++v'38) (v'67++v'42) (merge els1 mqls') (set_tls_rdy0 pwl tcbls_wlrdy)).
  {
    casetac v'68 (nil: list os_inv.EventCtr) Hnil Hnnil.
    - lets H00: H55 Hnil.
      destruct H00 as (Heid & Heq' & Hnil').
      subst x3. subst v'70. subst v'69. subst v'68.
      assert (v'67 = nil /\ els1 = emp).
      { unfold ECBList_P in H50. simpljoin1. splits; auto. }
      simpljoin1.
      simpl app.
      rewrite jl_merge_emp'.
      auto.
    -
    lets H00: H72 Hnnil. 
    destruct H00 as (Hv'eq & Hglp & Hupd).
    subst v'71.
    eapply ecb_list_join_join; eauto.
    apply EcbMod.join_comm.
    clear -Hjomg. auto. 
  }

  assert (Hjo_rm: join (merge els10 mqls'_) (sig (eid_b, Int.zero) (absmsgq msgs maxlen pwl, wl)) els).
  {
    clear - Hjo_ Hjo'_.
    apply join_comm in Hjo'_.
    eapply join_lib_aux.join_join_join_merge; eauto. 
  }
  assert (Hjo_rm': join (merge els1 mqls') (sig (eid_b, Int.zero) (absmsgq msgs maxlen pwl, nil)) els_wlrdy). 
  {
    clear - Hjo Hjo'.
    apply join_comm in Hjo'.
    eapply join_lib_aux.join_join_join_merge; eauto. 
  }
  assert (Hmgeq: merge els1 mqls' = merge els10 mqls'_).
  {
    unprotect Heqels_wlrdy.
    subst els_wlrdy.
    apply join_set_r with (a:=(eid_b,Int.zero)) (b:=(absmsgq msgs maxlen pwl, wl)) in Hjo_rm'.
    rewrite set_sig in Hjo_rm'.
    Require Import join_prop.
    rewrite <- set_set_eq in Hjo_rm'.
    apply join_comm in Hjo_rm.
    apply join_comm in Hjo_rm'.
    assert (Hsetsame: set els (eid_b, Int.zero) (absmsgq msgs maxlen pwl, wl) = els).
    { eapply get_set_same; eauto. }
    rewrite <- Hsetsame in Hjo_rm.
    eapply map_join_cancel. clear -Hjo_rm'. eauto. auto. eauto.
    unfold indom. eexists. rewrite get_a_sig_a; eauto.
  }

  (* fold evaux_node *)
  fold_evaux_q Vnull.
  (* folding of llsegevaux completed *) 

  assert (Hcs:
            (Int.eq i0 Int.zero = false \/ Int.eq i Int.zero = false) \/
            (Int.eq i0 Int.zero = true /\ Int.eq i Int.zero = true)).
  {
    destruct (Int.eq i0 Int.zero); destruct (Int.eq i Int.zero); auto. 
  }
  destruct Hcs as [Hwt | Hnwt].

  (* there existed tasks waiting for the queue *) 
  assert (Hwlpwl: wl <> nil \/ pwl <> nil).  
  {
    destruct Hwt as [Hwt | Hwt].
    lets H00: ecb_wt_ex_prop Hwt H26 H16 H23 H19.
    lets H00': H00 Hecbl1_ Hecbetbl_ H. clear H00. 
    simpljoin1.
    unfold get, EcbMap in Hgetmq_.
    rewrite Hgetmq_ in H87.
    inverts H87.
    left. auto.
    lets H00: ecb_wt_ex_pwl_prop Hwt H34 Hmtpetbl Hlenpetbl H22.
    lets H00': H00 Hecbl1_ Hecbpetbl_ H. clear H00.
    simpljoin1.
    unfold get, EcbMap in Hgetmq_.
    rewrite Hgetmq_ in H87.
    inverts H87.
    right. auto.
  }
  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, curtid, evptr).
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply absinfer_qdel_succ_ex_wait; eauto.
  go. unfold CurTid. go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL;ₛ *)
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop  ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).

  hoare forward prim.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (evsllseg v'71, evsllseg x3).
  apply evsllseg_app in Hsat.
  unfold EvtInv.
  unfold AECBList.
  unfold AOSEventFreeList.
  unfold AOSQFreeList.
  unfold AOSQFreeBlk.
  unfold tcbllsegevaux.
  sep normal.
  sep eexists.
  trycancel_EvtInv.
  sep cancel Aier.
  sep cancel tcbdllflag.
  sep pauto.
  sep cancel evsllseg.
  sep cancel APthreadAttr.
  unfold qblkf_sll.
  unfold os_inv.sll.
  unfold ecbf_sll.
  instantiate (12:=(v'8 :: x18 :: nil) :: v'29).
  instantiate (11:= (v'9 :: x15 :: x9 :: x10 :: x11 :: Vint32 i6 :: Vint32 i5 :: Vptr (v'87, Int.zero) :: nil) :: v'28).
  instantiate (10:=(V$ OS_EVENT_TYPE_UNUSED
                     :: Vint32 Int.zero :: Vint32 i7 :: Vptr (v'85, Int.zero) :: x1 :: v'5 :: Vint32 Int.zero :: x6 :: nil) :: v'26).
  unfold qblkf_sllseg; fold qblkf_sllseg.
  unfold node.
  unfold_sll.
  unfold_ecbfsll.
  sep normal.
  sep eexists.
  sep cancel ecbf_sllseg.
  sep cancel sllseg.
  sep cancel qblkf_sllseg.
  sep split; eauto.
  sep cancel OS_EVENT_TYPE_UNUSED.
  sep cancel OS_EVENT_TBL_SIZE.
  sep cancel OS_MAX_Q_SIZE.
  sep cancel Astruct.
  sep cancel Astruct.
  unfold AOSPostEventTbl in Hsat.
  sep cancel Aarray.
  sep cancel CapabilityInv.
  sep_lifts_trms_in Hsat ASemEIBs.
  eapply asemeib_del_q_preserve; eauto.
  sep cancel ASemEIBs.
  2: { unfold eib_ref in Hnref. introv Hsr; apply Hnref. auto. }
  sep_lifts_trms_in Hsat AMuxEIBs.
  eapply amuxeib_del_q_preserve; eauto.
  sep cancel AMuxEIBs.
  2: { unfold eib_ref in Hnref. introv Hmr; apply Hnref. auto. }
  eapply amqeib_del_q_preserve; eauto.
  sep cancel AMqEIBs.
  2: { unfold eib_ref in Hnref. introv Hsr; apply Hnref. auto. }
  cancel_corecommuinv.
  unfold p_local, LINV, OSLInv.
  sep pauto.
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)
  
  splits; eauto.
  splits; auto. go.
  splits; auto. go.
  splits; auto. go.
  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto.
  eapply mq_ecb_p_qdel_preserve; eauto.
  eapply mux_ecb_p_qdel_preserve; eauto.
  eapply sem_ecb_p_qdel_preserve; eauto.
  rewrite <- Hmgeq. auto.
  {  unfold RH_CurTCB.
    unprotect Heqtcbls_wlrdy.
    rename H0 into Hct.
    unfolds in Hct.
    destruct Hct as (p_ & st_ & msg_ & sus_ & Hgetct).
    lets H00: set_tls_rdy_get_some Hgetct.
    instantiate (1:=wl) in H00.
    destruct H00 as (st'_ & m'_ & Hgetct').
    apply set_tls_rdy0_get_some with (wls:=pwl) in Hgetct'.
    simpljoin1; do 3 eexists; eauto. 
  }
   { (* RH_TCBList_ECBList_P *)
    assert (Hjo00:
        join (merge els10 mqls'_) (sig (eid_b, Int.zero) (absmsgq msgs maxlen nil, nil))
          (set els_wlrdy (eid_b, Int.zero) (absmsgq msgs maxlen nil, nil))).
    {
      unprotect Heqels_wlrdy.
      rewrite Heqels_wlrdy.
      rewrite <- set_set_eq.
      apply join_set_r with (a:=(eid_b, Int.zero)) (b:=(absmsgq msgs maxlen nil, nil)) in Hjo_rm.
      clear -Hjo_rm.
      rewrite set_sig in Hjo_rm.
      auto. eauto.
      unfold indom. eexists. rewrite get_a_sig_a; eauto.
    }
    clear -Hjo00 H42.
    eapply ecb_del_prop_RHhold; eauto.
  }

  pure_auto. (* GoodFrm *)

  assert (Hnzor: v'14 = V$1 \/ v'27 = V$1).
  {
    clear -Hcond1 Hcond2 Hwt. 
    destruct Hwt as [Hnz | Hnz].
    left. destruct Hcond1. simpljoin1. rewrite Hnz in H. simpljoin1; tryfalse.
    right. destruct Hcond2. simpljoin1. rewrite Hnz in H. simpljoin1; tryfalse.
  }
  hoare forward.
  destruct Hcond1; simpljoin1; pure_auto. 
  destruct Hcond1; simpljoin1; pure_auto. 
  destruct Hcond2; simpljoin1; pure_auto.
  destruct Hcond2; simpljoin1; pure_auto.
  destruct Hcond1; destruct Hcond2; simpljoin1; pure_auto. 
  hoare_split_pure_all.
  rename H87 into Hinjand. clear Hinjand. 

  (* OS_Sched (­) *)
  hoare forward.
  go.
  introv Hsat.
  sep destruct Hsat.
  eexists.
  sep cancel p_local.
  simpl; auto.
  introv Hsat.
  sep destruct Hsat.
  eexists.
  sep cancel p_local.
  simpl;auto.

  eapply backward_rule1.
  introv Hsat.
  destruct Hsat as [Hs | Hs].
  2: {
     destruct Hnzor; subst;
     destruct Hcond1; destruct Hcond2; simpljoin;
     tryfalse;
     simpl val_eq in Hs;
     change (Int.eq ($ 1) ($ 1)) with true in Hs;
     simpl val_inj in Hs;
     try change (Int.ltu Int.one Int.zero) with false in Hs;
     try change (Int.ltu Int.zero Int.one) with true in Hs;
     sep_lifts_trms_in Hs val_inj;
     simpl val_inj in Hs;
     apply sep_pure_split in Hs;
     destruct Hs as (Hif & Hs);
     destruct Hif as [Hif1 | Hif2]; tryfalse.
  }
  eauto.
  hoare unfold.
  unfold getasrt. 
  unfold OS_SchedPost.
  unfold OS_SchedPost'.
  hoare unfold.
  inverts H54.

  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_qdel_ret.
  go.
  eapply absinfer_eq.

  (* return *)
  eapply rete_rule.
  introv Hsat.
  split.
  sep normal.
  sep eexists.
  sep cancel Aier.
  trycancel.
  sep pauto.
  eapply cast_rv_tnull.
  eapply null_rv.
  go.

  (******* there existed no task waiting for the queue *******)
  destruct Hnwt as (Hnwt1 & Hnwt2).
  assert (wl = (nil: list tid)).
  { eapply rlh_ecb_nowait_prop with (v'40:=etbl) (pwl:=pwl) (x3:=wl); eauto. }
  subst wl.
  assert (pwl = (nil: list tid)).
  { eapply rlh_ecb_nowait_pwl_prop with (v'41:=petbl) (pwl:=pwl) (x3:=nil); eauto. }
  subst pwl.
  
  hoare_lifts_trms_pre (Aop, absecblsid, curtid, evptr). 
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply absinfer_qdel_succ_nex_wait; eauto. 
  go. unfold CurTid. go.
  eapply absinfer_eq.

  assert (tcbls_wlrdy = tcbls).
  {
    unprotect Heqtcbls_wlrdy.
    rewrite Heqtcbls_wlrdy.
    rewrite set_tls_rdy_nil; auto. 
  }
  subst tcbls_wlrdy.
  rewrite set_tls_rdy0_nil in *.

  (* TODO: exit from crit. sect. *)
  hoare_lifts_trms_pre (Aisr, Ais, Aier).
  transform_pre add_aemp_isr_is_prop  ltac:(sep cancel Aisr; sep cancel Ais; sep cancel Aier).

  hoare forward prim.
  get_hsat Hsat.
  sep_lifts_trms_in Hsat (evsllseg v'71, evsllseg x3).
  sep cancel APthreadAttr.
  apply evsllseg_app in Hsat.
  unfold EvtInv.
  unfold AECBList.
  unfold AOSEventFreeList.
  unfold AOSQFreeList.
  unfold AOSQFreeBlk.
  unfold tcbllsegevaux.
  sep normal.
  sep eexists.
  trycancel_EvtInv.
  sep cancel Aier.
  sep cancel tcbdllflag.
  sep pauto.
  sep cancel evsllseg.
  unfold qblkf_sll.
  unfold os_inv.sll.
  unfold ecbf_sll.
  instantiate (12:=(v'8 :: x18 :: nil) :: v'29).
  instantiate (11:= (v'9 :: x15 :: x9 :: x10 :: x11 :: Vint32 i6 :: Vint32 i5 :: Vptr (v'87, Int.zero) :: nil) :: v'28).
  instantiate (10:=(V$ OS_EVENT_TYPE_UNUSED
                     :: Vint32 Int.zero :: Vint32 i7 :: Vptr (v'85, Int.zero) :: x1 :: v'5 :: Vint32 Int.zero :: x6 :: nil) :: v'26).
  unfold qblkf_sllseg; fold qblkf_sllseg.
  unfold node.
  unfold_sll.
  unfold_ecbfsll.
  sep normal.
  sep eexists.
  sep cancel ecbf_sllseg.
  sep cancel sllseg.
  sep cancel qblkf_sllseg.
  sep split; eauto.
  sep cancel OS_EVENT_TYPE_UNUSED.
  sep cancel OS_EVENT_TBL_SIZE.
  sep cancel OS_MAX_Q_SIZE.
  sep cancel Astruct.
  sep cancel Astruct.
  sep cancel CapabilityInv.
  unfold AOSPostEventTbl in Hsat.
  sep cancel Aarray.
  sep_lifts_trms_in Hsat ASemEIBs.
  eapply asemeib_del_q_preserve; eauto.
  sep cancel ASemEIBs.
  2: { unfold eib_ref in Hnref. introv Hsr; apply Hnref. auto. }
  sep_lifts_trms_in Hsat AMuxEIBs.
  eapply amuxeib_del_q_preserve; eauto.
  sep cancel AMuxEIBs.
  2: { unfold eib_ref in Hnref. introv Hmr; apply Hnref. auto. }
  eapply amqeib_del_q_preserve; eauto.
  sep cancel AMqEIBs.
  2: { unfold eib_ref in Hnref. introv Hsr; apply Hnref. auto. }
  cancel_corecommuinv.
  unfold p_local, LINV, OSLInv.
  sep pauto.
  cancel_partitioninv.
  eauto.
  splits; eauto.
  splits; auto. go.
  splits; auto. go.
  splits; auto. go.
  eapply evdel_nodup_set_null3_preserve; eauto.
  eapply evcre_nodup_set_null3_preserve; eauto.
  eapply mq_ecb_p_qdel_preserve; eauto.
  eapply mux_ecb_p_qdel_preserve; eauto.
  eapply sem_ecb_p_qdel_preserve; eauto.
  rewrite <- Hmgeq. auto.
   { (* RH_TCBList_ECBList_P *)
    assert (Hjo00:
        join (merge els10 mqls'_) (sig (eid_b, Int.zero) (absmsgq msgs maxlen nil, nil))
          (set els_wlrdy (eid_b, Int.zero) (absmsgq msgs maxlen nil, nil))).
    {
      unprotect Heqels_wlrdy.
      rewrite Heqels_wlrdy.
      rewrite <- set_set_eq.
      apply join_set_r with (a:=(eid_b, Int.zero)) (b:=(absmsgq msgs maxlen nil, nil)) in Hjo_rm.
      clear -Hjo_rm.
      rewrite set_sig in Hjo_rm.
      auto. eauto.
      unfold indom. eexists. rewrite get_a_sig_a; eauto.
    }
    clear -Hjo00 H42.
    eapply ecb_del_prop_RHhold; eauto.
  }

  pure_auto. (* GoodFrm *)

  assert (Hz1: v'14 = Vint32 Int.zero).
  {
    clear - Hcond1 Hnwt1. 
    destruct Hcond1; simpljoin1.
    rewrite H in Hnwt1. tryfalse. 
  }
  assert (Hz2: v'27 = Vint32 Int.zero).
  {
    clear - Hcond2 Hnwt2. 
    destruct Hcond2; simpljoin1.
    rewrite H in Hnwt2. tryfalse. 
  }
  subst v'14. subst v'27.
  hoare forward.
  hoare unfold.
  rename H87 into Hf.
  match type of Hf with ?t <> _ => change t with (Vint32 Int.zero) in Hf end.
  clear -Hf. tryfalse. 
  instantiate (1:=Afalse).
  apply hoare_disj_afalseP_l_pre.

  hoare unfold.
  rename H87 into Hinjor. clear Hinjor.

  hoare_lifts_trms_pre Aop. 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_qdel_ret.
  go.
  eapply absinfer_eq.

  (* return *)
  eapply rete_rule.
  introv Hsat.
  split.
  sep normal.
  sep eexists.
  sep cancel Aier.
  trycancel.
  sep pauto.
  eapply cast_rv_tnull.
  eapply null_rv. 
  go.

  Unshelve.
  trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. trivial. 

Qed.

