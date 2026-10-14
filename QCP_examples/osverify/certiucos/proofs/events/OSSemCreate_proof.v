Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.

Require Import abs_step.
Require Import abs_infer_abt.
Require Import sem_common.
Require Import evtinv_lemmas.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(*********************** sem cre **************************************)

Lemma semcre_absimp_iserr:
  forall P n sch s,
    can_change_aop P ->
    absinfer sch
             ( <|| semcre (Vint32 n :: Vnull :: nil) ;; s ||> ** P)
             (<|| s ||> ** P).
Proof.
  intros.
  eapply absinfer_trans; try (eapply absinfer_seq_end; auto); eauto.
  eapply absinfer_seq; eauto.
  infer_solver 0%nat.
Qed.

Lemma semcre_absimp_iserr_abt:
  forall P n sch s rv,
    can_change_aop P ->
    rv <> Vnull ->
    absinfer sch
             ( <|| semcre (Vint32 n :: rv :: nil) ;; s ||> ** P)
             (<|| ABORT ||> ** P).
Proof.
  intros.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; auto); eauto.
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try (eapply absinfer_choice1; auto); eauto.
   eapply absinfer_abt; auto.
  absimp_abt_solver.
Qed.

Lemma semcre_absimp_no_free:
  forall P n sch s ct locmp locmp',
    can_change_aop P ->
    (Z.leb (Int.unsigned n) Int16.max_unsigned) = true ->
    locmp' = set locmp ct (Vint32 (Int.repr __EvLoc_ecbcre1)) -> 
    absinfer sch
             ( <|| semcre (Vint32 n :: Vnull :: nil) ;; s ||> ** HEvLoc locmp ** HCurTCB ct ** P)
             (<|| s ||> ** HEvLoc locmp' ** HCurTCB ct ** P).
Proof.
    intros.
  assert (Hc: forall locmp, can_change_aop (HEvLoc locmp ** HCurTCB ct ** P)) 
    by (intros; can_change_aop_solver).
  (eapply absinfer_trans; try (eapply absinfer_seq_end; auto); eauto).
  eapply absinfer_seq; eauto.
  infer_solver 1%nat.
Qed.

Lemma semcre_absimp_no_free_abt:
  forall P n sch v' s locmp ct,
    can_change_aop P ->
    (Z.leb (Int.unsigned n) Int16.max_unsigned) = true ->
    v' <> Vnull ->
    absinfer sch
             ( <|| semcre (Vint32 n :: v' :: nil) ;; s ||> ** HEvLoc locmp ** HCurTCB ct ** P)
             ( <|| ABORT ||> ** HEvLoc locmp ** HCurTCB ct ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HEvLoc locmp ** HCurTCB ct ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
  eapply absinfer_abt; eauto.
  absimp_abt_solver;
  instantiate (3:=semcre_no_free (|Vint32 n :: v' :: nil|));
  instantiate (3:=s0);
  sep pauto.
Qed.

Lemma absinfer_seq1:
  forall (p : asrt) (s1 : absop)  (s2 : spec_code) (s1' : absop) (sc : ossched),
                   can_change_aop p ->
                   sc ⊢  <|| s1 ||>  ** p ⇒  <|| s1' ||>  ** p ->
                   sc ⊢  <|| s1;; s2 ||>  ** p ⇒  <|| s1';; s2 ||>  ** p.
Proof.
intros.
eapply absinfer_seq; try eauto.
Qed.

Lemma semcre_absimp_ecb_avail:
  forall P sch s n els  sid locmp locmp' ptrmp ptrmp' ct muxp semp qp, 
    can_change_aop P ->
    get els sid = None ->
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre1)) ->
    get ptrmp ct = Some (muxp, semp, qp) ->
    ptrmp' = set ptrmp ct (muxp, Vptr sid, qp) ->
    absinfer sch
             (<|| semcre(Vint32 n :: Vptr sid :: nil) ;; s ||> 
                ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| semcre_ecb_activate (|Vint32 n :: Vptr sid :: nil|) ;; s ||> 
                ** HECBList els ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).  
Proof. 
  introv Hcp Hget Hlmp' Hgtp Hpmp'.
  eapply absinfer_trans.
  unfold semcre.
  eapply absinfer_seq1.
  can_change_aop_solver.
  eapply absinfer_choice2; can_change_aop_solver.
  intros. auto.
  eapply absinfer_seq.
  can_change_aop_solver.
  can_change_aop_solver.
  infer_solver 1%nat.
Qed.

Lemma semcre_absimp_ecb_avail_abt:
  forall P sch s n els sid v' locmp locmp' ptrmp ptrmp' ct muxp semp qp, 
    can_change_aop P ->
    get els sid = None ->
    v' <> Vptr sid -> 
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre1)) ->
    get ptrmp ct = Some (muxp, semp, qp) ->
    ptrmp' = set ptrmp ct (muxp, Vptr sid, qp) ->
    absinfer sch
             (<|| semcre(Vint32 n :: v' :: nil) ;; s ||> 
                ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| ABORT ||> 
                ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P).
Proof.
    intros.
  assert (Hc:
                  can_change_aop (HECBList els ** 
                                                       HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P))
  by (can_change_aop_solver).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver;
  try instantiate (3:= s0);
  try instantiate (4:= s0);
  try instantiate (2:= semcre_ecb_available (| v' :: nil|));
  try instantiate (3:= semcre_ecb_available (| v':: nil|));
  sep pauto.
Qed.

Lemma semcre_absimp_ecb_avail_abt2:
  forall P sch s n els sid v' locmp locmp' ptrmp ptrmp' ct muxp semp qp, 
    can_change_aop P ->
    get els sid = None ->
    (exists t', tsk_normal_ev locmp ptrmp t' sid) -> 
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre1)) ->
    get ptrmp ct = Some (muxp, semp, qp) ->
    ptrmp' = set ptrmp ct (muxp, Vptr sid, qp) ->
    absinfer sch
             (<|| semcre(Vint32 n :: v' :: nil) ;; s ||> 
                ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| ABORT ||> 
                ** HECBList els ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P).
Proof.
    intros.
  assert (Hc:
                  can_change_aop (HECBList els ** 
                                                       HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P))
  by (can_change_aop_solver).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; eauto)).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver;
  try instantiate (3:= s0);
  try instantiate (4:= s0);
  try instantiate (2:= semcre_ecb_available (| v' :: nil|));
  try instantiate (3:= semcre_ecb_available (| v':: nil|));
  sep pauto.
Qed.  

Lemma semcre_absimp_ecb_activate: 
  forall sch n sid s locmp locmp' ct P els els',       
    can_change_aop P ->
    (Int.unsigned n <=? Int16.max_unsigned) = true -> 
    get els sid = None -> 
    els' = (set els sid (abssem n, nil)) -> 
    locmp' = set locmp ct (Vint32 ($__EvLoc_ecbcre2)) ->
    absinfer sch
             (<|| semcre_ecb_activate (|Vint32 n :: Vptr sid :: nil|);; s ||> ** HECBList els **  HEvLoc locmp ** HCurTCB ct ** P)
             (<|| s ||> ** HECBList els' ** HEvLoc locmp' ** HCurTCB ct ** P).  
Proof.
  introv Hcop Hrgn Hnone Hels' Hlmp'.
  subst els'. subst locmp'.
  infer_solver 0%nat.
Qed.  

(* new in OSSemCreateProof.v *)

Require Import sem_corecommu.
Require Import sem_common.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
  
Require Import hoare_forward.
Require Import inv_prop.

Require Import gjb_common.
Require Import gjb_sem_common.
Require Import freeevtlist_lemmas.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.

Local Open Scope code_scope.

Open Scope code_scope.

Lemma OSSemCreate_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal OSSemCreate vl logicl OSSemCreatePre ct->
    Some r =
    BuildRetI os_internal OSSemCreate vl logicl OSSemCreatePost ct->
    exists t d1 d2 s,
      os_internal OSSemCreate = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'1 into vsid.
  change ((Vint32 i :: nil) ++ (vsid :: nil)) with (Vint32 i :: vsid :: nil).
  subst logicl. 

  (* OSIntNesting *)
   hoare forward prim.
   (* splits;intros;auto.
   splits;auto. *)
  unfold AGVars.
  hoare unfold.
  hoare forward.
  pure_auto.
  hoare unfold.
  assert (Hvret: vsid =Vnull \/ vsid <> Vnull) by tauto. 
   destruct Hvret.
   2: { hoare abscsq.
           apply noabs_oslinv.
           eapply semcre_absimp_iserr_abt; eauto.
           pure_auto.
           can_change_aop_solver.
           eapply absabort_rule.
         } 
  subst.
  hoare abscsq.
  apply noabs_oslinv.
  eapply semcre_absimp_iserr; eauto.
  pure_auto.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  pure_auto.
  pure_auto.
  hoare forward.
  splits;eauto.
  unfold isptr; eauto.
  (*  end of retrun Vnull *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare forward prim.
  unfold AGVars.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep pauto.
  pure_auto.
  pure_auto.
  clear -H1.
  (* end add *)

  hoare forward prim; pure_auto.
  unfold EvtInv.
  hoare unfold.

  rename v'18 into vcspace.
  rename v'19 into v19. 
  rename v'20 into v20. 
  rename v'21 into v21. 

  rename v'22 into v'18. 
  rename v'23 into v'19. 
  rename v'24 into v'20. 
  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 
  rename v'37 into v'33. 
  rename v'38 into v'34. 
  rename v'39 into v'35. 
  rename v'40 into v'36. 
  
  hoare forward; pure_auto.

  destruct v'19; hoare unfold.
  
(***************************** OSEventFreeList = Null **************************)
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.one) <> Vint32 Int.zero /\
         Vint32 (Int.notbool Int.one) <> Vnull /\
         Vint32 (Int.notbool Int.one) <> Vundef |- _ =>
      destruct H as (H & _);
      unfold Int.notbool in H;
      rewrite Int.eq_false in H; eauto;
      tryfalse
    | _ => idtac
  end.

  assert (Hvret: vsid =Vnull \/ vsid <> Vnull) by tauto. 
  destruct Hvret. 
  {
  subst.
  (* vsid =Vnull  *)
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (Aop, Aabsdata evlocid, Aabsdata curtid).
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply semcre_absimp_no_free; pure_auto.
  eapply absinfer_eq.
  
  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local).
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.
  hoare_assign_evaux.
  unfold isevloc; auto.

  rename v'35 into locmp.
  rename v'36 into ptrmp.
  assert (Hnull: get ptrmp ct = Some (Vnull, Vnull, Vnull)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  (* preparation for EXIT_CRITICAL;ₛ *) 
   fold_evaux_sem_loc (V$ __EvLoc_ecbcre1) Vnull.
  lets Heq: EvAuxPtrMod.get_set_same Hnull.
  rewrite Heq.
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part1.
  sep cancel AOSQFreeList. sep cancel AOSQFreeBlk. sep cancel AECBList.
  sep cancel (Aabsdata absecblsid).
  sep pauto. 
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part2. eauto. eauto.
  instantiate ( 8:= (set locmp ct (V$ __EvLoc_ecbcre1))).
  eapply semecb_semnull_preserve; eauto.
  eapply muxecb_semnull_preserve; eauto.
  eapply qecb_semnull_preserve; eauto.
  eapply cre_nodup_null_cre1_preserve; eauto.
  eapply del_nodup_null_cre1_preserve; eauto.
  eauto.
  unfold AOSEventFreeList.
  unfold tcbllsegevaux. 
  sep pauto.
  unfold ecbf_sll. unfold ecbf_sllseg. sep split; auto.
  sep cancel ASemEIBs. sep cancel AMuxEIBs. sep cancel AMqEIBs.
  sep cancel llsegevaux.
  sep pauto.
  
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm.
  sep cancel EvtInv_part1.
  sep cancel EvtInv_part2. sep pauto.
  (* EXIT_CRITICAL;ₛ *) 
  hoare forward prim.
  sep cancel Aier.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep normal.
  sep eexists.
  sep split; eauto.
  sep cancel CurTid.
  sep cancel flag_off.
  try_cancel_evaux_asst.
  sep cancel CoreCommuInv.
  sep cancel PartitionInv.
  eauto.
  3:eauto.
  splits; eauto.
  unfold isevloc. pure_auto.
  pure_auto.
  pure_auto.
  
  (* If (pevent ′ !=ₑ NULL) *) 
  lzh_hoare_if. 
  change (Int.notbool Int.one) with Int.zero in LHift_true.
  destruct LHift_true. tryfalse.
  instantiate (1:= Afalse).
  eapply pfalse_rule.
  hoare forward.
  }

  (* opv <>Vnull  *)
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (Aop, Aabsdata evlocid, Aabsdata curtid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semcre_absimp_no_free_abt; pure_auto.
  eapply absinfer_eq.
  eapply absabort_rule.
  
(***************************** OSEventFreeList <> Null **************************)
  rename v'41 into pevent_block. 
  rename v'37 into pevent_event_tbl.
  rename v'39 into pevent_event_ptbl.
  rename v'40 into petbl.

  pure intro.
  hoare_assert_pure (EcbMod.get v'10 (pevent_block, Int.zero) = None). 
  {
    get_hsat Hsat. 
    unfold AECBList in Hsat.
    sep normal in Hsat.
    destruct Hsat.
    get_hsat Hsat.
    sep split in Hsat.
    eapply semcre_ecblist_star_not_inh; eauto.
    instantiate (3:= s0).
    sep pauto.
  }
  hoare_split_pure_all.
  rename H11 into Hnone.  (* EcbMod.get v'14 (pevent_block, Int.zero) = None *)

  hoare_assert_pure (notIncoreSemQ (pevent_block, Int.zero)).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat (CoreCommuInv).
     unfold CoreCommuInv,DynamicRefactorINV in *.
     sep normal in Hsat.
     sep destruct Hsat.
     sep split in Hsat.
     unfold notIncoreSemQ.
     clear -H11 H14 H25 Hnone.
     funfold H25.
     unfold is_que,is_sem in *.
     unfold get in *. unfold EcbMap in *.
     splits; introv Hf; try rewrite Hf in *; try  eapply H in Hf; try  eapply H0 in Hf;
     try rewrite Hnone in *; simpljoin; tryfalse.
   }
  hoare_split_pure_all.
  rename H11 into Hcre_nincore.

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local).
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  assert (Hnull: get v'36 ct = Some (Vnull, Vnull, Vnull)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  assert (Hvsid: vsid = Vptr (pevent_block, Int.zero) \/ vsid <> Vptr (pevent_block, Int.zero)) by tauto. 
  destruct Hvsid.
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, evlocid, evptrid, curtid). 
    eapply abscsq_rule. 
    apply noabs_oslinv.
    eapply semcre_absimp_ecb_avail_abt; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  assert (Hncre1: ~(exists t, tsk_loc_ev v'35 v'36 t __EvLoc_ecbcre1 (pevent_block, Int.zero))).
  {
    match goal with
      H: SEM_ECB_P _ _ _ _ (?v :: ?vl) _ _ _ |- _ => remember v as hv; remember vl as tvl
    end.
    assert (Hptrin: ptr_in_ecblist (Vptr (pevent_block, Int.zero)) (Vptr (pevent_block, Int.zero)) (hv :: tvl)).
    {
      unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
      asserts_rewrite (beq_pos pevent_block pevent_block = true).
      {
        rewrite beq_pos_Pos_eqb_eq. 
        apply Pos.eqb_refl.
      }
      change (Int.eq Int.zero Int.zero) with true.
      simpl. auto.
    }
     eapply ptr_in_freelist_notcre1; eauto. 
  }
  assert (Hv: pevent_event_tbl = (pevent_block, Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))) by
      (simpl in H12; inverts H12; auto).
  rewrite Hv.
 assert (Hv': pevent_event_ptbl = (pevent_block, Int.zero +ᵢ  ($ 1 +ᵢ  ($ 4 +ᵢ ($ 8 +ᵢ ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))))))  by
      (simpl in H13; inverts H13; auto).
  rewrite Hv'.
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.zero) = Vint32 Int.zero \/
         Vint32 (Int.notbool Int.zero) = Vnull |- _ =>
      unfold Int.notbool in H; simpl in H;
      rewrite Int.eq_true in H; auto;
      destruct H; tryfalse
    | _ => idtac
  end.
  hoare forward; pure_auto.

  clear Hif_true.
  subst vsid.

  assert (Hnormal:
            (~(exists t, tsk_normal_ev v'35 v'36 t (pevent_block, Int.zero))) \/
            (exists t, tsk_normal_ev v'35 v'36 t (pevent_block, Int.zero))) by tauto.
  destruct Hnormal as [Hnml | Hnnml].
  2: {
    hoare_lifts_trms_pre (Aop, absecblsid, evlocid, evptrid, curtid).
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply semcre_absimp_ecb_avail_abt2; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }

  hoare normal pre. hoare_ex_intro.  
  hoare_lifts_trms_pre (Aop, absecblsid, evlocid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply semcre_absimp_ecb_avail; pure_auto.
  eapply absinfer_eq.

  hoare_assign_evaux.
  hoare_assign_evaux.
  unfold isevloc; auto.

  (* prepare for EXIT_CRITICAL;ₛ *)
   fold_evaux_sem_loc (V$ __EvLoc_ecbcre1) (Vptr (pevent_block, Int.zero)).

  assert (Hncre2: ~exists t, tsk_loc_ev v'35 v'36 t __EvLoc_ecbcre2 (pevent_block, Int.zero)). 
  {
    eapply not_in_els_notcre2; eauto. 
  }

  hoare_assert_pure (isptr v'13).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat ecbf_sllseg.
    lets H00: isptr_ecbf_sllseg_frm Hsat.
    auto.
  }
  hoare_split_pure_all.
  hoare_assert_pure (~ptr_in_ecblist (Vptr (pevent_block, Int.zero)) v'13 v'19).
  {
    match goal with H: isptr _ |- _ => rename H into Hisptr end.
    unfold isptr in Hisptr.
    destruct Hisptr.
    subst v'13. unfolds. introv Hf. unfold ptr_in_ecblist in Hf. destruct v'19; tryfalse.
    simpljoin.
    get_hsat Hsat.
    sep_lifts_trms_in Hsat (Astruct, ecbf_sllseg). 
    apply hd_not_in_evt_freelist in Hsat; auto.
  }
  hoare_split_pure_all.
  match goal with
    H: SEM_ECB_P _ _ _ _ (?v :: ?vl) _ _ _ |- _ => remember v as hv; remember vl as tvl
  end.  
  assert (Hin: ptr_in_ecblist (Vptr (pevent_block, Int.zero)) (Vptr (pevent_block, Int.zero)) (hv :: tvl)).
  {
    unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
    asserts_rewrite (beq_pos pevent_block pevent_block = true).
    {
      rewrite beq_pos_Pos_eqb_eq. 
      apply Pos.eqb_refl.
    }
    change (Int.eq Int.zero Int.zero) with true.
    simpl. auto.
  }
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part1.
  sep cancel AOSQFreeList. sep cancel AOSQFreeBlk. sep cancel AECBList.
  sep cancel (Aabsdata absecblsid).
  sep pauto. 
  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_part2. eauto. eauto.
  instantiate ( 8:= (set v'35 ct (V$ __EvLoc_ecbcre1))).
  instantiate ( 7:= ((set v'36 ct (Vnull, Vptr (pevent_block, Int.zero), Vnull)))).

  unfold ASemEIBs, AMuxEIBs, AMqEIBs in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.  
  eapply semecb_preserve_cre1; eauto. rewrite Heqhv. unfold V_OSEventListPtr. simpl. auto.

  unfold ASemEIBs, AMuxEIBs, AMqEIBs in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.  
  eapply muxecb_preserve_cre1; eauto. rewrite Heqhv. unfold V_OSEventListPtr. simpl. auto.

  unfold ASemEIBs, AMuxEIBs, AMqEIBs in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.  
  eapply qecb_preserve_cre1; eauto. rewrite Heqhv. unfold V_OSEventListPtr. simpl. auto.

  eapply not_in_els_notdel; eauto.
  eapply evcre_nodup_cre1_preserve; eauto.
  eapply evdel_nodup_cre1_preserve; eauto.

  eauto.
  unfold AOSEventFreeList.
  unfold tcbllsegevaux. 
  sep pauto.

  sep cancel ASemEIBs. sep cancel AMuxEIBs. sep cancel AMqEIBs.
  sep cancel llsegevaux.
  unfold ecbf_sll. unfold V_OSEventListPtr. sep cancel ecbf_sllseg. 
  sep pauto.

  eapply backward_rule1.
  introv Hsat.
  eapply fold_EvtInv_frm.
  sep cancel EvtInv_part1.
  sep cancel EvtInv_part2. sep pauto.
  (* EXIT_CRITICAL;ₛ *) 
  hoare forward prim. 
  sep cancel EvtInv.
  sep cancel Aier.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep normal.
  sep eexists.
  sep split; eauto.
  sep cancel CurTid.
  sep cancel flag_off.
  try_cancel_evaux_asst.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  eauto.
  splits; eauto.
  unfold isevloc. pure_auto.
  pure_auto.
  pure_auto.
  
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.zero) = Vint32 Int.zero \/
         Vint32 (Int.notbool Int.zero) = Vnull |- _ =>
      unfold Int.notbool in H; simpl in H;
      rewrite Int.eq_true in H; auto;
      destruct H; tryfalse
    | _ => idtac
  end.
  instantiate (1:= <|| v'0 ||>  **
         Aisr empisr **
         (EX v'2 ,Aier v'2) ** 
         Aie true **
         Ais nil **
         Acs nil **
         p_local OSLInv ct
         (logic_val (V$ 1)
                    :: logic_val (V$ __EvLoc_ecbcre2)
                    :: logic_val Vnull
                    :: logic_val (Vptr (pevent_block, Int.zero)) :: logic_val Vnull :: nil) ** 
         A_dom_lenv ((cnt, Int16u) :: (pevent, OS_EVENT ∗) :: nil) **
         LV pevent @ OS_EVENT ∗ |-> Vptr (pevent_block, Int.zero) **
         LV cnt @ Int16u |-> Vint32 i). 
  (* assign *)
  hoare forward.
  subst hv. simpl. mauto.
  hoare forward. 
  pure_auto. subst hv. simpl. mauto.
  hoare forward.
  subst hv. simpl. mauto.
  hoare forward. 
  sep cancel Aisr.
  sep cancel Aier.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aie.
  sep cancel Aop.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel p_local.
  sep pauto.
  change (Int.unsigned ($ OS_EVENT_TYPE_SEM)) with 3.
  unfold isptr.
  splits; eauto.
  (* auto with zarith. *) 
  pure_auto.
  
  intros. sep auto.
  intros. sep auto.

  unfold OS_EventWaitListInitPost.
  unfold OS_EventWaitListInitPost'.
  unfold getasrt.

  pure intro.
  rename v'53 into er.
  inverts H37.  (* eq. on logicl *) 
  hoare forward prim.
  (* splits;intros;eauto. splits;auto. *)
  hoare normal pre.
  hoare_ex_intro.
  hoare unfold.
  unfold EvtInv.

  rename v'63 into vcspace1.
  rename v'64 into v64. 
  rename v'65 into v65. 
  rename v'66 into v66. 

  hoare unfold.
  hoare forward.
  pure_auto.
  rename v'44 into pb.
  hoare_assert_pure (EcbMod.get v'55 (pb, Int.zero) = None). 
  {
    eapply semcre_ecblist_star_not_inh; eauto.
    instantiate (3:= s0).
    sep pauto.
  }
  hoare_split_pure_all.
  
  hoare unfold.
  hoare forward.
  fold_AEventNode_r.

  hoare_lifts_trms_pre (tcbllsegevaux,AOSTCBList,p_local).
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  
  hoare_assign_evaux.
  unfold isevloc;auto.
  rename v'80 into locmp.
  rename v'81 into ptrmp.
  assert (Hptr: get ptrmp ct = Some (Vnull, Vptr (pb, Int.zero), Vnull)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }  
  assert (Hloc: get locmp ct = Some (V$ __EvLoc_ecbcre1)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  assert (Hncre1': ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 (pb, Int.zero)).
  {
    eapply cre_nodup_no_cre1; eauto.
  }
  assert (Hncre2': ~exists t, t <> ct /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 (pb, Int.zero)).
  {
    eapply cre_nodup_no_cre2; eauto.
  }
  assert (Hndel: ~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel (pb, Int.zero)).
  {
    eapply not_in_els_notdel; eauto.
  }
  (* execute absop *)
  hoare_lifts_trms_pre (Aop, absecblsid, evlocid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply semcre_absimp_ecb_activate; auto.
  can_change_aop_solver.
  simpl. intros; split; auto.
  pure_auto.
  eapply absinfer_eq.

  (* prepare to exit from critical section *) 

  fold_evaux_sem_loc (V$ __EvLoc_ecbcre2) (Vptr (pb, Int.zero)).
  assert (Heq:(EvAuxPtrMod.set ptrmp ct (Vnull, Vptr (pb, Int.zero), Vnull)) = ptrmp).
  {
     clear - Hptr.
     eapply EvAuxPtrMod.get_set_same.
     unfold get in Hptr.
     unfold EvAuxPtrMap in Hptr.
     auto.
  }
  rewrite Heq.
  eapply backward_rule1. 
  introv Hsat.
  eapply fold_EvtInv_part2.
  eauto. eauto.
  unfold ASemEIBs, AMuxEIBs, AMqEIBs in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat. 
  eapply sem_ecb_cre2_preserve; eauto.
  unfold ASemEIBs, AMuxEIBs, AMqEIBs in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat. 
  eapply mux_ecb_cre2_preserve; eauto.
  unfold ASemEIBs, AMuxEIBs, AMqEIBs in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat. 
  eapply q_ecb_cre2_preserve; eauto.
  introv Hex. apply Hndel.
  destruct Hex as (t & Hneq & tle).
  exists t. auto.
  eapply evcre_nodup_cre2_preserve; eauto.
  eapply evdel_nodup_cre2_preserve; eauto.
  eauto.
  sep pauto.
  unfold tcbllsegevaux.
  sep cancel llsegevaux.
  sep_lifts_trms_in Hsat (ASemEIBs,AMuxEIBs,AMqEIBs).
  destruct_s s.
  sep remember (1::nil)%nat in Hsat.
  sep remember (1::nil)%nat.
  solve_sat Hsat.
  eapply ASemEIBs_set_els_preserve; eauto.
  sep remember (1::nil)%nat in H68.
  sep remember (1::nil)%nat. 
  solve_sat H68.
  eapply AMuxEIBs_set_els_preserve; eauto.
  sep remember (1::nil)%nat in H71.
  sep remember (1::nil)%nat. 
  solve_sat H71.
  eapply AMqEIBs_set_els_preserve; eauto.

  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eapply fold_EvtInv_frm.
  sep cancel EvtInv_part2.
  sep cancel tcbdllflag.
  sep cancel Aier.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep cancel CurTid.
  sep normal. sep eexists.
  sep split; eauto.
  try_cancel_evaux_asst.
  sep cancel flag_off.
  2: { splits; eauto. unfold isevloc. auto. } 
  unfold EvtInv_part1.
  unfold AECBList.
  sep pauto.

  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  instantiate (2:= (DSem v'46) :: v'68). (* DSem n :: ecbls *) 
  instantiate (2:= ((V$ OS_EVENT_TYPE_SEM
            :: Vint32 Int.zero :: Vint32 v'46 :: Vnull :: v'48 :: v'82 :: Vint32 Int.zero :: v'52 :: nil), INIT_EVENT_TBL,INIT_EVENT_PTBL) :: v'65). 
  simpl evsllseg at 1.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold AOSEventTbl.
  unfold AOSPostEventTbl.
  sep pauto.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel evsllseg.
  cancel_corecommuinv. 
  
  (* PartitionInv *)
  Require Import sem_partition.
  cancel_partitioninv.
  eauto.
  (* end of PartitionInv *)

  clear -H33.
  int auto.
  unfold V_OSEventListPtr. simpl. auto.
  eapply semcre_RL_Tbl_init_prop.
  unfolds; simpl; auto.
  eauto.
  unfold array_type_vallist_match.
  splits; pauto.
  eapply semcre_RL_Tbl_init_prop.
  unfold V_OSEventGrp; simpl; auto.
  auto.
  unfold array_type_vallist_match.
  splits; pauto.
  eapply semcre_ECBList_P; eauto.
  eapply semcre_RH_TCBList_ECBList_P; eauto.
  pure_auto.
  sep pauto.
  sep cancel Aisr. sep cancel Aie. sep cancel Ais. sep cancel Acs. sep cancel A_dom_lenv. sep cancel Aier. sep pauto.
  (* return *) 
  hoare unfold.
  hoare forward.
  right. splits; eauto.
  Unshelve.
  exact Atrue.
  exact Vnull.
Qed.
