Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import ACSpace_defs.
Require Import CapSpec.
Require Import include_frm.
Require Import os_inv.
Require Import abs_op.
Require Import abs_op_capability.
Require Import os_spec.
Require Import os_program.
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import Lia.
Require Import sem_lab. 
Require Import CapPure.
Require Import abs_op_capability.
Require Import CapRelLemmas.

Import DeprecatedTactic.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.
Set Keyed Unification.

Definition EINVAL := 30%Z.

Lemma user_cnode_delete_absimp_null:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  (Int.ltu ($ OS_LOWEST_PRIO) i  = true \/ Int.eq i ($ OS_LOWEST_PRIO) = true) ->
  absinfer sch ( <|| user_cnode_delete_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P ).
Proof.
infer_solver 0%nat.
Qed.  

Lemma user_cnode_delete_absimp_wrong:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  Int.ltu ($ CAP_TASK_TYPE) i0 = true ->
  absinfer sch ( <|| user_cnode_delete_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P ).
Proof.
infer_solver 1%nat.
Qed. 

Lemma user_cnode_delete_absimp_slotnum:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  (Int.ltu (Int.repr CAP_TASK_TYPE) i0 = false) ->
  (not ((Int.ltu  (Int.repr OS_LOWEST_PRIO) i = true \/ Int.eq i (Int.repr OS_LOWEST_PRIO) = true))) ->
  absinfer sch ( <|| user_cnode_delete_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P ).
Proof.
infer_solver 3%nat.
Qed. 

Lemma user_cnode_delete_absimp_failure:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  absinfer sch ( <|| user_cnode_delete_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr CNODE_DELETE_FAILURE))) ||> ** P ).
Proof.
infer_solver 2%nat.
Qed. 

Lemma user_cnode_delete_absimp_nocap:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
   absinfer sch ( <|| user_cnode_delete_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||>  ** P)
           ( <|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||>  ** P ).
Proof.
infer_solver 4%nat.
Qed.

Lemma user_cnode_delete_absimp_succ_category:
forall i i0 i1 v' sch P acspace  slots childs prio 
slot_type cap_type cap_content cap_right object_t acspace' acspace'' index,
  can_change_aop P -> 
  CSpaceMod.get acspace i = Some (slots, childs, prio) ->
  nth_slots (Z.to_nat (Int.unsigned index)) slots =
    Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
  (acspace' =  (CSpaceMod.set acspace i
      (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) slots
        (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))),
      childs, prio))) ->
  (acspace'' = (CSpaceMod.set acspace' i
  (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) 
  (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) slots
  (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))))
  (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, Int.zero, object_t))),
  childs, prio))) ->
absinfer sch ( <|| user_cnode_delete_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** Hcapspace acspace ** P)
    ( <|| END (Some (Vint32 (Int.repr CNODE_DELETE_SUCCESS))) ||> ** Hcapspace acspace'' ** P).
Proof.
infer_solver 5%nat.
Qed. 

Lemma user_cnode_delete_absimp_succ_object:
forall i i0 i1 v' sch P acspace  slots childs prio 
slot_type cap_type cap_content cap_right object_t acspace' acspace'' index,
  can_change_aop P -> 
  CSpaceMod.get acspace i = Some (slots, childs, prio) ->
  nth_slots (Z.to_nat (Int.unsigned index)) slots =
    Some (slot_type, (cap_type, (cap_content, cap_right, object_t))) ->
  (acspace' =
  (CSpaceMod.set acspace i
    (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) slots
      (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))),
    childs, prio))) ->
  ( acspace'' = (CSpaceMod.set acspace' i
  (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) 
  (update_nth_list slot_val_type (Z.to_nat (Int.unsigned index)) slots
  (Int.repr SLOT_NULL_CAP, (cap_type, (cap_content, cap_right, object_t))))
  (Int.repr SLOT_NULL_CAP, (Int.zero, (Int.zero, cap_right, Vnull))),
  childs, prio))) ->
absinfer sch ( <|| user_cnode_delete_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** Hcapspace acspace ** P)
    ( <|| END (Some (Vint32 (Int.repr CNODE_DELETE_SUCCESS))) ||> ** Hcapspace acspace'' ** P).
Proof.
infer_solver 6%nat.
Qed. 



Lemma UserCnodeDeleteProof: 
  forall  tid vl p r, 
    Some p =
    BuildPreA' os_api user_cnode_delete
    user_cnode_delete_api vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api user_cnode_delete
    user_cnode_delete_api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api user_cnode_delete = Some (t, d1, d2, s) /\ 
            {|Cap_spec, GetHPrio, OSLInv,  I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  (*The 1st If*)
  lzh_hoare_if; pure_auto.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply user_cnode_delete_absimp_null.
  can_change_aop_solver.
  unfold val_inj in LHift_true;pure_auto.
  hoare forward.
(*Enter critical*)
hoare forward prim. pure_auto.

  (*The second If*)
  lzh_hoare_if; pure_auto.
  pure intro.
  hoare forward prim.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel APthreadAttr.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel EvtInv.
  sep cancel tcbdllflag.
  exact H1. 
  apply H.
  go.
  
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply user_cnode_delete_absimp_wrong.
  can_change_aop_solver.
  eauto.
  hoare forward.

  assert (destlt64: Int.unsigned i < ios_cap_defs.OS_LOWEST_PRIO).
  clear -Hif_false.
  unfold val_inj,bool_or in Hif_false.
  int auto. simpl in Hif_false.
  inversion Hif_false.
  inversion H0.
  try false.
  int auto. simpl in Hif_false.
  inversion Hif_false.
  inversion H2.
  try false.
  change (ios_cap_defs.OS_LOWEST_PRIO) with 63.
  lia.
  change (ios_cap_defs.OS_LOWEST_PRIO) with 63.
  lia.

  
  unfold CapabilityInv.
  (*将pre中的pure提到前面，同时EX也提到了前面*)
  pure intro.
  rename H7 into Hwellform_descendents.
  rename H8 into  H7.
  rename H9 into H8.
  destruct v'24.
 

(*func_capability ′ =ᶠ Check_Cap_Type (·func_capability ′, 
func_capType ′, destTask_Prio ′·);ₛ*)
  
  unfold EvtInv.
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  unfold AGVars.
  hoare_split_pure_all.
  (*destruct v'6.*)
  destruct v'60.
  destruct v'61.
  destruct v'62.
  eapply backward_rule1.
  intros.
  Require Import seplog_trm_tacs.
  sep_lifts_trms_in H33 (Aisr, Ais, A_isr_is_prop).
  (* sep remember(1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::nil)%nat in H55.  *)
  eapply elim_a_isr_is_prop in H33.
  sep_lifts_trms_in H33 aemp_isr_is.
  eapply aemp_isr_elim in H33.   
  exact H33. 
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold Check_Cap_Type_spec_weak.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  change Byte.max_unsigned with 255.
  assert(Int.unsigned i0 <=? 255 = true).
  clear -Hif_false0.
  change CAP_TASK_TYPE with 5 in Hif_false0.
  unfold Int.ltu in Hif_false0.
  destruct (zlt (Int.unsigned ($ 5)) (Int.unsigned i0)).
  try false.
  int auto.
  rewrite H34. auto.
  eapply rvl_elim. sep get rv.
  change Byte.max_unsigned with 255.
  assert(Int.unsigned i <=? 255 = true).
  clear -H3.
  int auto.
  rewrite H34. auto.
  eapply rvl_nil.
  intros.
  sep cancel func_capability.
  unfold getasrt.
  unfold Check_Cap_TypePre.
  unfold Check_Cap_TypePre'.  
  sep normal.
  sep eexists.
  sep cancel Aie. sep cancel Ais. sep cancel Acs. sep cancel Aisr. sep cancel Aier.
  sep cancel Aop.
  sep split.
  sep cancel AOSCSpacePrioTbl.
  sep cancel AMqAttr.
  sep cancel ASeminfo.
  sep cancel APthreadMutex.
  sep cancel AOSCSpaceObjectPointer.
  sep cancel AOSTCBPrioTbl.  
  sep cancel p_local.
  exact H33.
  8:
  {
    unfold AOSCSpaceCapParent.    
    unfold CSpaceGVars.
    good_frm_sovler.
    (* eapply GoodFrm_ACSpaceAarrayTptr.     *)
  }
  5: simpl;eauto.
  5: simpl;eauto.
  5: simpl;eauto.  
  eauto. eauto. eauto. eauto.
  apply retpost_CheckCapTypeWeakPost.
  unfold tl_vl_match; unfold type_val_match; pure_auto.
  {
    unfold getasrt.
    unfold Check_Cap_TypeWeakPost.
    unfold Check_Cap_TypePost''.
    intros.
    sep destruct H33. eexists.
    sep cancel p_local. simpl. auto.
  }
  {
    unfold getasrt.
    unfold Check_Cap_TypePre.
    unfold Check_Cap_TypePre'.
    intros.
    sep destruct H33. eexists.
    sep cancel p_local. simpl. auto.
  }  
  unfold getasrt.
  unfold Check_Cap_TypeWeakPost.
  unfold Check_Cap_TypePost''.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (AOSTCBList, AOSTCBPrioTbl).
  inverts H38. 
  simpl in H33, H34, H35.
  inverts H33. inverts H34. inverts H35.
  hoare normal pre; hoare_ex_intro.

  (*add A_isr... back*)
  eapply backward_rule1.
  intros.
  Require Import seplog_trm_tacs.
  sep_lifts_trms_in H33 (Aisr, Ais).
  (* sep remember(1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::nil)%nat in H55.  *)
  eapply add_a_isr_is_prop in H33.
  sep_lifts_trms_in H33 (Aisr, Ais, Aier).
  eapply add_aemp_isr_is_prop in H33.  
  exact H33. 

  (*begin: fold the assertions back*)
  eapply backward_rule1 with (p:=<||
  user_cnode_delete_spec (Vint32 v'63 :: Vint32 v'62 :: Vint32 v'61 :: v')
  ||>  **
  OldOSInvWL tid (logic_val (V$ 1)::logic_val (V$ __EvLoc_normal)
  :: logic_val Vnull
     :: logic_val Vnull :: logic_val Vnull :: nil) **
   aemp_isr_is **
   Aisr empisr ** Aier v'64 ** Aie false ** Ais nil ** Acs (true :: nil) **
   ([|Some v'60 = Some (V$ SLOT_NUM)|] \\//
    [|(exists ret, Some v'60 = Some (V$ ret) /\ 0 <= ret < 255) /\
    (Int.unsigned v'62 = CAP_FUNCTION_TYPE /\
      Int.unsigned v'61 <= CAP_CHANNEL_CLASS \/
      (Int.unsigned v'62 = CAP_SEM_TYPE \/
       Int.unsigned v'62 = CAP_MUTEX_TYPE \/
       Int.unsigned v'62 = CAP_Q_TYPE) /\
      Int.unsigned v'61 <  OS_USER_MAX_EVENTS /3  \/
      Int.unsigned v'62 = CAP_TASK_TYPE /\
      Int.unsigned v'61 < OS_STAT_PRIO)|]) **
         LV func_capability @ long |-> v'60 **
         LV y @ char_t |-> v'2 **
         LV ios_cap_defs.i @ char_t |-> v'1 **
         LV pCSpace @ CSPACE ∗ |-> v'0 **
         LV func_capType @ char_t |-> Vint32 v'62 **
         LV destTask_Prio @ char_t |-> Vint32 v'63 **
         A_dom_lenv
           ((func_capability, long)
            :: (func_capType, char_t)
               :: (destTask_Prio, char_t)
                  :: (pCSpace, CSPACE ∗)
                     :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)
).
  intros.
  unfold OldOSInvWL.
  unfold CapabilityInv.
  unfold AGVars.
  unfold EvtInv.
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  sep normal. sep eexists.
  sep cancel AOSCSpacePrioTbl.
  sep cancel AOSCSpaceObjectPointer.
  sep cancel AOSCSpaceCapParent.
  sep cancel AMqAttr.
  sep cancel AMqCap.
  sep cancel APthreadMutex.
  sep cancel AMuxCap.
  sep cancel ASeminfo.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AOSQFreeList.
  sep cancel AECBList.
  sep cancel ASemCap.
  sep cancel CSpaceGVars.
  sep cancel cspaceid.
  sep cancel absecblsid.
  sep cancel eblsid.
  sep cancel AErrblkList.
  sep cancel pblsid.
  sep cancel APosblkList.
  sep cancel evatomheapid.
  sep cancel AEvAtomHeap.
  sep cancel evstructheapid.
  sep cancel AEvStructHeap.
  sep cancel AEvArrayHeap.
  sep cancel evarrayheapid.
  sep cancel seminfoid.
  sep cancel absmutinfoid.
  sep cancel absmqattrid.
  sep cancel evlocid.
  sep cancel evptrid.
  sep cancel tcbllsegevaux.
  sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSTCBList.
  sep cancel AOSTCBFreeList.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTime.
  sep cancel APthreadAttr.
  sep cancel A_isr_is_prop.
  sep cancel IntInv.
  sep cancel TmrInv.
  sep cancel CoreCommuInv.
  sep cancel PartitionInv.
  sep cancel tcbdllflag.
  sep cancel OSLockNesting.
  sep cancel OSIntNesting.
  sep cancel ios_int.INT_MUX_H.
  sep cancel ios_int.INT_MUX_L.
  sep cancel ios_int.CGEM_regs_INTMUX3.
  sep cancel ios_int.CGEM_regs_INTMUX2.
  sep cancel ios_int.CGEM_regs_INTMUX1.
  sep cancel OSIntExitY.
  sep cancel OSPrioCur.
  sep cancel OSTCBHighRdy.
  sep cancel OSCtxSwCtr.
  sep cancel OSPrioHighRdy.
  sep cancel aemp_isr_is.
  sep cancel abstcblsid.
  sep cancel ostmid.
  sep cancel curtid.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie.
  sep cancel A_dom_lenv.
  sep cancel OSRunning.
  sep cancel func_capability.
  sep cancel p_local.
  sep cancel y.
  sep cancel ios_cap_defs.i.
  sep cancel pCSpace.
  sep cancel func_capType.
  sep cancel destTask_Prio.
  sep cancel v'60.
  sep pauto.
  (*end*)  

 (*If (func_capability ′ ==ₑ ′ SLOT_NUM)*)
  pure intro.
  lzh_hoare_if.
  assert (s
    |= ([|Some v'60 = Some (V$ SLOT_NUM)|] \\//
        [|(exists ret, Some v'60 = Some (V$ ret) /\ 0 <= ret < 255) /\
        (Int.unsigned v'62 = CAP_FUNCTION_TYPE /\
      Int.unsigned v'61 <= CAP_CHANNEL_CLASS \/
      (Int.unsigned v'62 = CAP_SEM_TYPE \/
       Int.unsigned v'62 = CAP_MUTEX_TYPE \/
       Int.unsigned v'62 = CAP_Q_TYPE) /\
      Int.unsigned v'61 < OS_USER_MAX_EVENTS / 3 \/
      Int.unsigned v'62 = CAP_TASK_TYPE /\
      Int.unsigned v'61 < OS_STAT_PRIO)|]) ** Atrue).
  sep pauto.
  eapply disj_split in H33.
  destruct H33.
  sep split in H33. inverts H34.
  auto. 
  Optimize Proof.
  Optimize Heap.
  sep split in H33.
  simpljoin. inverts H34.
  auto. 
  assert (s
    |= ([|Some v'60 = Some (V$ SLOT_NUM)|] \\//
        [|(exists ret, Some v'60 = Some (V$ ret) /\ 0 <= ret < 255) /\(Int.unsigned v'62 = CAP_FUNCTION_TYPE /\
        Int.unsigned v'61 <= CAP_CHANNEL_CLASS \/
        (Int.unsigned v'62 = CAP_SEM_TYPE \/
         Int.unsigned v'62 = CAP_MUTEX_TYPE \/
         Int.unsigned v'62 = CAP_Q_TYPE) /\
        Int.unsigned v'61 < OS_USER_MAX_EVENTS / 3 \/
        Int.unsigned v'62 = CAP_TASK_TYPE /\
        Int.unsigned v'61 < OS_STAT_PRIO)|]) ** Atrue).
  sep pauto.
  unfold val_inj, val_eq.
  eapply disj_split in H33.
  destruct H33.
  sep split in H33.
  inverts H34.
  rewrite Int.eq_true. auto. 
  sep split in H33.
  simpljoin.
  inverts H34.
  destruct (Int.eq ($ x) ($ SLOT_NUM)); auto. 

  eapply seq_rule.
  (*hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  *)



  hoare forward prim. 
   go. 
  unfold GoodFrm. auto.  

  (**)
  hoare_lifts_trms_pre (Aop).
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply user_cnode_delete_absimp_slotnum.
  can_change_aop_solver.
  unfold can_change_aop. auto. eauto. 
  unfold val_inj in Hif_false;simpl in Hif_false;destruct Hif_false;pure_auto;tryfalse.
  rewrite H34 in HeqH33.
  tryfalse.
  rewrite H34 in HeqH34.
  tryfalse. 
  hoare forward;pure_auto.
  sep_lifts_trms_in H24 (SLOT_NUM).
  eapply disj_split in H24.
  destruct H24.
  sep split in H24.
  eauto.
  sep split in H24.
  eauto.

  (*to refine the condition to be
    [|exists ret, Some v'60 = Some (V$ ret) /\ 0 <= ret < 255|]*)
  eapply backward_rule1 with (p:=<||
  user_cnode_delete_spec
    (Vint32 v'63 :: Vint32 v'62 :: Vint32 v'61 :: v') ||>  **
  OldOSInvWL tid
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  aemp_isr_is **
  Aisr empisr **
  Aier v'64 **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  [|exists ret, Some v'60 = Some (V$ ret) /\ 0 <= ret < 255|] **
  LV func_capability @ long |-> v'60 **
  LV y @ char_t |-> v'2 **
  LV ios_cap_defs.i @ char_t |-> v'1 **
  LV pCSpace @ CSPACE ∗ |-> v'0 **
  LV func_capType @ char_t |-> Vint32 v'62 **
  LV destTask_Prio @ char_t |-> Vint32 v'63 **
  A_dom_lenv
    ((func_capability, long)
     :: (func_capType, char_t)
        :: (destTask_Prio, char_t)
           :: (pCSpace, CSPACE ∗)
              :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  intros.
  sep_lifts_trms_in H24 v'60.
  apply disj_split in H24.
  destruct H24.
  sep split in H24.
  inverts H33.
  clear -Hif_false1.
  unfold val_inj,val_eq in Hif_false1.
  assert (Int.eq ($ SLOT_NUM) ($ SLOT_NUM) = true).
  go. rewrite H in Hif_false1.
  inverts Hif_false1. inverts H0. tryfalse.
  sep pauto. 
  rewrite H33.
  eauto.
  
     
  (*y ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ*)
  unfold OldOSInvWL.
  unfold AOSTCBList;unfold_dll.
  pure intro.
  assert(Hpriolt64:Int.unsigned i3 < 64).
  unfold TCBList_P in H41.
  simpljoin.
  unfold TCBNode_P in H44.
  destruct x3, p, p.
  simpljoin. 
  unfold RL_TCBblk_P in H60.
  simpljoin.
  unfold V_OSTCBPrio in H60. simpl in H60.
  inverts H60. lia.
  assert(Htrue: Int.unsigned i3 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -Hpriolt64. int auto.
  assert(Hitrue: Int.unsigned v'63 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H3. int auto.

  hoare forward.
  go. 
  pure intro.
  unfold CapabilityInv.
  hoare_split_pure_all.
  rename H61 into Hwellform_descendents1.
  destruct v'10. 
  hoare remember (1::nil)%nat pre.
  unfold AOSCSpacePrioTbl. hoare_split_pure_all.
  assert(Htypematch : array_type_vallist_match CSPACE ∗ v'15).
  simpljoin. auto.
  assert(Hlenv'76: length v'15 = 64%nat). simpljoin. auto.
  assert(Hlenv'30: length v'60 = 64%nat). simpljoin. auto.
  eapply backward_rule1 with (p:=AOSCSpacePrioTbl (b, i6) v'15 v'60 v'97 ** H61).
  intros.
  unfold AOSCSpacePrioTbl. 
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep split; auto.
  subst H61.
  clear H62.
  Require Import seplog_trm_tacs.
  hoare_lifts_trms_pre (Aop, AOSCSpacePrioTbl, Alvarmapsto pCSpace, Alvarmapsto y, A_dom_lenv, p_local).
  hoare remember (1::2::3::4::5::6::nil)%nat pre.
  unfold AOSCSpacePrioTbl.
  hoare_split_pure_all.
  eapply seq_rule.
  
  eapply assign_rule_lvar.
  {
    intros. split. intros.
    sep_lifts_trms_in H63 (pCSpace).
    exact H63.
    intros.
    sep pauto.
  }
  {
    intros.
    eapply array_member_rv_g.
    unfold GAarray.
    sep normal. sep eexists.
    sep cancel OSCSpacePrioTbl. 
    sep cancel Aarray. sep cancel A_dom_lenv.
    exact H63.
    simpl. auto.
    eauto.
    sep get rv.
    rewrite Htrue. auto.
    eauto. auto. lia. lia.
    rewrite Hlenv'76. auto.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hlenv'76. lia.
  }
  eapply eq_vptr. eauto.
  intros.
  eexists.
  sep cancel p_local. simpl. auto.
  eapply backward_rule1 with(p:=<|| user_cnode_delete_spec (Vint32 v'63 :: Vint32 v'62 :: Vint32 v'61 :: v')
  ||>  **
  LV pCSpace @ CSPACE ∗ |-> nth_val' (Z.to_nat (Int.unsigned i3)) v'15 **
  AOSCSpacePrioTbl (b, i6) v'15 v'60 v'97 **
  LV y @ char_t |-> Vint32 i3 **
A_dom_lenv
  ((func_capability, long)
   :: (func_capType, char_t)
      :: (destTask_Prio, char_t)
         :: (pCSpace, CSPACE ∗)
            :: (ios_cap_defs.i, char_t)
               :: (y, char_t) :: nil) **
               p_local OSLInv (v'96, Int.zero) init_lg ** H61).
  intros. unfold AOSCSpacePrioTbl.
  sep cancel H61. sep auto.
  subst H61.
  assert(HpCSpacetype: rule_type_val_match CSPACE ∗
  (nth_val' (Z.to_nat (Int.unsigned i3)) v'15) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hlenv'76. lia.
  clear H62.
  hoare forward.
  unfold val_inj, val_eq.
  clear -HpCSpacetype.
  unfold rule_type_val_match in HpCSpacetype.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i3)) v'15); tryfalse; auto;destruct a; auto.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop).
  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  
  unfold OldOSInvWL.
  unfold CapabilityInv.
  try unfold AOSTCBList;unfold_dll.
  sep normal. sep eexists.
  sep cancel AOSCSpacePrioTbl. sep cancel AOSCSpaceObjectPointer.
  sep cancel AOSCSpaceCapParent.
  sep cancel CSpaceGVars. 
  sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl. sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp. sep cancel AOSTime.
  sep cancel APthreadAttr. 
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  sep cancel AOSTCBFreeList. sep cancel A_isr_is_prop.
  sep cancel tcbdllflag.
  sep cancel Astruct.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel cspaceid.
  sep cancel EvtInv.
  sep cancel AGVars.
  sep cancel OSTCBList.
  sep cancel OSTCBCur.
  sep cancel abstcblsid.
  sep cancel ostmid.
  sep cancel curtid.
  sep pauto.
  eauto.  eauto. eauto. go. go.
  unfold GoodFrm. eauto.
  
  (*RETURN 〈 char_t 〉 ′ CNODE_DELETE_FAILURE*)
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  Optimize Proof.
  Optimize Heap.
  eapply user_cnode_delete_absimp_failure.
  can_change_aop_solver.
  hoare forward.
 (* unfold init_lg.
  sep_lifts_trms_in H61 v'60.
  eapply disj_split in H61.
  destruct H61.
  sep split in H61.
  eauto.
  sep split in H61.
  eauto.
  *)

(*IF ((((((((pCSpace ′ → cnode) .. slots) [′ SLOT_CNODE_CAP])
                      .. capability) .. cap_content) .. category)
                   .. category_right &ₑ ′ CNODE_DELETE_CAP) ==ₑ ′ 0
                  ||ₑ CapParent ′ [destTask_Prio ′]
                      !=ₑ OSTCBCur ′ → OSTCBPrio &&ₑ
                      destTask_Prio ′ !=ₑ OSTCBCur ′ → OSTCBPrio)*)
               
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hnotnull: (nth_val' (Z.to_nat (Int.unsigned i3)) v'15) <> Vnull).
  clear -HpCSpacetype  H61.
  unfold rule_type_val_match in HpCSpacetype.
  unfold val_inj, val_eq in H61.
  destruct (nth_val' (Z.to_nat (Int.unsigned i3)) v'15); destruct H61; tryfalse.
  destruct a; auto. destruct a. auto.
  clear H61.
  eapply backward_rule1.
  intros.

  sep_lifts_trms_in H61 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned i3)) in H61.
  exact H61.
  rewrite Hlenv'30.
  lia.
  auto.
  hoare_split_pure_all.
  unfold ACSpace.
  destruct v'100, p, p, p, v'104.
  unfold Acnode. 
  destruct c, p. 
  hoare_split_pure_all.
  (*在这里，关系直接代入，消失了。*)
  simpljoin.
  rename H70 into Hi7range.
  rename H71 into H70.
  rename H72 into H71.
  eapply backward_rule1.
  intros.
   
  sep_lifts_trms_in H61 (ASlots).
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(SLOT_CNODE_CAP)) in H61; eauto. 
  (* eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned i1)) in H29; eauto.  *)
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  hoare_split_pure_all.
  simpljoin.
  unfold ACap. destruct v'104, c, p. 
  unfold AOSCSpaceCapParent.
  hoare_split_pure_all.
  destruct H74.
  destruct H75. 
  assert(Hx: (Z.to_nat(Int.unsigned v'63) < 64)%nat).
  clear -destlt64.
  change ios_cap_defs.OS_LOWEST_PRIO with 63 in destlt64. lia. 
  lets Hy: nthval'_has_value_Tint32 H74 H75 Hx.
  destruct Hy. destruct H77.
  assert (nth_val' (Z.to_nat (Int.unsigned i3))
        (v'102 ++ Vptr (b0, i9) :: v'103) = Vptr (b0, i9)).
  eapply nth_val'_length_imp. eauto.
  rewrite H79.
  eapply forward_rule1 with(q:=Afalse \\//Afalse).
  intros.
  destruct H80; auto.
  eapply if_rule2.
  intros.
  eapply bop_rv.
  eapply bop_rv.
  eapply bop_rv.
  eapply lv_mapsto_to_rv.
  2:{
    eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply field_asrt_impl_struct_aop'.
        3:{
          eapply field_asrt_impl_struct_aop'.
          3:{
            eapply expr_field_array_asrt_impl_frm_val.
            4:{
            eapply local_val_struct_member_addr_frm.
              4:{
                sep cancel pCSpace. exact H80.
                } 
                unfold CSPACE. eauto.
                unfold field_offset. simpl. eauto.
                simpl. unfold Cte. simpl. eauto. 
              }
              unfold field_offset. simpl.
              rewrite Int.add_zero.
              change ($ 4 +ᵢ  $ 4) with ($8). eauto.
              instantiate(1:=2%nat). simpl. auto.
              simpl. unfold Slot. eauto.
              }
              simpl. unfold Cap. eauto.
              unfold field_offset. simpl. rewrite Int.add_zero.
              eauto.
            }
            simpl.
            unfold Content. eauto.
            unfold field_offset. simpl.
            rewrite Int.add_zero. eauto.
          }
          simpl. unfold Cap_Category. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl.
        rewrite Int.add_zero. eauto.
      }
  2:{
  rewrite Int.add_zero.
  rewrite Int.add_zero.
  simpl typelen in *.
  rewrite <- addition_trans.
  rewrite Int.unsigned_repr.
  rewrite Int.add_assoc.
  change ($ 4 +ᵢ  $ 4) with ($8).
  unfold SLOT_CNODE_CAP.

  sep normal in H80.
  sep lift 5%nat in H80.
  unfold Aptrmapsto in H80 at 1.
  exact H80.
  unfold SLOT_CNODE_CAP. rewrite max_unsigned_val.
  lia. lia. 
}
simpl. auto. 
destruct_s s. simpl; eauto.
eauto.
unfold val_inj, bop_eval, and. 
auto. 
simpl. eauto.
destruct_s s. simpl; eauto.
eauto.
unfold val_inj, bop_eval, and, val_eq.
destruct(Int.eq (i14&ᵢ$ CNODE_DELETE_CAP) ($ 0)); auto.
simpl. eauto.
sep get rv.
rewrite Hitrue. auto. 
rewrite H77. auto. go.
rewrite H77. 
unfold val_inj, val_eq.
destruct (Int.eq x0 i3); eauto.
rewrite H77. 
unfold val_inj, notint, val_eq.
destruct (Int.eq x0 i3); eauto.
rewrite Hitrue. auto. go.
unfold val_inj.
destruct (Int.eq v'63 i3);eauto.
unfold val_inj, notint.
destruct (Int.eq v'63 i3); eauto.
Ltac val_help:=
      try change (Int.ltu Int.zero Int.zero) with (false);
      try change (Int.ltu Int.one Int.zero) with (false);
      try change (Int.ltu Int.zero Int.one) with (true);
      try change (Int.ltu Int.one Int.one) with (false);
      try change (Int.eq Int.one Int.one) with (true);
      try change (Int.eq Int.one Int.zero) with (false);
      try change (Int.eq Int.zero Int.one) with (false);
      try change (Int.eq Int.zero Int.zero) with (true).
   
unfold val_inj, bop_eval, val_eq, and, uop_eval, notint, bool_and.
unfold Int.zero.
rewrite H77.
destruct (Int.eq x0 i3);destruct (Int.eq v'63 i3);unfold Int.notbool;repeat (val_help;simpl); auto.
simpl. eauto.
unfold val_inj, bop_eval, val_eq, and, uop_eval, notint, bool_and.
unfold Int.zero.
rewrite H77.
destruct (Int.eq (i14&ᵢ$ CNODE_DELETE_CAP) ($ 0));destruct (Int.eq v'63 i3);destruct (Int.eq x0 i3);unfold Int.notbool;repeat (val_help;simpl); auto.
simpl. eauto.


(*EXIT_CRITICAL;ₛ*) 
hoare_split_pure_all.
eapply backward_rule1.
intros.
sep lifts (3::4::5::6::nil)%nat in H81. 
eapply fold_Cap in H81.
sep lifts (2::3::1::4::nil)%nat in H81.
eapply ASlots_fold_any_idx_frm in H81; [idtac | eauto..]. 
sep lifts (6::7::1::nil)%nat in H81.
eapply fold_Acnode in H81.
sep lifts (1::6::7::8::9::nil)%nat in H81.
eapply fold_ACSpace  in H81; [idtac | eauto..]. 
sep lifts (5::1::6::nil)%nat in H81. 
eapply ACSpaceAarray_fold_any_idx_frm in H81; [idtac | eauto; try lia..]. 
sep lifts (2::1::3::4::nil)%nat in H81.
eapply fold_AOSCSpacePrioTbl1 in H81.
exact H81. 
rewrite app_length. simpl.
rewrite H63, H71. rewrite S_add_sub_S. lia.
clear -Hpriolt64. lia.
rewrite app_length. simpl.
rewrite H64, H70. rewrite S_add_sub_S. lia. lia.
eauto.
rewrite nth_val_imp_nth_val'_2. rewrite H79. eauto.
(* clear -Hc1. eapply Z2Nat.inj_lt; int auto.  *)
rewrite app_length. simpl. 
rewrite H63, H71. rewrite S_add_sub_S. lia. lia.
clear -Hpriolt64. lia. 
rewrite app_length. simpl. 
rewrite H62, H73. rewrite S_add_sub_S.
unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
eauto.
eapply seq_rule.
hoare forward prim. 
try unfold AOSTCBList;unfold_dll.
unfold CapabilityInv.
unfold AOSCSpaceCapParent.
sep normal. sep eexists.
sep cancel AOSCSpacePrioTbl.
sep cancel AOSCSpaceObjectPointer.
sep cancel CapParent.
sep cancel CSpaceGVars.
sep cancel APthreadAttr.
sep cancel Astruct.
sep cancel dllseg.
sep cancel dllseg.
sep cancel OSTCBList.
sep cancel OSTCBCur.
sep cancel EvtInv.
sep cancel CoreCommuInv.
sep cancel tcbdllflag.
sep cancel p_local.
sep cancel Aier. 
sep pauto.
eauto. eauto. eauto.
go. eauto. go. 
unfold GoodFrm. auto.  

(*RETURN 
〈 char_t 〉 ′ USER_CAPABILITY_NONE*)

hoare_lifts_trms_pre (Aop).
hoare abscsq.
Hint Resolve noabs_oslinv.
auto.
  Optimize Proof.
  Optimize Heap.
eapply user_cnode_delete_absimp_nocap.
can_change_aop_solver.
unfold can_change_aop. auto.
hoare forward.
(*
sep_lifts_trms_in H81 v'60.
eapply disj_split in H81. 
destruct H81. 
sep split in H81.
unfold init_lg. eauto.
sep split in H81.
unfold init_lg. eauto.
*)

  (*ELSE ios_cap_defs.i ′ =ᶠ ucos_CNode_Delete (·destTask_Prio ′,
func_capability ′·);ₛ*)

(*fold the invariant*)
eapply backward_rule1.
intros.
sep lifts (3::4::5::6::nil)%nat in H80. 
eapply fold_Cap in H80.
sep lifts (2::3::1::4::nil)%nat in H80.
eapply ASlots_fold_any_idx_frm in H80; [idtac | eauto..]. 
sep lifts (6::7::1::nil)%nat in H80.
eapply fold_Acnode in H80.
sep lifts (1::6::7::8::9::nil)%nat in H80.
eapply fold_ACSpace  in H80; [idtac | eauto..].
sep lifts (5::1::6::nil)%nat in H80. 
eapply ACSpaceAarray_fold_any_idx_frm in H80; [idtac | eauto; try lia..]. 
sep lifts (2::1::3::4::nil)%nat in H80.
eapply fold_AOSCSpacePrioTbl1 in H80; [idtac | eauto; try lia..].
sep_lifts_trms_in H80 (aemp_isr_is).  
eapply aemp_isr_elim in H80.
sep_lifts_trms_in H80 (Aisr, Ais, A_isr_is_prop).
eapply elim_a_isr_is_prop in H80. 
exact H80.
rewrite nth_val_imp_nth_val'_2. rewrite H79. eauto.
rewrite Hlenv'76. lia. 
eauto.
unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
eauto.
assert (Hcases: 
not (nth_val' (Z.to_nat (Int.unsigned v'63))
 (v'102 ++ Vptr (b0, i9) :: v'103) <> Vnull)\/
(nth_val' (Z.to_nat (Int.unsigned v'63))
 (v'102 ++ Vptr (b0, i9) :: v'103) <> Vnull)) by tauto.
destruct Hcases as [Hfail|Hsucc1].


eapply seq_rule.  
eapply calle_rule_lvar'.

unfold Cap_spec.
simpl. unfold ucos_CNode_Delete_spec.
eauto.
intros.
eapply rvl_elim. sep get rv.
rewrite Hitrue. auto.
eapply rvl_elim. sep get rv.
eapply rvl_nil.
intros. unfold getasrt.
unfold ucos_CNode_DeletePre.
unfold ucos_CNode_DeletePre'.


sep normal. sep eexists.  
sep cancel Aie. sep cancel Aier.
sep cancel Aisr. sep cancel Ais.
sep cancel Acs. sep cancel Aop.
sep split.
sep cancel p_local.
sep cancel AOSCSpacePrioTbl.
sep cancel 31%nat 1%nat.  
exact H80.
go. eauto. eauto.
simpl;eauto. 
simpl;eauto. 
go.   
unfold AOSCSpaceObjectPointer.
go.
unfold CSpaceGVars.
go.
(* eapply GoodFrm_ACSpaceAarrayTptr. *)
unfold retpost.
unfold ucos_CNode_DeletePost.  unfold getasrt. 
unfold ucos_CNode_DeletePost'.
intros. sep destruct H80.

sep lifts (14::nil)%nat in H80.
eapply disj_split in H80.
destruct H80;  sep split in H80. 
rewrite H82. eauto.
eapply disj_split in H80.
destruct H80;  sep split in H80. 
rewrite H95. eauto.
eapply disj_split in H80.
destruct H80;  sep split in H80. 
rewrite H97. eauto.
rewrite H97. eauto.

simpl.
rewrite Hitrue. auto.

unfold getasrt, ucos_CNode_DeletePost,ucos_CNode_DeletePost'.
intros. sep destruct H80.
eexists.
sep cancel p_local. simpl. auto.
unfold getasrt. 
unfold ucos_CNode_DeletePre.
unfold ucos_CNode_DeletePre'.

intros. sep destruct H80. eexists.
sep cancel p_local. simpl. auto.
(*IF (ios_cap_defs.i ′ ==ₑ ′ CNODE_NONE_FAULT)*)
unfold getasrt, ucos_CNode_DeletePost,ucos_CNode_DeletePost'.
hoare_split_pure_all.
inverts H84.
simpl in H80, H81.
apply sym_eq in H80.
apply sym_eq in H81.
inverts H80. inverts H81. 


(*1 case*)
eapply backward_rule1.
intros.
sep lift 9%nat in H80.
apply disj_split in H80.
exact H80.
apply disj_rule.
hoare_split_pure_all.
inverts H81.
hoare forward.
hoare_split_pure_all.
clear - H81.
unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H81.
unfold val_inj in H81.
assert(Int.eq ($9) ($0) = false).
clear - H81.
int auto.
destruct (Int.eq ($ 9) ($ 0)).
tryfalse.
destruct H81.
tryfalse.
(*ELSE failure*)
hoare_split_pure_all.

eapply seq_rule.
eapply forward_rule2.
hoare_lifts_trms_pre (Aop).
eapply excrit1_rule'_ISnil_ISRemp'''_lg.
intros. 

sep lifts (4::2::5::nil)%nat in H86.
eapply add_aemp_isr_is_prop in H86.
eapply add_isr_is_prop in H86. 
unfold OldOSInvWL.
sep normal. sep eexists.
try unfold AOSTCBList;unfold_dll.
unfold CapabilityInv.
unfold AOSCSpaceCapParent.
sep normal. sep eexists.
sep cancel AOSCSpacePrioTbl.
sep cancel AOSCSpaceObjectPointer.
sep cancel CSpaceGVars. 
sep cancel CapParent. sep cancel AOSMapTbl.
sep cancel AOSUnMapTbl. sep cancel AOSTCBPrioTbl.
sep cancel AOSRdyTblGrp. sep cancel AOSTime.
sep cancel APthreadAttr. sep cancel EvtInv.
sep cancel IntInv. sep cancel TmrInv.
sep cancel CoreCommuInv. sep cancel PartitionInv.
sep cancel Acs. sep cancel Aier. sep cancel Ais.
sep cancel Aisr. sep cancel Aie. sep cancel p_local.
sep cancel Astruct. sep cancel dllseg.
sep cancel dllseg. sep cancel AOSTCBFreeList.
sep cancel OSTCBList. sep cancel OSTCBCur.
sep cancel AGVars.
instantiate(1:=LV func_capability @ long |-> (V$ x) **
  LV func_capType @ char_t |-> Vint32 v'62 **
  LV destTask_Prio @ char_t |-> Vint32 v'63 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_DELETE_FAILURE) **
         LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i9) **
         LV y @ char_t |-> Vint32 i3 **
         A_dom_lenv
           ((func_capability, long)
            :: (func_capType, char_t)
               :: (destTask_Prio, char_t)
                  :: (pCSpace, CSPACE ∗)
                     :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
sep auto; eauto.
split. eauto.
go.
go.
go.
eauto.

(*ELSE failure case*)
hoare abscsq. 
Hint Resolve noabs_oslinv.
go. 
eapply user_cnode_delete_absimp_failure.
can_change_aop_solver.
hoare forward.

destruct H81.  sep split in H81. 
clear - H84.
unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H84.
unfold val_inj in H84.
assert(Int.eq ($9) ($0) = false).
int auto.
  Optimize Proof.
  Optimize Heap.
destruct (Int.eq ($ 9) ($ 0)).
tryfalse.
destruct H84.
tryfalse.

sep split in H81.
exact H81.

hoare_split_pure_all.
rename H81 into Hnew_capability.
(*更新了ucoscnodemutate_post后直接可以找到矛盾条件，可以不用再证后面的内容了*)
(*但由于v'47和原来的表不能联系起来，仍然不能这么证明，还要用原来的方法证明*)
(*更新了ucoscnodemutate_post后v'47和原来的表可以联系起来了，可以直接找矛盾*)
destruct H80.  destruct H81.
clear -H84 Hfail.
tauto.

(*Hsucc1 case*)

assert (Hcasesfuncap: (not (Int.unsigned ($ x) < SLOT_NUM) \/ Int.unsigned ($ x) < SLOT_NUM)) by tauto.
destruct Hcasesfuncap as [Hfail|Hsucc2].

eapply seq_rule.  
eapply calle_rule_lvar'.

unfold Cap_spec.
simpl. unfold ucos_CNode_Delete_spec.
eauto.
intros.
eapply rvl_elim. sep get rv.
rewrite Hitrue. auto.
eapply rvl_elim. sep get rv.
eapply rvl_nil.
intros. unfold getasrt.
unfold ucos_CNode_DeletePre.
unfold ucos_CNode_DeletePre'.


sep normal. sep eexists.  
sep cancel Aie. sep cancel Aier.
sep cancel Aisr. sep cancel Ais.
sep cancel Acs. sep cancel Aop.
sep split.
sep cancel p_local.
sep cancel AOSCSpacePrioTbl.
sep cancel 31%nat 1%nat.  
exact H80.
go. eauto. eauto.
simpl;eauto. 
simpl;eauto. 
go.   
unfold AOSCSpaceObjectPointer.
go.
unfold CSpaceGVars.
go.
(* eapply GoodFrm_ACSpaceAarrayTptr. *)
unfold retpost.
unfold ucos_CNode_DeletePost.  unfold getasrt. 
unfold ucos_CNode_DeletePost'.
intros. sep destruct H80.

sep lifts (14::nil)%nat in H80.
eapply disj_split in H80.
destruct H80;  sep split in H80. 
rewrite H82. eauto.
eapply disj_split in H80.
destruct H80;  sep split in H80. 
rewrite H95. eauto.
eapply disj_split in H80.
destruct H80;  sep split in H80. 
rewrite H97. eauto.
rewrite H97. eauto.

simpl.
rewrite Hitrue. auto.

unfold getasrt, ucos_CNode_DeletePost,ucos_CNode_DeletePost'.
intros. sep destruct H80.
eexists.
sep cancel p_local. simpl. auto.
unfold getasrt. 
unfold ucos_CNode_DeletePre.
unfold ucos_CNode_DeletePre'.

intros. sep destruct H80. eexists.
sep cancel p_local. simpl. auto.
(*IF (ios_cap_defs.i ′ ==ₑ ′ CNODE_NONE_FAULT)*)
unfold getasrt, ucos_CNode_DeletePost,ucos_CNode_DeletePost'.
hoare_split_pure_all.
inverts H84.
simpl in H80, H81.
apply sym_eq in H80.
apply sym_eq in H81.
inverts H80. inverts H81. 


(*1 case*)
eapply backward_rule1.
intros.
sep lift 9%nat in H80.
apply disj_split in H80.
exact H80.
apply disj_rule.
hoare_split_pure_all.
inverts H81.
hoare forward.
hoare_split_pure_all.
clear - H81.
unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H81.
unfold val_inj in H81.
assert(Int.eq ($9) ($0) = false).
clear - H81.
int auto.
destruct (Int.eq ($ 9) ($ 0)).
tryfalse.
destruct H81.
tryfalse.
(*ELSE failure*)
hoare_split_pure_all.

eapply seq_rule.
eapply forward_rule2.
hoare_lifts_trms_pre (Aop).
eapply excrit1_rule'_ISnil_ISRemp'''_lg.
intros. 

sep lifts (4::2::5::nil)%nat in H86.
eapply add_aemp_isr_is_prop in H86.
eapply add_isr_is_prop in H86. 
unfold OldOSInvWL.
sep normal. sep eexists.
try unfold AOSTCBList;unfold_dll.
unfold CapabilityInv.
unfold AOSCSpaceCapParent.
sep normal. sep eexists.
sep cancel AOSCSpacePrioTbl.
sep cancel AOSCSpaceObjectPointer.
sep cancel CSpaceGVars. 
sep cancel CapParent. sep cancel AOSMapTbl.
sep cancel AOSUnMapTbl. sep cancel AOSTCBPrioTbl.
sep cancel AOSRdyTblGrp. sep cancel AOSTime.
sep cancel APthreadAttr. sep cancel EvtInv.
sep cancel IntInv. sep cancel TmrInv.
sep cancel CoreCommuInv. sep cancel PartitionInv.
sep cancel Acs. sep cancel Aier. sep cancel Ais.
sep cancel Aisr. sep cancel Aie. sep cancel p_local.
sep cancel Astruct. sep cancel dllseg.
sep cancel dllseg. sep cancel AOSTCBFreeList.
sep cancel OSTCBList. sep cancel OSTCBCur.
sep cancel AGVars.
instantiate(1:=LV func_capability @ long |-> (V$ x) **
  LV func_capType @ char_t |-> Vint32 v'62 **
  LV destTask_Prio @ char_t |-> Vint32 v'63 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_DELETE_FAILURE) **
         LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i9) **
         LV y @ char_t |-> Vint32 i3 **
         A_dom_lenv
           ((func_capability, long)
            :: (func_capType, char_t)
               :: (destTask_Prio, char_t)
                  :: (pCSpace, CSPACE ∗)
                     :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
sep auto; eauto.
split. eauto.
go.
go.
go.
eauto.

(*ELSE failure case*)
hoare abscsq. 
Hint Resolve noabs_oslinv.
go. 
eapply user_cnode_delete_absimp_failure.
can_change_aop_solver.
hoare forward.

destruct H81.  sep split in H81. 
clear - H84.
unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H84.
unfold val_inj in H84.
assert(Int.eq ($9) ($0) = false).
int auto.
  Optimize Proof.
  Optimize Heap.
destruct (Int.eq ($ 9) ($ 0)).
tryfalse.
destruct H84.
tryfalse.

sep split in H81.
exact H81.

hoare_split_pure_all.

  (*2 case*)
eapply backward_rule1.
intros.
apply disj_split in H84.
exact H84.
apply disj_rule.
hoare_split_pure_all.
inverts H86.
hoare forward.
hoare_split_pure_all.
clear - H86.
unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H86.
unfold val_inj in H86.
assert(Int.eq ($9) ($0) = false).
clear - H86.
int auto.
destruct (Int.eq ($ 9) ($ 0)).
tryfalse.
destruct H86.
tryfalse.
hoare_split_pure_all.
eapply seq_rule.
eapply forward_rule2.
hoare_lifts_trms_pre (Aop).
eapply excrit1_rule'_ISnil_ISRemp'''_lg.
intros. 
sep lifts (4::2::5::nil)%nat in H88.
eapply add_aemp_isr_is_prop in H88. 
eapply add_isr_is_prop in H88. 
unfold OldOSInvWL.
sep normal. sep eexists.
try unfold AOSTCBList;unfold_dll.
unfold CapabilityInv.
unfold AOSCSpaceCapParent.
sep normal. sep eexists.
sep cancel AOSCSpacePrioTbl.
sep cancel AOSCSpaceObjectPointer.
sep cancel CSpaceGVars. 
sep cancel CapParent. sep cancel AOSMapTbl.
sep cancel AOSUnMapTbl. sep cancel AOSTCBPrioTbl.
sep cancel AOSRdyTblGrp. sep cancel AOSTime.
sep cancel APthreadAttr. sep cancel EvtInv.
sep cancel IntInv. sep cancel TmrInv.
sep cancel CoreCommuInv. sep cancel PartitionInv.
sep cancel Acs. sep cancel Aier. sep cancel Ais.
sep cancel Aisr. sep cancel Aie. sep cancel p_local.
sep cancel Astruct. sep cancel dllseg.
sep cancel dllseg. sep cancel AOSTCBFreeList.
sep cancel OSTCBList. sep cancel OSTCBCur.
sep cancel AGVars.
instantiate(1:=LV func_capability @ long |-> (V$ x) **
  LV func_capType @ char_t |-> Vint32 v'62 **
  LV destTask_Prio @ char_t |-> Vint32 v'63 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_DELETE_FAILURE) **
         LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i9) **
         LV y @ char_t |-> Vint32 i3 **
         A_dom_lenv
           ((func_capability, long)
            :: (func_capType, char_t)
               :: (destTask_Prio, char_t)
                  :: (pCSpace, CSPACE ∗)
                     :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
sep auto; eauto.
split. eauto.
go.
go.
go.
eauto.
(*ELSE failure case*)
hoare abscsq. 
Hint Resolve noabs_oslinv.
go. 
eapply user_cnode_delete_absimp_failure.
can_change_aop_solver.
hoare forward.

destruct H86.  sep split in H80. 
clear - H84.
unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H84.
unfold val_inj in H84.
assert(Int.eq ($9) ($0) = false).
int auto.
destruct (Int.eq ($ 9) ($ 0)).
tryfalse.
destruct H84.
tryfalse.
sep split in H80.
exact H80.

destruct H80.
tryfalse.

(*Hsucc2 case*)
hoare_split_pure_all.
eapply backward_rule1.
intros.
sep_lifts_trms_in H81 AOSCSpacePrioTbl.
eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'63)) in H81.
exact H81.

unfold AOSCSpacePrioTbl in H81.
sep split in H81.
destruct H82.
destruct H90.
rewrite H90. lia.
eauto.

hoare_split_pure_all.
simpljoin.
unfold ACSpace.
destruct v'105, p, p, p, v'109.
unfold Acnode. 
destruct c, p. 

 
  hoare_split_pure_all.
  simpljoin.
  rename H92 into Hi20range.
  eapply backward_rule1.
  intros.
  sep lifts(7::nil)%nat in H92.
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned ($ x))) in H92; eauto. 
  clear -Hsucc2.  unfold SLOT_NUM. unfold SLOT_NUM in Hsucc2.
  lia. 
  hoare_split_pure_all.

  unfold ACap. destruct v'111, c, p.  
  hoare_split_pure_all.

  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H96. 
  eapply fold_Cap in H96.
  sep lifts (2::3::1::4::nil)%nat in H96.
  eapply ASlots_fold_any_idx_frm in H96; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H96.
  eapply fold_Acnode in H96.
  sep lifts (1::6::7::8::9::nil)%nat in H96.
  eapply fold_ACSpace  in H96; [idtac | eauto..]. 
  sep lifts (5::1::6::nil)%nat in H96. 
  eapply ACSpaceAarray_fold_any_idx_frm in H96; [idtac | eauto; try lia..]. 
  (*sep lifts (2::1::3::4::nil)%nat in H96.
  eapply fold_AOSCSpacePrioTbl1 in H96; [idtac | eauto; try lia..].
  *)
  exact H96. eauto. clear -Hsucc2.
  unfold SLOT_NUM. unfold SLOT_NUM in Hsucc2. lia. 
  
  destruct H93.
  eauto. 
  destruct H93.
  eauto.
  eauto. 
 
  eapply seq_rule.  
  eapply calle_rule_lvar'.
  
  unfold Cap_spec.
  simpl. unfold ucos_CNode_Delete_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_CNode_DeletePre.
  unfold ucos_CNode_DeletePre'.
  
  
  sep normal. sep eexists.  
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  sep split.
  sep cancel p_local.
  sep lifts (2::1::3::4::nil)%nat in H96.
  eapply fold_AOSCSpacePrioTbl1 in H96; [idtac | eauto; try lia..].

  sep cancel AOSCSpacePrioTbl.
  sep pauto. rewrite H81. 
  eapply nth_val_length_imp;eauto. 
  go. eauto. eauto.
  simpl;eauto. 
  simpl;eauto. 
  go.   
  unfold AOSCSpaceObjectPointer.
  go.
  unfold CSpaceGVars.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold ucos_CNode_DeletePost.  unfold getasrt. 
  unfold ucos_CNode_DeletePost'.
  intros. sep destruct H96.
  
  sep lifts (14::nil)%nat in H96.
  eapply disj_split in H96.
  destruct H96;  sep split in H96. 
  rewrite H98. eauto.
  eapply disj_split in H96.
  destruct H96;  sep split in H96. 
  rewrite H111. eauto.
  eapply disj_split in H96.
  destruct H96;  sep split in H96. 
  rewrite H113. eauto.
  rewrite H113. eauto.
  
  simpl.
  rewrite Hitrue. auto.
  
  unfold getasrt, ucos_CNode_DeletePost,ucos_CNode_DeletePost'.
  intros. sep destruct H96.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. 
  unfold ucos_CNode_DeletePre.
  unfold ucos_CNode_DeletePre'.
  
  intros. sep destruct H96. eexists.
  sep cancel p_local. simpl. auto.
  (*IF (ios_cap_defs.i ′ ==ₑ ′ CNODE_NONE_FAULT)*)
  unfold getasrt, ucos_CNode_DeletePost,ucos_CNode_DeletePost'.
  hoare_split_pure_all.
  inverts H100.
  simpl in H96, H97.
  apply sym_eq in H96.
  apply sym_eq in H97.
  inverts H96. inverts H97. 
  
  
  (*1 case*)
  eapply backward_rule1.
  intros.
  sep lift 9%nat in H96.
  apply disj_split in H96.
  exact H96.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H97.
  hoare forward.
  hoare_split_pure_all.
  clear - H97.
  unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H97.
  unfold val_inj in H97.
  assert(Int.eq ($9) ($0) = false).
  clear - H97.
  int auto.
  Optimize Proof.
  Optimize Heap.
  destruct (Int.eq ($ 9) ($ 0)).
  tryfalse.
  destruct H97.
  tryfalse.
  (*ELSE failure*)
  hoare_split_pure_all.
  
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  
  sep lifts (4::2::5::nil)%nat in H101.
  eapply add_aemp_isr_is_prop in H101.
  eapply add_isr_is_prop in H101. 
  unfold OldOSInvWL.
  sep normal. sep eexists.
  try unfold AOSTCBList;unfold_dll.
  unfold CapabilityInv.
  unfold AOSCSpaceCapParent.
  sep normal. sep eexists.
  sep cancel AOSCSpacePrioTbl.
  sep cancel AOSCSpaceObjectPointer.
  sep cancel CSpaceGVars. 
  sep cancel CapParent. sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl. sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp. sep cancel AOSTime.
  sep cancel APthreadAttr. sep cancel EvtInv.
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. sep cancel AOSTCBFreeList.
  sep cancel OSTCBList. sep cancel OSTCBCur.
  sep cancel AGVars.
  instantiate(1:=LV func_capability @ long |-> (V$ x) **
    LV func_capType @ char_t |-> Vint32 v'62 **
    LV destTask_Prio @ char_t |-> Vint32 v'63 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_DELETE_FAILURE) **
           LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i9) **
           LV y @ char_t |-> Vint32 i3 **
           A_dom_lenv
             ((func_capability, long)
              :: (func_capType, char_t)
                 :: (destTask_Prio, char_t)
                    :: (pCSpace, CSPACE ∗)
                       :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  go.
  eauto.
  
  (*ELSE failure case*)
  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply user_cnode_delete_absimp_failure.
  can_change_aop_solver.
  hoare forward.
  
  destruct H97.  sep split in H92. 
  clear - H93.
  unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H93.
  unfold val_inj in H93.
  assert(Int.eq ($9) ($0) = false).
  int auto.
  destruct (Int.eq ($ 9) ($ 0)).
  tryfalse.
  destruct H93.
  tryfalse.
  
  sep split in H92.
  exact H92.
  
  hoare_split_pure_all.
  
    (*2 case*)
  eapply backward_rule1.
  intros.
  apply disj_split in H100.
  exact H100.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H101.
  hoare forward.
  hoare_split_pure_all.
  clear - H101.
  unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H101.
  unfold val_inj in H101.
  assert(Int.eq ($9) ($0) = false).
  clear - H101.
  int auto.
  destruct (Int.eq ($ 9) ($ 0)).
  tryfalse.
  destruct H101.
  tryfalse.
  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (4::2::5::nil)%nat in H103.
  eapply add_aemp_isr_is_prop in H103. 
  eapply add_isr_is_prop in H103. 
  unfold OldOSInvWL.
  sep normal. sep eexists.
  try unfold AOSTCBList;unfold_dll.
  unfold CapabilityInv.
  unfold AOSCSpaceCapParent.
  sep normal. sep eexists.
  sep cancel AOSCSpacePrioTbl.
  sep cancel AOSCSpaceObjectPointer.
  sep cancel CSpaceGVars. 
  sep cancel CapParent. sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl. sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp. sep cancel AOSTime.
  sep cancel APthreadAttr. sep cancel EvtInv.
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. sep cancel AOSTCBFreeList.
  sep cancel OSTCBList. sep cancel OSTCBCur.
  sep cancel AGVars.
  instantiate(1:=LV func_capability @ long |-> (V$ x) **
    LV func_capType @ char_t |-> Vint32 v'62 **
    LV destTask_Prio @ char_t |-> Vint32 v'63 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_DELETE_FAILURE) **
           LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i9) **
           LV y @ char_t |-> Vint32 i3 **
           A_dom_lenv
             ((func_capability, long)
              :: (func_capType, char_t)
                 :: (destTask_Prio, char_t)
                    :: (pCSpace, CSPACE ∗)
                       :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  go.
  eauto.
  (*ELSE failure case*)
  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply user_cnode_delete_absimp_failure.
  can_change_aop_solver.
  hoare forward.
  
  destruct H101.  sep split in H92. 
  clear - H93.
  unfold CNODE_DELETE_FAILURE, CNODE_NONE_FAULT in H93.
  unfold val_inj in H93.
  assert(Int.eq ($9) ($0) = false).
  int auto.
  destruct (Int.eq ($ 9) ($ 0)).
  tryfalse.
  destruct H93.
  tryfalse.
  sep split in H92.
  exact H92.
  
  destruct H92.
  tryfalse.

eapply backward_rule1.
intros.
sep lift 2%nat in H92.
apply disj_split in H92.
exact H92.
apply disj_rule.
hoare_split_pure_all.

inverts H101.
hoare forward.
hoare_split_pure_all.
clear H101.

rewrite H82 in H48.
  lets bak_23: H48.
  unfolds in H48.
  destruct H48.
  assert(Ha: 0 <= Int.unsigned v'63 < 64).
  clear -Hx.
  int auto. 
  Optimize Proof.
  Optimize Heap.
  assert(Hb: nth_cspace_val ∘ (Int.unsigned v'63)
  (v'104 ++ (i18, i19, l1, i16, l0, v1, i15) :: v'106)  = 
  Some (i18, i19, l1, i16, l0, v1, i15)).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.

  (*rewrite <- app_assoc_reverse in H48.*)
  lets Hc: H48 Hb.
  destruct Hc. destruct H103. destruct H103. destruct H104.
  
  rewrite H82 in H97.

  (*
  
  <<<
  rewrite get_capability_nth_mth_cspace_length_imp in H75; eauto.
  destruct H76.
  rewrite e in H75.
  inverts H75.

  rewrite  H49 in Hnew_capability.
  assert(v3 = v'74).
  {
   rewrite list_trans_1 in Hnew_capability.
   rewrite get_capability_nth_mth_cspace_length_imp in Hnew_capability; eauto.
   inverts Hnew_capability. auto.
   rewrite app_length. simpl.
   rewrite H51, H52.
   rewrite S_add_sub_S.
   clear -Hsrc_dest_lt.
   lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; try (int auto).
  }
  subst v'74.
  *)

hoare_lifts_trms_pre (Aop, cspaceid).
hoare abscsq. 
Hint Resolve noabs_oslinv.
go. 

eapply user_cnode_delete_absimp_succ_category.
can_change_aop_solver.
unfold AOSCSpacePrioTbl.
can_change_aop_solver.
eapply can_change_aop_ACSpaceAarrayTptr.
unfold AOSCSpaceObjectPointer.
can_change_aop_solver.
unfold CSpaceGVars.
can_change_aop_solver.
eauto.
eauto.
eauto.
eauto.

(*add two assertions back*)
eapply backward_rule1.
intros. 
sep lifts (6::4::7::nil)%nat in H106.
eapply add_aemp_isr_is_prop in H106.
eapply add_isr_is_prop in H106. 
exact H106.

(*EXIT success*)
eapply seq_rule.
hoare forward prim.
sep cancel Aier.
sep cancel APthreadAttr.
sep cancel EvtInv.
sep cancel CoreCommuInv.
sep cancel p_local.
try unfold AOSTCBList;unfold_dll.
unfold CapabilityInv.
unfold AOSCSpaceCapParent.
sep normal. sep eexists.
sep cancel AOSCSpacePrioTbl.
sep cancel CSpaceGVars.
sep cancel AOSCSpaceObjectPointer.
sep cancel CapParent.
sep cancel OSTCBCur.
sep cancel OSTCBList.
sep cancel dllseg.
sep cancel dllseg.
sep cancel tcbdllflag.
sep cancel Astruct.
sep cancel cspaceid.
sep pauto.

eauto. eauto. eauto.
go.
{
  eapply Capability_wellform_descendents_update_cap; eauto.
  eapply Capability_wellform_descendents_update_type; eauto.

}

{
  eapply taskPrioProp_update_slots_cap_remain.
  eapply taskPrioProp_update_slots_type_remain.
  eauto.
}

{
  unfold Int.zero.
  assert(v'128 = v2).
  {
    unfold get_capability in H97.
    rewrite nth_cspace_eq_nth_cspace_val in Hb.
    unfold nat_of_Z in Hb.
    rewrite Hb in H97.
    rewrite H94 in H97.
    inverts H97. auto.
  }
  subst v'128.
  rewrite H82.
  rewrite update_nth_list_eq_update_nth_slots.
  rewrite update_nth_list_eq_update_nth_slots.
  eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
  
  eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
  rewrite nth_cspace_length_imp; eauto.
  unfold update_nth_cspace_slots_type.
  rewrite nth_cspace_length_imp; eauto.
  rewrite H94. 
  rewrite <- update_nth_list_eq_update_nth_slots.
  rewrite update_nth_cspace_eq; eauto.
  rewrite app_length. simpl.
  rewrite H84, H85. rewrite S_add_sub_S.
  clear -destlt64. unfold ios_cap_defs.OS_LOWEST_PRIO in *.
  lia.
  clear -destlt64. unfold ios_cap_defs.OS_LOWEST_PRIO in *.
  lia.
  rewrite update_nth_slots_eq_update_slots_type.
  rewrite update_nth_slots_eq; eauto.
  rewrite H87.
  clear -Hsucc2. 
  unfold SLOT_NUM in *. lia.
  rewrite get_set_eq; eauto.
}


{
  eapply RL_Cap_Parent_Child_remain.
  eapply RL_Cap_Parent_Child_update_slots_type_remain.
  eauto.
}
{
  unfold nat_of_Z in Hb.
  rewrite nth_cspace_eq_nth_cspace_val in Hb.
  rewrite update_nth_list_eq_update_nth_slots.
  rewrite update_nth_list_eq_update_nth_slots.
  eapply RLH_CapParent_update_slots_cap_remain; eauto.
  eapply RLH_CapParent_update_slots_type_remain; eauto.
  {
    instantiate(7:=update_nth_cspace_slots_type
    (Z.to_nat (Int.unsigned v'63))
    (Z.to_nat (Int.unsigned ($ x)))
    (v'104 ++
     (i18, i19, l1, i16, l0, v1, i15)
     :: v'106) ($ SLOT_NULL_CAP)).
    unfold update_nth_cspace_slots_type.
    rewrite nth_cspace_length_imp; eauto.
    rewrite H94. 
    rewrite <- update_nth_list_eq_update_nth_slots.
    rewrite update_nth_cspace_eq; eauto.
    rewrite app_length. simpl.
    rewrite H84, H85. rewrite S_add_sub_S.
    clear -destlt64. unfold ios_cap_defs.OS_LOWEST_PRIO in *.
    lia.
    clear -destlt64. unfold ios_cap_defs.OS_LOWEST_PRIO in *.
    lia.
  }
  rewrite update_nth_slots_eq_update_slots_type.
  rewrite update_nth_slots_eq; eauto.
  rewrite H87.
  clear -Hsucc2. 
  unfold SLOT_NUM in *. lia.
  rewrite get_set_eq; eauto.
} 
eauto.
go.
hoare forward.
hoare_split_pure_all.
rewrite Int.eq_true in H101.
unfold val_inj in H101.
destruct H101; tryfalse.
destruct H101. sep split in H93. auto.
sep split in H93.
clear -H96.
rewrite Int.eq_true in H96.
unfold val_inj in H96.
destruct H96; tryfalse.

(*OBJECT*)
hoare_split_pure_all.

inverts H101.
hoare forward.
hoare_split_pure_all.
clear H101.

rewrite H82 in H48.
  lets bak_23: H48.
  unfolds in H48.
  destruct H48.
  assert(Ha: 0 <= Int.unsigned v'63 < 64).
  clear -Hx.
  int auto. 
  Optimize Proof.
  Optimize Heap.
  assert(Hb: nth_cspace_val ∘ (Int.unsigned v'63)
  (v'104 ++ (i18, i19, l1, i16, l0, v1, i15) :: v'106)  = 
  Some (i18, i19, l1, i16, l0, v1, i15)).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.

  (*rewrite <- app_assoc_reverse in H48.*)
  lets Hc: H48 Hb.
  destruct Hc. destruct H103. destruct H103. destruct H104.
  
  rewrite H82 in H97.

  (*
  
  <<<
  rewrite get_capability_nth_mth_cspace_length_imp in H75; eauto.
  destruct H76.
  rewrite e in H75.
  inverts H75.

  rewrite  H49 in Hnew_capability.
  assert(v3 = v'74).
  {
   rewrite list_trans_1 in Hnew_capability.
   rewrite get_capability_nth_mth_cspace_length_imp in Hnew_capability; eauto.
   inverts Hnew_capability. auto.
   rewrite app_length. simpl.
   rewrite H51, H52.
   rewrite S_add_sub_S.
   clear -Hsrc_dest_lt.
   lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; try (int auto).
  }
  subst v'74.
  *)

hoare_lifts_trms_pre (Aop, cspaceid).
hoare abscsq. 
Hint Resolve noabs_oslinv.
go. 

eapply user_cnode_delete_absimp_succ_object.
can_change_aop_solver.
unfold AOSCSpacePrioTbl.
can_change_aop_solver.
eapply can_change_aop_ACSpaceAarrayTptr.
unfold AOSCSpaceObjectPointer.
can_change_aop_solver.
unfold CSpaceGVars.
can_change_aop_solver.
eauto.
eauto.
eauto.
eauto.

(*add two assertions back*)
eapply backward_rule1.
intros. 
sep lifts (6::4::7::nil)%nat in H106.
eapply add_aemp_isr_is_prop in H106.
eapply add_isr_is_prop in H106. 
exact H106.

(*EXIT success*)
eapply seq_rule.
hoare forward prim.
sep cancel Aier.
sep cancel APthreadAttr.
sep cancel EvtInv.
sep cancel CoreCommuInv.
sep cancel p_local.
try unfold AOSTCBList;unfold_dll.
unfold CapabilityInv.
unfold AOSCSpaceCapParent.
sep normal. sep eexists.
sep cancel AOSCSpacePrioTbl.
sep cancel CSpaceGVars.
sep cancel AOSCSpaceObjectPointer.
sep cancel CapParent.
sep cancel OSTCBCur.
sep cancel OSTCBList.
sep cancel dllseg.
sep cancel dllseg.
sep cancel tcbdllflag.
sep cancel Astruct.
sep cancel cspaceid.
sep pauto.

eauto. eauto. eauto.
go.
{
  eapply Capability_wellform_descendents_update_cap; eauto.
  eapply Capability_wellform_descendents_update_type; eauto.

}

{
  eapply taskPrioProp_update_slots_cap_remain.
  eapply taskPrioProp_update_slots_type_remain.
  eauto.
}

{
  unfold Int.zero.
  assert(v'127 = i22).
  {
  unfold get_capability in H97.
  rewrite nth_cspace_eq_nth_cspace_val in Hb.
  unfold nat_of_Z in Hb.
  rewrite Hb in H97.
  rewrite H94 in H97.
  inverts H97. auto.
  }
  subst i22.
  rewrite H82.
  rewrite update_nth_list_eq_update_nth_slots.
  rewrite update_nth_list_eq_update_nth_slots.
  eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
  
  eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
  rewrite nth_cspace_length_imp; eauto.
  unfold update_nth_cspace_slots_type.
  rewrite nth_cspace_length_imp; eauto.
  rewrite H94. 
  rewrite <- update_nth_list_eq_update_nth_slots.
  rewrite update_nth_cspace_eq; eauto.
  rewrite app_length. simpl.
  rewrite H84, H85. rewrite S_add_sub_S.
  clear -destlt64. unfold ios_cap_defs.OS_LOWEST_PRIO in *.
  lia.
  clear -destlt64. unfold ios_cap_defs.OS_LOWEST_PRIO in *.
  lia.
  rewrite update_nth_slots_eq_update_slots_type.
  rewrite update_nth_slots_eq; eauto.
  rewrite H87.
  clear -Hsucc2. 
  unfold SLOT_NUM in *. lia.
  rewrite get_set_eq; eauto.
}


{
  eapply RL_Cap_Parent_Child_remain.
  eapply RL_Cap_Parent_Child_update_slots_type_remain.
  eauto.
}
{
  unfold nat_of_Z in Hb.
  rewrite nth_cspace_eq_nth_cspace_val in Hb.
  rewrite update_nth_list_eq_update_nth_slots.
  rewrite update_nth_list_eq_update_nth_slots.
  eapply RLH_CapParent_update_slots_cap_remain; eauto.
  eapply RLH_CapParent_update_slots_type_remain; eauto.
  {
    instantiate(7:=update_nth_cspace_slots_type
    (Z.to_nat (Int.unsigned v'63))
    (Z.to_nat (Int.unsigned ($ x)))
    (v'104 ++
     (i18, i19, l1, i16, l0, v1, i15)
     :: v'106) ($ SLOT_NULL_CAP)).
    unfold update_nth_cspace_slots_type.
    rewrite nth_cspace_length_imp; eauto.
    rewrite H94. 
    rewrite <- update_nth_list_eq_update_nth_slots.
    rewrite update_nth_cspace_eq; eauto.
    rewrite app_length. simpl.
    rewrite H84, H85. rewrite S_add_sub_S.
    clear -destlt64. unfold ios_cap_defs.OS_LOWEST_PRIO in *.
    lia.
    clear -destlt64. unfold ios_cap_defs.OS_LOWEST_PRIO in *.
    lia.
  }
  rewrite update_nth_slots_eq_update_slots_type.
  rewrite update_nth_slots_eq; eauto.
  rewrite H87.
  clear -Hsucc2. 
  unfold SLOT_NUM in *. lia.
  rewrite get_set_eq; eauto.
} 
eauto.
go.
hoare forward.
hoare_split_pure_all.
rewrite Int.eq_true in H101.
unfold val_inj in H101.
destruct H101; tryfalse.
destruct H101. sep split in H93. auto.
sep split in H93.
clear -H96.
rewrite Int.eq_true in H96.
unfold val_inj in H96.
destruct H96; tryfalse.
Unshelve. all: exact(Aemp).
Qed.


