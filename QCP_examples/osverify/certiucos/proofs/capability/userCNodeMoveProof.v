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
Require Import seplog_trm_tacs.
Require Import ios_int_tac.
Require Import CapRelLemmas.
Require Import gjb_common.
Require Import Aarray_new_common.

Import DeprecatedTactic.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.
Set Keyed Unification.
Definition EINVAL := 30%Z.

Lemma move_cap_absimp_invalid:
forall dest src captype v' sch P capability,
  can_change_aop P -> 
  (((Int.ltu (Int.repr OS_LOWEST_PRIO) dest = true) \/ 
  (Int.eq dest (Int.repr OS_LOWEST_PRIO) = true))
  \/ ((Int.ltu (Int.repr OS_LOWEST_PRIO) src = true) \/
    (Int.eq src (Int.repr OS_LOWEST_PRIO) = true))) ->
  absinfer sch ( <|| user_cnode_move_code ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P ).
Proof.
  infer_solver 0%nat.
Qed.  

Lemma move_cap_absimp_err:
forall dest src captype v' sch P capability,
  can_change_aop P -> 
  Int.ltu (Int.repr CAP_TASK_TYPE) captype = true ->
  absinfer sch ( <|| user_cnode_move_code ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P ).
Proof.
  infer_solver 1%nat.
Qed.

Lemma move_cap_absimp_err_slotnum:
forall dest src captype v' sch P capability,
  can_change_aop P -> 
  (Int.ltu (Int.repr CAP_TASK_TYPE) captype = false) ->
  absinfer sch ( <|| user_cnode_move_code ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P ).
Proof.
infer_solver 2%nat.
Qed.

Lemma move_cap_absimp_failure:
forall dest src captype v' sch P capability,
  can_change_aop P -> 
  absinfer sch ( <|| user_cnode_move_code ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr CNODE_MOVE_FAILURE))) ||> ** P ).
Proof.
  infer_solver 3%nat.
Qed.

Lemma move_cap_absimp_nocap:
forall dest src captype v' sch P capability,
  can_change_aop P -> 
  absinfer sch ( <|| user_cnode_move_code ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||> ** P ).
Proof.
infer_solver 4%nat.
Qed.

Lemma move_cap_absimp_succ_category:
forall dest src captype v' sch P capability dest_prio dest_slot_type dest_cap_content dest_cap_right dest_object_t cs cs' cs'' cs''' dest_cap_type
  dest_slots dest_childs src_slots src_childs src_prio src_cap_content src_cap_right  src_object_t src_slot_type index,
  can_change_aop P -> 
  get cs dest = Some (dest_slots, dest_childs, dest_prio) ->
  get cs src = Some (src_slots, src_childs, src_prio) ->
  nth_slots (Z.to_nat index) dest_slots =
               Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) ->
  nth_slots (Z.to_nat index) src_slots =
              Some (src_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, src_object_t))) ->
  cs' = CSpaceMod.set cs dest (update_nth_slots (Z.to_nat index) dest_slots (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, dest_object_t))), dest_childs, dest_prio) ->
  cs'' = CSpaceMod.set cs' src (update_nth_slots (Z.to_nat index) src_slots (src_slot_type, (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio) ->
  cs''' = CSpaceMod.set cs'' src (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots (src_slot_type, (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t)))) 
          ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, Int.repr 0, src_object_t))), src_childs, src_prio) ->
  absinfer sch ( <|| user_cnode_move_code ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') ||> ** Hcapspace cs ** P)
           ( <|| END (Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS))) ||> ** Hcapspace cs''' ** P ).
Proof.
infer_solver 9%nat.
Qed.

Lemma move_cap_absimp_succ_object:
forall dest src captype v' sch P capability dest_prio dest_slot_type dest_obj_right dest_dummy dest_dummy_1 cs cs' cs'' cs''' dest_cap_type
  dest_slots dest_childs src_slots src_childs src_prio src_obj_right src_dummy src_object_t src_slot_type index dest_idx,
  can_change_aop P -> 
  get cs dest = Some (dest_slots, dest_childs, dest_prio) ->
  get cs src = Some (src_slots, src_childs, src_prio) ->
  nth_slots (Z.to_nat dest_idx) dest_slots =
               Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, src_object_t))) ->
  nth_slots (Z.to_nat index) src_slots =
              Some (src_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, src_dummy, src_object_t))) ->
  cs' = CSpaceMod.set cs dest (update_nth_slots (Z.to_nat dest_idx) dest_slots (dest_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, dest_dummy_1, src_object_t))), dest_childs, dest_prio) ->
  cs'' = CSpaceMod.set cs' src (update_nth_slots (Z.to_nat index) src_slots (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) ->
  cs''' = CSpaceMod.set cs'' src (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull)))) 
          ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) ->
  absinfer sch ( <|| user_cnode_move_code ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') ||> ** Hcapspace cs ** P)
           ( <|| END (Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS))) ||> ** Hcapspace cs''' ** P ).
Proof.
infer_solver 10%nat.
Qed.

Lemma move_cap_absimp_succ_objectnot:
forall dest src captype v' sch P capability dest_prio cs cs' cs'' cs'''
  dest_slots dest_childs src_slots src_childs src_prio src_obj_right src_dummy src_object_t src_slot_type index ranindex dest_dummy_1 some_slot_type
  slots_vll11 slots_vll12 slots_vll21 endPtr src_cap_type,
  can_change_aop P -> 
  get cs dest = Some (dest_slots, dest_childs, dest_prio) ->
  get cs src = Some (src_slots, src_childs, src_prio) ->
  nth_slots (Z.to_nat index) src_slots =
      Some (src_slot_type, (src_cap_type, (src_obj_right, src_dummy, src_object_t))) ->
  dest_slots = (slots_vll11 ++ slots_vll12 ++ slots_vll21) ->
  length slots_vll11 = Z.to_nat(OBJ_POSITION) ->
  length (slots_vll11 ++ slots_vll12) = Z.to_nat(Int.unsigned endPtr) ->
 ( ~exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy,
      0 <= dest_idx < Z.of_nat (length slots_vll12) /\
      nth_slots (Z.to_nat dest_idx) slots_vll12 =
          Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, src_object_t)))) ->
  cs' = CSpaceMod.set cs dest (update_nth_slots (Z.to_nat ranindex) dest_slots (some_slot_type, (Int.repr CAP_OBJECT_TYPE, (src_obj_right, dest_dummy_1, src_object_t))), dest_childs, dest_prio) ->
  cs'' = CSpaceMod.set cs' src (update_nth_slots (Z.to_nat index) src_slots (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) ->
  cs''' = CSpaceMod.set cs'' src (update_nth_slots (Z.to_nat index) (update_nth_slots (Z.to_nat index) src_slots (src_slot_type, (Int.repr 0, (Int.repr 0, src_dummy, Vnull)))) 
          ((Int.repr SLOT_NULL_CAP), (Int.repr 0, (Int.repr 0, src_dummy, Vnull))), src_childs, src_prio) ->
  absinfer sch ( <|| user_cnode_move_code ((Vint32 dest) :: (Vint32 src) :: (Vint32 captype) :: (Vint32 capability) :: v') ||> ** Hcapspace cs ** P)
           ( <|| END (Some (Vint32 (Int.repr CNODE_MOVE_SUCCESS))) ||> ** Hcapspace cs''' ** P ).
Proof.
infer_solver 11%nat.
Qed.

Lemma UserCnodeMoveProof: 
  forall  tid vl p r, 
    Some p =
    BuildPreA' os_api user_cnode_move
    user_cnode_move_api vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api user_cnode_move
    user_cnode_move_api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api user_cnode_move = Some (t, d1, d2, s) /\
      {|Cap_spec, GetHPrio, OSLInv,  I, r, Afalse|}|-tid {{p ** (EX srcTask_Prio destTask_Prio, [|Some(Vint32 destTask_Prio) = nth_val 3%nat vl /\
      Some(Vint32 srcTask_Prio) = nth_val 2%nat vl /\ (Int.unsigned destTask_Prio < 63) /\ (Int.unsigned srcTask_Prio >= OS_N_SYS_TASKS)
      /\ (Int.unsigned srcTask_Prio < Int.unsigned destTask_Prio)|])}}s {{Afalse}}.
Proof.
  init_spec.
  simpl in H.
  destruct H. destruct H0. destruct H1.
  inverts H. inverts H0.
  destruct H5. 
  rename H0 into Hsrc_dest_lt.
  assert(Hi0lt63:Int.unsigned i0 < 63) by lia.
  (*The 1st If*)
  lzh_hoare_if; pure_auto.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply move_cap_absimp_invalid.
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
  exact H6. 
  apply H0.
  go.

  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply move_cap_absimp_err.
  can_change_aop_solver.
  eauto.
  hoare forward.

  assert (srclt63: Int.unsigned i0 < ios_cap_defs.OS_LOWEST_PRIO).
  unfold ios_cap_defs.OS_LOWEST_PRIO.
  auto.

  unfold CapabilityInv.
  pure intro.
  destruct v'25.
  unfold EvtInv.
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  unfold AGVars.
  hoare_split_pure_all.
  (*index ′ =ᶠ Check_Cap_Type (·func_capability ′, func_capType ′, srcTask_Prio ′·);ₛ*)
  destruct v'61.
  destruct v'62.
  destruct v'63.
  eapply backward_rule1.
  intros.
  
  sep_lifts_trms_in H37 (Aisr, Ais, A_isr_is_prop, aemp_isr_is).
  eapply elim_a_isr_is_prop in H37.
  eapply elim_aemp_isr_is_prop in H37. 
  exact H37. 
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold Check_Cap_Type_spec_weak.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  change Byte.max_unsigned with 255.
  assert(Int.unsigned i1 <=? 255 = true).
  clear -Hif_false0.
  change CAP_TASK_TYPE with 5 in Hif_false0.
  unfold Int.ltu in Hif_false0.
  destruct (zlt (Int.unsigned ($ 5)) (Int.unsigned i1)).
  try false.
  int auto.
  rewrite H38. auto.
  eapply rvl_elim. sep get rv.
  change Byte.max_unsigned with 255.
  assert(Int.unsigned i0 <=? 255 = true).
  clear -H3.
  int auto.
  rewrite H38. auto.
  eapply rvl_nil.
  intros.
  sep_lifts_trms_in H37 (ios_cap_defs.index).
  sep cancel ios_cap_defs.index.
  unfold getasrt.
  unfold Check_Cap_TypePre.
  unfold Check_Cap_TypePre'.  
  sep normal.
  sep eexists.
  sep cancel Aie. sep cancel Ais. sep cancel Acs. sep cancel Aisr. sep cancel Aier.
  sep cancel Aop.
  sep split.
  sep cancel AMqAttr.
  sep cancel ASeminfo.
  sep cancel APthreadMutex.
  sep cancel AOSCSpaceObjectPointer.
  sep cancel AOSTCBPrioTbl.  
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  exact H37.
  (*sep remember(1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::nil)%nat in H35.*)
  5:{
    simpl; eauto.
  }
  eauto.
  eauto.
  5:
  {
    unfold AOSCSpaceCapParent.    
    unfold CSpaceGVars.
    good_frm_sovler.
    (* eapply GoodFrm_ACSpaceAarrayTptr.     *)
  }
  eauto. eauto.
  simpl;eauto.
  simpl;eauto.
  apply retpost_CheckCapTypeWeakPost.
  unfold tl_vl_match; unfold type_val_match; pure_auto.
  {
    unfold getasrt.
    unfold Check_Cap_TypeWeakPost.
    unfold Check_Cap_TypePost''.
    intros.
    sep destruct H37. eexists.
    sep cancel p_local. simpl. auto.
  }
  {
    unfold getasrt.
    unfold Check_Cap_TypePre.
    unfold Check_Cap_TypePre'.
    intros.
    sep destruct H37. eexists.
    sep cancel p_local. simpl. auto.
  }

  unfold getasrt.
  unfold Check_Cap_TypeWeakPost.
  unfold Check_Cap_TypePost''.
  hoare_split_pure_all.
  inverts H42.
  simpl in H37, H39, H38.
  inverts H37. inverts H39. inverts H38.
  hoare normal pre; hoare_ex_intro.
  (*add A_isr... back*)
  eapply backward_rule1.
  intros.
  (* sep remember(1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::35::36::nil)%nat in H37. *)
  sep_lifts_trms_in H37 (Aisr, Ais).
  eapply add_a_isr_is_prop in H37.
  sep_lifts_trms_in H37 (Aisr, Ais, Aier).
  eapply add_aemp_isr_is_prop in H37.  
  exact H37. 

  eapply backward_rule1 with (p:=<||
  user_cnode_move_code (Vint32 i :: Vint32 v'64 :: Vint32 v'63 :: Vint32 v'62 :: v')
  ||>  **
  OldOSInvWL tid (logic_val (V$ 1)::logic_val (V$ __EvLoc_normal)
  :: logic_val Vnull
     :: logic_val Vnull :: logic_val Vnull :: nil) **
   aemp_isr_is **
   Aisr empisr ** Aier v'65 ** Aie false ** Ais nil ** Acs (true :: nil) **
   ([|Some v'61 = Some (V$ SLOT_NUM)|] \\//
   [|(exists ret, Some v'61 = Some (V$ ret) /\ 0 <= ret < 255) /\
     (Int.unsigned v'63 = CAP_FUNCTION_TYPE /\ Int.unsigned v'62 <= CAP_CHANNEL_CLASS \/
      (Int.unsigned v'63 = CAP_SEM_TYPE \/ Int.unsigned v'63 = CAP_MUTEX_TYPE \/ Int.unsigned v'63 = CAP_Q_TYPE) /\
      Int.unsigned v'62 < OS_USER_MAX_EVENTS / 3 \/ Int.unsigned v'63 = CAP_TASK_TYPE /\ Int.unsigned v'62 < OS_STAT_PRIO)|]) **
         LV func_capability @ long |-> Vint32 v'62 **
         LV y @ char_t |-> v'3 **
         LV ios_cap_defs.i @ char_t |-> v'2 **
         LV pCSpace @ CSPACE ∗ |-> v'0 **
         LV func_capType @ char_t |-> Vint32 v'63 **
         LV srcTask_Prio @ char_t |-> Vint32 v'64 **
         LV destTask_Prio @ char_t |-> Vint32 i **
         LV ios_cap_defs.index @ long |-> v'61 **
         A_dom_lenv
           ((func_capability, long)
            :: (func_capType, char_t)
              :: (srcTask_Prio, char_t)
               :: (destTask_Prio, char_t)
                  :: (pCSpace, CSPACE ∗)
                     :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)
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
  sep cancel v'61.
  sep pauto.
  (*end*)  

(*If (index ′ ==ₑ ′ SLOT_NUM)*)
  pure intro.
  lzh_hoare_if.
  assert (s
    |= ([|Some v'61 = Some (V$ SLOT_NUM)|] \\//
    [|(exists ret, Some v'61 = Some (V$ ret) /\ 0 <= ret < 255) /\
      (Int.unsigned v'63 = CAP_FUNCTION_TYPE /\ Int.unsigned v'62 <= CAP_CHANNEL_CLASS \/
       (Int.unsigned v'63 = CAP_SEM_TYPE \/ Int.unsigned v'63 = CAP_MUTEX_TYPE \/ Int.unsigned v'63 = CAP_Q_TYPE) /\
       Int.unsigned v'62 < OS_USER_MAX_EVENTS / 3 \/ Int.unsigned v'63 = CAP_TASK_TYPE /\ Int.unsigned v'62 < OS_STAT_PRIO)|]) ** Atrue).
  sep pauto.
  eapply disj_split in H37.
  destruct H37.
  sep split in H37.
  destruct v'61.   
  try false.
  try false.
  go.
  try false. 
  sep split in H37.
  simpljoin.
  inverts H38.
  auto.
  Optimize Proof.
  Optimize Heap.
  unfold val_eq, val_inj.
  assert (s
    |= ([|Some v'61 = Some (V$ SLOT_NUM)|] \\//
    [|(exists ret, Some v'61 = Some (V$ ret) /\ 0 <= ret < 255) /\
      (Int.unsigned v'63 = CAP_FUNCTION_TYPE /\ Int.unsigned v'62 <= CAP_CHANNEL_CLASS \/
       (Int.unsigned v'63 = CAP_SEM_TYPE \/ Int.unsigned v'63 = CAP_MUTEX_TYPE \/ Int.unsigned v'63 = CAP_Q_TYPE) /\
       Int.unsigned v'62 < OS_USER_MAX_EVENTS / 3 \/ Int.unsigned v'63 = CAP_TASK_TYPE /\ Int.unsigned v'62 < OS_STAT_PRIO)|]) ** Atrue).
  sep pauto.
  destruct v'61.
  eapply disj_split in H37. 
  destruct H37. 
  sep split in H37.
  try false.
  sep split in H37.
  simpljoin.
  try false.
  eapply disj_split in H37. 
  destruct H37. 
  sep split in H37.
  try false.
  sep split in H37.
  simpljoin.
  try false.
  unfold val_inj;unfold val_eq;destruct (Int.eq i0 ($ SLOT_NUM)).
  go.
  go.
  eapply disj_split in H37. 
  destruct H37. 
  sep split in H37.
  try false.
  sep split in H37.
  simpljoin.
  tryfalse.
  (*EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  go. 
  unfold GoodFrm. auto.  
  
  (*RETURN 〈Int8u〉′EINVAL*)
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply move_cap_absimp_err_slotnum.
  can_change_aop_solver.
  unfold can_change_aop. auto. eauto. 
  hoare forward.
  sep lift 2%nat in H28.
  eapply disj_split in H28.
  destruct H28.
  sep split in H28.
  sep cancel p_local.
  sep split in H28.
  sep cancel p_local.

  (*to refine the condition to be
  [|exists ret, Some v'60 = Some (V$ ret) /\ 0 <= ret < 255|]*)
  eapply backward_rule1 with (p:=<||
  user_cnode_move_code
    (Vint32 i :: Vint32 v'64 :: Vint32 v'63 :: Vint32 v'62 :: v') ||>  **
  OldOSInvWL tid
    (logic_val (V$ 1)
      :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  aemp_isr_is **
  Aisr empisr **
  Aier v'65 **
  Aie false **
  Ais nil **
  Acs (true :: nil) **
  [|(exists ret, Some v'61 = Some (V$ ret) /\ 0 <= ret < 255) /\
  (Int.unsigned v'63 = CAP_FUNCTION_TYPE /\ Int.unsigned v'62 <= CAP_CHANNEL_CLASS \/
   (Int.unsigned v'63 = CAP_SEM_TYPE \/ Int.unsigned v'63 = CAP_MUTEX_TYPE \/ Int.unsigned v'63 = CAP_Q_TYPE) /\
   Int.unsigned v'62 < OS_USER_MAX_EVENTS / 3 \/ Int.unsigned v'63 = CAP_TASK_TYPE /\ Int.unsigned v'62 < OS_STAT_PRIO)|] **
  LV func_capability @ long |-> Vint32 v'62 **
  LV y @ char_t |-> v'3 **
  LV ios_cap_defs.i @ char_t |-> v'2 **
  LV pCSpace @ CSPACE ∗ |-> v'0 **
  LV func_capType @ char_t |-> Vint32 v'63 **
  LV srcTask_Prio @ char_t |-> Vint32 v'64 **
  LV destTask_Prio @ char_t |-> Vint32 i **
  LV ios_cap_defs.index @ long |-> v'61 **
  A_dom_lenv
    ((func_capability, long)
      :: (func_capType, char_t)
        :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
              :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  intros.
  sep_lifts_trms_in H28 v'61.
  apply disj_split in H28.
  destruct H28.
  sep split in H28.
  inverts H37.
  clear -Hif_false1.
  unfold val_inj,val_eq in Hif_false1.
  assert (Int.eq ($ SLOT_NUM) ($ SLOT_NUM) = true).
  go. rewrite H in Hif_false1.
  inverts Hif_false1. inverts H0. tryfalse.
  sep pauto. 
  rewrite H37.
  eauto.

  (*y ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ*)
  unfold OldOSInvWL.
  unfold AOSTCBList;unfold_dll.
  pure intro.
  assert(Hpriolt64:Int.unsigned i4 < 64). 
  unfold TCBList_P in H45.
  simpljoin.
  unfold TCBNode_P in H48.
  destruct x3, p, p.
  simpljoin. 
  unfold RL_TCBblk_P in H65.
  simpljoin.
  unfold V_OSTCBPrio in H65. simpl in H65. inverts H65. lia.
  assert(Htrue: Int.unsigned i4 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -Hpriolt64. int auto.
  assert(Hitrue: Int.unsigned i <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H4. int auto.

  hoare forward.
  go. 

  (*pCSpace′=ₑOSCSpacePrioTbl′[y′];ₛ*)
  unfold CapabilityInv.
  hoare_split_pure_all.
  destruct v'11. 
  hoare remember (1::nil)%nat pre.
  unfold AOSCSpacePrioTbl. hoare_split_pure_all.
  assert(Htypematch : array_type_vallist_match CSPACE ∗ v'16).
  simpljoin. auto.
  assert(Hlenv'76: length v'16 = 64%nat). simpljoin. auto.
  assert(Hlenv'30: length v'61 = 64%nat). simpljoin. auto.
  eapply backward_rule1 with (p:=AOSCSpacePrioTbl (b, i7) v'16 v'61 v'98 ** H67).
  intros.
  unfold AOSCSpacePrioTbl. 
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep split; auto.
  subst H67.
  clear H68.
  hoare_lifts_trms_pre (Aop, AOSCSpacePrioTbl, Alvarmapsto pCSpace, Alvarmapsto y, A_dom_lenv, p_local).
  hoare remember (1::2::3::4::5::6::nil)%nat pre.
  unfold AOSCSpacePrioTbl.
  hoare_split_pure_all.
  eapply seq_rule.
  
  eapply assign_rule_lvar.
  {
    intros. split. intros.
    sep_lifts_trms_in H69 (pCSpace).
    exact H69.
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
    exact H69.
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
  eapply backward_rule1 with(p:=<|| user_cnode_move_code (Vint32 i :: Vint32 v'64 :: Vint32 v'63 :: Vint32 v'62 :: v')
  ||>  **
  LV pCSpace @ CSPACE ∗ |-> nth_val' (Z.to_nat (Int.unsigned i4)) v'16 **
  AOSCSpacePrioTbl (b, i7) v'16 v'61 v'98 **
  LV y @ char_t |-> Vint32 i4 **
  A_dom_lenv
    ((func_capability, long)
    :: (func_capType, char_t)
      :: (srcTask_Prio, char_t)
        :: (destTask_Prio, char_t)
          :: (pCSpace, CSPACE ∗)
              :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil) **
                p_local OSLInv (v'97, Int.zero) init_lg ** H67).
  intros. unfold AOSCSpacePrioTbl.
  sep cancel H67. sep auto.
  subst H67.
  assert(HpCSpacetype: rule_type_val_match CSPACE ∗
  (nth_val' (Z.to_nat (Int.unsigned i4)) v'16) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hlenv'76. lia.
  clear H68.
  hoare forward.
  unfold val_inj, val_eq.
  clear -HpCSpacetype.
  unfold rule_type_val_match in HpCSpacetype.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i4)) v'16); tryfalse; auto;destruct a; auto.
  hoare_split_pure_all.
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
  
  (*RETURN 〈 char_t 〉 ′ CNODE_DELETE_FAILURE*)
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  Optimize Proof.
  Optimize Heap.
  eapply move_cap_absimp_failure.
  can_change_aop_solver.
  hoare forward.

(*IF ((((((((pCSpace ′ → cnode) .. slots) [′ SLOT_CNODE_CAP])
                      .. capability) .. cap_content) .. category)
                   .. category_right &ₑ ′ CNODE_DELETE_CAP) ==ₑ ′ 0
                  ||ₑ CapParent ′ [destTask_Prio ′]
                      !=ₑ OSTCBCur ′ → OSTCBPrio &&ₑ
                      destTask_Prio ′ !=ₑ OSTCBCur ′ → OSTCBPrio)*)
               
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hnotnull: (nth_val' (Z.to_nat (Int.unsigned i4)) v'16) <> Vnull).
  clear -HpCSpacetype  H67.
  unfold rule_type_val_match in HpCSpacetype.
  unfold val_inj, val_eq in H67.
  destruct (nth_val' (Z.to_nat (Int.unsigned i4)) v'16); destruct H67; tryfalse.
  destruct a; auto. destruct a. auto.
  clear H67.
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H67 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned i4)) in H67.
  exact H67.
  rewrite Hlenv'30.
  lia.
  auto.
  hoare_split_pure_all.
  unfold ACSpace.
  destruct v'101, p, p, p, v'105.
  unfold Acnode. 
  destruct c, p. 
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H67 (ASlots).
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(SLOT_CNODE_CAP)) in H67; eauto. 
  (* eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned i1)) in H29; eauto.  *)
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  hoare_split_pure_all.
  simpljoin.
  unfold ACap. destruct v'105, c, p. 
  unfold AOSCSpaceCapParent.
  hoare_split_pure_all.
  destruct H81.
  destruct H82. 
  assert(Hx: (Z.to_nat(Int.unsigned i4) < 64)%nat).
  clear -Hpriolt64. lia. 
  assert(Hxi: (Z.to_nat(Int.unsigned i) < 64)%nat).
  lia.
  assert(Hv58true: Int.unsigned v'64 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  lia.
  lets Hy: nthval'_has_value_Tint32 H81 H82 Hxi.
  destruct Hy. destruct H84.
  assert (nth_val' (Z.to_nat (Int.unsigned i4))
        (v'103 ++ Vptr (b0, i10) :: v'104) = Vptr (b0, i10)).
  eapply nth_val'_length_imp. eauto.
  rewrite H86.
  eapply forward_rule1 with(q:=Afalse \\//Afalse).
  intros.
  destruct H87; auto.
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
                sep cancel pCSpace. exact H87.
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
    sep normal in H87.
    sep lift 5%nat in H87.
    unfold Aptrmapsto in H87 at 1.
    exact H87.
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
  destruct(Int.eq (i15&ᵢ$ CNODE_MOVE_CAP) ($ 0)); auto.
  simpl. eauto.
  sep get rv.
  rewrite Hitrue. auto. 
  rewrite H84. auto. 
  rewrite Hv58true.
  auto.
  rewrite H84. 
  unfold val_inj, val_eq.
  destruct (Int.eq x0 v'64); eauto.
  rewrite H84. 
  unfold val_inj, notint, val_eq.
  destruct (Int.eq x0 v'64); eauto.
  Ltac val_help:=
        try change (Int.ltu Int.zero Int.zero) with (false);
        try change (Int.ltu Int.one Int.zero) with (false);
        try change (Int.ltu Int.zero Int.one) with (true);
        try change (Int.ltu Int.one Int.one) with (false);
        try change (Int.eq Int.one Int.one) with (true);
        try change (Int.eq Int.one Int.zero) with (false);
        try change (Int.eq Int.zero Int.one) with (false);
        try change (Int.eq Int.zero Int.zero) with (true).
  eauto.
  unfold val_inj, bop_eval, val_eq, and, uop_eval, notint, bool_and.
  unfold Int.zero.
  rewrite H84.
  destruct (Int.eq
    (i15&ᵢ$ CNODE_MOVE_CAP)
    ($ 0)); 
    destruct (Int.eq x0 v'64); unfold Int.notbool;repeat (val_help; simpl); eauto.
  simpl. eauto.

  (*EXIT_CRITICAL;ₛ*) 
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H88. 
  eapply fold_Cap in H88.
  sep lifts (2::3::1::4::nil)%nat in H88.
  eapply ASlots_fold_any_idx_frm in H88; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H88.
  eapply fold_Acnode in H88.
  sep lifts (1::6::7::8::9::nil)%nat in H88.
  eapply fold_ACSpace  in H88; [idtac | eauto..]. 
  sep lifts (5::1::6::nil)%nat in H88. 
  eapply ACSpaceAarray_fold_any_idx_frm in H88; [idtac | eauto; try lia..]. 
  sep lifts (2::1::3::4::nil)%nat in H88.
  eapply fold_AOSCSpacePrioTbl1 in H88.
  exact H88. 
  rewrite app_length. simpl.
  rewrite H69, H78. rewrite S_add_sub_S. clear -Hpriolt64. lia.
  eauto. 
  rewrite app_length. simpl.
  rewrite H70, H77. rewrite S_add_sub_S. clear -Hpriolt64. lia. lia.
  eauto.
  rewrite nth_val_imp_nth_val'_2. rewrite H86. eauto.
  rewrite app_length. simpl. 
  rewrite H69, H78. rewrite S_add_sub_S. clear -Hpriolt64. lia. lia.
  eauto.
  rewrite app_length. simpl. 
  rewrite H68, H80. rewrite S_add_sub_S.
  unfold SLOT_CNODE_CAP, SLOT_NUM. clear -Hsrc_dest_lt. lia.
  unfold SLOT_CNODE_CAP, SLOT_NUM. clear -Hsrc_dest_lt. lia.
  unfold SLOT_CNODE_CAP, SLOT_NUM. clear -Hsrc_dest_lt. lia.
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

  (*RETURN 
  〈 char_t 〉 ′ USER_CAPABILITY_NONE*)
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  Optimize Proof.
  Optimize Heap.
  eapply move_cap_absimp_nocap.
  can_change_aop_solver.
  hoare forward.

  (*fold the invariant*)
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H88. 
  eapply fold_Cap in H88.
  sep lifts (2::3::1::4::nil)%nat in H88.
  eapply ASlots_fold_any_idx_frm in H88; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H88.
  eapply fold_Acnode in H88.
  sep lifts (1::6::7::8::9::nil)%nat in H88.
  eapply fold_ACSpace  in H88; [idtac | eauto..].
  sep lifts (5::1::6::nil)%nat in H88. 
  eapply ACSpaceAarray_fold_any_idx_frm in H88; [idtac | eauto; try lia..]. 
  sep lifts (2::1::3::4::nil)%nat in H88.
  eapply fold_AOSCSpacePrioTbl1 in H88; [idtac | eauto; try lia..].
  sep_lifts_trms_in H88 (Aisr, Ais, aemp_isr_is, A_isr_is_prop).  
  eapply elim_aemp_isr_is_prop in H88. 
  eapply elim_a_isr_is_prop in H88. 
  exact H88.
  rewrite nth_val_imp_nth_val'_2. rewrite H86. eauto.
  rewrite Hlenv'76. lia. 
  eauto.
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  eauto.

  assert (Hcases1: 
  not ((nth_val' (Z.to_nat (Int.unsigned i)) (v'103 ++ Vptr (b0, i10) :: v'104) <> Vnull) /\
       (nth_val' (Z.to_nat (Int.unsigned v'64)) (v'103 ++ Vptr (b0, i10) :: v'104) <> Vnull)) \/
  (nth_val' (Z.to_nat (Int.unsigned i)) (v'103 ++ Vptr (b0, i10) :: v'104) <> Vnull) /\
  (nth_val' (Z.to_nat (Int.unsigned v'64)) (v'103 ++ Vptr (b0, i10) :: v'104) <> Vnull)) by tauto.
  destruct Hcases1 as [Hfail1|Hsucc1].

  (* eapply backward_rule1.
  intros.
  sep_lifts_trms_in H88 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with(idx1:=Z.to_nat(Int.unsigned i)) (idx2:=Z.to_nat(Int.unsigned v'64)) in H88.
  exact H88.
  unfold AOSCSpacePrioTbl in H88.
  sep split in H88.
  destruct H89.
  destruct H97.
  rewrite H97. lia.
  clear -Hsrc_dest_lt.
  eapply Z2Nat.inj_lt; int auto.
  eauto. eauto.
  int auto. *)


  (*i = ucos_CNode_Move()*)
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_CNode_Move_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  (* rewrite Hd1. *)
  rewrite Hv58true. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.

  intros. unfold getasrt.
  unfold ucos_CNode_MovePre.
  unfold ucos_CNode_MovePre'.
  sep normal. sep eexists.

  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel AOSCSpaceObjectPointer.
  sep cancel 30%nat 1%nat.
  exact H88.
  change SLOT_NUM with 255.
  8:simpl; eauto.
  8:simpl; eauto.
  8:simpl; eauto.
  rewrite Int.unsigned_repr.
  lia.
  unfold Int.max_unsigned.
  simpl.
  lia.
  auto.
  change ios_cap_defs.OS_LOWEST_PRIO with 63.
  lia.
  eauto.

  lia.
  go.
  go.
  go.
  unfold CSpaceGVars.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  2:{
    simpl.
    rewrite Hitrue, Hv58true. auto.
  }
  unfold retpost.
  unfold ucos_CNode_MovePost.  unfold getasrt. 
  unfold ucos_CNode_MovePost'.
  intros. sep destruct H88.
  sep lift 16%nat in H88.
  eapply disj_split in H88.
  destruct H88.
  sep split in H88.
  destruct H90.
  rewrite H90.
  eauto.
  sep split in H88.
  eapply disj_split in H88.
  destruct H88.
  sep split in H88.
  rewrite H105. eauto.
  eapply disj_split in H88.
  destruct H88.
  sep split in H88.
  rewrite H109. eauto.
  sep normal in H88.
  sep destruct H88.
  sep lift 3%nat in H88.
  eapply disj_split in H88.
  destruct H88.
  sep normal in H88.
  sep destruct H88.
  sep lift 2%nat in H88.
  eapply disj_split in H88.
  destruct H88.
  sep split in H88.
  destruct H105.
  rewrite H105; eauto.
  sep split in H88.
  rewrite H105; eauto.
  sep split in H88.
  rewrite H105; eauto.
  unfold getasrt, ucos_CNode_MovePost,ucos_CNode_MovePost'.
  intros. sep destruct H88.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt, ucos_CNode_MovePre, ucos_CNode_MovePre'.
  intros.
  sep destruct H88. eexists.
  sep cancel p_local. simpl. auto.

  unfold getasrt, ucos_CNode_MovePost,ucos_CNode_MovePost'.
  hoare_split_pure_all.
  inverts H93.
  simpl in H90, H88, H89.
  apply sym_eq in H90.
  apply sym_eq in H88.
  apply sym_eq in H89.
  inverts H90. inverts H88. inverts H89. 

  (*The first case*)
  (*IF(i == CNODE_NONE_FAULT)*)
  eapply backward_rule1.
  intros.
  sep lift 10%nat in H88.
  apply disj_split in H88.
  exact H88.
  apply disj_rule.
  hoare_split_pure_all.
  destruct H89.
  inverts H89.
  hoare forward.
  hoare_split_pure_all.
  unfold CNODE_MOVE_FAILURE, CNODE_NONE_FAULT in H89.
  unfold val_inj in H89.
  assert(Int.eq ($7) ($0) = false).
  int auto.
  change ios_cap_defs.OS_LOWEST_PRIO with 63.
  lia.
  Optimize Proof.
  Optimize Heap.
  unfold CAP_TASK_TYPE.
  lia.
  change ios_cap_defs.OS_LOWEST_PRIO with 63.
  lia.
  destruct (Int.eq ($ 7) ($ 0)).
  tryfalse.
  destruct H89.
  tryfalse.
  (*ELSE failure*)
  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 

  sep lifts (4::2::5::nil)%nat in H93.
  eapply add_aemp_isr_is_prop in H93.
  
  eapply add_isr_is_prop in H93.  
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
  instantiate(1:=LV func_capability @ long |-> Vint32 v'62 **
    LV ios_cap_defs.index @ long |-> (V$ x) **
    LV func_capType @ char_t |-> Vint32 v'63 **
    LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 v'64 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MOVE_FAILURE) **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i10) **
    LV y @ char_t |-> Vint32 i4 **
    A_dom_lenv
      ((func_capability, long)
        :: (func_capType, char_t)
          :: (srcTask_Prio, char_t)
            :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  destruct H90.
  rewrite H90.
  eauto.
  destruct H90.
  rewrite H90.
  eauto.
  destruct H90.
  rewrite H90.
  eauto.
  destruct H90.
  rewrite H90.
  eauto.
  go.
  eauto.

  (*ELSE failure case*)
  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply move_cap_absimp_failure.
  can_change_aop_solver.
  hoare forward.

  destruct H89.  sep split in H89. 
  unfold CNODE_MOVE_FAILURE, CNODE_NONE_FAULT in H90.
  unfold val_inj in H90.
  assert(Int.eq ($7) ($0) = false).
  int auto.
  change ios_cap_defs.OS_LOWEST_PRIO with 63.
  lia.
  unfold CAP_TASK_TYPE.
  lia.
  change ios_cap_defs.OS_LOWEST_PRIO with 63.
  lia.
  destruct (Int.eq ($ 7) ($ 0)).
  tryfalse.
  destruct H90.
  tryfalse.
  sep split in H89.
  exact H89.

  hoare_split_pure_all. 
  rename H89 into Hnew_capability.
  clear -Hfail1 H88.  
  tryfalse.

  (*Hsucc1*)
  destruct Hsucc1.
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H90 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with(idx1:=Z.to_nat(Int.unsigned i)) (idx2:=Z.to_nat(Int.unsigned v'64)) in H90.
  exact H90.
  unfold AOSCSpacePrioTbl in H90.
  sep split in H90.
  destruct H91.
  destruct H99.
  rewrite H99. lia.

  clear -Hsrc_dest_lt.
  eapply Z2Nat.inj_lt; int auto.
  eauto. eauto.

  hoare_split_pure_all.
  simpljoin.
  unfold ACSpace.
  destruct v'106, p, p, p, v'113.
  unfold Acnode. 
  destruct c, p. 
  destruct v'107, p, p, p, v'114.
  destruct c, p. 

  hoare_split_pure_all.
  simpljoin.
  rename H109 into Hi16range.
  rename H108 into Hi21range.
  eapply backward_rule1.
  intros.
  sep lifts(10::nil)%nat in H108.
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned ($ x))) in H108; eauto. 
  unfold SLOT_NUM. clear -H52 H51.
  int auto.  
  
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  intros.
  sep lifts(21::nil)%nat in H108.
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned ($ x))) in H108; eauto. 
  unfold SLOT_NUM. clear -H52 H51.
  int auto.  
  hoare_split_pure_all.
  simpljoin.
  unfold ACap. destruct v'118, c, p. destruct v'114, c, p.  

  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H116. 
  eapply fold_Cap in H116.
  sep lifts (2::3::1::4::nil)%nat in H116.
  eapply ASlots_fold_any_idx_frm in H116; [idtac | eauto..]. 
  sep lifts (23::24::1::nil)%nat in H116.
  eapply fold_Acnode in H116.
  sep lifts (1::23::24::25::26::nil)%nat in H116.
  eapply fold_ACSpace in H116; [idtac | eauto..]. 
  sep lifts (4::5::6::7::nil)%nat in H116. 
  eapply fold_Cap in H116.
  sep lifts (3::4::1::5::nil)%nat in H116.
  clear H71.
  eapply ASlots_fold_any_idx_frm with (slotsvl:=(v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107)) in H116; [idtac | eauto..]. 
  sep lifts (10::11::1::nil)%nat in H116.
  eapply fold_Acnode in H116.
  sep lifts (1::10::11::12::13::nil)%nat in H116.
  eapply fold_ACSpace in H116; [idtac | eauto..]. 
  sep lifts (9::1::10::nil)%nat in H116. 
  eapply ACSpaceAarray_fold_any_idx_frm in H116; [idtac | eauto; try lia..]. 
  sep lifts (1::2::9::nil)%nat in H116. 
  eapply ACSpaceAarray_fold_any_idx_frm in H116; [idtac | eauto; try lia..].
  sep lifts (5::3::6::nil)%nat in H116.
  eapply Aarray'_fold_any_idx_frm in H116; [idtac | eauto..].
  sep lifts (1::4::5::nil)%nat in H116.
  eapply Aarray'_fold_any_idx_frm in H116; [idtac | eauto..].
  exact H116. 
  simpl. rewrite max_unsigned_val. lia.
  simpl. rewrite max_unsigned_val. lia.
  splits.
  rewrite app_length. simpl.
  rewrite H92, H96. rewrite S_add_sub_S. clear -Hsrc_dest_lt. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto. eauto. 
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  simpl. rewrite max_unsigned_val. clear -H1. lia.
  simpl. rewrite max_unsigned_val. lia.
  rewrite app_length. simpl. 
  rewrite H94, H93. rewrite S_add_sub_S. clear -Hsrc_dest_lt. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl.
  rewrite H92, H96. rewrite S_add_sub_S. clear -Hsrc_dest_lt. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  rewrite app_assoc_reverse. eauto.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl.
  rewrite H94, H93. rewrite S_add_sub_S. clear -Hsrc_dest_lt. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  eauto.
  unfold SLOT_NUM. clear -H52 H51.
  int auto.  
  Optimize Proof.
  Optimize Heap.
  eauto.
  eauto.
  unfold SLOT_NUM. clear -H52 H51.
  int auto.  
  eauto.

  (*i = ucos_CNode_Move()*)
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_CNode_Move_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  (* rewrite Hd1. *)
  rewrite Hv58true. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.

  intros. unfold getasrt.
  unfold ucos_CNode_MovePre.
  unfold ucos_CNode_MovePre'.
  sep normal. sep eexists.

  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  unfold AOSCSpacePrioTbl.
  unfold Aarray.
  sep split.
  sep cancel p_local.
  sep cancel OSCSpacePrioTbl.
  sep cancel Aarray'.
  sep cancel ACSpaceAarrayTptr.
  sep cancel AOSCSpaceObjectPointer.
  sep cancel 30%nat 1%nat.
  exact H116.
  change SLOT_NUM with 255.
  9:simpl; eauto.
  9:simpl; eauto.
  9:simpl; eauto.
  rewrite Int.unsigned_repr.
  lia.
  unfold Int.max_unsigned.
  simpl.
  lia.
  auto.
  change ios_cap_defs.OS_LOWEST_PRIO with 63.
  lia.
  eauto.
  splits.
  rewrite app_length. simpl. rewrite app_length. simpl.
  rewrite H92, H96, H97. rewrite S_add_sub_S. 
  clear -Hsrc_dest_lt H1.
  lia.
  clear -Hsrc_dest_lt H1.
  eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl. 
  rewrite H77, H70. rewrite S_add_sub_S. clear -Hpriolt64. lia.
  clear -Hpriolt64.
  lia.
  rewrite H90 in Htypematch.
  rewrite app_assoc_reverse. eauto.
  clear -Hsrc_dest_lt. int auto.
  rewrite H90 in H48.
  rewrite app_assoc_reverse. eauto.
  rewrite H90 in H64.
  rewrite app_assoc_reverse. eauto.
  unfold CSpaceGVars.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  2:{
    simpl.
    rewrite Hitrue, Hv58true. auto.
  }
  unfold retpost.
  unfold ucos_CNode_MovePost.  unfold getasrt. 
  unfold ucos_CNode_MovePost'.
  intros. sep destruct H116.
  sep lift 16%nat in H116.
  eapply disj_split in H116.
  destruct H116.
  sep split in H116.
  destruct H118.
  rewrite H118.
  eauto.
  sep split in H116.
  eapply disj_split in H116.
  destruct H116.
  sep split in H116.
  rewrite H133. eauto.
  eapply disj_split in H116.
  destruct H116.
  sep split in H116.
  rewrite H137. eauto.
  sep normal in H116.
  sep destruct H116.
  sep lift 3%nat in H116.
  eapply disj_split in H116.
  destruct H116.
  sep normal in H116.
  sep destruct H116.
  sep lift 2%nat in H116.
  eapply disj_split in H116.
  destruct H116.
  sep split in H116.
  destruct H133.
  rewrite H133; eauto.
  sep split in H116.
  rewrite H133; eauto.
  sep split in H116.
  rewrite H133; eauto.
  unfold getasrt, ucos_CNode_MovePost,ucos_CNode_MovePost'.
  intros. sep destruct H116.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt, ucos_CNode_MovePre, ucos_CNode_MovePre'.
  intros.
  sep destruct H116. eexists.
  sep cancel p_local. simpl. auto.

  unfold getasrt, ucos_CNode_MovePost,ucos_CNode_MovePost'.
  hoare_split_pure_all.
  simpljoin.
  inverts H121.
  simpl in H117, H116, H118.
  apply sym_eq in H117.
  apply sym_eq in H116.
  apply sym_eq in H118.
  inverts H117. inverts H116. inverts H118. 

  (*The first case*)
  (*IF(i == CNODE_NONE_FAULT)*)
  eapply backward_rule1.
  intros.
  sep lift 10%nat in H116.
  apply disj_split in H116.
  exact H116.
  apply disj_rule.
  hoare_split_pure_all.
  rewrite app_assoc_reverse in H116.
  destruct H116; tryfalse.
  
  (*The second case*)
  (*IF(i == CNODE_NONE_FAULT)*)
  eapply backward_rule1.
  intros.
  sep lift 4%nat in H116.
  apply disj_split in H116.
  exact H116.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H117.
  hoare forward.
  hoare_split_pure_all.
  unfold CNODE_MOVE_FAILURE, CNODE_NONE_FAULT in H117.
  unfold val_inj in H117.
  assert(Int.eq ($7) ($0) = false).
  clear -H4.
  int auto.
  destruct (Int.eq ($ 7) ($ 0)).
  tryfalse.
  destruct H117.
  tryfalse.

  (*ELSE failure case*)
  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (4::2::5::nil)%nat in H124.
  eapply add_aemp_isr_is_prop in H124.
  eapply add_isr_is_prop in H124. 
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
  instantiate(1:=LV func_capability @ long |-> Vint32 v'62 **
    LV ios_cap_defs.index @ long |-> (V$ x) **
    LV func_capType @ char_t |-> Vint32 v'63 **
    LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 v'64 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MOVE_FAILURE) **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i10) **
    LV y @ char_t |-> Vint32 i4 **
    A_dom_lenv
      ((func_capability, long)
        :: (func_capType, char_t)
          :: (srcTask_Prio, char_t)
            :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  destruct H118.
  rewrite H118.
  eauto.
  destruct H118.
  rewrite H118.
  eauto.
  destruct H118.
  rewrite H118.
  eauto.
  destruct H118.
  rewrite H118.
  eauto.
  go.
  eauto.
  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply move_cap_absimp_failure.
  can_change_aop_solver.
  hoare forward.

  destruct H117.  sep split in H116. 
  clear - H117.
  unfold CNODE_MOVE_FAILURE, CNODE_NONE_FAULT in H117.
  unfold val_inj in H117.
  assert(Int.eq ($7) ($0) = false).
  int auto.
  Optimize Proof.
  Optimize Heap.
  destruct (Int.eq ($ 7) ($ 0)).
  tryfalse.
  destruct H117.
  tryfalse.
  sep split in H116.
  exact H116.

  (*The 3rd case*)
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H121.
  exact H121.
  eapply disj_rule.
  hoare_split_pure_all.
  inverts H126.
  hoare forward.
  hoare_split_pure_all.
  clear H126.

  rewrite H91 in H53.
  lets bak_53: H53.
  unfolds in H53.
  destruct H53.
  assert(Ha: 0 <= Int.unsigned v'64 < 64).
  clear -Hi0lt63.
  int auto. 
  assert(Hb: nth_cspace_val ∘ (Int.unsigned v'64)
    (v'105 ++
    ((i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)
    :: v'108) ++
    (i24, i25, v'115 ++ (v'117, (i26, (i27, i28, v3))) :: v'116, i22, l2, v2, i21)
    :: v'109)  = 
    Some (i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.

  (*rewrite <- app_assoc_reverse in H48.*)
  lets Hc: H53 Hb.
  destruct Hc. destruct H127. destruct H127. destruct H128.
  clear Ha Hb.

  assert(Ha: 0 <= Int.unsigned i < 64).
  clear -H1. int auto.
  assert(Hb: nth_cspace_val ∘ (Int.unsigned i)
    ((v'105 ++
    ((i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)
    :: v'108)) ++
    (i24, i25, v'115 ++ (v'117, (i26, (i27, i28, v3))) :: v'116, i22, l2, v2, i21)
    :: v'109)  = 
    Some (i24, i25, v'115 ++ (v'117, (i26, (i27, i28, v3))) :: v'116, i22, l2, v2, i21)).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.
  rewrite app_length. simpl. 
  rewrite H93, H94. rewrite S_add_sub_S. unfold nat_of_Z. clear -Hsrc_dest_lt. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.

  rewrite <- app_assoc_reverse in H53.
  lets Hc: H53 Hb.
  destruct Hc. destruct H130. destruct H130. destruct H131.
  clear Ha Hb.

  rewrite H91 in H117.
  rewrite get_capability_nth_mth_cspace_length_imp in H117; eauto.
  assert(v'135 = $ CAP_CATEGORY_TYPE).
  clear -H121.
  rewrite <-H121.
  eapply unsigned_inj.
  int auto.
  rewrite H133 in H117.
  inverts H117.
  rewrite H91 in H118.
  rewrite list_trans_1 in H118.
  rewrite get_capability_nth_mth_cspace_length_imp in H118; eauto.
  inverts H118.
  2:{
    rewrite app_length. simpl.
    rewrite H93, H94.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt.
    lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  
  hoare_lifts_trms_pre (Aop, cspaceid).
  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply move_cap_absimp_succ_category.
  (*需要一个success情况下的lemma*)
  unfold AOSCSpaceObjectPointer, CSpaceGVars, AOSCSpacePrioTbl.
  go.
  eapply can_change_aop_ACSpaceAarrayTptr.
  eauto. eauto.
  eauto. eauto. eauto. eauto. eauto.
  
  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (5::3::6::nil)%nat in H117.
  eapply add_aemp_isr_is_prop in H117. 
  eapply add_isr_is_prop in H117. 
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
  instantiate(1:=LV func_capability @ long |-> Vint32 v'62 **
  LV ios_cap_defs.index @ long |-> (V$ x) **
  LV func_capType @ char_t |-> Vint32 v'63 **
  LV destTask_Prio @ char_t |-> Vint32 i **
  LV srcTask_Prio @ char_t |-> Vint32 v'64 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_NONE_FAULT) **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i10) **
  LV y @ char_t |-> Vint32 i4 **
  A_dom_lenv
    ((func_capability, long)
      :: (func_capType, char_t)
        :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
              :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  sep auto; eauto.
  split; eauto. go.
  {
    clear -H66.
    eapply Capability_wellform_descendents_update_type.
    eapply Capability_wellform_descendents_update_cap.
    eapply Capability_wellform_descendents_update_cap; auto.
  }
  {
    eapply taskPrioProp_update_slots_type_remain.
    eapply taskPrioProp_update_slots_cap_remain.
    eapply taskPrioProp_update_slots_cap_remain.
    eauto.
  }
  {
    rewrite H91.
    eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
    eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
    eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H93, H94. rewrite S_add_sub_S.
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; try (int auto).
    rewrite list_trans.
    rewrite <-H91. eauto.
    rewrite H91.
    rewrite list_trans_1.
    unfold update_nth_cspace_slots_cap.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_neqrev; eauto.
    rewrite app_assoc_reverse.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
  Optimize Proof.
  Optimize Heap.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite app_length. simpl.
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    clear -Hsrc_dest_lt.
    intro. 
    eapply Z2Nat.inj in H.
    lia.
    int auto. int auto.
    rewrite app_length. simpl.
    rewrite H93, H94.
    rewrite S_add_sub_S. 
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite <-H127.
    eapply CSpaceMod.map_get_set'.
    clear -Hsrc_dest_lt.
    intro.
    rewrite H in Hsrc_dest_lt.
    lia.

    unfold update_nth_cspace_slots_cap.
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_neqrev; eauto.
    rewrite app_assoc_reverse.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_eq; eauto.
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_slots_length_imp; eauto.
    rewrite update_nth_list_len_eq.
    rewrite app_length. simpl. 
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S_add.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    clear -H1. lia.
    rewrite app_length. simpl.
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite app_length. simpl. 
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.

    eapply Z2Nat.inj_lt; (int auto).
    clear -Hsrc_dest_lt.
    intro.
    eapply Z2Nat.inj in H.
    lia.
    int auto. int auto.
    rewrite app_length. simpl.
    rewrite H93, H94.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite update_nth_slots_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.

    eapply get_set_eq.
  }
  {
    eapply RL_Cap_Parent_Child_update_slots_type_remain.
    eapply RL_Cap_Parent_Child_remain. 
    eapply RL_Cap_Parent_Child_remain; auto.
  }
  {
    eapply RLH_CapParent_update_slots_type_remain.
    eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=(v'11 ++
    (i11, i12, v'16 ++ (v'101, (i13, (i14, i15, v0))) :: v'61, i9, l, v, i8)
    :: v'102)); eauto.
    
    eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=(v'11 ++
    (i11, i12, v'16 ++ (v'101, (i13, (i14, i15, v0))) :: v'61, i9, l, v, i8)
    :: v'102)); eauto. 
    rewrite H91.
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H93, H94. rewrite S_add_sub_S.
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; try (int auto).
    rewrite H91.
    (* rewrite list_trans.
    rewrite <-H49. eauto. *)
    (* unfold update_nth_cspace_slots_cap.
    rewrite list_trans_1. *)
    rewrite nth_cspace_length_imp; eauto.
    rewrite <-H127.
    eapply CSpaceMod.map_get_set'.
    clear -Hsrc_dest_lt.
    intro.
    rewrite H in Hsrc_dest_lt.
    lia.
    instantiate(7:= (update_nth_cspace_slots_cap (Z.to_nat (Int.unsigned v'64))
    (Z.to_nat (Int.unsigned ($ x)))
    (update_nth_cspace_slots_cap
        (Z.to_nat (Int.unsigned i))
        (Z.to_nat (Int.unsigned ($ x)))
        (v'105 ++
        ((i19, i20, v'106 ++ (v'113, ($ CAP_CATEGORY_TYPE, (v'136, v'137, v'138))) :: v'107,
         i17, l0, v1, i16) :: v'108) ++
        (i24, i25, v'115 ++ (v'117, (v'141, (v'142, v'143, v'140))) :: v'116, i22, l2, v2, i21)
        :: v'109)
        ($ CAP_CATEGORY_TYPE, (v'142, v'143, v'140)))
        ($ 0, ($ 0, $ 0, v'138)))).
    unfold update_nth_cspace_slots_cap.
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_neqrev; eauto.
    rewrite app_assoc_reverse.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_eq; eauto.
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_slots_length_imp; eauto.
    rewrite update_nth_list_len_eq.
    rewrite app_length. simpl. 
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S_add.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    clear -H1. lia.
    rewrite app_length. simpl.
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).

    rewrite app_length. simpl. 
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    clear -Hsrc_dest_lt.
    intro.
    eapply Z2Nat.inj in H.
    lia.
  Optimize Proof.
  Optimize Heap.
    int auto. int auto.
    rewrite app_length. simpl.
    rewrite H93, H94.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite update_nth_slots_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    eapply get_set_eq.
  }
  go.
  go.
  hoare forward.

  hoare_split_pure_all.
  clear -H126.
  unfold CNODE_NONE_FAULT in H126.
  unfold val_inj in H126.
  assert(Int.eq ($0) ($0) = true) by auto.
  rewrite H122 in H126.
  destruct H126; tryfalse.
  destruct H126.
  sep split in H116.
  eauto.
  sep split in H116.
  clear -H122.
  unfold CNODE_NONE_FAULT in H122.
  unfold val_inj in H122.
  assert(Int.eq ($0) ($0) = true) by auto.
  rewrite H in H122.
  destruct H122; tryfalse. 

  (*The 4th case*)
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lift 2%nat in H123.
  eapply disj_split in H123.
  exact H123.
  eapply disj_rule.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H125.
  exact H125.
  eapply disj_rule.
  hoare_split_pure_all.
  destruct H126.
  inverts H126.
  hoare forward.
  hoare_split_pure_all.
  unfold SLOT_RANGE_OVERFLOW, CNODE_NONE_FAULT in H126.
  unfold val_inj in H126.
  assert(Int.eq ($2) ($0) = false).
  clear -H126.
  int auto.
  destruct (Int.eq ($ 2) ($ 0)).
  tryfalse.
  destruct H126.
  tryfalse.

  (*ELSE failure case*)
  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (5::3::6::nil)%nat in H128.
  eapply add_aemp_isr_is_prop in H128.
  eapply add_isr_is_prop in H128. 
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
  instantiate(1:=LV func_capability @ long |-> Vint32 v'62 **
    LV ios_cap_defs.index @ long |-> (V$ x) **
    LV func_capType @ char_t |-> Vint32 v'63 **
    LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 v'64 **
    LV ios_cap_defs.i @ char_t |-> (V$ SLOT_RANGE_OVERFLOW) **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i10) **
    LV y @ char_t |-> Vint32 i4 **
    GetObjSlotRetval i
            ((v'110 ++ Vptr (b1, i18) :: v'111) ++ Vptr (b2, i23) :: v'112) v'133
            (v'11 ++
             (i11, i12, v'16 ++ (v'101, (i13, (i14, i15, v0))) :: v'61, i9, l, v, i8)
             :: v'102) v'138 v'65 **
    A_dom_lenv
      ((func_capability, long)
        :: (func_capType, char_t)
          :: (srcTask_Prio, char_t)
            :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  destruct H127.
  rewrite H121.
  eauto.
  destruct H127.
  rewrite H121.
  eauto.
  destruct H127.
  rewrite H121.
  eauto.
  destruct H127.
  rewrite H121.
  eauto.
  go.
  unfold GetObjSlotRetval.
  unfold GoodFrm.
  splits; auto.
  splits; auto.
  intros.
  splits; auto.
  eauto.
  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply move_cap_absimp_failure.
  can_change_aop_solver.
  unfold GetObjSlotRetval.
  unfold can_change_aop.
  splits; auto.
  splits; auto.
  intros.
  splits; auto.
  unfold GetObjSlotRetval.
  instantiate(1:=Afalse).
  eapply backward_rule1.
  intros.
  sep lift 16%nat in H128.
  eapply disj_split in H128.
  eauto.
  eapply disj_rule.
  2:{
    hoare_split_pure_all.
    clear -H1 H128.
    false.
    unfold ios_cap_defs.OS_LOWEST_PRIO in H128.
    lia.
  }
  eapply backward_rule1.
  intros.
  sep normal in H128.
  sep lift 2%nat in H128.
  eapply disj_split in H128.
  eauto.
  eapply disj_rule.
  hoare_split_pure_all.
  hoare forward.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H131.
  exact H131.
  eapply disj_rule.
  hoare_split_pure_all.
  hoare forward.
  hoare forward.
  destruct H126.
  sep split in H116.
  unfold SLOT_RANGE_OVERFLOW, CNODE_NONE_FAULT in H121.
  assert(Int.eq ($ 2) ($ 0) = false) by auto.
  rewrite H126 in H121.
  unfold val_inj in H121.
  destruct H121; tryfalse.
  sep split in H116.
  eauto.

  (*object_found*)
  2:{
    hoare_split_pure_all.
    inverts H124.
    hoare forward.
    hoare_split_pure_all.
    clear H124.
    instantiate(1:=Afalse).
    eapply backward_rule1.
    intros.
    unfold GetObjSlotRetval in H124.
    eapply disj_split in H124.
    exact H124.
    eapply disj_rule.
    hoare_split_pure_all.
    eapply backward_rule1.
    intros.
    eapply disj_split in H129.
    eauto.
    eapply disj_rule.
    hoare_split_pure_all.
    destruct H116; tryfalse.
    hoare_split_pure_all.
    eapply backward_rule1.
    intros.
    eapply disj_split in H131.
    eauto.
    eapply disj_rule.
    unfold Slots_eq_object.
    hoare_split_pure_all.
    
    assert(0 <= v'114 < Z.of_nat (length v'119)).
    destruct H134.
    destruct H134.
    destruct H134.
    destruct H134.
    destruct H134.
    destruct H134.
    destruct H134.
    auto.
  Optimize Proof.
  Optimize Heap.
    assert((Z.to_nat v'114) < length v'119)%nat.
    clear -H136.
    lia.
    eapply nth_slots_exists in H137.
    destruct H137.
    destruct x1.
    destruct p.
    destruct c.
    destruct p.
    destruct H134.
    destruct H134.
    destruct H134.
    destruct H134.
    destruct H134.
    destruct H134.
    destruct H134.
    rename H138 into Hnth.
    destruct Hnth.
    destruct H139.
    subst x3 x6.
    rewrite <- nth_slots_eq_nth_slots in H138.
    rewrite H137 in H138.
    inverts H138.
    destruct H135.
    subst v'65.
    unfold val_inj,  Vint32_inj in H121.
    assert(v'98 = v'114 + OBJ_POSITION).
    clear -H121 H138.
    rewrite Int.unsigned_repr in H121.
    eauto.
    unfold Int.max_unsigned.
    simpl.
    unfold OBJ_POSITION in *.
    int auto.
    assert(nth_slots (Z.to_nat v'98) (v'118 ++ v'119 ++ v'120) = Some(x1, (x2, (x4, x5, v'138)))).
    rewrite H135.
    clear -H137 H132 H136.
    assert(Z.to_nat (v'114 + OBJ_POSITION) = 
    (Z.to_nat v'114 + Z.to_nat OBJ_POSITION)%nat).
    eapply Z2Nat.inj_add. lia. unfold OBJ_POSITION. lia.
    rewrite H. clear H.
    eapply nth_slots_length_ll; auto.
    rewrite H91 in H53.
    lets bak_53: H53.
    unfolds in H53.
    destruct H53.
    assert(Ha: 0 <= Int.unsigned v'64 < 64).
    clear -Hi0lt63.
    int auto. 
    assert(Hb: nth_cspace_val ∘ (Int.unsigned v'64)
      (v'105 ++
      ((i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)
      :: v'108) ++
      (i24, i25, v'115 ++ (v'117, (i26, (i27, i28, v3))) :: v'116, i22, l2, v2, i21)
      :: v'109)  = 
      Some (i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)).
    rewrite nth_cspace_eq_nth_cspace_val; eauto.
    rewrite nth_cspace_length_imp; eauto.

    lets Hc: H53 Hb.
    destruct Hc. destruct H141. destruct H141. destruct H142.
    clear Ha Hb.
    assert(Ha: 0 <= Int.unsigned i < 64).
    clear -H1. int auto.
    assert(Hb: nth_cspace_val ∘ (Int.unsigned i)
      ((v'105 ++
      ((i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)
      :: v'108)) ++
      (i24, i25, v'115 ++ (v'117, (i26, (i27, i28, v3))) :: v'116, i22, l2, v2, i21)
      :: v'109)  = 
      Some (i24, i25, v'115 ++ (v'117, (i26, (i27, i28, v3))) :: v'116, i22, l2, v2, i21)).
    rewrite nth_cspace_eq_nth_cspace_val; eauto.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl. 
    rewrite H93, H94. rewrite S_add_sub_S. unfold nat_of_Z. clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
    rewrite H91 in H131.
    unfold get_slots in H131.
    rewrite list_trans_1 in H131.
    rewrite nth_cspace_length_imp in H131; auto.
    2:{
      rewrite app_length.
      simpl.
      rewrite H93, H94.
      clear -Hsrc_dest_lt H1.
      rewrite S_add_sub_S. lia.
      eapply Z2Nat.inj_lt; int auto.
    }
    inverts H131.
    rewrite <- app_assoc_reverse in H53.
    lets Hc: H53 Hb.
    destruct Hc. destruct H131. destruct H131.
    destruct H144.
    clear Ha Hb.
    rewrite H91 in H117.
    rewrite get_capability_nth_mth_cspace_length_imp in H117; eauto.
    assert(v'135 = $ CAP_OBJECT_TYPE).
    clear -H122.
    rewrite <-H122.
    eapply unsigned_inj.
    int auto.
    rewrite H147 in H117.
    inverts H117.
    
    rewrite H145 in H131.
    assert(nth_slots (Z.to_nat v'114) v'119 =
    Some (x1, (x2, (x4, x5, v'138)))).
    clear -H136 H139 H135 H132.
    rewrite H135 in H139.
    assert(Z.to_nat (v'114 + OBJ_POSITION) = Z.to_nat OBJ_POSITION +
    Z.to_nat v'114)%nat. 
    rewrite Nat.add_comm.
    eapply Z2Nat.inj_add. lia. unfold OBJ_POSITION. lia.
    rewrite H in H139.
    assert(nth_slots
    (Z.to_nat OBJ_POSITION +
     Z.to_nat v'114)
    (v'118 ++ v'119 ++ v'120) = nth_slots(Z.to_nat v'114)(v'119 ++ v'120)).
    eapply nth_slots_help_2; auto.
    rewrite H0 in H139.
    eapply nth_slots_help_3; eauto. lia.
    eapply nth_slots_help_4 in H117.
    destruct H117. destruct H117.
    destruct H117. destruct H148.
    rewrite H117 in H131.
    assert(v'118 ++
    (x11 ++
     (x1, (x2, (x4, x5, v'138)))
     :: x12) ++ v'120 = (v'118 ++ x11) 
     ++(x1, (x2, (x4, x5, v'138))) ::(x12 ++ v'120)).
    rewrite app_assoc_reverse. simpl.
    rewrite app_assoc_reverse. auto.
    rewrite H145 in *.
    clear H145.
    inverts H117.
    rewrite H150 in *.
    inverts H145.
    clear H150.
    remember (v'118 ++ x11) as fv'118.
    remember (x12 ++ v'120) as lv'120.
    
    hoare_lifts_trms_pre (Aop, cspaceid).
    hoare abscsq. 
    Hint Resolve noabs_oslinv.
    go. 
    eapply move_cap_absimp_succ_object.
    unfold AOSCSpaceObjectPointer, CSpaceGVars, AOSCSpacePrioTbl.
    go.
    
    eapply can_change_aop_ACSpaceAarrayTptr.
    eapply H131.
    eauto. 
    eapply H139.
    eauto. eauto. eauto. eauto.

    hoare_split_pure_all.
    eapply seq_rule.
    instantiate(2:=v'139).
    eapply forward_rule2.
    hoare_lifts_trms_pre (Aop).
    eapply excrit1_rule'_ISnil_ISRemp'''_lg.
    intros. 
    sep lifts (5::3::6::nil)%nat in H117.
    eapply add_aemp_isr_is_prop in H117. 
    eapply add_isr_is_prop in H117. 
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
    sep cancel A_isr_is_prop.
    sep cancel aemp_isr_is.
    instantiate(1:=LV func_capability @ long |-> Vint32 v'62 **
    LV ios_cap_defs.index @ long |-> (V$ x) **
    LV func_capType @ char_t |-> Vint32 v'63 **
    LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 v'64 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_NONE_FAULT) **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i10) **
    LV y @ char_t |-> Vint32 i4 **
    A_dom_lenv
      ((func_capability, long)
        :: (func_capType, char_t)
          :: (srcTask_Prio, char_t)
            :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
    sep cancel A_dom_lenv.
    sep cancel tcbdllflag.
    sep auto; eauto.
    split; eauto. go.
    {
      clear -H66.
      eapply Capability_wellform_descendents_update_type.
      eapply Capability_wellform_descendents_update_cap.
      eapply Capability_wellform_descendents_update_cap; auto.
    }
    {
      eapply taskPrioProp_update_slots_type_remain.
      eapply taskPrioProp_update_slots_cap_remain.
      eapply taskPrioProp_update_slots_cap_remain.
      eauto.
    }
    {
      rewrite H91.
      eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
      eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
      eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
      rewrite list_trans_1.
      rewrite nth_cspace_length_imp; eauto.
      rewrite app_length. simpl.
      rewrite H93, H94. rewrite S_add_sub_S.
      clear -Hsrc_dest_lt. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; try (int auto).
      rewrite list_trans.
      rewrite list_trans_1.
      unfold update_nth_cspace_slots_cap.
      rewrite nth_cspace_length_imp; eauto.
      rewrite nth_slots_length_imp; eauto.
      rewrite update_nth_cspace_neqrev; eauto.
      rewrite app_assoc_reverse.
      rewrite nth_cspace_length_imp; eauto.
      rewrite app_length. simpl.
      rewrite app_length. simpl.
      rewrite H93, H94, H95.
      rewrite S_add_sub_S.
      rewrite S_add_sub_S.
      clear -Hsrc_dest_lt H1.
      lia.
  Optimize Proof.
  Optimize Heap.
      clear -H1. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      rewrite app_length. simpl.
      rewrite app_length. simpl.
      rewrite H93, H94, H95.
      rewrite S_add_sub_S.
      rewrite S_add_sub_S.
      clear -Hsrc_dest_lt H1.
      lia.
      clear -H1. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      clear -Hsrc_dest_lt.
      intro. 
      eapply Z2Nat.inj in H.
      lia.
      int auto. int auto.
      rewrite app_length. simpl.
      rewrite H132, H148.
      clear - H138.
      unfold OBJ_POSITION in H138.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.inj_add.
      int auto.
      lia.
      unfold OBJ_POSITION.
      lia.
      unfold OBJ_POSITION.
      unfold Int.max_unsigned. simpl.
      lia.
      rewrite app_length. simpl.
      rewrite H93, H94.
      rewrite S_add_sub_S. 
      clear -Hsrc_dest_lt. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      rewrite <-H141.
      eapply CSpaceMod.map_get_set'.
      clear -Hsrc_dest_lt.
      intro.
      rewrite H in Hsrc_dest_lt.
      lia.

      unfold update_nth_cspace_slots_cap.
      rewrite list_trans_1.
      rewrite nth_cspace_length_imp; eauto.
      rewrite nth_slots_length_imp; eauto.
      rewrite update_nth_cspace_neqrev; eauto.
      rewrite app_assoc_reverse.
      rewrite nth_cspace_length_imp; eauto.
      rewrite nth_slots_length_imp; eauto.
      rewrite update_nth_cspace_eq; eauto.
      rewrite update_nth_list_length_imp; eauto.
      rewrite update_nth_slots_length_imp; eauto.
      rewrite update_nth_list_len_eq.
      rewrite app_length. simpl. 
      rewrite app_length. simpl.
      rewrite H93, H94, H95.
      rewrite S_add_sub_S.
      rewrite S_add_sub_S_add.
      clear -Hsrc_dest_lt H1.
      lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      clear -H1. lia.
      rewrite app_length. simpl.
      rewrite app_length. simpl.
      rewrite H93, H94, H95.
      rewrite S_add_sub_S.
      rewrite S_add_sub_S.
      clear -Hsrc_dest_lt H1.
      lia.
      clear -H1. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      rewrite app_length. simpl. 
      rewrite app_length. simpl.
      rewrite H93, H94, H95.
      rewrite S_add_sub_S.
      rewrite S_add_sub_S.
      clear -Hsrc_dest_lt H1.
      lia.
      clear -H1. lia.
      clear -Hsrc_dest_lt.

      eapply Z2Nat.inj_lt; (int auto).
      clear -Hsrc_dest_lt.
      intro.
      eapply Z2Nat.inj in H.
      lia.
      int auto. int auto.
      rewrite app_length. simpl.
      rewrite H132, H148.
      clear - H138.
      unfold OBJ_POSITION in H138.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.inj_add.
      int auto.
      lia.
      unfold OBJ_POSITION.
      lia.
      unfold OBJ_POSITION.
      unfold Int.max_unsigned. simpl.
      lia.
      rewrite app_length. simpl.
      rewrite H93, H94.
      rewrite S_add_sub_S.
      clear -Hsrc_dest_lt. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      rewrite update_nth_slots_length_imp; eauto.
      rewrite nth_slots_length_imp; eauto.

      eapply get_set_eq.
    }
    {
      eapply RL_Cap_Parent_Child_update_slots_type_remain.
      eapply RL_Cap_Parent_Child_remain. 
      eapply RL_Cap_Parent_Child_remain; auto.
    }
    {
      eapply RLH_CapParent_update_slots_type_remain.
      eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=(v'11 ++
      (i11, i12, v'16 ++ (v'101, (i13, (i14, i15, v0))) :: v'61, i9, l, v, i8)
      :: v'102)); eauto.
      
      eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=(v'11 ++
      (i11, i12, v'16 ++ (v'101, (i13, (i14, i15, v0))) :: v'61, i9, l, v, i8)
      :: v'102)); eauto. 
      rewrite H91.
      rewrite list_trans_1.
      rewrite nth_cspace_length_imp; eauto.
      rewrite app_length. simpl.
      rewrite H93, H94. rewrite S_add_sub_S.
      clear -Hsrc_dest_lt. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; try (int auto).
      rewrite H91.
      (* rewrite list_trans.
      rewrite <-H49. eauto. *)
      (* unfold update_nth_cspace_slots_cap.
      rewrite list_trans_1. *)
      rewrite nth_cspace_length_imp; eauto.
      rewrite <-H141.
      eapply CSpaceMod.map_get_set'.
      clear -Hsrc_dest_lt.
      intro.
      rewrite H in Hsrc_dest_lt.
      lia.
      instantiate(7:= (update_nth_cspace_slots_cap (Z.to_nat (Int.unsigned v'64))
      (Z.to_nat (Int.unsigned ($ x)))
      (update_nth_cspace_slots_cap
          (Z.to_nat (Int.unsigned i))
          (Z.to_nat (v'114 + OBJ_POSITION))
          (v'105 ++
          ((i19, i20, v'106 ++ (v'113, ($ CAP_CATEGORY_TYPE, (v'136, v'137, v'138))) :: v'107,
          i17, l0, v1, i16) :: v'108) ++
          (i24, i25, (v'118 ++ x11) ++ (x1, (x2, (x4, x5, v'138))) :: x12 ++ v'120, i22, l2, v2, i21)
          :: v'109)
          ($ CAP_OBJECT_TYPE, (v'136, v'139, v'138)))
          (($ 0, ($ 0, v'137, Vnull))))).
      unfold update_nth_cspace_slots_cap.
      rewrite list_trans_1.
      rewrite nth_cspace_length_imp; eauto.
      rewrite nth_slots_length_imp; eauto.
      rewrite update_nth_cspace_neqrev; eauto.
      rewrite app_assoc_reverse.
      rewrite nth_cspace_length_imp; eauto.
      rewrite nth_slots_length_imp; eauto.
      rewrite update_nth_cspace_eq; eauto.
      rewrite update_nth_list_length_imp; eauto.
      rewrite update_nth_slots_length_imp; eauto.
      rewrite update_nth_list_len_eq.
      rewrite app_length. simpl. 
      rewrite app_length. simpl.
      rewrite H93, H94, H95.
      rewrite S_add_sub_S.
      rewrite S_add_sub_S_add.
      clear -Hsrc_dest_lt H1.
      lia.
  Optimize Proof.
  Optimize Heap.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      clear -H1. lia.
      rewrite app_length. simpl.
      rewrite app_length. simpl.
      rewrite H93, H94, H95.
      rewrite S_add_sub_S.
      rewrite S_add_sub_S.
      clear -Hsrc_dest_lt H1.
      lia.
      clear -H1. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).

      rewrite app_length. simpl. 
      rewrite app_length. simpl.
      rewrite H93, H94, H95.
      rewrite S_add_sub_S.
      rewrite S_add_sub_S.
      clear -Hsrc_dest_lt H1.
      lia.
      clear -H1. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      clear -Hsrc_dest_lt.
      intro.
      eapply Z2Nat.inj in H.
      lia.
      int auto. int auto.
      rewrite app_length. simpl.
      rewrite H132, H148.
      clear - H138.
      unfold OBJ_POSITION in H138.
      rewrite Z2Nat.inj_add.
      int auto.
      lia.
      unfold OBJ_POSITION.
      lia.
      rewrite app_length. simpl.
      rewrite H93, H94.
      rewrite S_add_sub_S.
      clear -Hsrc_dest_lt. lia.
      clear -Hsrc_dest_lt.
      eapply Z2Nat.inj_lt; (int auto).
      rewrite update_nth_slots_length_imp; eauto.
      rewrite nth_slots_length_imp; eauto.
      eapply get_set_eq.
    }
    go.
    go.
    hoare forward.

    (*GetObjSlotRetval 3rd case*)
    hoare_split_pure_all.
    subst v'65.
    unfold val_inj in H121.
    assert(v'98 = SLOT_NULL_CAP).
    clear -H121.
    rewrite Int.unsigned_repr in H121.
    eauto.
    unfold SLOT_NULL_CAP.
    unfold Int.max_unsigned. simpl.
    lia.
    clear - H135 H123.
    tryfalse.

    (*GetObjSlotRetval 4th case*)
    hoare_split_pure_all.
    unfold ios_cap_defs.OS_LOWEST_PRIO in H124.
    clear -H1 H124.
    tryfalse.

    (*ELSE RETURN FAILURE*)
    hoare_split_pure_all.
    clear -H124.
    unfold CNODE_NONE_FAULT, val_inj in H124.
    assert(Int.eq ($0) ($0) = true) by auto.
    rewrite H121 in H124.
    destruct H124; tryfalse.
    destruct H124.
    sep split in H116.
    eauto.
    sep split in H116.
    clear -H121.
    unfold CNODE_NONE_FAULT, val_inj in H121.
    assert(Int.eq ($0) ($0) = true) by auto.
    rewrite H in H121.
    destruct H121; tryfalse.
  }

  (*The 5th case*)
  hoare_split_pure_all.
  inverts H126.
  hoare forward.
  hoare_split_pure_all.
  clear H126.
  unfold GetObjSlotRetval.
  eapply backward_rule1.
  intros.
  eapply disj_split in H126.
  eauto.
  eapply disj_rule.
  eapply backward_rule1.
  intros.
  sep normal in H126.
  sep lift 2%nat in H126.
  eapply disj_split in H126.
  eauto.
  eapply disj_rule.
  instantiate(1:=Afalse).
  (*GetObjSlotRetval 1st case*)
  hoare_split_pure_all.
  destruct H116.
  tryfalse.
  (*GetObjSlotRetval 2nd case*)
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H133.
  eauto.
  eapply disj_rule.
  hoare_split_pure_all.
  destruct H137.
  subst v'65.
  unfold val_inj, Vint32_inj in H121.
  assert(v'98 = v'118 + OBJ_POSITION).
  clear -H121 H138.
  rewrite Int.unsigned_repr in H121.
  eauto.
  unfold OBJ_POSITION in *.
  unfold Int.max_unsigned. simpl.
  lia.
  clear -H124 H138 H137.
  unfold SLOT_NULL_CAP in H124.
  false.
  subst v'98.
  rewrite <- H137 in H138.
  unfold OBJ_POSITION in H138.
  lia.

  2:{
    (*GetObjSlotRetval 4th case*)
    hoare_split_pure_all.
    clear - H1 H126.
    unfold ios_cap_defs.OS_LOWEST_PRIO in H126.
    lia.
  }

  2:{
    (*ELSE RETURN FAILURE*)
    hoare_split_pure_all.
    clear -H126.
    unfold CNODE_NONE_FAULT, val_inj in H126.
    assert(Int.eq ($0) ($0) = true) by auto.
    rewrite H121 in H126.
    destruct H126; tryfalse.
  }

  2:{
    destruct H126.
    sep split in H116.
    eauto.
    sep split in H116.
    clear -H121.
    unfold CNODE_NONE_FAULT, val_inj in H121.
    assert(Int.eq ($0) ($0) = true) by auto.
    rewrite H in H121.
    destruct H121; tryfalse.
  }

  (*Object not found*)
  hoare_split_pure_all.
  rewrite H91 in H133.
  unfold get_slots in H133.
  rewrite list_trans_1 in H133.
  rewrite nth_cspace_length_imp in H133; auto.
  assert(v'100 = v'114).
  clear -H123 H126.
  rewrite H123 in H126.
  inversion H126.
  trivial.
  subst v'100.
  2:{
    rewrite app_length.
    simpl.
    rewrite H93, H94.
    clear -Hsrc_dest_lt H1.
    rewrite S_add_sub_S. lia.
    eapply Z2Nat.inj_lt; int auto.
  }
  inverts H133.
  rewrite H139 in *.
  clear H139.
  assert((Z.to_nat (Int.unsigned v'114)) < length (v'118 ++ v'119 ++ v'120) )%nat.
  clear -H103 H125.
  rewrite H103.
  unfold SLOT_NUM.
  lia.
  Optimize Proof.
  Optimize Heap.
  eapply nth_slots_exists in H133.
  destruct H133.
  destruct x1.
  destruct p.
  destruct c.
  destruct p.
  rename H133 into Hislots.
  assert(nth_slots (Z.to_nat (Int.unsigned v'114)) (v'118 ++ v'119 ++ v'120) = Some (i32, (i33, (i34, i35, v5)))).
  eauto.
  eapply nth_slots_help_4 in H133.
  destruct H133.
  destruct H133.
  destruct H133.
  destruct H138.
  rewrite H133 in *.

  rewrite H91 in H53.
  lets bak_53: H53.
  unfolds in H53.
  destruct H53.
  assert(Ha: 0 <= Int.unsigned v'64 < 64).
  clear -Hi0lt63.
  int auto. 
  assert(Hb: nth_cspace_val ∘ (Int.unsigned v'64)
    (v'105 ++
    ((i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)
    :: v'108) ++
    (i24, i25, x1 ++ (i32, (i33, (i34, i35, v5))) :: x2, i22, l2, v2, i21)
    :: v'109)  = 
    Some (i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.
  lets Hc: H53 Hb.
  destruct Hc. destruct H141. destruct H141.
  clear Ha Hb.

  assert(Ha: 0 <= Int.unsigned i < 64).
  clear -H1. int auto.
  assert(Hb: nth_cspace_val ∘ (Int.unsigned i)
    ((v'105 ++
    ((i19, i20, v'106 ++ (v'113, (i29, (i30, i31, v4))) :: v'107, i17, l0, v1, i16)
    :: v'108)) ++
    (i24, i25, x1 ++ (i32, (i33, (i34, i35, v5))) :: x2, i22, l2, v2, i21)
    :: v'109)  = 
    Some (i24, i25, x1 ++ (i32, (i33, (i34, i35, v5))) :: x2, i22, l2, v2, i21)).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.
  rewrite app_length. simpl. 
  rewrite H93, H94. rewrite S_add_sub_S. unfold nat_of_Z. clear -Hsrc_dest_lt. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.

  rewrite <- app_assoc_reverse in H53.
  lets Hc: H53 Hb.
  destruct Hc. destruct H143. destruct H143.
  clear Ha Hb.

  rewrite H91 in H117.
  rewrite get_capability_nth_mth_cspace_length_imp in H117; eauto.
  assert(v'135 = $ CAP_OBJECT_TYPE).
  clear -H122.
  rewrite <-H122.
  eapply unsigned_inj.
  int auto.
  rewrite H145 in H117.
  inverts H117.
  
  hoare_lifts_trms_pre (Aop, cspaceid).
  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply move_cap_absimp_succ_objectnot.
  unfold AOSCSpaceObjectPointer, CSpaceGVars, AOSCSpacePrioTbl.
  go.
  eapply can_change_aop_ACSpaceAarrayTptr.
  eapply H143.
  eauto. eauto.
  rewrite <- H133.
  eauto. eauto. eauto.
  clear -H136.
  unfold Slots_neq_object in H136.
  assert (Hexists: 
  (exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy,
    0 <= dest_idx < Z.of_nat (length v'119) /\
    nth_slots (Z.to_nat dest_idx) v'119 =
    Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, v'138)))) \/
  ~ (exists dest_idx dest_slot_type dest_cap_type dest_obj_right dest_dummy,
    0 <= dest_idx < Z.of_nat (length v'119) /\
    nth_slots (Z.to_nat dest_idx) v'119 =
    Some (dest_slot_type, (dest_cap_type, (dest_obj_right, dest_dummy, v'138))))) by tauto.
  destruct Hexists as [Hfailcase|Hnotexists].
  simpljoin.
  assert(0 <= x < Z.of_nat (length v'119)).
  lia.
  lets Hx : H136 H2.
  lets Hx1 : Hx H0.
  destruct Hx1.
  eauto.
  eauto.
  eauto.
  eauto. eauto. eauto.
  
  hoare_split_pure_all.
  eapply seq_rule.
  instantiate(2:=v'139).
  instantiate(2:=i32).
  instantiate(2:=(Int.unsigned v'114)).
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (5::3::6::nil)%nat in H117.
  eapply add_aemp_isr_is_prop in H117. 
  eapply add_isr_is_prop in H117. 
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
  sep cancel A_isr_is_prop.
  sep cancel tcbdllflag.
  instantiate(1:=LV func_capability @ long |-> Vint32 v'62 **
  LV ios_cap_defs.index @ long |-> (V$ x) **
  LV func_capType @ char_t |-> Vint32 v'63 **
  LV destTask_Prio @ char_t |-> Vint32 i **
  LV srcTask_Prio @ char_t |-> Vint32 v'64 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_NONE_FAULT) **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i10) **
  LV y @ char_t |-> Vint32 i4 **
  A_dom_lenv
    ((func_capability, long)
      :: (func_capType, char_t)
        :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
              :: (ios_cap_defs.index, long) :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil)).
  sep auto; eauto.
  split; eauto. go.
  {
    clear -H66.
    eapply Capability_wellform_descendents_update_type.
    eapply Capability_wellform_descendents_update_cap.
    eapply Capability_wellform_descendents_update_cap; auto.
  }
  {
    eapply taskPrioProp_update_slots_type_remain.
    eapply taskPrioProp_update_slots_cap_remain.
    eapply taskPrioProp_update_slots_cap_remain.
    eauto.
  }
  {
    rewrite H91.
    eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
    eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
    eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H93, H94. rewrite S_add_sub_S.
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; try (int auto).
    rewrite list_trans.
    rewrite <-H91. eauto.
    rewrite H91.
    rewrite list_trans_1.
    unfold update_nth_cspace_slots_cap.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_neqrev; eauto.
    rewrite app_assoc_reverse.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
  Optimize Proof.
  Optimize Heap.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite app_length. simpl.
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    clear -Hsrc_dest_lt.
    intro. 
    eapply Z2Nat.inj in H.
    lia.
    int auto. int auto.
    rewrite app_length. simpl.
    rewrite H93, H94.
    rewrite S_add_sub_S. 
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite <-H141.
    eapply CSpaceMod.map_get_set'.
    clear -Hsrc_dest_lt.
    intro.
    rewrite H in Hsrc_dest_lt.
    lia.

    unfold update_nth_cspace_slots_cap.
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_neqrev; eauto.
    rewrite app_assoc_reverse.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_eq; eauto.
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_slots_length_imp; eauto.
    rewrite update_nth_list_len_eq.
    rewrite app_length. simpl. 
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S_add.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    clear -H1. lia.
    rewrite app_length. simpl.
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite app_length. simpl. 
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.

    eapply Z2Nat.inj_lt; (int auto).
    clear -Hsrc_dest_lt.
    intro.
    eapply Z2Nat.inj in H.
    lia.
    int auto. int auto.
    rewrite app_length. simpl.
    rewrite H93, H94.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite update_nth_slots_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.

    eapply get_set_eq.
  }
  {
    eapply RL_Cap_Parent_Child_update_slots_type_remain.
    eapply RL_Cap_Parent_Child_remain. 
    eapply RL_Cap_Parent_Child_remain; auto.
  }
  {
    eapply RLH_CapParent_update_slots_type_remain.
    eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=(v'11 ++
    (i11, i12, v'16 ++ (v'101, (i13, (i14, i15, v0))) :: v'61, i9, l, v, i8)
    :: v'102)); eauto.
    
    eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=(v'11 ++
    (i11, i12, v'16 ++ (v'101, (i13, (i14, i15, v0))) :: v'61, i9, l, v, i8)
    :: v'102)); eauto. 
    rewrite H91.
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H93, H94. rewrite S_add_sub_S.
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; try (int auto).
    rewrite H91.
    
    rewrite nth_cspace_length_imp; eauto.
    rewrite <-H141.
    eapply CSpaceMod.map_get_set'.
    clear -Hsrc_dest_lt.
    intro.
    rewrite H in Hsrc_dest_lt.
    lia.
    instantiate(7:= (update_nth_cspace_slots_cap (Z.to_nat (Int.unsigned v'64))
    (Z.to_nat (Int.unsigned ($ x)))
    (update_nth_cspace_slots_cap
        (Z.to_nat (Int.unsigned i))
        (Z.to_nat (Int.unsigned v'114))
        (v'105 ++
          ((i19, i20, v'106 ++ (v'113, ($ CAP_OBJECT_TYPE, (v'136, v'137, v'138))) :: v'107, i17, l0, v1, i16) :: v'108) ++
          (i24, i25, x1 ++ (i32, (i33, (i34, i35, v5))) :: x2, i22, l2, v2, i21) :: v'109)
        ($ CAP_OBJECT_TYPE, (v'136, v'139, v'138)))
        (($ 0, ($ 0, v'137, Vnull))))).
    unfold update_nth_cspace_slots_cap.
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_neqrev; eauto.
    rewrite app_assoc_reverse.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_cspace_eq; eauto.
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_slots_length_imp; eauto.
    rewrite update_nth_list_len_eq.
    rewrite app_length. simpl. 
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S_add.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    clear -H1. lia.
    rewrite app_length. simpl.
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).

    rewrite app_length. simpl. 
    rewrite app_length. simpl.
    rewrite H93, H94, H95.
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt H1.
    lia.
    clear -H1. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    clear -Hsrc_dest_lt.
    intro.
    eapply Z2Nat.inj in H.
    lia.
    int auto. int auto.
    rewrite app_length. simpl.
    rewrite H93, H94.
    rewrite S_add_sub_S.
    clear -Hsrc_dest_lt. lia.
    clear -Hsrc_dest_lt.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite update_nth_slots_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    eapply get_set_eq.
  }
  go.
  go.
  hoare forward.
  Unshelve. all:exact (Aemp).
Qed.  
