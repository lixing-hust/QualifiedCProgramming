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

Definition user_cnode_revoke_invalid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
    match rst with
      | (opv, O2) => 
         opv = Some (Vint32 (Int.repr OS_PRIO_INVALID)) /\
         O2 = Some O1 /\
         (exists dest captype capability v',
           vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
           ((Int.ltu  (Int.repr OS_LOWEST_PRIO) dest = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true))
         )
    end. 

Definition user_cnode_revoke_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        O2 = Some O1 /\
        (exists dest captype capability v',
          vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          Int.ltu (Int.repr CAP_TASK_TYPE) captype = true
        )
  end. 

Definition user_cnode_revoke_failure (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
    (*这个是没有OSPrioCur这个变量*)
        opv = Some (Vint32 (Int.repr CNODE_REVOKE_FAILURE)) /\
        O2 = Some O1 
end. 
Definition user_cnode_revoke_slotnum (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O2) => 
      exists dest captype capability v',
          vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
          (Int.ltu (Int.repr CAP_TASK_TYPE) captype = false) /\
          (not((Int.ltu  (Int.repr OS_LOWEST_PRIO) dest = true \/ Int.eq dest (Int.repr OS_LOWEST_PRIO) = true))) /\
          O2 = Some O1         
  end.
Definition user_cnode_revoke_nocap (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        (opv = Some (Vint32 (Int.repr USER_CAPABILITY_NONE)) /\ O2 = Some O1)           
  end.
  
  
Definition user_cnode_revoke_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O2) => 
    exists dest captype capability v',
        vl = ((Vint32 dest) ::  (Vint32 captype) :: (Vint32 capability) :: v') /\
        (opv = Some (Vint32 (Int.repr CNODE_REVOKE_SUCCESS)) /\
        (exists acspace acspace' n_capability,
        get O1 cspaceid = Some(capcspace acspace) /\
        reset_descendents_cspace_slot_abs dest n_capability acspace acspace' /\
        O2 = Some (set O1 cspaceid (capcspace acspace'))) 
        )
  end.


Definition user_cnode_revoke_spec (vl: vallist) :=
  user_cnode_revoke_invalid  (|vl|) ??
  user_cnode_revoke_err (|vl|) ??
  user_cnode_revoke_failure (|vl|)??
  user_cnode_revoke_slotnum (|vl|) ?? 
  user_cnode_revoke_nocap(|vl|) ??
  user_cnode_revoke_succ(|vl|).
Definition user_cnode_revoke_api :=
(user_cnode_revoke_spec, (Tint8, Tint8 :: Tint8 :: Tint32 :: nil)).


Lemma user_cnode_revoke_absimp_invalid:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  (Int.ltu ($ OS_LOWEST_PRIO) i  = true \/ Int.eq i ($ OS_LOWEST_PRIO) = true) ->
  absinfer sch ( <|| user_cnode_revoke_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
            ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P ).
Proof.
  infer_solver 0%nat.
Qed.  

Lemma user_cnode_revoke_absimp_wrong:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  Int.ltu ($ CAP_TASK_TYPE) i0 = true ->
  absinfer sch ( <|| user_cnode_revoke_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P ).
Proof.
  infer_solver 1%nat.
Qed. 

Lemma user_cnode_revoke_absimp_failure:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  absinfer sch ( <|| user_cnode_revoke_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr CNODE_REVOKE_FAILURE))) ||> ** P ).
Proof.
infer_solver 2%nat.
Qed. 

Lemma user_cnode_revoke_absimp_slotnum:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  (Int.ltu (Int.repr CAP_TASK_TYPE) i0 = false) ->
  (not ((Int.ltu  (Int.repr OS_LOWEST_PRIO) i = true \/ Int.eq i (Int.repr OS_LOWEST_PRIO) = true))) ->
  absinfer sch ( <|| user_cnode_revoke_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P ).
Proof.
  infer_solver 3%nat.
Qed. 
Lemma user_cnode_revoke_absimp_nocap:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
   absinfer sch ( <|| user_cnode_revoke_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||>  ** P)
           ( <|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||>  ** P ).
Proof.
infer_solver 4%nat.
Qed.

Lemma user_cnode_revoke_absimp_succ:
forall i i0 i1 v' sch P cs cs' n_capability,
can_change_aop P ->
reset_descendents_cspace_slot_abs i n_capability cs cs' ->
absinfer sch ( <|| user_cnode_revoke_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||>  ** 
        Hcapspace cs ** P)
        ( <|| END (Some (Vint32 (Int.repr CNODE_REVOKE_SUCCESS))) ||>  
        ** Hcapspace cs'** P ).
Proof.
  infer_solver 5%nat. 
Qed.
Lemma UserCnodeRevokeProof: 
  forall  tid vl p r, 
    Some p =
    BuildPreA' os_api user_cnode_revoke
    user_cnode_revoke_api vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api user_cnode_revoke
    user_cnode_revoke_api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api user_cnode_revoke = Some (t, d1, d2, s) /\ 
            {|Cap_spec, GetHPrio, OSLInv,  I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  lzh_hoare_if; pure_auto.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply user_cnode_revoke_absimp_invalid.
  go.
  unfold val_inj, bool_or in LHift_true; pure_auto.
  hoare forward.

  hoare forward prim. pure_auto.
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
  eapply user_cnode_revoke_absimp_wrong.
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
  assert(Hi0: Int.unsigned i0 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H2. int auto.
  assert(Hi: Int.unsigned i <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H3. int auto.
  unfold CapabilityInv.
  pure intro.
  rename H7 into Hwellform_descendents.
  rename H8 into H7.
  rename H9 into H8.
  destruct v'24.

  unfold EvtInv.
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  unfold AGVars.
  hoare_split_pure_all.
  destruct v'60.
  destruct v'61.
  destruct v'62.
  eapply backward_rule1.
  intros.
  Require Import seplog_trm_tacs.
  sep_lifts_trms_in H33 (Aisr, Ais, A_isr_is_prop).
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
  rewrite Hi0. auto.
  eapply rvl_elim. sep get rv.
  rewrite Hi. auto.
  eapply rvl_nil.
  intros.
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
  sep cancel func_capability.
  exact H33.
  8:{
    unfold AOSCSpaceCapParent.    
    unfold CSpaceGVars.
    good_frm_sovler.
    (* eapply GoodFrm_ACSpaceAarrayTptr.     *)
  }
  5: simpl;eauto.
  5: simpl;eauto.
  5: simpl;eauto.  
  all: eauto.
  apply retpost_CheckCapTypeWeakPost.
  simpl. rewrite Hi0. rewrite Hi. auto.
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
  
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H33 (Aisr, Ais).
  eapply add_a_isr_is_prop in H33.
  sep_lifts_trms_in H33 (Aisr, Ais, Aier).
  eapply add_aemp_isr_is_prop in H33.  
  exact H33. 

  eapply backward_rule1 with (p:=<||
  user_cnode_revoke_spec (Vint32 v'63 :: Vint32 v'62 :: Vint32 v'61 :: v')
  ||>  **
  OldOSInvWL tid (logic_val (V$ 1)::logic_val (V$ __EvLoc_normal)
  :: logic_val Vnull
     :: logic_val Vnull :: logic_val Vnull :: nil) **
   aemp_isr_is **
   Aisr empisr ** Aier v'64 ** Aie false ** Ais nil ** Acs (true :: nil) **
   ([|Some v'60 = Some (V$ SLOT_NUM)|] \\//
    [|exists ret, Some v'60 = Some (V$ ret) /\ 0 <= ret < 255 /\
    (Int.unsigned v'62 = CAP_FUNCTION_TYPE /\
    Int.unsigned v'61 <= CAP_CHANNEL_CLASS \/
    (Int.unsigned v'62 = CAP_SEM_TYPE \/
     Int.unsigned v'62 = CAP_MUTEX_TYPE \/
     Int.unsigned v'62 = CAP_Q_TYPE) /\
    Int.unsigned v'61 < OS_USER_MAX_EVENTS / 3 \/
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
  sep_lifts_trms_in H33 v'60.
  eapply disj_split in H33.
  destruct H33.
  assert(v'60 = (Vint32 (Int.repr SLOT_NUM))).
  sep split in H33. inverts H34. auto.
  sep_lifts_trms v'60.
  eapply disj_split.
  left.

  sep pauto.
  sep split in H33.
  simpljoin.
  sep pauto.
  sep split; eauto.
  right. sep split; eauto.
  (*end*)  

  pure intro.
  lzh_hoare_if.
  sep_lifts_trms_in H24 v'60.
  eapply disj_split in H24.
  destruct H24. sep split in H24.
  inverts H33. auto.
  sep split in H24. simpljoin.
  inverts H33. auto. 
  unfold val_inj, val_eq.
  sep_lifts_trms_in H24 v'60.
  eapply disj_split in H24.
  destruct H24. sep split in H24.
  inverts H33. auto.
  sep split in H24. simpljoin.
  inverts H33. auto. 
  destruct (Int.eq ($ x) ($ SLOT_NUM)); auto.

  eapply seq_rule.
  hoare forward prim. 
  go. 
  unfold GoodFrm. auto.  

  hoare_lifts_trms_pre (Aop).
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply user_cnode_revoke_absimp_slotnum.
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
  destruct H24; sep split in H24; eauto.
  eapply backward_rule1. intros.
  sep_lifts_trms_in H24 (SLOT_NUM).
  eapply disj_split in H24.
  exact H24. 
  eapply disj_rule.
  hoare_split_pure_all. inverts H24.
  false.
  unfold val_inj, val_eq in Hif_false1.
  rewrite Int.eq_true in Hif_false1.
  destruct Hif_false1; tryfalse.

  unfold OldOSInvWL.
  unfold AOSTCBList;unfold_dll.
  pure intro.

  assert(Hpriolt64:Int.unsigned i3 < 64).
  unfold TCBList_P in H41.
  simpljoin.
  unfold TCBNode_P in H44.
  destruct x3, p, p.
  simpljoin. 
  unfold RL_TCBblk_P in H61.
  simpljoin.
  unfold V_OSTCBPrio in H61. simpl in H61.
  inverts H61. lia.
  assert(Hi3: Int.unsigned i3 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -Hpriolt64. int auto.
  rename Hi0 into Hv'62.
  rename Hi into Hv'63.

  hoare forward. 
  go.
  pure intro.
  unfold CapabilityInv.
  hoare_split_pure_all.
  rename H62 into Hwellform_descendents1.
  destruct v'10. 
  hoare remember (1::nil)%nat pre.
  unfold AOSCSpacePrioTbl. hoare_split_pure_all.
  assert(Htypematch : array_type_vallist_match CSPACE ∗ v'15).
  simpljoin. auto.
  assert(Hlenv'15: length v'15 = 64%nat). simpljoin. auto.
  assert(Hlenv'60: length v'60 = 64%nat). simpljoin. auto.
  eapply backward_rule1 with (p:=AOSCSpacePrioTbl (b, i6) v'15 v'60 v'97 ** H62).
  intros.
  unfold AOSCSpacePrioTbl. 
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep split; auto.
  subst H62.
  clear H63.
  hoare_lifts_trms_pre (Aop, AOSCSpacePrioTbl, Alvarmapsto pCSpace, Alvarmapsto y, A_dom_lenv, p_local).
  hoare remember (1::2::3::4::5::6::nil)%nat pre.
  unfold AOSCSpacePrioTbl.
  hoare_split_pure_all.
  eapply seq_rule.
  
  eapply assign_rule_lvar.
  {
    intros. split. intros.
    sep_lifts_trms_in H64 (pCSpace).
    exact H64.
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
    exact H64.
    simpl. auto.
    eauto.
    sep get rv.
    rewrite Hi3. auto.
    eauto. auto. lia. lia.
    rewrite Hlenv'15. auto.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hlenv'15. lia.
  }
  eapply eq_vptr. eauto.
  intros. eexists. sep cancel p_local. simpl. auto.
  eapply backward_rule1 with(p:=<|| user_cnode_revoke_spec (Vint32 v'63 :: Vint32 v'62 :: Vint32 v'61 :: v')
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
               p_local OSLInv (v'96, Int.zero) init_lg ** H62).
  intros. unfold AOSCSpacePrioTbl.
  sep cancel H62. sep auto.
  subst H62.
  assert(HpCSpacetype: rule_type_val_match CSPACE ∗
  (nth_val' (Z.to_nat (Int.unsigned i3)) v'15) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hlenv'15. lia.
  clear H63.
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
  eauto.  eauto. eauto.
  go. go.

  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply user_cnode_revoke_absimp_failure.
  can_change_aop_solver.
  hoare forward.
  eapply disj_rule. 
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hnotnull: (nth_val' (Z.to_nat (Int.unsigned i3)) v'15) <> Vnull).
  clear -HpCSpacetype  H62.
  unfold rule_type_val_match in HpCSpacetype.
  unfold val_inj, val_eq in H62.
  destruct (nth_val' (Z.to_nat (Int.unsigned i3)) v'15); destruct H62; tryfalse.
  destruct a; auto. destruct a. auto.
  clear H62.
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H62 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned i3)) in H62.

  exact H62.
  rewrite Hlenv'60.
  lia.
  auto.
  hoare_split_pure_all.
  unfold ACSpace.
  destruct v'100, p, p, p, v'104.
  unfold Acnode. 
  destruct c, p. 
  hoare_split_pure_all.
  simpljoin.
  rename H71 into Hi7range.
  rename H72 into H71.
  rename H73 into H72.

  eapply backward_rule1.
  intros.
   
  sep_lifts_trms_in H62 (ASlots).
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(SLOT_CNODE_CAP)) in H62; eauto. 
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  hoare_split_pure_all.
  simpljoin.
  unfold ACap. destruct v'104, c, p. 
  unfold AOSCSpaceCapParent.
  hoare_split_pure_all.
  destruct H75.
  destruct H76. 
  assert(Hx: (Z.to_nat(Int.unsigned v'63) < 64)%nat).
  clear -destlt64.
  change ios_cap_defs.OS_LOWEST_PRIO with 63 in destlt64. lia. 
  lets Hy: nthval'_has_value_Tint32 H75 H76 Hx.
  destruct Hy. destruct H78.
  assert (nth_val' (Z.to_nat (Int.unsigned i3))
        (v'102 ++ Vptr (b0, i9) :: v'103) = Vptr (b0, i9)).
  eapply nth_val'_length_imp. eauto.
  rewrite H80.
  eapply forward_rule1 with(q:=Afalse \\//Afalse).
  intros.
  destruct H81; auto.
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
                sep cancel pCSpace. exact H81.
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

  sep normal in H81.
  sep lift 5%nat in H81.
  unfold Aptrmapsto in H81 at 1.
  exact H81.
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
  destruct(Int.eq (i14&ᵢ$ CNODE_REVOKE_CAP) ($ 0)); auto.
  simpl. eauto.
  sep get rv.
  rewrite Hv'63. auto. 
  rewrite H78. auto. go.
  rewrite H78. 
  unfold val_inj, val_eq.
  destruct (Int.eq x0 i3); eauto.
  rewrite H78. 
  unfold val_inj, notint, val_eq.
  destruct (Int.eq x0 i3); eauto.
  rewrite Hv'63. auto. go.
  unfold val_inj.
  destruct (Int.eq v'63 i3);eauto.
  unfold val_inj, notint.
  destruct (Int.eq v'63 i3); eauto.
  unfold val_inj, bop_eval, val_eq, and, uop_eval, notint, bool_and.
  unfold Int.zero.
  rewrite H78.
  destruct (Int.eq x0 i3);destruct (Int.eq v'63 i3);unfold Int.notbool;repeat (val_help;simpl); auto.
  simpl. eauto.
  unfold val_inj, bop_eval, val_eq, and, uop_eval, notint, bool_and.
  unfold Int.zero.
  rewrite H78.
  destruct (Int.eq (i14&ᵢ$ CNODE_REVOKE_CAP) ($ 0));destruct (Int.eq v'63 i3);destruct (Int.eq x0 i3);unfold Int.notbool;repeat (val_help;simpl); auto.
  simpl. eauto.

  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H82. 
  eapply fold_Cap in H82.
  sep lifts (2::3::1::4::nil)%nat in H82.
  eapply ASlots_fold_any_idx_frm in H82; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H82.
  eapply fold_Acnode in H82.
  sep lifts (1::6::7::8::9::nil)%nat in H82.
  eapply fold_ACSpace  in H82; [idtac | eauto..]. 
  sep lifts (5::1::6::nil)%nat in H82. 
  eapply ACSpaceAarray_fold_any_idx_frm in H82; [idtac | eauto; try lia..]. 
  sep lifts (2::1::3::4::nil)%nat in H82.
  eapply fold_AOSCSpacePrioTbl1 in H82.
  exact H82. 
  rewrite app_length. simpl.
  rewrite H64, H72. rewrite S_add_sub_S. lia.
  clear -Hpriolt64. lia.
  rewrite app_length. simpl.
  rewrite H65, H71. rewrite S_add_sub_S. lia. lia.
  eauto.
  rewrite nth_val_imp_nth_val'_2. rewrite H80. eauto.
  rewrite app_length. simpl. 
  rewrite H64, H72. rewrite S_add_sub_S. lia. lia.
  clear -Hpriolt64. lia. 
  rewrite app_length. simpl. 
  rewrite H63, H74. rewrite S_add_sub_S.
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

  hoare_lifts_trms_pre (Aop).
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply user_cnode_revoke_absimp_nocap.
  can_change_aop_solver.
  unfold can_change_aop. auto.
  hoare forward.

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
  eapply fold_AOSCSpacePrioTbl1 in H81; [idtac | eauto; try lia..].
  sep_lifts_trms_in H81 (aemp_isr_is).  
  eapply aemp_isr_elim in H81.
  sep_lifts_trms_in H81 (Aisr, Ais, A_isr_is_prop).
  eapply elim_a_isr_is_prop in H81. 
  exact H81.
  rewrite nth_val_imp_nth_val'_2. rewrite H80. eauto.
  rewrite Hlenv'15. lia. 
  eauto.
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  eauto.
  unfold EvtInv.
  unfold ASemEIBs.
  unfold AMuxEIBs.
  unfold AMqEIBs.
  hoare_split_pure_all.
  destruct v'125. destruct v'124.
  destruct v'123.
  assert(Hwellform_descendents_bak: Capability_wellform_descendents
  (v'10 ++
   (i10, i11,
   v'15 ++
   (v'100,
   (i12,
   (i13, i14, v0)))
   :: v'60, i8, l,
   v, i7) :: v'101)
  v'97) by auto.
  unfolds in Hwellform_descendents_bak.
  lets Hexist: Hwellform_descendents_bak v'63.
  assert(Hy: 0 <= Int.unsigned v'63 < 64).
  clear -destlt64.
  unfold ios_cap_defs.OS_LOWEST_PRIO in destlt64.
  int auto.
  lets Hz: Hexist Hy. destruct Hz.
  clear Hexist Hy.
  rename H104 into Hwellform_descendents_v'63.
  eapply seq_rule.  
  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_CNode_Revoke_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hv'63. auto.
  eapply rvl_elim. 
  sep get rv. rewrite Hv'62. auto.
  eapply rvl_elim.
  sep get rv. 
  
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_CNode_RevokePre.
  unfold ucos_CNode_RevokePre'.

  sep normal. sep eexists.  
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel ASeminfo. 
  sep cancel APthreadMutex.
  sep cancel AMqAttr. 
  sep cancel AOSCSpaceObjectPointer.  
  sep cancel AOSTCBPrioTbl.
  sep cancel (Alvarmapsto ios_cap_defs.i).
  exact H104.
  go. eauto. eauto.
  2: simpl; eauto.
  2: simpl; eauto.
  2: simpl; eauto.
  eapply Hwellform_descendents_v'63.
  unfold CSpaceGVars.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  Lemma retpost_ucos_CNode_RevokePost: 
    retpost ucos_CNode_RevokePost.
  Proof.
    unfolds.
    unfold getasrt.
    unfold ucos_CNode_RevokePost.
    unfold ucos_CNode_RevokePost'.
    intros.
    sep normal in H. sep destruct H.
    sep_lifts_trms_in H (ios_cap_defs.OS_PRIO_INVALID).
    eapply disj_split in H.
    destruct H. sep split in H. inverts H1. auto.
    sep normal in H. sep lift 3%nat in H.
    eapply disj_split in H. destruct H.
    sep split in H. inverts H2. auto.
    sep split in H. inverts H2. auto.
  Qed.
  eapply retpost_ucos_CNode_RevokePost.
  simpl. rewrite Hv'63. rewrite Hv'62. auto.
  unfold getasrt. unfold ucos_CNode_RevokePost.
  unfold ucos_CNode_RevokePost'.
  intros.
  sep normal in H104. sep destruct H104.
  eexists. sep cancel p_local. simpl. auto.
  unfold getasrt. unfold ucos_CNode_RevokePre.
  unfold ucos_CNode_RevokePre'.
  intros.
  sep normal in H104. sep destruct H104.
  eexists. sep cancel p_local. simpl. auto.
  unfold getasrt. unfold ucos_CNode_RevokePost.
  unfold ucos_CNode_RevokePost'.
  hoare_split_pure_all.
  simpl in H106, H104, H105.
  inverts H105.
  inverts H104.
  inverts H106.
  inverts H109.

  (*1 case*)
  eapply backward_rule1. intros.
  sep_lifts_trms_in H96 (Int.unsigned v'124).
  eapply disj_split in H96.
  exact H96.
  apply disj_rule.
  hoare_split_pure_all.
  subst v'133.
  inverts H105.
  hoare forward.
  hoare_split_pure_all.
  clear -H105.
  unfold ios_cap_defs.OS_PRIO_INVALID, CNODE_NONE_FAULT in H105.
  assert(Int.eq ($ 42) ($ 0) = false).
  clear -H105. int auto.
  rewrite H104 in H105.
  unfold val_inj in H105.
  destruct H105; tryfalse.
  (*ELSE failure*)
  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 

  sep lifts (4::2::5::nil)%nat in H106.
  eapply add_aemp_isr_is_prop in H106.
  eapply add_isr_is_prop in H106. 
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
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. sep cancel AOSTCBFreeList.
  sep cancel OSTCBList. sep cancel OSTCBCur.
  sep cancel AGVars.
  sep cancel AOSRdyTblGrp.
  sep cancel AOSTime.
  sep cancel APthreadAttr.
  sep cancel A_isr_is_prop. sep cancel IntInv.
  sep cancel TmrInv. sep cancel tcbdllflag.
  sep cancel aemp_isr_is.
  unfold EvtInv. unfold ASemEIBs, AMuxEIBs, AMqEIBs.
  sep normal. sep eexists.
  sep cancel AOSEventFreeList. sep cancel AOSQFreeList.
  sep cancel AECBList. sep cancel AOSQFreeBlk.
  sep cancel AErrblkList. sep cancel APosblkList.
  sep cancel AEvAtomHeap. sep cancel AEvStructHeap.
  sep cancel AEvArrayHeap. 
  sep cancel ASeminfo. sep cancel ASemCap.
  sep cancel AMqAttr. sep cancel AMqCap.
  sep cancel APthreadMutex. sep cancel AMuxCap.
  sep cancel tcbllsegevaux.
  instantiate(1:=LV func_capability @ long
  |-> (V$ x) **
  LV func_capType @ char_t
  |-> Vint32 v'125 **
  LV destTask_Prio @ char_t
  |-> Vint32 v'124 **
  LV ios_cap_defs.i @ char_t
  |-> (V$ ios_cap_defs.OS_PRIO_INVALID) **
  LV pCSpace @ CSPACE ∗
  |-> Vptr (b0, i9) **
  LV y @ char_t |-> Vint32 i3 **
  A_dom_lenv
    ((func_capability, long)
      :: (func_capType, char_t)
        :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
              :: (ios_cap_defs.i,
                  char_t)
                  :: (y, char_t)
                    :: nil)).
  
  sep auto; eauto.
  split. eauto.
  go. 
  go. 
  eauto.

  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply user_cnode_revoke_absimp_failure.
  can_change_aop_solver.
  hoare forward.

  destruct H105. sep split in H104.
  assert(Int.eq
  ($
   ios_cap_defs.OS_PRIO_INVALID)
  ($ CNODE_NONE_FAULT) = false).
  unfold ios_cap_defs.OS_PRIO_INVALID, CNODE_NONE_FAULT.
  auto.
  rewrite H106 in H105.
  unfold val_inj in H105. destruct H105; tryfalse.
  sep split in H104; auto.

  (*2 cases*)
  eapply backward_rule1.
  intros.
  sep normal in H96.
  sep lift 3%nat in H96.
  eapply disj_split in H96.
  exact H96.
  eapply disj_rule.
  1:{
    hoare_split_pure_all.
    inverts H106.
    hoare forward.
    hoare_split_pure_all.
    clear H106.
    2:{
      hoare_split_pure_all.
      false.
      rewrite Int.eq_true in H106.
      unfold val_inj in H106.
      destruct H106; tryfalse.
    }
    assert(exists acspace',
    reset_descendents_cspace_slot_abs v'124
      ($ Z.of_nat (Z.to_nat (Int.unsigned ($ x)))) v'87 acspace' /\
    RLH_cspace_slots_P v'133 acspace' v'136 v'98).
    clear -H105 H49. 
    lets Hx: reset_descendents_cspace_slot_LRH  H105 H49. 
    eauto.
    rewrite Int.unsigned_repr in H106.
    2:{
      clear -H46 H48.
      rewrite max_unsigned_val. lia.
    }
    destruct H106.
    rewrite Z2Nat.id in H106.
    2:{
      clear -H46. lia.
    }
    destruct H106.
    rename H106 into Hreset_abs.
    rename H111 into HRLH_cspace_slots_P.
    hoare lifts (6::44::nil)%nat pre.
    eapply abscsq_rule'.
    Hint Resolve noabs_oslinv.
    go.
    
    
    eapply user_cnode_revoke_absimp_succ.
    unfold AOSCSpacePrioTbl, AOSCSpaceObjectPointer, CSpaceGVars.
    can_change_aop_solver.
    eapply can_change_aop_ACSpaceAarrayTptr.
    eauto.
  
    eapply seq_rule.
    eapply forward_rule2.
    hoare_lifts_trms_pre (Aop).
    eapply excrit1_rule'_ISnil_ISRemp'''_lg.
    intros. 

    sep lifts (5::3::6::nil)%nat in H106.
    eapply add_aemp_isr_is_prop in H106.
    eapply add_isr_is_prop in H106. 
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
    sep cancel CoreCommuInv. sep cancel PartitionInv.
    sep cancel Acs. sep cancel Aier. sep cancel Ais.
    sep cancel Aisr. sep cancel Aie. sep cancel p_local.
    sep cancel Astruct. sep cancel dllseg.
    sep cancel dllseg. sep cancel AOSTCBFreeList.
    sep cancel OSTCBList. sep cancel OSTCBCur.
    sep cancel AGVars.
    sep cancel AOSRdyTblGrp.
    sep cancel AOSTime.
    sep cancel APthreadAttr.
    sep cancel A_isr_is_prop. sep cancel IntInv.
    sep cancel TmrInv. sep cancel tcbdllflag.
    sep cancel aemp_isr_is.
    unfold EvtInv. unfold ASemEIBs, AMuxEIBs, AMqEIBs.
    sep normal. sep eexists.
    sep cancel AOSEventFreeList. sep cancel AOSQFreeList.
    sep cancel AECBList. sep cancel AOSQFreeBlk.
    sep cancel AErrblkList. sep cancel APosblkList.
    sep cancel AEvAtomHeap. sep cancel AEvStructHeap.
    sep cancel AEvArrayHeap. 
    sep cancel ASeminfo. sep cancel ASemCap.
    sep cancel AMqAttr. sep cancel AMqCap.
    sep cancel APthreadMutex. sep cancel AMuxCap.
    sep cancel tcbllsegevaux.
    instantiate(1:=LV func_capability @ long
    |-> (V$ x) **
    LV func_capType @ char_t
    |-> Vint32 v'125 **
    LV destTask_Prio @ char_t
    |-> Vint32 v'124 **
    LV ios_cap_defs.i @ char_t
    |-> (V$ CNODE_NONE_FAULT) **
    LV pCSpace @ CSPACE ∗
    |-> Vptr (b0, i9) **
    LV y @ char_t |-> Vint32 i3 **
    A_dom_lenv
      ((func_capability, long)
        :: (func_capType, char_t)
          :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i,
                    char_t)
                    :: (y, char_t)
                      :: nil)).
    sep auto; eauto.
    split. eauto.
    go. 
    go. 
    eauto.
    eapply reset_descendents_cspace_slot_abs_Capability_wellform_descendents_keep; eauto.
    eapply reset_descendents_cspace_slot_abs_taskPrioProp_keep; eauto.
    eapply reset_descendents_cspace_slot_abs_RL_Cap_Parent_Child_keep'; eauto.
    eapply reset_descendents_cspace_slot_RLH_CapParent_keep; eauto.
    go.
    intros. eauto.
    hoare forward.
    destruct H106. sep split in H104. auto.
    sep split in H104.
    rewrite Int.eq_true in H106.
    unfold val_inj in H106.
    destruct H106; tryfalse.
  }
  {
    hoare_split_pure_all.
    subst v'137.
    inverts H106.
    hoare forward.
    hoare_split_pure_all.
    clear -H96.
    unfold ios_cap_defs.OS_PRIO_INVALID, CNODE_NONE_FAULT in H96.
    assert(Int.eq ($ 42) ($ 0) = false).
    clear -H96. int auto.
    rewrite H104 in H96.
    unfold val_inj in H96.
    destruct H96; tryfalse.
    (*ELSE failure*)
    hoare_split_pure_all.
    eapply seq_rule.
    eapply forward_rule2.
    hoare_lifts_trms_pre (Aop).
    eapply excrit1_rule'_ISnil_ISRemp'''_lg.
    intros. 

    sep lifts (4::2::5::nil)%nat in H106.
    eapply add_aemp_isr_is_prop in H106.
    eapply add_isr_is_prop in H106. 
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
    sep cancel CoreCommuInv. sep cancel PartitionInv.
    sep cancel Acs. sep cancel Aier. sep cancel Ais.
    sep cancel Aisr. sep cancel Aie. sep cancel p_local.
    sep cancel Astruct. sep cancel dllseg.
    sep cancel dllseg. sep cancel AOSTCBFreeList.
    sep cancel OSTCBList. sep cancel OSTCBCur.
    sep cancel AGVars.
    sep cancel AOSRdyTblGrp.
    sep cancel AOSTime.
    sep cancel APthreadAttr.
    sep cancel A_isr_is_prop. sep cancel IntInv.
    sep cancel TmrInv. sep cancel tcbdllflag.
    sep cancel aemp_isr_is.
    unfold EvtInv. unfold ASemEIBs, AMuxEIBs, AMqEIBs.
    sep normal. sep eexists.
    sep cancel AOSEventFreeList. sep cancel AOSQFreeList.
    sep cancel AECBList. sep cancel AOSQFreeBlk.
    sep cancel AErrblkList. sep cancel APosblkList.
    sep cancel AEvAtomHeap. sep cancel AEvStructHeap.
    sep cancel AEvArrayHeap. 
    sep cancel ASeminfo. sep cancel ASemCap.
    sep cancel AMqAttr. sep cancel AMqCap.
    sep cancel APthreadMutex. sep cancel AMuxCap.
    sep cancel tcbllsegevaux.
    instantiate(1:=LV func_capability @ long
    |-> (V$ x) **
    LV func_capType @ char_t
    |-> Vint32 v'125 **
    LV destTask_Prio @ char_t
    |-> Vint32 v'124 **
    LV ios_cap_defs.i @ char_t
    |-> (V$ ios_cap_defs.OS_PRIO_INVALID) **
    LV pCSpace @ CSPACE ∗
    |-> Vptr (b0, i9) **
    LV y @ char_t |-> Vint32 i3 **
    A_dom_lenv
      ((func_capability, long)
        :: (func_capType, char_t)
          :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i,
                    char_t)
                    :: (y, char_t)
                      :: nil)).
    sep auto; eauto.
    split. eauto.
    go. 
    go. 
    eauto.

    hoare abscsq.
    Hint Resolve noabs_oslinv.
    go.
    eapply user_cnode_revoke_absimp_failure.
    can_change_aop_solver.
    hoare forward.

    destruct H96. sep split in H96.
    assert(Int.eq
    ($
    ios_cap_defs.OS_PRIO_INVALID)
    ($ CNODE_NONE_FAULT) = false).
    unfold ios_cap_defs.OS_PRIO_INVALID, CNODE_NONE_FAULT.
    auto.
    rewrite H105 in H104.
    unfold val_inj in H104. destruct H104; tryfalse.
    sep split in H96; auto.
  }
  Unshelve. all: exact (Aemp).
Qed.
