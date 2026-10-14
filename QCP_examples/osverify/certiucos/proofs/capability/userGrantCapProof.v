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
Require Import sep_auto.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import Lia.
Require Import sem_lab. 
Require Import CapPure.
Require Import userGrantCapPure.
Require Import abs_op_capability. 
Require Import CapRelLemmas.

Import DeprecatedTactic.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.
Set Keyed Unification.


Ltac val_help:=
  try change (Int.ltu Int.zero Int.zero) with (false);
  try change (Int.ltu Int.one Int.zero) with (false);
  try change (Int.ltu Int.zero Int.one) with (true);
  try change (Int.ltu Int.one Int.one) with (false);
  try change (Int.eq Int.one Int.one) with (true);
  try change (Int.eq Int.one Int.zero) with (false);
  try change (Int.eq Int.zero Int.one) with (false);
  try change (Int.eq Int.zero Int.zero) with (true).

Lemma grant_cspace_cap_absimp_null:
forall i i0 i1 v' sch P,
  can_change_aop P -> 
  (Int.ltu ($ OS_LOWEST_PRIO) i  = true \/ Int.eq i ($ OS_LOWEST_PRIO) = true)->
  absinfer sch ( <|| grant_cspace_cap_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** P)
           ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P ).
Proof.
infer_solver 0%nat.
Qed.  

Lemma grant_cspace_cap_absimp_succ_fail:
  forall i i0 i1 v' sch P,
  can_change_aop P -> 
  absinfer sch ( <|| grant_cspace_cap_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> **P)
              ( <|| END (Some (Vint32 (Int.repr CNODE_GRANT_FAILURE))) ||>  **P).

Proof.
  infer_solver 2%nat.
Qed. 


Lemma grant_cspace_cap_absimp_succ:
forall i i0 i1 v' sch P tls ready ct p msg sus cs cur_slots cur_childs parent 
      dest_slots dest_childs dest_parent cur_slot_type cur_cap_type cur_cap_right cur_cap_content cur_object_t
      dest_slot_type  dest_cap_type dest_cap_content dest_cap_right dest_object_t,
  get tls ct = Some (p, ready, msg, sus) -> 
  get cs p =   Some (cur_slots, cur_childs, parent) ->
  nth_slots (Z.to_nat (Int.unsigned ($ SLOT_CNODE_CAP))) cur_slots =
  Some (cur_slot_type, (cur_cap_type, (cur_cap_content, cur_cap_right, cur_object_t))) ->
  can_change_aop P -> 
  get cs i = Some (dest_slots, dest_childs, dest_parent) ->
  Int.ltu i ($ OS_LOWEST_PRIO) = true  ->
  nth_slots (Z.to_nat (Int.unsigned i0)) dest_slots =
  Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) ->
  Int.eq
  (cur_cap_right&ᵢ$ CNODE_GRANT_CAP) ($ 0) = false ->
  Int.eq p dest_parent = true ->
  absinfer sch ( <|| grant_cspace_cap_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> ** HTCBList tls
                   ** HCurTCB ct ** Hcapspace cs ** P)
              ( <|| END (Some (Vint32 (Int.repr CSPACE_NONE_FAULT))) ||> ** HTCBList tls ** HCurTCB ct ** 
                Hcapspace (set cs i
                 (update_nth_slots
                  (Z.to_nat (Int.unsigned i0))
                   dest_slots
                  (dest_slot_type,  ($ CAP_CATEGORY_TYPE, (i0, Int.or (dest_cap_right&ᵢ$ 4095) i1, dest_object_t))), dest_childs, dest_parent)) ** P).

Proof.
infer_solver 3%nat.
Qed.


Lemma grant_cspace_cap_absimp_capabilitynone:
forall i i0 i1 v' sch P ,
  can_change_aop P -> 
  absinfer sch ( <|| grant_cspace_cap_spec (Vint32 i :: Vint32 i0 :: Vint32 i1 :: v') ||> **P)
              ( <|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||>  **P).

Proof.
  infer_solver 4%nat. 
Qed.

Lemma grant_cspace_cap_absimp_curpspace_null:
  forall dest funcap rights v' sch P,
  can_change_aop P -> 
  absinfer sch ( <|| grant_cspace_cap_spec (Vint32 dest :: Vint32 funcap :: Vint32 rights :: v') ||> **P)
              ( <|| END (Some (Vint32 (Int.repr CNODE_GRANT_FAILURE))) ||>  **P).

Proof.
  infer_solver 1%nat.
Qed. 

Open Scope int_scope.


Lemma UserGrantCapProof: 
  forall  tid vl p r, 
    Some p =
    BuildPreA' os_api grant_cspace_cap
    grant_cspace_cap_api vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api grant_cspace_cap
    grant_cspace_cap_api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api grant_cspace_cap = Some (t, d1, d2, s) /\ 
            {|Cap_spec, GetHPrio, OSLInv,  I, r, Afalse|}|-tid {{p}} s {{Afalse}}.
Proof.
  init_spec.
  simpljoin.
  lzh_hoare_if; pure_auto.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  auto.
  eapply grant_cspace_cap_absimp_null.
  can_change_aop_solver.
  unfold val_inj in LHift_true;pure_auto.
  hoare forward.
  
  assert(Hiltlowestprio: Int.unsigned i < 63).
  clear -Hif_false. unfold  ios_cap_defs.OS_LOWEST_PRIO in *.
  int auto;
  unfold val_inj, bop_eval,  bool_or, val_eq in Hif_false;
  try change (Int.ltu Int.zero Int.zero) with (false) in Hif_false;
  try change (Int.ltu Int.zero Int.one) with (true) in Hif_false; simpl in Hif_false;
  destruct Hif_false; tryfalse.
  assert(Hilt64:Int.unsigned i < 64 ) by lia.
  (*在这里unfold OSTCBCur*)
  hoare forward prim; pure_auto.
  pure intro.
  try unfold OSInv; try unfold AOSTCBList;unfold_dll.
  pure intro.
  unfold AGVars.
  hoare forward.
  go. 
  pure intro.
  pure intro.


  assert(Hpriolt64:Int.unsigned i6 < 64).
  clear -H9.
  unfold TCBList_P in H9.
  simpljoin.
  unfold TCBNode_P in H2.
  destruct x2, p, p. 
  simpljoin.
  unfold RL_TCBblk_P in H5.
  simpljoin.
  unfold V_OSTCBPrio in H5. simpl in H5. inverts H5. lia.

  assert(Htrue: Int.unsigned i6 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -Hpriolt64. int auto.
  assert(Hitrue: Int.unsigned i <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H3. int auto.

  unfold CapabilityInv.
  hoare_split_pure_all.
  rename H27 into Hcap_well_des.
  destruct v'39.
  hoare remember (1::nil)%nat pre.
  unfold AOSCSpacePrioTbl. hoare_split_pure_all.
  assert(Htypematch : array_type_vallist_match CSPACE ∗ v'40).
  simpljoin. auto.
  assert(Hlenv'40: length v'40 = 64%nat). simpljoin. auto.
  assert(Hlenv'41: length v'41 = 64%nat). simpljoin. auto.
  eapply backward_rule1 with (p:=AOSCSpacePrioTbl (b, i9) v'40 v'41 v'42 **
  H27).
  intros.
  unfold AOSCSpacePrioTbl. 
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep split; auto.
  subst H27.
  clear H28.

  Require Import seplog_trm_tacs.
  hoare_lifts_trms_pre (Aop, AOSCSpacePrioTbl, Alvarmapsto pCSpace, Agvarmapsto OSPrioCur, A_dom_lenv, p_local).
  hoare remember (1::2::3::4::5::6::nil)%nat pre.
  unfold AOSCSpacePrioTbl.
  hoare_split_pure_all.
  eapply seq_rule.
  
  eapply assign_rule_lvar.
  {
    intros. split. intros.
    sep_lifts_trms_in H29 (Alvarmapsto pCSpace).

    exact H29.
    intros.
    sep cancel H27.
    sep auto.
  }
  {
    intros.
    eapply array_member_rv_g.
    unfold GAarray.
    sep normal. sep eexists.
    sep cancel OSCSpacePrioTbl. 
    sep cancel Aarray. sep cancel A_dom_lenv.
    exact H29.
    simpl. auto.
    eauto.
    sep get rv.
    rewrite Htrue. auto.
    eauto. auto. lia. lia.
    rewrite Hlenv'40. auto.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hlenv'40. lia.
  }
  eapply eq_vptr. eauto.
  intros.
  eexists.
  sep cancel p_local. simpl. auto.
  eapply backward_rule1 with(p:=<||
  grant_cspace_cap_spec
    (Vint32 i
     :: Vint32 i0
        :: Vint32 i1
           ::v') ||>  **
  AOSCSpacePrioTbl (b, i9) v'40 v'41
    v'42 **
  LV pCSpace @ CSPACE ∗ |-> nth_val' (Z.to_nat (Int.unsigned i6)) v'40 **
  GV OSPrioCur @ char_t |-> Vint32 i6 **
  A_dom_lenv
    ((cap_Right, long)
     :: (cap_Class, long)
        :: (destTask_Prio, char_t)
           :: (ios_cap_defs.i, char_t)
              :: (pCSpace, CSPACE ∗) :: nil) **
  p_local OSLInv (v'28, Int.zero)
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull
           :: logic_val Vnull
              :: logic_val Vnull :: nil) ** H27).
  intros. unfold AOSCSpacePrioTbl.
  sep cancel H27. sep auto.
  subst H27.
  assert(HpCSpacetype: rule_type_val_match CSPACE ∗
  (nth_val' (Z.to_nat (Int.unsigned i6)) v'40) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hlenv'40. lia.
  clear H28.
  hoare forward.
  unfold val_inj, val_eq.
  clear -HpCSpacetype.
  unfold rule_type_val_match in HpCSpacetype.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i6))
  v'40); tryfalse; auto;destruct a; auto.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop).
  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  
  unfold OldOSInvWL.
  unfold CapabilityInv.
  unfold AOSCSpaceCapParent.
  unfold AGVars.
  try unfold AOSTCBList;unfold_dll.
  sep normal. sep eexists.
  sep cancel AOSCSpacePrioTbl. sep cancel AOSCSpaceObjectPointer.
  sep cancel CSpaceGVars. 
  sep cancel AOSMapTbl.
  sep cancel AOSUnMapTbl. sep cancel AOSTCBPrioTbl.
  sep cancel AOSRdyTblGrp. sep cancel AOSTime.
  sep cancel APthreadAttr. sep cancel EvtInv.
  sep cancel IntInv. sep cancel TmrInv.
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.
  sep cancel AOSTCBFreeList. sep cancel A_isr_is_prop.
  (* sep cancel AGVars.  *)
  unfold AOSCSpaceCapParent in H28.
  sep normal in H28.  sep cancel CapParent.
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. 
  instantiate(1:=LV pCSpace @ CSPACE ∗ |-> nth_val' (Z.to_nat (Int.unsigned i6)) v'40 **
  A_dom_lenv
  ((cap_Right, long)
   :: (cap_Class, long)
      :: (destTask_Prio, char_t)
         :: (ios_cap_defs.i, char_t)
            :: (pCSpace, CSPACE ∗) :: nil) **
            LV ios_cap_defs.i @ char_t |-> v'0 **
            LV cap_Right @ long |-> Vint32 i1 **
            LV cap_Class @ long |-> Vint32 i0 **
            LV destTask_Prio @ char_t |-> Vint32 i).
  sep auto; eauto.
  splits; auto. go.
  clear -Hpriolt64.
  lia.
  Optimize Proof.
  Optimize Heap.
  go.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply grant_cspace_cap_absimp_curpspace_null.
  can_change_aop_solver.
  hoare forward. 
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hnotnull: (nth_val' (Z.to_nat (Int.unsigned i6)) v'40) <> Vnull).
  clear -HpCSpacetype  H27.
  unfold rule_type_val_match in HpCSpacetype.
  unfold val_inj, val_eq in H27.
  destruct (nth_val' (Z.to_nat (Int.unsigned i6)) v'40); destruct H27; tryfalse.
  destruct a; auto. destruct a. auto.
  clear H27.

  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H27 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned i6)) in H27; eauto.
  unfold AOSCSpacePrioTbl in H27. sep split in H27.
  rewrite Hlenv'41. lia.

  hoare_split_pure_all.
  unfold ACSpace.
  destruct v'45, p, p, p, v'49.
  unfold Acnode. 
  destruct c, p. 
  hoare_split_pure_all.
  simpljoin.
  rename H36 into Hi10range.
  rename H37 into H36.
  rename H38 into H37.
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H27 (ASlots).
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(SLOT_CNODE_CAP)) in H27; eauto. 
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  hoare_split_pure_all.
  simpljoin.
  unfold ACap. destruct v'49, c, p. 
  unfold AOSCSpaceCapParent.
  hoare_split_pure_all.

  (*IF (OSRunning ′ ==ₑ CFalse
  ||ₑ ((((((((OSCSpacePrioTbl ′ [OSPrioCur ′]) → cnode) .. slots) [′ SLOT_CNODE_CAP])
          .. capability) .. cap_content) .. category) .. category_right &ₑ
        ′ CNODE_GRANT_CAP) !=ₑ ′ 0 &&ₑ CapParent ′ [destTask_Prio ′] ==ₑ OSPrioCur ′)*)
  
  destruct H40.
  destruct H41.
  assert(Hx: (Z.to_nat(Int.unsigned i6) < 64)%nat).
  clear -Hpriolt64. lia. 
  assert(Hix: (Z.to_nat(Int.unsigned i) < 64)%nat).
  clear -Hilt64. lia. 
  assert (nth_val' (Z.to_nat (Int.unsigned i6))
  (v'47 ++ Vptr (b0, i12) :: v'48) = Vptr (b0, i12)).
  eapply nth_val'_length_imp. eauto.
  rename H43 into Hcurspace.
  rewrite Hcurspace.

  eapply forward_rule1 with(q:=Afalse \\//Afalse).
  intros. 
  destruct H43; auto.
  eapply if_rule2.
  intros.
  eapply bop_rv.
  eapply bop_rv.
  sep get rv.
  sep get rv.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  destruct(Int.eq ($ 1) Int.zero); auto.
  simpl. eauto.
  eapply bop_rv.
  eapply uop_rv.
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
                sep cancel pCSpace. exact H43.
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
    sep normal in H43.
    sep lift 5%nat in H43.
    unfold Aptrmapsto in H43 at 1.
    exact H43.
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
  destruct(Int.eq (i17&ᵢ$ CNODE_GRANT_CAP) ($ 0)); auto.
  simpl. eauto.
  eauto. unfold val_inj, bop_eval, uop_eval, and, val_eq.
  destruct (Int.eq (i17&ᵢ$ CNODE_GRANT_CAP)
  ($ 0)); eauto.
  simpl. eauto.
  sep get rv.
  rewrite Hitrue. auto.

  lets Hy: nthval'_has_value_Tint32 H40 H41 Hix.
  destruct Hy. destruct H44. rewrite H44. auto.
  rewrite Htrue. auto.
  lets Hy: nthval'_has_value_Tint32 H40 H41 Hix.
  destruct Hy. destruct H44. rewrite H44. 
  unfold val_inj, val_eq.
  destruct (Int.eq x i6); eauto.
  eauto.
  lets Hy: nthval'_has_value_Tint32 H40 H41 Hix.
  destruct Hy. destruct H44. rewrite H44.
  unfold val_inj, bop_eval, val_eq, and.
  
  destruct (Int.eq
  (i17&ᵢ$ CNODE_GRANT_CAP)
  ($ 0)); 
  destruct (Int.eq x i6); unfold Int.notbool;repeat (val_help; simpl); auto.
  simpl. eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq, and, uop_eval, notint, bool_and.
  unfold Int.zero.
  assert(Int.eq ($1) ($0) = false).
  eapply eq_one_zero.
  rewrite H44.
  clear H44.
  unfold bool_or.
  lets Hy: nthval'_has_value_Tint32 H40 H41 Hix.
  destruct Hy. destruct H44. rewrite H44. 
  destruct (Int.eq
  (i17&ᵢ$ CNODE_GRANT_CAP)
  ($ 0)); 
  destruct (Int.eq x i6); unfold Int.notbool;repeat (val_help; simpl); auto.
  simpl. eauto.

  hoare_split_pure_all.

  eapply backward_rule1.
  intros.



  sep lifts (3::4::5::6::nil)%nat in H44.
  eapply fold_Cap in H44; [idtac | eauto..].
  sep lifts (2::3::1::4::nil)%nat in H44.
  eapply ASlots_fold_any_idx_frm in H44; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H44.
  eapply fold_Acnode in H44; [idtac | eauto..]. 
  sep lifts (1::6::7::8::9::nil)%nat in H44.
  eapply fold_ACSpace  in H44; [idtac | eauto..]. 
  sep lifts (5::1::6::nil)%nat in H44. 
  eapply ACSpaceAarray_fold_any_idx_frm in H44;  [idtac | eauto; try lia..]. 
  sep lifts (2::1::3::4::nil)%nat in H44.
  eapply fold_AOSCSpacePrioTbl1 in H44; eauto; try lia.
  
  rewrite nth_val_imp_nth_val'_2.
  rewrite Hcurspace. eauto.
  rewrite Hlenv'40.
  eauto.
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.

  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H44 (aemp_isr_is).
  
  eapply aemp_isr_elim in H44.

  sep_lifts_trms_in H44 (Aisr, Ais, A_isr_is_prop).
  eapply elim_a_isr_is_prop in H44. 
  exact H44.

  assert (Hcases: 
  not (nth_val' (Z.to_nat (Int.unsigned i))
  (v'47 ++ Vptr (b0, i12) :: v'48) <> Vnull)\/
  (nth_val' (Z.to_nat (Int.unsigned i))
  (v'47 ++ Vptr (b0, i12) :: v'48) <> Vnull)) by tauto.
  destruct Hcases as [Hfail|Hsucc1].


  eapply seq_rule.

  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_Grant_Cap_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_Grant_CapPre.
  unfold ucos_Grant_CapPre'.
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel 41%nat 1%nat.
  exact H44.
  eauto.
  eauto.
  eauto.
  simpl.  eauto.
  simpl.  eauto.
  simpl.  eauto.
  unfold AOSCSpaceObjectPointer, CSpaceGVars, A_isr_is_prop.
  go.
  unfold retpost.
  unfold getasrt. unfold ucos_Grant_CapPost.
  unfold ucos_Grant_CapPost'.
  intros. sep destruct H44.

  sep lifts (15::nil)%nat in H44.
  eapply disj_split in H44.
  destruct H44;  sep split in H44. 
  rewrite H46. eauto.
  rewrite H46. eauto.
  simpl. rewrite Hitrue.
  eauto.
  unfold getasrt. unfold ucos_Grant_CapPost.
  unfold ucos_Grant_CapPost'.
  intros. sep destruct H44.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. unfold ucos_Grant_CapPre.
  unfold ucos_Grant_CapPre'.
  intros. sep destruct H44. eexists.
  sep cancel p_local. simpl. auto.

  (*进行spec前提的一些准备工作*)
  unfold getasrt, ucos_Grant_CapPost, ucos_Grant_CapPost'.
  hoare_split_pure_all.
  inverts H49.
  simpl in H44, H45, H46.
  apply sym_eq in H46.
  apply sym_eq in H45.
  apply sym_eq in H44.
  inverts H44. inverts H45. inverts H46.

  eapply backward_rule1.
  intros.
  sep lift 9%nat in H44.
  eapply disj_split in H44.
  exact H44.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H45.
  hoare forward.
  hoare_split_pure_all.
  unfold CNODE_GRANT_FAILURE, CNODE_NONE_FAULT in H45.
  unfold val_inj in H45.
  assert(Int.eq ($11) ($0) = false).
  clear - H45.
  int auto.
  Optimize Proof.
  Optimize Heap.
  rewrite H49 in H45.
  destruct H45.
  tryfalse.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  
  sep lifts (4::2::5::nil)%nat in H49.
  eapply add_aemp_isr_is_prop in H49. 
  eapply add_isr_is_prop in H49. 

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
  (* sep cancel Hcapspace. *)
  sep cancel CoreCommuInv. sep cancel PartitionInv.
  sep cancel Acs. sep cancel Aier. sep cancel Ais.
  sep cancel Aisr. sep cancel Aie. sep cancel p_local.

  
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. sep cancel AOSTCBFreeList.
  sep cancel OSTCBList. sep cancel OSTCBCur.
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV cap_Right @ long
  |-> Vint32 i1 **
  LV cap_Class @ long
  |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_GRANT_FAILURE) ** 
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i12) **
  A_dom_lenv
           ((cap_Right, long)
            :: (cap_Class, long)
               :: (destTask_Prio, char_t)
                   :: (ios_cap_defs.i, char_t)
                     :: (pCSpace, CSPACE ∗) 
                       :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  clear -Hpriolt64. lia.
  go.
  go.
  hoare abscsq.
  auto.

  eapply grant_cspace_cap_absimp_succ_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H45.  sep split in H43. 
  clear - H45.
  unfold CNODE_GRANT_FAILURE, CNODE_NONE_FAULT in H45.
  unfold val_inj in H45.
  assert(Int.eq ($11) ($0) = false).
  int auto.
  destruct (Int.eq
  ($ 11) ($ 0)).
  tryfalse.
  destruct H45.
  tryfalse.

  sep split in H43.
  exact H43.

  hoare_split_pure_all.
  destruct H44. destruct H50.
  tauto.
  rename Hsucc1 into Hinotnull.

  assert(Hcasesfuncap:
  (not (CAP_NULL_CLASS <= Int.unsigned i0 <= CAP_CHANNEL_CLASS) \/
  (CAP_NULL_CLASS <= Int.unsigned i0 <= CAP_CHANNEL_CLASS))) by tauto.
  destruct Hcasesfuncap as [Hfail|Hsucc1].

  eapply seq_rule.

  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_Grant_Cap_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_Grant_CapPre.
  unfold ucos_Grant_CapPre'.
  
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel 41%nat 1%nat.
  exact H44.
  eauto.
  eauto.
  eauto.
  simpl.  eauto.
  simpl.  eauto.
  simpl.  eauto.
  
  unfold AOSCSpaceObjectPointer, CSpaceGVars, A_isr_is_prop.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold getasrt. unfold ucos_Grant_CapPost.
  unfold ucos_Grant_CapPost'.
  intros. sep destruct H44.

  sep lifts (15::nil)%nat in H44.
  eapply disj_split in H44.
  destruct H44;  sep split in H44. 
  rewrite H46. eauto.
  rewrite H46. eauto.
  simpl. rewrite Hitrue.
  eauto.
  unfold getasrt. unfold ucos_Grant_CapPost.
  unfold ucos_Grant_CapPost'.
  intros. sep destruct H44.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. unfold ucos_Grant_CapPre.
  unfold ucos_Grant_CapPre'.
  intros. sep destruct H44. eexists.
  sep cancel p_local. simpl. auto.


  (*进行spec前提的一些准备工作*)
  unfold getasrt, ucos_Grant_CapPost, ucos_Grant_CapPost'.
  hoare_split_pure_all.
  inverts H49.
  simpl in H44, H45, H46.
  apply sym_eq in H46.
  apply sym_eq in H45.
  apply sym_eq in H44.
  inverts H44. inverts H45. inverts H46.

  eapply backward_rule1.
  intros.
  sep lift 9%nat in H44.
  eapply disj_split in H44.
  exact H44.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H45.
  hoare forward.
  hoare_split_pure_all.
  unfold CNODE_GRANT_FAILURE, CNODE_NONE_FAULT in H45.
  unfold val_inj in H45.
  assert(Int.eq ($11) ($0) = false).
  clear - H45.
  int auto.
  rewrite H49 in H45.
  destruct H45.
  tryfalse.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  
  sep lifts (4::2::5::nil)%nat in H49.
  eapply add_aemp_isr_is_prop in H49. 
  eapply add_isr_is_prop in H49. 

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
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV cap_Right @ long
  |-> Vint32 i1 **
  LV cap_Class @ long
  |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_GRANT_FAILURE) ** 
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i12) **
  A_dom_lenv
           ((cap_Right, long)
            :: (cap_Class, long)
               :: (destTask_Prio, char_t)
                   :: (ios_cap_defs.i, char_t)
                     :: (pCSpace, CSPACE ∗) 
                       :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  clear -Hpriolt64. lia.
  go.
  go.

  hoare abscsq.
  auto.
  Optimize Proof.
  Optimize Heap.

  eapply grant_cspace_cap_absimp_succ_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H45.  sep split in H43. 
  clear - H45.
  unfold CNODE_GRANT_FAILURE, CNODE_NONE_FAULT in H45.
  unfold val_inj in H45.
  assert(Int.eq ($11) ($0) = false).
  int auto.
  destruct (Int.eq
  ($ 11) ($ 0)).
  tryfalse.
  destruct H45.
  tryfalse.

  sep split in H43.
  exact H43.

  hoare_split_pure_all.
  destruct H44.
  tryfalse.

  destruct Hsucc1.
  rename H45 into Hi0le16. unfold CAP_CHANNEL_CLASS in Hi0le16.

  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H45 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned i)) in H45.
  exact H45.

  unfold AOSCSpacePrioTbl in H45.
  sep split in H45.
  destruct H46.
  destruct H54.
  rewrite H54. lia.

  eauto.

  hoare_split_pure_all.
  simpljoin.
  unfold ACSpace.
  destruct v'50, p, p, p, v'54.
  unfold Acnode. 
  destruct c, p. 

  hoare_split_pure_all.
  simpljoin.
  rename H58 into Hi18range.
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H58 (ASlots).

  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned i0)) in H58; eauto. 
  unfold SLOT_NUM. clear -Hi0le16. lia.
  hoare_split_pure_all.
  simpljoin.

  unfold ACap. destruct v'56, c, p. 
  hoare_split_pure_all.

  eapply backward_rule1.
  intros.

  sep lifts (3::4::5::6::nil)%nat in H62.
  eapply fold_Cap in H62; [idtac | eauto..].
  sep lifts (2::3::1::4::nil)%nat in H62.
  eapply ASlots_fold_any_idx_frm in H62; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H62.
  eapply fold_Acnode in H62; [idtac | eauto..]. 
  sep lifts (1::6::7::8::9::nil)%nat in H62.
  eapply fold_ACSpace  in H62; [idtac | eauto..]. 
  sep lifts (5::1::6::nil)%nat in H62. 
  eapply ACSpaceAarray_fold_any_idx_frm in H62;  [idtac | eauto; try lia..]. 
  sep lifts (2::1::3::4::nil)%nat in H62.
  eapply fold_AOSCSpacePrioTbl1 in H62; eauto; try lia.
  
  rewrite nth_val_imp_nth_val'_2.
  rewrite H45.
  assert(
  (nth_val' (Z.to_nat (Int.unsigned i))
     (v'52 ++ Vptr (b1, i20) :: v'53)) =
  (Vptr (b1, i20))).
  eapply nth_val'_length_imp. eauto.
  rewrite H63. eauto.
  rewrite Hlenv'40.
  eauto.
  unfold SLOT_NUM. lia.

  eapply seq_rule.

  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_Grant_Cap_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_Grant_CapPre.
  unfold ucos_Grant_CapPre'.
  
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel 41%nat 1%nat.
  exact H62.
  eauto.
  eauto.
  eauto.
  simpl.  eauto.
  simpl.  eauto.
  simpl.  eauto.
  
  unfold AOSCSpaceObjectPointer, CSpaceGVars, A_isr_is_prop.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold getasrt. unfold ucos_Grant_CapPost.
  unfold ucos_Grant_CapPost'.
  intros. sep destruct H62.

  sep lifts (15::nil)%nat in H62.
  eapply disj_split in H62.
  destruct H62;  sep split in H62. 
  rewrite H64. eauto.
  rewrite H64. eauto.
  simpl. rewrite Hitrue.
  eauto.

  unfold getasrt. unfold ucos_Grant_CapPost.
  unfold ucos_Grant_CapPost'.
  intros. sep destruct H62.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. unfold ucos_Grant_CapPre.
  unfold ucos_Grant_CapPre'.
  intros. sep destruct H62. eexists.
  sep cancel p_local. simpl. auto.

  (*进行spec前提的一些准备工作*)
  unfold getasrt, ucos_Grant_CapPost, ucos_Grant_CapPost'.
  hoare_split_pure_all.
  inverts H67.
  simpl in H62, H63, H64.
  apply sym_eq in H62.
  apply sym_eq in H63.
  apply sym_eq in H64.
  inverts H62. inverts H63. inverts H64.

  eapply backward_rule1.
  intros.
  sep lift 9%nat in H62.
  eapply disj_split in H62.
  exact H62.
  apply disj_rule.
  hoare_split_pure_all.

  destruct H62.
  destruct H62.
  tryfalse.
  unfold CAP_CHANNEL_CLASS in H62.
  tryfalse.
  destruct H62.
  tryfalse.
  tryfalse.

  hoare_split_pure_all.
  inverts H63.
  hoare forward.
  hoare_split_pure_all.
  (*为证明当前任务作准备*)
  unfolds in H0. 
  destruct H0.
  do 3 destruct e.
  assert(x = i6).
  {
    clear -e H7 H9.
    unfolds in H9. simpljoin.
    unfolds in H2. 
    destruct x8, p, p. 
    simpljoin.
    unfolds in H4. simpl in H4.
    inverts H4.
    inverts H. 
    clear -e H7 H1.
    Search(TcbJoin _).
    assert(get v'12 (v'28, Int.zero) =
    Some (p, t, m, s)).
    eapply join_joinsig_get; eauto.
    rewrite H in e.
    inverts e. auto.
  }
  subst x.
(*为证明当前任务的权能空间作准备*)
  lets bak_24: H24.
  unfolds in H24.
  destruct H24.
  assert(Ha: 0 <= Int.unsigned i < 64).
  clear -Hilt64.
  int auto.
  Optimize Proof.
  Optimize Heap.
  assert(Hb: nth_cspace_val ∘ (Int.unsigned i)
  (v'39 ++
        (i13, i14,
        v'40 ++
        (v'45, (i15, (i16, i17, v0))) :: v'41,
        i11, l, v, i10) :: v'46) = Some ((i21, i22,
        v'50 ++
        (v'55, (i23, (i24, i25, v2))) :: v'54, i19,
        l0, v1, i18))).
    rewrite nth_cspace_eq_nth_cspace_val; eauto.
    rewrite H46.
    rewrite nth_cspace_length_imp; eauto.

  lets Hc: H0 Hb.
  destruct Hc. destruct H68. destruct H68.
  clear Ha Hb.
(*为证明目标任务的权能空间作准备*)
   assert(Ha: 0 <= Int.unsigned i6 < 64).
   clear -Hpriolt64.
   int auto.
   assert(Hb: nth_cspace_val ∘ (Int.unsigned i6)
   (v'39 ++
         (i13, i14,
         v'40 ++
         (v'45, (i15, (i16, i17, v0))) :: v'41,
         i11, l, v, i10) :: v'46) = Some ((i13, i14,
         v'40 ++
         (v'45, (i15, (i16, i17, v0))) :: v'41,
         i11, l, v, i10))).
     rewrite nth_cspace_eq_nth_cspace_val; eauto.
     rewrite nth_cspace_length_imp; eauto.
 
   lets Hc: H0 Hb.
   destruct Hc. destruct H70. destruct H70.
   clear Ha Hb.

   lets bak_11: H11.
   unfolds in H11.
   destruct H11.

  assert  (Hix064: 0 <= Int.unsigned i < 64).
  clear -Hilt64.
  int auto.
  lets Hy: H72 H68.
  rewrite nth_val_imp_nth_val'_2 in Hy.
  unfold nat_of_Z in Hy.
  inverts Hy. 
  rewrite H74 in H43.
  clear H74. 
 
  rewrite H46 in H64. 
  rewrite get_capability_nth_mth_cspace_length_imp in H64; eauto.
  inverts H64.

  hoare_lifts_trms_pre (Aop, abstcblsid, curtid, cspaceid).
  hoare abscsq. 

  go. 
  eapply grant_cspace_cap_absimp_succ.
  rewrite e.
  eauto.
  eauto.
  eauto.
  unfold AOSCSpaceObjectPointer, CSpaceGVars, AOSCSpacePrioTbl.
  go.
  eapply can_change_aop_ACSpaceAarrayTptr.

  eauto.
  unfold OS_LOWEST_PRIO.
  clear -Hiltlowestprio.
  int auto.
  eauto.

  {
  unfold val_inj, bop_eval, val_eq in H43.
  assert(Int.eq ($1) (Int.zero) = false).
  clear -H43.
  int auto.
  rewrite H64 in H43.
  unfold bool_or, bool_and, uop_eval, notint, Int.notbool, Int.one in H43.
  destruct (Int.eq(i17&ᵢ$ CNODE_GRANT_CAP)
  ($ 0)) eqn: Ha; destruct (Int.eq x3
  i6) eqn: Hb; repeat val_help H43; eauto.
  simpl in H43.
  rewrite Ha in H43.
  rewrite H64 in H43.

  try change (Int.ltu Int.zero Int.zero) with (false) in H43.
  simpl in H43. 
  try change (Int.ltu Int.zero Int.zero) with (false) in H43.
  simpl in H43.
  tryfalse.

  simpl in H43.
  rewrite Ha in H43.
  rewrite H64 in H43.

  try change (Int.ltu Int.zero Int.zero) with (false) in H43.
  simpl in H43. 
  try change (Int.ltu Int.zero Int.zero) with (false) in H43.
  simpl in H43.
  tryfalse.
  }

  {
  unfold val_inj, bop_eval, val_eq in H43.
  assert(Int.eq ($1) (Int.zero) = false).
  clear -H43.
  int auto.
  rewrite H64 in H43.
  unfold bool_or, bool_and, uop_eval, notint, Int.notbool, Int.one in H43.
  destruct (Int.eq(i17&ᵢ$ CNODE_GRANT_CAP)
  ($ 0)) eqn: Ha; destruct (Int.eq x3
  i6) eqn: Hb; repeat val_help H43; eauto.
  rewrite Int.eq_sym.
  eauto.
  simpl in H43.
  rewrite Ha in H43.
  rewrite H64 in H43.

  try change (Int.ltu Int.zero Int.zero) with (false) in H43.
  simpl in H43. 
  try change (Int.ltu Int.zero Int.zero) with (false) in H43.
  simpl in H43.
  tryfalse.
  rewrite Int.eq_sym.
  eauto.

  simpl in H43.
  rewrite Ha in H43.
  try change (Int.eq Int.zero Int.zero) with (true) in H43.
  simpl in H43. 
  try change (Int.ltu Int.zero Int.zero) with (false) in H43.
  simpl in H43.
  try change (Int.ltu Int.zero ($ 1)) with (true) in H43.
  simpl in H43.
  try change (Int.ltu Int.zero Int.zero) with (false) in H43.
  simpl in H43.
  tryfalse.
  }
 
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  
  sep lifts (7::5::8::nil)%nat in H64.
  eapply add_aemp_isr_is_prop in H64. 
  eapply add_isr_is_prop in H64. 

  unfold OldOSInvWL.
  sep normal. sep eexists.
  try unfold AOSTCBList;unfold_dll.
  unfold CapabilityInv.
  unfold AOSCSpaceCapParent.
  unfold RH_CurTCB.
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
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV cap_Right @ long
  |-> Vint32 i1 **
  LV cap_Class @ long
  |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> (V$ CSPACE_NONE_FAULT) ** 
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i12) **
  A_dom_lenv
           ((cap_Right, long)
            :: (cap_Class, long)
               :: (destTask_Prio, char_t)
                   :: (ios_cap_defs.i, char_t)
                     :: (pCSpace, CSPACE ∗) 
                       :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  eapply Capability_wellform_descendents_update_cap.
  eauto.
  eapply taskPrioProp_update_slots_cap_remain.
  eauto.
  rewrite H46.
  eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
  rewrite <-H46.
  eauto.

  rewrite nth_cspace_length_imp; eauto.

  eapply RL_Cap_Parent_Child_remain; auto.

  eapply RLH_CapParent_update_slots_cap_remain with (cspacevl:=
  v'39 ++
  (i13, i14,
  v'40 ++
  (v'45, (i15, (i16, i17, v0))) :: v'41,
  i11, l, v, i10) :: v'46 ); eauto.
  rewrite H46.
  rewrite nth_cspace_length_imp; eauto.
  clear -Hpriolt64.
  lia.
  Optimize Proof.
  Optimize Heap.
  go.
  go.
  hoare forward.
  (* unfold nat_of_Z. *)
  rewrite H41.
  eauto.

  hoare_split_pure_all.


  unfold CNODE_NONE_FAULT in H63.
  destruct H63. 
  unfold val_inj in H63.
  assert(Int.eq ($0) ($0) = true).
  clear - H63.
  int auto.
  rewrite H68 in H63.
  tryfalse.
  unfold val_inj in H63.
  assert(Int.eq ($0) ($0) = true).
  clear - H63.
  int auto.
  rewrite H68 in H63.
  tryfalse.

  destruct H63.
  sep split in H62.
  exact H62.
  sep split in H62.
  unfold CNODE_NONE_FAULT in H63.
  destruct H63. 
  unfold val_inj in H63.
  assert(Int.eq ($0) ($0) = true).
  clear - H63.
  int auto.
  rewrite H67 in H63.
  tryfalse.
  unfold val_inj in H63.
  assert(Int.eq ($0) ($0) = true).
  clear - H63.
  int auto.
  rewrite H67 in H63.
  tryfalse.
  hoare_split_pure_all.

  eapply backward_rule1.
  intros.

  sep lifts (3::4::5::6::nil)%nat in H44.
  eapply fold_Cap in H44; [idtac | eauto..].
  sep lifts (2::3::1::4::nil)%nat in H44.
  eapply ASlots_fold_any_idx_frm in H44; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H44.
  eapply fold_Acnode in H44; [idtac | eauto..]. 
  sep lifts (1::6::7::8::9::nil)%nat in H44.
  eapply fold_ACSpace  in H44; [idtac | eauto..]. 
  sep lifts (5::1::6::nil)%nat in H44. 
  eapply ACSpaceAarray_fold_any_idx_frm in H44;  [idtac | eauto; try lia..]. 
  sep lifts (2::1::3::4::nil)%nat in H44.
  eapply fold_AOSCSpacePrioTbl1 in H44; eauto; try lia.
  
  rewrite nth_val_imp_nth_val'_2.
  rewrite Hcurspace. eauto.
  rewrite Hlenv'40.
  eauto.
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.

 
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 

  unfold OldOSInvWL.
  sep normal. sep eexists.
  try unfold AOSTCBList;unfold_dll.
  unfold CapabilityInv.
  unfold AOSCSpaceCapParent.
  unfold AGVars.
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
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV cap_Right @ long
  |-> Vint32 i1 **
  LV cap_Class @ long
  |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> v'0 ** 
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i12) **
  A_dom_lenv
           ((cap_Right, long)
            :: (cap_Class, long)
               :: (destTask_Prio, char_t)
                   :: (ios_cap_defs.i, char_t)
                     :: (pCSpace, CSPACE ∗) 
                       :: nil)).
  sep auto; eauto.

  split. eauto.
  go.
  clear -Hpriolt64. lia.
  go.
  go.

  hoare abscsq. 
  go. 
  eapply grant_cspace_cap_absimp_capabilitynone.
  can_change_aop_solver.
  hoare forward.
  Unshelve. all:exact (Aemp).
Qed.