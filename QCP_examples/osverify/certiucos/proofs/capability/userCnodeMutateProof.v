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
Require Import abs_op_capability. 
Require Import CapRelLemmas.
Import DeprecatedTactic.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.
Set Keyed Unification.



(* ucos mutate *)

Lemma absimp_userCnodeMutate_prio_invalid:
  forall dest src i1 i2 v' sch P,
    can_change_aop P -> 
    (((Int.ltu dest (Int.repr OS_LOWEST_PRIO) = false) )
      \/ ((Int.ltu src (Int.repr OS_LOWEST_PRIO) = false))) ->
    absinfer sch ( <|| user_cnode_mutate_spec (Vint32 dest :: Vint32 src :: Vint32 i1 :: Vint32 i2 :: v') ||> ** P)
             ( <|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P ).
  Proof.
  infer_solver 0%nat.
Qed.  

Lemma absimp_user_cnode_mutate_curpspace_null:
  forall dest src funcap rights v' sch P,
  can_change_aop P -> 
  absinfer sch ( <|| user_cnode_mutate_spec (Vint32 dest :: Vint32 src :: Vint32 funcap :: Vint32 rights :: v') ||> **P)
              ( <|| END (Some (Vint32 (Int.repr CNODE_MUTATE_FAILURE))) ||>  **P).

Proof.
  infer_solver 1%nat.
Qed. 



Lemma absimp_user_cnode_mutate_none:
  forall dest src funcap rights v' sch P,
  can_change_aop P -> 
  absinfer sch ( <|| user_cnode_mutate_spec (Vint32 dest :: Vint32 src :: Vint32 funcap :: Vint32 rights :: v') ||> **P)
              ( <|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||>  **P).

Proof.
  infer_solver 2%nat.
Qed. 

Lemma absimp_user_cnode_mutate_succ_fail:
  forall dest src funcap rights v' sch P,
  can_change_aop P -> 
  absinfer sch ( <|| user_cnode_mutate_spec (Vint32 dest :: Vint32 src :: Vint32 funcap :: Vint32 rights :: v') ||> **P)
              ( <|| END (Some (Vint32 (Int.repr CNODE_MUTATE_FAILURE))) ||>  **P).

Proof.
  infer_solver 4%nat.
Qed. 

Lemma absimp_user_cnode_mutate_succ_succ:
  forall dest src funcap rights v' sch P dest_parent dest_slot_type dest_cap_content dest_cap_right dest_object_t cs cs' cs'' cs''' dest_cap_type
        dest_slots dest_childs src_slots src_childs src_parent src_cap_content src_cap_right  src_object_t src_slot_type,
    can_change_aop P -> 
    get cs dest =   Some (dest_slots, dest_childs, dest_parent) ->
    get cs src =   Some (src_slots, src_childs, src_parent) ->
    nth_slots (Z.to_nat (Int.unsigned funcap)) dest_slots =
               Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) ->
    nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots =
               Some (src_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, src_cap_right, src_object_t))) ->
    cs' = set cs dest
        (update_nth_slots (Z.to_nat (Int.unsigned funcap)) dest_slots
        (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, rights, dest_object_t))), dest_childs, dest_parent) ->
   cs'' = CSpaceMod.set cs' src
  (update_nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots
        (src_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, (Int.and src_cap_right (Int.not rights)), src_object_t))), src_childs, src_parent) ->
     cs''' = CSpaceMod.set cs'' src
        (update_nth_slots (Z.to_nat (Int.unsigned funcap)) ((update_nth_slots (Z.to_nat (Int.unsigned funcap)) src_slots
        (src_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, (Int.and src_cap_right (Int.not rights)), src_object_t)))))
             ($SLOT_NULL_CAP, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, (Int.and src_cap_right (Int.not rights)), src_object_t))), src_childs, src_parent) ->
   absinfer sch ( <|| user_cnode_mutate_spec (Vint32 dest :: Vint32 src :: Vint32 funcap :: Vint32 rights :: v') ||> **
                      Hcapspace cs **P)
                ( <|| END (Some (Vint32 (Int.repr CNODE_MUTATE_SUCCESS))) ||>  **  
                      Hcapspace cs''' ** P).     
Proof.
  infer_solver 3%nat.
Qed. 


Lemma UserCnodeMutateProof: 
  forall  tid vl p r, 
    Some p =
    BuildPreA' os_api user_cnode_mutate
    user_cnode_mutate_api vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api user_cnode_mutate
    user_cnode_mutate_api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api user_cnode_mutate = Some (t, d1, d2, s) /\
      {|Cap_spec, GetHPrio, OSLInv,  I, r, Afalse|}|-tid 
      {{p ** (EX srcTask_Prio destTask_Prio, [|Some(Vint32 destTask_Prio) = nth_val 3%nat vl /\
          Some(Vint32 srcTask_Prio) = nth_val 2%nat vl /\ (Int.unsigned destTask_Prio < 64)
          /\ (Int.unsigned destTask_Prio > Int.unsigned srcTask_Prio)|])}}s {{Afalse}}.
Proof.
  init_spec.
  simpl in H.
  destruct H. destruct H0. destruct H1.
  inverts H. inverts H0. 
  rename H2 into Hsrc_dest_lt.
  rename H1 into Hilt64.
  assert(Hi0lt64:Int.unsigned i0 < 64) by lia.
  lzh_hoare_if; pure_auto.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply absimp_userCnodeMutate_prio_invalid.
  can_change_aop_solver.
  clear -LHift_true.
  unfold ios_cap_defs.OS_LOWEST_PRIO, ios_cap_defs.OS_PRIO_INVALID in LHift_true.
  unfold OS_LOWEST_PRIO, OS_PRIO_INVALID. 
  unfold val_inj in LHift_true; int auto; pure_auto.
  hoare forward.

  hoare forward prim;pure_auto.
  hoare_split_pure_all.
  try unfold OSInv; try unfold AOSTCBList;unfold_dll.
  pure intro.
  assert(Hpriolt64:Int.unsigned i7 < 64).
  unfold TCBList_P in H10.
  simpljoin.
  unfold TCBNode_P in H12.
  destruct x2, p, p.
  simpljoin. 
  unfold RL_TCBblk_P in H25.
  simpljoin.
  unfold V_OSTCBPrio in H25. simpl in H25. inverts H25. lia.
  assert(Htrue: Int.unsigned i7 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -Hpriolt64. int auto.
  assert(Hitrue: Int.unsigned i <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H4. int auto.
  assert(Hi0true: Int.unsigned i0 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H3. int auto.
  
  hoare forward.
  go. 
  pure intro.

  unfold CapabilityInv.
  hoare_split_pure_all.
  rename H26 into Hwellform_descendents.
  destruct v'6. 
  hoare remember (1::nil)%nat pre.
  unfold AOSCSpacePrioTbl. hoare_split_pure_all.
  assert(Htypematch : array_type_vallist_match CSPACE ∗ v'8).
  simpljoin. auto.
  assert(Hlenv'8: length v'8 = 64%nat). simpljoin. auto.
  assert(Hlenv'30: length v'30 = 64%nat). simpljoin. auto.
  eapply backward_rule1 with (p:=AOSCSpacePrioTbl (b, i10) v'8 v'30 v'31 **
  H26).
  intros.
  unfold AOSCSpacePrioTbl. 
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep split; auto.
  subst H26.
  clear H27.
  Require Import seplog_trm_tacs.
  hoare_lifts_trms_pre (Aop, AOSCSpacePrioTbl, Alvarmapsto pCSpace, Alvarmapsto y, A_dom_lenv, p_local).
  hoare remember (1::2::3::4::5::6::nil)%nat pre.
  unfold AOSCSpacePrioTbl.
  hoare_split_pure_all.
  eapply seq_rule.
  
  eapply assign_rule_lvar.
  {
    intros. split. intros.
    sep_lifts_trms_in H28 (Alvarmapsto pCSpace).

    exact H28.
    intros.
    sep cancel H26.
    sep auto.
  }
  {
    intros.
    eapply array_member_rv_g.
    unfold GAarray.
    sep normal. sep eexists.
    sep cancel OSCSpacePrioTbl. 
    sep cancel Aarray. sep cancel A_dom_lenv.
    exact H28.
    simpl. auto.
    eauto.
    sep get rv.
    rewrite Htrue. auto.
    eauto. auto. lia. lia.
    rewrite Hlenv'8. auto.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hlenv'8. lia.
  }
  eapply eq_vptr. eauto.
  intros.
  eexists.
  sep cancel p_local. simpl. auto.
  eapply backward_rule1 with(p:=<||
  user_cnode_mutate_spec
    (Vint32 i
     :: Vint32 i0
        :: Vint32 i1
           :: Vint32 i2 :: v') ||>  **
  AOSCSpacePrioTbl (b, i10) v'8 v'30
    v'31 **
  LV pCSpace @ CSPACE ∗ |-> nth_val' (Z.to_nat (Int.unsigned i7)) v'8 **
  LV y @ char_t |-> Vint32 i7 **
  A_dom_lenv
    ((rights, long)
     :: (func_capability, long)
        :: (srcTask_Prio, char_t)
           :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                 :: (ios_cap_defs.i,
                    char_t)
                    :: (y, char_t)
                       :: nil) **
  p_local OSLInv (v'29, Int.zero)
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull
           :: logic_val Vnull
              :: logic_val Vnull
                 :: nil) ** H26).
  intros. unfold AOSCSpacePrioTbl.
  sep cancel H26. sep auto.
  subst H26.
  assert(HpCSpacetype: rule_type_val_match CSPACE ∗
  (nth_val' (Z.to_nat (Int.unsigned i7)) v'8) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hlenv'8. lia.
  clear H27.
  hoare forward.
  unfold val_inj, val_eq.
  clear -HpCSpacetype.
  unfold rule_type_val_match in HpCSpacetype.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned i7))
  v'8); tryfalse; auto;destruct a; auto.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop).
  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  
  unfold OldOSInvWL.
  unfold CapabilityInv.
  unfold AOSCSpaceCapParent.
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
  sep cancel AGVars. unfold AOSCSpaceCapParent in H27.
  sep normal in H27.  sep cancel CapParent.
  sep cancel Astruct. sep cancel dllseg.
  sep cancel dllseg. 
  instantiate(1:=LV pCSpace @ CSPACE ∗ |-> nth_val' (Z.to_nat (Int.unsigned i7)) v'8 **
  LV y @ char_t |-> Vint32 i7 **
  A_dom_lenv
    ((rights, long)
     :: (func_capability, long)
        :: (srcTask_Prio, char_t)
           :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                 :: (ios_cap_defs.i, char_t) :: (y, char_t) :: nil) **
                 LV ios_cap_defs.i @ char_t |-> v'1 **
         LV rights @ long |-> Vint32 i2 **
         LV func_capability @ long |-> Vint32 i1 **
         LV srcTask_Prio @ char_t |-> Vint32 i0 **
         LV destTask_Prio @ char_t |-> Vint32 i).
  sep auto; eauto.
  splits; auto. go.
  go.
  hoare abscsq.
  Hint Resolve noabs_oslinv.
  go.
  eapply absimp_user_cnode_mutate_curpspace_null.
  can_change_aop_solver.
  hoare forward. 

  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hnotnull: (nth_val' (Z.to_nat (Int.unsigned i7)) v'8) <> Vnull).
  clear -HpCSpacetype  H26.
  unfold rule_type_val_match in HpCSpacetype.
  unfold val_inj, val_eq in H26.
  destruct (nth_val' (Z.to_nat (Int.unsigned i7)) v'8); destruct H26; tryfalse.
  destruct a; auto. destruct a. auto.
  clear H26.
  eapply backward_rule1.
  intros.

  sep_lifts_trms_in H26 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned i7)) in H26.
  exact H26.
  rewrite Hlenv'30.
  lia.
  Optimize Proof.
  Optimize Heap.
  auto.
  hoare_split_pure_all.
  

  unfold ACSpace.
  destruct v'34, p, p, p, v'38.

  unfold Acnode. 
  destruct c, p. 
  hoare_split_pure_all.
  simpljoin.
  rename H35 into Hi11range.
  rename H36 into H35.
  rename H37 into H36.
  eapply backward_rule1.
  intros.

  sep_lifts_trms_in H26 (ASlots).
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(SLOT_CNODE_CAP)) in H26; eauto. 
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  hoare_split_pure_all.
  simpljoin.
  unfold ACap. destruct v'38, c, p. 
  unfold AOSCSpaceCapParent.
  hoare_split_pure_all.
  destruct H39.
  destruct H40.
  assert(Hx: (Z.to_nat(Int.unsigned i7) < 64)%nat).
  clear -Hpriolt64. lia. 
  assert(Hxi: (Z.to_nat(Int.unsigned i) < 64)%nat).
  clear -Hilt64. lia. 
  assert(Hxi0: (Z.to_nat(Int.unsigned i0) < 64)%nat).
  clear -Hi0lt64. lia. 
  lets Hy: nthval'_has_value_Tint32 H39 H40 Hxi.
  destruct Hy. destruct H42.
  assert (nth_val' (Z.to_nat (Int.unsigned i7))
        (v'36 ++ Vptr (b0, i13) :: v'37) = Vptr (b0, i13)).
  eapply nth_val'_length_imp. eauto.
  rewrite H44.
  eapply forward_rule1 with(q:=Afalse \\//Afalse).
  intros.
  destruct H45; auto.
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
                sep cancel pCSpace. exact H45.
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
      (* simpl. *)
      2:{
      rewrite Int.add_zero.
      rewrite Int.add_zero.
      simpl typelen in *.
      rewrite <- addition_trans.
      rewrite Int.unsigned_repr.
      rewrite Int.add_assoc.
      change ($ 4 +ᵢ  $ 4) with ($8).
      unfold SLOT_CNODE_CAP.

      sep normal in H45.
      sep lift 5%nat in H45.
      unfold Aptrmapsto in H45 at 1.
      exact H45.
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
    destruct(Int.eq (i18&ᵢ$ CNODE_MUTATE_CAP) ($ 0)); auto.
    simpl. eauto.
    sep get rv.

    rewrite Hitrue. auto. 
    rewrite H42. auto.
    rewrite Hi0true. auto.
    rewrite H42. 
    unfold val_inj, val_eq.
    destruct (Int.eq x i0); eauto.
    rewrite H42. 
    unfold val_inj, notint, val_eq.
    destruct (Int.eq x i0); eauto.
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
    rewrite H42.
    destruct (Int.eq
    (i18&ᵢ$ CNODE_MUTATE_CAP)
    ($ 0)); 
    destruct (Int.eq x i0); unfold Int.notbool;repeat (val_help; simpl); auto.
    simpl. eauto.
    hoare_split_pure_all.
    eapply backward_rule1.
    intros.
    sep lifts (3::4::5::6::nil)%nat in H46. 
    eapply fold_Cap in H46.
    sep lifts (2::3::1::4::nil)%nat in H46.
    eapply ASlots_fold_any_idx_frm in H46; [idtac | eauto..]. 
    sep lifts (6::7::1::nil)%nat in H46.
    eapply fold_Acnode in H46.
    sep lifts (1::6::7::8::9::nil)%nat in H46.
    eapply fold_ACSpace  in H46; [idtac | eauto..]. 
    sep lifts (5::1::6::nil)%nat in H46. 
    eapply ACSpaceAarray_fold_any_idx_frm in H46; [idtac | eauto; try lia..]. 
    sep lifts (2::1::3::4::nil)%nat in H46.
    eapply fold_AOSCSpacePrioTbl1 in H46.
    exact H46. 
    rewrite app_length. simpl.
    rewrite H28, H36. rewrite S_add_sub_S. lia.
    eauto. 
    rewrite app_length. simpl.
    rewrite H29, H35. rewrite S_add_sub_S. lia. lia.
    eauto.
    eauto.
    rewrite nth_val_imp_nth_val'_2. rewrite H44. eauto.
    rewrite app_length. simpl. 
    rewrite H28, H36. rewrite S_add_sub_S. lia. lia.
    eauto.
    rewrite app_length. simpl. 
    rewrite H27, H38. rewrite S_add_sub_S.
    unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
    unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
    unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
    eauto.
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
    instantiate(1:=LV destTask_Prio @ char_t
    |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 i0 **
    LV ios_cap_defs.i @ char_t |-> v'1 **
    LV rights @ long |-> Vint32 i2 **
    LV func_capability @ long |-> Vint32 i1 **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
    LV y @ char_t |-> Vint32 i7 ** 
    A_dom_lenv
      ((rights, long)
      :: (func_capability, long)
        :: (srcTask_Prio, char_t)
            :: (destTask_Prio, char_t)
              :: (pCSpace, CSPACE ∗)
                  :: (ios_cap_defs.i, char_t)
                    :: (y, char_t) :: nil)).
    sep auto; eauto.
    (* unfolds. *)
    split. eauto.
    go.
    go.
    go.
    hoare abscsq.
    auto.
  Optimize Proof.
  Optimize Heap.
    eapply absimp_user_cnode_mutate_none; eauto.
    can_change_aop_solver.
    hoare forward.
    hoare_split_pure_all.
    rewrite H42 in H45.
  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H46. 
  eapply fold_Cap in H46.
  sep lifts (2::3::1::4::nil)%nat in H46.
  eapply ASlots_fold_any_idx_frm in H46; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H46.
  eapply fold_Acnode in H46.
  sep lifts (1::6::7::8::9::nil)%nat in H46.
  eapply fold_ACSpace  in H46; [idtac | eauto..]. 
  sep lifts (5::1::6::nil)%nat in H46. 
  eapply ACSpaceAarray_fold_any_idx_frm in H46; [idtac | eauto; try lia..]. 
  sep lifts (2::1::3::4::nil)%nat in H46.
  eapply fold_AOSCSpacePrioTbl1 in H46; [idtac | eauto; try lia..].

   sep_lifts_trms_in H46 (aemp_isr_is).
  
  eapply aemp_isr_elim in H46.

  sep_lifts_trms_in H46 (Aisr, Ais, A_isr_is_prop).
  
  eapply elim_a_isr_is_prop in H46. 

  exact H46.
  rewrite nth_val_imp_nth_val'_2. rewrite H44. eauto.
  rewrite Hlenv'8. lia. 
  eauto.
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  eauto.
  assert (Hcases: 
  not ((nth_val' (Z.to_nat (Int.unsigned i))
  (v'36 ++ Vptr (b0, i13) :: v'37) <> Vnull) /\
  (nth_val' (Z.to_nat (Int.unsigned i0))
  (v'36 ++ Vptr (b0, i13) :: v'37) <> Vnull))\/
  (nth_val' (Z.to_nat (Int.unsigned i))
  (v'36 ++ Vptr (b0, i13) :: v'37) <> Vnull) /\
  (nth_val' (Z.to_nat (Int.unsigned i0))
  (v'36 ++ Vptr (b0, i13) :: v'37) <> Vnull)) by tauto.
  destruct Hcases as [Hfail|Hsucc1].
  eapply seq_rule.  
  eapply calle_rule_lvar'.

  unfold Cap_spec.
  simpl. unfold ucos_CNode_Mutate_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  rewrite Hi0true. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_CNode_MutatePre.
  unfold ucos_CNode_MutatePre'.
 

  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.

  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel 30%nat 1%nat.
  exact H46.
  5:simpl; eauto.
  5:simpl; eauto. 
  5:simpl; eauto.
  5:simpl; eauto.
  eauto.
  go.
  eauto.
  eauto.
  unfold AOSCSpaceObjectPointer, CSpaceGVars.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold ucos_CNode_MutatePost.  unfold getasrt. 
  unfold ucos_CNode_MutatePost'.
  intros. sep destruct H46.
  sep lifts (16::nil)%nat in H46.
  eapply disj_split in H46.
  destruct H46;  sep split in H46. 
  rewrite H48. eauto.
  eapply disj_split in H46.
  destruct H46;  sep split in H46. 
  rewrite H64. eauto.
  rewrite H67. eauto.

  simpl.
  rewrite Hitrue, Hi0true. auto.

  unfold getasrt, ucos_CNode_MutatePost,ucos_CNode_MutatePost'.
  intros. sep destruct H46.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. 
  unfold ucos_CNode_MutatePre.
  unfold ucos_CNode_MutatePre'.

  intros. sep destruct H46. eexists.
  sep cancel p_local. simpl. auto.

  unfold getasrt, ucos_CNode_MutatePost,ucos_CNode_MutatePost'.
  hoare_split_pure_all.
  inverts H52.
  simpl in H46, H47, H48, H49.
  apply sym_eq in H46.
  apply sym_eq in H47.
  apply sym_eq in H48.
  apply sym_eq in H49.
  inverts H46. inverts H47. inverts H48. inverts H49.
  eapply backward_rule1.
  intros.
  sep lift 9%nat in H46.

  apply disj_split in H46.
  exact H46.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H47.
  hoare forward.
  hoare_split_pure_all.
  clear - H47.
  unfold CNODE_MUTATE_FAILURE, CNODE_NONE_FAULT in H47.
  unfold val_inj in H47.
  assert(Int.eq ($8) ($0) = false).
  clear - H47.
  int auto.
  destruct (Int.eq
  ($ 8) ($ 0)).
  tryfalse.
  destruct H47.
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
  sep cancel AGVars.
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV srcTask_Prio @ char_t |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MUTATE_FAILURE) **
  LV rights @ long |-> Vint32 i2 **
  LV func_capability @ long |-> Vint32 i1 **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
  LV y @ char_t |-> Vint32 i7 ** 
  A_dom_lenv
    ((rights, long)
    :: (func_capability, long)
      :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i, char_t)
                  :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  go.
  eauto.

  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply absimp_user_cnode_mutate_succ_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H47.  sep split in H47. 
  clear - H48.
  unfold CNODE_MUTATE_FAILURE, CNODE_NONE_FAULT in H48.
  unfold val_inj in H48.
  assert(Int.eq ($8) ($0) = false).
  int auto.
  Optimize Proof.
  Optimize Heap.
  destruct (Int.eq
  ($ 8) ($ 0)).
  tryfalse.
  destruct H48.
  tryfalse.

  sep split in H47.
  exact H47.

  hoare_split_pure_all.
  rename H48 into Hnew_capability.
  destruct H46.  destruct H48.
  tryfalse.
  destruct Hsucc1. 
  assert(Hcasesfuncap:
  (not (CAP_NULL_CLASS <= Int.unsigned i1 <= CAP_CHANNEL_CLASS) \/
  (CAP_NULL_CLASS <= Int.unsigned i1 <= CAP_CHANNEL_CLASS))) by tauto.
  destruct Hcasesfuncap as [Hfail|Hsucc1].

  eapply seq_rule.  
  eapply calle_rule_lvar'.

  unfold Cap_spec.
  simpl. unfold ucos_CNode_Mutate_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  rewrite Hi0true. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_CNode_MutatePre.
  unfold ucos_CNode_MutatePre'.
 

  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.

  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel 30%nat 1%nat.
  exact H48.
  5:simpl; eauto.
  5:simpl; eauto. 
  5:simpl; eauto.
  5:simpl; eauto.
  eauto.
  go.
 
  eauto.
  eauto.
  
  unfold AOSCSpaceObjectPointer, CSpaceGVars.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold ucos_CNode_MutatePost.  unfold getasrt. 
  unfold ucos_CNode_MutatePost'.
  intros. sep destruct H48.
  sep lifts (16::nil)%nat in H48.
  eapply disj_split in H48.
  destruct H48;  sep split in H48. 
  rewrite H50. eauto.
  eapply disj_split in H48.
  destruct H48;  sep split in H48. 
  rewrite H66. eauto.
  rewrite H69. eauto.

  simpl.
  rewrite Hitrue, Hi0true. auto.

  unfold getasrt, ucos_CNode_MutatePost,ucos_CNode_MutatePost'.
  intros. sep destruct H48.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. 
  unfold ucos_CNode_MutatePre.
  unfold ucos_CNode_MutatePre'.

  intros. sep destruct H48. eexists.
  sep cancel p_local. simpl. auto.

  unfold getasrt, ucos_CNode_MutatePost,ucos_CNode_MutatePost'.
  hoare_split_pure_all.
  inverts H54.
  simpl in H48, H49, H50, H51.
  apply sym_eq in H48.
  apply sym_eq in H49.
  apply sym_eq in H50.
  apply sym_eq in H51.
  inverts H48. inverts H49. inverts H50. inverts H51.
  eapply backward_rule1.
  intros.
  sep lift 9%nat in H48.

  apply disj_split in H48.
  exact H48.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H49.
  hoare forward.
  hoare_split_pure_all.
  clear - H49.
  unfold CNODE_MUTATE_FAILURE, CNODE_NONE_FAULT in H49.
  unfold val_inj in H49.
  assert(Int.eq ($8) ($0) = false).
  clear - H49.
  int auto.
  destruct (Int.eq
  ($ 8) ($ 0)).
  tryfalse.
  destruct H49.
  tryfalse.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  
  sep lifts (4::2::5::nil)%nat in H51.
  eapply add_aemp_isr_is_prop in H51. 
  eapply add_isr_is_prop in H51. 

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
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV srcTask_Prio @ char_t |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MUTATE_FAILURE) **
  LV rights @ long |-> Vint32 i2 **
  LV func_capability @ long |-> Vint32 i1 **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
  LV y @ char_t |-> Vint32 i7 ** 
  A_dom_lenv
    ((rights, long)
    :: (func_capability, long)
      :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i, char_t)
                  :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  go.

  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply absimp_user_cnode_mutate_succ_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H49.  sep split in H49. 
  clear - H50.
  unfold CNODE_MUTATE_FAILURE, CNODE_NONE_FAULT in H50.
  unfold val_inj in H50.
  assert(Int.eq ($8) ($0) = false).
  int auto.
  Optimize Proof.
  Optimize Heap.
  destruct (Int.eq
  ($ 8) ($ 0)).
  tryfalse.
  destruct H50.
  tryfalse.

  sep split in H49.
  exact H49.

  hoare_split_pure_all.
  rename H50 into Hnew_capability.

  eapply backward_rule1.
  intros.

  apply disj_split in H50.
  exact H50.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H51.
  hoare forward.

  hoare_split_pure_all.
  
  unfold CNODE_MUTATE_FAILURE, CNODE_NONE_FAULT in H51.
  unfold val_inj in H51.
  assert(Int.eq ($8) ($0) = false).
  clear -H51.
  int auto.
  destruct (Int.eq
  ($ 8) ($ 0)).
  tryfalse.
  destruct H51.
  tryfalse.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  
  sep lifts (4::2::5::nil)%nat in H55.
  eapply add_aemp_isr_is_prop in H55. 
  eapply add_isr_is_prop in H55. 

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
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV srcTask_Prio @ char_t |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MUTATE_FAILURE) **
  LV rights @ long |-> Vint32 i2 **
  LV func_capability @ long |-> Vint32 i1 **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
  LV y @ char_t |-> Vint32 i7 ** 
  A_dom_lenv
    ((rights, long)
    :: (func_capability, long)
      :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i, char_t)
                  :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  go.
  

  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply absimp_user_cnode_mutate_succ_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H51.  sep split in H48. 
  clear - H51.
  unfold CNODE_MUTATE_FAILURE, CNODE_NONE_FAULT in H51.
  unfold val_inj in H51.
  assert(Int.eq ($8) ($0) = false).
  int auto.
  destruct (Int.eq
  ($ 8) ($ 0)).
  tryfalse.
  destruct H51.
  tryfalse.

  sep split in H48.
  exact H48.

  destruct H48.
  tryfalse.
  destruct Hsucc1.
  rename H49 into Hi1le16. unfold CAP_CHANNEL_CLASS in Hi1le16.
  clear H48.

  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H48 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with(idx1:=Z.to_nat(Int.unsigned i)) (idx2:=Z.to_nat(Int.unsigned i0)) in H48.
  exact H48.


  unfold AOSCSpacePrioTbl in H48.
  sep split in H48.
  destruct H49.
  destruct H57.
  rewrite H57. lia.
  
  clear -Hsrc_dest_lt.
  eapply Z2Nat.inj_lt; int auto.
  eauto. eauto.

  hoare_split_pure_all.
  simpljoin.
  unfold ACSpace.
  destruct v'39, p, p, p, v'46.
  unfold Acnode. 
  destruct c, p. 

  destruct v'40, p, p, p, v'47.
  unfold Acnode. 
  destruct c, p. 
  hoare_split_pure_all.
  simpljoin.
  rename H67 into Hi20range.
  rename H66 into Hi24range.
  eapply backward_rule1.
  intros.
  sep lifts(10::nil)%nat in H66.
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned i1)) in H66; eauto. 
  unfold SLOT_NUM. clear -Hi1le16. lia.
  hoare_split_pure_all.

  simpljoin.
  eapply backward_rule1.
  intros.
  sep lifts(21::nil)%nat in H66.
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned i1)) in H66; eauto. 
  unfold SLOT_NUM. clear -Hi1le16. lia.
  hoare_split_pure_all.
  simpljoin.

  unfold ACap. destruct v'51, c, p.  destruct v'47, c, p.  
  hoare_split_pure_all.

  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H74. 
  eapply fold_Cap in H74.
  sep lifts (2::3::1::4::nil)%nat in H74.
  eapply ASlots_fold_any_idx_frm in H74; [idtac | eauto..]. 
  sep lifts (23::24::1::nil)%nat in H74.
  eapply fold_Acnode in H74.
  sep lifts (1::23::24::25::26::nil)%nat in H74.
  eapply fold_ACSpace  in H74; [idtac | eauto..]. 
  sep lifts (4::5::6::7::nil)%nat in H74. 
  eapply fold_Cap in H74.
  sep lifts (3::4::1::5::nil)%nat in H74.
  clear H70.
  eapply ASlots_fold_any_idx_frm with (slotsvl:=(v'39 ++
  (v'46, (i32, (i33, i34, v4))) :: v'40)) in H74; [idtac | eauto..]. 
  sep lifts (10::11::1::nil)%nat in H74.
  eapply fold_Acnode in H74.
  sep lifts (1::10::11::12::13::nil)%nat in H74.
  eapply fold_ACSpace  in H74; [idtac | eauto..]. 
  sep lifts (9::1::10::nil)%nat in H74. 
  eapply ACSpaceAarray_fold_any_idx_frm in H74; [idtac | eauto; try lia..]. 
  sep lifts (1::2::9::nil)%nat in H74. 
  eapply ACSpaceAarray_fold_any_idx_frm in H74; [idtac | eauto; try lia..].
  sep lifts (5::3::6::nil)%nat in H74.
  eapply Aarray'_fold_any_idx_frm in H74; [idtac | eauto..].
  sep lifts (1::4::5::nil)%nat in H74.
  eapply Aarray'_fold_any_idx_frm in H74;[idtac | eauto..].
  exact H74. 
  simpl. rewrite max_unsigned_val. lia.
  simpl. rewrite max_unsigned_val. lia.
  splits.
  rewrite app_length. simpl.
  rewrite H50, H54. rewrite S_add_sub_S. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  eauto. 
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  simpl. rewrite max_unsigned_val. lia.
  simpl. rewrite max_unsigned_val. lia.
  rewrite app_length. simpl. 
  rewrite H51, H52. rewrite S_add_sub_S. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl.
  rewrite H50, H54. rewrite S_add_sub_S. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  rewrite app_assoc_reverse. eauto.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl.
  rewrite H51, H52. rewrite S_add_sub_S. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  eauto.
  unfold SLOT_NUM. clear -Hi1le16. lia.
  eauto.
  eauto.
  unfold SLOT_NUM. clear -Hi1le16. lia.
  eauto.

  eapply seq_rule.  
  eapply calle_rule_lvar'.

  unfold Cap_spec.
  simpl. unfold ucos_CNode_Mutate_spec.
  eauto.
  intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  rewrite Hi0true. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_CNode_MutatePre.
  unfold ucos_CNode_MutatePre'.
 

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
  sep cancel 30%nat 1%nat.

  exact H74.
  6:simpl; eauto.
  6:simpl; eauto. 
  6:simpl; eauto.
  6:simpl; eauto.
  eauto.
  go.
  splits.
  rewrite app_length. simpl.   rewrite app_length. simpl.
  rewrite H50, H54, H55. rewrite S_add_sub_S. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl. 
  rewrite H29, H35. rewrite S_add_sub_S. lia.
  lia.
  Optimize Proof.
  Optimize Heap.
  rewrite H48 in Htypematch.
  rewrite app_assoc_reverse. eauto.
  rewrite H48 in H12.
  rewrite app_assoc_reverse. eauto.
  rewrite H48 in H24.
  rewrite app_assoc_reverse. eauto.   
  unfold AOSCSpaceObjectPointer, CSpaceGVars.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold ucos_CNode_MutatePost.  unfold getasrt. 
  unfold ucos_CNode_MutatePost'.
  intros. sep destruct H74.
  sep lifts (16::nil)%nat in H74.
  eapply disj_split in H74.
  destruct H74;  sep split in H74. 
  rewrite H76. eauto.
  eapply disj_split in H74.
  destruct H74;  sep split in H74. 
  rewrite H92. eauto.
  rewrite H95. eauto.

  simpl.
  rewrite Hitrue, Hi0true. auto.

  unfold getasrt, ucos_CNode_MutatePost,ucos_CNode_MutatePost'.
  intros. sep destruct H74.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. 
  unfold ucos_CNode_MutatePre.
  unfold ucos_CNode_MutatePre'.

  intros. sep destruct H74. eexists.
  sep cancel p_local. simpl. auto.

  unfold getasrt, ucos_CNode_MutatePost,ucos_CNode_MutatePost'.
  hoare_split_pure_all.
  simpljoin.
  inverts H80.
  simpl in H74, H75, H76, H77.
  apply sym_eq in H74.
  apply sym_eq in H75.
  apply sym_eq in H76.
  apply sym_eq in H77.
  inverts H74. inverts H75. inverts H76. inverts H77.
  eapply backward_rule1.
  intros.
  sep lift 9%nat in H74.

  apply disj_split in H74.
  exact H74.
  apply disj_rule.
  hoare_split_pure_all.
  rewrite H48 in H46.
  rewrite H48 in H47.
  clear -Hilt64 Hi0lt64 Hi1le16 H46 H47 H74.
  unfold CAP_NULL_CLASS, CAP_CHANNEL_CLASS in H74.
  false.
  destruct H74.
  destruct H.
  assert(0<=Int.unsigned i1 <= 16).
  int auto.
  int auto.

  eauto.
  destruct H.
  int auto.
  rewrite app_assoc_reverse in H.
  destruct H; tryfalse.
  
 

  hoare_split_pure_all.
  rename H76 into Hnew_capability.

  eapply backward_rule1.
  intros.

  apply disj_split in H76.
  exact H76.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H77.
  hoare forward.

  hoare_split_pure_all.
  
  unfold CNODE_MUTATE_FAILURE, CNODE_NONE_FAULT in H77.
  unfold val_inj in H77.
  assert(Int.eq ($8) ($0) = false).
  clear -H77.
  int auto.
  destruct (Int.eq
  ($ 8) ($ 0)).
  tryfalse.
  destruct H77.
  tryfalse.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  
  sep lifts (4::2::5::nil)%nat in H81.
  eapply add_aemp_isr_is_prop in H81. 
  eapply add_isr_is_prop in H81. 

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
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV srcTask_Prio @ char_t |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MUTATE_FAILURE) **
  LV rights @ long |-> Vint32 i2 **
  LV func_capability @ long |-> Vint32 i1 **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
  LV y @ char_t |-> Vint32 i7 ** 
  A_dom_lenv
    ((rights, long)
    :: (func_capability, long)
      :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i, char_t)
                  :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  go.
  

  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply absimp_user_cnode_mutate_succ_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H77.  sep split in H74. 
  clear - H77.
  unfold CNODE_MUTATE_FAILURE, CNODE_NONE_FAULT in H77.
  unfold val_inj in H77.
  assert(Int.eq ($8) ($0) = false).
  int auto.
  destruct (Int.eq
  ($ 8) ($ 0)).
  tryfalse.
  destruct H77.
  tryfalse.

  sep split in H74.
  exact H74.

  hoare_split_pure_all.

  inverts H82.
  hoare forward.
  hoare_split_pure_all.
  clear H82.

  rewrite H49 in H23.
  lets bak_23: H23.
  unfolds in H23.
  destruct H23.
  assert(Ha: 0 <= Int.unsigned i0 < 64).
  clear -Hi0lt64.
  int auto.
  Optimize Proof.
  Optimize Heap.
  assert(Hb: nth_cspace_val ∘ (Int.unsigned i0)
  (v'38 ++
  ((i22, i23,
   v'39 ++
   (v'46, (i32, (i33, i34, v4))) :: v'40,
   i20, l0, v1, i19) :: v'41) ++
  (i27, i28,
  v'48 ++
  (v'50, (i29, (i30, i31, v3))) :: v'49,
  i25, l2, v2, i24) :: v'42) = Some ( (i22, i23,
  v'39 ++
  (v'46, (i32, (i33, i34, v4))) :: v'40,
  i20, l0, v1, i19))).
    rewrite nth_cspace_eq_nth_cspace_val; eauto.
    rewrite nth_cspace_length_imp; eauto.


  lets Hc: H23 Hb.
  destruct Hc. destruct H83. destruct H83.
  clear Ha Hb.

  assert(Ha: 0 <= Int.unsigned i < 64).
  clear -Hilt64.
  int auto.
  assert(Hb: nth_cspace_val ∘ (Int.unsigned i)
  ((v'38 ++
  ((i22, i23,
   v'39 ++
   (v'46, (i32, (i33, i34, v4))) :: v'40,
   i20, l0, v1, i19) :: v'41)) ++
  (i27, i28,
  v'48 ++
  (v'50, (i29, (i30, i31, v3))) :: v'49,
  i25, l2, v2, i24) :: v'42) = Some ( (i27, i28,
  v'48 ++
  (v'50, (i29, (i30, i31, v3))) :: v'49,
  i25, l2, v2, i24))).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.

  rewrite app_length. simpl. 
  rewrite H51, H52. rewrite S_add_sub_S. unfold nat_of_Z. lia.
  clear -Hsrc_dest_lt. eapply Z2Nat.inj_lt; int auto.

  rewrite <- app_assoc_reverse in H23.
  lets Hc: H23 Hb.
  destruct Hc. destruct H85. destruct H85.
  clear Ha Hb.

  rewrite H49 in H75.
  
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

  hoare_lifts_trms_pre (Aop, cspaceid).
  hoare abscsq. 
  Hint Resolve noabs_oslinv.
  go. 
  eapply absimp_user_cnode_mutate_succ_succ.
  unfold AOSCSpaceObjectPointer, CSpaceGVars, AOSCSpacePrioTbl.
    
   go.
  eapply can_change_aop_ACSpaceAarrayTptr.
  

  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  
  sep lifts (5::3::6::nil)%nat in H75.
  eapply add_aemp_isr_is_prop in H75. 
  eapply add_isr_is_prop in H75. 

  unfold OldOSInvWL.
  sep normal. sep eexists.
  try unfold AOSTCBList;unfold_dll.
  unfold CapabilityInv.
  unfold AOSCSpaceCapParent.


  sep normal. sep eexists.
  sep cancel AOSCSpacePrioTbl.
  (* sep cancel Aarray'.
  sep cancel ACSpaceAarrayTptr.  *)
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
  sep cancel AGVars.
  sep cancel 3%nat 7%nat. 
  
  instantiate(1:=LV destTask_Prio @ char_t
  |-> Vint32 i **
  LV srcTask_Prio @ char_t |-> Vint32 i0 **
  LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MUTATE_SUCCESS) **
  LV rights @ long |-> Vint32 i2 **
  LV func_capability @ long |-> Vint32 i1 **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
  LV y @ char_t |-> Vint32 i7 ** 
  A_dom_lenv
    ((rights, long)
    :: (func_capability, long)
      :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i, char_t)
                  :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
 
  {
    clear -Hwellform_descendents.
    eapply Capability_wellform_descendents_update_type.
    eapply Capability_wellform_descendents_update_cap.
    eapply Capability_wellform_descendents_update_cap; auto.
  }
  (* 
  clear -H25. *)
  {
    (* rewrite H49 in H25. *)
    eapply taskPrioProp_update_slots_type_remain.
    eapply taskPrioProp_update_slots_cap_remain.
    eapply taskPrioProp_update_slots_cap_remain.
    eauto.
  }
  { 
   rewrite H49.
   eapply RLH_cspace_slots_P_update_slots_type_remain; eauto.
   eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
  
   eapply RLH_cspace_slots_P_update_slots_cap_remain; eauto.
  
   rewrite list_trans_1.
   rewrite nth_cspace_length_imp; eauto.
   rewrite app_length. simpl.
   rewrite H51, H52. rewrite S_add_sub_S.
   clear -Hsrc_dest_lt. lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; try (int auto).
   rewrite list_trans.
   rewrite <-H49. eauto.
   rewrite H49.
   rewrite list_trans_1.
   unfold update_nth_cspace_slots_cap.
   rewrite nth_cspace_length_imp; eauto.
   rewrite nth_slots_length_imp; eauto.
   rewrite update_nth_cspace_neqrev; eauto.
   rewrite app_assoc_reverse.
   rewrite nth_cspace_length_imp; eauto.
   rewrite app_length. simpl.
   rewrite app_length. simpl.
   rewrite H51, H52, H53.
   rewrite S_add_sub_S.
   rewrite S_add_sub_S.
   clear -Hsrc_dest_lt Hi0lt64.
   lia.
  Optimize Proof.
  Optimize Heap.
   clear -Hilt64. lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; (int auto).
   
  

   rewrite app_length. simpl.
   rewrite app_length. simpl.
   rewrite H51, H52, H53.
   rewrite S_add_sub_S.
   rewrite S_add_sub_S.
   clear -Hsrc_dest_lt Hilt64.
   lia.
   clear -Hilt64. lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; (int auto).
   
   
   clear -Hsrc_dest_lt.
   intro. 
   eapply Z2Nat.inj in H.
   lia.
   int auto. int auto.
   rewrite app_length. simpl.
   rewrite H51, H52.
   rewrite S_add_sub_S. 
   clear -Hsrc_dest_lt. lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; (int auto).
   rewrite <-H83.
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
   rewrite H51, H52, H53.
   rewrite S_add_sub_S.
   rewrite S_add_sub_S_add.
   clear -Hsrc_dest_lt Hilt64.
   lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; (int auto).
   clear -Hilt64. lia.
   rewrite app_length. simpl.
   rewrite app_length. simpl.
   rewrite H51, H52, H53.
   rewrite S_add_sub_S.
   rewrite S_add_sub_S.
   clear -Hsrc_dest_lt Hilt64.
   lia.
   clear -Hilt64. lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; (int auto).
   rewrite app_length. simpl. 
   rewrite app_length. simpl.
   rewrite H51, H52, H53.
   rewrite S_add_sub_S.
   rewrite S_add_sub_S.
   clear -Hsrc_dest_lt Hilt64.
   lia.
   clear -Hilt64. lia.
   clear -Hsrc_dest_lt.

   eapply Z2Nat.inj_lt; (int auto).
   clear -Hsrc_dest_lt.
   intro.
   eapply Z2Nat.inj in H.
   lia.
   int auto. int auto.
   rewrite app_length. simpl.
   rewrite H51, H52.
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
   eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=(v'6 ++
   (i14, i15,
   v'8 ++ (v'34, (i16, (i17, i18, v0))) :: v'30,
   i12, l, v, i11) :: v'35)); eauto.
   
   eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=(v'6 ++
   (i14, i15,
   v'8 ++ (v'34, (i16, (i17, i18, v0))) :: v'30,
   i12, l, v, i11) :: v'35)); eauto. 
   rewrite H49.
   rewrite list_trans_1.
   rewrite nth_cspace_length_imp; eauto.
   rewrite app_length. simpl.
   rewrite H51, H52. rewrite S_add_sub_S.
   clear -Hsrc_dest_lt. lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; try (int auto).
   rewrite H49.

   rewrite nth_cspace_length_imp; eauto.
   rewrite <-H83.
   eapply CSpaceMod.map_get_set'.
   clear -Hsrc_dest_lt.
   intro.
   rewrite H in Hsrc_dest_lt.
   lia.
   instantiate(7:= (update_nth_cspace_slots_cap (Z.to_nat (Int.unsigned i0))
   (Z.to_nat (Int.unsigned i1))
   (update_nth_cspace_slots_cap
      (Z.to_nat (Int.unsigned i))
      (Z.to_nat (Int.unsigned i1))
      (v'38 ++
       ((i22, i23,
        v'39 ++
        (v'46, ($ CAP_CATEGORY_TYPE, (v'65, v'66, v'67)))
        :: v'40, i20, l0, v1, i19) :: v'41) ++
       (i27, i28,
       v'48 ++ (v'50, (i29, (i30, i31, v3))) :: v'49, i25,
       l2, v2, i24) :: v'42)
      ($ CAP_CATEGORY_TYPE, (v'65, i2, v3)))
   ($ CAP_CATEGORY_TYPE, (v'65, v'66&ᵢInt.not i2, v'67)))).
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
   rewrite H51, H52, H53.
   rewrite S_add_sub_S.
   rewrite S_add_sub_S_add.
   clear -Hsrc_dest_lt Hilt64.
   lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; (int auto).
   clear -Hilt64. lia.
   rewrite app_length. simpl.
   rewrite app_length. simpl.
   rewrite H51, H52, H53.
   rewrite S_add_sub_S.
   rewrite S_add_sub_S.
   clear -Hsrc_dest_lt Hilt64.
   lia.
   clear -Hilt64. lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; (int auto).

   rewrite app_length. simpl. 
   rewrite app_length. simpl.
   rewrite H51, H52, H53.
   rewrite S_add_sub_S.
   rewrite S_add_sub_S.
   clear -Hsrc_dest_lt Hilt64.
   lia.
  Optimize Proof.
  Optimize Heap.
   clear -Hilt64. lia.
   clear -Hsrc_dest_lt.
   eapply Z2Nat.inj_lt; (int auto).
   clear -Hsrc_dest_lt.
   intro.
   eapply Z2Nat.inj in H.
   lia.
   int auto. int auto.
   rewrite app_length. simpl.
   rewrite H51, H52.
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
  clear - H82.
  unfold CNODE_NONE_FAULT in H82.
  unfold val_inj in H82.
  assert(Int.eq ($0) ($0) = true) by auto.
  rewrite H77 in H82.
  destruct H82; tryfalse.

  destruct H82.
  sep split in H74.
  exact H74.

  sep split in H74.
  clear - H76.
  unfold CNODE_NONE_FAULT in H76.
  unfold val_inj in H76.
  assert(Int.eq ($0) ($0) = true) by auto.
  rewrite H in H76.
  destruct H76; tryfalse.
  Unshelve. all:exact (Aemp).
Qed.





 