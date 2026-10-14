
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
(*Require Import sem_lab.*) 
Require Import abs_op_capability. 

Import DeprecatedTactic.

Require Import seplog_trm_tacs.
Require Import GetObjSlotPure.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext. 

Require Import CapRelLemmas.

Open Scope list_scope.  
Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.
Set Keyed Unification.

(* CNode Mint *)

(* w/ OS_PRIO_SELF *)

Lemma user_cnode_mint_absinfer_invalid:
  forall P dest src cap rights sch v,
    can_change_aop P ->
    ((((Int.ltu (Int.repr OS_LOWEST_PRIO) src = true) \/ (Int.eq src (Int.repr OS_LOWEST_PRIO) = true))) \/
     (((Int.ltu (Int.repr OS_LOWEST_PRIO) dest = true) \/ (Int.eq dest (Int.repr OS_LOWEST_PRIO) = true)))) ->
    absinfer sch
             (<|| user_cnode_mint_code (Vint32 dest :: Vint32 src :: Vint32 cap :: Vint32 rights :: v) ||> ** P)
             (<|| END (Some (Vint32 (Int.repr OS_PRIO_INVALID))) ||> ** P).
Proof.
  intros.
  infer_solver 0%nat.
Qed.

Lemma user_cnode_mint_absinfer_null_cspace:
  forall P dest src cap rights sch v,
    can_change_aop P ->
    absinfer sch
             (<|| user_cnode_mint_code (Vint32 dest :: Vint32 src :: Vint32 cap :: Vint32 rights :: v) ||> ** P)
             (<|| END (Some (Vint32 (Int.repr CNODE_MINT_FAILURE))) ||> ** P).
Proof.
  intros.
  infer_solver 1%nat.
Qed.

Lemma user_cnode_mint_absinfer_non_cap:
  forall dest src cap rights sch P v,
    can_change_aop P -> 
    absinfer sch ( <|| user_cnode_mint_code (Vint32 dest :: Vint32 src :: Vint32 cap :: Vint32 rights :: v) ||> ** P)
                 ( <|| END (Some (Vint32 (Int.repr USER_CAPABILITY_NONE))) ||>  ** P).

Proof.
  infer_solver 2%nat.
Qed. 

Lemma user_cnode_mint_absinfer_succ:
  forall P dest src cap rights sch v cs cs' src_slots src_childs src_parent src_slot_type src_cap_type src_cap_content src_cap_right src_object_t
    dest_slots dest_childs dest_parent dest_slot_type dest_cap_type dest_cap_content dest_cap_right dest_object_t,
    CSpaceMod.get cs src = Some (src_slots, src_childs, src_parent) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) src_slots =
      Some (src_slot_type, (src_cap_type, (src_cap_content, src_cap_right, src_object_t))) ->
    CSpaceMod.get cs dest = Some (dest_slots, dest_childs, dest_parent) ->
    nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots =
      Some (dest_slot_type, (dest_cap_type, (dest_cap_content, dest_cap_right, dest_object_t))) ->  
    Int.eq src_cap_type (Int.repr CAP_CATEGORY_TYPE) = true ->
    Int.eq (Int.and (Int.not src_cap_right) rights) (Int.repr (Z.of_nat 0)) = true ->
    Int.eq rights src_cap_right = false ->
    cs' = CSpaceMod.set cs dest 
      (update_nth_slots (Z.to_nat (Int.unsigned cap)) dest_slots
        (dest_slot_type, (Int.repr CAP_CATEGORY_TYPE, (src_cap_content, rights, dest_object_t))), dest_childs, dest_parent) ->
    can_change_aop P ->
    absinfer sch
             (<|| user_cnode_mint_code (Vint32 dest :: Vint32 src :: Vint32 cap :: Vint32 rights :: v) ||> ** 
             Hcapspace cs ** P) 
             (<|| END (Some (Vint32 (Int.repr CNODE_MINT_SUCCESS))) ||> ** 
             Hcapspace cs' ** P).
Proof.
  intros.
  infer_solver 3%nat.
Qed.

Lemma user_cnode_mint_absinfer_fail:
  forall P dest src cap rights sch v,
    can_change_aop P ->
    absinfer sch
             (<|| user_cnode_mint_code (Vint32 dest :: Vint32 src :: Vint32 cap :: Vint32 rights :: v) ||> ** P)
             (<|| END (Some (Vint32 (Int.repr CNODE_MINT_FAILURE))) ||> ** P).
Proof.
  intros.
  infer_solver 4%nat.
Qed.

Ltac val_help H:=
    try change (Int.ltu Int.zero Int.zero) with (false) in H;
    try change (Int.ltu Int.one Int.zero) with (false) in H;
    try change (Int.ltu Int.zero Int.one) with (true) in H;
    try change (Int.ltu Int.one Int.one) with (false) in H;
    try change (Int.eq Int.one Int.one) with (true) in H;
    try change (Int.eq Int.one Int.zero) with (false) in H;
    try change (Int.eq Int.zero Int.one) with (false) in H;
    try change (Int.eq Int.zero Int.zero) with (true) in H;
    try change (Int.ltu Int.zero (Int.notbool Int.one)) with (false) in H;
    try change (Int.ltu Int.zero (Int.notbool Int.zero)) with (true) in H.

Lemma UserCNodeMintProof: 
  forall  tid vl p r, 
    Some p =
    BuildPreA' os_api user_cnode_mint
    user_cnode_mint_api vl  OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api user_cnode_mint
    user_cnode_mint_api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api user_cnode_mint = Some (t, d1, d2, s) /\
      {|Cap_spec, GetHPrio, OSLInv,  I, r, Afalse|}|-tid 
        {{p ** (EX destTask_Prio srcTask_Prio, [|
                Some(Vint32 destTask_Prio) = nth_val 3%nat vl /\
                Some(Vint32 srcTask_Prio) = nth_val 2%nat vl /\
                (Int.unsigned destTask_Prio < 64) /\ 
                (Int.unsigned destTask_Prio > Int.unsigned srcTask_Prio)|])}} s {{Afalse}}.
Proof.
  init_spec.
  simpl in H.
  destruct H. destruct H0. destruct H1.
  inverts H. inverts H0. 
  rename H2 into Hsrc_lt_dest.
  rename H1 into Hilt64.
  assert(Hi0lt64: Int.unsigned i0 < 64). lia.

  hoare forward. 
  pure_auto. destruct (Int.ltu (Int.repr OS_LOWEST_PRIO) i0); simpl; auto. 
  pure_auto. destruct (Int.eq i0 (Int.repr OS_LOWEST_PRIO)); simpl; auto.
  destruct (Int.ltu (Int.repr OS_LOWEST_PRIO) i0); destruct (Int.eq i0 (Int.repr OS_LOWEST_PRIO)); simpl; auto.
  pure_auto. destruct (Int.ltu (Int.repr OS_LOWEST_PRIO) i); simpl; auto. 
  pure_auto. destruct (Int.eq i (Int.repr OS_LOWEST_PRIO)); simpl; auto.
  destruct (Int.ltu (Int.repr OS_LOWEST_PRIO) i); destruct (Int.eq i (Int.repr OS_LOWEST_PRIO)); simpl; auto.
  pure_auto.
  hoare unfold.
  hoare abscsq. apply noabs_oslinv.
  eapply user_cnode_mint_absinfer_invalid. go.
  destruct (Int.ltu (Int.repr OS_LOWEST_PRIO) i0) eqn: Hi0ll;
  destruct (Int.eq i0 (Int.repr OS_LOWEST_PRIO)) eqn: Hi0el; 
  destruct (Int.ltu (Int.repr OS_LOWEST_PRIO) i) eqn: Hill;
  destruct (Int.eq i (Int.repr OS_LOWEST_PRIO)) eqn: Hiel; auto; 
  do 3 (simpl in H; val_help H); simpl in H; tryfalse.
  hoare forward.

  hoare forward.
  hoare forward prim.

  try unfold AOSTCBList;unfold_dll.
  pure intro.
  hoare forward.
  go.

  assert(Htrue: Int.unsigned i7 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H19. int auto.
  assert(Hitrue: Int.unsigned i <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H4. int auto.
  assert(Hi0true: Int.unsigned i0 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H3. int auto.
  assert(Hpriolt64: Int.unsigned i7 < 64).
  unfold TCBList_P in H8.
  simpljoin.
  unfold TCBNode_P in H13.
  destruct x2, p, p.
  simpljoin. 
  unfold RL_TCBblk_P in H26.
  simpljoin.
  unfold V_OSTCBPrio in H26. simpl in H26. inverts H26. lia.

  unfold CapabilityInv.
  hoare_split_pure_all.
  rename H27 into Hwellform_descendents.
  destruct v'6. 
  hoare remember (1::nil)%nat pre.
  unfold AOSCSpacePrioTbl. hoare_split_pure_all.
  assert(Htypematch : array_type_vallist_match CSPACE ∗ v'8).
  simpljoin. auto.
  assert(Hlenv'8: length v'8 = 64%nat). simpljoin. auto.
  assert(Hlenv'30: length v'30 = 64%nat). simpljoin. auto.
  eapply backward_rule1 with (p:=AOSCSpacePrioTbl (b, i10) v'8 v'30 v'31 ** H27).
  intros.
  unfold AOSCSpacePrioTbl. 
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep split; auto.
  subst H27.
  clear H28.
  Require Import seplog_trm_tacs.
  hoare_lifts_trms_pre (Aop, AOSCSpacePrioTbl, Alvarmapsto pCSpace, Alvarmapsto y, A_dom_lenv, p_local).
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
    rewrite Htrue; auto.
    eauto. auto. lia.
    apply Hpriolt64. 
    rewrite Hlenv'8. apply Hpriolt64.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hlenv'8. lia.
  }
  eapply eq_vptr. eauto.
  intros.
  eexists.
  sep cancel p_local. simpl. auto.
  eapply backward_rule1 with(p:=<||
    user_cnode_mint_code
      (Vint32 i
      :: Vint32 i0
          :: Vint32 i1
            :: Vint32 i2 :: v') ||>  **
    AOSCSpacePrioTbl (b, i10) v'8 v'30 v'31 **
    LV pCSpace @ CSPACE ∗ |-> nth_val' (Z.to_nat (Int.unsigned i7)) v'8 **
    LV y @ char_t |-> Vint32 i7 **
    A_dom_lenv
      ((rights, long)
      :: (func_capability, long)
          :: (srcTask_Prio, char_t)
            :: (destTask_Prio, char_t)
                :: (pCSpace, CSPACE ∗)
                  :: (ios_cap_defs.i, char_t)
                      :: (y, char_t) :: nil) **
    p_local OSLInv (v'29, Int.zero)
      (logic_val (V$ 1)
      :: logic_val (V$ __EvLoc_normal)
          :: logic_val Vnull
            :: logic_val Vnull
                :: logic_val Vnull :: nil) ** H27).
  intros. unfold AOSCSpacePrioTbl.
  sep cancel H27. sep auto.

  subst H27.
  assert(HpCSpacetype: rule_type_val_match CSPACE ∗
    (nth_val' (Z.to_nat (Int.unsigned i7)) v'8) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hlenv'8. lia.
  clear H28.
  hoare forward.
  unfold val_inj, val_eq.
  clear -HpCSpacetype.
  unfold rule_type_val_match in HpCSpacetype.
  destruct (nth_val' (Z.to_nat (Int.unsigned i7)) v'8); tryfalse; auto;
  destruct a; auto.
  hoare_split_pure_all.

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
  sep cancel AGVars. unfold AOSCSpaceCapParent in H28.
  sep normal in H28.  sep cancel CapParent.
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
  splits; auto. go. go.
  
  hoare abscsq.
  apply noabs_oslinv.
  eapply user_cnode_mint_absinfer_null_cspace.
  can_change_aop_solver.
  hoare forward. 

  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hnotnull: (nth_val' (Z.to_nat (Int.unsigned i7)) v'8) <> Vnull).
  clear -HpCSpacetype H27.
  unfold rule_type_val_match in HpCSpacetype.
  unfold val_inj, val_eq in H27.
  destruct (nth_val' (Z.to_nat (Int.unsigned i7)) v'8); destruct H27; tryfalse.
  destruct a; auto. destruct a. auto.
  clear H27.
  eapply backward_rule1.
  intros.

  sep_lifts_trms_in H27 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned i7)) in H27.
  exact H27.
  rewrite Hlenv'30; lia. auto.
  hoare_split_pure_all.
  unfold ACSpace.
  destruct v'34, p, p, p, v'38.
  unfold Acnode. 
  destruct c, p. 
  hoare_split_pure_all.
  simpljoin.
  rename H36 into Hi11range.
  rename H37 into H36.
  rename H38 into H37.
  eapply backward_rule1.
  intros.

  sep_lifts_trms_in H27 (ASlots).
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(SLOT_CNODE_CAP)) in H27; eauto. 
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  hoare_split_pure_all.
  simpljoin.
  unfold ACap. destruct v'38, c, p. 
  unfold AOSCSpaceCapParent.
  hoare_split_pure_all.
  destruct H40.
  destruct H41.
  assert(Hxi: (Z.to_nat(Int.unsigned i) < 64)%nat).
  clear -Hilt64. lia.  
  lets Hy: nthval'_has_value_Tint32 H40 H41 Hxi.
  destruct Hy. destruct H43.
  assert (nth_val' (Z.to_nat (Int.unsigned i7))
        (v'36 ++ Vptr (b0, i13) :: v'37) = Vptr (b0, i13)).
  eapply nth_val'_length_imp. eauto.
  rewrite H45.
  eapply forward_rule1 with (q:=Afalse \\//Afalse).
  intros.
  destruct H46; auto.
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
                  sep cancel pCSpace.
                  exact H46.
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

      sep normal in H46.
      sep lift 5%nat in H46.
      unfold Aptrmapsto in H46 at 1.
      exact H46.
      unfold SLOT_CNODE_CAP. rewrite max_unsigned_val.
      lia. lia. 
    }
    simpl. auto. 
    destruct_s s. simpl; eauto.
    eauto.
    unfold val_inj, bop_eval, and. 
    auto. 
  Optimize Proof.
  Optimize Heap.
    simpl. eauto.
    destruct_s s. simpl; eauto.
    eauto.
    unfold val_inj, bop_eval, and, val_eq.
    destruct(Int.eq (i18&ᵢ$ CNODE_MINT_CAP) ($ 0)); auto.
    simpl. eauto.
    sep get rv.

    rewrite Hitrue. auto. 
    rewrite H43. auto.
    rewrite Hi0true. auto.
    rewrite H43. 
    unfold val_inj, val_eq.
    destruct (Int.eq x i0); eauto.
    rewrite H43. 
    unfold val_inj, notint, val_eq.
    destruct (Int.eq x i0); eauto.
    eauto. 
    unfold val_inj, bop_eval, val_eq, and, uop_eval, notint, bool_and.
    unfold Int.zero.
    rewrite H43.
    destruct (Int.eq (i18&ᵢ$ CNODE_MINT_CAP) ($ 0)); 
    destruct (Int.eq x i0); unfold Int.notbool;repeat (val_help; simpl); auto.
    simpl. eauto.
    hoare_split_pure_all.
    eapply backward_rule1.
    intros.
    sep lifts (3::4::5::6::nil)%nat in H47. 
    eapply fold_Cap in H47.
    sep lifts (2::3::1::4::nil)%nat in H47.
    eapply ASlots_fold_any_idx_frm in H47; [idtac | eauto..]. 
    sep lifts (6::7::1::nil)%nat in H47.
    eapply fold_Acnode in H47.
    sep lifts (1::6::7::8::9::nil)%nat in H47.
    eapply fold_ACSpace in H47; [idtac | eauto..]. 
    sep lifts (5::1::6::nil)%nat in H47. 
    eapply ACSpaceAarray_fold_any_idx_frm in H47; [idtac | eauto; try lia..]. 
    sep lifts (2::1::3::4::nil)%nat in H47.
    eapply fold_AOSCSpacePrioTbl1 in H47.
    exact H47. 
    rewrite app_length. simpl.
    rewrite H29, H37. rewrite S_add_sub_S. lia.
    clear -Hpriolt64. lia. 
    rewrite app_length. simpl.
    rewrite H30, H36. rewrite S_add_sub_S. lia. lia.
    eauto.
    rewrite nth_val_imp_nth_val'_2. rewrite H45. eauto.
    (* clear -Hc1. eapply Z2Nat.inj_lt; int auto.  *)
    rewrite app_length. simpl. 
    rewrite H29, H37. rewrite S_add_sub_S. lia. lia.
    clear -Hpriolt64. lia. 
    rewrite app_length. simpl. 
    rewrite H28, H39. rewrite S_add_sub_S.
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
    instantiate(1:=LV destTask_Prio @ char_t |-> Vint32 i **
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
    split. eauto.
    go.
    go.
    go.
    hoare abscsq.
    apply noabs_oslinv.
    eapply user_cnode_mint_absinfer_non_cap; eauto.
    can_change_aop_solver.
    hoare forward.

  hoare_split_pure_all.
  rewrite H43 in H46.
(* 调用ucos_CNode预操作，合上不变式 *)
  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H47. 
  eapply fold_Cap in H47.
  sep lifts (2::3::1::4::nil)%nat in H47.
  eapply ASlots_fold_any_idx_frm in H47; [idtac | eauto..]. 
  sep lifts (6::7::1::nil)%nat in H47.
  eapply fold_Acnode in H47.
  sep lifts (1::6::7::8::9::nil)%nat in H47.
  eapply fold_ACSpace in H47; [idtac | eauto..]. 
  sep lifts (5::1::6::nil)%nat in H47. 
  eapply ACSpaceAarray_fold_any_idx_frm in H47; [idtac | eauto; try lia..]. 
  sep lifts (2::1::3::4::nil)%nat in H47.
  eapply fold_AOSCSpacePrioTbl1 in H47; [idtac | eauto; try lia..].
  sep_lifts_trms_in H47 (aemp_isr_is).
  eapply aemp_isr_elim in H47.
  sep_lifts_trms_in H47 (Aisr, Ais, A_isr_is_prop). 
  eapply elim_a_isr_is_prop in H47. 
  exact H47.
  rewrite nth_val_imp_nth_val'_2. rewrite H45. eauto.
  rewrite Hlenv'8. lia. 
  eauto.
  unfold SLOT_CNODE_CAP, SLOT_NUM. lia.
  eauto.
  assert (Hcases1: 
    not ((nth_val' (Z.to_nat (Int.unsigned i)) (v'36 ++ Vptr (b0, i13) :: v'37) <> Vnull) /\
         (nth_val' (Z.to_nat (Int.unsigned i0)) (v'36 ++ Vptr (b0, i13) :: v'37) <> Vnull)) \/
    (nth_val' (Z.to_nat (Int.unsigned i)) (v'36 ++ Vptr (b0, i13) :: v'37) <> Vnull) /\
    (nth_val' (Z.to_nat (Int.unsigned i0)) (v'36 ++ Vptr (b0, i13) :: v'37) <> Vnull)) by tauto.
  destruct Hcases1 as [Hfail1|Hsucc1].
  eapply seq_rule.  
  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_CNode_Mint_spec.
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
  unfold ucos_CNode_MintPre.
  unfold ucos_CNode_MintPre'.
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel 30%nat 1%nat.
  exact H47.
  4:simpl; eauto.
  4:simpl; eauto. 
  4:simpl; eauto.
  4:simpl; eauto.
  go.
  eauto.
  eauto.
  unfold AOSCSpaceObjectPointer, CSpaceGVars.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold ucos_CNode_MintPost. unfold getasrt. 
  unfold ucos_CNode_MintPost'.
  intros. sep destruct H47.
  sep lifts (16::nil)%nat in H47.
  eapply disj_split in H47.
  destruct H47; sep split in H47. 
  rewrite H49. eauto.
  eapply disj_split in H47.
  destruct H47; sep split in H47. 
  rewrite H65. eauto.
  rewrite H66. eauto.    
  simpl.
  rewrite Hitrue, Hi0true. auto.
  unfold getasrt, ucos_CNode_MintPost, ucos_CNode_MintPost'.
  intros. sep destruct H47.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. 
  unfold ucos_CNode_MintPre.
  unfold ucos_CNode_MintPre'.
  intros. sep destruct H47. eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt, ucos_CNode_MintPost, ucos_CNode_MintPost'.
  hoare_split_pure_all.
  inverts H53.
  simpl in H47, H48, H49, H50.
  apply sym_eq in H47.
  apply sym_eq in H48.
  apply sym_eq in H49.
  apply sym_eq in H50.
  inverts H47. inverts H48. inverts H49. inverts H50.
  eapply backward_rule1.
  intros.
  sep lift 9%nat in H47.
  apply disj_split in H47.
  exact H47.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H48.
  hoare forward.
  hoare_split_pure_all.
  clear - H48.
  unfold CNODE_MINT_FAILURE, CNODE_NONE_FAULT in H48.
  unfold val_inj in H48.
  assert(Int.eq ($5) ($0) = false).
  clear - H48.
  int auto.
  Optimize Proof.
  Optimize Heap.
  destruct (Int.eq ($ 5) ($ 0)).
  tryfalse.
  destruct H48.
  tryfalse.
  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (4::2::5::nil)%nat in H50.
  eapply add_aemp_isr_is_prop in H50. 
  eapply add_isr_is_prop in H50. 
  unfold OldOSInvWL.
  sep normal. sep eexists.
  try unfold AOSTCBList; unfold_dll.
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
  instantiate(1:=LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 i0 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MINT_FAILURE) **
    LV rights @ long |-> Vint32 i2 **
    LV func_capability @ long |-> Vint32 i1 **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
    LV y @ char_t |-> Vint32 i7 ** 
    A_dom_lenv ((rights, long) :: (func_capability, long)
      :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i, char_t)
                  :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  eauto.
  hoare abscsq. 
  apply noabs_oslinv.
  eapply user_cnode_mint_absinfer_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H48. sep split in H48. 
  clear - H49.
  unfold CNODE_MINT_FAILURE, CNODE_NONE_FAULT in H49.
  unfold val_inj in H49.
  assert(Int.eq ($5) ($0) = false).
  int auto.
  destruct (Int.eq ($ 5) ($ 0)).
  tryfalse.
  destruct H49.
  tryfalse.
  sep split in H48.
  exact H48.

  hoare_split_pure_all.
  (*rename H48 into Hsrc_capability.*)
  rename H49 into Hdest_capability.
  destruct H47. destruct H49.
  tryfalse.

  destruct Hsucc1. 
  assert(Hcases2:
    (not (CAP_NULL_CLASS <= Int.unsigned i1 <= CAP_CHANNEL_CLASS) \/
    (CAP_NULL_CLASS <= Int.unsigned i1 <= CAP_CHANNEL_CLASS))) by tauto.
  destruct Hcases2 as [Hfail2|Hsucc2].

  eapply seq_rule.  
  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_CNode_Mint_spec.
  eauto. intros.
  eapply rvl_elim. sep get rv.
  rewrite Hitrue. auto.
  eapply rvl_elim. sep get rv.
  rewrite Hi0true. auto.
  eapply rvl_elim. sep get rv.
  eapply rvl_elim. sep get rv.
  eapply rvl_nil.
  intros. unfold getasrt.
  unfold ucos_CNode_MintPre.
  unfold ucos_CNode_MintPre'.

  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aier.
  sep cancel Aisr. sep cancel Ais.
  sep cancel Acs. sep cancel Aop.
  sep split.
  sep cancel p_local.
  sep cancel AOSCSpacePrioTbl.
  sep cancel 30%nat 1%nat.
  exact H49.
  4:simpl; eauto.
  4:simpl; eauto. 
  4:simpl; eauto.
  4:simpl; eauto.
  eauto.
  go.
  eauto.
  
  unfold AOSCSpaceObjectPointer, CSpaceGVars. go.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold ucos_CNode_MintPost. unfold getasrt. 
  unfold ucos_CNode_MintPost'.
  intros. sep destruct H49.
  sep lifts (16::nil)%nat in H49.
  eapply disj_split in H49.
  destruct H49; sep split in H49. 
  rewrite H51. eauto.
  eapply disj_split in H49.
  destruct H49; sep split in H49. 
  rewrite H67. eauto.
  rewrite H68. eauto.

  simpl.
  rewrite Hitrue, Hi0true. auto.

  unfold getasrt, ucos_CNode_MintPost, ucos_CNode_MintPost'.
  intros. sep destruct H49.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. 
  unfold ucos_CNode_MintPre.
  unfold ucos_CNode_MintPre'.

  intros. sep destruct H49. eexists.
  sep cancel p_local. simpl. auto.

  unfold getasrt, ucos_CNode_MintPost, ucos_CNode_MintPost'.
  hoare_split_pure_all.
  inverts H55.
  simpl in H49, H50, H51, H52.
  apply sym_eq in H49.
  apply sym_eq in H50.
  apply sym_eq in H51.
  apply sym_eq in H52.
  inverts H49. inverts H50. inverts H51. inverts H52.
  eapply backward_rule1.
  intros.
  sep lift 9%nat in H49.

  apply disj_split in H49.
  exact H49.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H50.
  hoare forward.
  hoare_split_pure_all.
  clear - H50.
  unfold CNODE_MINT_FAILURE, CNODE_NONE_FAULT in H50.
  unfold val_inj in H50.
  assert(Int.eq ($5) ($0) = false).
  clear - H50.
  int auto.
  destruct (Int.eq ($ 5) ($ 0)).
  tryfalse.
  destruct H50.
  tryfalse.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (4::2::5::nil)%nat in H52.
  eapply add_aemp_isr_is_prop in H52. 
  eapply add_isr_is_prop in H52. 
  unfold OldOSInvWL.
  sep normal. sep eexists.
  try unfold AOSTCBList; unfold_dll.
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
  instantiate(1:=LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 i0 **
    LV rights @ long |-> Vint32 i2 **
    LV func_capability @ long |-> Vint32 i1 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MINT_FAILURE) **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
    LV y @ char_t |-> Vint32 i7 ** 
    A_dom_lenv ((rights, long) :: (func_capability, long)
      :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i, char_t)
                  :: (y, char_t) :: nil)).
  sep auto; eauto.
  split. eauto.
  go.
  go.
  eauto.
  hoare abscsq. 
  apply noabs_oslinv.
  eapply user_cnode_mint_absinfer_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H50. sep split in H50. 
  clear - H51.
  unfold CNODE_MINT_FAILURE, CNODE_NONE_FAULT in H51.
  unfold val_inj in H51.
  assert(Int.eq ($5) ($0) = false).
  int auto.
  Optimize Proof.
  Optimize Heap.
  destruct (Int.eq ($ 5) ($ 0)).
  tryfalse.
  destruct H51.
  tryfalse.
  sep split in H50.
  exact H50.

  hoare_split_pure_all.
  rename H51 into Hdest_capability.
  eapply backward_rule1.
  intros.
  apply disj_split in H51.
  exact H51.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H52.
  hoare forward.
  hoare_split_pure_all.
  unfold CNODE_MINT_FAILURE, CNODE_NONE_FAULT in H52.
  unfold val_inj in H52.
  assert(Int.eq ($5) ($0) = false).
  clear -H52.
  int auto.
  destruct (Int.eq ($ 5) ($ 0)).
  tryfalse.
  destruct H52.
  tryfalse.
  hoare_split_pure_all.

  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (4::2::5::nil)%nat in H56.
  eapply add_aemp_isr_is_prop in H56. 
  eapply add_isr_is_prop in H56. 
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
  instantiate(1:=LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 i0 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MINT_FAILURE) **
    LV rights @ long |-> Vint32 i2 **
    LV func_capability @ long |-> Vint32 i1 **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
    LV y @ char_t |-> Vint32 i7 ** 
    A_dom_lenv ((rights, long) :: (func_capability, long)
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
  apply noabs_oslinv.
  eapply user_cnode_mint_absinfer_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H52. sep split in H49. 
  clear - H52.
  unfold CNODE_MINT_FAILURE, CNODE_NONE_FAULT in H52.
  unfold val_inj in H52.
  assert(Int.eq ($5) ($0) = false).
  int auto.
  destruct (Int.eq ($ 5) ($ 0)).
  tryfalse.
  destruct H52.
  tryfalse.
  sep split in H49.
  exact H49.
  destruct H49.
  tryfalse.

  destruct Hsucc2.
  rename H50 into Hi1le16. unfold CAP_CHANNEL_CLASS in Hi1le16.
  clear H49.
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H49 AOSCSpacePrioTbl.
  eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with(idx1:=Z.to_nat(Int.unsigned i)) (idx2:=Z.to_nat(Int.unsigned i0)) in H49.
  exact H49.
  unfold AOSCSpacePrioTbl in H49.
  sep split in H49.
  destruct H50.
  destruct H58.
  rewrite H58. lia.
  
  clear -Hsrc_lt_dest.
  eapply Z2Nat.inj_lt; int auto.
  eauto. eauto.

  hoare_split_pure_all.
  simpljoin.
  unfold ACSpace.
  destruct v'40, p, p, p, v'47.
  unfold Acnode. 
  destruct c, p. 
  destruct v'39, p, p, p, v'46.
  destruct c, p. 

  hoare_split_pure_all.
  simpljoin.
  rename H67 into Hi20range.
  rename H68 into Hi24range.
  eapply backward_rule1.
  intros.
  sep lifts(10::nil)%nat in H67.
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned i1)) in H67; eauto. 
  unfold SLOT_NUM. clear -Hi1le16. lia.
  
  hoare_split_pure_all.
  simpljoin.
  eapply backward_rule1.
  intros.
  sep lifts(21::nil)%nat in H67.
  eapply ASlots_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned i1)) in H67; eauto. 
  unfold SLOT_NUM. clear -Hi1le16. lia.

  hoare_split_pure_all.
  simpljoin.
  unfold ACap. destruct v'51, c, p. destruct v'47, c, p.  

  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lifts (3::4::5::6::nil)%nat in H75. 
  eapply fold_Cap in H75.
  sep lifts (2::3::1::4::nil)%nat in H75.
  eapply ASlots_fold_any_idx_frm in H75; [idtac | eauto..]. 
  sep lifts (23::24::1::nil)%nat in H75.
  eapply fold_Acnode in H75.
  sep lifts (1::23::24::25::26::nil)%nat in H75.
  eapply fold_ACSpace in H75; [idtac | eauto..]. 
  sep lifts (4::5::6::7::nil)%nat in H75. 
  eapply fold_Cap in H75.
  sep lifts (3::4::1::5::nil)%nat in H75.
  clear H71.
  eapply ASlots_fold_any_idx_frm with (slotsvl:=(v'39 ++
    (v'46, (i32, (i33, i34, v4))) :: v'40)) in H75; [idtac | eauto..]. 
  sep lifts (10::11::1::nil)%nat in H75.
  eapply fold_Acnode in H75.
  sep lifts (1::10::11::12::13::nil)%nat in H75.
  eapply fold_ACSpace in H75; [idtac | eauto..]. 
  sep lifts (9::1::10::nil)%nat in H75. 
  eapply ACSpaceAarray_fold_any_idx_frm in H75; [idtac | eauto; try lia..]. 
  sep lifts (1::2::9::nil)%nat in H75. 
  eapply ACSpaceAarray_fold_any_idx_frm in H75; [idtac | eauto; try lia..].
  sep lifts (5::3::6::nil)%nat in H75.
  eapply Aarray'_fold_any_idx_frm in H75; [idtac | eauto..].
  sep lifts (1::4::5::nil)%nat in H75.
  eapply Aarray'_fold_any_idx_frm in H75; [idtac | eauto..].
  exact H75. 
  simpl. rewrite max_unsigned_val. lia.
  simpl. rewrite max_unsigned_val. lia.
  splits.
  rewrite app_length. simpl.
  rewrite H51, H55. rewrite S_add_sub_S. lia.
  clear -Hsrc_lt_dest. eapply Z2Nat.inj_lt; int auto. eauto. 
  clear -Hsrc_lt_dest. eapply Z2Nat.inj_lt; int auto.
  simpl. rewrite max_unsigned_val. lia.
  simpl. rewrite max_unsigned_val. lia.
  rewrite app_length. simpl. 
  rewrite H52, H53. rewrite S_add_sub_S. lia.
  clear -Hsrc_lt_dest. eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl.
  rewrite H51, H55. rewrite S_add_sub_S. lia.
  clear -Hsrc_lt_dest. eapply Z2Nat.inj_lt; int auto.
  rewrite app_assoc_reverse. eauto.
  clear -Hsrc_lt_dest. eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl.
  rewrite H52, H53. rewrite S_add_sub_S. lia.
  clear -Hsrc_lt_dest. eapply Z2Nat.inj_lt; int auto.
  eauto.
  unfold SLOT_NUM. clear -Hi1le16. lia.
  eauto.
  eauto.
  unfold SLOT_NUM. clear -Hi1le16. lia.
  eauto.

  eapply seq_rule.  
  eapply calle_rule_lvar'.
  unfold Cap_spec.
  simpl. unfold ucos_CNode_Mint_spec.
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
  unfold ucos_CNode_MintPre.
  unfold ucos_CNode_MintPre'.
 
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

  exact H75.
  5:simpl; eauto.
  5:simpl; eauto. 
  5:simpl; eauto.
  5:simpl; eauto.
  go.
  splits.
  rewrite app_length. simpl. rewrite app_length. simpl.
  rewrite H51, H55, H56. rewrite S_add_sub_S. lia.
  clear -Hsrc_lt_dest. eapply Z2Nat.inj_lt; int auto.
  rewrite app_length. simpl. 
  rewrite H30, H36. rewrite S_add_sub_S. lia.
  lia.
  Optimize Proof.
  Optimize Heap.
  rewrite H49 in Htypematch.
  rewrite app_assoc_reverse. eauto.
  rewrite H49 in H13.
  rewrite app_assoc_reverse. eauto.
  rewrite H49 in H25.
  rewrite app_assoc_reverse. eauto.   
  unfold AOSCSpaceObjectPointer, CSpaceGVars. go.
  go.
  (* eapply GoodFrm_ACSpaceAarrayTptr. *)
  unfold retpost.
  unfold ucos_CNode_MintPost.  unfold getasrt. 
  unfold ucos_CNode_MintPost'.
  intros. sep destruct H75.
  sep lifts (16::nil)%nat in H75.
  eapply disj_split in H75.
  destruct H75; sep split in H75. 
  rewrite H77. eauto.
  eapply disj_split in H75.
  destruct H75; sep split in H75. 
  rewrite H93. eauto.
  rewrite H94. eauto.
  simpl.
  rewrite Hitrue, Hi0true. auto.

  unfold getasrt, ucos_CNode_MintPost,ucos_CNode_MintPost'.
  intros. sep destruct H75.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. 
  unfold ucos_CNode_MintPre.
  unfold ucos_CNode_MintPre'.

  intros. sep destruct H75. eexists.
  sep cancel p_local. simpl. auto.

  unfold getasrt, ucos_CNode_MintPost,ucos_CNode_MintPost'.
  hoare_split_pure_all.
  simpljoin.
  inverts H81.
  simpl in H75, H76, H77, H78.
  apply sym_eq in H75.
  apply sym_eq in H76.
  apply sym_eq in H77.
  apply sym_eq in H78.
  inverts H75. inverts H76. inverts H77. inverts H78.
  eapply backward_rule1.
  intros.
  sep lift 9%nat in H75.
  apply disj_split in H75.
  exact H75.
  apply disj_rule.
  hoare_split_pure_all.
  rewrite H49 in H47.
  rewrite H49 in H48.
  clear -Hilt64 Hi0lt64 Hi1le16 H47 H48 H75.
  unfold CAP_NULL_CLASS, CAP_CHANNEL_CLASS in H75.
  false.
  destruct H75.
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
  rename H77 into Hdest_capability.
  eapply backward_rule1.
  intros.
  apply disj_split in H77.
  exact H77.
  apply disj_rule.
  hoare_split_pure_all.
  inverts H78.
  hoare forward.

  hoare_split_pure_all.
  unfold CNODE_MINT_FAILURE, CNODE_NONE_FAULT in H78.
  unfold val_inj in H78.
  assert(Int.eq ($5) ($0) = false).
  clear -H78.
  int auto.
  destruct (Int.eq ($ 5) ($ 0)).
  tryfalse.
  destruct H78.
  tryfalse.

  hoare_split_pure_all.
  eapply seq_rule.
  eapply forward_rule2.
  hoare_lifts_trms_pre (Aop).
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros. 
  sep lifts (4::2::5::nil)%nat in H82.
  eapply add_aemp_isr_is_prop in H82. 
  eapply add_isr_is_prop in H82. 
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
  instantiate(1:=LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 i0 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_MINT_FAILURE) **
    LV rights @ long |-> Vint32 i2 **
    LV func_capability @ long |-> Vint32 i1 **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
    LV y @ char_t |-> Vint32 i7 ** 
    A_dom_lenv ((rights, long) :: (func_capability, long)
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
  apply noabs_oslinv.
  eapply user_cnode_mint_absinfer_fail.
  can_change_aop_solver.
  hoare forward.

  destruct H78. sep split in H75. 
  clear - H78.
  unfold CNODE_MINT_FAILURE, CNODE_NONE_FAULT in H78.
  unfold val_inj in H78.
  assert(Int.eq ($5) ($0) = false).
  int auto.
  destruct (Int.eq ($ 5) ($ 0)).
  tryfalse.
  destruct H78.
  tryfalse.
  sep split in H75.
  exact H75.

  hoare_split_pure_all.
  inverts H81.
  hoare forward.
  hoare_split_pure_all.
  clear H81.

  rewrite H50 in H24.
  lets bak_24: H24.
  unfolds in H24.
  destruct H24.
  assert(Ha: 0 <= Int.unsigned i0 < 64).
  clear -Hi0lt64; int auto.
  assert(Hb: nth_cspace_val ∘ (Int.unsigned i0)
    (v'38 ++ 
      ((i27, i28, v'39 ++ (v'46, (i32, (i33, i34, v4))) :: v'40, 
        i25, l2, v2, i24) :: v'41) ++ 
      (i22, i23, v'48 ++ (v'50, (i29, (i30, i31, v3))) :: v'49,
        i20, l0, v1, i19) :: v'42) = 
    Some (i27, i28, v'39 ++ (v'46, (i32, (i33, i34, v4))) :: v'40,
      i25, l2, v2, i24)).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.

  lets Hc: H24 Hb.
  destruct Hc. destruct H82. destruct H82.
  clear Ha Hb.

  assert(Ha: 0 <= Int.unsigned i < 64).
  clear -Hilt64. int auto.

  assert(Hb: nth_cspace_val ∘ (Int.unsigned i)
    ((v'38 ++
    ((i27, i28, v'39 ++ (v'46, (i32, (i33, i34, v4))) :: v'40,
      i25, l2, v2, i24) :: v'41)) ++
    (i22, i23, v'48 ++ (v'50, (i29, (i30, i31, v3))) :: v'49,
      i20, l0, v1, i19) :: v'42) = 
    Some (i22, i23, v'48 ++ (v'50, (i29, (i30, i31, v3))) :: v'49,
    i20, l0, v1, i19)).
  rewrite nth_cspace_eq_nth_cspace_val; eauto.
  rewrite nth_cspace_length_imp; eauto.
  rewrite app_length. simpl. 
  rewrite H52, H53. rewrite S_add_sub_S. unfold nat_of_Z. lia.
  clear -Hsrc_lt_dest. eapply Z2Nat.inj_lt; int auto.

  rewrite <- app_assoc_reverse in H24.
  lets Hc: H24 Hb.
  destruct Hc. destruct H84. destruct H84.
  clear Ha Hb.

  rewrite H50 in H76.
  rewrite get_capability_nth_mth_cspace_length_imp in H76; eauto.
  destruct H77.
  rewrite e in H76.
  inverts H76.

  rewrite H50 in Hdest_capability.
  assert(v3 = v'72).
  {
   rewrite list_trans_1 in Hdest_capability.
   rewrite get_capability_nth_mth_cspace_length_imp in Hdest_capability; eauto.
   inverts Hdest_capability. auto.
   rewrite app_length. simpl.
   rewrite H52, H53.
   rewrite S_add_sub_S.
   clear -Hsrc_lt_dest.
   lia.
  Optimize Proof.
  Optimize Heap.
   clear -Hsrc_lt_dest.
   eapply Z2Nat.inj_lt; try (int auto).
  }
  subst v'72.

  hoare_lifts_trms_pre (Aop, cspaceid).
  hoare abscsq. 
  apply noabs_oslinv.
  eapply user_cnode_mint_absinfer_succ.
  (*需要一个success情况下的lemma*)
  eauto. eauto. eauto. eauto. eauto.
  destruct a. rewrite H76. simpl. apply Int.eq_true.
  destruct a. rewrite Int.eq_sym. apply Int.eq_false. apply H77.
  go.
  unfold AOSCSpacePrioTbl. go.
  eapply can_change_aop_ACSpaceAarrayTptr.
  unfold AOSCSpaceObjectPointer. go.
  unfold CSpaceGVars. go.
  
  eapply seq_rule.
  eapply forward_rule2.
  eapply excrit1_rule'_ISnil_ISRemp'''_lg.
  intros.
  sep lifts (5::3::6::nil)%nat in H76.
  eapply add_aemp_isr_is_prop in H76. 
  eapply add_isr_is_prop in H76. 
  unfold OldOSInvWL.
  unfold CapabilityInv.
  unfold AOSCSpaceCapParent.
  try unfold AOSTCBList;unfold_dll.
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
  instantiate(1:=LV destTask_Prio @ char_t |-> Vint32 i **
    LV srcTask_Prio @ char_t |-> Vint32 i0 **
    LV ios_cap_defs.i @ char_t |-> (V$ CNODE_NONE_FAULT) **
    LV rights @ long |-> Vint32 i2 **
    LV func_capability @ long |-> Vint32 i1 **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b0, i13) **
    LV y @ char_t |-> Vint32 i7 ** 
    A_dom_lenv ((rights, long) :: (func_capability, long)
      :: (srcTask_Prio, char_t)
          :: (destTask_Prio, char_t)
            :: (pCSpace, CSPACE ∗)
                :: (ios_cap_defs.i, char_t)
                  :: (y, char_t) :: nil)).
    sep auto; eauto.
    splits; auto. go. 
    {
      clear -Hwellform_descendents.
      eapply Capability_wellform_descendents_update_cap; auto.
    }    
    eapply taskPrioProp_update_slots_cap_remain; auto.
    eapply RLH_cspace_slots_P_update_slots_cap_remain; auto.
    rewrite H50; auto. 
    rewrite H50; auto. 
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H52, H53. rewrite S_add_sub_S.
    clear -Hsrc_lt_dest. lia.
    clear -Hsrc_lt_dest.
    eapply Z2Nat.inj_lt; try (int auto).
    apply H72.
    eapply RL_Cap_Parent_Child_remain; auto.
    eapply RLH_CapParent_update_slots_cap_remain with(cspacevl:=
    v'6 ++
      (i14, i15,
      v'8 ++
      (v'34, (i16, (i17, i18, v0))) :: v'30,
      i12, l, v, i11) :: v'35); eauto.
    rewrite H50; auto. 
    rewrite list_trans_1.
    rewrite nth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H52, H53. rewrite S_add_sub_S.
    clear -Hsrc_lt_dest. lia.
    clear -Hsrc_lt_dest.
    eapply Z2Nat.inj_lt; try (int auto).
    go. go.

    hoare forward.

  hoare_split_pure_all.
  clear - H81.
  unfold CNODE_NONE_FAULT in H81.
  unfold val_inj in H81.
  rewrite Int.eq_true in H81.
  destruct H81; tryfalse.
  destruct H81.
  sep split in H75.
  exact H75.
  sep split in H75.
  clear - H77.
  unfold CNODE_NONE_FAULT in H77.
  unfold val_inj in H77.
  rewrite Int.eq_true in H77.
  destruct H77; tryfalse.
  Unshelve. all:exact (Aemp).
Qed.
