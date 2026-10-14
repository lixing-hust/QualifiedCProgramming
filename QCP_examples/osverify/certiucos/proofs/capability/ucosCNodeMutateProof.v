Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import Lia.
Require Import ACSpace_defs.
Require Import CapSpec. 
Require Import seplog_trm_tacs.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Set Nested Proofs Allowed.
Lemma ucos_CNode_Mutate_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal ucos_CNode_Mutate
                  vl logicl ucos_CNode_MutatePre ct->
      Some r =
      BuildRetI os_internal ucos_CNode_Mutate vl logicl ucos_CNode_MutatePost ct->
      exists t d1 d2 s,
      os_internal ucos_CNode_Mutate = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
    init spec.
    simpl in H, H0, H5, H6.
    inverts H. inverts H0.
    inverts H5. inverts H6.
    rename H10 into Hc1.
    Ltac p_local_go:= 
      try unfold p_local;
      try unfold CurTid;
      try unfold OSLInv;
      try unfold LINV;
      try unfold AOSCSpacePrioTbl;
      try unfold AOSExchandler;
      try good_frm_sovler;
      try go.
    unfold AOSCSpacePrioTbl at 2. hoare_split_pure_all.
    assert(Hv'11len: length v'11 = 64%nat).
    simpljoin. auto.
    assert(Hv'12len: length v'12 = 64%nat).
    simpljoin. auto.
    assert(Harraymatch: array_type_vallist_match CSPACE ∗ v'11).
    simpljoin. auto.
    eapply backward_rule1 with (p:=
    Aie false **
    Ais nil **
    Acs v'9 **
    Aisr v'10 **
    Aier v'7 **
    <|| v'8 ||>  **
    AOSCSpacePrioTbl (v'13 ↝ {v'14}) v'11
      v'12 v'15 **
    p_local OSLInv ct init_lg **
    LV cap2 @ Cap ∗ |-> v'2 **
    LV cap1 @ Cap ∗ |-> v'1 **
    LV pCSpace2 @ CSPACE ∗ |-> v'0 **
    LV pCSpace1 @ CSPACE ∗ |-> v' **
    LV rights @ long |-> Vint32 v'6 **
    LV func_capability @ long |-> Vint32 v'5 **
    LV srcTask_Prio @ char_t |-> Vint32 v'4 **
    LV destTask_Prio @ char_t |-> Vint32 v'3 **
    A_dom_lenv
      ((rights ↝ {long})
      :: (func_capability ↝ {long})
          :: (srcTask_Prio ↝ {char_t})
            :: (destTask_Prio ↝ {char_t})
                :: (pCSpace1 ↝ {CSPACE ∗})
                  :: (pCSpace2 ↝ {CSPACE ∗})
                      :: (cap1 ↝ {Cap ∗})
                        :: (cap2 ↝ {Cap ∗})
                            :: nil)).
    intros.
    unfold AOSCSpacePrioTbl. sep auto.
    clear H.
    hoare forward.
    destruct  (Int.ltu v'5 ($ CAP_NULL_CLASS)); auto.
    destruct  (Int.ltu ($ CAP_CHANNEL_CLASS) v'5); auto.
    destruct (Int.ltu v'5 ($ CAP_NULL_CLASS));
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'5); auto.
    hoare_split_pure_all.
    hoare forward; eauto.
    sep lift 2%nat.
    eapply disj_split.
    left. sep auto. left.
    2: simpl; eauto.
    2: simpl; eauto.
    2: simpl; eauto.
    2: simpl; eauto.
    eapply func_capability_if_true_range; eauto.
    eapply disj_rule. hoare_split_pure_all. 
    eapply pfalse_rule.
    hoare_split_pure_all.
    assert(Hrange: CAP_NULL_CLASS <= Int.unsigned v'5 <= CAP_CHANNEL_CLASS).
    unfold val_inj, bool_or in H.
    destruct (Int.ltu v'5 ($ CAP_NULL_CLASS)) eqn: Hlt1;
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'5) eqn: Hlt2;
    val_help_H H; simpl in H;destruct H; tryfalse;
    try(rewrite Intlt_false_is_Zge in Hlt1);
    try(rewrite Intlt_false_is_Zge in Hlt2);
    try(rewrite Int.unsigned_repr in Hlt1);
    try(rewrite Int.unsigned_repr in Hlt2);
    try lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    clear H.
    assert(Hv'3: Int.unsigned v'3 <=? Byte.max_unsigned= true).
    change Byte.max_unsigned with 255.
    clear -H4. int auto.
    assert(Hv'4: Int.unsigned v'4 <=? Byte.max_unsigned= true).
    change Byte.max_unsigned with 255.
    clear -H3. int auto.

    hoare forward.
    rewrite Hv'3. auto.
    destruct (Int.ltu ($ 64) v'3); auto.
    rewrite Hv'3. auto.
    destruct (Int.eq v'3 ($ 64)); auto.
    destruct (Int.ltu ($ 64) v'3);
    destruct (Int.eq v'3 ($ 64)); auto.
    rewrite Hv'4. auto.
    destruct (Int.ltu ($ 64) v'4); auto.
    rewrite Hv'4. auto.
    destruct ( Int.eq v'4 ($ 64)); auto.
    destruct (Int.ltu ($ 64) v'4);
    destruct (Int.eq v'4 ($ 64)); auto.
    destruct (Int.ltu ($ 64) v'3);
    destruct (Int.eq v'3 ($ 64));
    destruct (Int.ltu ($ 64) v'4);
    destruct (Int.eq v'4 ($ 64)); auto.
    hoare_split_pure_all.
    hoare forward; eauto.
    sep lift 2%nat. eapply disj_split. left.
    sep auto. right. left.
    2: simpl; eauto.
    2: simpl; eauto.
    2: simpl; eauto.
    2: simpl; eauto.
    assert(Int.unsigned($64) = 64).
    rewrite Int.unsigned_repr. lia. rewrite max_unsigned_val. lia.

    destruct (Int.ltu ($ 64) v'3) eqn: Hlt1;
    destruct (Int.eq v'3 ($ 64)) eqn: Heq1;
    destruct (Int.ltu ($ 64) v'4) eqn: Hlt2;
    destruct (Int.eq v'4 ($ 64))eqn: Heq2; repeat(val_help_H H; simpl in H); tryfalse;
    try(rewrite Intlt_true_is_Zlt in Hlt1);
    try(rewrite Inteq_true_is_Zeq in Heq1);
    try(rewrite Intlt_true_is_Zlt in Hlt2);
    try (rewrite Inteq_true_is_Zeq in Heq2);
    try(rewrite H13 in Hlt1);
    try(rewrite H13 in Hlt2);
    try(rewrite H13 in Heq1);
    try(rewrite H13 in Heq2);
    try lia.
    eapply disj_rule. hoare_split_pure_all. eapply pfalse_rule.
    hoare_split_pure_all.
    assert(Int.unsigned v'3 < 64 /\ Int.unsigned v'4 < 64).
    assert(Int.unsigned($64) = 64).
    rewrite Int.unsigned_repr. lia. rewrite max_unsigned_val. lia.

    destruct (Int.ltu ($ 64) v'3) eqn: Hlt1;
    destruct (Int.eq v'3 ($ 64)) eqn: Heq1;
    destruct (Int.ltu ($ 64) v'4) eqn: Hlt2;
    destruct (Int.eq v'4 ($ 64))eqn: Heq2; repeat(val_help_H H; simpl in H); destruct H;tryfalse;
    try(rewrite Intlt_false_is_Zge in Hlt1);
    try(rewrite Inteq_false_is_Zneq in Heq1);
    try(rewrite Intlt_false_is_Zge in Hlt2);
    try (rewrite Inteq_false_is_Zneq in Heq2);
    try(rewrite H13 in Hlt1);
    try(rewrite H13 in Hlt2);
    try(rewrite H13 in Heq1);
    try(rewrite H13 in Heq2);
    try lia.
    simpljoin. 
    rename H0 into Hv'3range.
    rename H1 into Hv'4range.
    clear H.
    unfold CAP_NULL_CLASS in H2.
    unfold CAP_CHANNEL_CLASS in H5.
    assert(Hv'5range: 0 <= Int.unsigned v'5 <= 16) by lia.
    clear H2 H5.

    unfold AOSCSpacePrioTbl at 2.
    hoare_split_pure_all.
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply assign_rule_lvar.
    intros. splits; intros.
    sep cancel pCSpace1. eauto.
    sep auto.
    intros.
    eapply array_member_rv_g.
    unfold GAarray.
    sep normal. eexists.
    sep cancel OSCSpacePrioTbl. sep cancel Aarray.
    sep cancel A_dom_lenv. eauto.
    simpl. auto. eauto.
    sep get rv. rewrite Hv'3. auto.
    eauto. auto. lia. lia.
    rewrite Hv'11len. lia.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'11len. lia.
    eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply assign_rule_lvar.
    intros. splits; intros.
    sep cancel pCSpace2. eauto.
    sep auto.
  Optimize Proof.
  Optimize Heap.
    intros.
    eapply array_member_rv_g.
    unfold GAarray.
    sep normal. eexists.
    sep cancel OSCSpacePrioTbl. sep cancel Aarray.
    sep cancel A_dom_lenv. eauto.
    simpl. auto. eauto.
    sep get rv. rewrite Hv'4. auto.
    eauto. auto. lia. lia.
    rewrite Hv'11len. lia.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'11len. lia.
    eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.
    assert(HpCSpace2type: rule_type_val_match (Tptr CSPACE) (nth_val'
    (Z.to_nat (Int.unsigned v'4)) v'11) = true).
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'11len; lia.
    assert(HpCSpace1type: rule_type_val_match (Tptr CSPACE) (nth_val'
    (Z.to_nat (Int.unsigned v'3)) v'11) = true).
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'11len; lia.
    eapply backward_rule1 with (p:=
    Aie false **
    Ais nil **
    Acs v'9 **
    Aisr v'10 **
    Aier v'7 **
    <|| v'8 ||>  **
    AOSCSpacePrioTbl (v'13 ↝ {v'14}) v'11
      v'12 v'15 **
    p_local OSLInv ct init_lg **
    LV cap2 @ Cap ∗ |-> v'2 **
    LV cap1 @ Cap ∗ |-> v'1 **
    LV pCSpace2 @ CSPACE ∗ |-> nth_val'
    (Z.to_nat (Int.unsigned v'4)) v'11**
    LV pCSpace1 @ CSPACE ∗ |-> nth_val'
    (Z.to_nat (Int.unsigned v'3)) v'11 **
    LV rights @ long |-> Vint32 v'6 **
    LV func_capability @ long |-> Vint32 v'5 **
    LV srcTask_Prio @ char_t |-> Vint32 v'4 **
    LV destTask_Prio @ char_t |-> Vint32 v'3 **
    A_dom_lenv
      ((rights ↝ {long})
      :: (func_capability ↝ {long})
          :: (srcTask_Prio ↝ {char_t})
            :: (destTask_Prio ↝ {char_t})
                :: (pCSpace1 ↝ {CSPACE ∗})
                  :: (pCSpace2 ↝ {CSPACE ∗})
                      :: (cap1 ↝ {Cap ∗})
                        :: (cap2 ↝ {Cap ∗})
                            :: nil)).
    intros. unfold AOSCSpacePrioTbl.
    sep auto.
    clear H.
    hoare forward.
    unfold val_inj, val_eq.
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v'3)) v'11); auto.
    destruct a. auto.
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v'4)) v'11); auto.
    destruct a. auto.
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v'3)) v'11);
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v'4)) v'11); auto;
    try destruct a; auto.
    destruct a0. auto.
    hoare_split_pure_all.
    hoare forward; [idtac|simpl; eauto..].
    sep lift 2%nat. eapply disj_split.
    left. sep auto. right. right.
    clear -H HpCSpace1type HpCSpace2type.
    unfold val_inj, bool_or, val_eq in H.
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v'3)) v'11);
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v'4)) v'11); repeat(val_help_H H; simpl in H); tryfalse; auto.
    destruct a. destruct a0.
    val_help_H H. simpl in H. tryfalse.
    eapply disj_rule.
    hoare_split_pure_all. eapply pfalse_rule.
    hoare_split_pure_all.
    assert(Hnotnull1: nth_val'
    (Z.to_nat (Int.unsigned v'3))v'11 <> Vnull).
    unfold val_inj, bool_or, val_eq in H.
    destruct (nth_val'(Z.to_nat (Int.unsigned v'3))
    v'11);
    destruct (nth_val'(Z.to_nat (Int.unsigned v'4)) v'11); 
    val_help_H H; simpl in H; destruct H; tryfalse; auto.
    destruct a. tryfalse. destruct a. tryfalse.
    assert(Hnotnull2: nth_val'
    (Z.to_nat (Int.unsigned v'4))v'11 <> Vnull).
    unfold val_inj, bool_or, val_eq in H.
    destruct (nth_val'(Z.to_nat (Int.unsigned v'3))
    v'11);
    destruct (nth_val'(Z.to_nat (Int.unsigned v'4)) v'11); 
    val_help_H H; simpl in H; destruct H; tryfalse; auto.
    destruct a. tryfalse. destruct a. tryfalse.
    clear H.
    eapply backward_rule1.
    intros.
    sep lift 7%nat in H.
    eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with (idx1:=Z.to_nat(Int.unsigned v'3)) (idx2:=Z.to_nat(Int.unsigned v'4))in H; eauto.
    rewrite Hv'12len. lia.
    clear -Hc1. 
    eapply Z2Nat.inj_lt; try (int auto).

    pure intro.
    unfold ACSpace.
    destruct v'17. destruct p. destruct p. destruct p. destruct v'24.
    destruct v'18. destruct p. destruct p. destruct p. destruct v'25.
    
    unfold Acnode.
    destruct c. destruct p. destruct c0. destruct p.
    pure intro.
    rename H23 into Hi2range.
    rename H24 into Hirange.
    (*unfold two slots*)
    eapply backward_rule1.
    intros.
    sep lifts (10::18::nil)%nat in H23.
    eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'5)) in H23.
    sep lift 2%nat in H23.
    eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'5)) in H23.
    exact H23.
    unfold SLOT_NUM. lia. auto.
    auto. unfold SLOT_NUM. lia. auto. auto.
    pure intro.
    unfold ACap.
    destruct v'18. destruct c. destruct p.
    destruct v'27. destruct c. destruct p.
    hoare_lifts_trms_pre(Alvarmapsto pCSpace1, Alvarmapsto pCSpace2).
    assert(nth_val' (Z.to_nat (Int.unsigned v'3))
    (v'21 ++
     (Vptr (b ↝ {i1}) :: v'22) ++
     Vptr (b0 ↝ {i4}) :: v'23) = Vptr(b0, i4)).
    simpl. 
    rewrite list_trans_2.
    rewrite nth_val'_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H1, H9.
    rewrite S_add_sub_S.
    lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
    rewrite H23.
    assert(nth_val'
    (Z.to_nat (Int.unsigned v'4))
    (v'21 ++
     (Vptr (b ↝ {i1}) :: v'22) ++
     Vptr (b0 ↝ {i4}) :: v'23) = Vptr(b, i1)).
    simpl.
    rewrite nth_val'_length_imp; eauto.
    rewrite H26.
    clear H23 H26.

    (*cap1 ′ =ₑ&ₐ(((pCSpace1 ′ → cnode) .. slots)[func_capability ′]) .. capability;ₛ*)
    hoare_split_pure_all.
    rename H23 into Hptrv2.
    rename H26 into Hptrv1.
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply assign_rule_lvar.
    intros. split; intros.
    sep cancel cap1.
    eauto.
    sep auto.

    intros.
    eapply calculate_rv_expr_id_addr.
    3:{
      eapply expr_field_array_asrt_impl_frm.
      5:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep cancel pCSpace1.
          sep lift 46%nat in H23.
          eapply LV_to_Rv in H23; eauto.
          instantiate(2:=Z.to_nat(Int.unsigned v'5)).
          rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
          exact H23.
        }
        unfold CSPACE.
        eauto. unfold field_offset. simpl. eauto.
        simpl. unfold Cte. eauto.
      }
      unfold field_offset. simpl. rewrite Int.add_zero.
      change ($ 4 +ᵢ  $ 4) with ($8). eauto.
      instantiate(1:=2%nat). simpl. auto.
      auto.
  Optimize Proof.
  Optimize Heap.
      simpl. unfold Slot. eauto.
    }
    simpl. eauto. unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.

(*cap2 ′ =ₑ&ₐ(((pCSpace2 ′ → cnode) .. slots) [func_capability ′])
.. capability;ₛ*)
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply assign_rule_lvar.
    intros. split; intros.
    sep cancel cap2.
    eauto.
    sep auto.

    intros.
    eapply calculate_rv_expr_id_addr.
    3:{
      eapply expr_field_array_asrt_impl_frm.
      5:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep cancel pCSpace2.
          sep lift 46%nat in H23.
          eapply LV_to_Rv in H23; eauto.
          instantiate(2:=Z.to_nat(Int.unsigned v'5)).
          rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
          exact H23.
        }
        unfold CSPACE.
        eauto. unfold field_offset. simpl. eauto.
        simpl. unfold Cte. eauto.
      }
      unfold field_offset. simpl. rewrite Int.add_zero.
      change ($ 4 +ᵢ  $ 4) with ($8). eauto.
      instantiate(1:=2%nat). simpl. auto.
      auto.
      simpl. unfold Slot. eauto.
    }
    simpl. eauto. unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    simpl typelen.

    eapply seq_rule.
    eapply if_rule2'.
    intros.
    eapply bop_rv.
    eapply bop_rv.
    eapply bop_rv.

    eapply lv_mapsto_to_rv.
    2:{
        eapply local_val_struct_member_addr.
        sep lift 2%nat in H23.
        exact H23.
        unfold Cap.
        eauto.
        unfold field_offset. simpl. eauto.
        simpl. eauto.
    }
    2:{
        rewrite Int.add_zero.
        rewrite of_to_nat_unsignedv'.
        rewrite Int.repr_unsigned.
        sep lift 8%nat in H23.
        rewrite <- addition_trans.
        unfold Aptrmapsto in H23 at 1.
        exact H23.
        lia.
    }
    simpl. auto.
    destruct_s s. unfold CAP_CATEGORY_TYPE. simpl. split; eauto.
    eauto.
    unfold val_inj. unfold bop_eval.
    unfold val_eq. destruct (Int.eq i12 ($ 1)); eauto.
    simpl. eauto.
    eapply bop_rv. eapply bop_rv.
    eapply uop_rv.

    eapply lv_mapsto_to_rv.
    2:{
    eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep lift 2%nat in H23.
          exact H23.
        }
        unfold Cap. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero. eauto.
        simpl. unfold Content. eauto.
      }
      simpl. unfold Cap_Category. eauto.
    }
      simpl. eauto.
      unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    }
    2:{
      rewrite Int.add_zero in *.  simpl typelen in *.
      rewrite of_to_nat_unsignedv'.
      rewrite <- addition_trans. rewrite Int.unsigned_repr.
      rewrite Int.add_assoc.
      change ($ 4 +ᵢ  $ 4) with ($8).
      sep lift 10%nat in H23. unfold Aptrmapsto in H23 at 1.
      exact H23. clear -H9. int auto. lia.
    }
    simpl. eauto.
    eauto. 
    unfold val_inj, uop_eval. unfold negint. auto.
    simpl. eauto.
    sep lift 47%nat in H23.
    eapply LV_to_Rv in H23. eapply inline_tactics.monoasrt_mono in H23.
    exact H23. eapply inline_tactics.Rv_mono.
    auto. simpl. auto. eauto.
    unfold bop_eval, val_inj.
    unfold uop_eval. unfold negint. 
    unfold and. auto.
    simpl. eauto.
    destruct_s s. simpl. split; eauto.
    eauto.
    unfold val_inj, bop_eval, uop_eval.
    unfold negint. unfold and. unfold val_eq.
    destruct (Int.eq (Int.not i14&ᵢv'6) ($ 0)); auto.
    simpl. eauto.
    eauto.
    unfold val_inj, bop_eval, uop_eval.
    unfold negint. unfold and. unfold val_eq.
    unfold bool_and.
    destruct (Int.eq i12 ($ 1));
    destruct ( Int.eq (Int.not i14&ᵢv'6)($ 0));
    val_help; simpl; auto.
    simpl. eauto.
    eapply uop_rv. eapply bop_rv.
    {
      eapply lv_mapsto_to_rv.
      2:{
        eapply field_asrt_impl_struct_aop.
        3:{
          eapply field_asrt_impl_union_aop'.
          2:{
            eapply local_val_struct_member_addr_frm.
            4:{
              sep lift 2%nat in H23.
              exact H23.
            }
            unfold Cap. eauto.
            unfold field_offset. simpl. rewrite Int.add_zero. eauto.
            simpl. unfold Content. eauto.
          }
          simpl. unfold Cap_Category. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero. eauto.
      }
      2:{
        rewrite Int.add_zero in *.  simpl typelen in *.
        rewrite of_to_nat_unsignedv'.
        rewrite <- addition_trans. rewrite Int.unsigned_repr.
        rewrite Int.add_assoc.
        change ($ 4 +ᵢ  $ 4) with ($8).
        sep lift 10%nat in H23. unfold Aptrmapsto in H23 at 1.
        exact H23. clear -H9. int auto. lia.
      }
      simpl. auto.
    }
    sep lift 47%nat in H23.
    eapply LV_to_Rv in H23. eapply inline_tactics.monoasrt_mono in H23.
    exact H23. eapply inline_tactics.Rv_mono.
    auto. simpl. auto. eauto.
    unfold bop_eval, val_inj.
    unfold val_eq. destruct (Int.eq i14 v'6); auto.
    simpl. eauto.
    eauto. 
    unfold val_inj, uop_eval, bop_eval.
    unfold notint, val_eq.
    destruct (Int.eq i14 v'6); auto.
    simpl. eauto.
    eauto.
    unfold val_inj, uop_eval, bop_eval.
    unfold notint, val_eq.
    unfold bool_and, negint.
    unfold and.
    destruct ( Int.eq i12 ($ 1));
    destruct (Int.eq (Int.not i14&ᵢv'6));
    destruct (Int.eq i14 v'6);
    val_help; simpl; auto.
    simpl. eauto.
    hoare_split_pure_all. 
    destruct H23.
    destruct H26.

    (*cap1 ′ → cap_type =ₑ ′ CAP_CATEGORY_TYPE*)
    eapply seq_rule.
    eapply assign_rule_aop.
    2:{
      intros.
      eapply local_val_struct_member_addr.
      {
        sep lift 2%nat in H32.
        exact H32.
      }
      unfold Cap. eauto.
      unfold field_offset. simpl. eauto.
      simpl. unfold Content. eauto.
    }
    2:{
      intros.
      splits; intros.
      rewrite Int.add_zero in *. 
      simpl typelen in *.
      rewrite <- addition_trans. rewrite of_to_nat_unsignedv'.
      rewrite Int.unsigned_repr. 
      sep lift 14%nat in H32.
      exact H32.
      clear -H9. int auto.
      lia.
  Optimize Proof.
  Optimize Heap.
      intros. 
      rewrite Int.add_zero in *.
      simpl typelen in *.
      rewrite of_to_nat_unsignedv' in H32 at 1.
      rewrite <- addition_trans in H32 at 1. 
      sep cancel cap2.
      sep cancel cap1.
      sep cancel ASlots.
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      rewrite Int.unsigned_repr in H32 at 1.
      sep auto.
      clear -H9. int auto.
      lia.
    }
    2:{
      intros.
      destruct_s s. simpl.
      splits; eauto.
    }
    apply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.
    
    (*((cap1 ′ → cap_content) .. category) .. category_content =ₑ
((cap2 ′ → cap_content) .. category) .. category_content*)

eapply seq_rule.
eapply assign_rule_aop.
2:{
  intros.
  eapply field_asrt_impl_struct_aop.
  3:{
    eapply field_asrt_impl_union_aop'.
    2:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep lift 3%nat in H32.
        exact H32.
      }
      unfold Cap. eauto.
      unfold field_offset. simpl. rewrite Int.add_zero. eauto.
      simpl. unfold Content. eauto.
    }
    simpl. unfold Cap_Category. eauto.
  }
  simpl. eauto.
  unfold field_offset. simpl. eauto.
}
2:{
  intros. splits; intros.
  rewrite of_to_nat_unsignedv'.
  rewrite Int.repr_unsigned.
  rewrite Int.add_zero in *. rewrite Int.add_zero in *.
  simpl typelen in *.
  sep lift 15%nat in H32.
  rewrite <- addition_trans.
  exact H32. lia.
  simpl typelen in *.
  rewrite Int.add_zero in *.
  rewrite Int.add_zero in *.
  sep cancel cap2.
  sep cancel cap1.
  sep cancel ASlots.
  rewrite of_to_nat_unsignedv'.
  rewrite <- addition_trans.
  rewrite Int.unsigned_repr.
  rewrite <- addition_trans in H32.
  rewrite Int.unsigned_repr in H32.
  rewrite of_to_nat_unsignedv' in H32.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep auto.
  clear -H9. int auto.
  lia.
  clear -H9. int auto.
  lia.
}
2:{
  intros.
  eapply lv_mapsto_to_rv.
  2:{
    eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep lift 2%nat in H32.
          exact H32.
        }
        unfold Cap. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero. eauto.
        simpl. unfold Content. eauto.
      }
      simpl. unfold Cap_Category. eauto.
    }
    simpl. eauto.
    unfold field_offset. simpl. eauto.
  }
  2:{
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    rewrite of_to_nat_unsignedv'. 
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    sep lift 9%nat in H32.
    unfold Aptrmapsto in H32 at 1.
    exact H32.
    clear -H9. int auto.
    lia.
  }
  simpl. auto.
}
eapply eq_int. auto.
intros.
eexists. sep cancel p_local. simpl. auto.
(*((cap1 ′ → cap_content).. category).. category_right =ₑrights*)
eapply seq_rule.
eapply assign_rule_aop.
2:{
  intros.
  eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep lift 4%nat in H32.
          exact H32.
        }
        unfold Cap. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero. eauto.
        simpl. unfold Content. eauto.
      }
      simpl. unfold Cap_Category. eauto.
    }
    simpl. eauto.
    unfold field_offset. simpl. eauto.
}
2:{
  intros. splits; intros.
  rewrite Int.add_zero in *. rewrite Int.add_zero in *.
  rewrite of_to_nat_unsignedv'.
  rewrite <- addition_trans. 
  rewrite Int.unsigned_repr. 
  rewrite Int.add_assoc.
  change (($ 4 +ᵢ  $ 4)) with ($8).
  sep lift 16%nat in H32.
  exact H32.
  clear -H9. int auto. lia.
  simpl typelen in *.
  rewrite Int.add_zero in *.
  rewrite Int.add_zero in *.
  sep cancel cap2.
  sep cancel cap1.
  sep cancel ASlots.
  rewrite of_to_nat_unsignedv'.
  rewrite <- addition_trans.
  rewrite Int.unsigned_repr.
  rewrite <- addition_trans in H32.
  rewrite Int.unsigned_repr in H32.
  rewrite of_to_nat_unsignedv' in H32.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  rewrite Int.add_assoc in H32 at 1.
  change (($ 4 +ᵢ  $ 4)) with ($8) in H32.
  sep cancel 2%nat 1%nat.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  clear -H9. int auto.
  lia.
  clear -H9. int auto.
  lia.
}
2:{
  intros.
  sep lift 46%nat in H32.
  eapply LV_to_Rv in H32; eauto.
  eapply inline_tactics.monoasrt_mono in H32.
  exact H32.
  eapply inline_tactics.Rv_mono.
}
eapply eq_int. auto.
intros. eexists. sep cancel p_local. simpl. auto.

(*((cap2 ′ → cap_content) .. category)
.. category_right &= ∼ rights ′*)
eapply assign_rule_aop.
2:{
  intros.
  eapply field_asrt_impl_struct_aop.
  3:{
    eapply field_asrt_impl_union_aop'.
    2:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep lift 4%nat in H32.
        exact H32.
      }
      unfold Cap. eauto.
      unfold field_offset. simpl. rewrite Int.add_zero. eauto.
      simpl. unfold Content. eauto.
    }
    simpl. unfold Cap_Category. eauto.
  }
  simpl. eauto.
  unfold field_offset. simpl. rewrite Int.add_zero.
  eauto.
  }
  2:{
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    intros. splits; intros.
    rewrite of_to_nat_unsignedv'.
    sep lift 12%nat in H32.
    rewrite <- addition_trans.
    rewrite Int.add_assoc.
    change ($ 4 +ᵢ  $ 4) with ($8).
    rewrite Int.repr_unsigned.
    exact H32.
    lia.
    simpl typelen in *.
    sep cancel cap2.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H32.
    rewrite Int.unsigned_repr in H32.
    rewrite of_to_nat_unsignedv' in H32.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    rewrite Int.add_assoc in H32 at 1.
    change ($ 4 +ᵢ  $ 4) with ($8) in H32.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep auto.
    clear -H9. int auto.
    lia. 
    clear -H9. int auto.
    lia.
  }
  2:{
    intros.
    eapply bop_rv.
    eapply lv_mapsto_to_rv.
    2:{
      eapply field_asrt_impl_struct_aop.
      3:{
        eapply field_asrt_impl_union_aop'.
        2:{
          eapply local_val_struct_member_addr_frm.
          4:{
            sep lift 4%nat in H32.
            exact H32.
          }
          unfold Cap. eauto.
          unfold field_offset. simpl. rewrite Int.add_zero. eauto.
          simpl. unfold Content. eauto.
        }
        simpl. unfold Cap_Category. eauto.
      }
      simpl. eauto.
      unfold field_offset. simpl. rewrite Int.add_zero.
      eauto.
    }
    2:{
      rewrite Int.add_zero.
      rewrite Int.add_assoc.
      change ($ 4 +ᵢ  $ 4) with ($8).
      sep lift 12%nat in H32.
      unfold Aptrmapsto in H32 at 1.
      rewrite <- addition_trans.
      rewrite of_to_nat_unsignedv'.
      rewrite Int.repr_unsigned.
      exact H32.
      lia.
    }
    simpl. auto.
    eapply uop_rv.
    sep lift 46%nat in H32.
    eapply LV_to_Rv in H32.
    eapply inline_tactics.monoasrt_mono in H32.
    exact H32.
    eapply inline_tactics.Rv_mono.
    auto.
    simpl. auto.
    eauto. unfold val_inj, uop_eval.
    unfold negint. eauto.
    simpl. eauto.
    eauto.
    unfold val_inj, bop_eval, uop_eval.
    unfold and, negint.
    auto.
    simpl. eauto.
  }
  eapply eq_int. auto.
  intros. eexists. sep cancel p_local.
  simpl. auto.

  hoare_split_pure_all.
  instantiate(1:=Afalse).
  eapply rete_rule'.
  intros. 
  destruct_s s. unfold CNODE_MUTATE_FAILURE.
  simpl. split; eauto.
  intros.
  unfold ucos_CNode_MutatePost'.
  sep lifts (8::9::10::11::nil)%nat in H26.
  eapply fold_Cap in H26.
  sep lifts (7::8::1::9::nil)%nat in H26.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'24++(v'26,(i12,((i13, i14), v2)))::v'25))
  in H26; eauto.
  2: auto.
  sep lifts (9::10::11::12::nil)%nat in H26.
  eapply fold_Cap in H26.
  sep lifts (8::9::1::10::nil)%nat in H26.
  eapply ASlots_fold_any_idx_frm in H26; eauto.
  sep lifts (11::9::12::nil)%nat in H26.
  eapply Aarray'_fold_any_idx_frm in H26; eauto.
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    assert(Z.to_nat (Int.unsigned v'3) < 64)%nat. lia. 
    apply Z.le_trans with(m:= 64*4). simpl typelen.
    rewrite Nat2Z.inj_mul.
    lia. 
    rewrite max_unsigned_val. lia. 
  }
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  sep lifts (1::10::11::nil)%nat in H26.
  eapply Aarray'_fold_any_idx_frm in H26; eauto.
  2: lia.
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  2:{
    split; auto. 
    rewrite app_length.
    simpl. rewrite H1, H9.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2: auto.
  sep lifts (11::12::3::nil)%nat in H26.
  eapply fold_Acnode in H26; eauto.
  sep lifts (16::17::3::nil)%nat in H26.
  eapply fold_Acnode in H26; eauto.

  sep lifts (2::11::12::13::14::nil)%nat in H26.
  eapply fold_ACSpace in H26; eauto.
  sep lifts (2::12::13::14::15::nil)%nat in H26.
  eapply fold_ACSpace in H26; eauto.
  sep lifts (10::2::11::nil)%nat in H26.

  eapply ACSpaceAarray_fold_any_idx_frm in H26; eauto.
  2: lia. 
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl. 
    rewrite H2, H5.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (1::2::10::nil)%nat in H26.
  eapply ACSpaceAarray_fold_any_idx_frm in H26; eauto.
  2: lia. 
  2: lia.
  2:{
    rewrite app_length.
    simpl.
    rewrite H2, H5. 
    rewrite S_add_sub_S.
    lia. 
  Optimize Proof.
  Optimize Heap.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl.
    rewrite H1, H9.
    rewrite S_add_sub_S.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lift 2%nat. 
  unfold AOSCSpacePrioTbl. 
  sep auto.
  sep lift 4%nat. 
  eapply disj_split.
  right.
  sep lift 4%nat. 
  eapply disj_split. left.
  unfold AOSCSpacePrioTbl. 
  sep split.
  sep cancel OSCSpacePrioTbl. 
  unfold Aarray. 
  assert((v'21 ++
  Vptr (b ↝ {i1}) :: v'22) ++
  Vptr (b0 ↝ {i4}) :: v'23 = 
  v'21 ++
  (Vptr (b ↝ {i1}) :: v'22) ++
  Vptr (b0 ↝ {i4}) :: v'23).
  rewrite app_assoc_reverse. auto.
  rewrite H34 in H26. clear H34.
  sep cancel Aarray'. sep auto.
  auto.
  rewrite list_trans_1.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite app_length. simpl.
  rewrite H2, H5.
  rewrite S_add_sub_S.
  clear -Hc1. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt;(int auto).
  rewrite list_trans.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  splits; auto.
  auto. pauto.
  pauto.
  Require Import ucosCNodeMintPure.
  eapply three_bool_and_false in H23.
  auto.
  splits; try (rewrite app_length); try (rewrite app_length); simpl.
  rewrite H1, H9, H10.
  rewrite S_add_sub_S. 
  rewrite S_add_sub_S_add.
  lia.
  
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  lia.
  rewrite H2, H5, H6.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S_add.
  lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  lia.
  auto.
  rewrite app_assoc_reverse.
  simpl. auto.
  clear -H12. unfold SLOT_NUM. lia.
  auto.
  clear -H12. unfold SLOT_NUM. lia.
  auto.
  eapply disj_rule.
  hoare_split_pure_all.
  destruct H23. destruct H26.

  (*(((pCSpace2 ′ → cnode) .. slots)
 [func_capability ′]) .. slot_type =ₑ
′ SLOT_NULL_CAP*)
  eapply seq_rule.
  eapply assign_rule_aop.
  2:{
    rewrite Int.add_zero.
    intros.
    eapply field_asrt_impl_struct_aop.
    3:{
       eapply expr_field_array_asrt_impl_frm.
       5:{
          eapply local_val_struct_member_addr_frm.
          4:{
            sep cancel pCSpace2.
            sep lift 46%nat in H32.
            eapply LV_to_Rv in H32. 
            instantiate(2:=(Z.to_nat(Int.unsigned v'5))).
            rewrite of_to_nat_unsignedv'.
            rewrite Int.repr_unsigned.
            exact H32.
            auto.
            simpl. auto.
          }
          unfold CSPACE. eauto.
          unfold field_offset. simpl. eauto.
          simpl. unfold Cte. eauto.
       }
       unfold field_offset. simpl. rewrite Int.add_zero.
       change ($ 4 +ᵢ  $ 4) with ($8). eauto.
       instantiate(1:=2%nat). simpl. auto.
       auto. simpl. unfold Slot. eauto.
    }
    simpl. eauto.
    unfold field_offset. simpl. eauto.
  }
  2:{
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    unfold val_inj, bop_eval. unfold and, uop_eval.
    unfold negint.
    simpl typelen.
    intros.
    split; intros.
    sep lift 10%nat in H32.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned.
    exact H32.
    lia.
    sep cancel cap2.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H32.
    rewrite Int.unsigned_repr in H32.
    rewrite of_to_nat_unsignedv' in H32.
    sep auto.
    clear -H9. int auto.
    lia.
    clear -H9. int auto.
    lia.
  }
  2:{
    intros.
    destruct_s s. unfold SLOT_NULL_CAP.
    simpl. split; eauto.
  }
  eapply eq_int. auto.
  rewrite Int.add_zero.
  intros.
  eexists. sep cancel p_local. simpl. auto.
  (* RETURN 〈 char_t 〉 ′ CNODE_NONE_FAULT*)
  eapply rete_rule'.
  intros.
  destruct_s s. unfold CNODE_NONE_FAULT.
  simpl. split; eauto.
  rewrite Int.add_zero.
  rewrite Int.add_zero.
  simpl typelen.
  intros.
  unfold ucos_CNode_MutatePost'.
  sep lifts (12::13::3::14::nil)%nat in H32.
  sep lift 3%nat in H32.
  rewrite Int.add_assoc in H32 at 1.
  rewrite <- addition_trans in H32 at 1.
  change ($ 4 +ᵢ  $ 4) with ($8) in H32.
  rewrite of_to_nat_unsignedv' in H32.
  rewrite Int.repr_unsigned in H32.
  sep lifts (2::3::1::4::nil)%nat in H32.
  eapply fold_Cap in H32.
  sep lifts (11::3::1::12::nil)%nat in H32.
  rewrite <- addition_trans in H32.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'24++($ 0,(i12,((i13, i14&ᵢInt.not v'6), v2)))::v'25))
  in H32; eauto.
  2: auto.
  sep lifts (5::4::3::12::nil)%nat in H32.
  sep lift 3%nat in H32.
  rewrite Int.add_assoc in H32 at 1.
  change ($ 4 +ᵢ  $ 4) with ($8) in H32.
  sep lifts (2::3::1::4::nil)%nat in H32.
  eapply fold_Cap in H32.
  sep lifts (8::9::1::10::nil)%nat in H32.
  eapply ASlots_fold_any_idx_frm with(slotsvl :=(v'11++(v'17,($ CAP_CATEGORY_TYPE,((i13, v'6), v1)))::v'12))
  in H32 ; eauto.
  sep lifts (11::9::12::nil)%nat in H32.
  eapply Aarray'_fold_any_idx_frm in H32; eauto.
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    assert(Z.to_nat (Int.unsigned v'3) < 64)%nat. lia. 
    apply Z.le_trans with(m:= 64*4). simpl typelen.
    rewrite Nat2Z.inj_mul.
    lia. 
  Optimize Proof.
  Optimize Heap.
    rewrite max_unsigned_val. lia. 
  }
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  sep lifts (1::10::11::nil)%nat in H32.
  eapply Aarray'_fold_any_idx_frm in H32; eauto.
  2: lia.
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  2:{
    split; auto. 
    rewrite app_length.
    simpl. rewrite H1, H9.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2: auto.
  sep lifts (11::12::3::nil)%nat in H32.
  eapply fold_Acnode in H32; eauto.
  sep lifts (16::17::3::nil)%nat in H32.
  eapply fold_Acnode in H32; eauto.

  sep lifts (2::11::12::13::14::nil)%nat in H32.
  eapply fold_ACSpace in H32; eauto.
  sep lifts (2::12::13::14::15::nil)%nat in H32.
  eapply fold_ACSpace in H32; eauto.
  sep lifts (10::2::11::nil)%nat in H32.

  eapply ACSpaceAarray_fold_any_idx_frm in H32; eauto.
  2: lia. 
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl. 
    rewrite H2, H5.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (1::2::10::nil)%nat in H32.
  eapply ACSpaceAarray_fold_any_idx_frm with (cspacevl:=
  (v'16 ++
  (i5, i6,
  v'24 ++
  ($ 0, (i12, (i13, i14&ᵢInt.not v'6, v2)))
  :: v'25, i0, l, v, i) :: v'19) ++
  (i7, i8,
  v'11 ++
  (v'17,
  ($ CAP_CATEGORY_TYPE, (i13, v'6, v1)))
  :: v'12, i3, l0, v0, i2) :: v'20) in H32; eauto.
  2: lia. 
  2: lia.
  2:{
    rewrite app_length.
    simpl. rewrite app_length.
    simpl.
    rewrite H2, H5, H6. 
    rewrite S_add_sub_S.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl.
    rewrite H2, H5.
    rewrite S_add_sub_S.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lift 2%nat. 
  unfold AOSCSpacePrioTbl. 
  sep auto.
  sep lift 4%nat. 
  eapply disj_split.
  right.
  sep lift 4%nat. 
  eapply disj_split. right.
  sep split.
  sep cancel OSCSpacePrioTbl. 
  unfold Aarray. 
  assert((v'21 ++
  Vptr (b ↝ {i1}) :: v'22) ++
  Vptr (b0 ↝ {i4}) :: v'23 = 
  v'21 ++
  (Vptr (b ↝ {i1}) :: v'22) ++
  Vptr (b0 ↝ {i4}) :: v'23).
  rewrite app_assoc_reverse. auto.
  rewrite H36 in H32.
  clear H36.
  sep cancel Aarray'. sep auto.
  auto.
  rewrite list_trans_1.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite app_length. simpl.
  rewrite H2, H5. rewrite S_add_sub_S.
  clear -Hc1. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; (int auto).
  rewrite list_trans.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  splits; auto.
  pauto.
  {
    unfold update_nth_cspace_slots_cap.
    simpl.
    rewrite list_trans_2.
    rewrite nth_cspace_length_imp.
    rewrite nth_slots_length_imp.
    rewrite update_nth_list_length_imp.
    rewrite update_nth_list_length_imp.
    rewrite app_assoc_reverse.
    simpl.
    eauto. auto. 
    rewrite app_length. simpl.
    rewrite H2, H5. rewrite S_add_sub_S.
    clear -Hc1. lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
    auto.
    rewrite app_length. simpl.
    rewrite H2, H5. rewrite S_add_sub_S.
    clear -Hc1. lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  {
    unfold update_nth_cspace_slots_cap.
    simpl.
    
    rewrite nth_cspace_length_imp.
    rewrite nth_slots_length_imp.
    rewrite update_nth_list_length_imp.
    rewrite update_nth_list_length_imp.
    simpl. eauto. auto. auto. auto. auto.
    
  }
  {
    unfold update_nth_cspace_slots_type.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_list_length_imp; eauto.
    rewrite app_assoc_reverse.
    simpl. eauto.
  }
  eapply three_and_true; auto.
  splits; try (rewrite app_length); try (rewrite app_length); simpl.
  rewrite H1, H9, H10.
  rewrite S_add_sub_S. 
  rewrite S_add_sub_S_add.
  lia.
 
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  lia.
  rewrite H2, H5, H6.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S.
  lia. lia. 
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  auto. 
  rewrite app_length.
  simpl. rewrite H1, H9. rewrite S_add_sub_S.
  lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  clear -H16.
  rewrite app_length in *. simpl in *.
  auto.
  Optimize Proof.
  Optimize Heap.
  clear -H.
  rewrite app_length in *. simpl in *.
  auto.
  unfold SLOT_NUM. lia.
  clear -H16.
  rewrite app_length in *. simpl in *.
  auto.
  auto.
  unfold SLOT_NUM. lia.
  clear -H.
  rewrite app_length in *. simpl in *.
  auto.
  lia. auto. lia.
  hoare_split_pure_all.
  eapply pfalse_rule.
  Unshelve. all: auto.
Qed.


