Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import ucosCNodeMintPure.
Require Import Lia.
Require Import ACSpace_defs.
Require Import seplog_trm_tacs.
Require Import CapSpec.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Set Nested Proofs Allowed.

Lemma ucos_CNode_Mint_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal ucos_CNode_Mint
                  vl logicl ucos_CNode_MintPre ct->
      Some r =
      BuildRetI os_internal ucos_CNode_Mint vl logicl ucos_CNode_MintPost ct->
      exists t d1 d2 s,
      os_internal ucos_CNode_Mint = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
    init spec.
    unfold nth_val in H, H0, H5, H6.
    inverts H.
    inverts H0.
    inverts H5.
    inverts H6.
    hoare lifts (6::5::1::2::3::nil)%nat pre.
    unfold AOSCSpacePrioTbl at 2. hoare_split_pure_all.
    assert(Htypematch: array_type_vallist_match 
    CSPACE ∗ v'13).  simpljoin. auto.
    assert(Hv'13len: length v'13 = 64%nat). simpljoin. auto.
    assert(Hv'14len: length v'14 = 64%nat). simpljoin. auto.
    eapply backward_rule1 with (p:=<|| v'8 ||>  **
    Aier v'7 **
    Aie false **
    Ais nil **
    Acs v'11 **
    Aisr v'12 **
    AOSCSpacePrioTbl (v'9 ↝ {v'10}) v'13 v'14 v'15 **
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
                         :: (cap2 ↝ {Cap ∗}) :: nil)).
    intros. unfold AOSCSpacePrioTbl. sep auto.
    hoare forward.
    destruct (Int.ltu v'5 ($ CAP_NULL_CLASS)); auto.
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'5); auto.
    destruct (Int.ltu v'5 ($ CAP_NULL_CLASS)); 
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'5); auto.
    hoare_split_pure_all.
    hoare forward; [idtac | simpl; eauto..].
    sep lift 2%nat. eapply disj_split.
    left.
    sep auto.
    left.
    clear -H0.
    destruct (Int.ltu v'5 ($ CAP_NULL_CLASS)) eqn: Hlt1; 
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'5) eqn: Hlt2; val_help_H H0; simpl in H0; tryfalse;
    try(eapply Intlt_true_is_Zlt in Hlt1);
    try(eapply Intlt_true_is_Zlt in Hlt2);
    try(rewrite Int.unsigned_repr in Hlt1);
    try(rewrite Int.unsigned_repr in Hlt2);
    try lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    eapply disj_rule. hoare_split_pure_all. eapply pfalse_rule.
    hoare_split_pure_all.
    assert(Hv'5range: CAP_NULL_CLASS <= Int.unsigned v'5 <= CAP_CHANNEL_CLASS).
    destruct (Int.ltu v'5 ($ CAP_NULL_CLASS)) eqn: Hlt1; 
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'5) eqn: Hlt2;
    val_help_H H0; simpl in H0; destruct H0; tryfalse.
    eapply Intlt_false_is_Zge in Hlt1, Hlt2.
    rewrite Int.unsigned_repr in Hlt1, Hlt2.
    lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
    clear H0.
    assert(Hv'3: Int.unsigned v'3 <=? Byte.max_unsigned = true).
    clear -H4. 
    change Byte.max_unsigned with 255.
    int auto.
    assert(Hv'4: Int.unsigned v'4 <=? Byte.max_unsigned = true).
    clear -H3. 
    change Byte.max_unsigned with 255.
    int auto.

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
    destruct (Int.eq v'4 ($ 64)); auto.
    destruct (Int.ltu ($ 64) v'4);
    destruct (Int.eq v'4 ($ 64)); auto.
    destruct (Int.eq v'3 ($ 64)); 
    destruct (Int.ltu ($ 64) v'3);
    destruct (Int.ltu ($ 64) v'4);
    destruct (Int.eq v'4 ($ 64)); auto.
    hoare_split_pure_all.
    hoare forward; [idtac|simpl; eauto..].
    sep lift 2%nat. eapply disj_split. left.
    sep auto.
    right. left.
    clear -H0.
    destruct (Int.eq v'3 ($ 64)) eqn: Hv'3eq; 
    destruct (Int.ltu ($ 64) v'3) eqn: Hv'3lt;
    destruct (Int.ltu ($ 64) v'4) eqn: Hv'4lt;
    destruct (Int.eq v'4 ($ 64)) eqn: Hv'4eq; repeat(val_help_H H0; simpl in H0); tryfalse;
    try (eapply Intlt_true_is_Zlt in Hv'3lt);
    try (eapply Intlt_true_is_Zlt in Hv'4lt);
    try (eapply Inteq_true_is_Zeq in Hv'3eq);
    try (eapply Inteq_true_is_Zeq in Hv'4eq);
    try(rewrite Int.unsigned_repr in Hv'3lt);
    try(rewrite Int.unsigned_repr in Hv'4lt);
    try(rewrite Int.unsigned_repr in Hv'3eq);
    try(rewrite Int.unsigned_repr in Hv'4eq);
    try lia.
    all: try(rewrite max_unsigned_val; lia).
    eapply disj_rule. hoare_split_pure_all. eapply pfalse_rule.
    hoare_split_pure_all.
    assert(HvalidPrio: Int.unsigned v'3 < 64 /\ Int.unsigned v'4 < 64).
    destruct (Int.eq v'3 ($ 64)) eqn: Hv'3eq; 
    destruct (Int.ltu ($ 64) v'3) eqn: Hv'3lt;
    destruct (Int.ltu ($ 64) v'4) eqn: Hv'4lt;
    destruct (Int.eq v'4 ($ 64)) eqn: Hv'4eq; repeat(val_help_H H0; simpl in H0); destruct H0; tryfalse.
    eapply Intlt_false_is_Zge in Hv'3lt, Hv'4lt.
    eapply Inteq_false_is_Zneq in Hv'3eq, Hv'4eq.
    rewrite Int.unsigned_repr in Hv'3lt, Hv'3eq, Hv'4lt, Hv'4eq.
    lia.
    rewrite max_unsigned_val. lia.
    rewrite max_unsigned_val. lia.
    rewrite max_unsigned_val. lia.
    rewrite max_unsigned_val. lia.
    unfold AOSCSpacePrioTbl at 2.
    
    eapply seq_rule.
    eapply assign_rule_lvar.
    intros. splits; intros.
    sep cancel pCSpace1. exact H1.
    sep auto.
    intros.
    eapply array_member_rv_g.
    unfold GAarray.
    sep normal. sep eexists. sep cancel OSCSpacePrioTbl.
    sep cancel Aarray. sep cancel A_dom_lenv. eauto.
    simpl. auto. eauto.
    sep get rv. rewrite Hv'3. auto.
    eauto. auto. lia. lia.  rewrite Hv'13len. lia.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'13len. lia. eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.

    eapply seq_rule.
    eapply assign_rule_lvar.
    intros. splits; intros.
    sep cancel pCSpace2. exact H1.
    sep auto.
    intros.
    eapply array_member_rv_g.
    unfold GAarray.
    sep normal. sep eexists. sep cancel OSCSpacePrioTbl.
    sep cancel Aarray. sep cancel A_dom_lenv. eauto.
    simpl. auto. eauto.
    sep get rv. rewrite Hv'4. auto.
    eauto. auto. lia. lia.  rewrite Hv'13len. lia.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'13len. lia. eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.
    assert(HpCSpace1type : rule_type_val_match (Tptr CSPACE)(nth_val'
    (Z.to_nat (Int.unsigned v'3))
    v'13)  = true).
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'13len. lia.
    assert(HpCSpace2type : rule_type_val_match (Tptr CSPACE)(nth_val'
    (Z.to_nat (Int.unsigned v'4))
    v'13)  = true).
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'13len. lia.
    
    hoare forward.
    clear -HpCSpace1type.
    unfold rule_type_val_match in HpCSpace1type.
    destruct (nth_val'(Z.to_nat(Int.unsigned v'3)) v'13); tryfalse; auto; destruct a; auto.
    clear -HpCSpace2type.
    unfold rule_type_val_match in HpCSpace2type.
    destruct (nth_val'(Z.to_nat(Int.unsigned v'4)) v'13); tryfalse; auto; destruct a; auto.
    unfold rule_type_val_match in HpCSpace1type, HpCSpace2type.
    destruct (nth_val'(Z.to_nat(Int.unsigned v'3)) v'13);
    destruct (nth_val'(Z.to_nat(Int.unsigned v'4)) v'13);
    tryfalse; auto; destruct a; auto; destruct a0; auto.
    hoare forward; [idtac|simpl; eauto..].
    sep lift 2%nat. 
    eapply disj_split. left.
    unfold AOSCSpacePrioTbl. sep auto.
    right. right.
    unfold rule_type_val_match in HpCSpace1type, HpCSpace2type.
    destruct (nth_val'(Z.to_nat(Int.unsigned v'3)) v'13);
    destruct (nth_val'(Z.to_nat(Int.unsigned v'4)) v'13);
    tryfalse; auto; destruct a; auto; destruct a0; auto.
    unfold val_inj,bool_or, val_eq in H5.
    val_help_H H5. simpl in H5. tryfalse.
    eapply disj_rule. hoare_split_pure_all. eapply pfalse_rule.
    hoare_split_pure_all.
    assert(Hnotnull1: nth_val'
    (Z.to_nat (Int.unsigned v'3))v'13 <> Vnull).
    unfold val_inj, bool_or, val_eq in H2.
    destruct (nth_val'(Z.to_nat (Int.unsigned v'3))
    v'13);
    destruct (nth_val'(Z.to_nat (Int.unsigned v'4)) v'13); 
    val_help_H H2; simpl in H2; destruct H2; tryfalse; auto.
    destruct a. tryfalse. destruct a. tryfalse.
    assert(Hnotnull2: nth_val'
    (Z.to_nat (Int.unsigned v'4))v'13 <> Vnull).
    unfold val_inj, bool_or, val_eq in H2.
    destruct (nth_val'(Z.to_nat (Int.unsigned v'3))
    v'13);
    destruct (nth_val'(Z.to_nat (Int.unsigned v'4)) v'13); 
    val_help_H H2; simpl in H2; destruct H2; tryfalse; auto.
    destruct a. tryfalse. destruct a. tryfalse.
    eapply backward_rule1 with (p:=<|| v'8 ||>  **
    Aier v'7 **
    Aie false **
    Ais nil **
    Acs v'11 **
    Aisr v'12 **
    AOSCSpacePrioTbl (v'9 ↝ {v'10}) v'13 v'14 v'15 **
    p_local OSLInv ct init_lg **
    LV cap2 @ Cap ∗ |-> v'2 **
    LV cap1 @ Cap ∗ |-> v'1 **
    LV pCSpace2 @ CSPACE ∗ |-> nth_val'
    (Z.to_nat(Int.unsigned v'4))v'13  **
    LV pCSpace1 @ CSPACE ∗ |-> nth_val'
    (Z.to_nat(Int.unsigned v'3))v'13 **
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
                         :: (cap2 ↝ {Cap ∗}) :: nil)).
    intros.
    unfold AOSCSpacePrioTbl. sep auto.
    clear H1 H2 H0 H.
    (*由于要进行数组的拆分得到元素的位置，所以需要进行分类讨论
    destTask_Prio 和 srcTask_Prio的大小*)
    assert(Hc: (Int.unsigned v'3 > Int.unsigned v'4) \/ (Int.unsigned v'3 <  Int.unsigned v'4) \/ (Int.unsigned v'3 =  Int.unsigned v'4)).
    lia.
  Optimize Proof.
  Optimize Heap.
    destruct Hc as [Hc1 | [Hc2 | Hc3] ].

    (*第一种情况，当srcTaskPrio位于destTask_Prio的左边时*)
    eapply backward_rule1.
    intros.
    sep lift 7%nat in H.
    eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with (idx1:=Z.to_nat(Int.unsigned v'3)) (idx2:=Z.to_nat(Int.unsigned v'4))in H; eauto.
    unfold AOSCSpacePrioTbl in H. sep split in H.
    destruct H0. rewrite Hv'14len. lia.
    clear -Hc1. 
    eapply Z2Nat.inj_lt; try (int auto).
    

    pure intro.
    unfold ACSpace.
    destruct v'17. destruct p. destruct p. destruct p. destruct v'24.
    destruct v'18. destruct p. destruct p. destruct p. destruct v'25.
    unfold Acnode.
    destruct c. destruct p. destruct c0. destruct p.
    pure intro.
    rename H25 into Hi2range.
    rename H26 into Hirange.
    (*unfold two slots*)
    eapply backward_rule1.
    intros.
    sep lifts (10::18::nil)%nat in H25.
    eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'5)) in H25.
    sep lift 2%nat in H25.
    eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'5)) in H25.
    exact H25.
    clear -H15. unfold CAP_CHANNEL_CLASS in H15.
    unfold SLOT_NUM. lia. auto.
    auto. 
    clear -H15. unfold CAP_CHANNEL_CLASS in H15.
    unfold SLOT_NUM. lia. auto.
    auto. 
    pure intro.
    unfold ACap.
    destruct v'18. destruct c. destruct p.
    destruct v'27. destruct c. destruct p.
    hoare_lifts_trms_pre (Alvarmapsto pCSpace1, Alvarmapsto pCSpace2).
    hoare remember (1::2::nil)%nat pre.
    assert(nth_val' (Z.to_nat (Int.unsigned v'3))
    (v'21 ++
     (Vptr (b ↝ {i1}) :: v'22) ++
     Vptr (b0 ↝ {i4}) :: v'23) = Vptr(b0, i4)).
    simpl. rewrite list_trans_2. rewrite nth_val'_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H1, H10. rewrite S_add_sub_S.
    clear -Hc1. lia.
    clear -Hc1. 
    eapply Z2Nat.inj_lt; try (int auto).
    rewrite H28.
    assert(nth_val' (Z.to_nat (Int.unsigned v'4))
    (v'21 ++
     (Vptr (b ↝ {i1}) :: v'22) ++
     Vptr (b0 ↝ {i4}) :: v'23) = Vptr(b, i1)).
    simpl. rewrite nth_val'_length_imp; eauto.
    rewrite H33.
    clear H28 H33.
    subst H25.
    
    (*cap1 ′ =ₑ&ₐ(((pCSpace1 ′ → cnode) .. slots)[func_capability ′]) .. capability;ₛ*)
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply assign_rule_lvar.
    intros. split; intros.
    sep cancel cap1.
    exact H25.
    sep auto.

    intros.
    eapply calculate_rv_expr_id_addr.
    3:{
      eapply expr_field_array_asrt_impl_frm.
      5:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep cancel pCSpace1.
          sep lift 48%nat in H25.
          eapply LV_to_Rv in H25; eauto.
          instantiate(2:=Z.to_nat(Int.unsigned v'5)).
          rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
          exact H25.
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

(*cap2 ′ =ₑ&ₐ(((pCSpace2 ′ → cnode) .. slots) [func_capability ′])
.. capability;ₛ*)
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply assign_rule_lvar.
    intros. split; intros.
    sep cancel cap2. 
    exact H25.
    sep auto.

    intros.
    eapply calculate_rv_expr_id_addr.
    3:{
      eapply expr_field_array_asrt_impl_frm.
      5:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep cancel pCSpace2.
          sep lift 48%nat in H25.
          eapply LV_to_Rv in H25; eauto.
          instantiate(2:=Z.to_nat(Int.unsigned v'5)).
          rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
          exact H25.
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
    pure intro.
    rename H25 into Hisptrv2.
    rename H28 into Hisptrv1.
    (*IF(cap2′→cap_type==ₑ′CAP_CATEGORY_TYPE&&ₑ((∼cap2′→cap_content..category..category_right)&ₑrights′)==ₑ′0&&ₑcap2′→cap_content..category..category_right !=ₑ rights′)*)
    eapply seq_rule.
    eapply if_rule2'.
    intros.
    eapply bop_rv. eapply bop_rv. eapply bop_rv.
    {
      simpl typelen in H25.
      rewrite Int.add_zero in *.
      eapply lv_mapsto_to_rv.
      2:{
        eapply local_val_struct_member_addr.
        sep lift 2%nat in H25.
        exact H25. unfold Cap. eauto.
        unfold field_offset. simpl. unfold Int.zero. eauto.
        simpl. eauto.
      }
      2:{
        rewrite Int.add_zero in *.
        sep lift 8%nat in H25.
        unfold Aptrmapsto in H25 at 1.
        rewrite of_to_nat_unsignedv'. rewrite <- addition_trans.
        rewrite Int.unsigned_repr. 
        exact H25.
        clear -H9.
        rewrite max_unsigned_val. int auto.
        lia.
      }
      simpl. auto.
    }
    destruct_s s. simpl. splits; eauto.
    eauto. unfold bop_eval. unfold val_inj. 
    unfold val_eq. destruct (Int.eq i12 ($ CAP_CATEGORY_TYPE)); eauto.
    simpl. eauto.

    eapply bop_rv. eapply bop_rv.
    eapply uop_rv.  
    {
      eapply lv_mapsto_to_rv.
      2:{
        eapply field_asrt_impl_struct_aop.
        3:{
          eapply field_asrt_impl_union_aop'.
          2:{
            eapply local_val_struct_member_addr_frm.
            4:{
              rewrite Int.add_zero in H25. 
              sep lift 2%nat in H25.
              exact H25.
            }
            unfold Cap. eauto.
            unfold field_offset. simpl. rewrite Int.add_zero. eauto.
            simpl. unfold Content. eauto.
          }
          simpl. unfold Cap_Category. eauto.
        }
        simpl. eauto. unfold field_offset. simpl. rewrite Int.add_zero. eauto.
      }
      2:{
        simpl typelen in *.
        rewrite Int.add_zero.
        rewrite of_to_nat_unsignedv'.
        rewrite Int.add_assoc.
        change($ 4 +ᵢ  $ 4) with ($8).
        rewrite <- addition_trans.
        rewrite Int.unsigned_repr.
        sep lift 10%nat in H25.
        unfold Aptrmapsto in H25 at 1.
        exact H25.  clear -H9. int auto.
        lia.
  Optimize Proof.
  Optimize Heap.
      }
      simpl. auto.
    }
    eauto.
    unfold val_inj, uop_eval.  unfold negint. eauto.
    simpl. eauto.
    sep lift 47%nat in H25.
    eapply LV_to_Rv in H25.
    eapply inline_tactics.monoasrt_mono in H25. exact H25.
    eapply inline_tactics.Rv_mono. eauto.
    simpl. auto. eauto.
    unfold val_inj, bop_eval. unfold uop_eval.
    unfold negint. unfold and. auto.
    simpl. auto. destruct_s s. simpl. split; eauto.
    eauto.
    unfold bop_eval, val_inj. unfold uop_eval. unfold negint. unfold and.
    unfold val_eq.  destruct (Int.eq (Int.not i14&ᵢv'6) ($ 0)); eauto.
    simpl. eauto.
    eauto. unfold bop_eval, val_inj. unfold uop_eval. unfold negint. unfold and.
    unfold val_eq. unfold bool_and.
    destruct (Int.eq i12 ($ CAP_CATEGORY_TYPE));
    destruct(Int.eq (Int.not i14&ᵢv'6) ($ 0));
    val_help; simpl; auto.
    simpl. eauto.

    eapply uop_rv.
    eapply bop_rv.
    {
      eapply lv_mapsto_to_rv.
      2:{
        eapply field_asrt_impl_struct_aop.
        3:{
          eapply field_asrt_impl_union_aop'.
          2:{
            eapply local_val_struct_member_addr_frm.
            4:{
              sep lift 2%nat in H25.
              exact H25.
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
        rewrite Int.add_zero in *. rewrite Int.add_zero in *. simpl typelen in *.
        rewrite of_to_nat_unsignedv'.
        rewrite <- addition_trans. rewrite Int.unsigned_repr.
        rewrite Int.add_assoc.
        change ($ 4 +ᵢ  $ 4) with ($8).
        sep lift 10%nat in H25. unfold Aptrmapsto in H25 at 1.
        exact H25. clear -H9. int auto. lia.
      }
      simpl. auto.
    }
    sep lift 47%nat in H25.
    eapply LV_to_Rv in H25. eapply inline_tactics.monoasrt_mono in H25.
    exact H25. eapply inline_tactics.Rv_mono.
    auto. simpl. auto. eauto.
    unfold bop_eval, val_inj.
    unfold val_eq.  destruct (Int.eq i14 v'6); auto.
    simpl. auto.
    eauto.
    unfold val_inj, uop_eval. unfold bop_eval.
    unfold val_eq. unfold notint.
    unfold Int.notbool.  
    destruct (Int.eq i14 v'6); val_help; simpl; auto.
    simpl. eauto.
    eauto.
    unfold val_inj, bop_eval. unfold val_eq, bool_and.
    unfold uop_eval. unfold negint. unfold and.
    destruct (Int.eq i12 ($ CAP_CATEGORY_TYPE));
    destruct (Int.eq (Int.not i14&ᵢv'6) ($ 0));
    destruct (Int.eq i14 v'6); 
    val_help; simpl; val_help; simpl; 
    try (unfold Int.notbool); val_help; simpl; val_help; simpl; eauto.
    simpl. eauto.

    pure intro.
    eapply seq_rule.
    eapply assign_rule_aop.
    2:{
      intros.
      eapply local_val_struct_member_addr.
      {
        sep lift 2%nat in H34.
        exact H34.
      }
      unfold Cap. eauto.
      unfold field_offset. simpl. eauto.
      simpl. unfold Content. eauto.
    }
    2:{
      intros.
      splits; intros.
      rewrite Int.add_zero in *. rewrite Int.add_zero in *.
      simpl typelen in *.
      rewrite <- addition_trans. rewrite of_to_nat_unsignedv'.
      rewrite Int.unsigned_repr. 
      sep lift 14%nat in H34.
      exact H34.
      clear -H9. int auto.
      lia.
      intros. 
      rewrite Int.add_zero in *.
      rewrite Int.add_zero in *.
      simpl typelen in *.
      rewrite of_to_nat_unsignedv' in H34 at 1.
      rewrite <- addition_trans in H34 at 1. 
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
      rewrite Int.unsigned_repr in H34 at 1.
      sep auto.
      clear -H9. int auto.
      lia.
    }
    2:{
      rewrite Int.add_zero.
      rewrite Int.add_zero.
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
            sep lift 3%nat in H34.
            exact H34.
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
      sep lift 15%nat in H34.
      rewrite <- addition_trans.
      exact H34. lia.
      simpl typelen in *.
      rewrite Int.add_zero in *.
      rewrite Int.add_zero in *.
      sep cancel cap2.
      sep cancel cap1.
      sep cancel ASlots.
      rewrite of_to_nat_unsignedv'.
      rewrite <- addition_trans.
      rewrite Int.unsigned_repr.
      rewrite <- addition_trans in H34.
      rewrite Int.unsigned_repr in H34.
      rewrite of_to_nat_unsignedv' in H34.
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
  Optimize Proof.
  Optimize Heap.
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
              sep lift 2%nat in H34.
              exact H34.
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
        sep lift 9%nat in H34.
        unfold Aptrmapsto in H34 at 1.
        exact H34.
        clear -H9. int auto.
        lia.
      }
      simpl. auto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.
  (*((cap1 ′ → cap_content).. category).. category_right =ₑrights*)

  eapply assign_rule_aop.
  2:{
    intros.
    eapply field_asrt_impl_struct_aop.
      3:{
        eapply field_asrt_impl_union_aop'.
        2:{
          eapply local_val_struct_member_addr_frm.
          4:{
            sep lift 4%nat in H34.
            exact H34.
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
    sep lift 16%nat in H34.
    exact H34.
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
    rewrite <- addition_trans in H34.
    rewrite Int.unsigned_repr in H34.
    rewrite of_to_nat_unsignedv' in H34.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    rewrite Int.add_assoc in H34 at 1.
    change (($ 4 +ᵢ  $ 4)) with ($8) in H34.
    sep cancel 2%nat 1%nat.
    sep auto.
    clear -H9. int auto.
    lia.
    clear -H9. int auto.
    lia.
  }
  2:{
    intros.
    sep lift 46%nat in H34.
    eapply LV_to_Rv in H34; eauto.
    eapply inline_tactics.monoasrt_mono in H34.
    exact H34.
    eapply inline_tactics.Rv_mono.
  }
  eapply eq_int. auto.
  intros. eexists. sep cancel p_local. simpl. auto.

  pure intro.
  instantiate(1:=Afalse).
  (*RETURN 〈 char_t 〉 ′ CNODE_MINT_FAILURE*)
  hoare forward; eauto.
  sep lifts (3::4::5::6::nil)%nat in H28.
  eapply fold_Cap in H28.
  sep lifts (2::3::1::4::nil)%nat in H28.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'24++(v'26,(i12,((i13, i14), v2)))::v'25))
  in H28; eauto.
  sep lifts (4::5::6::7::nil)%nat in H28.
  eapply fold_Cap in H28.
  sep lifts (3::4::1::5::nil)%nat in H28.
  eapply ASlots_fold_any_idx_frm in H28; eauto.
  sep lifts (6::4::7::nil)%nat in H28.
  eapply Aarray'_fold_any_idx_frm in H28; eauto.
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
  sep lifts (1::5::6::nil)%nat in H28.
  eapply Aarray'_fold_any_idx_frm in H28; eauto.
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
    simpl. rewrite H1, H10.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (6::7::3::nil)%nat in H28.
  eapply fold_Acnode in H28; eauto.
  sep lifts (11::12::3::nil)%nat in H28.
  eapply fold_Acnode in H28; eauto.

  sep lifts (2::6::7::8::9::nil)%nat in H28.
  eapply fold_ACSpace in H28; eauto.
  sep lifts (2::7::8::9::10::nil)%nat in H28.
  eapply fold_ACSpace in H28; eauto.
  sep lifts (5::2::6::nil)%nat in H28.

  eapply ACSpaceAarray_fold_any_idx_frm in H28; eauto.
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
  sep lifts (1::2::5::nil)%nat in H28.
  eapply ACSpaceAarray_fold_any_idx_frm in H28; eauto.
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
    rewrite H1, H10.
    rewrite S_add_sub_S.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_assoc_reverse.
    auto.
  }
  2: unfold SLOT_NUM; clear -H15; unfold CAP_CHANNEL_CLASS in H15;lia.
  2: auto.
  2: unfold SLOT_NUM; clear -H15; unfold CAP_CHANNEL_CLASS in H15;lia.
  2: auto.
  unfold AOSCSpacePrioTbl.
  sep cancel OSCSpacePrioTbl.
  rewrite app_assoc_reverse in H28.
  unfold Aarray.
  sep cancel Aarray'.
  sep cancel ACSpaceAarrayTptr.
  sep split; eauto.
  right.
  sep lift 4%nat. 
  eapply disj_split. left.
  sep split.
  
  3:{
  eapply get_capability_nth_mth_cspace_length_imp; eauto.
  }
  2:{
    rewrite list_trans_1.
    rewrite get_capability_nth_mth_cspace_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H2, H5. rewrite S_add_sub_S.
    clear -Hc1. lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; (int auto).
  }
  auto. pauto.
  pauto.
  pauto.
  eapply three_bool_and_false in H25.
  auto.

  (*CNODE_NONE_FAULT*)
  eapply disj_rule.
  hoare_split_pure_all.

  eapply rete_rule'.
  intros. destruct_s s. simpl. splits; eauto.
  intros.

  sep normal. sep eexists.
  sep cancel Aop;sep cancel Aie;sep cancel Aisr.
  sep cancel Ais; sep cancel Acs; sep cancel Aier.
  sep cancel cap1.
  sep cancel cap2.
  sep cancel pCSpace1.
  sep cancel pCSpace2.
  sep cancel destTask_Prio.
  sep cancel srcTask_Prio.
  sep cancel p_local.
  sep cancel func_capability.
  sep cancel rights; sep cancel A_dom_lenv.
  sep lift 9%nat. 
  eapply disj_split.
  right. sep lift 4%nat. 
  eapply disj_split. right.
  sep auto; eauto.
  rewrite Int.add_zero in *. rewrite Int.add_zero in *.
  rewrite <- addition_trans in H28.
  rewrite of_to_nat_unsignedv' in H28.
  rewrite Int.unsigned_repr in H28.
  rewrite Int.add_assoc in H28 at 1.
  change (($ 4 +ᵢ  $ 4)) with ($8) in H28.
  sep lifts (6::7::8::9::nil)%nat in H28.
  eapply fold_Cap in H28.
  2: auto.
  2:{
    rewrite max_unsigned_val.
    clear -H15. 
    unfold CAP_CHANNEL_CLASS in H15.
    int auto.
  }
  2: lia. 
  sep lifts (5::6::1::7::nil)%nat in H28.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'24++(v'26,(i12,((i13, i14), v2)))::v'25))
  in H28; eauto.
  sep lifts (4::3::2::7::nil)%nat in H28.
  eapply fold_Cap in H28.
  sep lifts (3::4::1::5::nil)%nat in H28.
  eapply ASlots_fold_any_idx_frm  with (slotsvl :=(v'13++(v'17, ($CAP_CATEGORY_TYPE, ((i13, v'6), v1)))::v'14))
  in H28 ; eauto.
  sep lifts (6::4::7::nil)%nat in H28.
  eapply Aarray'_fold_any_idx_frm in H28; eauto.
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
  sep lifts (1::5::6::nil)%nat in H28.
  eapply Aarray'_fold_any_idx_frm in H28; eauto.
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
    simpl. rewrite H1, H10.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (6::7::3::nil)%nat in H28.
  eapply fold_Acnode in H28; eauto.
  sep lifts (11::12::3::nil)%nat in H28.
  eapply fold_Acnode in H28; eauto.

  sep lifts (2::6::7::8::9::nil)%nat in H28.
  eapply fold_ACSpace in H28; eauto.
  sep lifts (2::7::8::9::10::nil)%nat in H28.
  eapply fold_ACSpace in H28; eauto.
  sep lifts (5::2::6::nil)%nat in H28.

  eapply ACSpaceAarray_fold_any_idx_frm in H28; eauto.
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
  sep lifts (1::2::5::nil)%nat in H28.
  eapply ACSpaceAarray_fold_any_idx_frm with (cspacevl:= (v'16 ++
  (i5, i6,
  v'24 ++
  (v'26, (i12, (i13, i14, v2))) :: v'25, i0,
  l, v, i) :: v'19) ++
 (i7, i8,
 v'13 ++
 (v'17,
 ($ CAP_CATEGORY_TYPE, (i13, v'6, v1)))
 :: v'14, i3, l0, v0, i2) :: v'20) in H28; eauto.
  
  
  2: lia. 
  2: lia.
  2:{
    rewrite app_length.
    simpl.
    rewrite app_length.
    simpl.
    rewrite H2, H5, H6. 
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
    rewrite H2, H5.
    rewrite S_add_sub_S.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  } 
  unfold AOSCSpacePrioTbl. sep auto.
  sep cancel OSCSpacePrioTbl. 
  unfold Aarray. 
  rewrite app_assoc.
  sep cancel Aarray'. 
  unfold update_nth_cspace_slots_cap.
  rewrite list_trans_1.
  
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  2:{
    rewrite app_length.
    simpl.
    rewrite H2, H5.
    rewrite S_add_sub_S. lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  rewrite update_nth_list_length_imp.
  rewrite update_nth_list_length_imp.
  eauto. auto.
  rewrite app_length.
  simpl.
  rewrite H2, H5.
  rewrite S_add_sub_S. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  splits; try (rewrite app_length); try (rewrite app_length); simpl.
  rewrite H1, H10, H11.
  rewrite S_add_sub_S_add.
  lia. 
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  unfold update_nth_cspace_slots_cap.
  rewrite list_trans_2.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite app_length. rewrite app_length.
  simpl.
  rewrite H2, H5, H6.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S.
  lia. lia. 
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite app_length. simpl.
  rewrite H2, H5.
  rewrite S_add_sub_S.
  lia. 
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite app_length. simpl.
  rewrite H2, H5.
  rewrite S_add_sub_S.
  lia. 
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  auto.
  rewrite app_length. simpl.
  rewrite H1, H10.
  rewrite S_add_sub_S.
  lia. 
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite app_length. simpl.
  rewrite app_length in H18. simpl in H18.
  auto.
  clear -H15.
  unfold CAP_CHANNEL_CLASS in *. unfold SLOT_NUM. lia.
  rewrite app_length. simpl.
  rewrite app_length in H18. simpl in H18.
  auto. auto.
  clear -H15.
  unfold CAP_CHANNEL_CLASS in *. unfold SLOT_NUM. lia.
  rewrite list_trans_1.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite app_length. simpl.
  rewrite H2, H5. rewrite S_add_sub_S.
  clear -Hc1. lia.
  clear -Hc1. 
  eapply Z2Nat.inj_lt; (int auto).
  rewrite list_trans.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  pauto.
  destruct H25.
  
  eapply three_and_true in H25. auto.
  hoare_split_pure_all. 
  eapply pfalse_rule.

  (*第二种情况，当srcTaskPrio位于destTask_Prio的右边时*)
  eapply backward_rule1.
  intros.
  sep lift 7%nat in H.
  eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with (idx1:=Z.to_nat(Int.unsigned v'4)) (idx2:=Z.to_nat(Int.unsigned v'3))in H; eauto.
  unfold AOSCSpacePrioTbl in H. sep split in H.
  destruct H0. rewrite Hv'14len. lia.
  clear -Hc2. 
  eapply Z2Nat.inj_lt; try (int auto).

  pure intro.
  unfold ACSpace.
  destruct v'17. destruct p. destruct p. destruct p. destruct v'24.
  destruct v'18. destruct p. destruct p. destruct p. destruct v'25.
  
  unfold Acnode.
  destruct c. destruct p. destruct c0. destruct p.
  pure intro.
  rename H25 into Hi2range.
  rename H26 into Hirange.

  (*unfold two slots*)
  eapply backward_rule1.
  intros.
  sep lifts (10::18::nil)%nat in H25.
  eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'5)) in H25.
  sep lift 2%nat in H25.
  eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'5)) in H25.
  exact H25.
  clear -H15. unfold CAP_CHANNEL_CLASS in H15.
  unfold SLOT_NUM. lia. auto.
  auto. 
  clear -H15. unfold CAP_CHANNEL_CLASS in H15.
  unfold SLOT_NUM. lia. auto. auto.
  pure intro.
  unfold ACap.
  destruct v'18. destruct c. destruct p.
  destruct v'27. destruct c. destruct p.
  hoare_lifts_trms_pre (Alvarmapsto pCSpace1, Alvarmapsto pCSpace2).
  hoare remember (1::2::nil)%nat pre.
  assert(nth_val' (Z.to_nat (Int.unsigned v'4))
  (v'21 ++
    (Vptr (b ↝ {i1}) :: v'22) ++
    Vptr (b0 ↝ {i4}) :: v'23) = Vptr(b0, i4)).
  simpl. rewrite list_trans_2. rewrite nth_val'_length_imp; eauto.
  rewrite app_length. simpl.
  rewrite H1, H10. rewrite S_add_sub_S.
  clear -Hc2. lia.
  clear -Hc2. 
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite H28.
  assert(nth_val' (Z.to_nat (Int.unsigned v'3))
  (v'21 ++
    (Vptr (b ↝ {i1}) :: v'22) ++
    Vptr (b0 ↝ {i4}) :: v'23) = Vptr(b, i1)).
  simpl. rewrite nth_val'_length_imp; eauto.
  rewrite H33.
  clear H28 H33.
  subst H25.
  (*cap1 ′ =ₑ&ₐ(((pCSpace1 ′ → cnode) .. slots)[func_capability ′]) .. capability;ₛ*)
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply assign_rule_lvar.
  intros. split; intros.
  sep cancel cap1.
  exact H25.
  sep auto.

  intros.
  eapply calculate_rv_expr_id_addr.
  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep cancel pCSpace1.
        sep lift 48%nat in H25.
        eapply LV_to_Rv in H25; eauto.
        instantiate(2:=Z.to_nat(Int.unsigned v'5)).
        rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
        exact H25.
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
  exact H25.
  sep auto.

  intros.
  eapply calculate_rv_expr_id_addr.
  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep cancel pCSpace2.
        sep lift 48%nat in H25.
        eapply LV_to_Rv in H25; eauto.
        instantiate(2:=Z.to_nat(Int.unsigned v'5)).
        rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
        exact H25.
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
  pure intro.
  rename H25 into Hisptrv2.
  rename H28 into Hisptrv1.
  (*IF(cap2′→cap_type==ₑ′CAP_CATEGORY_TYPE&&ₑ((∼cap2′→cap_content..category..category_right)&ₑrights′)==ₑ′0&&ₑcap2′→cap_content..category..category_right !=ₑ rights′)*)
  eapply seq_rule.
  eapply if_rule2'.
  intros.
  eapply bop_rv. eapply bop_rv. eapply bop_rv.
  {
    simpl typelen in H25.
    rewrite Int.add_zero in *.
    eapply lv_mapsto_to_rv.
    2:{
      eapply local_val_struct_member_addr.
      sep lift 2%nat in H25.
      exact H25. unfold Cap. eauto.
      unfold field_offset. simpl. unfold Int.zero. eauto.
      simpl. eauto.
    }
    2:{
      rewrite Int.add_zero in *.
      sep lift 15%nat in H25.
      unfold Aptrmapsto in H25 at 1.
      rewrite of_to_nat_unsignedv'. rewrite <- addition_trans.
      rewrite Int.unsigned_repr. 
      exact H25.
      clear -H9.
      rewrite max_unsigned_val. int auto.
      lia.
    }
    simpl. auto.
  }
  destruct_s s. simpl. splits; eauto.
  eauto. unfold bop_eval. unfold val_inj. 
  unfold val_eq. destruct (Int.eq i9 ($ CAP_CATEGORY_TYPE)); eauto.
  simpl. eauto.

  eapply bop_rv. eapply bop_rv.
  eapply uop_rv.  
  {
    eapply lv_mapsto_to_rv.
    2:{
      eapply field_asrt_impl_struct_aop.
      3:{
        eapply field_asrt_impl_union_aop'.
        2:{
          eapply local_val_struct_member_addr_frm.
          4:{
            rewrite Int.add_zero in H25. 
            sep lift 2%nat in H25.
            exact H25.
          }
          unfold Cap. eauto.
          unfold field_offset. simpl. rewrite Int.add_zero. eauto.
          simpl. unfold Content. eauto.
        }
        simpl. unfold Cap_Category. eauto.
      }
      simpl. eauto. unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    }
    2:{
      simpl typelen in *.
      rewrite Int.add_zero.
      rewrite of_to_nat_unsignedv'.
      rewrite Int.add_assoc.
      change($ 4 +ᵢ  $ 4) with ($8).
      rewrite <- addition_trans.
      rewrite Int.unsigned_repr.
      sep lift 17%nat in H25.
      unfold Aptrmapsto in H25 at 1.
      exact H25.  clear -H9. int auto.
      lia.
    }
    simpl. auto.
  }
  eauto.
  unfold val_inj, uop_eval.  unfold negint. eauto.
  simpl. eauto.
  sep lift 47%nat in H25.
  eapply LV_to_Rv in H25.
  eapply inline_tactics.monoasrt_mono in H25. exact H25.
  eapply inline_tactics.Rv_mono. eauto.
  simpl. auto. eauto.
  unfold val_inj, bop_eval. unfold uop_eval.
  unfold negint. unfold and. auto.
  simpl. auto. destruct_s s. simpl. split; eauto.
  eauto.
  unfold bop_eval, val_inj. unfold uop_eval. unfold negint. unfold and.
  unfold val_eq.  destruct (Int.eq (Int.not i11&ᵢv'6) ($ 0)); eauto.
  simpl. eauto.
  eauto. unfold bop_eval, val_inj. unfold uop_eval. unfold negint. unfold and.
  unfold val_eq. unfold bool_and.
  destruct (Int.eq i9 ($ CAP_CATEGORY_TYPE)); 
  destruct (Int.eq (Int.not i11&ᵢv'6) ($ 0));
  val_help; simpl; auto.
  simpl. eauto.

  eapply uop_rv.
  eapply bop_rv.
  {
    eapply lv_mapsto_to_rv.
    2:{
      eapply field_asrt_impl_struct_aop.
      3:{
        eapply field_asrt_impl_union_aop'.
        2:{
          eapply local_val_struct_member_addr_frm.
          4:{
            sep lift 2%nat in H25.
            exact H25.
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
      rewrite Int.add_zero in *. rewrite Int.add_zero in *. simpl typelen in *.
      rewrite of_to_nat_unsignedv'.
      rewrite <- addition_trans. rewrite Int.unsigned_repr.
      rewrite Int.add_assoc.
      change ($ 4 +ᵢ  $ 4) with ($8).
      sep lift 17%nat in H25. unfold Aptrmapsto in H25 at 1.
      exact H25. clear -H9. int auto. lia.
    }
    simpl. auto.
  }
  sep lift 47%nat in H25.
  eapply LV_to_Rv in H25. eapply inline_tactics.monoasrt_mono in H25.
  exact H25. eapply inline_tactics.Rv_mono.
  auto. simpl. auto. eauto.
  unfold bop_eval, val_inj.
  unfold val_eq.  destruct (Int.eq i11 v'6); auto.
  simpl. auto.
  eauto.
  unfold val_inj, uop_eval. unfold bop_eval.
  unfold val_eq. unfold notint.
  unfold Int.notbool.  
  destruct (Int.eq i11 v'6); val_help; simpl; auto.
  simpl. eauto.
  eauto.
  unfold val_inj, bop_eval. unfold val_eq, bool_and.
  unfold uop_eval. unfold negint. unfold and.
  destruct (Int.eq i9 ($ CAP_CATEGORY_TYPE));
  destruct (Int.eq (Int.not i11&ᵢv'6) ($ 0));
  destruct (Int.eq i11 v'6); 
  val_help; simpl; val_help; simpl; 
  try (unfold Int.notbool); val_help; simpl; val_help; simpl; eauto.
  simpl. eauto.

  pure intro.
  (*cap1 ′ → cap_type =ₑ ′ CAP_CATEGORY_TYPE*)
  eapply seq_rule.
  eapply assign_rule_aop.
  2:{
    intros.
    eapply local_val_struct_member_addr.
    {
      sep lift 2%nat in H34.
      exact H34.
    }
    unfold Cap. eauto.
    unfold field_offset. simpl. eauto.
    simpl. unfold Content. eauto.
  }
  2:{
    intros.
    splits; intros.
    rewrite Int.add_zero in *. rewrite Int.add_zero in *.
    simpl typelen in *.
    rewrite <- addition_trans. rewrite of_to_nat_unsignedv'.
    rewrite Int.unsigned_repr. 
    sep lift 7%nat in H34.
    exact H34.
    clear -H9. int auto.
    lia.
  Optimize Proof.
  Optimize Heap.
    intros. 
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    simpl typelen in *.
    rewrite of_to_nat_unsignedv' in H34 at 1.
    rewrite <- addition_trans in H34 at 1. 
    sep cancel cap2.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite Int.repr_unsigned in H34.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep auto.
    clear -H9. int auto.
  }
  2:{
    rewrite Int.add_zero.
    rewrite Int.add_zero.
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
          sep lift 3%nat in H34.
          exact H34.
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
    sep lift 8%nat in H34.
    rewrite <- addition_trans.
    exact H34. lia.
    simpl typelen in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    sep cancel cap2.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H34.
    rewrite Int.unsigned_repr in H34.
    rewrite of_to_nat_unsignedv' in H34.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
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
            sep lift 2%nat in H34.
            exact H34.
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
      sep lift 15%nat in H34.
      unfold Aptrmapsto in H34 at 1.
      exact H34.
      clear -H9. int auto.
      lia.
    }
    simpl. auto.
}
eapply eq_int. auto.
intros.
eexists. sep cancel p_local. simpl. auto.
(*((cap1 ′ → cap_content).. category).. category_right =ₑrights*)

  eapply assign_rule_aop.
  2:{
    intros.
    eapply field_asrt_impl_struct_aop.
      3:{
        eapply field_asrt_impl_union_aop'.
        2:{
          eapply local_val_struct_member_addr_frm.
          4:{
            sep lift 4%nat in H34.
            exact H34.
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
    sep lift 9%nat in H34.
    exact H34.
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
    rewrite <- addition_trans in H34.
    rewrite Int.unsigned_repr in H34.
    rewrite of_to_nat_unsignedv' in H34.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    rewrite Int.add_assoc in H34 at 1.
    change (($ 4 +ᵢ  $ 4)) with ($8) in H34.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
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
    sep lift 46%nat in H34.
    eapply LV_to_Rv in H34; eauto.
    eapply inline_tactics.monoasrt_mono in H34.
    exact H34.
    eapply inline_tactics.Rv_mono.
  }
  eapply eq_int. auto.
  intros. eexists. sep cancel p_local. simpl. auto.

  pure intro.
  instantiate(1:=Afalse).

  (*RETURN 〈 char_t 〉 ′ CNODE_MINT_FAILURE*)
  hoare forward; eauto.
  sep lifts (3::4::5::6::nil)%nat in H28.
  eapply fold_Cap in H28.
  sep lifts (2::3::1::4::nil)%nat in H28.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'24++(v'26,(i12,((i13, i14), v2)))::v'25))
  in H28; eauto.
  sep lifts (4::5::6::7::nil)%nat in H28.
  eapply fold_Cap in H28.
  sep lifts (3::4::1::5::nil)%nat in H28.
  eapply ASlots_fold_any_idx_frm in H28; eauto.
  sep lifts (6::4::7::nil)%nat in H28.
  eapply Aarray'_fold_any_idx_frm in H28; eauto.
  2:{
    clear -Hc2.
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
  sep lifts (1::5::6::nil)%nat in H28.
  eapply Aarray'_fold_any_idx_frm in H28; eauto.
  2: lia.
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  2: rewrite max_unsigned_val; simpl; lia.

  2:{
    split; auto. 
    rewrite app_length.
    simpl. rewrite H1, H10.
    rewrite S_add_sub_S. lia. 
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (6::7::3::nil)%nat in H28.
  eapply fold_Acnode in H28; eauto.
  sep lifts (11::12::3::nil)%nat in H28.
  eapply fold_Acnode in H28; eauto.

  sep lifts (2::6::7::8::9::nil)%nat in H28.
  eapply fold_ACSpace in H28; eauto.
  sep lifts (2::7::8::9::10::nil)%nat in H28.
  eapply fold_ACSpace in H28; eauto.
  sep lifts (5::2::6::nil)%nat in H28.

  eapply ACSpaceAarray_fold_any_idx_frm in H28; eauto.
  2: lia. 
  2:{
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl. 
    rewrite H2, H5.
    rewrite S_add_sub_S. lia. 
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (1::2::5::nil)%nat in H28.
  eapply ACSpaceAarray_fold_any_idx_frm in H28; eauto.
  2: lia. 
  2: lia.
  
  2:{
    rewrite app_length.
    simpl.
    rewrite H2, H5. 
    rewrite S_add_sub_S.
    lia. 
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl.
    rewrite H1, H10.
    rewrite S_add_sub_S.
    lia. 
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  unfold AOSCSpacePrioTbl. 
  sep split.
  sep cancel OSCSpacePrioTbl. 
  unfold Aarray. 
  rewrite app_assoc.
  sep cancel Aarray'. sep auto.
  sep cancel ACSpaceAarrayTptr.
  right.
  sep lift 4%nat. 
  eapply disj_split. left.
  sep split. auto.
  rewrite list_trans.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite list_trans_1.
  eapply get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite app_length. simpl.
  rewrite H2, H5. rewrite S_add_sub_S.
  lia. 
  clear -Hc2.
  eapply Z2Nat.inj_lt; try (int auto).
  
  splits. lia.
  lia.
  rewrite app_assoc_reverse. auto.
  rewrite app_assoc_reverse. auto.
  auto. pauto.
  eapply three_bool_and_false in H25.
  auto.

  splits; try (rewrite app_length); try (rewrite app_length); simpl.
  rewrite H1, H10, H11.
  rewrite S_add_sub_S. 
  rewrite S_add_sub_S_add.
  lia. 
  clear -Hc2.
  eapply Z2Nat.inj_lt; try (int auto).
  lia. 
  rewrite H2, H5, H6.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S_add.
  lia.
  clear -Hc2.
  eapply Z2Nat.inj_lt; try (int auto).
  lia.
  auto.
  rewrite app_assoc_reverse. auto.
  clear -H15. unfold CAP_CHANNEL_CLASS in H15.
  unfold SLOT_NUM. lia.
  auto.
  clear -H15. unfold CAP_CHANNEL_CLASS in H15.
  unfold SLOT_NUM. lia.
  auto.
  eapply disj_rule.
  hoare_split_pure_all.

  eapply rete_rule'.
  intros. destruct_s s. simpl. splits; eauto.
  intros.

  sep normal. sep eexists.
  sep cancel Aop;sep cancel Aie;sep cancel Aisr.
  sep cancel Ais; sep cancel Acs; sep cancel Aier.
  sep cancel cap1.
  sep cancel cap2.
  sep cancel pCSpace1.
  sep cancel pCSpace2.
  sep cancel destTask_Prio.
  sep cancel srcTask_Prio.
  sep cancel p_local.
  sep cancel func_capability.
  sep cancel rights; sep cancel A_dom_lenv.
  sep lift 9%nat. 
  eapply disj_split.
  right. sep lift 4%nat. 
  eapply disj_split. right.
  sep auto; eauto.
  rewrite Int.add_zero in *. rewrite Int.add_zero in *.
  rewrite <- addition_trans in H28.
  rewrite of_to_nat_unsignedv' in H28.
  rewrite Int.unsigned_repr in H28.
  rewrite Int.add_assoc in H28 at 1.
  change (($ 4 +ᵢ  $ 4)) with ($8) in H28.
  sep lifts (3::2::1::6::nil)%nat in H28.
  eapply fold_Cap in H28.
  2: auto.
  2:{
    rewrite max_unsigned_val.
    clear -H15. unfold CAP_CHANNEL_CLASS in H15.
    int auto. 
  Optimize Proof.
  Optimize Heap.
  }
  2: lia. 
  sep lifts (2::3::1::4::nil)%nat in H28.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'24++(v'26,($CAP_CATEGORY_TYPE,((i10, v'6), v2)))::v'25))
  in H28; eauto.
  sep lifts (4::5::6::7::nil)%nat in H28.
  eapply fold_Cap in H28.
  sep lifts (3::4::1::5::nil)%nat in H28.
  eapply ASlots_fold_any_idx_frm  with (slotsvl :=(v'13++(v'17, (i9, ((i10, i11), v1)))::v'14))
  in H28; eauto.
  sep lifts (6::4::7::nil)%nat in H28.
  eapply Aarray'_fold_any_idx_frm in H28; eauto.
  2:{
    clear -Hc2.
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
  sep lifts (1::5::6::nil)%nat in H28.
  eapply Aarray'_fold_any_idx_frm in H28; eauto.
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
    simpl. rewrite H1, H10.
    rewrite S_add_sub_S. lia. 
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (6::7::3::nil)%nat in H28.
  eapply fold_Acnode in H28; eauto.
  sep lifts (11::12::3::nil)%nat in H28.
  eapply fold_Acnode in H28; eauto.

  sep lifts (2::6::7::8::9::nil)%nat in H28.
  eapply fold_ACSpace in H28; eauto.
  sep lifts (2::7::8::9::10::nil)%nat in H28.
  eapply fold_ACSpace in H28; eauto.
  sep lifts (5::2::6::nil)%nat in H28.

  eapply ACSpaceAarray_fold_any_idx_frm in H28; eauto.
  2: lia. 
  2:{
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl. 
    rewrite H2, H5.
    rewrite S_add_sub_S. lia. 
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (1::2::5::nil)%nat in H28.
  eapply ACSpaceAarray_fold_any_idx_frm with (cspacevl :=
  (v'16 ++
  (i5, i6,
  v'24 ++
  (v'26,
  ($ CAP_CATEGORY_TYPE, (i10, v'6, v2)))
  :: v'25, i0, l, v, i) :: v'19) ++
  (i7, i8,
  v'13 ++ (v'17, (i9, (i10, i11, v1))) :: v'14,
  i3, l0, v0, i2) :: v'20)
  in H28; eauto.
  2: lia. 
  2: lia.
  2:{
    rewrite app_length.
    simpl.
    rewrite app_length. simpl.

    rewrite H2, H5, H6. 
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    lia. 
    lia.
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl.
    rewrite H2, H5.
    rewrite S_add_sub_S.
    lia. 
    clear -Hc2.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  unfold AOSCSpacePrioTbl. sep auto.
  sep cancel OSCSpacePrioTbl. 
  unfold Aarray. 
  rewrite app_assoc.
  sep cancel Aarray'. sep auto.
  unfold update_nth_cspace_slots_cap.
  rewrite list_trans.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp.
  rewrite update_nth_list_length_imp. 
  rewrite list_trans_2.
  sep cancel ACSpaceAarrayTptr.
  auto. auto.
  splits; try (rewrite app_length); try (rewrite app_length); simpl.
  rewrite H1, H10, H11.
  rewrite S_add_sub_S_add.
  lia. 
  clear -Hc2.
  eapply Z2Nat.inj_lt; try (int auto).
  unfold update_nth_cspace_slots_cap.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp.
  rewrite update_nth_list_length_imp.
  rewrite app_length. simpl.
  rewrite app_length. simpl.
  rewrite H2, H5, H6.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S_add.
  lia.
  clear -Hc2.
  eapply Z2Nat.inj_lt; try (int auto).
  auto. lia.
  auto. auto. auto.
  rewrite app_length. simpl.
  rewrite H1, H10.
  rewrite S_add_sub_S. lia.
  clear -Hc2.
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite app_length. simpl.
  rewrite app_length in H. simpl in H.
  auto. 
  clear -H15. unfold CAP_CHANNEL_CLASS in H15.
  unfold SLOT_NUM. lia.
  auto. 
  clear -H15. unfold CAP_CHANNEL_CLASS in H15.
  unfold SLOT_NUM. lia.
  rewrite app_length. simpl.
  rewrite app_length in H. simpl in H.
  auto.
  rewrite list_trans.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite list_trans_1.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite app_length. simpl.
  rewrite H2, H5.
  rewrite S_add_sub_S. lia.
  clear -Hc2.
  eapply Z2Nat.inj_lt; try (int auto).
  pauto.
  destruct H25.
  eapply three_and_true. auto.
  hoare_split_pure_all.
  eapply pfalse_rule.

(*当destTask_prio和srcTask_prio重合时*)
  assert(v'3 = v'4).
  apply unsigned_inj. auto.
  subst v'4.
  eapply backward_rule1.
  intros.
  sep lift 7%nat in H.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned v'3))in H; eauto.
  unfold AOSCSpacePrioTbl in H. sep split in H.
  destruct H0. rewrite Hv'14len. lia.
  pure intro.
  unfold ACSpace.
  destruct v'16. destruct p. destruct p. destruct p. destruct v'20.

  unfold Acnode.
  destruct c. destruct p.
  pure intro.
  rename H17 into Hirange.

  (*unfoldslots*)
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H17 ASlots.
  eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'5)) in H17.
  exact H17.
  clear -H13. unfold CAP_CHANNEL_CLASS in H13.
  unfold SLOT_NUM. lia. auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure intro.
  unfold ACap.
  destruct v'20. destruct c. destruct p.
  rewrite nth_val'_length_imp; eauto.

  (*cap1 ′ =ₑ&ₐ(((pCSpace1 ′ → cnode) .. slots)[func_capability ′]) .. capability;ₛ*)
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply assign_rule_lvar.
  intros. split; intros.
  sep cancel cap1.
  exact H17.
  sep auto.

  intros.
  eapply calculate_rv_expr_id_addr.
  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep cancel pCSpace1.
        sep lift 30%nat in H17.
        eapply LV_to_Rv in H17; eauto.
        instantiate(2:=Z.to_nat(Int.unsigned v'5)).
        rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
        exact H17.
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

  (*cap2 ′ =ₑ&ₐ(((pCSpace2 ′ → cnode) .. slots) [func_capability ′])
  .. capability;ₛ*)
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply assign_rule_lvar.
  intros. split; intros.
  sep cancel cap2.
  exact H17.
  sep auto.

  intros.
  eapply calculate_rv_expr_id_addr.
  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep cancel pCSpace2.
        sep lift 30%nat in H17.
        eapply LV_to_Rv in H17; eauto.
        instantiate(2:=Z.to_nat(Int.unsigned v'5)).
        rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
        exact H17.
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

  pure intro.
  rename H17 into Hisptrv0.
  (*IF(cap2′→cap_type==ₑ′CAP_CATEGORY_TYPE&&ₑ((∼cap2′→cap_content..category..category_right)&ₑrights′)==ₑ′0&&ₑcap2′→cap_content..category..category_right !=ₑ rights′)*)
  eapply seq_rule.
  eapply if_rule2'.
  intros.
  eapply bop_rv. eapply bop_rv. eapply bop_rv.
  {
    simpl typelen in H17.
    rewrite Int.add_zero in *.
    eapply lv_mapsto_to_rv.
    2:{
      eapply local_val_struct_member_addr.
      sep lift 2%nat in H17.
      exact H17. unfold Cap. eauto.
      unfold field_offset. simpl. unfold Int.zero. eauto.
      simpl. eauto.
    }
    2:{
      rewrite Int.add_zero in *.
      sep lift 6%nat in H17.
      unfold Aptrmapsto in H17 at 1.
      rewrite of_to_nat_unsignedv'. rewrite <- addition_trans.
      rewrite Int.unsigned_repr. 
      exact H17.
      clear -H9.
      rewrite max_unsigned_val. int auto.
      lia.
    }
    simpl. auto.
  }
  destruct_s s. simpl. splits; eauto.
  eauto. unfold bop_eval. unfold val_inj. 
  unfold val_eq. destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE)); eauto.
  simpl. eauto.

  eapply bop_rv. eapply bop_rv.
  eapply uop_rv.  
  {
    eapply lv_mapsto_to_rv.
    2:{
      eapply field_asrt_impl_struct_aop.
      3:{
        eapply field_asrt_impl_union_aop'.
        2:{
          eapply local_val_struct_member_addr_frm.
          4:{
            rewrite Int.add_zero in H17. 
            sep lift 2%nat in H17.
            exact H17.
          }
          unfold Cap. eauto.
          unfold field_offset. simpl. rewrite Int.add_zero. eauto.
          simpl. unfold Content. eauto.
        }
        simpl. unfold Cap_Category. eauto.
      }
      simpl. eauto. unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    }
    2:{
      simpl typelen in *.
      rewrite Int.add_zero.
      rewrite of_to_nat_unsignedv'.
      rewrite Int.add_assoc.
      change($ 4 +ᵢ  $ 4) with ($8).
      rewrite <- addition_trans.
      rewrite Int.unsigned_repr.
      sep lift 8%nat in H17.
      unfold Aptrmapsto in H17 at 1.
      exact H17.  clear -H9. int auto.
      lia.
    }
    simpl. auto.
  }
  eauto.
  unfold val_inj, uop_eval.  unfold negint. eauto.
  simpl. eauto.
  sep lift 30%nat in H17.
  eapply LV_to_Rv in H17.
  eapply inline_tactics.monoasrt_mono in H17. exact H17.
  eapply inline_tactics.Rv_mono. eauto.
  simpl. auto. eauto.
  unfold val_inj, bop_eval. unfold uop_eval.
  unfold negint. unfold and. auto.
  simpl. auto. destruct_s s. simpl. split; eauto.
  eauto.
  unfold bop_eval, val_inj. unfold uop_eval. unfold negint. unfold and.
  unfold val_eq.  destruct (Int.eq (Int.not i6&ᵢv'6) ($ 0)); eauto.
  simpl. eauto.
  eauto. unfold bop_eval, val_inj. unfold uop_eval. unfold negint. unfold and.
  unfold val_eq. unfold bool_and.
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE));
  destruct(Int.eq (Int.not i6&ᵢv'6) ($ 0));
  val_help; simpl; auto.
  simpl. eauto.

  eapply uop_rv.
  eapply bop_rv.
  {
    eapply lv_mapsto_to_rv.
    2:{
      eapply field_asrt_impl_struct_aop.
      3:{
        eapply field_asrt_impl_union_aop'.
        2:{
          eapply local_val_struct_member_addr_frm.
          4:{
            sep lift 2%nat in H17.
            exact H17.
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
      rewrite Int.add_zero in *. rewrite Int.add_zero in *. simpl typelen in *.
      rewrite of_to_nat_unsignedv'.
      rewrite <- addition_trans. rewrite Int.unsigned_repr.
      rewrite Int.add_assoc.
      change ($ 4 +ᵢ  $ 4) with ($8).
      sep lift 8%nat in H17. unfold Aptrmapsto in H17 at 1.
      exact H17. clear -H9. int auto. lia.
    }
    simpl. auto.
  }
  sep lift 30%nat in H17.
  eapply LV_to_Rv in H17. eapply inline_tactics.monoasrt_mono in H17.
  exact H17. eapply inline_tactics.Rv_mono.
  auto. simpl. auto. eauto.
  unfold bop_eval, val_inj.
  unfold val_eq.  destruct (Int.eq i6 v'6); auto.
  simpl. auto.
  eauto.
  unfold val_inj, uop_eval. unfold bop_eval.
  unfold val_eq. unfold notint.
  unfold Int.notbool.  
  destruct (Int.eq i6 v'6); val_help; simpl; auto.
  simpl. eauto.
  eauto.
  unfold val_inj, bop_eval. unfold val_eq, bool_and.
  unfold uop_eval. unfold negint. unfold and.
  destruct (Int.eq i4 ($ CAP_CATEGORY_TYPE));
  destruct (Int.eq (Int.not i6&ᵢv'6) ($ 0));
  destruct (Int.eq i6 v'6); 
  val_help; simpl; val_help; simpl; 
  try (unfold Int.notbool); val_help; simpl; val_help; simpl; eauto.
  simpl. eauto.

  pure intro.
  (*cap1 ′ → cap_type =ₑ ′ CAP_CATEGORY_TYPE*)
  eapply seq_rule.
  eapply assign_rule_aop.
  2:{
    intros.
    eapply local_val_struct_member_addr.
    {
      sep lift 2%nat in H23.
      exact H23.
    }
    unfold Cap. eauto.
    unfold field_offset. simpl. eauto.
    simpl. unfold Content. eauto.
  }
  2:{
    intros.
    splits; intros.
    rewrite Int.add_zero in *. rewrite Int.add_zero in *.
    simpl typelen in *.
    rewrite <- addition_trans. rewrite of_to_nat_unsignedv'.
    rewrite Int.unsigned_repr. 
    sep lift 5%nat in H23.
    exact H23.
    clear -H9. int auto.
    lia.
  Optimize Proof.
  Optimize Heap.
    intros. 
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    simpl typelen in *.
    rewrite of_to_nat_unsignedv' in H23 at 1.
    rewrite <- addition_trans in H23 at 1. 
    sep cancel cap2.
    sep cancel cap1.
    sep cancel ASlots.
    sep cancel 2%nat 1%nat.

    rewrite Int.unsigned_repr in H23 at 1.
    sep auto.
    clear -H9. int auto.
    lia.
  }
  2:{
    rewrite Int.add_zero.
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
          sep lift 3%nat in H23.
          exact H23.
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
    sep lift 6%nat in H23.
    rewrite <- addition_trans.
    exact H23. lia.
    simpl typelen in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    sep cancel cap2.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H23.
    rewrite Int.unsigned_repr in H23.
    rewrite of_to_nat_unsignedv' in H23.
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
      unfold field_offset. simpl. eauto.
    }
    2:{
      rewrite Int.add_zero in *.
      rewrite Int.add_zero in *.
      rewrite of_to_nat_unsignedv'. 
      rewrite <- addition_trans.
      rewrite Int.unsigned_repr.
      sep lift 6%nat in H23.
      unfold Aptrmapsto in H23 at 1.
      exact H23.
      clear -H9. int auto.
      lia.
    }
    simpl. auto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.
  (*((cap1 ′ → cap_content).. category).. category_right =ₑrights*)

  eapply assign_rule_aop.
  2:{
  intros.
  eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep lift 4%nat in H23.
          exact H23.
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
  sep lift 7%nat in H23.
  exact H23.
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
  rewrite <- addition_trans in H23.
  rewrite Int.unsigned_repr in H23.
  rewrite of_to_nat_unsignedv' in H23.
  rewrite Int.add_assoc in H23 at 1.
  change (($ 4 +ᵢ  $ 4)) with ($8) in H23.
  sep auto.
  clear -H9. int auto.
  lia.
  clear -H9. int auto.
  lia.
  }
  2:{
    intros.
    sep lift 29%nat in H23.
    eapply LV_to_Rv in H23; eauto.
    eapply inline_tactics.monoasrt_mono in H23.
    exact H23.
    eapply inline_tactics.Rv_mono.
  }
  eapply eq_int. auto.
  intros. eexists. sep cancel p_local. simpl. auto.

  pure intro.
  instantiate(1:=Afalse).

  (*RETURN 〈 char_t 〉 ′ CNODE_MINT_FAILURE*)
  hoare forward; eauto.
  sep lifts (3::4::5::6::nil)%nat in H21.
  eapply fold_Cap in H21.
  sep lifts (2::3::1::4::nil)%nat in H21.
  eapply ASlots_fold_any_idx_frm in H21; eauto.
  sep lifts (3::4::nil)%nat in H21.
  rewrite addition_trans in H21 at 1.
  assert(v'3 = $ Z.of_nat(Z.to_nat(Int.unsigned v'3))).
  rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned. auto.
  rewrite H23 in H21 at 1. clear H23.
  eapply array_asrt_eq_frm in H21; eauto.
  2: lia.
  2:{
    eapply nth_val_length_imp. auto.
  }
  2:{
    simpl.  lia.
  }
  sep lifts (5::6::2::nil)%nat in H21.
  eapply fold_Acnode in H21; eauto.

  sep lifts (1::5::6::7::8::nil)%nat in H21.
  eapply fold_ACSpace in H21; eauto.
  sep lifts (4::1::5::nil)%nat in H21.

  eapply ACSpaceAarray_fold_any_idx_frm in H21; eauto.
  2: lia. 
  2: lia.
  
  unfold AOSCSpacePrioTbl.
  sep normal.
  sep lift 5%nat. 
  eapply disj_split. right.
  sep lift 4%nat. 
  eapply disj_split. left.
  sep split. sep auto.
  3:{
    rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  }
  2:{
    rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  }
  2:{
    pauto.
  }
  splits; auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pauto.
  eapply three_bool_and_false; auto.
  clear -H13. unfold CAP_CHANNEL_CLASS in H13.
  unfold SLOT_NUM. lia.
  auto.
  eapply disj_rule.
  hoare_split_pure_all.

  eapply rete_rule'.
  intros. destruct_s s. simpl. splits; eauto.
  intros.

  sep normal. sep eexists.
  sep cancel Aop;sep cancel Aie;sep cancel Aisr.
  sep cancel Ais; sep cancel Acs; sep cancel Aier.
  sep cancel cap1.
  sep cancel cap2.
  sep cancel pCSpace1.
  sep cancel pCSpace2.
  sep cancel destTask_Prio.
  sep cancel srcTask_Prio.
  sep cancel p_local.
  sep cancel func_capability.
  sep cancel rights; sep cancel A_dom_lenv.
  sep lift 9%nat. 
  eapply disj_split. right.
  sep lift 4%nat. 
  eapply disj_split. right.
  sep auto; eauto.
  rewrite Int.add_zero in *. rewrite Int.add_zero in *.
  rewrite <- addition_trans in H21.
  rewrite of_to_nat_unsignedv' in H21.
  rewrite Int.unsigned_repr in H21.
  rewrite Int.add_assoc in H21 at 1.
  change (($ 4 +ᵢ  $ 4)) with ($8) in H21.
  sep lifts (3::2::1::6::nil)%nat in H21.
  eapply fold_Cap in H21.
  sep lifts (2::3::1::4::nil)%nat in H21.
  eapply ASlots_fold_any_idx_frm with (slotsvl :=(v'13++(v'16, ($CAP_CATEGORY_TYPE, ((i5, v'6), v0)))::v'14)) in H21; eauto.
  sep lifts (3::4::nil)%nat in H21.
  rewrite addition_trans in H21 at 1.
  assert(v'3 = $ Z.of_nat(Z.to_nat(Int.unsigned v'3))).
  rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned. auto.
  rewrite H22 in H21 at 1. clear H22.
  eapply array_asrt_eq_frm in H21; eauto.
  2: lia.
  2:{
    eapply nth_val_length_imp. auto.
  }
  2:{
    simpl.  lia.
  }
  sep lifts (5::6::2::nil)%nat in H21.
  eapply fold_Acnode in H21; eauto.

  sep lifts (1::5::6::7::8::nil)%nat in H21.
  eapply fold_ACSpace in H21; eauto.
  sep lifts (4::1::5::nil)%nat in H21.

  eapply ACSpaceAarray_fold_any_idx_frm with (cspacevl:=
  v'4 ++
(i2, i3,
v'13 ++
(v'16,
($ CAP_CATEGORY_TYPE, (i5, v'6, v0)))
:: v'14, i0, l, v, i) :: v'17)in H21; eauto.
  2: lia. 
  2: lia.
  2:{
  rewrite app_length.
  simpl. 
  rewrite H2, H5.
  rewrite S_add_sub_S. lia. 
  lia.
  }
  unfold AOSCSpacePrioTbl. 
  sep cancel OSCSpacePrioTbl.
  unfold Aarray. sep cancel Aarray'.
  unfold update_nth_cspace_slots_cap.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp.
  rewrite update_nth_list_length_imp.

  sep auto.

  splits; try (rewrite app_length); try (rewrite app_length); simpl.
  rewrite H1, H6.
  rewrite S_add_sub_S.
  lia. 
  lia.
  rewrite H2, H5. 
  rewrite S_add_sub_S.
  lia. lia.
  auto.
  auto. auto.
  rewrite app_length in H. simpl in H.
  rewrite app_length. simpl. auto.
  clear -H13. unfold CAP_CHANNEL_CLASS in H13.
  unfold SLOT_NUM. lia.
  rewrite app_length in H. simpl in H.
  rewrite app_length. simpl. auto.
  auto.
  rewrite max_unsigned_val.
  clear -H13. unfold CAP_CHANNEL_CLASS in H13.
  int auto. lia.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  pauto.
  destruct H17.
  eapply three_and_true; auto.
  hoare_split_pure_all.
  eapply pfalse_rule.
  Unshelve.
  all: auto.
Qed.


    
    



