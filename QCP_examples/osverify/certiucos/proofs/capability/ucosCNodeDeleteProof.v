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
Lemma ucos_CNode_Delete_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal ucos_CNode_Delete
                  vl logicl ucos_CNode_DeletePre ct->
      Some r =
      BuildRetI os_internal ucos_CNode_Delete vl logicl ucos_CNode_DeletePost ct->
      exists t d1 d2 s,
      os_internal ucos_CNode_Delete = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
  init spec.
  inverts H.
  inverts H0.
  unfold AOSCSpacePrioTbl at 2. hoare_split_pure_all.
  assert(Hv'7len: length v'7 = 64%nat). simpljoin. auto.
  assert(Hv'8len: length v'8 = 64%nat). simpljoin. auto.
  assert(Harraytypematch: array_type_vallist_match
  CSPACE ∗ v'7). simpljoin. auto.
  eapply backward_rule1 with (p:=Aie false **
  Ais nil **
  Acs v'5 **
  Aisr v'6 **
  Aier v'3 **
   <|| v'4 ||>  **
  AOSCSpacePrioTbl (v'9 ↝ {v'10}) v'7 v'8 v'11 **
  p_local OSLInv ct init_lg **
  LV cap1 @ Cap ∗ |-> v'0 **
  LV pCSpace1 @ CSPACE ∗ |-> v' **
  LV func_capability @ long |-> Vint32 v'2 **
  LV destTask_Prio @ char_t |-> Vint32 v'1 **
  A_dom_lenv
    ((func_capability ↝ {long})
     :: (destTask_Prio ↝ {char_t})
        :: (pCSpace1 ↝ {CSPACE ∗})
           :: (cap1 ↝ {Cap ∗}) :: nil)).
  intros. unfold AOSCSpacePrioTbl. sep auto.
  clear H.
  hoare forward.
  destruct (Int.ltu ($ SLOT_NUM) v'2); auto.
  destruct (Int.eq v'2 ($ SLOT_NUM)); auto.
  destruct (Int.ltu ($ SLOT_NUM) v'2);
  destruct (Int.eq v'2 ($ SLOT_NUM)); auto.
  hoare_split_pure_all.
  hoare forward; [idtac|simpl; eauto..].
  sep lift 2%nat. 
  eapply disj_split. left. sep auto; simpl; eauto.
  left.
  destruct (Int.ltu ($ SLOT_NUM) v'2) eqn: Hlt;
  destruct (Int.eq v'2 ($ SLOT_NUM)) eqn: Heq;
  (val_help_H H; simpl in H); tryfalse;
  try(rewrite Intlt_true_is_Zlt in Hlt);
  try(rewrite Inteq_true_is_Zeq in Heq);
  try(rewrite Int.unsigned_repr in Hlt);
  try(rewrite Int.unsigned_repr in Heq);
  try lia; try(unfold SLOT_NUM; rewrite max_unsigned_val); try lia.
  eapply disj_rule. hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all. 
  assert(Hv'2range: Int.unsigned v'2 < SLOT_NUM).
  destruct (Int.ltu ($ SLOT_NUM) v'2) eqn: Hlt;
  destruct (Int.eq v'2 ($ SLOT_NUM)) eqn: Heq;
  (val_help_H H; simpl in H); destruct H; tryfalse.
  rewrite Intlt_false_is_Zge in Hlt.
  rewrite Inteq_false_is_Zneq in Heq.
  rewrite Int.unsigned_repr in Hlt, Heq.
  lia.
  unfold SLOT_NUM. rewrite max_unsigned_val. lia.
  unfold SLOT_NUM. rewrite max_unsigned_val. lia.
  assert(Htrue: Int.unsigned v'1 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H2. int auto.
  hoare forward;[idtac|simpl;eauto..].
  rewrite Htrue. auto.
  destruct (Int.ltu ($ 64) v'1); auto.
  rewrite Htrue. auto.
  destruct (Int.eq v'1 ($ 64)); auto.
  destruct (Int.ltu ($ 64) v'1);
  destruct (Int.eq v'1 ($ 64)); auto.
  hoare_split_pure_all. hoare forward.
  sep lift 2%nat. eapply disj_split.
  left. sep auto.
  2: auto.
  2: auto.
  right. left.
  destruct (Int.ltu ($ 64) v'1) eqn: Hlt;
  destruct (Int.eq v'1 ($ 64)) eqn: Heq; val_help_H H0; simpl in H0; tryfalse.
  rewrite Intlt_true_is_Zlt in Hlt. rewrite Int.unsigned_repr in Hlt; [lia|rewrite max_unsigned_val; lia].
  rewrite Intlt_true_is_Zlt in Hlt. rewrite Int.unsigned_repr in Hlt; [lia|rewrite max_unsigned_val; lia].
  rewrite Inteq_true_is_Zeq in Heq. rewrite Int.unsigned_repr in Heq; try(rewrite max_unsigned_val); lia.
  eapply disj_rule. hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hv'1range: Int.unsigned v'1 < 64).
  destruct (Int.ltu ($ 64) v'1) eqn: Hlt;
  destruct (Int.eq v'1 ($ 64)) eqn: Heq;
  val_help_H H0; simpl in H0; destruct H0; tryfalse.
  rewrite Intlt_false_is_Zge in Hlt.
  rewrite Int.unsigned_repr in Hlt; try(rewrite max_unsigned_val); try lia.
  rewrite Inteq_false_is_Zneq in Heq.
  rewrite Int.unsigned_repr in Heq. lia.
  rewrite max_unsigned_val. lia.

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
  sep get rv. rewrite Htrue. auto.
  eauto. auto. lia. lia.
  rewrite Hv'7len. lia.
  2: eauto.
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'7len. lia.
  eapply eq_vptr. eauto.
  intros. eexists. sep cancel p_local. simpl. auto.
  eapply backward_rule1 with (p:=
  Aie false **
  Ais nil **
  Acs v'5 **
  Aisr v'6 **
  Aier v'3 **
   <|| v'4 ||>  **
  AOSCSpacePrioTbl (v'9 ↝ {v'10}) v'7 v'8
    v'11 **
  p_local OSLInv ct init_lg **
  LV cap1 @ Cap ∗ |-> v'0 **
  LV pCSpace1 @ CSPACE ∗ |-> nth_val'
  (Z.to_nat (Int.unsigned v'1))
  v'7 **
  LV func_capability @ long |-> Vint32 v'2 **
  LV destTask_Prio @ char_t |-> Vint32 v'1 **
  A_dom_lenv
    ((func_capability ↝ {long})
     :: (destTask_Prio ↝ {char_t})
        :: (pCSpace1 ↝ {CSPACE ∗})
           :: (cap1 ↝ {Cap ∗}) :: nil)
  ).
  intros.
  unfold AOSCSpacePrioTbl.
  sep auto.
  assert(HpCSpace1type: rule_type_val_match(Tptr CSPACE) (nth_val'
  (Z.to_nat (Int.unsigned v'1)) v'7)  = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'7len. lia.

  hoare forward.
  clear -HpCSpace1type.
  unfolds in HpCSpace1type.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned v'1)) v'7); tryfalse; auto.
  destruct a. auto.
  hoare forward; [idtac|simpl; eauto..].
  sep lift 2%nat. 
  eapply disj_split. left.
  sep auto.
  right. right.
  clear -HpCSpace1type H5.
  unfolds in HpCSpace1type.
  destruct (nth_val'(Z.to_nat (Int.unsigned v'1))
  v'7); tryfalse; auto.
  destruct a.
  unfold val_inj, val_eq in H5.
  tryfalse.
  eapply disj_rule. hoare_split_pure_all.
  eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hnotnull: nth_val'(Z.to_nat (Int.unsigned v'1))
  v'7 <> Vnull).
  clear -HpCSpace1type H6.
  unfolds in HpCSpace1type.
  destruct (nth_val'(Z.to_nat (Int.unsigned v'1))
  v'7); tryfalse; auto.
  unfold val_inj, val_eq in H6.
  destruct H6; tryfalse.
  clear H H0 H6.
  eapply backward_rule1.
  intros.
  sep lift 7%nat in H.
  eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:= Z.to_nat(Int.unsigned v'1)) in H.
  exact H.
  rewrite Hv'8len. lia.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure intro.

  
  (*unfold slots*)
  unfold ACSpace.
  destruct v'13. destruct p. destruct p. destruct p. destruct v'17.
  unfold Acnode.
  destruct c. destruct p.
  pure intro.
  rename H15 into Hirange.
  eapply backward_rule1.
  intros.
  sep lifts (7::nil)%nat in H15.
  eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'2)) in H15.
  exact H15.
  clear -Hv'2range. unfold SLOT_NUM in *.
  lia. auto.
  auto.
  pure intro.
  unfold ACap.
  destruct v'17. destruct c. destruct p.
  pure intro.
  rename H15 into Hptr.
  rewrite nth_val'_length_imp; eauto.
  (*cap1 ′ =ₑ&ₐ(((pCSpace1 ′ → cnode) .. slots)[func_capability ′]) .. capability;ₛ*)
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply assign_rule_lvar.
  intros. splits; intros.
  sep cancel cap1.
  exact H15. 
  intros. sep auto.
  intros.
  eapply calculate_rv_expr_id_addr.
  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep cancel pCSpace1.
        sep lift 26%nat in H15.
        eapply LV_to_Rv in H15; eauto.
        instantiate(2:=Z.to_nat(Int.unsigned v'2)).
        rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
        exact H15.
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

  eapply seq_rule.
  eapply if_rule2'.
  intros.
  eapply bop_rv.
  eapply lv_mapsto_to_rv.
  2:{
    eapply local_val_struct_member_addr.
    sep lift 2%nat in H15.
    rewrite Int.add_zero in H15.
    simpl typelen in H15.
    rewrite of_to_nat_unsignedv' in H15.
    exact H15.
    unfold Cap. eauto.
    unfold field_offset. simpl. eauto.
    simpl. eauto.
  }
  2:{
    rewrite Int.add_zero.
    rewrite Int.add_zero in H15.
    sep lift 5%nat in H15.
    simpl typelen in H15.
    rewrite <- addition_trans.
    rewrite Int.repr_unsigned.
    exact H15.
    lia.
  }
  simpl. auto.
  destruct_s s. unfold CAP_CATEGORY_TYPE. simpl. split; eauto.
  eauto.
  unfold val_inj, bop_eval. unfold val_eq.
  destruct (Int.eq i4 ($ 1)); eauto.
  simpl. eauto.

  (*cap1 ′ → cap_type =ₑ ′ 0;ₛ*)
  eapply seq_rule.
  pure intro.
  hoare_lifts_trms_pre(Aop).
  eapply assign_rule_aop.
  2:{
    intros.
    eapply local_val_struct_member_addr.
    {
      exact H21.
    }
    unfold Cap. eauto.
    unfold field_offset. simpl. eauto.
    simpl. unfold Content. eauto.
  }
  2:{
    intros. splits; intros.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    simpl typelen in *.
    sep lift 4%nat in H21.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned.
    exact H21.
    lia.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    simpl typelen in *.
    rewrite of_to_nat_unsignedv' in H21 at 1.
    rewrite <- addition_trans in H21 at 1. 
    sep cancel cap1.
    sep cancel ASlots.
    rewrite Int.repr_unsigned in H21.
    sep cancel 2%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep auto.
    clear -H4. int auto.
  }
  2:{
    intros.
    destruct_s s. simpl.
    splits; eauto.
  }
  eapply eq_int. auto.
  intros. 
  eexists. sep cancel p_local. simpl. auto.

  (*((cap1 ′ → cap_content) .. category)
.. category_content =ₑ ′ 0;ₛ*)
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
          sep lift 2%nat in H15.
          exact H15.
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
    sep lift 5%nat in H15.
    rewrite <- addition_trans.
    exact H15. lia.
    simpl typelen in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H15.
    rewrite Int.unsigned_repr in H15.
    rewrite of_to_nat_unsignedv' in H15.

    sep auto.
  Optimize Proof.
  Optimize Heap.
    clear -H4. int auto.
    lia.
    clear -H4. int auto.
    lia.
  }
  2:{
    intros.
    destruct_s s. simpl. splits; eauto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.

  (*((cap1 ′ → cap_content) .. category)
.. category_right =ₑ ′ 0;ₛ*)
  eapply assign_rule_aop.
  2:{
    intros.
    eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep lift 3%nat in H15.
          exact H15.
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
    rewrite Int.add_assoc.
    change ($ 4 +ᵢ  $ 4) with ($8).
    sep lift 6%nat in H15.
    rewrite <- addition_trans.
    exact H15. lia.
    simpl typelen in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H15.
    rewrite Int.unsigned_repr in H15.
    rewrite of_to_nat_unsignedv' in H15.
    rewrite Int.add_assoc in H15.
    change ($ 4 +ᵢ  $ 4) with ($8) in H15.
    sep auto.
   
    clear -H4. int auto.
    lia.
    clear -H4. int auto.
    lia.
  }
  2:{
    intros.
    destruct_s s. simpl. splits; eauto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.


  pure intro.
  (*IF (cap1 ′ → cap_type ==ₑ ′ CAP_OBJECT_TYPE)*)
  eapply if_rule2'.

  intros.
  eapply bop_rv.
  eapply lv_mapsto_to_rv.
  2:{
    eapply local_val_struct_member_addr.
    sep lift 2%nat in H19.
    rewrite Int.add_zero in H19.
    exact H19.
    unfold Cap. eauto.
    unfold field_offset. simpl.  eauto.
    simpl. eauto.
  }
  2:{
    simpl typelen in *.
    rewrite Int.add_zero.
    sep lift 5%nat in H19.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned.
    unfold Aptrmapsto in H19 at 1.
    exact H19.
    lia.
  }
  simpl. auto.
  destruct_s s. unfold CAP_OBJECT_TYPE. simpl. split; eauto.
  eauto.
  unfold bop_eval, val_inj. unfold val_eq.
  destruct(Int.eq i4 ($ 2)); eauto.
  simpl. eauto.

  eapply seq_rule.
  pure intro.
  hoare_lifts_trms_pre(Aop).
  eapply assign_rule_aop.
  2:{
    intros.
    eapply local_val_struct_member_addr.
    {
      exact H22.
    }
    unfold Cap. eauto.
    unfold field_offset. simpl. eauto.
    simpl. unfold Content. eauto.
  }
  2:{
    intros. splits; intros.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    simpl typelen in *.
    sep lift 4%nat in H22.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned.
    exact H22.
    lia.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    simpl typelen in *.
    rewrite of_to_nat_unsignedv' in H22 at 1.
    rewrite <- addition_trans in H22 at 1. 
    sep cancel cap1.
    sep cancel ASlots.
    rewrite Int.unsigned_repr in H22 at 1.
    sep cancel 2%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep cancel 1%nat 1%nat.
    
    sep auto.
    clear -H4. int auto.
    lia.
  }
  2:{
    intros.
    destruct_s s. simpl.
    splits; eauto.
  }
  eapply eq_int. auto.
  intros. 
  eexists. sep cancel p_local. simpl. auto.

  (*((cap1 ′ → cap_content) .. object) .. object_right =ₑ
′ 0;ₛ*)
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
          sep lift 2%nat in H19.
          exact H19.
        }
        unfold Cap. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero. eauto.
        simpl. unfold Content. eauto.
      }
      simpl. unfold Cap_Object. eauto.
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
    
    sep lift 5%nat in H19.
    rewrite <- addition_trans.
    exact H19. lia.
    simpl typelen in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H19.
    rewrite Int.unsigned_repr in H19.
    rewrite of_to_nat_unsignedv' in H19.
    
    sep auto.
  Optimize Proof.
  Optimize Heap.
    rewrite Int.add_assoc in H19.
    clear -H4. int auto.
    lia.
    clear -H4. int auto.
    lia.
  }
  2:{
    intros.
    destruct_s s. simpl. splits; eauto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.

  (*((cap1 ′ → cap_content) .. object) .. object_t =ₑ
〈 (Void) ∗ 〉NULL*)
  eapply assign_rule_aop.
  2:{
    intros.
    eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep lift 3%nat in H19.
          exact H19.
        }
        unfold Cap. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero. eauto.
        simpl. unfold Content. eauto.
      }
      simpl. unfold Cap_Object. eauto.
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
    change  ($ 4 +ᵢ  $ 4) with ($8).
    rewrite Int.add_assoc.
    change  ($ 4 +ᵢ  $ 8) with ($12).

    sep lift 7%nat in H19.
    rewrite <- addition_trans.
    exact H19. lia.
    simpl typelen in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H19.
    rewrite Int.unsigned_repr in H19.
    rewrite of_to_nat_unsignedv' in H19.
    change ($ 4 +ᵢ  $ 4) with ($8) in H19.
    rewrite Int.add_assoc in H19.
    change ($ 4 +ᵢ  $ 8) with ($12) in H19.
    sep auto.
    
    auto.
    clear -H4. int auto.
    lia.
    clear -H4. int auto.
    lia.
  }
  2:{
    intros.
    destruct_s s. simpl. splits; eauto.
  }
  eapply eq_vptr. eauto.
  intros.
  eexists. sep cancel p_local. simpl. auto.

  pure intro.
  (* RETURN 〈 char_t 〉 ′ CNODE_DELETE_FAILURE*)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl. unfold CNODE_COPY_FAILURE. splits; eauto.

  intros.
  unfold ucos_CNode_DeletePost'.
  rewrite Int.add_zero in H20.
  sep lifts (5::6::7::8::nil)%nat in H20.
  simpl typelen in H20.

  eapply fold_Cap in H20.
  sep lifts (4::5::1::6::nil)%nat in H20.
  eapply ASlots_fold_any_idx_frm in H20; eauto.
  sep lifts (5::6::nil)%nat in H20.
  rewrite addition_trans in H20 at 1.
  assert(v'1 = $ Z.of_nat(Z.to_nat(Int.unsigned v'1))).
  rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned. auto.
  rewrite H21 in H20 at 1.
  clear H21.
  eapply array_asrt_eq_frm in H20.
  sep lifts (7::8::2::nil)%nat in H20.
  eapply fold_Acnode in H20.
  sep lifts (1::7::8::9::10::nil)%nat in H20.
  eapply fold_ACSpace in H20; eauto.
  sep lifts (6::1::7::nil)%nat in H20.
  eapply ACSpaceAarray_fold_any_idx_frm in H20; eauto.
  2: lia.
  2: lia.
  2:{
    auto.
  }
  sep normal. sep eexists.
  sep lift 14%nat. 
  eapply disj_split.
  right. 
  sep normal.
  sep lift 3%nat. eapply disj_split.
  left.
  unfold AOSCSpacePrioTbl.
  sep auto; try(simpl; eauto).
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  clear -H15 H19.
  unfold bop_eval, val_inj, val_eq in *.
  destruct (Int.eq i4 ($ 1)) eqn: Heq1;
  destruct (Int.eq i4 ($ 2)) eqn: Heq2.
  destruct H15; tryfalse.
  destruct H15; tryfalse.
  destruct H19; tryfalse.
  rewrite Inteq_false_is_Zneq in Heq1, Heq2.
  unfold CAP_CATEGORY_TYPE, CAP_OBJECT_TYPE.
  rewrite Int.unsigned_repr in Heq1, Heq2.
  split; auto.
  int auto. int auto.
  lia.
  eapply nth_val_length_imp. auto.
  lia.
  clear -Hv'2range.
  unfold SLOT_NUM in *. lia.
  auto.
  eapply disj_rule.
  hoare_split_pure_all.
  eapply seq_rule.

  (*((pCSpace1 ′ → cnode) .. slots) [func_capability ′])
.. slot_type =ₑ ′ SLOT_NULL_CAP*) 
 eapply assign_rule_aop.
 2:{
  intros.
  eapply field_asrt_impl_struct_aop.
  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep cancel pCSpace1.
        sep lift 26%nat in H19.
        eapply LV_to_Rv in H19; eauto.
        instantiate(2:=Z.to_nat(Int.unsigned v'2)).
        rewrite of_to_nat_unsignedv'.
        rewrite Int.repr_unsigned.
        exact H19.
      }
      unfold CSPACE.
      eauto.
      unfold field_offset. simpl.
      eauto.
      simpl. unfold Cte. eauto.
    }
    unfold field_offset. simpl. rewrite Int.add_zero.
    change ($ 4 +ᵢ  $ 4) with ($8). eauto.
    instantiate(1:=2%nat). simpl. auto.
    auto. simpl. auto.
    unfold Slot. eauto.
  }
  simpl. eauto.
  unfold field_offset. simpl. auto.
 }
 2:{
    intros. split. intros.
    rewrite Int.add_zero.
    simpl typelen in *.
    rewrite Int.add_zero.
    sep lift 6%nat in H19.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
    exact H19.
    lia.
  Optimize Proof.
  Optimize Heap.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    simpl typelen.
    intros.
    sep auto.
    rewrite addition_trans. 
    rewrite of_to_nat_unsignedv' in H19. rewrite Int.repr_unsigned in H19.
    auto. lia.
 }
 2:{
    intros.
    destruct_s s. simpl. unfold SLOT_NULL_CAP. simpl; eauto.
 }
 eapply eq_int. auto.
 intros. sep auto.

 (* RETURN 〈 char_t 〉 ′ CNODE_NONE_FAULT *)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl. unfold CNODE_NONE_FAULT. split; eauto.
  intros.
  rewrite Int.add_zero in H19.
  rewrite Int.add_zero in H19.
  rewrite Int.add_zero in H19.
  rewrite Int.add_zero in H19.
  simpl typelen in H19.
  sep lifts (5::4::3::8::nil)%nat in H19.
  sep lift 3%nat in H19.
  rewrite Int.add_assoc in H19.
  change ($ 4 +ᵢ  $ 4) with ($8) in H19.
  sep lifts (2::3::1::4::nil)%nat in H19.
  rewrite addition_trans in H19.
  rewrite of_to_nat_unsignedv' in H19. 
  rewrite Int.repr_unsigned in H19.
  eapply fold_Cap in H19.
  sep lifts (5::3::1::6::nil)%nat in H19.
  rewrite <- addition_trans in H19.
  eapply ASlots_fold_any_idx_frm 
  with (slotsvl := (v'7++($ 0,($ 0,(($ 0, $ 0), v0)))::v'8)) in H19; eauto.
  sep lifts (5::6::nil)%nat in H19.
  rewrite addition_trans in H19 at 1.
  assert(v'1 = $ Z.of_nat(Z.to_nat(Int.unsigned v'1))).
  rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned. auto.
  rewrite H20 in H19 at 1.
  clear H20.
  eapply array_asrt_eq_frm in H19.
  sep lifts (7::8::2::nil)%nat in H19.
  eapply fold_Acnode in H19.
  sep lifts (1::7::8::9::10::nil)%nat in H19.
  eapply fold_ACSpace in H19; eauto.
  sep lifts (6::1::7::nil)%nat in H19.
  eapply ACSpaceAarray_fold_any_idx_frm 
  with(cspacevl:=v'12 ++
  (i2, i3,
  v'7 ++ ($ 0, ($ 0, ($ 0, $ 0, v0))) :: v'8,
  i0, l, v, i) :: v'14)in H19; eauto.
  2: lia.
  2: lia.
  2:{
    simpl.
    rewrite app_length.
    simpl. rewrite H8, H7.
    rewrite S_add_sub_S.
    lia.
    lia.
  }
  sep normal. sep eexists.
  sep lift 14%nat. 
  eapply disj_split.
  right.
  sep normal.
  sep lift 3%nat. eapply disj_split.
  right.
  sep normal.
  sep lift 2%nat. 
  eapply disj_split.
  left.
  unfold ucos_CNode_DeletePost'.
  unfold AOSCSpacePrioTbl.
  unfold Aarray.
  sep auto.
  2: rewrite get_capability_nth_mth_cspace_length_imp; eauto.

  splits.
  rewrite app_length.
  simpl.
  rewrite H6, H9. rewrite S_add_sub_S. lia. lia.
  rewrite app_length. simpl.
  rewrite H8, H7. rewrite S_add_sub_S. lia. lia.
  auto.
  unfold update_nth_cspace_slots_cap.
  unfold update_nth_cspace_slots_type.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  clear -H15.
  unfold val_inj, bop_eval, val_eq in H15.
  destruct (Int.eq i4 ($ 1)) eqn: Heq.
  rewrite Inteq_true_is_Zeq in Heq.
  rewrite Int.unsigned_repr in Heq. unfold CAP_CATEGORY_TYPE.
  auto. int auto. 
  destruct H15. tryfalse.

  rewrite app_length. simpl.
  rewrite H18, H16. rewrite S_add_sub_S.
  clear -Hv'2range.
  unfold SLOT_NUM in *.
  lia. unfold SLOT_NUM in *. lia.
  lia.
  eapply nth_val_length_imp. auto.
  lia.
  unfold SLOT_NUM in *. lia.
  rewrite app_length. simpl.
  rewrite H18, H16. unfold SLOT_NUM in *.
  rewrite S_add_sub_S. lia. lia.
  lia. auto. lia.

  hoare_split_pure_all.
  rewrite Int.add_zero.
  rewrite Int.add_zero.
  change ($ 4 +ᵢ  $ 4) with ($8).
  rewrite Int.add_assoc at 1.
  change ($ 4 +ᵢ  $ 8) with ($12).
  rewrite of_to_nat_unsignedv'.
  rewrite Int.repr_unsigned.
  eapply disj_rule.
  pure intro.


  eapply seq_rule.
  eapply assign_rule_aop.
 2:{
  intros.
  eapply field_asrt_impl_struct_aop.
  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep cancel pCSpace1.
        sep_lifts_trms_in H22 (Alvarmapsto func_capability).
        eapply LV_to_Rv in H22; eauto.
        instantiate(2:=Z.to_nat(Int.unsigned v'2)).
        rewrite of_to_nat_unsignedv'.
        rewrite Int.repr_unsigned.
        exact H22.
      }
      unfold CSPACE.
      eauto.
      unfold field_offset. simpl.
      eauto.
      simpl. unfold Cte. eauto.
    }
    unfold field_offset. simpl. rewrite Int.add_zero.
    change ($ 4 +ᵢ  $ 4) with ($8). eauto.
    instantiate(1:=2%nat). simpl. auto.
    auto. simpl. auto.
    unfold Slot. eauto.
  }
  simpl. eauto.
  unfold field_offset. simpl. auto.
 }
 2:{
    intros. split. intros.
    rewrite Int.add_zero.
    simpl typelen in *.
    rewrite Int.add_zero.
    sep lift 6%nat in H22.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
    exact H22.
    lia.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    simpl typelen.
    intros.
    sep auto.
  Optimize Proof.
  Optimize Heap.
    rewrite addition_trans. 
    rewrite of_to_nat_unsignedv' in H22. rewrite Int.repr_unsigned in H22.
    auto. lia.
 }
 2:{
    intros.
    destruct_s s. simpl. unfold SLOT_NULL_CAP. simpl; eauto.
 }
 eapply eq_int. auto.
 intros. sep auto.

 (* RETURN 〈 char_t 〉 ′ CNODE_NONE_FAULT *)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl. unfold CNODE_NONE_FAULT. split; eauto.
  intros.
  rewrite Int.add_zero in H22.
  rewrite Int.add_zero in H22.
  simpl typelen in H22.
  sep lifts (5::4::8::3::nil)%nat in H22.
  rewrite addition_trans in H22.
  rewrite of_to_nat_unsignedv' in H22. 
  rewrite Int.repr_unsigned in H22.
  eapply fold_Cap in H22.
  sep lifts (5::3::1::6::nil)%nat in H22.
  rewrite <- addition_trans in H22.
  eapply ASlots_fold_any_idx_frm 
  with (slotsvl := (v'7++($ 0,($ 0,(($ 0, i6), Vnull)))::v'8)) in H22; eauto.
  sep lifts (5::6::nil)%nat in H22.
  rewrite addition_trans in H22 at 1.
  assert(v'1 = $ Z.of_nat(Z.to_nat(Int.unsigned v'1))).
  rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned. auto.
  rewrite H23 in H22 at 1.
  clear H23.
  eapply array_asrt_eq_frm in H22.
  sep lifts (7::8::2::nil)%nat in H22.
  eapply fold_Acnode in H22.
  sep lifts (1::7::8::9::10::nil)%nat in H22.
  eapply fold_ACSpace in H22; eauto.
  sep lifts (6::1::7::nil)%nat in H22.
  eapply ACSpaceAarray_fold_any_idx_frm 
  with(cspacevl:= v'12 ++
  (i2, i3,
  v'7 ++
  ($ 0, ($ 0, ($ 0, i6, Vnull))) :: v'8, i0,
  l, v, i) :: v'14) in H22; eauto.
  2: lia.
  2: lia.
  2:{
    simpl.
    rewrite app_length.
    simpl. rewrite H8, H7.
    rewrite S_add_sub_S.
    lia.
    lia.
  }
  sep normal. sep eexists.
  sep lift 14%nat. 
  eapply disj_split.
  right.
  sep normal. sep lift 3%nat. 
  eapply disj_split. right.
  sep normal. sep lift 2%nat. 
  eapply disj_split. right.
  unfold ucos_CNode_DeletePost'.
  unfold AOSCSpacePrioTbl.
  sep auto; try(simpl; eauto).
  2: rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  splits.
  rewrite app_length.
  simpl.
  rewrite H6, H9. rewrite S_add_sub_S. lia. lia.
  rewrite app_length. simpl.
  rewrite H8, H7. rewrite S_add_sub_S. lia. lia.
  auto.
  unfold update_nth_cspace_slots_cap.
  unfold update_nth_cspace_slots_type.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  clear -H19. 
  unfold val_inj, bop_eval, val_eq in H19.
  destruct ( Int.eq i4 ($ 2)) eqn: Heq.
  rewrite Inteq_true_is_Zeq in Heq.
  rewrite Int.unsigned_repr in Heq.
  unfold CAP_OBJECT_TYPE. auto.
  int auto. tryfalse.
  rewrite app_length. simpl.
  rewrite H18, H16. rewrite S_add_sub_S.
  unfold SLOT_NUM in *. lia.
  unfold SLOT_NUM in *. lia.
  lia.
  eapply nth_val_length_imp. auto.
  lia.
  unfold SLOT_NUM in *. lia.
  rewrite app_length. simpl.
  rewrite H18, H16. unfold SLOT_NUM in *.
  rewrite S_add_sub_S.

  lia. lia.
  lia. unfold isptr. eauto. lia.

  hoare_split_pure_all.
  eapply pfalse_rule.
  Unshelve. all: auto.
Qed.