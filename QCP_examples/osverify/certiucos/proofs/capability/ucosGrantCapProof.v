Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import ucosGrantCapPure.
Require Import Lia.
Require Import ACSpace_defs.
Require Import CapSpec.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Set Nested Proofs Allowed.

Lemma ucos_Grant_Cap_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal ucos_Grant_Cap
                  vl logicl ucos_Grant_CapPre ct->
      Some r =
      BuildRetI os_internal ucos_Grant_Cap vl logicl ucos_Grant_CapPost ct->
      exists t d1 d2 s,
      os_internal ucos_Grant_Cap = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.  
    init spec.
    unfold nth_val in H4, H0, H.
    inverts H4.
    inverts H. inverts H0.
    hoare lifts (6::5::1::2::3::nil)%nat pre.
    eapply seq_rule.
    hoare forward.
    unfold val_inj.
    destruct (Int.ltu v'0 ($ CAP_NULL_CLASS)); auto.
    unfold val_inj.
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'0); auto.
    unfold val_inj, bool_or.
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS)
    v'0);
    destruct (Int.ltu v'0 ($ CAP_NULL_CLASS));
    val_help; simpl; auto.
    hoare_split_pure_all.
    eapply rete_rule'.
    intros.
    sep get rv.
    intros. unfold ucos_Grant_CapPost'.
    sep normal. sep eexists.
    sep lift 15%nat.
    eapply disj_split. left.
    sep auto.
    simpl; eauto.
    simpl; eauto.
    simpl; eauto.
    left.
    clear -H.
    clear -H.
    destruct (Int.ltu v'0 ($ CAP_NULL_CLASS)) eqn: Hlt1;
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'0) eqn: Hlt2;
    val_help_H H; simpl in H; destruct H; tryfalse; try(eapply Intlt_true_is_Zlt in Hlt1);
    try(eapply Intlt_true_is_Zlt in Hlt2); try (rewrite Int.unsigned_repr in Hlt1); 
    try (rewrite Int.unsigned_repr in Hlt2); try lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.


    eapply disj_rule.
    hoare_split_pure_all. eapply pfalse_rule.
    hoare_split_pure_all.
    assert(Htrue: Int.unsigned v' <=? Byte.max_unsigned = true).
    clear -H3. 
    change Byte.max_unsigned with 255.
    int auto.
    hoare forward.
    rewrite Htrue. auto.
    unfold val_inj.
    destruct (Int.ltu ($ 64) v'); auto.
    rewrite Htrue. auto.
    destruct (Int.eq v' ($ 64)); auto.
    unfold val_inj, bool_or.
    destruct (Int.ltu ($ 64) v');
    destruct (Int.eq v' ($ 64)); val_help; simpl; auto.
    hoare_split_pure_all.
    eapply rete_rule'.
    intros. sep get rv.
    intros.
    unfold ucos_Grant_CapPost'.
    sep normal. sep eexists.
    sep lift 15%nat.
    eapply disj_split. left.
    sep auto; simpl; eauto.
    right.
    left.
    destruct H0.
    unfold val_inj, bool_or in H0.
    destruct (Int.ltu ($ 64) v') eqn: Hlt;
    destruct (Int.eq v' ($ 64)) eqn: Heq; val_help_H H0; simpl in H0; tryfalse;
    try (eapply Intlt_true_is_Zlt in Hlt);
    try(eapply Inteq_true_is_Zeq in Heq);
    try (rewrite Int.unsigned_repr in Heq);
    try (rewrite Int.unsigned_repr in Hlt);try lia.
    rewrite max_unsigned_val. lia.
    rewrite max_unsigned_val. lia.
    rewrite max_unsigned_val. lia.
    rewrite max_unsigned_val. lia.
    eapply disj_rule. hoare_split_pure_all. eapply pfalse_rule.
    hoare_split_pure_all.
    assert(Hv'0range: CAP_NULL_CLASS<=Int.unsigned v'0<=CAP_CHANNEL_CLASS).
    clear -H.
    destruct (Int.ltu v'0 ($ CAP_NULL_CLASS)) eqn: Hlt1;
    destruct (Int.ltu ($ CAP_CHANNEL_CLASS) v'0) eqn: Hlt2;
    val_help_H H; simpl in H; destruct H; tryfalse.
    eapply Intlt_false_is_Zge in Hlt1, Hlt2.
    rewrite Int.unsigned_repr in Hlt1, Hlt2.
    lia.
    unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_NULL_CLASS. rewrite max_unsigned_val. lia.
    unfold CAP_NULL_CLASS, CAP_CHANNEL_CLASS in Hv'0range.
    assert(Hv'range: Int.unsigned v' < 64).
    clear -H0.
    destruct (Int.ltu ($ 64) v') eqn: Hlt;
    destruct (Int.eq v' ($ 64)) eqn: Heq;
    val_help_H H0; simpl in H0; destruct H0; tryfalse.
    eapply Intlt_false_is_Zge in Hlt.
    
    eapply Inteq_false_is_Zneq in Heq.
    rewrite Int.unsigned_repr in Hlt, Heq.
    lia.
    rewrite max_unsigned_val. lia.
    rewrite max_unsigned_val. lia.
    hoare remember (7::nil)%nat pre.
    unfold AOSCSpacePrioTbl.
    hoare_split_pure_all.
    assert(Htypematch: array_type_vallist_match CSPACE ∗ v'6).
    simpljoin. auto.
    eapply backward_rule1 with (p := AOSCSpacePrioTbl (v'8 ↝ {v'9}) v'6 v'7 v'10 **
    H1).
    intros. unfold AOSCSpacePrioTbl. sep auto.
    sep split in H4; auto.
    subst H1.
    clear H2.
    hoare lifts (2::3::4::5::6::7::nil)%nat pre.
    eapply seq_rule.
    eapply ift_rule'.
    intros.
    unfold AOSCSpacePrioTbl in H1.
    sep normal in H1.
    eapply bop_rv.
    eapply array_member_rv_g.
    unfold GAarray. sep normal. sep eexists.
    sep cancel OSCSpacePrioTbl.
    sep cancel Aarray.
    sep cancel A_dom_lenv.
    exact H1.
    simpl. auto. eauto.
    sep get rv.
    rewrite Htrue. auto.
    eauto. auto.
    lia. 
    lia.
    sep split in H1. destruct H2. rewrite H2.
    lia.
    2: eauto.
    sep split in H1. destruct H2. destruct H14.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite H2. lia.
    sep get rv.
    eauto.
    unfold val_inj, bop_eval, val_eq.
    assert(rule_type_val_match CSPACE ∗
    (nth_val' (Z.to_nat (Int.unsigned v'))
       v'6) = true).
    sep split in H1. destruct H2. destruct H14.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite H2. lia.
    unfold rule_type_val_match in H2.
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v')) v'6); tryfalse.
    auto.
    destruct a. auto.
    simpl. eauto.
    hoare_split_pure_all.
    eapply rete_rule'.
    intros. sep get rv.
    intros.
    unfold AOSCSpacePrioTbl in H2.
    sep normal. sep eexists.
    sep lift 18%nat.
    eapply disj_split.
    left.
    sep auto; simpl; eauto.
    right. right.
    assert(rule_type_val_match CSPACE ∗
    (nth_val' (Z.to_nat (Int.unsigned v'))
       v'6) = true).
    destruct H4. destruct H7.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite H4. lia.
    clear -H1 H7.
    unfold val_inj, bop_eval, val_eq in H1.
    unfold rule_type_val_match in H7.
    destruct (nth_val' (Z.to_nat (Int.unsigned v')) v'6); tryfalse; auto.
    destruct a. destruct H1. tryfalse.
   
    eapply disj_rule. eapply pfalse_rule.
    hoare_split_pure_all.

    Ltac p_local_go:= 
      try unfold p_local;
      try unfold CurTid;
      try unfold OSLInv;
      try unfold LINV;
      try unfold AOSExchandler;
      try good_frm_sovler;
      try go.
    assert(Hnotnull: nth_val'(Z.to_nat (Int.unsigned v'))
    v'6 <> Vnull).
    unfold val_inj, bop_eval, val_eq in H1.
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v'))
    v'6); destruct H1; tryfalse; auto.
    clear H H0 H1.

    (*第一句*)
    eapply backward_rule1.
    intros.

    assert(Hslotslen: length v'7 = 64%nat).
    {
      unfold AOSCSpacePrioTbl in H.
      sep split in H. destruct H0. destruct H12.
      auto.
    }
    sep lift 7%nat in H.
    eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:= Z.to_nat(Int.unsigned v')) in H.
    exact H.
    1:{
      rewrite Hslotslen.
      clear -Hv'range.
      lia.
    }
    auto. 
    hoare_split_pure_all.
    unfold ACSpace, Acnode.
    
    destruct v'12. destruct p. destruct p. destruct p. destruct v'16.
    destruct c. destruct p.
    pure intro.
    eapply backward_rule1.
    intros.
    sep normal in H.
    sep lift 7%nat in H. 
    eapply ASlots_unfold_any_idx_frm with(idx:= Z.to_nat(Int.unsigned v'0)) in H. 
    unfold ACap in H. 
    exact H. 
    unfold SLOT_NUM. lia.
    auto. sep split in H. auto.
    pure intro.
    rename H18 into Hnew_add.

    destruct v'16.
    destruct c.
    destruct p.
    eapply seq_rule.
    Require Import seplog_trm_tacs.
    hoare_lifts_trms_pre (Aop).
    eapply assign_rule_aop.
    2:{
      intros.
      assert(s|=Lv ((((OSCSpacePrioTbl ′ [destTask_Prio ′])
      → cnode) .. slots) [cap_Class ′])
    .. capability@ Cap == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4)).
      eapply cspace_to_capability_addr; eauto.
      assert(s
      |= Lv (((((OSCSpacePrioTbl ′ [destTask_Prio ′]) → cnode)
               .. slots) [cap_Class ′]) .. capability)
            .. cap_type @ Tint32 == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 0)).
      
      eapply field_asrt_impl_struct_aop; eauto.
      3:{ 
        unfold Cap in H18.
        instantiate (1:= Aemp).
        eapply astar_r_aemp_intro.
        exact H18.
      }
      simpl. auto.
      unfold field_offset. simpl. unfold Int.zero. auto.
      exact H19.
    }
    2:{
      intros.
      splits.
      intros.
      rewrite Int.add_zero.
      simpl typelen in H.
      sep lift 3%nat in H.
      rewrite  addition_trans in H. 
      exact H. lia. 
      intros.
      rewrite Int.add_zero in H. 
      rewrite <- addition_trans in H.
      simpl typelen.
      sep auto.
      lia.
    }
    2:{
      intros.
      destruct_s s.
      simpl.
      splits; eauto.
    }
    apply eq_int. splits; eauto.
    intros. 
    sep eexists. sep cancel p_local. simpl. auto.
    rewrite Int.add_zero.
    eapply seq_rule.
    eapply assign_rule_aop.
    2:{
      intros.
      assert(s|=Lv ((((((OSCSpacePrioTbl ′ [destTask_Prio ′])
      → cnode) .. slots) [cap_Class ′])
    .. capability)..cap_content)..category@ Cap_Category == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 0)).
      eapply cspace_to_category_addr; eauto.
      rewrite addition_trans.
      sep auto.
      simpl. lia. 
      eapply field_asrt_impl_struct_aop; eauto.
      3:{
        instantiate (1:=Aemp).
        eapply astar_r_aemp_intro.
        unfold Cap_Category in H18.
        exact H18.
      }
      simpl. eauto.
      unfold field_offset. simpl. eauto.
    }
    2:{
      intros.
      rewrite Int.add_zero.
      rewrite Int.add_zero.
      splits; intros.
      sep lift 4%nat in H. 
      exact H. 
      sep cancel 2%nat 1%nat. 
      sep cancel 2%nat 1%nat. 
      sep cancel 2%nat 1%nat. 
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.
      sep cancel ASlots.
      sep cancel Aarray_rm.
      sep cancel Aarray.
      sep cancel ACSpaceAarrayTptr.
      sep cancel ACSpaceAarrayTptr.
      sep cancel OSCSpacePrioTbl.
      sep semiauto.
    }
    2:{
      intros.
      destruct_s s.
      sep lift 27%nat in H.
      destruct H. simpljoin.
      simpl in H18, H20, H21. simpljoin1.
      simpl. rewrite H24.
      splits; eauto.
      apply mapstoval_load in H25. rewrite Int.unsigned_zero in H25.
      lets Hload: load_local H18 H25.
      eapply Hload.
      simpl. auto.
      auto.
    }
    apply eq_int. splits; eauto.
    intros. 
    sep eexists. sep cancel p_local. simpl. auto.
    (*第三句*)
    eapply seq_rule.
    eapply assign_rule_aop.
    2:{
      intros.
      assert(s|=Lv ((((((OSCSpacePrioTbl ′ [destTask_Prio ′])
             → cnode) .. slots) [cap_Class ′])
           .. capability)..cap_content)..category@ Cap_Category == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 0)).
      eapply cspace_to_category_addr; eauto.
      rewrite Int.add_zero in H. rewrite Int.add_zero in H. 
      rewrite addition_trans.
      sep cancel ASlots.
      sep cancel ASlots.
      sep cancel Aarray_rm.
      sep cancel Aarray.
      sep cancel ACSpaceAarrayTptr.
      sep cancel ACSpaceAarrayTptr.
      sep cancel OSCSpacePrioTbl.
      sep cancel 3%nat 1%nat. 
      sep cancel 2%nat 1%nat.
      sep cancel 1%nat 1%nat.
      sep cancel 1%nat 1%nat.
      
      sep semiauto.
      simpl. lia. 
      eapply field_asrt_impl_struct_aop.
      3:{
        instantiate(1:=Aemp).
        eapply astar_r_aemp_intro.
        rewrite Int.add_zero in H18.
        unfold Cap_Category in H18.
        exact H18.
      }
      simpl. eauto.
      unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    }
    2:{
      intros.
      splits; intros.
      rewrite Int.add_zero in H. rewrite Int.add_zero in H. 
      rewrite Int.add_assoc.
      assert(($ Z.of_nat 4 +ᵢ  $ 4) = $8) by auto.
      rewrite H18.
      sep lift 5%nat in H. 
      exact H. 
      rewrite Int.add_zero.
      rewrite Int.add_zero.
      sep cancel 2%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel ASlots.
      sep cancel Aarray_rm.
      sep cancel Aarray.
      sep cancel ACSpaceAarrayTptr.
      sep cancel ACSpaceAarrayTptr.
      sep cancel OSCSpacePrioTbl.
      sep cancel 2%nat 1%nat.
      rewrite Int.add_assoc in H at 1. 
      change ($ Z.of_nat 4 +ᵢ  $ 4) with ($8) in H.
      sep cancel 1%nat 1%nat. 
      sep cancel 1%nat 1%nat. 
      sep semiauto.
    }
    2:{
      intros.
      eapply bop_rv.
      eapply lv_mapsto_to_rv.
      2:{
      assert(s|=Lv ((((((OSCSpacePrioTbl ′ [destTask_Prio ′])
      → cnode) .. slots) [cap_Class ′])
      ..capability)..cap_content)..category@ Cap_Category == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 0)).
      eapply cspace_to_category_addr; eauto.
      rewrite addition_trans.
      rewrite Int.add_zero in H. rewrite Int.add_zero in H. 
      sep cancel ASlots.
      sep cancel Aarray_rm.
      sep cancel Aarray.
      sep cancel ACSpaceAarrayTptr.
      sep cancel ACSpaceAarrayTptr.
      sep cancel OSCSpacePrioTbl.
      sep cancel 3%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel 1%nat 1%nat. 
      sep cancel 1%nat 1%nat. 
      sep semiauto.
      simpl. lia.
      rewrite Int.add_zero in H18.
      eapply field_asrt_impl_struct_aop; eauto.
      3:{
        instantiate(1:=Aemp).
        eapply astar_r_aemp_intro.
        unfold Cap_Category in H18.
        exact H18.
      }
        simpl. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    }
    2:{
      rewrite Int.add_zero in H. rewrite Int.add_zero in H. 
      rewrite Int.add_assoc.
      assert($ Z.of_nat 4 +ᵢ  $ 4 = $8) by auto.
      rewrite H18.
      clear H18.
      sep lift 5%nat in H. 
      unfold Aptrmapsto in H at 1.
      exact H. 
    }
    simpl. auto.
    destruct_s s. simpl. splits; eauto.
    simpl. eauto.
    eauto.
    simpl. eauto.
  }
  eapply eq_int. splits; eauto.
  intros.
  sep eexists. sep cancel p_local. simpl. auto.

  (*第四句*)
  eapply seq_rule.
  eapply assign_rule_aop.
  2:{
    intros.
    assert(s|=Lv ((((((OSCSpacePrioTbl ′ [destTask_Prio ′])
             → cnode) .. slots) [cap_Class ′])
           .. capability)..cap_content)..category@ Cap_Category == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 0)).
    eapply cspace_to_category_addr; eauto.

    rewrite addition_trans.
    rewrite Int.add_assoc in H at 1.
    assert($ Z.of_nat 4 +ᵢ  $ 4 = $8) by auto.
    rewrite H18 in H. clear H18.
    sep cancel ASlots.
    sep cancel Aarray_rm.
    sep cancel Aarray.
    sep cancel ACSpaceAarrayTptr.
    sep cancel ACSpaceAarrayTptr.
    sep cancel OSCSpacePrioTbl.
    sep cancel 4%nat 1%nat. 
    sep cancel 3%nat 1%nat. 
    sep cancel 2%nat 1%nat. 
    sep cancel 1%nat 1%nat. 
    sep semiauto.
    simpl. lia.
    eapply field_asrt_impl_struct_aop.
    3:{
      instantiate(1:=Aemp).
      eapply astar_r_aemp_intro.
      unfold Cap_Category in H18.
      exact H18.
    }
    simpl. eauto.
    unfold field_offset. simpl. rewrite Int.add_zero. eauto.
  }
  2:{
    intros. splits; intros.
    rewrite Int.add_zero.
    exact H. 
    rewrite Int.add_zero in H.
    sep cancel ASlots.
    sep cancel ASlots.
    sep cancel Aarray_rm.
    sep cancel Aarray.
    sep cancel ACSpaceAarrayTptr.
    sep cancel ACSpaceAarrayTptr.
    sep cancel OSCSpacePrioTbl.
    sep cancel 1%nat 1%nat. 
    sep cancel 1%nat 1%nat. 
    sep cancel 1%nat 1%nat. 
    sep cancel 1%nat 1%nat. 
    sep semiauto.
  }
  2:{
    intros.
    eapply bop_rv.
    eapply lv_mapsto_to_rv.
    2:{
    assert(s|=Lv ((((((OSCSpacePrioTbl ′ [destTask_Prio ′])
    → cnode) .. slots) [cap_Class ′])
  .. capability)..cap_content)..category@ Cap_Category == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 0)).
    eapply cspace_to_category_addr; eauto.
    rewrite addition_trans.
    rewrite Int.add_assoc in H at 1.
    assert($ Z.of_nat 4 +ᵢ  $ 4 = $8) by auto.
    rewrite H18 in H. 
    clear H18.
    sep cancel ASlots.
    sep cancel ASlots.
    sep cancel Aarray_rm.
    sep cancel Aarray.
    sep cancel ACSpaceAarrayTptr.
    sep cancel ACSpaceAarrayTptr.
    sep cancel OSCSpacePrioTbl.
    sep cancel 4%nat 1%nat.
    sep cancel 3%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 1%nat 1%nat.
    sep semiauto.
    simpl. lia.
    eapply field_asrt_impl_struct_aop.
    3:{
      instantiate(1:=Aemp).
      eapply astar_r_aemp_intro.
      rewrite Int.add_zero in H18.
      unfold Cap_Category in H18.
      exact H18.
    }
    simpl. eauto.
    unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    }
    2:{
      unfold Aptrmapsto in H at 1.
      exact H. 
    }
    simpl. auto.
    sep lift 26%nat in H. 
    destruct_s s. destruct H. simpljoin.
    simpl in H18, H20, H21. simpljoin1.
    simpl. rewrite H24. splits; eauto.
    eapply mapstoval_load in H25.
    lets Hload: load_local H18 H25.
    eapply Hload. 
    simpl. auto. auto.
    eauto.
    eauto.
    simpl. eauto.
  }
  eapply eq_int. splits; eauto.
  intros.
  sep eexists. sep cancel p_local. simpl. auto.

  (*第五句*)
  
  eapply rete_rule'.
  intros.
  destruct_s s. simpl. splits; eauto.
  intros.
  
  unfold ucos_Grant_CapPost'. 
  sep normal. sep eexists.
  sep lift 18%nat.
  eapply disj_split. right.
  sep cancel Aie. sep cancel Aier.
  sep cancel Ais. sep cancel Acs.
  sep cancel Aisr.
  sep cancel A_dom_lenv.
  sep cancel Aop.
  sep split; eauto.
  unfold update_nth_cspace_slots_cap.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  change($ Z.of_nat 4) with ($4) in H.
  remember ((i1 +ᵢ  $ 8) +ᵢ  Int.mul ($ Z.of_nat 20) v'0 +ᵢ $4) as i520.
  sep lifts (3::2::1::6::nil)%nat in H.
  rewrite Int.add_assoc in H.
  change ($ Z.of_nat 0 +ᵢ  $ 4) with ($4) in H.
  rewrite Int.add_assoc in H.
  change (($ 4 +ᵢ  $ 4)) with ($8) in H.
  eapply fold_Cap in H. 
  subst i520.
  sep lifts (2::3::1::4::nil)%nat in H. 
  rewrite <- addition_trans in H.
  2: lia. 
  assert(20 = typelen Slot)%nat by auto.
  rewrite H18 in H at 1.
  rewrite H18 in H at 1.
  rewrite H18 in H at 1.
  clear H18.
  sep split in H.
  eapply ASlots_fold_any_idx_frm with 
  (slotsvl :=(v'6 ++ (v'12, ($ CAP_CATEGORY_TYPE, (v'0, Int.or (i6&ᵢ$ 4095) v'1, v0))) :: v'7)) in H; eauto. 
  3:{
    rewrite app_length.
    rewrite H0.
    simpl length. rewrite Hnew_add.
    rewrite S_add_sub_S. auto with arith.
    unfold SLOT_NUM. lia.
    clear -H17.
    unfold SLOT_NUM. lia.
  }
  sep lifts (6::7::1::nil)%nat in H. 
  eapply fold_Acnode in H. 
  sep lifts (1::6::7::8::9::nil)%nat in H.
  eapply fold_ACSpace  in H; eauto. 
  2:{
    rewrite app_length.
    rewrite H0.
    simpl.
    rewrite Hnew_add.
    rewrite S_add_sub_S. auto with arith.
    unfold SLOT_NUM. lia.
    clear -H17.
    unfold SLOT_NUM. lia.
  }
  sep lifts (5::1::6::nil)%nat in H. 
  eapply ACSpaceAarray_fold_any_idx_frm in H; eauto.
  2: lia.
  3:{
    simpl.
    rewrite app_length.
    simpl. rewrite H2, H14.
    rewrite S_add_sub_S.
    lia.
    lia.
  }
  sep lift 2%nat in H. 
  sep cancel p_local.
  sep cancel destTask_Prio.
  sep cancel cap_Class.
  sep cancel cap_Right.
  eapply fold_AOSCSpacePrioTbl in H; eauto.
  unfold AOSCSpacePrioTbl in H.
  sep auto.
  
 
  rewrite app_length.
  simpl.
  rewrite H1, H15.
  rewrite S_add_sub_S. lia. lia.
  rewrite app_length.
  simpl.
  rewrite H2, H14. rewrite S_add_sub_S.
  lia. lia.
  rewrite nth_val_length_imp; eauto.
  clear -Hv'range. lia.
  clear -Hv'range. lia.
  unfold SLOT_NUM. lia.
  sep split in H.
  auto. auto. auto.
  splits.
  rewrite app_length.
  simpl.
  rewrite H1, H15.
  rewrite S_add_sub_S. lia. lia.
  unfold update_nth_cspace_slots_cap.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite app_length. simpl.
  rewrite H2, H14.
  rewrite S_add_sub_S. lia.
  lia. auto.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  Unshelve.
  all: auto.
  exact Vnull.
  exact Vnull.
  exact Vnull.
Qed.



  

