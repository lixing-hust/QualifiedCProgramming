Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import include_frm.
Require Import sep_auto.
Require Import CapPure.
Require Import math_auto.
Require Import Lia.
Require Import ACSpace_defs.
Require Import CNodeDelRecPure.
Require Import CapSpec.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.

Set Keyed Unification.



Lemma CNode_delete_recursive_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal CNode_delete_recursive
                  vl logicl CNode_delete_recursivePre ct->
      Some r =
      BuildRetI os_internal CNode_delete_recursive vl logicl CNode_delete_recursivePost ct->
      exists t d1 d2 s,
      os_internal CNode_delete_recursive = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
    init spec.
    simpl in H0, H, H4.
    inverts H0. inverts H. inverts H4.
    rename H5 into H4.
    rename H6 into H5.
    rename H7 into H6.
    assert(H7: Int.unsigned v'3 >= 0) by int auto.
    unfold AOSCSpacePrioTbl.
    hoare_split_pure_all.
    assert(Hv'9len: length v'9 = 64%nat).
    simpljoin. auto.
    assert(Hv'10len: length v'10 = 64%nat).
    simpljoin. auto.
    assert(Harraytype: array_type_vallist_match CSPACE ∗ v'9).
    simpljoin. auto.
    eapply backward_rule1 with(p:=Aie false **
    Ais nil **
    Acs v'7 **
    Aisr v'8 **
    Aier v'5 **
     <|| v'6 ||>  **
    AOSCSpacePrioTbl (v'11 ↝ {v'12}) v'9 v'10
      v'13 **
    ASeminfo (v'16 ↝ {v'17}) v'18 **
    APthreadMutex (v'19 ↝ {v'20}) v'21 **
    AMqAttr (v'22 ↝ {v'23}) v'24 **
    AOSCSpaceObjectPointer v'25 **
    AOSTCBPrioTbl v'26 v'27 v'28 v'29 v'30 **
    p_local OSLInv ct init_lg **
    LV x @ long |-> v'1 **
    LV cap1 @ Cap ∗ |-> v'0 **
    LV i @ long |-> v' **
    LV func_capability @ long |-> Vint32 v'4 **
    LV func_capType @ char_t |-> Vint32 v'3 **
    LV dest_space @ CSPACE ∗ |-> Vptr v'2 **
    A_dom_lenv
      ((func_capability ↝ {long})
       :: (func_capType ↝ {char_t})
          :: (dest_space ↝ {CSPACE ∗})
             :: (i ↝ {long})
                :: (cap1 ↝ {Cap ∗})
                   :: (x ↝ {long}) :: nil)).
    (*i = 0*)
    intros. 
    unfold AOSCSpacePrioTbl.
    sep auto.
    clear H. 
    assert(Hv'3:Int.unsigned v'3 <=?
    Byte.max_unsigned = true).
    change Byte.max_unsigned with 255.
    clear -H2. int auto.
    hoare forward.

    assert(Hgets: get v'13 v'2 = Some v'14) by auto.
    (*展开ACSpace结构*)
    intros.
    unfold ptrvl_to_cspace_to_ptrvl in H9.
    destruct H9.
    eapply H0 in H4.
    eapply backward_rule1.
    intros.
    sep lift 8%nat in H1.
    eapply AOSCSpacePrioTbl_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned v'14)) in H1.
    exact H1.
    unfold AOSCSpacePrioTbl in H1. 
    sep split in H1. 
    destruct H9.
    destruct H18.
    rewrite H18. lia.
    clear -H4. 
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    pure intro.
    assert(v'2 = v'36).
    clear -H4 H11.
    unfold nat_of_Z in H4.
    assert(nth_val(Z.to_nat(Int.unsigned v'14))
    (v'34 ++Vptr v'36 :: v'35) =Some (Vptr v'36)).
    eapply nth_val_length_imp; auto.
    rewrite H in H4. 
    inverts H4. auto.
    subst v'36.
    Open Scope Z_scope.
    unfold ACSpace.
    destruct v'32. destruct p. destruct p. destruct p. destruct v'2.
    hoare_split_pure_all.
    eapply seq_rule.
    Require Import seplog_trm_tacs.
    hoare_lifts_trms_pre (Aop).
    eapply encrit2_rule'.
    intros.
    sep lifts (15::16::12::13::14::nil)%nat in H16.
    exact H16.
    eapply GoodI_I.
    Ltac p_local_go:= 
        try unfold p_local;
        try unfold CurTid;
        try unfold OSLInv;
        try unfold LINV;
        try unfold AOSCSpacePrioTbl;
        try unfold AOSCSpaceObjectPointer;
        try good_frm_sovler;
        try go.
    p_local_go.
    eapply GoodFrm_Aarray_rm.
    eapply seq_rule.
    eapply calle_rule_lvar'.
    unfold Cap_spec.
    simpl. unfold Check_Cap_Type_spec_weak.
    eauto.
    intros.
    eapply rvl_elim. sep get rv.
    eapply rvl_elim. sep get rv.
    rewrite Hv'3. auto.
    eapply rvl_elim. 
    2: eapply rvl_nil.
    eapply cast_rv_tint32_tint8.
    eapply lv_mapsto_to_rv.
    2:{
        eapply local_val_struct_member_addr.
        sep cancel dest_space.
        eauto.
        unfold CSPACE. eauto.
        unfold field_offset. simpl.
        rewrite Int.add_zero. eauto.
        simpl. eauto.
    }
    2:{
       sep lift 15%nat in H16.
       unfold MaxChildNum in H16.
       change (typelen UNION cspace ⋆) with 4%nat in H1.
       change (Z.of_nat (typelen CSPACE ∗)) with 4 in H1.
       assert(Int.mul ($ 64)
       ($ Z.of_nat 4) = $256).
       simpl. clear -H2.
       int auto.
       rewrite H17 in H16 at 1.
       
       change 5108 with (Z.of_nat(typelen(Cte))).
       rewrite Int.add_assoc in H16 at 1.
       rewrite Int.add_assoc in H16 at 1.
       rewrite Int.add_assoc in H16 at 1.
       assert(($ 4 +ᵢ
       ($ 256 +ᵢ  ($ 4 +ᵢ  $ Z.of_nat (typelen Cte)))) = 
       ($ Z.of_nat (typelen Cte) +ᵢ
        ($ 4 +ᵢ  ($ 256 +ᵢ  $ 4)))).
       clear -H2.
       int auto; (try simpl typelen; repeat(try rewrite Int.unsigned_repr); try (rewrite max_unsigned_val); 
       try lia).
       rewrite H18.
       clear H17 H18.
       unfold Aptrmapsto in H16 at 1.
       exact H16.
    }
    simpl. auto.
    simpl. eauto.
    intros. unfold getasrt. unfold Check_Cap_TypePre.
    unfold Check_Cap_TypePre'.
    sep normal. sep eexists.
    sep cancel Aie. sep cancel Ais.
    sep cancel Acs. sep cancel Aisr. sep cancel Aier.
    sep cancel Aop. sep cancel AOSTCBPrioTbl.
    sep cancel p_local.

    sep cancel ASeminfo.
    sep cancel APthreadMutex. sep cancel AMqAttr.
    sep cancel AOSCSpaceObjectPointer.
    sep lifts (5::6::7::8::9::nil)%nat in H16.
    eapply fold_ACSpace in H16; eauto.
    sep lifts (5::1::6::nil)%nat in H16.
    eapply ACSpaceAarray_fold_any_idx_frm in H16; eauto.
    sep lifts (3::4::nil)%nat in H16.
    rewrite addition_trans in H16 at 1.
    assert(v'14 = ($ Z.of_nat(Z.to_nat(Int.unsigned v'14)))).
    rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned. auto.
    rewrite H17 in H16 at 1.
    clear H17.
    eapply array_asrt_eq_frm in H16.
    unfold AOSCSpacePrioTbl.
    unfold Aarray.
    sep cancel OSCSpacePrioTbl. sep cancel Aarray'.
    sep cancel ACSpaceAarrayTptr.
    sep split; [idtac|simpl; eauto..].
    sep cancel x. eauto.  
    clear -H1.
    simpljoin.
    rewrite inline_bittblfunctions.mutexpost_intlemma1; auto.
    unfold OS_LOWEST_PRIO in H0. lia. 
    auto.
    Optimize Proof.
    Optimize Heap.
    unfolds. splits; auto.
    lia. eapply nth_val_length_imp; eauto. 
    simpl. lia. lia. lia. 
    p_local_go.
    unfolds. intros. 
    unfold getasrt in H16. 
    unfold Check_Cap_TypeWeakPost in H16.
    unfold Check_Cap_TypePost'' in H16.
    sep normal in H16. sep destruct H16.
    sep lift 20%nat in H16.
    eapply disj_split in H16.
    destruct H16. sep split in H16.
    subst v0. auto.
    sep split in H16. 
    clear -H17. simpljoin.
    auto.
    simpl. rewrite Hv'3.
    rewrite inline_bittblfunctions.mutexpost_intlemma1.
    change Byte.max_unsigned with 255.
    assert(Int.unsigned i <=? 255 = true).
    clear -H1. simpljoin.
    unfold OS_LOWEST_PRIO in H0.
    int auto.
    rewrite H16. auto.
    clear -H1. simpljoin.
    unfold OS_LOWEST_PRIO in H0. lia. 
    intros.
    unfold getasrt in H16. unfold Check_Cap_TypeWeakPost in H16.
    unfold Check_Cap_TypePost'' in H16.
    sep normal in H16. sep destruct H16.
    eexists. sep cancel p_local.
    simpl. auto.
    intros.
    unfold getasrt in H16. unfold Check_Cap_TypePre in H16.
    unfold Check_Cap_TypePre' in H16.
    sep normal in H16. sep destruct H16.
    eexists. sep cancel p_local.
    simpl. auto.
    unfold getasrt. unfold Check_Cap_TypeWeakPost.
    unfold Check_Cap_TypePost''.

    hoare_split_pure_all.
    inverts H21.
    eapply backward_rule1. intros.
    sep lift 14%nat in H21.
    eapply disj_split in H21.
    exact H21.
    eapply disj_rule.
    (*第一种情况*)
    {
    clear H46 H47 H49.
    hoare_split_pure_all.

    inverts H21.
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply excrit2_rule'.
    intros.
    sep lifts (4::5::1::2::3::nil)%nat in H21.
    exact H21.
    eapply GoodI_I.
    p_local_go. 
    eapply backward_rule1.
    intros.
    sep lift 7%nat in H21.
    eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:= Z.to_nat(Int.unsigned v'14)) in H21; eauto.
    
    rewrite app_length. simpl.
    rewrite app_length in Hv'10len. simpl in Hv'10len.
    rewrite Hv'10len. lia.
    clear -H4. eapply nth_val_nth_val'_some_eq in H4. 
    rewrite H4. auto.
    hoare_split_pure_all.
    unfold ACSpace.
    destruct v'5, p, p, p, v'12.
    pure intro.
    eapply list_map_eq3 in H21.
    destruct H21. destruct H17.
    subst v'34. inverts H17. subst v'35.
    eapply list_map_eq3 in H22.
    destruct H22.  destruct H17.
    subst v'31. inverts H17. subst v'33.
    rename H29 into Hl0len.
    remember (v'2 ++ (c0, i3, l0, v0, i2) :: v'6) as ls. 
    rewrite <- Heqls in *.
    eapply seq_rule.
    
    instantiate (1:=(EX ls',   
    Aarray' (v'40 ↝ {v'41}) 64 CSPACE ∗
    (v'8 ++ Vptr (b0 ↝ {i4}) :: v'11) **
  ACSpaceAarrayTptr 64 (v'8 ++ Vptr (b0 ↝ {i4}) :: v'11)
    ls' v'50 **
    <|| v'37 ||> ** 
    LV cap1 @ Tptr Cap
    |-> v'0 ** 
   G& OSCSpacePrioTbl @
   Tarray (Tptr CSPACE) 64 == (v'40, v'41)**
  Aie false **
  Ais nil **
  Acs v'7 **
  Aisr v'39 **
  Aier v'36 **
  ASeminfo (v'42, v'43) v'51 **
  APthreadMutex (v'44, v'45) v'52 **
  AMqAttr (v'46, v'47) v'53 **
  AOSCSpaceObjectPointer v'54 **
  AOSTCBPrioTbl v'55 v'56 v'57 v'58 v'59 **
  p_local OSLInv ct init_lg **
  LV os_code_defs.x @ Tint32 |-> (V$ SLOT_NUM) **
  LV ios_cap_defs.i @ Tint32 |-> (V$ 0) **
  LV func_capability @ long |-> Vint32 v'9 **
  LV func_capType @ Tint8 |-> Vint32 v'10 **
  LV dest_space @ CSPACE ∗ |-> Vptr (b0↝ {i4}) **
  A_dom_lenv
    ((func_capability, Tint32)
     :: (func_capType, Tint8)
        :: (dest_space, Tptr CSPACE)
           :: (ios_cap_defs.i, Tint32)
              :: (cap1, Tptr Cap)
                 :: (os_code_defs.x,
                    Tint32) :: nil) ** 
  [|exists n_class, reset_nth_cspace_slot_option v'14
    (Z.to_nat (x)) n_class ls ls'|]
)). 
    eapply forward_rule2.
    eapply ift_rule''.
    intros. symbolic_execution.
    hoare_split_pure_all. 
    rewrite Int.eq_true in H16.
    unfold val_inj, notint, Int.notbool in H16.
    assert(Int.eq Int.one Int.zero = false) by auto.
    rewrite H17 in H16.
    false.
    simpljoin. tryfalse.
    intros.
    destruct H16.
    sep split in H16.
    exact H16.
    sep split in H16.
    rewrite Int.eq_true in H17.
    sep lifts (2::3::nil)%nat in H16.
    rewrite addition_trans in H16.
    assert(v'14 = $(Z.of_nat(Z.to_nat (Int.unsigned v'14)))).
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned. auto.
    rewrite H37 in H16 at 1.
    eapply array_asrt_eq_frm in H16.
    clear H37.
    sep lifts (4::5::6::7::8::nil)%nat in H16.
    eapply fold_ACSpace in H16; eauto.
    sep lifts (4::1::5::nil)%nat in H16.
    eapply ACSpaceAarray_fold_any_idx_frm in H16; eauto.
    sep auto.
    unfold reset_nth_cspace_slot_option.
    exists (Z.to_nat SLOT_NUM).
    splits. unfolds. auto.
    assert( (0 <=? Z.to_nat SLOT_NUM)%nat = true).
    unfold SLOT_NUM. 
    clear -H1. int auto.
    assert((Z.to_nat SLOT_NUM <? Z.to_nat SLOT_NUM)%nat = false).
    clear -H1. unfolds SLOT_NUM. int auto.
    rewrite H18, H21. simpl.  auto.
    lia. lia. lia.
    auto. simpl. lia.
    2:{
        rewrite H12. auto.
    }
    2:{
        rewrite H13. auto.
    }
    2:{
        rewrite H11. auto.
    }
    2:{
        rewrite H14. auto.
    }
    hoare_split_pure_all.
    remember v'3 as ls'.
    hoare_lifts_trms_pre(
        Alvarmapsto ios_cap_defs.i
    ).
    (*提前写出的一些成立的前提*)
    assert(Hchildlen: length(child v'14 ls v'50) = Z.to_nat(Int.unsigned i3)).
    {
        unfold child. 
        rewrite Heqls.
        rewrite nth_cspace_length_imp; auto. 
        assert(Z.to_nat (Int.unsigned i3 )<= length l0)%nat.
        rewrite Hl0len. unfold MaxChildNum. lia.

        eapply reverse_map_len; eauto. 
    }
    


    (*ls'和ls之间的关系*)
    rename H16 into Hls2ls'.
    destruct Hls2ls'.
    rename x into n_class_x.
    rename H16 into Hls2ls'.
    assert(Hls'len: length ls'= 64%nat).
    assert(length ls' = length ls).
    unfold reset_nth_cspace_slot_option in Hls2ls'.
    destruct Hls2ls'.
    destruct ((0 <=? n_class_x)%nat &&
    (n_class_x <? Z.to_nat SLOT_NUM)%nat).
    rewrite <- H17.
    eapply reset_nth_cspace_slot_len_eq.
    rewrite H17. auto.
    rewrite H16. subst ls. 
    rewrite app_length. simpl.
    rewrite H13, H12.
    rewrite S_add_sub_S. lia.
    lia. 
    Optimize Proof.
    Optimize Heap.
    assert(Hlsls'similar: child_similar ls ls').
    eapply reset_nth_cspace_slot_option_child_similar; eauto.
    lets Hirange: unsigned_ge0 i3. 
    assert(Int.unsigned i3 > 0 \/ Int.unsigned i3 = 0) by lia.
    clear Hirange.
    destruct H16 as [Higt0 | Hieq0].
    (*孩子的至少存在一个*)
    assert(Hexists: exists x l, (child v'14 ls v'50) = x :: l).
    {
        destruct (child v'14 ls v'50). 
        simpl in Hchildlen. lia. 
        exists i l. 
        auto.  
    }
    destruct Hexists. destruct H16.
    rename H16 into Hchildhead.
    
    hoare remember (1::3::19::21::nil)%nat pre.
    (*循环不变式*)
    eapply backward_rule1 with (p:=
    (EX idx l1 v l2  ls'',
    LV ios_cap_defs.i @ long |-> (V$ (Z.of_nat idx)) **
    [|((S idx) <= Z.to_nat(Int.unsigned i3))%nat|] **
    LV func_capability @ long |-> Vint32 v'9 **
    LV dest_space @ CSPACE ∗
    |-> Vptr (b0 ↝ {i4}) ** 
    ACSpaceAarrayTptr 64%nat (v'8 ++ Vptr (b0 ↝ {i4}) :: v'11) ls'' v'50 **
    [|child v'14 ls v'50 = (l1 ++ v :: l2)|] **
    [|length l1 = idx /\ length l2 = (Z.to_nat(Int.unsigned i3) - (S idx))%nat|] ** 
    [|reset_descendents_cspace_list_slot l1 (Z.to_nat(Int.unsigned v'9)) v'50 ls' ls''|]
    ** H16) 
    (*描述儿子及其后代的清零情况*)
    \\//
    (EX l1 ls'',
    LV ios_cap_defs.i @ long |-> Vint32 i3 **
    LV func_capability @ long |-> Vint32 v'9** 
    LV dest_space @ CSPACE ∗
    |-> Vptr (b0 ↝ {i4}) ** 
    ACSpaceAarrayTptr 64%nat (v'8 ++ Vptr (b0 ↝ {i4}) :: v'11) ls'' v'50 **
    [|child v'14 ls v'50 = l1|] **
    [|reset_descendents_cspace_list_slot l1 (Z.to_nat(Int.unsigned v'9)) v'50 ls' ls''|] ** H16)
    ).

    intros.
    left.
    sep eexists.
    instantiate(5:=0%nat). 
    sep split.
    2: eapply reset_descendents_cspace_list_slot_nil.
    subst ls'. 
    sep cancel H16. sep cancel 1%nat 1%nat. 
    sep cancel 2%nat 1%nat. 
    sep cancel 2%nat 1%nat. auto.
    split; eauto.

    2:{
        simpl.
        eapply Hchildhead.
    }
    rewrite Hchildhead in Hchildlen.
    clear -Hchildlen H9.
    simpl in Hchildlen. lia.
    lia.
    
    (*进入循环已经完成, 下面需要证明循环间的递推关系*)
    (*while statement*)
   
    eapply seq_rule.
    eapply while_rule with (tp := Int32u).
    intros.
    destruct H17.
    sep destruct H17.
    eexists.

    eapply while_statement_val.
    6:{
        sep split in H17.
        sep lifts (1::4::3::nil)%nat in H17.
        exact H17.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H17. 
    assert(length ls' = length x5).
    eapply reset_descendents_cspace_list_slot_length_eq; eauto. 
    rewrite Hls'len in H34.
    auto.
    sep split in H17.
    eapply reset_descendents_cspace_list_slot_similar in H29.
    lets Hy: child_similar_trans Hlsls'similar H29.
    unfolds in Hy. 
    lets Hx: Hy v'14.
    destruct Hx. 
    rewrite <- H34.
    rewrite Heqls.
    rewrite nth_cspace_length_imp; eauto.
    unfold child_num_of. eauto.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    sep destruct H17.
    eexists.
    eapply while_statement_val.
    6:{
        sep split in H17.
        sep lifts (1::4::3::nil)%nat in H17.
        instantiate (10:=Z.to_nat(Int.unsigned i3)).
        rewrite of_to_nat_unsignedv'.
        rewrite Int.repr_unsigned.
        exact H17.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H17. 
    assert(length ls' = length x2).
    eapply reset_descendents_cspace_list_slot_length_eq in H21.
    auto. rewrite Hls'len in H22. auto.
    sep split in H17.
    eapply reset_descendents_cspace_list_slot_similar in H21.
    lets Hy: child_similar_trans Hlsls'similar H21.
    unfolds in Hy. 
    lets Hx: Hy v'14.
    destruct Hx.
    rewrite <- H22. 
    subst ls. 
    rewrite nth_cspace_length_imp; eauto.
    simpl. eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    
    eapply backward_rule1 with (p:=
    (EX (idx : nat) (l0 : list int32)
    (v1 : int32) (l2 : list int32)
    (ls'' : list cspace_val_type),
    LV ios_cap_defs.i @ long
    |-> (V$ Z.of_nat idx) **
    [|(S idx <= Z.to_nat (Int.unsigned i3))%nat|] **
    LV func_capability @ long |-> Vint32 v'9**
    LV dest_space @ CSPACE ∗
    |-> Vptr (b0 ↝ {i4}) **
    ACSpaceAarrayTptr 64
      (v'8 ++ Vptr (b0 ↝ {i4}) :: v'11) ls''
      v'50 **
    [|child v'14 ls v'50 = l0 ++ v1 :: l2|] **
    [|length l0 = idx /\
      length l2 =
      (Z.to_nat (Int.unsigned i3) - S idx)%nat|] **
    [|reset_descendents_cspace_list_slot l0
        (Z.to_nat (Int.unsigned v'9)) v'50 ls' ls''|] ** H16)).
    intros.
    destruct H17.
    destruct H17.
    auto.
    false.
    sep destruct H17.
    assert(s
    |= Rv dest_space ′ → child_num >ₑ
          ios_cap_defs.i ′ @ long ==
       val_inj
         (bop_eval (V$ Z.of_nat (Z.to_nat(Int.unsigned i3)))
            (Vint32 i3) long long olt)).
    assert(i3 = $ Z.of_nat(Z.to_nat(Int.unsigned i3))).
    rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned. auto.
    rewrite H21 in H17 at 1.
    clear H21.
    eapply while_statement_val.
    6:{
        sep split in H17.
        sep lifts (1::4::3::nil)%nat in H17.
        exact H17.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H17. 
    assert(length ls' = length x2).
    eapply reset_descendents_cspace_list_slot_length_eq; eauto.
    rewrite Hls'len in H29. auto.
    sep split in H17.
    eapply reset_descendents_cspace_list_slot_similar in H22.
    lets Hy: child_similar_trans Hlsls'similar H22.
    unfolds in Hy. 
    lets Hx: Hy v'14.
    destruct Hx.
    rewrite <- H29.
    subst ls.
    rewrite nth_cspace_length_imp; eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    destruct_s s.
    destruct H18. simpl getsmem in H18.
    destruct H21.
    simpl getsmem in H21.
    destruct H18.
    rewrite H21 in H18.
    inverts H18.
    clear -H29.
    rewrite of_to_nat_unsignedv' in H29.
    rewrite Int.repr_unsigned in H29.
    assert(Int.ltu i3 i3 = false). int auto.
    rewrite H in H29. unfold val_inj in H29.
    unfold istrue in H29. 
    rewrite Int.eq_true in H29. tryfalse.

    hoare_split_pure_all.
    assert(Hv'16len: length v'16 = 64%nat).
    eapply reset_descendents_cspace_list_slot_length_eq in H22.
    rewrite <- H22. auto.

    subst H16.
    eapply backward_rule1.
    intros.
    sep lift 4%nat in H16.
    eapply ACSpaceAarrayTptr_unfold_any_idx_frm with(idx:=Z.to_nat (Int.unsigned v'14)) in H16.
    exact H16.
    rewrite Hv'16len.
    lia.
    Optimize Proof.
    Optimize Heap.
    auto.
    rewrite app_length. simpl.
    rewrite H32, H23. rewrite S_add_sub_S.
    lia. lia.
    rewrite Hv'16len. lia.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    unfold ACSpace.
    hoare_split_pure_all.
    destruct v'18. destruct p. destruct p. destruct p. destruct v'22.
    hoare_split_pure_all.

    (*这个是数组的一一对应，进行名称上的转换*)
    assert(length v'8 = length v'20).
    destruct H34.
    rewrite H34. auto.
    assert(length v'11 = length v'21).
    destruct H34. rewrite H41.
    auto.
    lets Hx: list_map_eq3 H40 H41 H16.
    destruct Hx.
    destruct H43.
    subst v'20. subst v'21.
    assert(b = b0). inverts H43. auto.
    assert(i1 = i4). inverts H43. auto.
    subst b0 i4. clear H40 H41 H43.
    clear H16. 
    unfold child in H18.
    rewrite  Heqls in H18.
    rewrite nth_cspace_length_imp in H18.
    assert(i3 = i0 /\ l = l0).
    eapply reset_descendents_cspace_list_slot_similar in H22.
    lets Hy: child_similar_trans Hlsls'similar H22.
    unfold child_similar in Hy.
    lets Hx: Hy v'14.
    subst ls v'16.
    rewrite nth_cspace_length_imp in Hx; eauto.
    rewrite nth_cspace_length_imp in Hx; eauto.
    simpl in Hx. 
    destruct Hx.
    inverts H16. inverts H29. auto.
    destruct H35. auto.
    destruct H16.
    subst i3 l0.

    eapply backward_rule1.
    intros.
    sep lift 4%nat in H16.
    unfold Aarray in H16 at 1.
    eapply Aarray'_unfold_any_idx_frm with (idx:=v'4) in H16.
    exact H16.
    unfold MaxChildNum.
    lia.
    auto. unfold MaxChildNum. simpl.
    rewrite max_unsigned_val.
    lia.
    simpl typelen. rewrite max_unsigned_val. lia.
    hoare_split_pure_all.

    
    assert(rule_type_val_match UNION cspace ⋆ v'21 =
    true).
    clear -H38 H16.
    subst l.
    eapply array_type_match2rule_type_match; eauto.

    eapply rule_type_val_match_comptr_elim in H41.
    unfold isptr in H41.
    destruct H41.
    unfolds in H15.
    assert(0 <= v'4 < Z.to_nat (Int.unsigned i0))%nat by lia.
    eapply H15 in H42.
    subst l.
    rewrite nth_val'_length_imp in H42.
    destruct H42.  rewrite H41 in H16.
    tryfalse.
    destruct H40. auto.
    destruct H41. subst v'21.
    assert(0<= Int.unsigned (Int.repr (Z.of_nat v'4)) < 255).
    rewrite Int.unsigned_repr. lia.
    rewrite max_unsigned_val. lia.
    unfolds in H9.
    assert(nth_val ∘ (Int.unsigned ($ Z.of_nat v'4)) l =
    Some (Vptr x1)).
    
    eapply nth_val'2nth_val_ptr.
    rewrite Int.unsigned_repr.
    subst l. 
    eapply nth_val'_length_imp.
    rewrite nat_of_Z_of_nat.
    destruct H40. auto.
    rewrite max_unsigned_val. lia. 
    lets Hx: H9 H42. 
    destruct Hx.
    destruct H43 as [Hx2 Hx3].
    assert(child v'14 ls v'50 = reverse_map v'50  l).
    unfold child. 
    subst ls. 
    rewrite nth_cspace_length_imp; eauto.
    rewrite H18 in H43.


    lets Hx: wellform_descendents_trans_general2 H43 H6.
    destruct Hx. destruct H44. destruct H44.
    rename H43 into Hchildsplit.
    (*子孙后代分割, 左边一部分, 中间要执行的， 右边一部分，以及每一部分都不相交*)
    destruct H44 as [Hchildlist [Hwleft [Hwx [Hwright [Hx4x5 [Hx4x6 Hx5x6]]]]]].
    assert(x2 = v'12).
    rewrite Heqls in Hchildsplit.
    unfold child in Hchildsplit.
    rewrite nth_cspace_length_imp in Hchildsplit; eauto.
    rewrite H16 in Hchildsplit.

    assert(length v'18 = length v'5).
    destruct H40, H21.
    rewrite H21, H40. auto.
    assert(length v'18 < (Z.to_nat (Int.unsigned i0)))%nat. 
    destruct H40. rewrite H40.
    lia.
    eapply reverse_map_injection; eauto.
    subst l. auto. 
    subst v'12.

    eapply seq_rule.
    eapply call_rule'.
    unfold Cap_spec. simpl. unfold CNode_delete_recursive_spec.
    eauto.
    intros.
    eapply rvl_elim.
    eapply cast_rv_struct_tptr.
    eapply lv_mapsto_to_rv.
    2:{
        eapply field_array_asrt_impl.
        7:{
            exact H43.
        }
        3:{
            intros.
            sep_lifts_trms_in H44 (Alvarmapsto ios_cap_defs.i).
            eapply LV_to_Rv in H44.
            eapply inline_tactics.monoasrt_mono in H44.
            exact H44.
            eapply inline_tactics.Rv_mono.
            auto.
            simpl. auto.
        }
        3: auto.
        4:{
           intros.
           sep_lifts_trms_in H44 (Alvarmapsto dest_space).
           unfold CSPACE in H44 at 1.
           exact H44.
        }
        unfold field_offset. simpl. rewrite Int.add_zero.
        change ($ 4 +ᵢ  $ 5108) with ($5112).
        eauto.
        instantiate(1:=2%nat). simpl. auto.
        simpl.
        eauto.
    }
    2:{
        sep lift 2%nat in H43.
        rewrite <- addition_trans.
        simpl typelen.
        rewrite Int.unsigned_repr.
        rewrite Nat2Z.id.
        simpl typelen in H43.
        assert((i1 +ᵢ  $ 5108) +ᵢ  $ 4 = i1 +ᵢ  $ 5112).
        rewrite Int.add_assoc.
        change ($ 5108 +ᵢ  $ 4) with ($5112).
        auto.
        rewrite H44 in H43 at 1.
        unfold Aptrmapsto in H43 at 1.
        exact H43.

        clear -H17 H1.
        int auto.
        simpl.  lia.
    }
    clear -H16 H38.
    subst l. 
   
    eapply array_type_match2rule_type_match; eauto.
    clear -H16 H38.
    subst l. 
    eapply array_type_match2rule_type_match; eauto.

    eapply rvl_elim.
    sep_lifts_trms_in H43 (Alvarmapsto func_capType).
    eapply LV_to_Rv in H43.
    eapply inline_tactics.monoasrt_mono in H43.
    exact H43.
    eapply inline_tactics.Rv_mono.
    auto. simpl. auto.
    clear -H2.
    assert(Int.unsigned v'10 <=? Byte.max_unsigned = true).
    change Byte.max_unsigned with 255. int auto. 
    rewrite H. auto. 
    eapply rvl_elim.
    sep get rv.
    eapply rvl_nil.
    intros.
    unfold getasrt.
    unfold CNode_delete_recursivePre.
    unfold CNode_delete_recursivePre'.
    eapply Aarray'_fold_any_idx_frm  in H43; eauto.
    fold Aarray in H43.
    sep lifts (3::4::1::5::6::nil)%nat in H43.
    
    eapply fold_ACSpace in H43; eauto.
    sep lifts (2::1::3::nil)%nat in H43.
    eapply ACSpaceAarray_fold_any_idx_frm in H43; eauto.


    unfold AOSCSpacePrioTbl.
    sep split; eauto. 
    sep normal. sep eexists.
    sep cancel Aie. sep cancel Aier. sep cancel Ais.
    sep cancel Acs. sep cancel Aisr. sep cancel Aop.
    sep split.
    2: eauto.
    sep cancel OSCSpacePrioTbl.
    unfold Aarray.
    sep cancel Aarray'.
    sep cancel ACSpaceAarrayTptr.
    sep cancel p_local.
    sep cancel ASeminfo.
    sep cancel APthreadMutex.
    sep cancel AMqAttr.
    sep cancel AOSCSpaceObjectPointer.
    sep cancel AOSTCBPrioTbl.
    exact H43.
    splits. rewrite app_length. simpl. 
    rewrite H32, H23. rewrite S_add_sub_S.
    clear -H5. lia. 
    clear -H5. lia.
    rewrite Hv'16len. auto.
    auto. 
    Optimize Proof.
    Optimize Heap.
    unfold ptrvl_to_cspace_to_ptrvl. split; auto.
    auto. 
    5: simpl; eauto.
    4: simpl. eauto.
    4: eauto.
    3: eapply Hx2.
    assert(Hsimilar2: child_similar ls' v'16).
    eapply reset_descendents_cspace_list_slot_similar in H22.
    auto.
    lets Hsimilar3: child_similar_trans Hlsls'similar Hsimilar2.
    lets Hwv'16: wellform_descendents_child_similar Hwx Hsimilar3.
    eapply Hwv'16.

    lia.
    simpl. eauto.
    lia. lia. 
    auto. lia. lia. 
    unfold MaxChildNum.
    lia.
    unfold MaxChildNum.
    simpl. rewrite max_unsigned_val. lia.
    simpl. rewrite max_unsigned_val. lia.
    go. 
    unfold getasrt. unfold CNode_delete_recursivePost.
    unfold CNode_delete_recursivePost'.

    intros. sep normal in H43. sep destruct H43.
    eexists. sep cancel p_local.
    simpl. auto.
    unfold getasrt.
    unfold CNode_delete_recursivePre. 
    unfold CNode_delete_recursivePre'.
    intros. sep destruct H43.
    eexists. sep cancel p_local. simpl. auto.
    simpl. auto.
    unfold getasrt. unfold CNode_delete_recursivePost.
    unfold CNode_delete_recursivePost'.
    clear -H2.
    assert(Int.unsigned v'10 <=? Byte.max_unsigned = true).
    change Byte.max_unsigned with 255.
    int auto. 
    rewrite H. auto. 
    unfold getasrt. unfold CNode_delete_recursivePost.
    unfold CNode_delete_recursivePost'.
    hoare_split_pure_all.
    
    
    simpl in H44, H45, H46.
    inverts H44. inverts H45. inverts H46.
    inverts H50.
    
    assert (Hsuc: ($ Z.of_nat v'4 +ᵢ  $ 1) = ($ (Z.of_nat (S v'4)))).
    {
        clear -H17 H1.
        int auto.
    }
    assert (Hcond: Z.of_nat (S v'4) = (Int.unsigned i0) \/ Z.of_nat (S v'4) < (Int.unsigned i0)).
    clear -H17 H1.
    int auto.
    destruct Hcond as [Hco1 | Hco2].
    
    assert(x2 = v'34).
    rewrite Hx2 in H43. inverts H43. auto.
    subst v'34.
    (*1 case*)
    hoare normal pre; hoare_ex_intro.
    eapply forward_rule2.
    hoare_forward_first.
    intros.
    rewrite Hsuc in H29.
    rewrite Hco1 in H29.
    
    rewrite Int.repr_unsigned in H29.
    eapply adisj_intro.
    right.
    unfold AOSCSpacePrioTbl in H29.
    unfold Aarray in H29.
    sep auto.
    remember (v'18 ++ Vptr v'21 :: v'20) as l.
    remember (v'2 ++
    (c0, i0, l,
    v0, i2) :: v'6) as ls. 
    remember (reset_nth_cspace_slot_option v'14
    (Z.to_nat (Int.unsigned v'23)) n_class_x ls) as ls'.
    assert(v'13 = nil).
    clear -H21 Hco1.
    destruct H21.
    assert((Z.to_nat (Int.unsigned i0) - S v'4) = 0)%nat by lia.
    rewrite H1 in H0. 
    destruct v'13. auto. simpl in H0. tryfalse.
    subst v'13.
    (*v'40是v'14的最后一个儿子节点的int编号*)
    rewrite Hchildsplit.
    clear -H22 H49.

    eapply reset_descendents_cspace_list_slot_append; eauto.

    (*2 case*)
    assert(v'34 = x2).
    rewrite Hx2 in H43. inverts H43. auto.
    subst v'34.
    assert(Hv'13exists: exists x l, v'13 = x :: l).
    assert(length v'13 > 0)%nat. 
    destruct H21. rewrite H29. clear -Hco2. lia.
    destruct v'13. simpl in H29. lia.
    exists i3 v'13. auto.
    destruct Hv'13exists.
    destruct H29.
    subst v'13.
    hoare normal pre; hoare_ex_intro.
    eapply forward_rule2.
    hoare_forward_first.
    intros.
    rewrite Hsuc in H29.
    eapply adisj_intro.
    left.
    unfold AOSCSpacePrioTbl in H29.
    sep auto.
    lets Hx: reset_descendents_cspace_list_slot_append H22 H49.
    eapply Hx. 
    clear -H21 Hco2.
    splits. rewrite app_length.
    simpl. destruct H21. rewrite H16. lia.
    instantiate(1:= x6).
    destruct H21. clear -H21 Hco2.
    simpl in H21. lia.
    instantiate(1:= x1).
    unfold child.
    rewrite nth_cspace_length_imp; eauto.
    rewrite H18. 
    rewrite <- list_cons_assoc.
    auto.
    lia. auto.

    (*循环推理结束*)
    eapply backward_rule1.
    intros.
    destruct H17. 
    destruct H17.
    false. 
    sep destruct H17.
    assert(s
    |= Rv dest_space ′ → child_num >ₑ
          ios_cap_defs.i ′ @ long ==
       val_inj
         (bop_eval (V$ Z.of_nat x1)
            (Vint32 i3) long long olt)).
    eapply while_statement_val.
    6:{
        sep split in H17.
        sep lifts (1::4::3::nil)%nat in H17.
        exact H17.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H17. 
    assert(length ls' = length x5).
    eapply reset_descendents_cspace_list_slot_length_eq; eauto.
    rewrite Hls'len in H35. auto.
    sep split in H17.
    eapply reset_descendents_cspace_list_slot_similar in H34.

    lets Hy: child_similar_trans Hlsls'similar H34.
    lets Hx: Hy v'14.
    destruct Hx.
    rewrite <- H35.
    subst ls.
    rewrite nth_cspace_length_imp; eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    destruct H18.
    destruct H21.
    rewrite H21 in H18.
    destruct H18. inverts H18.
    sep split in H17.
    clear -H18 H29 H1.
    assert(Int.ltu ($ Z.of_nat x1) i3 = true).
    eapply Intlt_true_is_Zlt.
    rewrite Int.unsigned_repr. lia. 
    rewrite max_unsigned_val. lia. 
    rewrite H in H29. 
    unfold istrue in H29. 
    simpl in H29. 
    assert(Int.eq Int.one Int.zero = false) by auto.
    rewrite H0 in H29. 
    tryfalse.
    exact H17.

    eapply ret_rule'.
    intros.
    sep destruct H17.
    subst H16.
    unfold CNode_delete_recursivePost'.
    unfold AOSCSpacePrioTbl.
    sep normal. sep eexists.
    sep cancel OSCSpacePrioTbl.
    sep cancel ACSpaceAarrayTptr.
    sep cancel ASeminfo.
    sep cancel APthreadMutex.
    sep cancel AMqAttr.
    sep cancel AOSCSpaceObjectPointer.
    sep cancel AOSTCBPrioTbl.
    sep cancel Aie. sep cancel Aisr.
    sep cancel Aier. sep cancel Ais.
    sep cancel Acs. sep cancel Aop.
    sep cancel A_dom_lenv.
    sep split;[idtac|simpl; eauto..].
    unfold Aarray. sep cancel Aarray'.
    sep cancel p_local. sep cancel (Alvarmapsto os_code_defs.x).
    sep cancel (Alvarmapsto cap1).
    sep cancel (Alvarmapsto ios_cap_defs.i).
    sep cancel dest_space.
    sep cancel func_capType. 
    sep cancel func_capability.
    sep split in H17. auto.
    sep split in H17.
    eapply reset_descendents_cspace_slot_neqnull; eauto.
   
    rewrite H16. auto.
    splits. rewrite app_length.
    simpl. rewrite H32, H23. rewrite S_add_sub_S.
    lia. lia.
    sep split in H17.
    eapply reset_descendents_cspace_list_slot_length_eq in H18.
    rewrite <- H18.
    auto.
    Optimize Proof.
    Optimize Heap.
    auto.

    
    

    (*当i等于0的时候, 不进入循环*)
    eapply seq_rule.
    eapply while_rule with (tp := Int32u).
    intros.
    sep destruct H16.
    eexists.

    eapply while_statement_val.
    6:{
        sep split in H16.
        sep lifts (1::3::15::nil)%nat in H16.
        instantiate (10:=0%nat).
        exact H16.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H16.
    auto. 
    unfolds in Hlsls'similar.
    lets Hx: Hlsls'similar v'14.
    destruct Hx.
    rewrite <- H17.
    subst ls. rewrite nth_cspace_length_imp; eauto.
    simpl. eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    eapply backward_rule1.
    intros.
    instantiate(1:=Afalse).
    simpl. 
    destruct H16.
    assert(s
    |= Rv dest_space ′ → child_num >ₑ
          ios_cap_defs.i ′ @ long ==
       val_inj
         (bop_eval (V$ Z.of_nat 0)
            (Vint32 i3) long long olt)).
    eapply while_statement_val.
    6:{
        sep split in H16.
        sep lifts (1::3::15::nil)%nat in H16.
        exact H16.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H16. 
    auto.
    unfolds in Hlsls'similar.
    lets Hx: Hlsls'similar v'14.
    destruct Hx.
    rewrite <- H18.
    subst ls.
    rewrite nth_cspace_length_imp; eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    destruct H17, H18.
    rewrite H18 in H17.
    clear -Hieq0 H17.
    unfold val_inj, bop_eval in H17.
    unfold cmp_val, cmpu in H17.
    assert(Int.ltu ($ Z.of_nat 0) i3 = false).
    int auto. 
    rewrite H in H17. 
    destruct H17. inverts H0.
    unfold istrue in H1.
    rewrite Int.eq_true in H1. tryfalse.
    eapply pfalse_rule.
    
    eapply ret_rule'.
    intros.
    destruct H16. clear H17.
    sep destruct H16.
    unfold CNode_delete_recursivePost'.
    sep auto.
    unfold AOSCSpacePrioTbl.
    sep auto.
    
    3: simpl; eauto.
    3: simpl; eauto.
    3: simpl; eauto.
    2: simpl; eauto.
    auto.
    remember (v'2 ++ (c0, i3, l0, v0, i2) :: v'6) as ls.
    assert(child v'14 ls v'50 = nil).
    clear -Hchildlen Hieq0. 
    destruct (child v'14 ls v'50); tryfalse; auto.
    rewrite Hieq0 in Hchildlen. simpl in Hchildlen.
    lia. 
    eapply reset_descendents_cspace_slot_neqnull; eauto.
    rewrite H17.
    eapply reset_descendents_cspace_list_slot_nil.
    }
    (*第二种情况*)
    hoare_split_pure_all.
    simpljoin.
    rename H22 into Hcondition.
    inverts H21. 
    rename H23 into Hxge0.
    rename H24 into Hxlt255.
    hoare_lifts_trms_pre(Aop).
    eapply seq_rule.
    eapply excrit2_rule'.
    intros.
    sep lifts (4::5::1::2::3::nil)%nat in H21.
    exact H21.
    eapply GoodI_I.
    p_local_go.
    
    hoare normal pre.
    unfold Acnode. destruct c. destruct p.
    hoare normal pre.
    pure intro.
    eapply backward_rule1.
    intros.
    sep lift 7%nat in H16.
    eapply AOSCSpacePrioTbl_unfold_any_idx_frm with (idx:=Z.to_nat(Int.unsigned v'14)) in H16; eauto.
    rewrite app_length. simpl.
    rewrite app_length in Hv'10len. simpl in Hv'10len.
    rewrite Hv'10len. lia.
    rewrite nth_val'_length_imp; eauto.
    pure intro.
    unfold ACSpace.
    destruct v'3. destruct p. destruct p. destruct p. destruct v'8.
    pure intro.
    rename H29 into Hl1len.
    rename H30 into Hi0range.
    eapply list_map_eq3 in H16.
    destruct H16. subst v'34.
    destruct H29. inverts H16. subst v'35.
    2:{
      rewrite H11, H18. auto.
    }
    2:{
      rewrite H23, H14. auto.
    }

    eapply list_map_eq3 in H17.
    destruct H17. subst v'31.
    destruct H17. inverts H16.
    subst v'33.
    2:{
      rewrite H21, H12. auto.
    }
    2:{
      rewrite H22, H13. auto.
    }
    
    unfold Acnode.
    hoare_split_pure_all.
    eapply backward_rule1. intros.
    sep_lifts_trms_in H17 (ASlots).
    eapply ASlots_unfold_any_idx_frm with (idx:= (Z.to_nat x)) in H17; eauto.
    unfold SLOT_NUM.
    clear -Hxlt255. lia. 
    hoare_split_pure_all.
    subst l0.
    unfold ACap. 
    destruct v'12. destruct c. destruct p. 
    hoare_split_pure_all.
    remember (v'2 ++
    (i2, i3,
    v'3 ++
    (v'11, (i, (i0, i1, v)))
    :: v'8, i5, l1, v0, i4)
    :: v'4) as ls. 
    rewrite <- Heqls in *.
    eapply seq_rule.
    instantiate (1:=(EX ls',   
    Aarray' (v'40 ↝ {v'41}) 64 CSPACE ∗
    (v'5 ++ Vptr (b0 ↝ {i6}) :: v'6) **
  ACSpaceAarrayTptr 64 (v'5 ++ Vptr (b0 ↝ {i6}) :: v'6)
    ls' v'50 **
    <|| v'37 ||> ** 
    LV cap1 @ Tptr Cap
    |-> Vptr
          (b0,((i6 +ᵢ  $ 8) +ᵢ
    Int.mul ($ Z.of_nat 20) ($ x)) +ᵢ
    $ 4) **
   G& OSCSpacePrioTbl @
   Tarray (Tptr CSPACE) 64 == (v'40, v'41)**
  Aie false **
  Ais nil **
  Acs v'7 **
  Aisr v'39 **
  Aier v'36 **
  ASeminfo (v'42, v'43) v'51 **
  APthreadMutex (v'44, v'45) v'52 **
  AMqAttr (v'46, v'47) v'53 **
  AOSCSpaceObjectPointer v'54 **
  AOSTCBPrioTbl v'55 v'56 v'57 v'58 v'59 **
  p_local OSLInv ct init_lg **
  LV os_code_defs.x @ Tint32 |-> (V$ x) **
  LV ios_cap_defs.i @ Tint32 |-> (V$ 0) **
  LV func_capability @ long |-> Vint32 v'9 **
  LV func_capType @ Tint8 |-> Vint32 v'10 **
  LV dest_space @ CSPACE ∗ |-> Vptr (b0↝ {i6}) **
  A_dom_lenv
    ((func_capability, Tint32)
     :: (func_capType, Tint8)
        :: (dest_space, Tptr CSPACE)
           :: (ios_cap_defs.i, Tint32)
              :: (cap1, Tptr Cap)
                 :: (os_code_defs.x,
                    Tint32) :: nil) ** 
  [| exists n_class, reset_nth_cspace_slot_option v'14
    (Z.to_nat (x)) n_class ls ls'|]
)).
    eapply forward_rule2.
    eapply ift_rule''.
    intros.
    symbolic_execution.
    destruct (Int.eq ($ x) ($ SLOT_NUM)); auto.
    destruct (Int.eq ($ x) ($ SLOT_NUM)); auto.
    hoare_split_pure_all.
    clear H31.
    (*cap1′ =ₑ &ₐ(dest_space′→cnode..slots[func_capability′]..capability)*)
    eapply seq_rule.
    Require Import seplog_trm_tacs.
    hoare_lifts_trms_pre 
    (
        Aop 
    ).
    eapply assign_rule_lvar.
    {
        split; intros.
        sep_lifts_trms_in H31 (Alvarmapsto cap1).
        exact H31.
        sep auto.
    Optimize Proof.
    Optimize Heap.
    }
    {
        intros.
        eapply calculate_rv_expr_id_addr.
        3:{
            eapply expr_field_array_asrt_impl_frm.
            5:{
                eapply local_val_struct_member_addr_frm.
                4:{
                    sep cancel dest_space.
                    sep_lifts_trms_in H31 (Alvarmapsto os_code_defs.x). 
                    eapply LV_to_Rv in H31; eauto.
                    instantiate(2:=Z.to_nat(x)).
                    rewrite Z2Nat.id. 
                    exact H31.
                    lia. 
                }
                unfold CSPACE. eauto.
                unfold field_offset. simpl. eauto.
                simpl. unfold Cte. eauto.
            }
            unfold field_offset. simpl. rewrite Int.add_zero.  
            change($4+ᵢ$4) with ($8). eauto.
            instantiate(1:=2%nat). simpl. eauto.
            auto.
            simpl. unfold Slot. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero. eauto.
    }
    eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.
    simpl typelen.
    rewrite Int.add_zero. rewrite Z2Nat.id.
    2: lia. 
    
    
    eapply seq_rule.
    (*IF (cap1 ′ → cap_type ==ₑ ′ CAP_CATEGORY_TYPE)*)
    eapply if_rule2'.
    intros.
    eapply bop_rv.
    eapply lv_mapsto_to_rv.
    2:{
        eapply local_val_struct_member_addr.
        sep lift 2%nat in H31.
        exact H31.
        unfold Cap. eauto.
        unfold field_offset. simpl. eauto.
        simpl. eauto.
    }
    2:{
        rewrite Int.add_zero.
        sep lift 5%nat in H31.
        unfold Aptrmapsto in H31 at 1.
        rewrite <- addition_trans.
        rewrite Int.unsigned_repr.  
        exact H31.
        clear -Hxlt255 Hxge0.
        int auto.
        lia.
    }
    simpl. auto.
    destruct_s s. simpl. split; eauto.
    eauto.
    unfold val_inj, bop_eval, val_eq.
    destruct (Int.eq i ($ CAP_CATEGORY_TYPE)); eauto.
    simpl. eauto.
    hoare_split_pure_all.
    rename H31 into Hif1.
    eapply seq_rule.
    hoare_lifts_trms_pre(Aop).
    eapply assign_rule_aop.
    2:{
        intros.
        eapply local_val_struct_member_addr.
        exact H31.
        unfold Cap. eauto.
        unfold field_offset. simpl. eauto.
        simpl. eauto.
    }
    2:{
        split; intros.
        rewrite Int.add_zero.
        rewrite <- addition_trans.
        rewrite Int.unsigned_repr.
        sep lift 4%nat in H31.
        exact H31.
        clear -Hxlt255 Hxge0.
        int auto.
        lia.
        rewrite Int.add_zero in H31.
        sep auto.
        assert(x = Int.unsigned (Int.repr x)).
        rewrite Int.unsigned_repr; auto.
        clear -Hxlt255 Hxge0. int auto.
        rewrite H33. clear H33.
        rewrite addition_trans.
        auto.
        lia.
    }
    2:{
        intros.
        destruct_s s. simpl. split; eauto.
    }
    eapply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.

    (*((cap1 ′ → cap_content) .. category) .. category_content =ₑ ′ 0;ₛ*)
    eapply seq_rule.
    eapply assign_rule_aop.
    2:{
        intros.
        eapply field_asrt_impl_struct_aop.
        3:{
            eapply field_asrt_impl_union_aop'.
            2:{
                instantiate(1:=Aemp).
                eapply astar_r_aemp_intro.
                eapply local_val_struct_member_addr.
                sep lift 2%nat in H31.
                exact H31.
                unfold Cap. eauto.
                unfold field_offset. simpl.
                rewrite Int.add_zero. eauto.
                simpl. unfold Content. eauto.
            }
            simpl. unfold Cap_Category. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl. eauto.
    }
    2:{
        split; intros.
        rewrite Int.add_zero.
        rewrite Int.add_zero.
        rewrite Int.add_zero in H31.
        sep lift 5%nat in H31.
        rewrite <- addition_trans.
        rewrite Int.unsigned_repr.
        exact H31.
        clear -Hxge0 Hxlt255.
        int auto.
        lia.
        sep auto.
        rewrite Int.add_zero in *.
        rewrite Int.add_zero in H31.
        sep auto.
        assert(x = Int.unsigned(Int.repr x)).
        rewrite Int.unsigned_repr; auto.
        clear -Hxge0 Hxlt255. int auto.
        rewrite H33. clear H33.
        rewrite addition_trans. auto.
        lia.
    }
    2:{
        intros.
        destruct_s s. simpl. split; eauto.
    }
    eapply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.

    (*((cap1 ′ → cap_content) .. category) .. category_right =ₑ ′ 0 *)
    eapply assign_rule_aop.
    2:{
        intros.
        eapply field_asrt_impl_struct_aop.
        3:{
            eapply field_asrt_impl_union_aop'.
            2:{
                instantiate(1:=Aemp).
                eapply astar_r_aemp_intro.
                eapply local_val_struct_member_addr.
                sep lift 3%nat in H31.
                exact H31.
                unfold Cap. eauto.
                unfold field_offset. simpl.
                rewrite Int.add_zero. eauto.
                simpl. unfold Content. eauto.
            }
            simpl. unfold Cap_Category. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl. eauto.
    }
    2:{
        split; intros.
        rewrite Int.add_zero.
        rewrite Int.add_zero.
        rewrite Int.add_zero in H31.
        sep lift 6%nat in H31.
        rewrite <- addition_trans.
        rewrite Int.unsigned_repr. 
        rewrite Int.add_assoc.
        change($ 4 +ᵢ  $ 4) with ($8).
        exact H31.
        clear -Hxge0 Hxlt255. 
        int auto.
    Optimize Proof.
    Optimize Heap.
        lia.
        sep auto.
        rewrite Int.add_zero in *.
        rewrite Int.add_zero in H31.
        rewrite Int.add_zero in *.
        sep auto.
        assert(x = Int.unsigned($ x)).
        rewrite Int.unsigned_repr; auto.
        clear -Hxge0 Hxlt255.
        rewrite max_unsigned_val. lia.
        rewrite H33.
        rewrite addition_trans.
        clear H33. 
        rewrite Int.add_assoc in H31.
        change ($ 4 +ᵢ  $ 4) with ($8) in H31. auto.
        auto.  lia.
    }
    2:{
        intros.
        destruct_s s. simpl. split; eauto.
    }
    eapply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.

    (*If (cap1 ′ → cap_type ==ₑ′ ios_cap_defs.CAP_OBJECT_TYPE)*)
    
    hoare_split_pure_all.
    rename H31 into Hif1.

    eapply ift_rule''.
    intros.
    1:{
        eapply bop_rv.
        {
            eapply lv_mapsto_to_rv.
            2:{
                eapply local_val_struct_member_addr.
                sep lift 2%nat in H31.
                exact H31.
                unfold Cap. eauto.
                unfold field_offset. simpl. eauto.
                simpl. eauto.
            }
            2:{
                rewrite Int.add_zero.
                sep lift 5%nat in H31.
                unfold Aptrmapsto in H31 at 1.
                rewrite <- addition_trans.
                rewrite Int.unsigned_repr.
                exact H31.
                clear -Hxge0 Hxlt255. int auto.
                lia.
            }
            simpl. auto.
        }
        {
            destruct_s s.
            simpl. split; eauto.
        }
        eauto.
        unfold bop_eval. 
        unfold val_eq.  
        destruct (Int.eq i ($ ios_cap_defs.CAP_OBJECT_TYPE)); eauto.
        simpl. eauto.
    }
    hoare_split_pure_all.
    rename H31 into Hc1.
    (*cap1 ′ → cap_type =ₑ ′ 0;ₛ*)
    eapply seq_rule.
    eapply assign_rule_aop.
    2:{
        intros.
        eapply local_val_struct_member_addr.
        exact H31.
        unfold Cap. eauto.
        unfold field_offset. simpl. eauto.
        simpl. eauto.
    }
    2:{
        split; intros.
        rewrite Int.add_zero.
        rewrite <- addition_trans.
        2: lia.
        rewrite Int.unsigned_repr. 
        sep lift 4%nat in H31.  exact H31.
        clear -Hxge0 Hxlt255. int auto.
        sep auto.
        assert(x = Int.unsigned(Int.repr x)).
        clear -Hxge0 Hxlt255. int auto.
        rewrite H33. clear H33.
        rewrite addition_trans. 
        rewrite Int.add_zero in H31. auto.
        lia.
    }
    2:{
        intros.
        destruct_s s. simpl. split; eauto.
    }
    eapply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.

    (*((cap1 ′ → cap_content) .. object) .. object_right =ₑ ′ 0;ₛ*)
    eapply seq_rule.
    eapply assign_rule_aop.
    2:{
        intros.
        eapply field_asrt_impl_struct_aop.
        3:{
            eapply field_asrt_impl_union_aop'.
            2:{
                instantiate(1:=Aemp).
                eapply astar_r_aemp_intro.
                eapply local_val_struct_member_addr.
                sep lift 2%nat in H31.
                exact H31.
                unfold Cap. eauto.
                unfold field_offset. simpl.
                rewrite Int.add_zero. eauto.
                simpl. unfold Content. eauto.
            }
            simpl. unfold Cap_Object. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl. eauto.
    }
    2:{
        split; intros.
        rewrite Int.add_zero.
        rewrite Int.add_zero.
        rewrite Int.add_zero in H31.
        sep lift 5%nat in H31.
        rewrite <- addition_trans.
        rewrite Int.unsigned_repr.
        exact H31.
        clear -Hxge0 Hxlt255. int auto.
        lia.
        sep auto.
        rewrite Int.add_zero in *.
        rewrite Int.add_zero in H31.
        sep cancel 2%nat 1%nat. 
        assert(x = Int.unsigned(Int.repr x)).
        clear -Hxge0 Hxlt255. int auto.
        rewrite H33. clear H33.
        rewrite addition_trans. 
        auto.
        lia.
    }
    2:{
        intros.
        destruct_s s. simpl. split; eauto.
    }
    eapply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.

    (*(cap1 ′ → cap_content) .. object) .. object_t =ₑ〈 (Void) ∗ 〉 ′ NULL*)
    eapply assign_rule_aop.
    2:{
        intros.
        eapply field_asrt_impl_struct_aop.
        3:{
            eapply field_asrt_impl_union_aop'.
            2:{
                instantiate(1:=Aemp).
                eapply astar_r_aemp_intro.
                eapply local_val_struct_member_addr.
                sep lift 3%nat in H31.
                exact H31.
                unfold Cap. eauto.
                unfold field_offset. simpl.
                rewrite Int.add_zero. eauto.
                simpl. unfold Content. eauto.
            }
            simpl. unfold Cap_Object. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl. eauto.
    }
    2:{
        split; intros.
        rewrite Int.add_zero.
        rewrite Int.add_zero.
        rewrite Int.add_zero in H31.
        sep lift 7%nat in H31.
        rewrite <- addition_trans.
        rewrite Int.unsigned_repr.
        change  ($ 4 +ᵢ  $ 4) with ($8).
        rewrite Int.add_assoc.
        change($ 4 +ᵢ  $ 8) with ($12).
        exact H31.
        clear -Hxge0 Hxlt255. int auto.
        lia.
    Optimize Proof.
    Optimize Heap.
        sep auto.
        rewrite Int.add_zero in *.
        rewrite Int.add_zero in H31.
        rewrite Int.add_zero in *.
        sep auto.
        assert(x = Int.unsigned(Int.repr x)).
        clear -Hxge0 Hxlt255. int auto.
        rewrite H33.
        clear H33.
        rewrite addition_trans. 
        rewrite Int.add_assoc in H31. 
        change ($ 4 +ᵢ  ($ 4 +ᵢ $4)) with ($12) in H1. auto.
        lia.
    }
    2:{
        intros.
        destruct_s s. 
        simpl. split; eauto.
    }
    eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.


    rewrite Int.add_zero.
    rewrite Int.add_zero.
    instantiate (1:=(EX ls',   
    Aarray' (v'40 ↝ {v'41}) 64 CSPACE ∗
    (v'5 ++ Vptr (b0 ↝ {i6}) :: v'6) **
  ACSpaceAarrayTptr 64 (v'5 ++ Vptr (b0 ↝ {i6}) :: v'6)
    ls' v'50 **
    <|| v'37 ||> ** 
    LV cap1 @ Tptr Cap
    |-> Vptr
          (b0,((i6 +ᵢ  $ 8) +ᵢ
    Int.mul ($ Z.of_nat 20) ($ x)) +ᵢ
    $ 4) **
   G& OSCSpacePrioTbl @
   Tarray (Tptr CSPACE) 64 == (v'40, v'41)**
  Aie false **
  Ais nil **
  Acs v'7 **
  Aisr v'39 **
  Aier v'36 **
  ASeminfo (v'42, v'43) v'51 **
  APthreadMutex (v'44, v'45) v'52 **
  AMqAttr (v'46, v'47) v'53 **
  AOSCSpaceObjectPointer v'54 **
  AOSTCBPrioTbl v'55 v'56 v'57 v'58 v'59 **
  p_local OSLInv ct init_lg **
  LV os_code_defs.x @ Tint32 |-> (V$ x) **
  LV ios_cap_defs.i @ Tint32 |-> (V$ 0) **
  LV func_capability @ long |-> Vint32 v'9 **
  LV func_capType @ Tint8 |-> Vint32 v'10 **
  LV dest_space @ CSPACE ∗ |-> Vptr (b0↝ {i6}) **
  A_dom_lenv
    ((func_capability, Tint32)
     :: (func_capType, Tint8)
        :: (dest_space, Tptr CSPACE)
           :: (ios_cap_defs.i, Tint32)
              :: (cap1, Tptr Cap)
                 :: (os_code_defs.x,
                    Tint32) :: nil) ** 
  [|exists n_class, reset_nth_cspace_slot_option v'14
    (Z.to_nat (x)) n_class ls ls'|]
)).

    (*到达while有三种情况, true, false true*)
    apply disj_rule.
    
    
    
    (********************true*****************)

    hoare_split_pure_all.
    rename H31 into Hc1.
    hoare normal pre; hoare_ex_intro; 
    eapply forward_rule2.
    eapply assign_rule_aop.
    2:{
        intros.
        eapply field_asrt_impl_struct_aop.
        3:{
            eapply expr_field_array_asrt_impl_frm.
            5:{
                eapply local_val_struct_member_addr_frm.
                4:{
                    sep lift 2%nat. 
                    eapply LV_to_Rv.
                    3:{
                        sep cancel dest_space.
                        instantiate(2:=Z.to_nat(x)).
                        rewrite Z2Nat.id.
                        sep_lifts_trms_in H31 (Alvarmapsto os_code_defs.x).
                        exact H31.
                        auto.
                    }
                    auto.
                    simpl. auto.
                }
                unfold CSPACE. eauto.
                unfold field_offset. simpl. unfold Int.zero. eauto.
                simpl. unfold Cte. eauto.
            }
            unfold field_offset. simpl. rewrite Int.add_zero. change($ 4 +ᵢ  $ 4) with ($8).
            eauto. instantiate(1:=2%nat). simpl. eauto.
            auto. simpl. unfold Slot. eauto. 
        }
        simpl. eauto. unfold field_offset. simpl. eauto.
    }
    2:{
       split; intros.
       rewrite Z2Nat.id. simpl typelen.
       rewrite Int.add_zero.
       rewrite Int.add_zero.
       sep lift 6%nat in H31.
       rewrite <- addition_trans. 
       rewrite Int.unsigned_repr.
       exact H31.
       clear -Hxge0 Hxlt255. int auto.
       lia. auto.
       simpl typelen in *.
       sep auto.
       rewrite Int.add_zero in H31. rewrite Int.add_zero in H31.
       assert(x = Int.unsigned(Int.repr x)).
       clear -Hxge0 Hxlt255. int auto.
       rewrite H33.
       rewrite addition_trans.
       rewrite Z2Nat.id in H31.
       auto.
       auto. lia.
    }
    2:{
        intros.
        destruct_s s. simpl. split; eauto.
    }
    apply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.
    
    simpl typelen.
    (*在这里先把AOSCSpacePrioTbl折叠起来*)
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    intros.
    sep lifts (5::4::3::8::nil)%nat in H31.
    assert(x = Int.unsigned(Int.repr x)).
    clear -Hxge0 Hxlt255. int auto.
    rewrite H32 in H31 at 4.
    clear H32.
    rewrite addition_trans in H31.
    sep lift 3%nat in H31.
    rewrite Int.add_assoc in H31 at 1.
    change ($ 4 +ᵢ  $ 4) with ($8) in H31.
    sep lifts (2::3::1::4::nil)%nat in H31.
    eapply fold_Cap in H31. 
    sep lifts (5::3::1::6::nil)%nat in H31.
    rewrite <- addition_trans in H31 at 1.
    rewrite <- addition_trans in H31 at 1.
    rewrite Int.unsigned_repr in H31.
    rewrite Int.unsigned_repr in H31.
    rewrite Z2Nat.id in H31.
    eapply ASlots_fold_any_idx_frm with(slotsvl :=
    (v'3 ++ ($SLOT_NULL_CAP, ($ 0, ($0, $0, v))) :: v'8))
    in H31.

    sep lifts (8::9::1::nil)%nat in H31.
    eapply fold_Acnode in H31.
    fold Aarray in H31.
    sep lifts (1::8::9::10::11::nil)%nat in H31.
    eapply fold_ACSpace in H31; eauto.
    sep lifts (7::1::8::nil)%nat in H31.
    eapply ACSpaceAarray_fold_any_idx_frm 
    with(cspacevl:= v'2 ++
    (i2, i3,
    v'3 ++
    ($ SLOT_NULL_CAP, ($ 0, ($ 0, $ 0, v)))
    :: v'8, i5, l1, v0, i4) :: v'4) in H31; eauto.
    sep lifts (5::6::nil)%nat in H31.
    rewrite addition_trans in H31.

    assert(v'14 = $ Z.of_nat(Z.to_nat (Int.unsigned v'14))).
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned. auto.
    rewrite H32 in H31 at 1.
    clear H32.
    eapply array_asrt_eq_frm in H31.
    sep auto.
    Optimize Proof.
    Optimize Heap.
    unfold reset_nth_cspace_slot_option.
    exists (Z.to_nat x).
    splits.
    unfolds. right.
    clear -Hxge0 Hxlt255. unfold SLOT_NUM.
    lia.
    assert((0 <=? Z.to_nat x)%nat &&
    (Z.to_nat x <? Z.to_nat SLOT_NUM)%nat = true).
    clear -Hxge0 Hxlt255. unfold SLOT_NUM.
    assert((0 <=? Z.to_nat x)%nat = true). int auto.
    assert((Z.to_nat x <? Z.to_nat 255)%nat = true). 
    eapply Nat.ltb_lt. lia.
    rewrite H, H0. auto.
    rewrite H32.
    unfold reset_nth_cspace_slot.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    assert(Int.eq i ($CAP_CATEGORY_TYPE) = true).
    clear -Hc1.
    destruct Hc1.
    unfold val_inj, bop_eval, val_eq in H.
    destruct (Int.eq i ($ CAP_CATEGORY_TYPE)); tryfalse; auto.
    rewrite H33. clear H32 H33.
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_list_length_imp; eauto.
    destruct H29. auto.
    destruct H29. auto.
    clear H32.
    clear -H5. lia.
    eapply nth_val_length_imp; eauto.
    lia. lia. clear -H5. lia.
    rewrite app_length. simpl.
    rewrite H21, H22.
    rewrite S_add_sub_S. clear -H5. lia.
    clear -H5. lia.

    rewrite app_length. simpl.
    destruct H29. rewrite H29, H32.
    clear -Hxlt255. rewrite S_add_sub_S.
    unfold SLOT_NUM. lia.
    unfold SLOT_NUM. lia.
    unfold SLOT_NUM. clear -Hxlt255. lia.
    auto.
    rewrite app_length. simpl.
    destruct H29. rewrite H29, H32.
    clear -Hxlt255. rewrite S_add_sub_S.
    unfold SLOT_NUM. lia.
    unfold SLOT_NUM. lia.
    destruct H29. auto.
    destruct H29. auto.
    auto. auto.
    clear -Hxge0 Hxlt255. int auto.
    rewrite Z2Nat.id.
    clear -Hxge0 Hxlt255. int auto. auto.
    lia. lia.
    auto. lia.
   
    hoare_split_pure_all.
    rename H31 into Hc1.
    eapply disj_rule.
    hoare_split_pure_all.
    rename H31 into Hc2.
    hoare normal pre; hoare_ex_intro; 
    eapply forward_rule2.
    eapply assign_rule_aop.
    2:{
        intros.
        eapply field_asrt_impl_struct_aop.
        3:{
            eapply expr_field_array_asrt_impl_frm.
            5:{
                eapply local_val_struct_member_addr_frm.
                4:{
                    sep lift 2%nat. 
                    eapply LV_to_Rv.
                    3:{
                        sep cancel dest_space.
                        instantiate(2:=Z.to_nat(x)).
                        rewrite Z2Nat.id.
                        sep_lifts_trms_in H31 (Alvarmapsto os_code_defs.x).
                        exact H31.
                        auto.
                    }
                    auto.
                    simpl. auto.
                }
                unfold CSPACE. eauto.
                unfold field_offset. simpl. unfold Int.zero. eauto.
                simpl. unfold Cte. eauto.
            }
            unfold field_offset. simpl. rewrite Int.add_zero. change($ 4 +ᵢ  $ 4) with ($8).
            eauto. instantiate(1:=2%nat). simpl. eauto.
            auto. simpl. unfold Slot. eauto. 
        }
        simpl. eauto. unfold field_offset. simpl. eauto.
    }
    2:{
       split; intros.
       rewrite Z2Nat.id. simpl typelen.
       rewrite Int.add_zero.
       rewrite Int.add_zero.
       sep lift 6%nat in H31.
       rewrite <- addition_trans. 
       rewrite Int.unsigned_repr.
      
       exact H31. 
       clear -Hxge0 Hxlt255. int auto.
       lia. auto.
       simpl typelen in *.
       sep auto.
       rewrite Int.add_zero in H31. rewrite Int.add_zero in H31.
       rewrite Z2Nat.id in H31. 
       assert(x = Int.unsigned(Int.repr x)).
       clear -Hxge0 Hxlt255. int auto.
       rewrite H33.
       clear H33.
       rewrite addition_trans.
       auto.
       lia.
       auto.
    }
    2:{
        intros.
        destruct_s s. simpl. split; eauto.
    }
    apply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.
    
    simpl typelen.

    (*在这里先把AOSCSpacePrioTbl折叠起来*)
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    intros.
    sep lifts (5::4::3::8::nil)%nat in H31.
    assert(x = Int.unsigned(Int.repr x)).
    clear -Hxge0 Hxlt255. int auto.
    rewrite H32 in H31 at 4.
    clear H32.
    rewrite addition_trans in H31.
    sep lift 3%nat in H31.
    rewrite Int.add_assoc in H31 at 1.
    change ($ 4 +ᵢ  $ 4) with ($8) in H31.
    change ($ 4 +ᵢ  $ 8) with ($12) in H31.
    sep lifts (2::3::4::1::nil)%nat in H31.
    eapply fold_Cap in H31. 
    sep lifts (5::3::1::6::nil)%nat in H31.
    rewrite <- addition_trans in H31 at 1.
    rewrite <- addition_trans in H31 at 1.
    rewrite Int.unsigned_repr in H31.
    rewrite Int.unsigned_repr in H31.
    rewrite Z2Nat.id in H31.
    eapply ASlots_fold_any_idx_frm with(slotsvl :=
    (v'3 ++ ($SLOT_NULL_CAP, ($ 0, ($0, i1, Vnull))) :: v'8))
    in H31.

    sep lifts (8::9::1::nil)%nat in H31.
    eapply fold_Acnode in H31.
    fold Aarray in H31.
    sep lifts (1::8::9::10::11::nil)%nat in H31.
    eapply fold_ACSpace in H31; eauto.
    sep lifts (7::1::8::nil)%nat in H31.
    eapply ACSpaceAarray_fold_any_idx_frm 
    with(cspacevl:= v'2 ++
    (i2, i3,
    v'3 ++
    ($ SLOT_NULL_CAP, ($ 0, ($ 0, i1, Vnull)))
    :: v'8, i5, l1, v0, i4) :: v'4) in H31; eauto.
    sep lifts (5::6::nil)%nat in H31.
    rewrite addition_trans in H31.

    assert(v'14 = $ Z.of_nat(Z.to_nat (Int.unsigned v'14))).
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned. auto.
    rewrite H32 in H31 at 1.
    clear H32.
    eapply array_asrt_eq_frm in H31.
    sep auto.
    unfold reset_nth_cspace_slot_option.
    exists (Z.to_nat(x)).
    splits. unfolds. right.
    clear -Hxge0 Hxlt255. unfold SLOT_NUM. lia.
    assert((0 <=? Z.to_nat x)%nat &&
    (Z.to_nat x <? Z.to_nat SLOT_NUM)%nat = true).
    clear -Hxge0 Hxlt255. unfold SLOT_NUM.
    assert((0 <=? Z.to_nat x)%nat = true). int auto.
    assert((Z.to_nat x <? Z.to_nat 255)%nat = true). 
    eapply Nat.ltb_lt. lia.
    rewrite H, H0. auto.
    rewrite H32.
    unfold reset_nth_cspace_slot.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    assert(Int.eq i ($ CAP_CATEGORY_TYPE) = false).
    clear -Hc1.
    unfold val_inj, bop_eval, val_eq in Hc1.
    destruct (Int.eq i ($ CAP_CATEGORY_TYPE)); 
    destruct Hc1; tryfalse; auto.
    rewrite H33. clear H32 H33.
    assert(Int.eq i ($ CAP_OBJECT_TYPE) = true).
    clear -Hc2. destruct Hc2. 
    unfold val_inj, bop_eval, val_eq in H.
    destruct (Int.eq i ($ CAP_OBJECT_TYPE)). auto. tryfalse.
    rewrite H32.
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_list_length_imp; eauto.
    destruct H29. auto. destruct H29. auto.
    lia. rewrite nth_val_length_imp; eauto. lia.
    lia. lia. rewrite app_length. simpl.
    rewrite H21, H22. rewrite S_add_sub_S.
    lia. lia.
    rewrite app_length. simpl.
    destruct H29. rewrite H29, H32.
    clear -Hxlt255. rewrite S_add_sub_S.
    unfold SLOT_NUM. lia.
    unfold SLOT_NUM. lia.
    unfold SLOT_NUM. clear -Hxlt255. lia.
    auto.
    Optimize Proof.
    Optimize Heap.
    rewrite app_length. simpl.
    destruct H29. rewrite H29, H32.
    clear -Hxlt255. rewrite S_add_sub_S.
    unfold SLOT_NUM. lia.
    unfold SLOT_NUM. lia.
    destruct H29. auto.
    destruct H29. auto.
    auto. auto.
    clear -Hxge0 Hxlt255. int auto.
    rewrite Z2Nat.id.
    clear -Hxge0 Hxlt255. int auto. auto.
    lia. lia.
    unfold isptr. auto. lia.

    hoare_split_pure_all.
    rename H31 into Hc2.
    hoare normal pre; hoare_ex_intro; 
    eapply forward_rule2.
    eapply assign_rule_aop.
    2:{
        intros.
        eapply field_asrt_impl_struct_aop.
        3:{
            eapply expr_field_array_asrt_impl_frm.
            5:{
                eapply local_val_struct_member_addr_frm.
                4:{
                    sep lift 2%nat. 
                    eapply LV_to_Rv.
                    3:{
                        sep cancel dest_space.
                        instantiate(2:=Z.to_nat(x)).
                        rewrite Z2Nat.id.
                        sep_lifts_trms_in H31 (Alvarmapsto os_code_defs.x).
                        exact H31. auto.
                    }
                    auto.
                    simpl. auto.
                }
                unfold CSPACE. eauto.
                unfold field_offset. simpl. unfold Int.zero. eauto.
                simpl. unfold Cte. eauto.
            }
            unfold field_offset. simpl. rewrite Int.add_zero. change($ 4 +ᵢ  $ 4) with ($8).
            eauto. instantiate(1:=2%nat). simpl. eauto.
            auto. simpl. unfold Slot. eauto. 
        }
        simpl. eauto. unfold field_offset. simpl. eauto.
    }
    2:{
       rewrite Int.add_zero.
       rewrite Int.add_zero.
       split; intros.
       rewrite Z2Nat.id. 
       simpl typelen.
       
       sep lift 3%nat in H31.
       rewrite <- addition_trans. 
       rewrite Int.unsigned_repr.
       exact H31. 
       clear -Hxge0 Hxlt255. int auto.
       lia. auto.
       simpl typelen in *.
       sep auto.
       rewrite Z2Nat.id in H31. 
       assert(x = Int.unsigned(Int.repr x)).
       clear -Hxge0 Hxlt255. int auto.
       rewrite H33. clear H33.
       rewrite addition_trans.
       auto.
       lia.
       auto.
    }
    2:{
        intros.
        destruct_s s. simpl. split; eauto.
    }
    apply eq_int. auto.
    intros. eexists. sep cancel p_local. simpl. auto.
    
    simpl typelen.

    (*在这里先把AOSCSpacePrioTbl折叠起来*)
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    intros.
    sep lift 20%nat in H31.
    sep lifts (6::7::8::9::nil)%nat in H31.
    eapply fold_Cap in H31. 
    sep lifts (6::4::1::7::nil)%nat in H31.
    rewrite Z2Nat.id in H31.
    rewrite <- addition_trans in H31 at 1.
    rewrite Int.unsigned_repr in H31.
    rewrite <- addition_trans in H31 at 1.


    eapply ASlots_fold_any_idx_frm with(slotsvl :=
    (v'3 ++ ($SLOT_NULL_CAP, (i, (i0, i1, v))) :: v'8))
    in H31; eauto.

    sep lifts (9::10::1::nil)%nat in H31.
    eapply fold_Acnode in H31.
    fold Aarray in H31.
    sep lifts (1::9::10::11::12::nil)%nat in H31.
    eapply fold_ACSpace in H31; eauto.
    2:{
        rewrite app_length. simpl.
        destruct H29.
        rewrite H29, H32. rewrite S_add_sub_S.
        unfold SLOT_NUM. lia.
        unfold SLOT_NUM. lia.
    }
    2:{
      unfold SLOT_NUM. 
      lia.
    }
    2:{
        rewrite app_length. simpl.
        destruct H29.
        rewrite H29, H32. rewrite S_add_sub_S.
        unfold SLOT_NUM. lia.
        unfold SLOT_NUM. lia.
    }
    2:destruct H29; auto.
    2:destruct H29; auto. 
    2: lia. 
    2:{
      clear -Hxge0 Hxlt255.
      int auto.
    }
    2: lia.
    2: auto.
    2: auto.
    sep lifts (8::1::2::nil)%nat in H31.
    eapply ACSpaceAarray_fold_any_idx_frm 
    with(cspacevl:= 
    v'2 ++(i2, i3,
    v'3 ++
    ($ SLOT_NULL_CAP, (i, (i0, i1, v))) :: v'8,
    i5, l1, v0, i4) :: v'4)in H31; eauto.
    sep lifts (5::6::nil)%nat in H31.
    rewrite addition_trans in H31.

    assert(v'14 = $ Z.of_nat(Z.to_nat (Int.unsigned v'14))).
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned. auto.
    rewrite H32 in H31 at 1.
    clear H32.
    eapply array_asrt_eq_frm in H31.
    rewrite addition_trans in H31.
    sep auto.
    unfold reset_nth_cspace_slot_option.
    exists (Z.to_nat(x)). splits. right.
    clear -Hxge0 Hxlt255. unfold SLOT_NUM. lia.
    assert((0 <=? Z.to_nat x)%nat &&
    (Z.to_nat x <? Z.to_nat SLOT_NUM)%nat = true).
    clear -Hxge0 Hxlt255. unfold SLOT_NUM.
    assert((0 <=? Z.to_nat x)%nat = true). int auto.
    assert((Z.to_nat x <? Z.to_nat 255)%nat = true). 
    eapply Nat.ltb_lt. lia.
    rewrite H, H0. auto.
    rewrite H32.
    unfold reset_nth_cspace_slot.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    assert(Int.eq i ($ CAP_CATEGORY_TYPE) = false).
    clear -Hc1.
    unfold val_inj, bop_eval, val_eq in Hc1.
    destruct (Int.eq i ($ CAP_CATEGORY_TYPE)); 
    destruct Hc1; tryfalse; auto.
    rewrite H33. clear H32 H33.
    assert(Int.eq i ($ CAP_OBJECT_TYPE) = false).
    clear -Hc2.
    unfold val_inj, bop_eval, val_eq in Hc2.
    destruct (Int.eq i ($ CAP_OBJECT_TYPE));
    destruct Hc2; tryfalse; auto.
    rewrite H32.
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_list_length_imp; eauto.
    destruct H29. auto.
    destruct H29. auto.
    lia. lia.
    rewrite nth_val_length_imp; eauto. lia.
    lia. lia.
    rewrite app_length. simpl.
    rewrite H21, H22. rewrite S_add_sub_S.
    lia. lia.
    intros.
    destruct H31.
    sep auto.
    Optimize Proof.
    Optimize Heap.
    false.
    sep split in H31.
    clear -H32 Hxge0 Hxlt255. 
    unfold val_inj, notint, Int.notbool in H32.
    assert(Int.eq ($ x) ($ SLOT_NUM) = false).
    int auto.
    unfold SLOT_NUM in e. lia.
    unfold SLOT_NUM. lia.
    unfold SLOT_NUM. lia.
    rewrite H in H32.
    rewrite Int.eq_true in H32.
    destruct H32; tryfalse.
    
    hoare_split_pure_all.
    remember v'12 as ls'.
    hoare_lifts_trms_pre(
        Alvarmapsto ios_cap_defs.i
    ).
    (*提前写出的一些成立的前提*)
    assert(Hchildlen: length(child v'14 ls v'50) = Z.to_nat(Int.unsigned i5)).
    {
        unfold child. 
        rewrite Heqls.
        rewrite nth_cspace_length_imp; auto. 
        assert(Z.to_nat (Int.unsigned i5 )<= length l1)%nat.
        unfold MaxChildNum in Hl1len.
        lia. 
        eapply reverse_map_len; eauto. 
    
    }
    


    (*ls'和ls之间的关系*)
    destruct H31.
    rename H31 into Hls2ls'.
    rename x0 into n_class_x.
    assert(Hls'len: length ls'= 64%nat).
    assert(length ls' = length ls).
    unfold reset_nth_cspace_slot_option in Hls2ls'.
    destruct Hls2ls'.
    destruct ((0 <=? n_class_x)%nat &&
    (n_class_x <? Z.to_nat SLOT_NUM)%nat).
     rewrite <- H32.
    eapply reset_nth_cspace_slot_len_eq.
    rewrite H32. auto. 
    rewrite H31. subst ls. 
    rewrite app_length. simpl.
    rewrite H21, H22.
    rewrite S_add_sub_S. lia.
    lia. 
    assert(Hlsls'similar: child_similar ls ls').
    eapply reset_nth_cspace_slot_option_child_similar; eauto.
    
    lets Hirange: unsigned_ge0 i5. 
    assert(Int.unsigned i5 > 0 \/ Int.unsigned i5 = 0) by lia.
    clear Hirange.
    destruct H31 as [Higt0 | Hieq0].
    (*孩子的至少存在一个*)
    assert(Hexists: exists x l, (child v'14 ls v'50) = x :: l).
    {
        destruct (child v'14 ls v'50). 
        simpl in Hchildlen. lia. 
        exists i7 l. 
        auto.  
    }
    destruct Hexists. destruct H31.
    rename H31 into Hchildhead.
    
    hoare remember (1::3::19::21::nil)%nat pre.
    (*循环不变式*)
    eapply backward_rule1 with (p:=
    (EX idx l1 v l2  ls'',
    LV ios_cap_defs.i @ long |-> (V$ (Z.of_nat idx)) **
    [|((S idx) <= Z.to_nat(Int.unsigned i5))%nat|] **
    LV func_capability @ long |-> Vint32 v'9 **
    LV dest_space @ CSPACE ∗
    |-> Vptr (b0 ↝ {i6}) ** 
    ACSpaceAarrayTptr 64%nat (v'5 ++ Vptr (b0 ↝ {i6}) :: v'6) ls'' v'50 **
    [|child v'14 ls v'50 = (l1 ++ v :: l2)|] **
    [|length l1 = idx /\ length l2 = (Z.to_nat(Int.unsigned i5) - (S idx))%nat|] ** 
    [|reset_descendents_cspace_list_slot l1 (Z.to_nat(Int.unsigned v'9)) v'50 ls' ls''|]
    ** H31) 
    (*描述儿子及其后代的清零情况*)
    \\//
    (EX l1 ls'',
    LV ios_cap_defs.i @ long |-> Vint32 i5 **
    LV func_capability @ long |-> Vint32 v'9** 
    LV dest_space @ CSPACE ∗
    |-> Vptr (b0 ↝ {i6}) ** 
    ACSpaceAarrayTptr 64%nat (v'5 ++ Vptr (b0 ↝ {i6}) :: v'6) ls'' v'50 **
    [|child v'14 ls v'50 = l1|] **
    [|reset_descendents_cspace_list_slot l1 (Z.to_nat(Int.unsigned v'9)) v'50 ls' ls''|] ** H31)
    ).

    intros.
    left.
    sep eexists.
    instantiate(5:=0%nat). 
    sep split.
    2: eapply reset_descendents_cspace_list_slot_nil.
    subst ls'. 
    sep cancel H31. sep cancel 1%nat 1%nat. 
    sep cancel 2%nat 1%nat. 
    sep cancel 2%nat 1%nat. auto.
    split; eauto.

    2:{
        simpl.
        eapply Hchildhead.
    }
    rewrite Hchildhead in Hchildlen.
    clear -Hchildlen H9.
    simpl in Hchildlen. lia.
    lia.
    
    (*进入循环已经完成, 下面需要证明循环间的递推关系*)
    (*while statement*)
   
    eapply seq_rule.
    eapply while_rule with (tp := Int32u).
    intros.
    destruct H32.
    sep destruct H32.
    eexists.

    eapply while_statement_val.
    6:{
        sep split in H32.
        sep lifts (1::4::3::nil)%nat in H32.
        exact H32.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H32. 
    assert(length ls' = length x6).
    eapply reset_descendents_cspace_list_slot_length_eq; eauto. 
    rewrite Hls'len in H37.
    auto.
    sep split in H32.
    eapply reset_descendents_cspace_list_slot_similar in H36.
    lets Hy: child_similar_trans Hlsls'similar H36.
    unfolds in Hy. 
    lets Hx: Hy v'14.
    destruct Hx. 
    rewrite <- H37.
    rewrite Heqls.
    rewrite nth_cspace_length_imp; eauto.
    unfold child_num_of. eauto.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    sep destruct H32.
    eexists.
    eapply while_statement_val.
    6:{
        sep split in H32.
        sep lifts (1::4::3::nil)%nat in H32.
        instantiate (10:=Z.to_nat(Int.unsigned i5)).
        rewrite of_to_nat_unsignedv'.
        rewrite Int.repr_unsigned.
        exact H32.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H32. 
    assert(length ls' = length x3).
    eapply reset_descendents_cspace_list_slot_length_eq in H34.
    auto. rewrite Hls'len in H35. auto.
    sep split in H32.
    eapply reset_descendents_cspace_list_slot_similar in H34.
    lets Hy: child_similar_trans Hlsls'similar H34.
    unfolds in Hy. 
    lets Hx: Hy v'14.
    destruct Hx.
    rewrite <- H35. 
    subst ls. 
    rewrite nth_cspace_length_imp; eauto.
    simpl. eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    
    eapply backward_rule1 with (p:=
    (EX (idx : nat) (l0 : list int32)
    (v1 : int32) (l2 : list int32)
    (ls'' : list cspace_val_type),
    LV ios_cap_defs.i @ long
    |-> (V$ Z.of_nat idx) **
    [|(S idx <= Z.to_nat (Int.unsigned i5))%nat|] **
    LV func_capability @ long |-> Vint32 v'9**
    LV dest_space @ CSPACE ∗
    |-> Vptr (b0 ↝ {i6}) **
    ACSpaceAarrayTptr 64
      (v'5 ++ Vptr (b0 ↝ {i6}) :: v'6) ls''
      v'50 **
    [|child v'14 ls v'50 = l0 ++ v1 :: l2|] **
    [|length l0 = idx /\
      length l2 =
      (Z.to_nat (Int.unsigned i5) - S idx)%nat|] **
    [|reset_descendents_cspace_list_slot l0
        (Z.to_nat (Int.unsigned v'9)) v'50 ls' ls''|] ** H31)).
    intros.
    destruct H32.
    destruct H32.
    auto.
    Optimize Proof.
    Optimize Heap.
    false.
    sep destruct H32.
    assert(s
    |= Rv dest_space ′ → child_num >ₑ
          ios_cap_defs.i ′ @ long ==
       val_inj
         (bop_eval (V$ Z.of_nat (Z.to_nat(Int.unsigned i5)))
            (Vint32 i5) long long olt)).
    assert(i5 = $ Z.of_nat(Z.to_nat(Int.unsigned i5))).
    rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned. auto.
    rewrite H34 in H32 at 1.
    clear H34.
    eapply while_statement_val.
    6:{
        sep split in H32.
        sep lifts (1::4::3::nil)%nat in H32.
        exact H32.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H32. 
    assert(length ls' = length x3).
    eapply reset_descendents_cspace_list_slot_length_eq; eauto.
    rewrite Hls'len in H36. auto.
    sep split in H32.
    eapply reset_descendents_cspace_list_slot_similar in H35.
    lets Hy: child_similar_trans Hlsls'similar H35.
    unfolds in Hy. 
    lets Hx: Hy v'14.
    destruct Hx.
    rewrite <- H36.
    subst ls.
    rewrite nth_cspace_length_imp; eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    destruct_s s.
    destruct H33. simpl getsmem in H34.
    destruct H34.
    simpl getsmem in H34.
    destruct H33.
    rewrite H34 in H33.
    inverts H33.
    clear -H36.
    rewrite of_to_nat_unsignedv' in H36.
    rewrite Int.repr_unsigned in H36.
    assert(Int.ltu i5 i5 = false). int auto.
    rewrite H in H36. unfold val_inj in H36.
    unfold istrue in H36. 
    rewrite Int.eq_true in H36. tryfalse.

    hoare_split_pure_all.
    assert(Hv'19len: length v'19 = 64%nat).
    eapply reset_descendents_cspace_list_slot_length_eq in H35.
    rewrite <- H35. auto.

    subst H31.
    eapply backward_rule1.
    intros.
    sep lift 4%nat in H31.
    eapply ACSpaceAarrayTptr_unfold_any_idx_frm with(idx:=Z.to_nat (Int.unsigned v'14)) in H31.
    exact H31.
    rewrite Hv'19len.
    lia.
    auto.
    rewrite app_length. simpl.
    rewrite H18, H23. rewrite S_add_sub_S.
    lia. lia.
    rewrite Hv'19len. lia.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    unfold ACSpace.
    hoare_split_pure_all.
    destruct v'21. destruct p. destruct p. destruct p. destruct v'25.
    hoare_split_pure_all.

    (*这个是数组的一一对应，进行名称上的转换*)
    assert(length v'5 = length v'23).
    destruct H37.
    rewrite H37. auto.
    assert(length v'6 = length v'24).
    destruct H37. rewrite H44.
    auto.
    lets Hx: list_map_eq3 H43 H44 H31.
    destruct Hx.
    destruct H46.
    subst v'23. subst v'24.
    assert(b = b0). inverts H46. auto.
    assert(i6 = i9). inverts H46. auto.
    subst b0 i9. clear H43 H44 H46.
    clear H31. 
    unfold child in H33.
    rewrite  Heqls in H33.
    rewrite nth_cspace_length_imp in H33.
    assert(i5 = i8 /\ l = l1).
    eapply reset_descendents_cspace_list_slot_similar in H35.
    lets Hy: child_similar_trans Hlsls'similar H35.
    unfold child_similar in Hy.
    lets Hx: Hy v'14.
    subst ls v'19.
    rewrite nth_cspace_length_imp in Hx; eauto.
    rewrite nth_cspace_length_imp in Hx; eauto.
    simpl in Hx. 
    destruct Hx.
    inverts H31. inverts H36. auto.
    destruct H38. auto.
    destruct H31.
    subst i8 l1.

    eapply backward_rule1.
    intros.
    sep lift 4%nat in H31.
    unfold Aarray in H31 at 1.
    eapply Aarray'_unfold_any_idx_frm with (idx:=v'13) in H31.
    exact H31.
    unfold MaxChildNum.
    lia.
    auto. unfold MaxChildNum. simpl.
    rewrite max_unsigned_val.
    lia.
    simpl typelen. rewrite max_unsigned_val. lia.
    hoare_split_pure_all.

    
    assert(rule_type_val_match UNION cspace ⋆ v'24 =
    true).
    clear -H41 H31.
    subst l.
    eapply array_type_match2rule_type_match; eauto.

    eapply rule_type_val_match_comptr_elim in H44.
    unfold isptr in H44.
    destruct H44.
    unfolds in H15.
    assert(0 <= v'13 < Z.to_nat (Int.unsigned i5))%nat by lia.
    eapply H15 in H45.
    subst l.
    rewrite nth_val'_length_imp in H45.
    tryfalse.
    destruct H45. rewrite H44 in H31. tryfalse.
    destruct H43. auto.
    destruct H44. subst v'24.
    assert(0<= Int.unsigned (Int.repr (Z.of_nat v'13)) < 255).
    rewrite Int.unsigned_repr. lia.
    rewrite max_unsigned_val. lia.
    unfolds in H9.
    assert(nth_val ∘ (Int.unsigned ($ Z.of_nat v'13)) l =
    Some (Vptr x2)).
    
    eapply nth_val'2nth_val_ptr.
    rewrite Int.unsigned_repr.
    subst l. 
    eapply nth_val'_length_imp.
    rewrite nat_of_Z_of_nat.
    destruct H43. auto.
    rewrite max_unsigned_val. lia. 
    lets Hx: H9 H45. 
    destruct Hx.
    destruct H46 as [Hx2 Hx3].
    assert(child v'14 ls v'50 = reverse_map v'50  l).
    unfold child. 
    subst ls. 
    rewrite nth_cspace_length_imp; eauto.
    rewrite H33 in H46.


    lets Hx: wellform_descendents_trans_general2 H46 H6.
    destruct Hx. destruct H47. destruct H47.
    rename H46 into Hchildsplit.
    (*子孙后代分割, 左边一部分, 中间要执行的， 右边一部分，以及每一部分都不相交*)
    destruct H47 as [Hchildlist [Hwleft [Hwx [Hwright [Hx4x5 [Hx4x6 Hx5x6]]]]]].
    assert(x3 = v'17).
    rewrite Heqls in Hchildsplit.
    unfold child in Hchildsplit.
    rewrite nth_cspace_length_imp in Hchildsplit; eauto.
    rewrite H31 in Hchildsplit.

    assert(length v'21 = length v'16).
    destruct H43, H34.
    rewrite H34, H43. auto.
    assert(length v'21 < (Z.to_nat (Int.unsigned i5)))%nat. 
    destruct H43. rewrite H43.
    lia.
    Optimize Proof.
    Optimize Heap.
    eapply reverse_map_injection; eauto.
    subst l. auto. 
    subst v'17.

    eapply seq_rule.
    eapply call_rule'.
    unfold Cap_spec. simpl. unfold CNode_delete_recursive_spec.
    eauto.
    intros.
    eapply rvl_elim.
    eapply cast_rv_struct_tptr.
    eapply lv_mapsto_to_rv.
    2:{
        eapply field_array_asrt_impl.
        7:{
            exact H46.
        }
        3:{
            intros.
            sep_lifts_trms_in H47 (Alvarmapsto ios_cap_defs.i).
            eapply LV_to_Rv in H47.
            eapply inline_tactics.monoasrt_mono in H47.
            exact H47.
            eapply inline_tactics.Rv_mono.
            auto.
            simpl. auto.
        }
        3: auto.
        4:{
           intros.
           sep_lifts_trms_in H47 (Alvarmapsto dest_space).
           unfold CSPACE in H47 at 1.
           exact H47.
        }
        unfold field_offset. simpl. rewrite Int.add_zero.
        change ($ 4 +ᵢ  $ 5108) with ($5112).
        eauto.
        instantiate(1:=2%nat). simpl. auto.
        simpl.
        eauto.
    }
    2:{
        sep lift 2%nat in H46.
        rewrite <- addition_trans.
        simpl typelen.
        rewrite Int.unsigned_repr.
        rewrite Nat2Z.id.
        simpl typelen in H46.
        assert((i6 +ᵢ  $ 5108) +ᵢ  $ 4 = i6 +ᵢ  $ 5112).
        rewrite Int.add_assoc.
        change ($ 5108 +ᵢ  $ 4) with ($5112).
        auto.
        rewrite H47 in H46 at 1.
        unfold Aptrmapsto in H46 at 1.
        exact H46.

        clear -H32 H24.
        int auto.
        simpl.  lia.
    }
    clear -H41 H31.
    subst l. 
   
    eapply array_type_match2rule_type_match; eauto.
    clear -H41 H31.
    subst l. 
    eapply array_type_match2rule_type_match; eauto.

    eapply rvl_elim.
    sep_lifts_trms_in H46 (Alvarmapsto func_capType).
    eapply LV_to_Rv in H46.
    eapply inline_tactics.monoasrt_mono in H46.
    exact H46.
    eapply inline_tactics.Rv_mono.
    auto. simpl. auto.
    clear -H2.
    assert(Int.unsigned v'10 <=? Byte.max_unsigned = true).
    change Byte.max_unsigned with 255. int auto. 
    rewrite H. auto. 
    eapply rvl_elim.
    sep get rv.
    eapply rvl_nil.
    intros.
    unfold getasrt.
    unfold CNode_delete_recursivePre.
    unfold CNode_delete_recursivePre'.
    eapply Aarray'_fold_any_idx_frm  in H46; eauto.
    fold Aarray in H46.
    sep lifts (3::4::1::5::6::nil)%nat in H46.
    
    eapply fold_ACSpace in H46; eauto.
    sep lifts (2::1::3::nil)%nat in H46.
    eapply ACSpaceAarray_fold_any_idx_frm in H46; eauto.


    unfold AOSCSpacePrioTbl.
    sep split; eauto. 
    sep normal. sep eexists.
    sep cancel Aie. sep cancel Aier. sep cancel Ais.
    sep cancel Acs. sep cancel Aisr. sep cancel Aop.
    sep split.
    2: eauto.
    sep cancel OSCSpacePrioTbl.
    unfold Aarray.
    sep cancel Aarray'.
    sep cancel ACSpaceAarrayTptr.
    sep cancel p_local.
    sep cancel ASeminfo.
    sep cancel APthreadMutex.
    sep cancel AMqAttr.
    sep cancel AOSCSpaceObjectPointer.
    sep cancel AOSTCBPrioTbl.
    exact H46.
    splits. rewrite app_length. simpl. 
    rewrite H18, H23. rewrite S_add_sub_S.
    clear -H5. lia. 
    clear -H5. lia.
    rewrite Hv'19len. auto.
    auto. 
    unfold ptrvl_to_cspace_to_ptrvl. split; auto.
    auto. 
    5: simpl; eauto.
    4: simpl. eauto.
    4: simpl; eauto.
    3: eapply Hx2.
    assert(Hsimilar2: child_similar ls' v'19).
    eapply reset_descendents_cspace_list_slot_similar in H35.
    auto.
    lets Hsimilar3: child_similar_trans Hlsls'similar Hsimilar2.
    lets Hwv'19: wellform_descendents_child_similar Hwx Hsimilar3.
    eapply Hwv'19.

    lia.
    simpl. eauto.
    lia. lia. 
    auto. lia. lia. 
    unfold MaxChildNum.
    lia.
    unfold MaxChildNum.
    simpl. rewrite max_unsigned_val. lia.
    simpl. rewrite max_unsigned_val. lia.
    go. 
    unfold getasrt. unfold CNode_delete_recursivePost.
    unfold CNode_delete_recursivePost'.

    intros. sep normal in H46. sep destruct H46.
    eexists. sep cancel p_local.
    simpl. auto.
    unfold getasrt.
    unfold CNode_delete_recursivePre. 
    unfold CNode_delete_recursivePre'.
    intros. sep destruct H46.
    eexists. sep cancel p_local. simpl. auto.
    simpl. auto.
    unfold getasrt. unfold CNode_delete_recursivePost.
    unfold CNode_delete_recursivePost'.
    clear -H2.
    assert(Int.unsigned v'10 <=? Byte.max_unsigned = true).
    change Byte.max_unsigned with 255.
    int auto. 
    rewrite H. auto. 
    unfold getasrt. unfold CNode_delete_recursivePost.
    unfold CNode_delete_recursivePost'.
    hoare_split_pure_all.
    
    
    simpl in H47, H48, H49.
    inverts H47. inverts H48. inverts H49.
    inverts H53.
    
    assert (Hsuc: ($ Z.of_nat v'13 +ᵢ  $ 1) = ($ (Z.of_nat (S v'13)))).
    {
        clear -H32 H1.
        int auto.
    }
    assert (Hcond: Z.of_nat (S v'13) = (Int.unsigned i5) \/ Z.of_nat (S v'13) < (Int.unsigned i5)).
    clear -H32 H1.
    int auto.
    destruct Hcond as [Hco1 | Hco2].
    
    assert(x3 = v'48).
    rewrite Hx2 in H46. inverts H46. auto.
    subst v'48.
    (*1 case*)
    hoare normal pre; hoare_ex_intro.
    eapply forward_rule2.
    hoare_forward_first.
    intros.
    rewrite Hsuc in H36.
    rewrite Hco1 in H36.
    
    rewrite Int.repr_unsigned in H36.
    eapply adisj_intro.
    right.
    unfold AOSCSpacePrioTbl in H36.
    unfold Aarray in H36.
    sep auto.
    Optimize Proof.
    Optimize Heap.
    remember (v'21 ++ Vptr v'24 :: v'23) as l.
    remember (v'2 ++
    (i2, i3,
    v'3 ++
    (v'11, (i, (i0, i1, v))) :: v'8, i5,
    l, v0, i4) :: v'4) as ls. 
    remember (reset_nth_cspace_slot_option v'14
    (Z.to_nat x) n_class_x ls) as ls'.
    assert(v'18 = nil).
    clear -H34 Hco1.
    destruct H34.
    assert((Z.to_nat (Int.unsigned i5) - S v'13) = 0)%nat by lia.
    rewrite H1 in H0. 
    destruct v'18. auto. simpl in H0. tryfalse.
    subst v'18.
    (*v'40是v'14的最后一个儿子节点的int编号*)
    rewrite Hchildsplit.
    clear -H35 H52.

    eapply reset_descendents_cspace_list_slot_append; eauto.

    (*2 case*)
    assert(v'48 = x3).
    rewrite Hx2 in H46. inverts H46. auto.
    subst v'48.
    assert(Hv'18exists: exists x l, v'18 = x :: l).
    assert(length v'18 > 0)%nat. 
    destruct H34. rewrite H36. clear -Hco2. lia.
    destruct v'18. simpl in H36. lia.
    exists i8 v'18. auto.
    destruct Hv'18exists.
    destruct H36.
    subst v'18.
    hoare normal pre; hoare_ex_intro.
    eapply forward_rule2.
    hoare_forward_first.
    intros.
    rewrite Hsuc in H36.
    eapply adisj_intro.
    left.
    unfold AOSCSpacePrioTbl in H36.
    sep auto.
    clear -H35 H52.
    lets Hx: reset_descendents_cspace_list_slot_append H35 H52.
    eapply Hx. 
    clear -H34 Hco2.
    splits. rewrite app_length.
    simpl. destruct H34. rewrite H31. lia.
    instantiate(1:= x7).
    destruct H34. clear -H34 Hco2.
    simpl in H34. lia.
    instantiate(1:= x2).
    unfold child.
    rewrite nth_cspace_length_imp; eauto.
    rewrite H33. 
    rewrite <- list_cons_assoc.
    auto.
    lia. auto.

    (*循环推理结束*)
    eapply backward_rule1.
    intros.
    destruct H32. 
    destruct H32.
    false. 
    sep destruct H32.
    assert(s
    |= Rv dest_space ′ → child_num >ₑ
          ios_cap_defs.i ′ @ long ==
       val_inj
         (bop_eval (V$ Z.of_nat x2)
            (Vint32 i5) long long olt)).
    eapply while_statement_val.
    6:{
        sep split in H32.
        sep lifts (1::4::3::nil)%nat in H32.
        exact H32.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H32. 
    assert(length ls' = length x6).
    eapply reset_descendents_cspace_list_slot_length_eq; eauto.
    rewrite Hls'len in H38. auto.
    sep split in H32.
    eapply reset_descendents_cspace_list_slot_similar in H37.

    lets Hy: child_similar_trans Hlsls'similar H37.
    lets Hx: Hy v'14.
    destruct Hx.
    rewrite <- H38.
    subst ls.
    rewrite nth_cspace_length_imp; eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    destruct H33.
    destruct H34.
    rewrite H34 in H33.
    destruct H33. inverts H33.
    sep split in H32.
    clear -H33 H36 H1.
    assert(Int.ltu ($ Z.of_nat x2) i5 = true).
    eapply Intlt_true_is_Zlt.
    rewrite Int.unsigned_repr. lia. 
    rewrite max_unsigned_val. lia. 
    rewrite H in H36. 
    unfold istrue in H36. 
    simpl in H36. 
    assert(Int.eq Int.one Int.zero = false) by auto.
    rewrite H0 in H36. 
    tryfalse.
    exact H32.

    eapply ret_rule'.
    intros.
    sep destruct H32.
    subst H31.
    unfold CNode_delete_recursivePost'.
    unfold AOSCSpacePrioTbl.
    sep normal. sep eexists.
    sep cancel OSCSpacePrioTbl.
    sep cancel ACSpaceAarrayTptr.
    sep cancel ASeminfo.
    sep cancel APthreadMutex.
    sep cancel AMqAttr.
    sep cancel AOSCSpaceObjectPointer.
    sep cancel AOSTCBPrioTbl.
    sep cancel Aie. sep cancel Aisr.
    sep cancel Aier. sep cancel Ais.
    sep cancel Acs. sep cancel Aop.
    sep cancel A_dom_lenv.
    sep split;[idtac|simpl; eauto..].
    unfold Aarray. sep cancel Aarray'.
    sep cancel p_local. sep cancel (Alvarmapsto os_code_defs.x).
    sep cancel (Alvarmapsto cap1).
    sep cancel (Alvarmapsto ios_cap_defs.i).
    sep cancel dest_space.
    sep cancel func_capType. 
    sep cancel func_capability.
    sep split in H32. auto.
    sep split in H32.
    eapply reset_descendents_cspace_slot_neqnull; eauto.
   
    rewrite H31. auto.
    splits. rewrite app_length.
    simpl. rewrite H18, H23. rewrite S_add_sub_S.
    lia. lia.
    sep split in H32.
    eapply reset_descendents_cspace_list_slot_length_eq in H33.
    rewrite <- H33.
    auto.
    auto.

    
    

    (*当i等于0的时候, 不进入循环*)
    eapply seq_rule.
    eapply while_rule with (tp := Int32u).
    intros.
    sep destruct H31.
    eexists.

    eapply while_statement_val.
    6:{
        sep split in H31.
        sep lifts (1::3::15::nil)%nat in H31.
        instantiate (10:=0%nat).
        exact H31.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H31.
    auto. 
    unfolds in Hlsls'similar.
    lets Hx: Hlsls'similar v'14.
    destruct Hx.
    rewrite <- H32.
    subst ls. rewrite nth_cspace_length_imp; eauto.
    simpl. eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    eapply backward_rule1.
    intros.
    instantiate(1:=Afalse).
    simpl. 
    destruct H31.
    assert(s
    |= Rv dest_space ′ → child_num >ₑ
          ios_cap_defs.i ′ @ long ==
       val_inj
         (bop_eval (V$ Z.of_nat 0)
            (Vint32 i5) long long olt)).
    eapply while_statement_val.
    6:{
        sep split in H31.
        sep lifts (1::3::15::nil)%nat in H31.
        exact H31.
    }
    3: eauto.
    2: lia.
    2: lia.
    sep split in H31. 
    auto.
    Optimize Proof.
    Optimize Heap.
    unfolds in Hlsls'similar.
    lets Hx: Hlsls'similar v'14.
    destruct Hx.
    rewrite <- H33.
    subst ls.
    rewrite nth_cspace_length_imp; eauto.
    clear -H4.
    eapply nth_val_nth_val'_some_eq in H4.
    rewrite H4. auto.
    destruct H32, H33.
    rewrite H33 in H32.
    clear -Hieq0 H32.
    unfold val_inj, bop_eval in H32.
    unfold cmp_val, cmpu in H32.
    assert(Int.ltu ($ Z.of_nat 0) i5 = false).
    int auto. 
    rewrite H in H32. 
    destruct H32. inverts H0.
    unfold istrue in H1.
    rewrite Int.eq_true in H1. tryfalse.
    eapply pfalse_rule.
    
    eapply ret_rule'.
    intros.
    destruct H31. clear H32.
    sep destruct H31.
    unfold CNode_delete_recursivePost'.
    sep auto.
    unfold AOSCSpacePrioTbl.
    sep auto.
    
    3: simpl; eauto.
    3: simpl; eauto.
    3: simpl; eauto.
    2: simpl; eauto.
    auto.
    remember (v'2 ++
    (i2, i3,
    v'3 ++ (v'11, (i, (i0, i1, v))) :: v'8,
    i5, l1, v0, i4) :: v'4) as ls.
    assert(child v'14 ls v'50 = nil).
    clear -Hchildlen Hieq0. 
    destruct (child v'14 ls v'50); tryfalse; auto.
    rewrite Hieq0 in Hchildlen. simpl in Hchildlen.
    lia. 
    eapply reset_descendents_cspace_slot_neqnull; eauto.
    rewrite H32.
    eapply reset_descendents_cspace_list_slot_nil.
Qed.








    



    

    