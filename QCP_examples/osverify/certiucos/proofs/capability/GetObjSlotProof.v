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
Require Import GetObjSlotPure.
Require Import CapSpec.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope int_scope.
Open Scope Z_scope.
Set Nested Proofs Allowed.

Notation "E '..' I" := (efield E I) (at level 10)  : code_scope.


Lemma Get_Obj_Slot_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal Get_Obj_Slot
                  vl logicl Get_Obj_SlotPre ct->
      Some r =
      BuildRetI os_internal Get_Obj_Slot vl logicl Get_Obj_SlotPost ct->
      exists t d1 d2 s,
      os_internal Get_Obj_Slot = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
    init spec. 
    simpl in H3, H4.
    inverts H3.
    inverts H4.
    assert(Htrue: Int.unsigned v'2 <=? Byte.max_unsigned = true).
    change Byte.max_unsigned with 255.
    clear -H2. int auto.
    eapply seq_rule.
    hoare forward.
    rename H6 into Hptr.
    rewrite Htrue. auto.
    destruct (Int.ltu ($ OS_LOWEST_PRIO) v'2); auto.
    rewrite Htrue. auto.
    destruct (Int.eq v'2 ($ OS_LOWEST_PRIO)); auto.
    destruct (Int.ltu ($ OS_LOWEST_PRIO) v'2);
    destruct (Int.eq v'2 ($ OS_LOWEST_PRIO)); auto.
    hoare_split_pure_all.
    eapply rete_rule'.
    intros.
    {
        destruct_s s.
        simpl. 
        splits; eauto.
    }

    (*第一个条件成立*)
    {
      intros.
      sep auto.
      sep lift 3%nat.
      eapply disj_split.
      right.
      sep auto.
      3: simpl; eauto.
      3: simpl; eauto.
      2: auto.
      destruct H3.
      unfold bool_or, val_inj in H3.
      destruct (Int.ltu ($ OS_LOWEST_PRIO)
      v'2) eqn: Hlt;
      destruct (Int.eq v'2 ($ OS_LOWEST_PRIO))eqn: Heq;
      val_help_H H3; simpl in H3; tryfalse;
      try(eapply Intlt_true_is_Zlt in Hlt);
      try(eapply Inteq_true_is_Zeq in Heq);
      try(rewrite Int.unsigned_repr in Hlt);
      try(rewrite Int.unsigned_repr in Heq);
      try lia.
      unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
      unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
      unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
      unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
    }
    rename H6 into Hptr.

    eapply backward_rule1.
    intros.
    destruct H3.
    eapply astar_l_afalse_elim in H3.
    simpl in H3. tryfalse.
    exact H3.
    pure intro.

    eapply seq_rule.
    hoare lift 6%nat pre.
    eapply encrit2_rule'.
    intros. 
    sep lifts (4::5::1::2::3::nil)%nat in H4. 
    exact H4. 
    apply GoodI_I.
    Ltac p_local_go:= 
      try unfold p_local;
      try unfold CurTid;
      try unfold OSLInv;
      try unfold LINV;
      try unfold AOSCSpacePrioTbl;
      try unfold AOSExchandler;
      try good_frm_sovler;
      try go.
    p_local_go.
    (* apply GoodFrm_ACSpaceAarrayTptr. *)
    unfold AOSCSpaceObjectPointer.
    good_frm_sovler.

    
    (*endPtr ′ =ₑ OSCSpaceObjectPointer ′ [prio ′]*)
    unfold AOSCSpaceObjectPointer.
    pure intro.
    rename H6 into Hpointervl.
    assert(Hv'2lt63: Int.unsigned v'2 < 63).
    unfold val_inj, bool_or in H3.
    destruct (Int.ltu ($ OS_LOWEST_PRIO) v'2) eqn: Hlt;
    destruct (Int.eq v'2 ($ OS_LOWEST_PRIO)) eqn: Heq;
    val_help_H H3; simpl in H3; destruct H3;tryfalse.
    eapply Intlt_false_is_Zge in Hlt.
    eapply Inteq_false_is_Zneq in Heq.
    rewrite Int.unsigned_repr in Hlt, Heq.
    unfold OS_LOWEST_PRIO in Hlt, Heq.
    lia. 
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
    unfold OS_LOWEST_PRIO. rewrite max_unsigned_val. lia.
    lets Hrange1: Int.unsigned_range_2 (v'2).
    destruct Hrange1.
    assert(0 <= 64). lia. 
    lets Hrange: Z2Nat.inj_lt H6 H8.
    assert(Int.unsigned v'2 < 64) by lia.
    eapply Hrange in H9.
    clear Hrange.
    assert(Hprionat: (Z.to_nat(Int.unsigned v'2) < Z.to_nat 64)%nat) by lia.
    lets Hexists: nthval'_has_value_Tint32 H4 H5 Hprionat.
    
    destruct Hexists.
    destruct H10. 
    assert(Int.unsigned x <= 255).
    clear -H5 H6 H7 Hpointervl  Hprionat H10.
    unfold objectpointer in Hpointervl.
    assert((0<= (Z.to_nat (Int.unsigned v'2))<length v'10)%nat).
    split; lia.
    eapply inline_bittblfunctions.nth_val'2nth_val in H10.
    lets Htmp: Hpointervl H H10.
    lia.
    clear H6 H7 H8  H9 Hprionat H11.
    rename H12 into Hxlt255.
    
    hoare forward.
    rewrite Htrue. auto.
    eapply array_type_vallist_match_imp_rule_type_val_match.
    
    rewrite H5.
    lia. 
    auto.
    rewrite H10.
    rename H10 into Hnth_val'ofv'10.

    unfold AOSCSpacePrioTbl.
    hoare_split_pure_all.
    assert(Htypematch: array_type_vallist_match 
    CSPACE ∗ v'11). simpljoin1. auto.
    assert(Hv'11len: length v'11 = 64%nat).
    simpljoin1. auto.
    assert(Hv'12len: length v'12 = 64%nat).
    simpljoin1. auto.
    eapply backward_rule1 with (p:=<|| v'5 ||>  **
    LV endPtr @ long |-> Vint32 x **
    Aier v'4 **
    Aisr v'7 **
    Aie false **
    Ais nil **
    Acs (false :: v'6) **
    AOSCSpacePrioTbl (v'8 ↝ {v'9}) v'11
      v'12 v'13 **
    GAarray OSCSpaceObjectPointer
      (Tarray long 64) v'10 **
    p_local OSLInv ct init_lg **
    LV pCSpace @ CSPACE ∗ |-> v'1 **
    LV i @ long |-> v' **
    LV func_object @ (Void) ∗ |-> v'3 **
    LV prio @ char_t |-> Vint32 v'2 **
    A_dom_lenv
      ((func_object ↝ {(Void) ∗})
       :: (prio ↝ {char_t})
          :: (i ↝ {long})
             :: (endPtr ↝ {long})
                :: (pCSpace ↝ {CSPACE ∗})
                   :: nil)).
    intros. unfold AOSCSpacePrioTbl.
    sep auto.
    clear H6.
    unfold AOSCSpacePrioTbl.
    eapply seq_rule.
    hoare normal pre. hoare_ex_intro.
    Require Import seplog_trm_tacs.
    hoare_lifts_trms_pre (Aop, Alvarmapsto pCSpace).
    eapply assign_rule_lvar.
    intros. splits; intros.
    exact H6. auto.
    intros.
    eapply array_member_rv_g.
    unfold GAarray.
    sep normal. sep eexists. sep cancel OSCSpacePrioTbl.
    sep cancel Aarray. sep cancel A_dom_lenv.
    eauto. simpl. auto. eauto.
    sep get rv.
    rewrite Htrue. auto.
    eauto. auto. lia. lia.
    sep split in H6. destruct H7. rewrite H7. lia.
    2: eauto.
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    sep split in H6. destruct H7. rewrite H7. lia.
    eapply eq_vptr. eauto.
    intros. eexists. sep cancel p_local. simpl. auto.
    eapply seq_rule.
    eapply excrit2_rule'.
    intros.
    sep lifts (4::3::5::6::7::nil)%nat in H6.
    exact H6.
    apply GoodI_I.
    p_local_go. 
    (* eapply GoodFrm_ACSpaceAarrayTptr. *)
    eapply backward_rule1 with (p:=<|| v'5 ||>  **
    Aisr v'7 **
    Aier v'4 **
    Aie false **
    Ais nil **
    Acs v'6 **
    LV pCSpace @ CSPACE ∗
    |-> nth_val'
          (Z.to_nat (Int.unsigned v'2))
          v'11 **
    LV endPtr @ long |-> Vint32 x **
    AOSCSpacePrioTbl (v'8 ↝ {v'9}) v'11
      v'12 v'13 **
    GAarray OSCSpaceObjectPointer
      (Tarray long 64) v'10 **
      p_local OSLInv ct init_lg **
      LV i @ long |-> v' **
      LV func_object @ (Void) ∗ |-> v'3 **
      LV prio @ char_t |-> Vint32 v'2 **
      A_dom_lenv
        ((func_object ↝ {(Void) ∗})
         :: (prio ↝ {char_t})
            :: (i ↝ {long})
               :: (endPtr ↝ {long})
                  :: (pCSpace ↝ {CSPACE ∗})
                     :: nil)).
    intros. unfold AOSCSpacePrioTbl. sep auto.
    assert(HpCSpacetype: rule_type_val_match CSPACE ∗ (nth_val'
    (Z.to_nat (Int.unsigned v'2))
    v'11 ) = true).
    eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hv'11len. lia.
    hoare forward.
    unfold val_inj, val_eq. 
    clear -HpCSpacetype.
    unfold rule_type_val_match in HpCSpacetype.
    destruct (nth_val'
    (Z.to_nat (Int.unsigned v'2))
    v'11); tryfalse; auto. destruct a. auto.
    hoare_split_pure_all.
    eapply rete_rule'.
    intros.  unfold SLOT_NULL_CAP.
    destruct_s s. simpl. splits; eauto.
    intros.
    sep normal. sep eexists.
    unfold AOSCSpacePrioTbl in H7. sep auto.
    sep lift 4%nat. 
    eapply disj_split.  left.
    unfold OS_LOWEST_PRIO. sep split; auto.
    sep normal. sep eexists.
    eapply disj_split. left.
    sep auto; auto.
    clear -H6 HpCSpacetype.
    destruct H6.
    unfold val_inj, val_eq in H.
    unfold rule_type_val_match in HpCSpacetype.
    destruct (nth_val' (Z.to_nat (Int.unsigned v'2)) v'11); tryfalse; auto;
    destruct a; tryfalse.
    auto.
    eapply disj_rule.
    hoare_split_pure_all.
    eapply pfalse_rule.
    hoare_split_pure_all.
    assert(Hnotnull:nth_val'
    (Z.to_nat (Int.unsigned v'2))
    v'11 <> Vnull).
    clear -H6 HpCSpacetype.
    unfold val_inj, val_eq in H6.
    unfold rule_type_val_match in HpCSpacetype.
    destruct (nth_val'(Z.to_nat(Int.unsigned v'2))
    v'11); tryfalse; auto; destruct H6; tryfalse.
    clear H6.

    eapply backward_rule1.
    intros.
    sep lift 9%nat in H6.
    eapply AOSCSpacePrioTbl_unfold_any_idx_frm with(idx:= Z.to_nat(Int.unsigned v'2)) in H6.
    exact H6.
    rewrite Hv'12len. lia.
    auto.
    
    pure intro.
    eapply backward_rule1.
    intros.
    unfold ACSpace in H6. 
    unfold Acnode in H6.
    exact H6.
    pure intro.
    destruct v'15. destruct p. destruct p. 
    destruct p.
    destruct v'19.
    destruct c.  destruct p.
    eapply backward_rule1.
    intros.
    sep normal in H6.
    sep lift 7%nat in H6. 
    exact H6.
    pure intro.
    rename H16 into Hirange.

    (*i ′ =ₑ′ OBJ_POSITION;ₛ*)
    hoare forward.
    Require Import seplog_trm_tacs.
    (*WHILE (endPtr ′ >ₑ i ′)*)
    (*分成 i < endPtr和 i >= endPtr两种情况*)
    assert(Hiend: OBJ_POSITION < Int.unsigned x \/ OBJ_POSITION >= Int.unsigned x) by lia.
    destruct Hiend as [Hiendlt | Hiendge].
    hoare_lifts_trms_pre 
    (ASlots, 
    Alvarmapsto ios_cap_defs.i, 
    Alvarmapsto endPtr,
    Alvarmapsto pCSpace,
    Alvarmapsto func_object
    ).
    hoare remember (1::2::3::4::5::nil)%nat pre.
    eapply backward_rule1.
    intros.
    eapply ASlots_unfold_any_idx_frm in H17; eauto.
    instantiate (1:=Z.to_nat(OBJ_POSITION)). 
    unfold OBJ_POSITION. unfold SLOT_NUM. lia.
    hoare_split_pure_all.
    destruct H18.
    rename H18 into Hlengthv'11.
    rename H20 into Hlengthv'12.
    rename H19 into HnthSlots.
    eapply backward_rule1 with (p:=
      (
      (EX idx vll11 vll12 vll2 slot_type slot_cap,
      LV ios_cap_defs.i @ long |-> (V$ (Z.of_nat idx)) **
      ASlots (b, i1 +ᵢ  $ 8) idx (vll11 ++ vll12)**
      PV (b, i1 +ᵢ  $ 8+ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
      ACap (b, i1 +ᵢ  $ 8 +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
      ** ASlots (b, i1 +ᵢ  $ 8 +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (Z.to_nat SLOT_NUM - (S idx)) vll2
      ** [|l0 = (vll11 ++ vll12) ++ (slot_type, slot_cap):: vll2|] **
      [|length vll11 = (Z.to_nat (OBJ_POSITION)) /\ length (vll11 ++ vll12) = idx 
       /\ length vll2 = (255 - (S idx))%nat|] **
      [|((S idx) <= Z.to_nat(Int.unsigned x))%nat|]  ** 
      [|Slots_neq_object vll12 v'3|]) ** (*循环不变式*)
      LV endPtr @ long |-> Vint32 x **
      LV pCSpace @ CSPACE ∗ |-> Vptr (b ↝ {i1})**
      LV func_object @ (Void) ∗ |-> v'3 **
      H16) \\//
      (
      (EX vll11 vll12 vll2, 
      LV ios_cap_defs.i @ long |-> Vint32 x **
      LV endPtr @ long |-> Vint32 x ** 
      LV pCSpace @ CSPACE ∗ |-> Vptr (b, i1)**
      LV func_object @ (Void) ∗ |-> v'3**
      ASlots(b, i1 +ᵢ $8)(Z.to_nat SLOT_NUM) (vll11 ++ vll12++vll2) **
      [|l0 = vll11++vll12 ++ vll2|] **
      [|length vll11 = Z.to_nat(OBJ_POSITION) /\ length (vll11 ++ vll12) = Z.to_nat(Int.unsigned x)
      /\length(vll11++vll12++vll2) = Z.to_nat SLOT_NUM|] ** 
      [|Slots_neq_object vll12 v'3|]) ** H16)
    ).
    subst l0.
    intros.
    left.
    unfold OBJ_POSITION in *.
    sep normal. sep eexists.
    sep cancel H16.
    instantiate(1:=nil).
    instantiate (5:=v'11).
    rewrite app_nil_r.
    sep cancel ASlots.
    change (Z.of_nat (Z.to_nat 17)) with 17.
    sep cancel ios_cap_defs.i.
    sep pauto.
    rewrite nth_val'_length_imp; auto.
    unfold Slots_neq_object. simpl. auto with zarith.
    lia. 
  
    eapply seq_rule.

    eapply while_rule with (tp := Int32u).

    intros.
    destruct H18.
    symbolic_execution.
    destruct (Int.ltu ($ Z.of_nat x0) x); simpl; auto.
    symbolic_execution.
    destruct (Int.ltu x x); simpl; auto.
    eapply backward_rule1 with (p:=
    (
      (EX idx vll11 vll12 vll2 slot_type slot_cap,
      LV ios_cap_defs.i @ long |-> (V$ (Z.of_nat idx)) **
      ASlots (b, i1 +ᵢ  $ 8) idx (vll11 ++ vll12)**
      PV (b, i1 +ᵢ  $ 8+ᵢ $ Z.of_nat (idx * (typelen Slot))) @ Int32 |-> Vint32 slot_type ** 
      ACap (b, i1 +ᵢ  $ 8 +ᵢ $ Z.of_nat (idx * (typelen Slot)) +ᵢ (Int.repr 4)) slot_cap
      ** ASlots (b, i1 +ᵢ  $ 8 +ᵢ $ Z.of_nat ((S idx) * (typelen Slot))) (Z.to_nat SLOT_NUM - (S idx)) vll2
      ** [|l0 = (vll11 ++ vll12) ++ (slot_type, slot_cap):: vll2|] **
      [|length vll11 = (Z.to_nat (OBJ_POSITION)) /\ length (vll11 ++ vll12) = idx 
       /\ length vll2 = (255 - (S idx))%nat|] ** 
       [|((S idx) <= Z.to_nat (Int.unsigned x))%nat|]  ** 
      [|Slots_neq_object vll12 v'3|]) (*循环不变式*)
      **LV endPtr @ long |-> Vint32 x **
      LV pCSpace @ CSPACE ∗ |-> Vptr (b ↝ {i1})**
      LV func_object @ (Void) ∗ |-> v'3 **
       H16)
    ).
    intros.
    destruct H18.
    destruct H18.
    sep normal in H18.
    do 6 destruct H18.
    sep normal. do 6 eexists.
    sep pauto.
  
    sep normal in H18.
    sep destruct  H18.
    sep remember(1::2::nil) in H18. 
    false. 
    destruct_s s. 
    destruct H18. simpljoin.
    simpl in H21, H23, H24. simpljoin1.
    destruct H25. simpljoin.
    simpl in H17, H20, H23. simpljoin1.
    simpl in H19.
    rewrite H22, H27 in H19.
    unfold cmp_int_type in H19.
    rewrite Int.unsigned_zero in H24, H28.
    apply mapstoval_load in H24, H28.
    lets Hloadv'12: load_local H21 H24.
    lets Hloadx2': load_local H17 H28.
    apply map_join_comm in H21.
    lets Hloadx2: load_local H21 Hloadx2'.
    rewrite Hloadx2 in H19.
    rewrite Hloadv'12 in H19.
    unfold cmp_val in H19. unfold cmpu in H19.
    assert(Int.ltu x x = false).
    unfold Int.ltu.
    apply zlt_false.
    lia. rewrite H16 in H19.
    destruct H19. destruct H18.
    inverts H18.
    simpl in H19. tryfalse.
    auto. auto.

    
    unfold ACap.
    hoare_split_pure_all.
    destruct v'25.  destruct c. 
    destruct p. 
    
    assert(Hgetp:
    LV ios_cap_defs.i @ long
  |-> (V$ Z.of_nat v'20) **
  ASlots (b ↝ {i1 +ᵢ  $ 8}) v'20
    (v'21 ++ v'22) **
  PV b
     ↝ {(i1 +ᵢ  $ 8) +ᵢ
        $
        Z.of_nat
          (v'20 * typelen Slot)} @
  long |-> Vint32 v'24 **
  (PV b
      ↝ {((i1 +ᵢ  $ 8) +ᵢ
          $
          Z.of_nat
            (v'20 * typelen Slot))
         +ᵢ  $ 4} @ long
   |-> Vint32 i4 **
   PV b
      ↝ {(((i1 +ᵢ  $ 8) +ᵢ
           $
           Z.of_nat
             (v'20 * typelen Slot))
          +ᵢ  $ 4) +ᵢ  
         $ 4} @ long
   |-> Vint32 i5 **
   PV b
      ↝ {(((i1 +ᵢ  $ 8) +ᵢ
           $
           Z.of_nat
             (v'20 * typelen Slot))
          +ᵢ  $ 4) +ᵢ  
         $ 8} @ long
   |-> Vint32 i6 **
   PV b
      ↝ {(((i1 +ᵢ  $ 8) +ᵢ
           $
           Z.of_nat
             (v'20 * typelen Slot))
          +ᵢ  $ 4) +ᵢ  
         $ 12} @ (Void) ∗ |-> v0 **
   [|isptr v0|]) **
  ASlots
    (b
     ↝ {(i1 +ᵢ  $ 8) +ᵢ
        $
        Z.of_nat
          (S v'20 * typelen Slot)})
    (Z.to_nat SLOT_NUM - S v'20)
    v'23 **
  LV endPtr @ long |-> Vint32 x **
  LV pCSpace @ CSPACE ∗
  |-> Vptr (b ↝ {i1}) **
  LV func_object @ (Void) ∗
  |-> v'3 ** H16==> Rv ((((((pCSpace ′ → cnode) .. slots)
       [ios_cap_defs.i ′]) .. capability)
     .. cap_content) .. object) .. object_t ==ₑ
   func_object ′ @ long== val_inj
   (bop_eval v0 v'3 (Void) ∗ (Void) ∗ oeq)).
   {
    intros.
    eapply bop_rv.
    {
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
                eapply expr_field_array_asrt_impl_frm.
                5:{
                  eapply local_val_struct_member_addr_frm.
                  4:{
                    instantiate(2:=v'20).
                    instantiate(2:=Tint32).
                    instantiate(2:=i1).
                    instantiate(2:=b).
                    instantiate(2:=CSPACE).
                    sep lifts (11::1::nil)%nat in H22.
                    sep cancel 1%nat 1%nat. 
                    eapply LV_to_Rv in H22; eauto.
                  }
                  unfold CSPACE. eauto.
                  unfold field_offset. simpl. eauto.
                  simpl. unfold Cte. eauto.
                }
                unfold field_offset. simpl. rewrite Int.add_zero.
                eauto.
                instantiate(1:=2%nat). simpl. auto.
                auto. simpl. unfold Slot. eauto.
              }
              simpl. unfold Cap. eauto.
              unfold field_offset. simpl. rewrite Int.add_zero. eauto.
            }
            simpl. unfold Content. eauto.
            unfold field_offset. simpl. rewrite Int.add_zero. eauto.
          }
          simpl. unfold Cap_Object. eauto.
        }
        simpl. eauto.
        unfold field_offset. simpl. rewrite Int.add_zero.
        eauto.
      }
      2:{
        rewrite Int.add_zero.
        rewrite Int.add_zero.
        change (($ 4 +ᵢ  $ 4)) with ($8).
        simpl typelen.
        simpl typelen in H22.
        rewrite <- addition_trans.
        2: simpl; lia. 
        rewrite Int.add_assoc.
        change (($ 4 +ᵢ  $ 8)) with ($12).
        assert(Z.of_nat
        (Z.to_nat
           (Int.unsigned ($ Z.of_nat v'20)) *
         20) = Z.of_nat (v'20 * 20)). 
         rewrite Nat2Z.inj_mul.
         rewrite of_to_nat_unsignedv'. 
         rewrite Int.unsigned_repr.  
         rewrite Nat2Z.inj_mul. auto.
         assert(v'20 < 255)%nat by lia. 
         rewrite max_unsigned_val. lia. 
         rewrite H23.
         sep normal in H22.
         sep lift 7%nat in H22.
         clear H23. unfold Aptrmapsto in H22 at 1.
         exact H22.
      }
      simpl. auto.
      sep split in H22.
      clear -H23.
      unfold isptr in H23.
      destruct H23. subst v0. auto.
      destruct H. subst v0. auto.
      
    }
    {
      sep lift 12%nat in H22.
      instantiate(1:=v'3).
      instantiate(1:=(Void) ∗).
      sep get rv.
      clear -Hptr.
      unfold isptr in Hptr.
      destruct Hptr.
      subst v'3. auto.
      destruct H. subst v'3. auto.
    }
    eauto.
    unfold val_inj. unfold bop_eval.
    unfold val_eq.
    sep split in H22.
    clear -Hptr H23. 
    unfold isptr in *.
    destruct Hptr; destruct H23.
    subst v'3. subst v0. auto.
    destruct H0.
    subst v'3 v0.
    destruct x. auto.
    destruct H. subst v'3 v0.
    destruct x. auto.
    destruct H, H0.
    subst v'3 v0.
    destruct x0, x.
    destruct (peq b b0);
    destruct(Int.eq i i0);
    auto.
    simpl. auto.
   }
   subst l0.

    (*If (((((((pCSpace ′ → cnode) .. slots) [ios_cap_defs.i ′])
       .. capability) .. cap_content) .. object)*)
    eapply seq_rule.
    eapply ift_rule_general.
    intros. 
    eexists.
    eapply Hgetp.
    sep pauto.
    sep pauto.
 
    remember (val_inj(bop_eval (v0) (v'3) 
       (Void) ∗ (Void) ∗ oeq)) as X.
    eapply backward_rule1 with (p:= (LV ios_cap_defs.i @ long
    |-> (V$ Z.of_nat v'20) **
    ASlots (b ↝ {i1 +ᵢ  $ 8}) v'20
      (v'21 ++ v'22) **
    PV b
       ↝ {(i1 +ᵢ  $ 8) +ᵢ
          $ Z.of_nat (v'20 * typelen Slot)} @
    long |-> Vint32 v'24 **
    (PV b
        ↝ {((i1 +ᵢ  $ 8) +ᵢ
            $ Z.of_nat (v'20 * typelen Slot))
           +ᵢ  $ 4} @ long |-> 
     Vint32 i4 **
     PV b
        ↝ {(((i1 +ᵢ  $ 8) +ᵢ
             $ Z.of_nat (v'20 * typelen Slot))
            +ᵢ  $ 4) +ᵢ  $ 4} @ long
     |-> Vint32 i5 **
     PV b
        ↝ {(((i1 +ᵢ  $ 8) +ᵢ
             $ Z.of_nat (v'20 * typelen Slot))
            +ᵢ  $ 4) +ᵢ  $ 8} @ long
     |-> Vint32 i6 **
     PV b
        ↝ {(((i1 +ᵢ  $ 8) +ᵢ
             $ Z.of_nat (v'20 * typelen Slot))
            +ᵢ  $ 4) +ᵢ  $ 12} @ 
     (Void) ∗ |-> v0 ** [|isptr v0|]) **
    ASlots
      (b
       ↝ {(i1 +ᵢ  $ 8) +ᵢ
          $ Z.of_nat (S v'20 * typelen Slot)})
      (Z.to_nat SLOT_NUM - S v'20) v'23 **
    LV endPtr @ long |-> Vint32 x **
    LV pCSpace @ CSPACE ∗ |-> Vptr (b ↝ {i1}) **
    LV func_object @ (Void) ∗ |-> v'3 ** H16) **
  [|X <> Vint32 Int.zero /\ X <> Vnull /\ X <> Vundef|]).
  lets Htrue2:  sep_aconj_r_aistrue_to_astar Hgetp.
  intros. eapply Htrue2. 
  clear Hgetp Htrue2.
  destruct H17.
  eapply aconj_intro.
  sep normal.  sep normal in H17.
  clear -H17.
  sep auto.
  sep pauto.

  instantiate(1:=Afalse).
  clear Hgetp.
  hoare unfold.
  rename H17 into Hptrv0.
  hoare forward; eauto.
  sep lifts (3::4::5::6::nil)%nat in H16.
  eapply fold_Cap in H16.
  sep lifts (2::3::1::4::nil)%nat in H16.
  eapply ASlots_fold_any_idx_frm in H16; eauto.
  sep lifts (6::7::1::nil)%nat in H16.
  eapply fold_Acnode in H16. 
  sep lifts (1::6::7::8::9::nil)%nat in H16.
  eapply fold_ACSpace  in H16; eauto. 
  2: auto. 
  sep lifts (5::1::6::nil)%nat in H16.
  eapply ACSpaceAarray_fold_any_idx_frm in H16; eauto.
  2: lia. 
  2: lia. 

  sep lift 2%nat in H16.
  eapply fold_AOSCSpacePrioTbl in H16; eauto.
  {
    
    sep lift 4%nat. 
    apply disj_split.
    left. 
    sep normal. sep eexists.
    sep lift 2%nat. 
    eapply disj_split. right.
    sep normal. sep eexists.
    sep lift 2%nat. eapply disj_split.
    left.
    unfold AOSCSpacePrioTbl in H16.
    sep auto.
    eauto.
    auto.
    5:{
      unfold get_slots.
      rewrite nth_cspace_length_imp.
      2: auto.
      
      rewrite H18.

      rewrite <- list_prop1.
      lets Hsplit: firstn_skipn (Z.to_nat(Int.unsigned x) - S(length(v'21++v'22)))%nat v'23.
      rewrite <- Hsplit.
      rewrite app_assoc_reverse.
      rewrite list_5_assoc.
      
      instantiate(3:=v'21).
      instantiate(1:=skipn (Z.to_nat (Int.unsigned x) -
      S(length (v'21 ++ v'22))) v'23).
      rewrite Hsplit.
      eauto.
    }
    instantiate (1:= Z.of_nat(length(v'21++v'22)) - OBJ_POSITION).
    rewrite Z.sub_simpl_r. auto.
    split; eauto.
    
    split. 
    rewrite app_length.
    rewrite H19. 
    lia.
    clear -Hxlt255 H20.
    lia.
    3: auto.
    2:{
      rewrite app_length.
      rewrite app_length.
      rewrite app_length.
      rewrite firstn_length.
      assert(Init.Nat.min
      (Z.to_nat (Int.unsigned x) - S(length (v'21 ++ v'22)))
      (length v'23) = (Z.to_nat (Int.unsigned x) - S(length (v'21 ++ v'22)))%nat).
      
      eapply Min.min_l.
      rewrite H26. lia. 
      rewrite H27. simpl.
      rewrite S_add_sub_S; eauto.
      rewrite app_length.
      rewrite Nat.add_assoc.
      rewrite le_plus_minus_r; eauto. 
      clear -H20.
      rewrite <- app_length. lia. 
    }
    unfold Slots_eq_object.
    simpl. 
    exists v'24. exists i4. do 4 eexists.
    intros.
    
    splits.
    rewrite app_length. 
    rewrite app_length. simpl.
    rewrite firstn_length.
    assert(Init.Nat.min
    (Z.to_nat (Int.unsigned x) -
     S (length v'21 + length v'22))
    (length v'23) = (Z.to_nat (Int.unsigned x) -
    S (length v'21 + length v'22))%nat).
    clear -H26 Hxlt255.
    rewrite H26. rewrite app_length.
    remember (S (length v'21 + length v'22)) as X.
    lia.
    rewrite H27.
    rewrite S_add_sub_S; auto.
    assert(Z.of_nat (length v'21 + length v'22) -
    OBJ_POSITION = Z.of_nat(length v'22)).
    clear -H19 H20 Hxlt255.
    rewrite Nat2Z.inj_add.  rewrite H19. 
    rewrite Z2Nat.id. lia. unfold OBJ_POSITION. lia.
    rewrite H30.
    assert(length v'22 +
    (Z.to_nat (Int.unsigned x) -
     (length v'21 + length v'22)) =
     Z.to_nat(Int.unsigned x) - length v'21)%nat. 
    clear -H19 H20 Hxlt255.
    rewrite NPeano.Nat.sub_add_distr.
    rewrite le_plus_minus_r. auto.
    rewrite app_length in H20. lia.
    rewrite H32. 
    clear -H19 H20 Hxlt255.
    rewrite app_length in H20. lia.
    clear -H19 H20 Hxlt255.
    rewrite app_length in H20. lia.
    assert(Z.to_nat (Z.of_nat (length (v'21 ++ v'22)) - OBJ_POSITION) = length(v'22)).
    {
      rewrite app_length.
      rewrite Nat2Z.inj_add.
      rewrite H19. 
      assert(Z.of_nat (Z.to_nat OBJ_POSITION) = OBJ_POSITION) by auto with arith.
      rewrite H27. 
      rewrite Z.add_simpl_l.
      rewrite Nat2Z.id. auto.
    }
    rewrite H27.
    rewrite nth_slots_length_imp; eauto.
    eauto.
    clear -H22 H23 H24 Hptrv0.
    unfold isptr in Hptrv0.
    destruct Hptrv0. subst v0.
    unfold val_inj, bop_eval, val_eq in H22, H23, H24.
    destruct v'3; tryfalse. auto.
    destruct a; tryfalse.
    simpljoin.
    unfold val_inj, bop_eval, val_eq in H22, H23, H24.
    destruct x.
    destruct v'3; tryfalse. auto.
    destruct a. 
    lets Hx: peq b b0.
    lets Hy: Int.eq_dec i i0.
    destruct Hx;destruct Hy; substs.
    auto.
    rewrite peq_true in H22. rewrite Int.eq_false in H22. tryfalse.
    auto.
    rewrite peq_false in H22; auto. tryfalse.
    rewrite peq_false in H22; auto. tryfalse.
  }

  eapply nth_val_length_imp; eauto.
  lia.
  assert((length (v'21 ++ v'22)) < Z.to_nat (Int.unsigned x))%nat by lia. 
  unfold SLOT_NUM. lia. 
  auto.
  hoare_split_pure_all.
  remember (val_inj(bop_eval (v0) (v'3) 
       (Void) ∗ (Void) ∗ oeq)) as X.
    eapply backward_rule1 with (p:= (
      LV ios_cap_defs.i @ long
  |-> (V$ Z.of_nat v'20) **
  ASlots (b ↝ {i1 +ᵢ  $ 8}) v'20
    (v'21 ++ v'22) **
  PV b
     ↝ {(i1 +ᵢ  $ 8) +ᵢ
        $ Z.of_nat (v'20 * typelen Slot)} @
  long |-> Vint32 v'24 **
  (PV b
      ↝ {((i1 +ᵢ  $ 8) +ᵢ
          $ Z.of_nat (v'20 * typelen Slot))
         +ᵢ  $ 4} @ long |-> 
   Vint32 i4 **
   PV b
      ↝ {(((i1 +ᵢ  $ 8) +ᵢ
           $ Z.of_nat (v'20 * typelen Slot))
          +ᵢ  $ 4) +ᵢ  $ 4} @ long
   |-> Vint32 i5 **
   PV b
      ↝ {(((i1 +ᵢ  $ 8) +ᵢ
           $ Z.of_nat (v'20 * typelen Slot))
          +ᵢ  $ 4) +ᵢ  $ 8} @ long
   |-> Vint32 i6 **
   PV b
      ↝ {(((i1 +ᵢ  $ 8) +ᵢ
           $ Z.of_nat (v'20 * typelen Slot))
          +ᵢ  $ 4) +ᵢ  $ 12} @ 
   (Void) ∗ |-> v0 ** [|isptr v0|]) **
  ASlots
    (b
     ↝ {(i1 +ᵢ  $ 8) +ᵢ
        $ Z.of_nat (S v'20 * typelen Slot)})
    (Z.to_nat SLOT_NUM - S v'20) v'23 **
  LV endPtr @ long |-> Vint32 x **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b ↝ {i1}) **
  LV func_object @ (Void) ∗ |-> v'3 ** H16 ) **
  [|X = Vint32 Int.zero \/ X = Vnull|]).
  intros.
  destruct H17.  tryfalse.
  lets Hf:  sep_aconj_r_aisfalse_to_astar Hgetp.
  intros. eapply Hf. clear Hgetp Hf.
  destruct H17.
  eapply aconj_intro.
  sep normal in H17.
  sep normal.
  clear -H17.
  sep auto.
  sep pauto.

  clear Hgetp.
  (*++ ios_cap_defs.i ′*)
  hoare_split_pure_all.
  rename H17 into Hptrv0.
  subst H16.
  assert (Hsuc: ($ Z.of_nat v'20 +ᵢ  $ 1) = ($ (Z.of_nat (S v'20)))).
  {
    clear -H20 Hxlt255.
    int auto.
  }
  assert (Hcond: Z.of_nat (S v'20) = (Int.unsigned x) \/ Z.of_nat (S v'20) < (Int.unsigned x)).
  clear -H20  Hxlt255.
  int auto.
  destruct Hcond as [Hc1 | Hc2].
  
  (*1 case *)
  hoare forward.
  rewrite Hsuc in H16.
  rewrite Hc1 in H16.
  eapply adisj_intro.
  right.
  
  sep lifts (5::6::7::8::nil)%nat in H16.
  eapply fold_Cap in H16. 

  sep lifts (4::5::1::6::nil)%nat in H16.
  eapply ASlots_fold_any_idx_frm with
  (slotsvl := (v'21 ++ v'22) ++ (v'24, (i4, ((i5, i6), v0))) :: v'23)
  in H16; eauto.
  assert(((v'21 ++ v'22) ++ (v'24, (i4, ((i5, i6), v0))) :: v'23) =
  (v'21++(v'22++ ((v'24, (i4, ((i5, i6), v0))) :: nil)) ++ v'23)).
  rewrite <- list_prop1.
  remember (((v'24, (i4, ((i5, i6), v0))) :: nil)) as Y.
   rewrite <- app_assoc.
  assert(v'22 ++ Y ++ v'23 = (v'22++Y)++v'23).
  rewrite app_assoc. auto.
  eapply app_inv_head_iff with(l:=v'21) in H24. auto.
  rewrite H24 in H16.
  clear H24.
  sep normal. sep eexists.
  sep cancel ASlots.
  sep pauto. 
  rewrite Int.repr_unsigned. auto.
  2:{
    splits; eauto.
    rewrite app_length. 
    rewrite app_length.
    simpl. 
    rewrite Nat.add_1_r.
    rewrite <- Hc1.
    rewrite app_length. lia.
    rewrite H18 in H6.
    clear -H6.
    rewrite app_length in *.
    rewrite app_length in *.
    rewrite app_length in *.
    simpl. simpl in H6.  lia.
  }
  2:{
    clear -H18.
    rewrite H18.
    rewrite app_assoc_reverse.
    rewrite app_assoc_reverse.
    rewrite list_prop1.
    auto.
  }
  2:{
    clear -H20 Hxlt255.
    unfold SLOT_NUM.
    lia.
  } 
 
  rewrite <- Slots_neq_object_split.
  split; auto.
  unfold Slots_neq_object.
  simpl. intros.
  assert(idx = 0). 
  destruct H19. lia. rewrite H28 in H24. 
  simpl in H24. inverts H24. 
  inverts H30.

  clear -H22 Hptr.
  pure_auto.
  rewrite H in H22.
  unfold bop_eval in H22. 
  unfold val_eq in H22. 
  unfold isptr in Hptr. destruct Hptr. subst v'3.
  destruct H22. tryfalse. tryfalse.
  destruct H0. subst v'3.
  destruct x.
  rewrite peq_true in H22.
  rewrite Int.eq_true in H22. destruct H22; tryfalse.


  rewrite H18 in H6. auto.
  auto.

  (*2 case*)
  destruct v'23.
  {
    false.
    destruct H19. destruct H17.
    clear -Hc2 H19 Hxlt255.
    assert(255 = S v'20)%nat. 
    simpl length in H19. lia. 
    rewrite <- H in Hc2.
    lia. 
  }

  hoare forward.
  rewrite Hsuc in H16.
  eapply adisj_intro.
  left.
  sep lifts (5::6::7::8::nil)%nat in H16.
  eapply fold_Cap in H16.
  sep lifts (4::5::1::6::nil)%nat in H16.
  eapply ASlots_fold_any_idx_frm with 
  (slotsvl := (v'21 ++ v'22) ++ (v'24, (i4, ((i5, i6), v0))) :: (p ::v'23)) in H16; eauto.
  remember (v'24, (i4, ((i5, i6), v0))) as Y.
  assert (Hvl: (v'21 ++ v'22) ++ Y :: p :: v'23 = (v'21 ++ (v'22 ++ (Y :: nil))) ++ (p :: v'23)).
  {
    rewrite app_assoc_reverse.
    rewrite app_assoc.
    rewrite app_assoc.
    remember(v'21++v'22) as T.
    remember (p::v'23) as TA.
    rewrite app_assoc_reverse.
    rewrite list_prop1. subst T. subst TA.
    auto.
  }
  rewrite Hvl in H16.
  assert(Z.to_nat(SLOT_NUM) = length(((v'21 ++ v'22) ++ Y :: nil)) + length(p::v'23))%nat. 
  {
    rewrite app_length.
    rewrite H19, H23. simpl length.
    rewrite Nat.add_1_r. unfold SLOT_NUM.
    lia.
  }
  rewrite H24 in H16. clear H24 Hvl. 
  eapply ASlots_split_strong_frm in H16.
  sep lift 2%nat in H16.
  simpl length in H16. 
  eapply ASlots_succ_imp_alt in H16. 
  simpl ASlots in H16 at 1.
  destruct p. 
  unfold ACap in H16.
  destruct p. destruct c. destruct p.
  sep normal in H16.
  sep normal. sep eexists.
  sep cancel 10%nat 1%nat. 
  sep lift 8%nat in H16. 
  assert(length ((v'21 ++ v'22) ++ Y :: nil) = S v'20).
  {
    rewrite app_length. simpl. 
    rewrite H19.
    rewrite Nat.add_1_r. auto.
  }
  rewrite H24 in H16.
  clear H24. sep cancel 1%nat 1%nat. 
  sep cancel 1%nat 1%nat. 
  
  sep semiauto; eauto.
  sep normal. 
  instantiate(2:=(i8, ((i9, i10), v1))).
  sep normal.
  sep cancel 1%nat 1%nat. 
  sep cancel 1%nat 1%nat. 
  sep cancel 1%nat 1%nat. 
  sep cancel 1%nat 1%nat. 
  assert(Z.to_nat SLOT_NUM - S (S (length (v'21 ++ v'22))) = length v'23)%nat. 
  rewrite H18 in H6.
  clear -H6.
  rewrite app_length in H6.
  simpl length in H6. lia. 
  rewrite H25. sep auto.
  remember (S (length (v'21 ++ v'22))) as IDX.
  assert (Hsimp: $ Z.of_nat (IDX * typelen (Slot)) +ᵢ  $ Z.of_nat (typelen (Slot)) =
                   $ Z.of_nat (S IDX * typelen (Slot))).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen (Slot))%nat with (typelen (Slot)).
    simpl. 
    assert (Ha: Z.of_nat (IDX * 20) = Int.unsigned ($ (Z.of_nat (IDX * 20)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      apply lt_imply_le.
      clear -Hc2 Hxlt255.
      rewrite max_unsigned_val. 
      apply Z.lt_le_trans with (m:=255 * 20).
      mauto. mauto.
    }
    assert (Hb: 20 = Int.unsigned ($20)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  rewrite <- Hsimp. sep auto.
 
  instantiate(1:=v'23).
  rewrite <- Int.add_assoc.
  sep pauto.
  2:{
    clear -Hc2 Hxlt255.
    lia.
  }
  2:{
    splits; eauto.
    rewrite app_length. rewrite app_length.
    simpl. rewrite app_length. lia.
    rewrite H18 in H6. 
    clear -H6.
    rewrite app_length in H6. simpl length in H6.
    unfold SLOT_NUM in H6. lia. 
  }
  2:{
    rewrite app_assoc_reverse.
    rewrite app_assoc.
    rewrite app_assoc.
    rewrite app_assoc_reverse.
    rewrite app_assoc_reverse.
    rewrite list_prop1. 
    rewrite app_assoc. auto.
  }
  2:{
    clear -H20 Hxlt255 H19.
    rewrite app_length. rewrite H19.
    rewrite max_unsigned_val.
    simpl length.
    apply lt_imply_le.
    apply Z.lt_le_trans with (m:=300 * 20).
    simpl typelen. lia. lia.
  }
  2:{
    splits; eauto.
    rewrite app_length.
    rewrite app_length.
    simpl length.
    rewrite app_length.
    rewrite app_length. simpl length. lia. 
  }
  2:{
    clear -H20 Hxlt255.
    unfold SLOT_NUM. lia. 
  }
  rewrite <- Slots_neq_object_split.
  splits; auto.
  unfold Slots_neq_object.
  intros.
  assert(idx=0). simpl length in H19.
  lia. subst idx. simpl in H25. inverts H25.
  inverts H27. pure_auto.
  rewrite H25 in H22.
  unfold bop_eval in H22. 
  unfold val_eq in H22.
  clear -Hptr H22.
  unfold isptr in Hptr. destruct Hptr. subst v'3.
  destruct H22; tryfalse.
  destruct H. subst v'3.
  destruct x.
  rewrite Int.eq_true in H22. 
  rewrite peq_true in H22. 
  destruct H22; tryfalse.
  rewrite H18 in H6. auto.
  auto.


  (*start of while Aisfalse*)
 
  eapply backward_rule1 with(p:=(EX vll11 vll12 vll2  index,
  LV ios_cap_defs.i @ long |-> Vint32 (Int.repr (Z.of_nat index)) **
  LV endPtr @ long |-> Vint32 x **
  LV pCSpace @ CSPACE ∗ |-> Vptr (b ↝ {i1}) **
  LV func_object @ (Void) ∗ |-> v'3 **
  ASlots (b ↝ {i1 +ᵢ  $ 8}) (Z.to_nat SLOT_NUM)
    (vll11 ++ vll12 ++ vll2) **
  [|l0 = vll11++vll12 ++ vll2|] **
  [|length vll11 = Z.to_nat OBJ_POSITION /\
    length (vll11 ++ vll12) = Z.to_nat (Int.unsigned x)
    /\ length (vll11++vll12++vll2) = Z.to_nat SLOT_NUM|] **
  [|Slots_neq_object vll12 v'3|]) ** H16).

  intros.
  destruct H18.
  destruct H18.
  1:{
    false.
    sep normal in H18.
    sep destruct H18.
    sep split in H18.
    sep lifts (1::6::nil)%nat in H18.
    destruct_s s.
    destruct H18. simpljoin.
    simpl in H24, H26, H27. simpljoin1.
    destruct H28. simpljoin.
    simpl in H17, H25, H26. simpljoin1.
    rewrite Int.unsigned_zero in H29, H33.
    simpl in H19.
    destruct H19. rewrite H27, H32 in H16.
    unfold cmp_int_type in H16.
    apply mapstoval_load in H29, H33.
    lets Hloadx16: load_local H24 H29.
    lets Hloadx18': load_local H17 H33.
    apply map_join_comm in H24.
    lets Hloadx18: load_local H24 Hloadx18'.
    rewrite Hloadx16, Hloadx18 in H16.
    clear -H16 H22 Hxlt255.
    unfold cmp_val in H16. unfold cmpu in H16.
    destruct(Int.ltu ($Z.of_nat(length(x1++x2))) x) eqn: Heqn.
    destruct H16. inverts H. 
    simpl in H0.  change(Int.eq Int.one Int.zero) with(false) in H0.
    simpl in H0. tryfalse.

    apply Intlt_false_is_Zge in Heqn.
    rewrite Int.unsigned_repr in Heqn.
    2:{
      rewrite max_unsigned_val.
      lia.
    }
    lia.
    simpl. auto. simpl. auto.
  }
  clear H19.
  sep normal in H18. sep destruct H18.
  sep normal. sep eexists.
  sep cancel H16.
  instantiate (1:=x1).
  sep cancel ASlots.
  sep cancel endPtr.
  sep cancel pCSpace.
  sep cancel func_object.
  instantiate(1:=(Z.to_nat(Int.unsigned x))).
  rewrite of_to_nat_unsignedv'.
  rewrite Int.repr_unsigned. sep auto.

  eapply rete_rule'.
  intros.
  destruct_s s. simpl.
  splits; eauto.
  sep auto.
  
  sep lifts (7::8::1::nil)%nat in H18.
  eapply fold_Acnode in H18.
  sep lifts (1::7::8::9::10::nil)%nat in H18.
  eapply fold_ACSpace in H18; eauto.
  sep lifts (6::1::7::nil)%nat in H18.
  2:{
    destruct H20. destruct H17. auto.
  }
  2: auto.
  eapply ACSpaceAarray_fold_any_idx_frm with (n:=64%nat)
  (vll1:=v'14)(vll2:=v'16) in H18; eauto.
  sep lifts (3::1::4::5::nil)%nat in H18.
  sep split in H18.
  eapply fold_AOSCSpacePrioTbl in H18.
  {
    sep lift 4%nat. 
    apply disj_split.
    left. 
    sep normal. sep eexists.
    sep lift 2%nat. 
    eapply disj_split. right.
    sep normal. sep eexists.
    sep lift 2%nat. 
    eapply disj_split. right. 
    unfold AOSCSpacePrioTbl in H18.
    sep auto.
    eauto.  
    
    2:{
      destruct H20. destruct a. 
      instantiate(1:=x1).  instantiate(1:=x0). auto.
    }
    auto. destruct H20. auto.
    unfold get_slots.
    rewrite nth_cspace_length_imp.
    rewrite H19.
    eauto. auto.
  }
  rewrite app_length. simpl length.
  rewrite H8, H11. lia.
  rewrite app_length. simpl. rewrite H9, H10. lia.
  auto.
  apply nth_val_length_imp; eauto.
  lia. lia. lia. 
  rewrite H19. auto.
  (*OBJ_POSITION >= Int.unsigned x*)

  eapply seq_rule.
  eapply while_rule with(tp:=Int32u).
  intros.
  symbolic_execution.
  destruct (Int.ltu ($ OBJ_POSITION) x); eauto.

  eapply backward_rule1.
  intros.
  instantiate(1:=Afalse).
  simpl.
  destruct H16.
  sep lifts (2::21::nil)%nat in H16.
  change (OBJ_POSITION) with (Z.of_nat(Z.to_nat OBJ_POSITION)) in H16.
  lets Hok: Ais_true_x_y H16 H17.
  simpl. lia.
  clear -Hiendge Hok.
  
  lia.
  apply pfalse_rule.

  eapply rete_rule'.
  intros.
  destruct_s s. simpl.
  splits; eauto.
  intros.
  destruct H16.
  sep normal in H16. sep destruct H16.
  sep normal. sep eexists.

  
  clear H17.
  sep cancel endPtr.
  sep cancel pCSpace.
  sep cancel func_object.
  sep cancel OSCSpaceObjectPointer.
  sep cancel p_local.
  sep cancel ios_cap_defs.i.
  sep cancel prio.
  sep cancel Aie. 
  sep cancel Ais. 
  sep cancel Aisr.
  sep cancel Acs.
  sep cancel Aier.
  sep cancel Aop.
  sep semiauto; eauto.
  
  sep lifts (6::7::1::nil)%nat in H16.
  eapply fold_Acnode in H16.
  sep lifts (1::6::7::8::9::nil)%nat in H16.
  eapply fold_ACSpace in H16; eauto.
  sep lifts (5::1::6::nil)%nat in H16.
  eapply ACSpaceAarray_fold_any_idx_frm with (n:=64%nat)
  (vll1:=v'14)(vll2:=v'16) in H16; eauto.
  sep lifts (2::1::3::4::nil)%nat in H16.
  sep split in H16.
  eapply fold_AOSCSpacePrioTbl in H16.
  sep auto.

  {
    sep lift 4%nat. 
    apply disj_split.
    left. 
    sep normal. sep eexists.
    sep lift 2%nat. 
    eapply disj_split. right.
    sep normal. sep eexists.
    sep lift 2%nat. 
    eapply disj_split. right.
    assert(Int.unsigned x = OBJ_POSITION).
    assert(Int.unsigned x >= OBJ_POSITION).
    clear -Hv'2lt63 Hnth_val'ofv'10 Hpointervl H5.
    unfolds in Hpointervl.
    assert(Hrange: (0 <= (Z.to_nat(Int.unsigned v'2)) < length v'10)%nat).
    rewrite H5. lia.
    Require Import inline_bittblfunctions.
    eapply nth_val'2nth_val in Hnth_val'ofv'10.
    lets Hx: Hpointervl Hrange  Hnth_val'ofv'10.
    destruct Hx.
    eapply inj_ge in H.
    rewrite Z2Nat.id in H. 
    rewrite Z2Nat.id in H.
    lia. unfold OBJ_POSITION. lia.
    int auto.
    lia.
    
    lets Hsplit: (firstn_skipn (Z.to_nat OBJ_POSITION) l0).
    unfold AOSCSpacePrioTbl in H16.
    sep auto.
    eauto.
    instantiate (1:=nil). 
    unfold Slots_neq_object. 
    intros. simpl in H20. lia.
    rewrite app_nil_r. eauto. 
    instantiate (1:=firstn
    (Z.to_nat OBJ_POSITION)l0).
    rewrite firstn_length. 
    rewrite H18. rewrite H6.
    unfold min. simpl. lia.
    rewrite firstn_length.
    rewrite H6. unfold min. simpl. lia.
    unfold get_slots. 
    rewrite nth_cspace_length_imp; eauto.
    rewrite <- Hsplit at 1.
    instantiate (1:=skipn (Z.to_nat OBJ_POSITION)
    l0).
    auto.
  }
  rewrite app_length. simpl length.
  rewrite H8, H11. lia.
  rewrite app_length. simpl. rewrite H9, H10. lia.
  auto.
  apply nth_val_length_imp; eauto.
  lia. lia. lia.
  auto.
  Unshelve.
  all: auto.
Qed.