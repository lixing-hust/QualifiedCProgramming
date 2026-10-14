Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import CapSpec.
Require Import Lia.
Require Import ACSpace_defs.
Require Import seplog_trm_tacs.
Require Import ucosCNodeCopyPure.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.

Lemma ucosCNodeCopyPart1_proof:
forall 
(logicl: list logicvar)
(ct: tid)
(v'5: int32)
(H2: Int.unsigned v'5 <= 255)
(v'4: int32)
(H3: Int.unsigned v'4 <= 255)
(v': val)
(v'0: val)
(v'1: val)
(v'2: val)
(v'3: val)
(v'6: int32)
(v'7: ier)
(v'8: absop)
(v'9: block)
(v'10: int32)
(v'11: cs)
(v'12: isr)
(v'13: vallist)
(v'14: list cspace_val_type)
(v'15: CSpaceptr2prioMod.map)
(v'16: list val)
(H5: CSPACEList_P v'13 0 v'15)
(H6: ptrvl_to_cspace_to_ptrvl v'13 v'15)
(H8: logicl =
     logic_cs v'11
     :: logic_isr v'12
        :: logic_ier v'7
           :: logic_cspacel v'14
              :: logic_lv v'16
                 :: logic_code v'8
                    :: logic_abscap v'15
                     ::  logic_lv v'13
                       :: nil)
(Hv'4range: Int.unsigned v'4 < 63)
(Hv'5range: Int.unsigned v'5 < 63)
(Hv'6range: Int.unsigned v'6 < SLOT_NUM)
(Hv'13len: length v'13 = 64%nat)
(Hv'14len: length v'14 = 64%nat)
(Htypematch: array_type_vallist_match
               (Tptr CSPACE) v'13)
(Hv'4: (Int.unsigned v'4 <=?
        Byte.max_unsigned) = true)
(Hv'5: (Int.unsigned v'5 <=?
        Byte.max_unsigned) = true)
(HpCSpace1type: rule_type_val_match
                  (Tptr CSPACE)
                  (nth_val'
                     (Z.to_nat
                        (Int.unsigned v'4))
                     v'13) = true)
(HpCSpace2type: rule_type_val_match
                  (Tptr CSPACE)
                  (nth_val'
                     (Z.to_nat
                        (Int.unsigned v'5))
                     v'13) = true)
(Hnotnull1: nth_val'
              (Z.to_nat (Int.unsigned v'4))
              v'13 <> Vnull)
(Hnotnull2: nth_val'
              (Z.to_nat (Int.unsigned v'5))
              v'13 <> Vnull)
(Hc1: Int.unsigned v'4 > Int.unsigned v'5)              ,
{|Cap_spec, GetHPrio, OSLInv, I,
fun v : option val =>
((EX v0 : val, LV func_capability @ long |-> v0) **
 (EX v0 : val, LV srcTask_Prio @ char_t |-> v0) **
 (EX v0 : val, LV destTask_Prio @ char_t |-> v0) **
 (EX v0 : val, LV idx @ long |-> v0) **
 (EX v0 : val, LV pCSpace1 @ CSPACE ∗ |-> v0) **
 (EX v0 : val, LV pCSpace2 @ CSPACE ∗ |-> v0) **
 (EX v0 : val, LV cap1 @ Cap ∗ |-> v0) **
 (EX v0 : val, LV cap2 @ Cap ∗ |-> v0) ** Aemp) **
(EX (destTask_Prio srcTask_Prio func_capability : int32) 
 (er : ier) (s : absop) (b : block) (i : int32) (cs : language.cs)
 (isr : language.isr) (ptrvl : list val)
 (priotbl priotbl' : list cspace_val_type) (cspacels : CSpaceptr2prioMod.map)
 (pointervl : vallist) (pointervl' : list val)
 (captype_val categorycontent_val categoryright_val : int32)
 (categoryobject_val : val) (origin_right : int32) 
 (origin_object : val),
 Aie false **
 Ais nil **
 Acs cs **
 Aisr isr **
 Aier er **
<|| s ||>  **
[|nth_val 0
(rev
    (Vint32 v'6
    :: Vint32 v'5 :: Vint32 v'4 :: nil)) =
Some (Vint32 destTask_Prio)|] **
[|nth_val 1
(rev
    (Vint32 v'6
    :: Vint32 v'5 :: Vint32 v'4 :: nil)) =
Some (Vint32 srcTask_Prio)|] **
[|nth_val 2
(rev
    (Vint32 v'6
    :: Vint32 v'5 :: Vint32 v'4 :: nil)) =
Some (Vint32 func_capability)|] **
AOSCSpaceObjectPointer pointervl' **
[|CSPACEList_P ptrvl 0 cspacels|] **
[|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
AOSCSpacePrioTbl (b ↝ {i}) ptrvl priotbl' cspacels **
[|logicl =
logic_cs cs
:: logic_isr isr
   :: logic_ier er
      :: logic_cspacel priotbl
         :: logic_lv pointervl
            :: logic_code s
               :: logic_abscap cspacels
                  :: logic_lv ptrvl
                  :: nil|] **
 p_local OSLInv ct init_lg **
 (
[|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull \/
nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl = Vnull|] ** [|v = Some(Vint32(Int.repr CNODE_COPY_FAILURE))/\priotbl' = priotbl /\ pointervl' = pointervl|] \\//
([|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull /\
nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl <> Vnull|] **
[|get_capability (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
priotbl = Some(captype_val, (categorycontent_val, categoryright_val, categoryobject_val))|] **
(
([|(Int.unsigned captype_val <> CAP_CATEGORY_TYPE) /\ (Int.unsigned captype_val <> CAP_OBJECT_TYPE)|]
** [|v = Some(Vint32 ($CNODE_COPY_FAILURE))|]
** [|priotbl' = priotbl /\ pointervl' = pointervl|]) \\//(
[|(Int.unsigned captype_val = CAP_CATEGORY_TYPE)|] **
[|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
($CAP_CATEGORY_TYPE , (categorycontent_val, categoryright_val, origin_object)))|] ** 
[|pointervl' = pointervl|] ** [|v = Some(Vint32 ($CNODE_NONE_FAULT))|]
) \\// ([|(Int.unsigned captype_val = CAP_OBJECT_TYPE)|] **
  (EX idxval idxz,
  GetObjSlotRetval destTask_Prio ptrvl pointervl priotbl categoryobject_val idxval **
  [|idxz = Int.unsigned(Vint32_inj (val_inj idxval))|] **(
   [|idxz = SLOT_NULL_CAP|] ** (
    EX pointeridx, 
    [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) pointervl = (Vint32 pointeridx)|] **
    (([|Int.unsigned pointeridx >= 255|] ** [|v = Some(Vint32 ($SLOT_RANGE_OVERFLOW)) /\ priotbl' = priotbl /\
    pointervl' = pointervl|])\\//
    ([|Int.unsigned pointeridx < 255|] **  [|v = Some(Vint32 ($CNODE_NONE_FAULT))|] **
    [|pointervl' = update_nth_val (Z.to_nat(Int.unsigned destTask_Prio)) pointervl (Vint32 (Int.add pointeridx (Int.repr 1)))|] **
    [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat (Int.unsigned pointeridx)) priotbl
    ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|])))
     \\//[|idxz <> SLOT_NULL_CAP|] **(
    [|v = Some(Vint32 ($CNODE_NONE_FAULT))|] **
    [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat idxz) priotbl
    ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|] **  [|pointervl' = pointervl|]
    ))
))
)
)) )**
A_dom_lenv
  ((func_capability ↝ {long})
   :: (srcTask_Prio ↝ {char_t})
      :: (destTask_Prio ↝ {char_t})
         :: (idx ↝ {long})
            :: (pCSpace1 ↝ {CSPACE ∗})
               :: (pCSpace2 ↝ {CSPACE ∗})
                  :: (cap1 ↝ {Cap ∗}) :: (cap2 ↝ {Cap ∗}) :: nil),
Afalse|}|- ct
{{ <|| v'8 ||>  **
LV pCSpace2 @ Tptr CSPACE
|-> nth_val'
      (Z.to_nat (Int.unsigned v'5))
      v'13 **
LV pCSpace1 @ Tptr CSPACE
|-> nth_val'
      (Z.to_nat (Int.unsigned v'4))
      v'13 **
LV cap2 @ Tptr Cap |-> Vnull **
LV cap1 @ Tptr Cap |-> Vnull **
Aie false **
Ais nil **
Acs v'11 **
Aisr v'12 **
Aier v'7 **
AOSCSpaceObjectPointer v'16 **
AOSCSpacePrioTbl (v'9, v'10) v'13 v'14
  v'15 **
p_local OSLInv ct init_lg **
LV idx @ Tint32 |-> v' **
LV func_capability @ Tint32
|-> Vint32 v'6 **
LV srcTask_Prio @ Tint8 |-> Vint32 v'5 **
LV destTask_Prio @ Tint8 |-> Vint32 v'4 **
A_dom_lenv
  ((func_capability, Tint32)
   :: (srcTask_Prio, Tint8)
      :: (destTask_Prio, Tint8)
         :: (idx, Tint32)
            :: (pCSpace1, Tptr CSPACE)
               :: (pCSpace2,
                  Tptr CSPACE)
                  :: (cap1, Tptr Cap)
                     :: (cap2,
                        Tptr Cap)
                        :: nil)}} 
    cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[func_capability′]..capability);ₛ
    cap2′ =ₑ &ₐ(pCSpace2′→cnode..slots[func_capability′]..capability);ₛ
    (*这里稍许做了些改动，框架没有实现if elseif else的操作,可以等价为两个if else{if else{}}*)
    IF(cap2′→cap_type==ₑ′CAP_CATEGORY_TYPE){
        cap1′→cap_type =ₑ ′CAP_CATEGORY_TYPE;ₛ
        cap1′→cap_content..category..category_content =ₑ cap2′→cap_content..category..category_content;ₛ
        cap1′→cap_content..category..category_right =ₑ cap2′→cap_content..category..category_right
    }ELSE{
        IF(cap2′→cap_type==ₑ′CAP_OBJECT_TYPE){
            idx′ =ᶠ Get_Obj_Slot(·destTask_Prio′ ,cap2′→cap_content..object..object_t·);ₛ
            If(idx′==ₑ′SLOT_NULL_CAP){
                idx′ =ₑ OSCSpaceObjectPointer′[destTask_Prio′];ₛ
                If(idx′≥′SLOT_NUM){
                    RETURN ′SLOT_RANGE_OVERFLOW
                };ₛ
          ++OSCSpaceObjectPointer′[destTask_Prio′]
            };ₛ
            cap1′ =ₑ &ₐ(pCSpace1′→cnode..slots[idx′]..capability);ₛ
            cap1′→cap_type =ₑ ′CAP_OBJECT_TYPE;ₛ
            cap1′→cap_content..object..object_right =ₑ cap2′→cap_content..object..object_right;ₛ
            cap1′→cap_content..object..object_t =ₑ cap2′→cap_content..object..object_t;ₛ
              
            RETURN 〈Int8u〉′CNODE_NONE_FAULT  (*在这里加上一个return,没有影响程序的正确性，证明起来的时候减少了中间生成变量的影响
            *)
        }ELSE{
            RETURN ′CNODE_COPY_FAILURE
        }
    };ₛ
    RETURN 〈Int8u〉′CNODE_NONE_FAULT {{Afalse}}.
Proof.
    intros.
    eapply backward_rule1.
    intros.
    sep lift 12%nat in H.
    eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with (idx1:=Z.to_nat(Int.unsigned v'4)) (idx2:=Z.to_nat(Int.unsigned v'5))in H; eauto.
    (*这个地方需要记录下来AOSCSpacePrioTbl的第destTask_prio元素和srcTask_Prio元素*)
    
    rewrite Hv'14len. lia.
    clear -Hc1. 
    eapply Z2Nat.inj_lt; try (int auto).
    pure intro.
    unfold ACSpace.
    destruct v'18. destruct p. destruct p. destruct p. destruct v'25.
    destruct v'19. destruct p. destruct p. destruct p. destruct v'26.

    unfold Acnode.
    destruct c. destruct p. destruct c0. destruct p.
    pure intro.
    rename H21 into Hi2range.
    rename H22 into Hirange'.
    rename H into Hl1len.
    rename H0 into Hirange.
    rename H8 into Hlv'15.
    rename H12 into Hltype.
    rename H13 into Hlnotnull.
    rename H14 into Hl2len.
    rename H15 into Hi1range.
    rename H16 into Hl0v'15.
    rename H17 into Hl0type.
    rename H18 into Hl0notnull.
    rename H19 into Hllen.
    rename H20 into Hl0len.
    assert(nth_val'
    (Z.to_nat (Int.unsigned v'5))
    (v'22 ++
     (Vptr (b ↝ {i1}) :: v'23) ++
     Vptr (b0 ↝ {i4}) :: v'24) = Vptr(b, i1)).
    simpl. 
    eapply nth_val'_length_imp; eauto.
    rewrite H.
    clear H.
    assert(nth_val'
    (Z.to_nat
       (Int.unsigned v'4))
    (v'22 ++
     (Vptr (b ↝ {i1}) :: v'23) ++
     Vptr (b0 ↝ {i4}) :: v'24) = Vptr(b0, i4)).
    rewrite list_trans_1. eapply nth_val'_length_imp; eauto.
    rewrite app_length. simpl. 
    rewrite H1, H10. rewrite S_add_sub_S.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; int auto.
    rewrite H. 
    clear H.
    (*unfold two slots*)
    eapply backward_rule1.
    intros.
    sep lifts (10::18::nil)%nat in H.
    eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'6)) in H.
    sep lift 2%nat in H.
    eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'6)) in H.
    exact H.
    clear -Hv'6range.
    eapply Z2Nat.inj_lt; int auto. 
    unfold SLOT_NUM. lia. auto. auto.
    clear -Hv'6range.
    eapply Z2Nat.inj_lt; int auto. 
    unfold SLOT_NUM. lia.
    auto. auto.
    pure intro.
    unfold ACap.
    destruct v'28. destruct c. destruct p.
    destruct v'19. destruct c. destruct p.
    pure intro.
    rename H into Hisptrv1.
    rename H12 into Hisptrv2.
    (*cap1 ′ =ₑ&ₐ(((pCSpace1 ′ → cnode) .. slots)[func_capability ′]) .. capability;ₛ*)
    eapply seq_rule.
    hoare_lifts_trms_pre (Aop).
    eapply assign_rule_lvar.
    intros. split; intros.
    sep cancel cap1.
    exact H.
    sep auto.

    intros.
    eapply calculate_rv_expr_id_addr.
    3:{
      eapply expr_field_array_asrt_impl_frm.
      5:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep cancel pCSpace1.
          sep_lifts_trms_in H (Alvarmapsto func_capability).
          eapply LV_to_Rv in H; eauto.
          instantiate(2:=Z.to_nat(Int.unsigned v'6)).
          rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
          exact H.
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
  exact H.
  sep auto.

  intros.
  eapply calculate_rv_expr_id_addr.
  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep cancel pCSpace2.
        sep_lifts_trms_in H (Alvarmapsto func_capability).
        eapply LV_to_Rv in H; eauto.
        instantiate(2:=Z.to_nat(Int.unsigned v'6)).
        rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
        exact H.
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

  (*IF (cap2 ′ → cap_type ==ₑ ′ CAP_CATEGORY_TYPE)*)

  eapply seq_rule.
  eapply if_rule2'.
  intros.
  eapply bop_rv.
  {
    simpl typelen in H.
    rewrite Int.add_zero in *.
    eapply lv_mapsto_to_rv.
    2:{
      eapply local_val_struct_member_addr.
      sep lift 2%nat in H.
      exact H. unfold Cap. eauto.
      unfold field_offset. simpl. unfold Int.zero. eauto.
      simpl. eauto.
    }
    2:{
      rewrite Int.add_zero in *.
      sep lift 6%nat in H.
      unfold Aptrmapsto in H at 1.
      rewrite of_to_nat_unsignedv'. rewrite <- addition_trans.
      rewrite Int.unsigned_repr. 
      exact H.
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

  pure intro.
  (*cap1 ′ → cap_type =ₑ ′ CAP_CATEGORY_TYPE*)
  eapply seq_rule.
  eapply assign_rule_aop.
  2:{
    intros.
    eapply local_val_struct_member_addr.
    {
      sep lift 2%nat in H18.
      exact H18.
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
      sep lift 12%nat in H18.
      exact H18.
      clear -H9. int auto.
      lia.
  Optimize Proof.
  Optimize Heap.
      intros. 
      rewrite Int.add_zero in *.
      rewrite Int.add_zero in *.
      simpl typelen in *.
      rewrite of_to_nat_unsignedv' in H18 at 1.
      rewrite <- addition_trans in H18 at 1. 
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
      rewrite Int.unsigned_repr in H18 at 1.
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
((cap2 ′ → cap_content) .. category) .. category_content;ₛ*)
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
          sep lift 3%nat in H18.
          exact H18.
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
    sep lift 13%nat in H18.
    rewrite <- addition_trans.
    exact H18. lia.
    simpl typelen in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    sep cancel cap2.
    sep cancel cap1.
    sep cancel ASlots.
    rewrite of_to_nat_unsignedv'.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite <- addition_trans in H18.
    rewrite Int.unsigned_repr in H18.
    rewrite of_to_nat_unsignedv' in H18.
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
            sep lift 2%nat in H18.
            exact H18.
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
      sep lift 7%nat in H18.
      unfold Aptrmapsto in H18 at 1.
      exact H18.
      clear -H9. int auto.
      lia.
    }
    simpl. auto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.

  (*((cap1 ′ → cap_content) .. category) .. category_right =ₑ
((cap2 ′ → cap_content) .. category) .. category_right*)
  eapply assign_rule_aop.
  2:{
    intros.
    eapply field_asrt_impl_struct_aop.
    3:{
      eapply field_asrt_impl_union_aop'.
      2:{
        eapply local_val_struct_member_addr_frm.
        4:{
          sep lift 4%nat in H18.
          exact H18.
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
    sep lift 14%nat in H18.
    exact H18. 
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
    rewrite <- addition_trans in H18.
    rewrite Int.unsigned_repr in H18.
    rewrite of_to_nat_unsignedv' in H18.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    sep cancel 2%nat 1%nat.
    rewrite Int.add_assoc in H18 at 1.
    change (($ 4 +ᵢ  $ 4)) with ($8) in H18.
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
            sep lift 3%nat in H18.
            exact H18.
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
      rewrite Int.add_assoc.
      change  (($ 4 +ᵢ  $ 4)) with ($8).
      sep lift 9%nat in H18.
      unfold Aptrmapsto in H18 at 1.
      exact H18.
      clear -H9. int auto.
      lia.
    }
    simpl. auto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.

  pure intro.

  (*IF (cap2 ′ → cap_type ==ₑ ′ CAP_OBJECT_TYPE)*)
  eapply if_rule2'.
  intros.

  intros.
  eapply bop_rv.
  {
    simpl typelen in H.
    rewrite Int.add_zero in *.
    eapply lv_mapsto_to_rv.
    2:{
      eapply local_val_struct_member_addr.
      sep lift 2%nat in H12.
      exact H12. unfold Cap. eauto.
      unfold field_offset. simpl. unfold Int.zero. eauto.
      simpl. eauto.
    }
    2:{
      rewrite Int.add_zero in *.
      sep lift 6%nat in H12.
      unfold Aptrmapsto in H12 at 1.
      rewrite of_to_nat_unsignedv'. rewrite <- addition_trans.
      rewrite Int.unsigned_repr. 
      exact H12.
      clear -H9.
      rewrite max_unsigned_val. int auto.
      simpl.
      lia.
    }
    simpl. auto.
  }

  destruct_s s. simpl. splits; eauto.
  eauto. unfold bop_eval. unfold val_inj. 
  unfold val_eq. destruct (Int.eq i9 ($ CAP_OBJECT_TYPE)); eauto.
  simpl. eauto.

  pure intro.
  instantiate(1:=Afalse).
  (*idx ′ =ᶠ Get_Obj_Slot (·destTask_Prio ′,
((cap2 ′ → cap_content) .. object) .. object_t·);ₛ*)
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec. simpl. 
  unfold Get_Obj_Slot_spec. eauto.

  intros.
  eapply rvl_elim.
  {
    sep_lifts_trms_in H19 (Alvarmapsto destTask_Prio).
    eapply LV_to_Rv in H19.
    eapply inline_tactics.monoasrt_mono in H19.
    exact H19.
    eapply inline_tactics.Rv_mono.
    auto.
    simpl. 
    rewrite Hv'4. auto.
  }
  eapply rvl_elim.
  eapply lv_mapsto_to_rv.
  2:{
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
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    rewrite of_to_nat_unsignedv'. 
    simpl typelen in *.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    rewrite Int.add_assoc.
    change  (($ 4 +ᵢ  $ 4)) with ($8).
    change ($ 4 +ᵢ  $ 8) with ($12).
    sep lift 9%nat in H19.
    unfold Aptrmapsto in H19 at 1.
    exact H19.
    clear -H9. int auto.
    lia.
  }
  simpl. auto.
  clear - Hisptrv1.
  unfold isptr in Hisptrv1. destruct Hisptrv1.
  subst v1. auto.
  destruct H. subst v1. auto.
  eapply rvl_nil.

  intros.
  unfold Get_Obj_SlotPre.
  unfold getasrt. unfold Get_Obj_SlotPre'.

  simpl typelen in *.
  sep lifts (6::7::8::9::nil)%nat in H19.
  eapply fold_Cap in H19.
  sep lifts (5::6::1::7::nil)%nat in H19.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'25++(v'27,(i9,((i10, i11), v1)))::v'26))
  in H19; eauto.
  sep lifts (7::8::9::10::nil)%nat in H19.
  eapply fold_Cap in H19.
  sep lifts (6::7::1::8::nil)%nat in H19.
  eapply ASlots_fold_any_idx_frm in H19; eauto.
  sep lifts (9::7::10::nil)%nat in H19.
  eapply Aarray'_fold_any_idx_frm in H19; eauto.
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    assert(Z.to_nat (Int.unsigned v'4) < 64)%nat. lia. 
    apply Z.le_trans with(m:= 64*4). simpl typelen.
    rewrite Nat2Z.inj_mul.
    lia. 
    rewrite max_unsigned_val. lia. 
  }
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  sep lifts (1::8::9::nil)%nat in H19.
  eapply Aarray'_fold_any_idx_frm in H19; eauto.
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
  sep lifts (9::10::3::nil)%nat in H19.
  eapply fold_Acnode in H19; eauto.
  sep lifts (14::15::3::nil)%nat in H19.
  eapply fold_Acnode in H19; eauto.

  sep lifts (2::9::10::11::12::nil)%nat in H19.
  eapply fold_ACSpace in H19; eauto.
  sep lifts (2::10::11::12::13::nil)%nat in H19.
  eapply fold_ACSpace in H19; eauto.
  sep lifts (8::2::9::nil)%nat in H19.

  eapply ACSpaceAarray_fold_any_idx_frm in H19; eauto.
  2: lia. 
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl. 
    rewrite H4, H7.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (1::2::8::nil)%nat in H19.
  eapply ACSpaceAarray_fold_any_idx_frm in H19; eauto.
  2: lia. 
  2: lia.
  2:{
    rewrite app_length.
    simpl. rewrite H4,H7.
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
    simpl. eauto.
  }
  unfold AOSCSpacePrioTbl. 
  
  sep normal. sep eexists.

  sep cancel ACSpaceAarrayTptr.
  sep cancel Aie. sep cancel Acs.
  sep cancel Aier. sep cancel Ais. sep cancel Aop.
  sep cancel Aisr. sep cancel OSCSpacePrioTbl.
  unfold Aarray.  sep cancel Aarray'.
  sep split.
  sep lifts (5::6::7::nil)%nat in H19.
  exact H19.
  3: simpl; eauto.
  3: simpl; eauto.
  auto.
  eauto.
  rewrite app_assoc_reverse. auto.
  rewrite app_assoc_reverse. auto.
  splits. rewrite app_length. simpl.
  rewrite app_length. simpl. 
  rewrite H1, H10, H11.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S.
  lia.   lia. 
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite app_length. simpl. rewrite app_length.
  simpl. 
  rewrite H4, H7, H9.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S_add.
  lia.  
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  lia.
  rewrite app_assoc_reverse.
  auto.
  clear -Hv'6range.
  eapply Z2Nat.inj_lt; try (int auto).
  unfold SLOT_NUM. lia.
  auto. 
  clear -Hv'6range.
  eapply Z2Nat.inj_lt; try (int auto).
  unfold SLOT_NUM. lia.
  auto.
  good_frm_sovler.
  eapply retpost_GetObjSlotPost.
  simpl.
 
  rewrite Hv'4. 
  clear -Hisptrv1. unfold isptr in Hisptrv1.
  destruct Hisptrv1. subst v1. auto.
  destruct H. subst v1. auto.
  intros. sep destruct H19. 
  unfold getasrt in H19. unfold Get_Obj_SlotPost in H19.
  unfold Get_Obj_SlotPost' in H19.
  
  sep normal in H19. sep destruct H19.
  eexists.
  sep cancel p_local. simpl. auto.
  intros. 
  unfold getasrt in H19. unfold Get_Obj_SlotPre in H19.
  unfold Get_Obj_SlotPre' in H19.
  sep normal in H19. sep destruct H19.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt. unfold Get_Obj_SlotPost.
  unfold Get_Obj_SlotPost'. pure intro.
  inverts H23.
  (*分了很多种情况，来获取idx具体的值*)
  eapply backward_rule1.
  intros.
  sep lift 10%nat in H19.
  eapply disj_split in H19.
  exact H19.
  eapply disj_rule.
  pure intro.
  eapply backward_rule1.
  intros.

  
  eapply disj_split in H20.
  exact H20.
  eapply disj_rule.
  pure intro.
  Require Import ucosCNodeCopyPart1_0Proof.
  eapply ucosCNodeCopyPart1_0proof; eauto.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H25.
  exact H25.
  eapply disj_rule.
  hoare_split_pure_all.
  Require Import ucosCNodeCopyPart1_1Proof.
  eapply ucosCNodeCopyPart1_1proof; eauto.
  hoare_split_pure_all.
  Close Scope code_scope.
  inverts H29.
  Require Import ucosCNodeCopyPart1_2Proof.
  eapply ucosCNodeCopyPart1_2proof with(v'17:= v'17); eauto.

  pure intro. 
  clear -Hv'4range H19.
  false.
  unfold OS_LOWEST_PRIO in *.
  lia.
  


  (*RETURN ′ CNODE_COPY_FAILURE*)
  pure intro.
  eapply rete_rule'.
  intros.
  destruct_s s. unfold CNODE_COPY_FAILURE.
  simpl. split; eauto.

  intros.
  rewrite Int.add_zero in H17.
  rewrite Int.add_zero in H17.
  simpl typelen in H17.
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Acs.
  sep cancel Aier. sep cancel Ais. sep cancel Aop.
  sep cancel Aisr.
  simpl typelen in *.
  sep lifts (5::6::7::8::nil)%nat in H17.
  eapply fold_Cap in H17.
  sep lifts (4::5::1::6::nil)%nat in H17.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'25++(v'27,(i9,((i10, i11), v1)))::v'26))
  in H17; eauto.
  sep lifts (6::7::8::9::nil)%nat in H17.
  eapply fold_Cap in H17.
  sep lifts (5::6::1::7::nil)%nat in H17.
  eapply ASlots_fold_any_idx_frm in H17; eauto.
  sep lifts (8::6::9::nil)%nat in H17.
  eapply Aarray'_fold_any_idx_frm in H17; eauto.
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    assert(Z.to_nat (Int.unsigned v'4) < 64)%nat. lia. 
    apply Z.le_trans with(m:= 64*4). simpl typelen.
    rewrite Nat2Z.inj_mul.
    lia. 
    rewrite max_unsigned_val. lia. 
  }
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  sep lifts (1::7::8::nil)%nat in H17.
  eapply Aarray'_fold_any_idx_frm in H17; eauto.
  2:{
    clear -Hv'4range. lia.
  }
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
  sep lifts (8::9::3::nil)%nat in H17.
  eapply fold_Acnode in H17; eauto.
  sep lifts (13::14::3::nil)%nat in H17.
  eapply fold_Acnode in H17; eauto.

  sep lifts (2::8::9::10::11::nil)%nat in H17.
  eapply fold_ACSpace in H17; eauto.
  sep lifts (2::9::10::11::12::nil)%nat in H17.
  eapply fold_ACSpace in H17; eauto.
  sep lifts (7::2::8::nil)%nat in H17.

  eapply ACSpaceAarray_fold_any_idx_frm in H17; eauto.
  2: lia. 
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl. 
    rewrite H4, H7.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (1::2::7::nil)%nat in H17.
  eapply ACSpaceAarray_fold_any_idx_frm in H17; eauto.
  2: lia. 
  2: lia.
  2:{
    rewrite app_length.
    simpl.
    rewrite H4, H7. 
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
  sep lift 10%nat. 
  eapply disj_split.
  right.
  sep normal. sep lift 3%nat. eapply disj_split.
  left.
  sep cancel cap1. sep cancel cap2.
  unfold AOSCSpacePrioTbl. sep cancel OSCSpacePrioTbl.
  unfold Aarray. sep cancel Aarray'. sep cancel AOSCSpaceObjectPointer.
  sep auto; eauto.
  rewrite app_assoc_reverse. auto.
  splits. 
  rewrite app_length. simpl.
  rewrite app_length. simpl.
  rewrite H1, H10, H11. rewrite S_add_sub_S.
  rewrite S_add_sub_S. 
  clear -Hc1 Hv'4range. lia.
  clear -Hv'4range. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite app_length. simpl. rewrite app_length.
  simpl.
  rewrite H4, H7, H9. rewrite S_add_sub_S.
  rewrite S_add_sub_S_add. clear -Hc1 Hv'4range. lia.
  
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  clear -Hv'4range. lia.
  clear -Htypematch.
  simpl in *.  rewrite app_assoc_reverse.  simpl. auto.
  clear -H6.
  simpl in H6. rewrite app_assoc_reverse.
  auto.
  clear -H5.
  simpl in H5. rewrite app_assoc_reverse.
  auto.
  rewrite list_trans.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  splits; rewrite app_assoc_reverse; auto.

  clear -H H12.
  unfold val_inj, bop_eval, val_eq in *.
  destruct (Int.eq i9 ($ CAP_CATEGORY_TYPE)) eqn: Heq1;
  destruct (Int.eq i9 ($ CAP_OBJECT_TYPE)) eqn: Heq2;
  destruct H; destruct H12; tryfalse.
  rewrite Inteq_false_is_Zneq in Heq1, Heq2.
  rewrite Int.unsigned_repr in Heq1, Heq2.
  auto. unfold CAP_OBJECT_TYPE. rewrite max_unsigned_val. lia.
  unfold CAP_CATEGORY_TYPE. rewrite max_unsigned_val. lia.
  rewrite app_assoc_reverse. auto.
  clear -Hv'6range.
  unfold SLOT_NUM in *.
  eapply Z2Nat.inj_lt; (int auto).
  auto. 
  clear -Hv'6range.
  unfold SLOT_NUM in *.
  eapply Z2Nat.inj_lt; (int auto).
  auto.
  eapply disj_rule.
  hoare_split_pure_all. 
  rename H into Heq.

  (* RETURN 〈 char_t 〉 ′ CNODE_NONE_FAULT*)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl. split; eauto.
  intros.
  rewrite Int.add_zero in H.
  rewrite Int.add_zero in H.
  simpl typelen in H.
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Acs.
  sep cancel Aier. sep cancel Ais. sep cancel Aop.
  sep cancel Aisr.
  simpl typelen in *.
  sep lifts (8::9::10::11::nil)%nat in H.
  eapply fold_Cap in H.
  sep lifts (7::8::1::9::nil)%nat in H.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'25++(v'27,(i9,((i10, i11), v1)))::v'26))
  in H; eauto.
  sep lifts (4::3::2::9::nil)%nat in H.
  sep lift 3%nat in H.
  rewrite Int.add_assoc in H.
  change ($ 4 +ᵢ  $ 4) with ($8) in H.
  sep lifts (2::3::1::4::nil)%nat in H.
  rewrite <- addition_trans in H.
  rewrite Int.unsigned_repr in H.
  rewrite Z2Nat.id in H.
  eapply fold_Cap in H.
  sep lifts (5::6::1::7::nil)%nat in H.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'13++(v'18,($ CAP_CATEGORY_TYPE,((i10, i11), v2)))::v'14))
  in H; eauto.
  sep lifts (8::6::9::nil)%nat in H.
  eapply Aarray'_fold_any_idx_frm in H; eauto.
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    assert(Z.to_nat (Int.unsigned v'4) < 64)%nat. lia. 
    apply Z.le_trans with(m:= 64*4). simpl typelen.
    rewrite Nat2Z.inj_mul.
    lia. 
    rewrite max_unsigned_val. lia. 
  }
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  sep lifts (1::7::8::nil)%nat in H.
  eapply Aarray'_fold_any_idx_frm in H; eauto.
  2: clear -Hv'4range; lia.
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
  sep lifts (8::9::3::nil)%nat in H.
  eapply fold_Acnode in H; eauto.
  sep lifts (13::14::3::nil)%nat in H.
  eapply fold_Acnode in H; eauto.

  sep lifts (2::8::9::10::11::nil)%nat in H.
  eapply fold_ACSpace in H; eauto.
  sep lifts (2::9::10::11::12::nil)%nat in H.
  eapply fold_ACSpace in H; eauto.
  sep lifts (7::2::8::nil)%nat in H.

  eapply ACSpaceAarray_fold_any_idx_frm in H; eauto.
  2: lia. 
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl. 
    rewrite H4, H7.
    rewrite S_add_sub_S. lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (1::2::7::nil)%nat in H.
  eapply ACSpaceAarray_fold_any_idx_frm
  with(cspacevl:= (v'17 ++
  (i5, i6,
  v'25 ++
  (v'27, (i9, (i10, i11, v1))) :: v'26, i0,
  l, v, i) :: v'20) ++
 (i7, i8,
 v'13 ++
 (v'18,
 ($ CAP_CATEGORY_TYPE, (i10, i11, v2)))
 :: v'14, i3, l0, v0, i2) :: v'21)
  in H; eauto.
  2: lia. 
  2: lia.
  2:{
    rewrite app_length.
    simpl. rewrite app_length. simpl.
    rewrite H4, H7, H9. 
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hv'4range Hc1.
    lia. 
  Optimize Proof.
  Optimize Heap.
    clear -Hv'4range. lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl.
    rewrite H4, H7.
    rewrite S_add_sub_S.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lift 10%nat. 
  eapply disj_split.
  right.
  sep normal. sep lift 3%nat. 
  eapply disj_split.
  right.
  eapply disj_split. left.
  sep cancel cap1. sep cancel cap2.
  unfold AOSCSpacePrioTbl. sep cancel OSCSpacePrioTbl.
  unfold Aarray. sep cancel Aarray'. sep cancel AOSCSpaceObjectPointer.
  sep auto; eauto.
  rewrite app_assoc_reverse. auto.
  splits.
  rewrite app_length. simpl.
  rewrite app_length. simpl.
  rewrite H1, H10, H11. rewrite S_add_sub_S.
  rewrite S_add_sub_S. clear -Hc1 Hv'4range. lia.
  clear -Hv'4range. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite app_length. simpl. rewrite app_length.
  simpl.
  rewrite H4, H7, H9. rewrite S_add_sub_S.
  rewrite S_add_sub_S. 
  clear -Hc1 Hv'4range. lia.
  clear -Hv'4range. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  
  rewrite app_assoc_reverse. auto.
  clear -H6.
  simpl in H6. rewrite app_assoc_reverse.
  auto.
  clear -H5.
  simpl in H5. rewrite app_assoc_reverse.
  auto.
  simpl.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  splits; rewrite app_assoc_reverse; auto.
  {
    unfold update_nth_cspace_slots_cap.
    rewrite app_assoc.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_list_length_imp; eauto.
    rewrite app_length. simpl.
    clear -H4 H7 Hc1.
    rewrite H4, H7. rewrite S_add_sub_S.
    lia. 
    eapply Z2Nat.inj_lt; try (int auto).
    rewrite app_length. simpl.
    clear -H4 H7 Hc1.
    rewrite H4, H7. rewrite S_add_sub_S.
    lia. 
    eapply Z2Nat.inj_lt; try (int auto).
  }
  clear -Heq.
  unfold val_inj, bop_eval,val_eq in Heq.
  destruct (Int.eq i9 ($ CAP_CATEGORY_TYPE)) eqn: Heqn.
  eapply Inteq_true_is_Zeq in Heqn.
  rewrite Int.unsigned_repr in Heqn. auto.
  unfold CAP_CATEGORY_TYPE. rewrite max_unsigned_val.
  lia.
  tryfalse.
  destruct Heq; tryfalse.
  rewrite app_length. simpl.
  rewrite H1, H10. rewrite S_add_sub_S.
  clear -Hc1. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt;(int auto).

  rewrite app_length. simpl. auto.
  rewrite app_length in Hl2len. simpl in Hl2len.
  auto.
  clear -Hv'6range. unfold SLOT_NUM in *. int auto.
  rewrite app_length. simpl. auto.
  rewrite app_length in Hl2len. simpl in Hl2len.
  auto. auto.
  eapply Z.ge_le. eapply unsigned_ge0.
  clear -Hv'6range.
  unfold SLOT_NUM in *.
  rewrite max_unsigned_val. lia.
  lia.
  clear -Hv'6range.
  unfold SLOT_NUM in *.
  int auto. auto.
  pure intro. eapply disj_rule. pure intro. eapply pfalse_rule.
  pure intro. eapply pfalse_rule.
  Unshelve.
  all: auto.
Qed.