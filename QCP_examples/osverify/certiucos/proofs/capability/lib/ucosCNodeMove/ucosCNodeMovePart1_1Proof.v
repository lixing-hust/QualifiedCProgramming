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
Set Keyed Unification.
Lemma ucosCNodeMovePart1_1proof:
forall 
(ct: tid)
(v'5: int32)
(H2: Int.unsigned v'5 <= 255)
(v'28: int32)
(H3: Int.unsigned v'28 <= 255)
(v':val)
(v'0: val)
(v'1: val)
(v'2: val)
(v'3: val)
(v'6: int32)
(v'9: block)
(v'10: int32)
(v'22: list val)
(v'23: list val)
(v'24: list val)
(b: block)
(i1: int32)
(b0: block)
(i4: int32)
(v'39: CSpaceptr2prioMod.map)
(v'17: list cspace_val_type)
(i5: int32)
(i6: int32)
(i0: int32)
(l: list val)
(v: val)
(i: int32)
(i7: int32)
(i8: int32)
(i3: int32)
(l0: list val)
(v0: val)
(i2: int32)
(v'20: list cspace_val_type)
(v'21: list cspace_val_type)
(v'25: list
(int32 * (int32 * cap_content_type)))
(v'26: list
         (int32 * (int32 * cap_content_type)))
(v'27: int32)
(i9: int32)
(i10: int32)
(i11: int32)
(v'13:  list
(int32 * (int32 * cap_content_type)))
(v'14: list
         (int32 * (int32 * cap_content_type)))
(v'18: int32)
(i12: int32)
(i13: int32)
(i14: int32)
(v2: val)
(v'29: val)
(v'30: ier)
(v'31: absop)
(v'32: cs)
(v'33: isr)
(v'36: list val)
(H5: CSPACEList_P
       (v'22 ++
        (Vptr (b ↝ {i1}) :: v'23) ++
        Vptr (b0 ↝ {i4}) :: v'24) 0 v'39)
(H6: ptrvl_to_cspace_to_ptrvl
       (v'22 ++
        (Vptr (b ↝ {i1}) :: v'23) ++
        Vptr (b0 ↝ {i4}) :: v'24) v'39)
(Hv'4range: Int.unsigned v'28 < 63)
(Hv'5range: Int.unsigned v'5 < 63)
(Hv'6range: Int.unsigned v'6 < SLOT_NUM)
(Hv'13len: length
             (v'22 ++
              (Vptr (b ↝ {i1}) :: v'23) ++
              Vptr (b0 ↝ {i4}) :: v'24) =
           64%nat)
(Hv'14len: length
(v'17 ++
 ((i5, i6,
  v'25 ++
  (v'27, (i9, (i10, i11, v'29))) :: v'26, i0,
  l, v, i) :: v'20) ++
 (i7, i8,
 v'13 ++ (v'18, (i12, (i13, i14, v2))) :: v'14,
 i3, l0, v0, i2) :: v'21) = 64%nat)
(Htypematch: array_type_vallist_match
               CSPACE ∗
               (v'22 ++
                (Vptr (b ↝ {i1}) :: v'23) ++
                Vptr (b0 ↝ {i4}) :: v'24))
(Hv'4: (Int.unsigned v'28 <=?
        Byte.max_unsigned) = true)
(Hv'5: (Int.unsigned v'5 <=?
        Byte.max_unsigned) = true)
(Hnotnull2: nth_val'
              (Z.to_nat (Int.unsigned v'5))
              (v'22 ++
               (Vptr (b ↝ {i1}) :: v'23) ++
               Vptr (b0 ↝ {i4}) :: v'24) <>
            Vnull)
(Hnotnull1: nth_val'
              (Z.to_nat (Int.unsigned v'28))
              (v'22 ++
               (Vptr (b ↝ {i1}) :: v'23) ++
               Vptr (b0 ↝ {i4}) :: v'24) <>
            Vnull)
(HpCSpace2type: isptr
                  (nth_val'
                     (Z.to_nat
                        (Int.unsigned v'5))
                     (v'22 ++
                      (Vptr (b ↝ {i1})
                       :: v'23) ++
                      Vptr (b0 ↝ {i4})
                      :: v'24)))
(Hc1: Int.unsigned v'28 > Int.unsigned v'5)
(HpCSpace1type: isptr
                  (nth_val'
                     (Z.to_nat
                        (Int.unsigned v'28))
                     (v'22 ++
                      (Vptr (b ↝ {i1})
                       :: v'23) ++
                      Vptr (b0 ↝ {i4})
                      :: v'24)))
(H1: length v'22 =
     Z.to_nat (Int.unsigned v'5))
(H11: length v'24 =
      (64 - S (Z.to_nat (Int.unsigned v'28)))%nat)
(H10: length v'23 =
      (Z.to_nat (Int.unsigned v'28) -
       S (Z.to_nat (Int.unsigned v'5)))%nat)
(H4: length v'17 =
     Z.to_nat (Int.unsigned v'5))
(H9: length v'21 =
     (64 - S (Z.to_nat (Int.unsigned v'28)))%nat)
(H7: length v'20 =
     (Z.to_nat (Int.unsigned v'28) -
      S (Z.to_nat (Int.unsigned v'5)))%nat)
(Hl1len: length
(v'25 ++
 (v'27,
 (i9, (i10, i11, v'29)))
 :: v'26) = Z.to_nat SLOT_NUM)
(Hirange: Int.unsigned i0 <= 64)
(Hlv'15: ptrlv_in_cspace_ls l v'39)
(Hltype: array_type_vallist_match
           UNION cspace ⋆ l)
(Hlnotnull: children_not_null l
              (Z.to_nat (Int.unsigned i0)))
(Hl2len: length
(v'13 ++
 (v'18, (i12, (i13, i14, v2)))
 :: v'14) = Z.to_nat SLOT_NUM)
(Hi1range: Int.unsigned i3 <= 64)
(Hl0v'15: ptrlv_in_cspace_ls l0 v'39)
(Hl0type: array_type_vallist_match
            UNION cspace ⋆ l0)
(Hl0notnull: children_not_null l0
               (Z.to_nat (Int.unsigned i3)))
(Hllen: length l = Z.to_nat MaxChildNum)
(Hl0len: length l0 = Z.to_nat MaxChildNum)
(H0: length v'25 =
     Z.to_nat (Int.unsigned v'6))
(H16: length v'26 =
      (Z.to_nat SLOT_NUM -
       S (Z.to_nat (Int.unsigned v'6)))%nat)
(H8: nth_slots
(Z.to_nat (Int.unsigned v'6))
(v'25 ++
 (v'27, (i9, (i10, i11, v'29)))
 :: v'26) =
Some (v'27, (i9, (i10, i11, v'29))))
(H13: length v'13 =
      Z.to_nat (Int.unsigned v'6))
(H15: length v'14 =
      (Z.to_nat SLOT_NUM -
       S (Z.to_nat (Int.unsigned v'6)))%nat)
(H14: nth_slots
(Z.to_nat (Int.unsigned v'6))
(v'13 ++
 (v'18, (i12, (i13, i14, v2)))
 :: v'14) =
Some (v'18, (i12, (i13, i14, v2))))
(Hisptrv1: isptr v'29)
(Hisptrv2: isptr v2)
(H: val_inj
      (bop_eval (Vint32 i9)
         (V$ CAP_CATEGORY_TYPE) long long
         oeq) = Vint32 Int.zero \/
    val_inj
      (bop_eval (Vint32 i9)
         (V$ CAP_CATEGORY_TYPE) long long
         oeq) = Vnull)
(H12: val_inj
        (bop_eval (Vint32 i9)
           (V$ CAP_OBJECT_TYPE) long long
           oeq) <> Vint32 Int.zero)
(H17: val_inj
        (bop_eval (Vint32 i9)
           (V$ CAP_OBJECT_TYPE) long long
           oeq) <> Vnull)
(H18: val_inj
        (bop_eval (Vint32 i9)
           (V$ CAP_OBJECT_TYPE) long long
           oeq) <> Vundef)
(v'19: val)
(v'34: block)
(v'35: int32)
(H22: ptrvl_to_cspace_to_ptrvl
        ((v'22 ++ Vptr (b ↝ {i1}) :: v'23) ++
         Vptr (b0 ↝ {i4}) :: v'24) v'39)
(H21: CSPACEList_P
        ((v'22 ++ Vptr (b ↝ {i1}) :: v'23) ++
         Vptr (b0 ↝ {i4}) :: v'24) 0 v'39)
(H24: isptr v'29)
(H19: Int.unsigned v'28 < OS_LOWEST_PRIO)
(v'4: int32)
(H20: nth_val'
        (Z.to_nat (Int.unsigned v'28))
        v'36 = Vint32 v'4)
(H23: nth_val'
        (Z.to_nat (Int.unsigned v'28))
        ((v'22 ++
          Vptr (b ↝ {i1}) :: v'23) ++
         Vptr (b0 ↝ {i4}) :: v'24) <>
      Vnull)
(v'7: Z)
(v'8: list slot_val_type)
(v'11: list slot_val_type)
(v'12: list slot_val_type)
(H25: get_slots
        (Z.to_nat (Int.unsigned v'28))
        (v'17 ++
         (i5, i6,
         v'25 ++
         (v'27,
         (i9, (i10, i11, v'29)))
         :: v'26, i0, l, v, i)
         :: v'20 ++
            (i7, i8,
            v'13 ++
            (v'18,
            (i12, (i13, i14, v2)))
            :: v'14, i3, l0, v0, i2)
            :: v'21) =
      Some (v'8 ++ v'11 ++ v'12))
(H26: length v'8 =
      Z.to_nat OBJ_POSITION)
(H27: length (v'8 ++ v'11) =
      Z.to_nat (Int.unsigned v'4))
(H28: Slots_eq_object v'7 v'11 v'29)
(H29: Some v'19 =
      Some (V$ (v'7 + OBJ_POSITION)) /\
      OBJ_POSITION <= v'7 + OBJ_POSITION < 255),
{|Cap_spec, GetHPrio, OSLInv, I,
fun v1 : option val =>
((EX v3 : val,
LV func_capability @ Tint32 |-> v3) **
(EX v3 : val,
LV srcTask_Prio @ Tint8 |-> v3) **
(EX v3 : val,
LV destTask_Prio @ Tint8 |-> v3) **
(EX v3 : val, LV idx @ Tint32 |-> v3) **
(EX v3 : val,
LV pCSpace1 @ Tptr CSPACE |-> v3) **
(EX v3 : val,
LV pCSpace2 @ Tptr CSPACE |-> v3) **
(EX v3 : val, LV cap1 @ Tptr Cap |-> v3) **
(EX v3 : val, LV cap2 @ Tptr Cap |-> v3) **
Aemp) **
(EX (destTask_Prio srcTask_Prio
  func_capability : int32) 
(er : ier) (s : absop) (b1 : block)
(i15 : int32) (cs : language.cs)
(isr : language.isr) (ptrvl : list val)
(priotbl priotbl' priotbl'' priotbl''': list cspace_val_type)
(cspacels : CSpaceptr2prioMod.map)
(pointervl : vallist)
(pointervl' : list val)
(captype_val categorycontent_val
categoryright_val : int32)
(categoryobject_val : val)
(origin_right : int32)
(origin_object : val)
(captype_val_dest: int32)
 (categorycontent_val_dest: int32)(categoryright_val_dest : int32),
Aie false **
Ais nil **
Acs cs **
Aisr isr **
Aier er **
<|| s ||>  **
[|Some (Vint32 v'28) =
Some (Vint32 destTask_Prio)|] **
[|Some (Vint32 v'5) =
Some (Vint32 srcTask_Prio)|] **
[|Some (Vint32 v'6) =
Some (Vint32 func_capability)|] **
AOSCSpaceObjectPointer pointervl' **
[|CSPACEList_P ptrvl 0 cspacels|] **
[|ptrvl_to_cspace_to_ptrvl ptrvl cspacels|] **
AOSCSpacePrioTbl (b1, i15) ptrvl priotbl'''
cspacels **
[|logic_cs v'32
:: logic_isr v'33
   :: logic_ier v'30
      :: logic_cspacel
           (v'17 ++
            ((i5, i6,
             v'25 ++
             (v'27,
             (i9, (i10, i11, v'29)))
             :: v'26, i0, l, v, i)
             :: v'20) ++
            (i7, i8,
            v'13 ++
            (v'18,
            (i12, (i13, i14, v2)))
            :: v'14, i3, l0, v0, i2)
            :: v'21)
         :: logic_lv v'36
            :: logic_code v'31
               :: logic_abscap v'39
                  :: logic_lv
                       (v'22 ++
                       (Vptr (b, i1)
                       :: v'23) ++
                       Vptr (b0, i4)
                       :: v'24) :: nil =
logic_cs cs
:: logic_isr isr
   :: logic_ier er
      :: logic_cspacel priotbl
         :: logic_lv pointervl
            :: logic_code s
               :: logic_abscap
                    cspacels
                  :: logic_lv ptrvl
                     :: nil|] **
p_local OSLInv ct init_lg **(
  [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull \/
  nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl = Vnull|] ** [|v1 = Some(Vint32(Int.repr CNODE_MOVE_FAILURE))/\priotbl''' = priotbl /\ pointervl' = pointervl|] \\//
  ([|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull /\
  nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl <> Vnull|] **
  [|get_capability (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
  priotbl = Some(captype_val, (categorycontent_val, categoryright_val, categoryobject_val))|] **
  [|get_capability (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
  priotbl = Some(captype_val_dest, (categorycontent_val_dest, categoryright_val_dest, origin_object))|] **
  (
  ([|(Int.unsigned captype_val <> CAP_CATEGORY_TYPE) /\ (Int.unsigned captype_val <> CAP_OBJECT_TYPE)|]
  ** [|v1 = Some(Vint32 ($CNODE_MOVE_FAILURE))|]
  ** [|priotbl''' = priotbl /\ pointervl' = pointervl|]) \\//(
 [|(Int.unsigned captype_val = CAP_CATEGORY_TYPE)|] **
[|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
($CAP_CATEGORY_TYPE , (categorycontent_val, categoryright_val, origin_object)))|] **
[|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
($0 , ($0, $0, categoryobject_val)))|] **
[|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
($ SLOT_NULL_CAP))|] **
[|pointervl' = pointervl|] ** [|v1 = Some(Vint32 ($CNODE_NONE_FAULT))|]
  ) \\// ([|(Int.unsigned captype_val = CAP_OBJECT_TYPE)|] **
    (EX idxval idxz,
    GetObjSlotRetval destTask_Prio ptrvl pointervl priotbl categoryobject_val idxval **
    [|idxz = Int.unsigned (Vint32_inj (val_inj idxval))|] **(
     [|idxz = SLOT_NULL_CAP|] ** (
      EX pointeridx, 
      [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) pointervl = (Vint32 pointeridx)|] **
      (([|Int.unsigned pointeridx >= 255|] ** [|v1 = Some(Vint32 ($SLOT_RANGE_OVERFLOW)) /\ priotbl''' = priotbl /\
      pointervl' = pointervl|])\\//
      ([|Int.unsigned pointeridx < 255|] **  [|v1 = Some(Vint32 ($CNODE_NONE_FAULT))|] **
      [|pointervl' = update_nth_val (Z.to_nat(Int.unsigned destTask_Prio)) pointervl (Vint32 (Int.add pointeridx (Int.repr 1)))|] **
      [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat (Int.unsigned pointeridx)) priotbl
      ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|]  **
      [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
      ($0 , ($0, categoryright_val, Vnull)))|]  ** 
      [|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
      ($ SLOT_NULL_CAP))|])))
       \\//[|idxz <> SLOT_NULL_CAP|] **(
      [|v1 = Some(Vint32 ($CNODE_NONE_FAULT))|] **
      [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat idxz) priotbl
      ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|]
      ** [|priotbl'' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl'
      ($0 , ($0, categoryright_val, Vnull)))|] **
      [|priotbl''' = (update_nth_cspace_slots_type (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl''
      ($ SLOT_NULL_CAP))|] **  [|pointervl' = pointervl|]
      ))
  ))
  )
  )))**
A_dom_lenv
((func_capability ↝ {long})
  :: (srcTask_Prio ↝ {char_t})
    :: (destTask_Prio ↝ {char_t})
        :: (idx ↝ {long})
          :: (pCSpace1 ↝ {CSPACE ∗})
              :: (pCSpace2 ↝ {CSPACE ∗})
                :: (cap1 ↝ {Cap ∗}) :: (cap2 ↝ {Cap ∗}) :: nil),
Afalse|}|- ct
{{Aie false **
Ais nil **
Acs v'32 **
Aisr v'33 **
Aier v'30 **
 <|| v'31 ||>  **
AOSCSpacePrioTbl (v'34, v'35)
  ((v'22 ++ Vptr (b, i1) :: v'23) ++
   Vptr (b0, i4) :: v'24)
  (v'17 ++
   (i5, i6,
   v'25 ++
   (v'27, (i9, (i10, i11, v'29))) :: v'26,
   i0, l, v, i)
   :: v'20 ++
      (i7, i8,
      v'13 ++
      (v'18, (i12, (i13, i14, v2))) :: v'14,
      i3, l0, v0, i2) :: v'21) v'39 **
AOSCSpaceObjectPointer v'36 **
p_local OSLInv ct init_lg **
LV idx @ Tint32 |-> v'19 **
LV cap2 @ Tptr Cap
|-> Vptr
      (b,
      (((i1 +ᵢ  Int.zero) +ᵢ  $ 8) +ᵢ
       Int.mul ($ Z.of_nat 20)
         ($
          Z.of_nat
            (Z.to_nat (Int.unsigned v'6))))
      +ᵢ  $ 4) **
LV cap1 @ Tptr Cap
|-> Vptr
      (b0,
      (((i4 +ᵢ  Int.zero) +ᵢ  $ 8) +ᵢ
       Int.mul ($ Z.of_nat 20)
         ($
          Z.of_nat
            (Z.to_nat (Int.unsigned v'6))))
      +ᵢ  $ 4) **
LV pCSpace2 @ Tptr CSPACE |-> Vptr (b, i1) **
LV pCSpace1 @ Tptr CSPACE |-> Vptr (b0, i4) **
LV func_capability @ Tint32 |-> Vint32 v'6 **
LV srcTask_Prio @ Tint8 |-> Vint32 v'5 **
LV destTask_Prio @ Tint8 |-> Vint32 v'28 **
A_dom_lenv
  ((func_capability, Tint32)
   :: (srcTask_Prio, Tint8)
      :: (destTask_Prio, Tint8)
         :: (idx, Tint32)
            :: (pCSpace1, Tptr CSPACE)
               :: (pCSpace2, Tptr CSPACE)
                  :: (cap1, Tptr Cap)
                     :: (cap2, Tptr Cap)
                        :: nil)}} 
      If (idx ′ ==ₑ ′ SLOT_NULL_CAP)
      {idx ′ =ₑ OSCSpaceObjectPointer ′ [destTask_Prio ′];ₛ
      If (idx ′ ≥ ′ SLOT_NUM){RETURN ′ SLOT_RANGE_OVERFLOW};ₛ
      ++ OSCSpaceObjectPointer ′ [destTask_Prio ′]};ₛ
      cap1 ′ =ₑ
      &ₐ
      (((pCSpace1 ′ → cnode) .. slots) [idx ′])
      .. capability;ₛ
      cap1 ′ → cap_type =ₑ ′ CAP_OBJECT_TYPE;ₛ
      ((cap1 ′ → cap_content) .. object) .. object_right =ₑ
      ((cap2 ′ → cap_content) .. object) .. object_right;ₛ
      ((cap1 ′ → cap_content) .. object) .. object_t =ₑ
      ((cap2 ′ → cap_content) .. object) .. object_t;ₛ
      cap2 ′ → cap_type =ₑ ′ 0;ₛ
      ((cap2 ′ → cap_content) .. object) .. object_right =ₑ
      ′ 0;ₛ
      ((cap2 ′ → cap_content) .. object) .. object_t =ₑ
      〈 (Void) ∗ 〉 NULL;ₛ
      (((pCSpace2 ′ → cnode) .. slots) [func_capability ′])
      .. slot_type =ₑ ′ SLOT_NULL_CAP;ₛ
      RETURN 〈 char_t 〉 ′ CNODE_NONE_FAULT {{Afalse}}.
Proof.
  intros.
  unfold AOSCSpaceObjectPointer.
  pure intro.
  assert(Z.to_nat(Int.unsigned v'28) < 64)%nat. 
  clear -Hv'4range.
  lia.


  hoare forward.
  destruct (Int.eq ($ (v'7 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)); eauto.
  hoare_split_pure_all. false.
  clear -H33 H34 H35.
  unfold val_inj in H35.
  assert(Int.eq ($ (v'7 + OBJ_POSITION))
  ($ SLOT_NULL_CAP) = false).
  unfold OBJ_POSITION in *.
  unfold SLOT_NULL_CAP.
  clear -H33 H34. int auto.
  rewrite H in H35.
  destruct H35; tryfalse.
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  clear H35.
  (*这里需要展开AOSCSPrioTbl*)
  eapply backward_rule1.
  intros.
  sep lift 7%nat in H35.
  eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with (idx1:=Z.to_nat(Int.unsigned v'28)) (idx2:=Z.to_nat(Int.unsigned v'5))in H35; eauto.
  unfold AOSCSpacePrioTbl in H35. sep split in H35.
  rewrite Hv'14len. lia.
  clear -Hc1. 
  eapply Z2Nat.inj_lt; try (int auto).
  clear -Hnotnull2. rewrite app_assoc_reverse.
  simpl in *. auto.
  hoare_split_pure_all.
  simpljoin.
  (*变量一一对应*)
  eapply list_map_eq5 in H35.
  destruct H35. subst v'40.
  destruct H43. inverts H35.
  destruct H43. subst v'41.
  destruct H43. inverts H43. inverts H35.
 
  eapply eq_sym in H36.
  rewrite list_trans_1 in H36.
  eapply list_map_eq5 in H36.
  destruct H36. subst v'17.
  destruct H36. subst v'16.
  destruct H36. subst v'37.
  destruct H36. subst v'19.
  subst v'38.
  2:{
    rewrite H4, H38. auto.
  }
  2:{
    rewrite H7, H39. auto.
  }
  2:{
    rewrite H9, H40. auto.
  }
  2:{
    rewrite H1, H37. auto.
  }
  2:{
    rewrite H10, H41. auto.
  }
  2:{
    rewrite H11, H42. auto.
  }



  unfold ACSpace.

  unfold Acnode.
  pure intro.
  rename H52 into Hi2range.
  rename H53 into Hirange'.
  (*unfold two slots*)
  eapply backward_rule1.
  intros.
  sep lifts (10::18::nil)%nat in H44.
  eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'6)) in H44.
  sep lift 2%nat in H44.
  eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(v'7+OBJ_POSITION)) in H44.
  exact H44.
  clear -H34.
  unfold SLOT_NUM. lia. auto.
  rewrite app_length. simpl.
  rewrite app_length in Hl2len. simpl in Hl2len. auto.
  clear -Hv'6range.
  eapply Z2Nat.inj_lt; (int auto).
  unfold SLOT_NUM. lia. 
  auto. 
  Optimize Proof.
  Optimize Heap.
  rewrite app_length. simpl.
  rewrite app_length in Hl1len. simpl in Hl1len. auto.
  pure intro.

  unfold ACap.
  destruct v'41. destruct c. destruct p.
  destruct v'24. destruct c. destruct p.
  pure intro.
  rewrite H54 in *.
  rewrite H44 in *.
  eapply list_map_eq3 in H44.
  destruct H44. subst v'37.
  destruct H61. inverts H44. 
  subst v'38.
  2:{
    rewrite H52, H0. auto.
  }
  2:{
    rewrite H58, H16. auto.
  }
  (*cap1 ′ =ₑ&ₐ(((pCSpace1 ′ → cnode) .. slots) [idx ′])
            .. capability;ₛ*)
  hoare_lifts_trms_pre(Aop).
  eapply seq_rule.
  eapply assign_rule_lvar.
  split; intros.
  sep_lifts_trms_in H44 (Alvarmapsto cap1).
  exact H44.
  intros. sep auto.
  intros.
  eapply calculate_rv_expr_id_addr.

  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep split in H44.
        sep cancel pCSpace1.
        sep_lifts_trms_in H44 (Alvarmapsto idx).
        eapply LV_to_Rv in H44; eauto.

        instantiate(2:=Z.to_nat(v'7+OBJ_POSITION)).
        rewrite Z2Nat.id.
        exact H44.
        clear -H33.
        unfold OBJ_POSITION in *. lia.
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

  (*cap1 ′ → cap_type =ₑ ′ CAP_CATEGORY_TYPE*)
  eapply seq_rule.
  eapply assign_rule_aop.
  2:{
    intros.
    eapply local_val_struct_member_addr.
    exact H44.
    unfold Cap. eauto.
    unfold field_offset. simpl. eauto.
    simpl. eauto.
  }
  2:{
    split; intros. simpl typelen in *.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    rewrite Z2Nat.id.
    sep lift 11%nat in H44.
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    exact H44.
    clear -H33 H34.
    unfold OBJ_POSITION in *. int auto.
    lia. clear -H33. unfold OBJ_POSITION in *. lia.

    intros.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    simpl typelen in *.
    rewrite Z2Nat.id in H44 at 1.
    rewrite <- addition_trans in H44 at 1. 
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
    rewrite Int.unsigned_repr in H44 at 1.
    sep auto.
  Optimize Proof.
  Optimize Heap.
    clear -H33 H34. 
    unfold OBJ_POSITION in *.  
    rewrite max_unsigned_val. 
    int auto. lia.
    clear -H33. unfold OBJ_POSITION in *.
    lia.
  }
  2:{
    intros.
    destruct_s s. simpl.
    split; eauto.
  }
  eapply eq_int. auto.
  intros. eexists. sep cancel p_local. simpl. auto.
  (*((cap1 ′ → cap_content) .. object) .. object_right =ₑ
  ((cap2 ′ → cap_content) .. object) .. object_right;ₛ*)
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
        sep lift 2%nat in H44.
        exact H44.
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
  rewrite Z2Nat.id.
  
  rewrite Int.add_zero in *. rewrite Int.add_zero in *.
  simpl typelen in *.
  sep lift 12%nat in H44.
  rewrite <- addition_trans.
  rewrite Int.unsigned_repr.
  rewrite Int.add_zero.
  exact H44. 
  clear -H33 H34. 
  unfold OBJ_POSITION in *.  
  rewrite max_unsigned_val. 
  int auto. lia.
  clear -H33. unfold OBJ_POSITION in *.
  lia.
  simpl typelen in *.
  rewrite Int.add_zero in *.
  rewrite Int.add_zero in *.
  sep cancel cap2.
  sep cancel cap1.
  sep cancel ASlots.
  rewrite Z2Nat.id.
  rewrite <- addition_trans.
  rewrite Int.unsigned_repr.
  rewrite <- addition_trans in H44.
  rewrite Int.unsigned_repr in H44.
  rewrite Z2Nat.id in H44.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  rewrite Int.add_zero in H44.
  sep auto.
  clear -H33. unfold OBJ_POSITION in *. int auto.
  rewrite Z2Nat.id.
  clear -H33 H34. 
  unfold OBJ_POSITION in *.  
  rewrite max_unsigned_val. 
  int auto.
  Optimize Proof.
  Optimize Heap.
  clear -H33. unfold OBJ_POSITION in *.
  lia.
  lia.
  clear -H33 H34. 
  unfold OBJ_POSITION in *.  
  rewrite max_unsigned_val. 
  int auto. lia.
  clear -H33. unfold OBJ_POSITION in *.
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
          sep_lifts_trms_in H44 (Alvarmapsto cap2).
          exact H44.
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
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    sep lift 6%nat in H44.
    unfold Aptrmapsto in H44 at 1.
    exact H44.
    clear -Hv'6range. int auto.
    lia.
  }
  simpl. auto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.
(*((cap1 ′ → cap_content) .. object) .. object_t =ₑ
  ((cap2 ′ → cap_content) .. object) .. object_t*)
  hoare_lifts_trms_pre(Aop).
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
        sep lift 3%nat in H44.
        exact H44.
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
  rewrite Z2Nat.id.
  rewrite Int.add_zero in *. rewrite Int.add_zero in *.
  simpl typelen in *.
  sep lift 14%nat in H44.
  rewrite <- addition_trans.
  change ($ 4 +ᵢ  $ 4) with ($8).
  rewrite Int.add_assoc.
  change ($ 4 +ᵢ  $ 8) with ($12).
  rewrite Int.unsigned_repr.
  exact H44. 
  clear -H33 H34. 
  unfold OBJ_POSITION in *.  
  rewrite max_unsigned_val. 
  int auto. lia.
  clear -H33. unfold OBJ_POSITION in *.
  lia.
  Optimize Proof.
  Optimize Heap.
  simpl typelen in *.
  rewrite Int.add_zero in *.
  rewrite Int.add_zero in *.
  rewrite Int.add_zero in *.
  sep cancel cap2.
  sep cancel cap1.
  sep cancel ASlots.
  rewrite Z2Nat.id.
  rewrite <- addition_trans.
  rewrite Int.unsigned_repr.
  rewrite <- addition_trans in H44.
  rewrite Int.unsigned_repr in H44.
  rewrite Z2Nat.id in H44.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  change ($ 4 +ᵢ  $ 4) with ($8) in H44.
  rewrite Int.add_assoc in H44 at 1.
  change ($ 4 +ᵢ  $ 8) with ($12) in H44.
  sep cancel 1%nat 3%nat.
  do 37(try (sep cancel 1%nat 1%nat)). auto.
  clear -H33. unfold OBJ_POSITION in *. int auto.
  rewrite Z2Nat.id.
  clear -H33 H34. 
  unfold OBJ_POSITION in *.  
  rewrite max_unsigned_val. 
  int auto. 
  clear -H33. unfold OBJ_POSITION in *.
  lia.
  lia.
  clear -H33 H34. 
  unfold OBJ_POSITION in *.  
  rewrite max_unsigned_val. 
  int auto. lia.
  clear -H33. unfold OBJ_POSITION in *.
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
          sep_lifts_trms_in H44 (Alvarmapsto cap2).
          exact H44.
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
    rewrite of_to_nat_unsignedv'. 
    rewrite <- addition_trans.
    rewrite Int.unsigned_repr.
    sep lift 9%nat in H44.
    unfold Aptrmapsto in H44 at 1.
    change ($ 4 +ᵢ  $ 4) with ($8).
    rewrite Int.add_assoc.
    change ($ 4 +ᵢ  $ 8) with ($12).
    exact H44.
    clear -H9. int auto.
    lia.
  }
    simpl. auto.
    clear -H59.
    unfold isptr in *.
    destruct H59. subst v1. auto.
    destruct H. subst v1. auto.
  }
  eapply eq_vptr. eauto.
  intros.
  eexists. sep cancel p_local. simpl. auto.

  (*cap2 ′ → cap_type =ₑ ′ 0*)
  eapply seq_rule.
  eapply assign_rule_aop.
  2:{
    intros.
    eapply local_val_struct_member_addr.
    sep_lifts_trms_in H44 (Alvarmapsto cap2).
    sep cancel cap2. 
    exact H44.
    unfold Cap. eauto.
    unfold field_offset. simpl. eauto.
    simpl. eauto.
  }
  2:{
    intros. split. intros.
    rewrite Int.add_zero.
    sep lift 7%nat in H44.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
    rewrite Int.add_zero.
    exact H44. lia.
    intros.
    rewrite Int.add_zero in H44.
    
    sep lift 8%nat.
    rewrite <- addition_trans in H44 at 1.
    rewrite of_to_nat_unsignedv' in H44 at 1.
    rewrite Int.repr_unsigned in H44 at 1.
    sep auto.
  Optimize Proof.
  Optimize Heap.
    rewrite Int.add_zero in H44.
    auto.
    lia.
  }
  2:{
    intros.
    destruct_s s. simpl. split; eauto.
  }
  eapply eq_int. auto.
  intros.
  eexists. sep cancel p_local. simpl. auto.
  (*((cap2 ′ → cap_content).. category).. category_content =ₑ ′ 0;ₛ*)
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
          sep_lifts_trms_in H44 (Alvarmapsto cap2).
          sep cancel cap2. 
          exact H44.
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
    intros.
    split. intros.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
    
    sep lift 8%nat in H44.
    rewrite Int.add_zero.
    exact H44.
    lia.
    intros.
    rewrite Int.add_zero in H44.
    rewrite Int.add_zero in H44.
    sep lift 8%nat. 
    rewrite <- addition_trans in H44 at 1.
    rewrite of_to_nat_unsignedv' in H44 at 1.
    rewrite Int.repr_unsigned in H44 at 1.
    sep auto.
    rewrite Int.add_zero in H44. auto.
    lia.
  }
  2:{
    intros.
    destruct_s s. simpl. split; eauto.
  }
  eapply eq_int.
  auto.
  intros. eexists. sep cancel p_local.
  simpl. auto.
  (*((cap2 ′ → cap_content).. category).. category_right =ₑ′ 0*)
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
          sep_lifts_trms_in H44 (Alvarmapsto cap2).
          sep cancel cap2. 
          exact H44.
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
    intros.
    split. intros.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    rewrite <- addition_trans.
    rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
    sep lift 10%nat in H44.
    rewrite Int.add_assoc.
    change ($ 4 +ᵢ  $ 4) with ($8).
    exact H44.
    lia.
  Optimize Proof.
  Optimize Heap.
    intros.
    sep lift 10%nat. 
    rewrite Int.add_zero in H44 at 1.
    rewrite Int.add_assoc in H44 at 1.
    change ($ 0 +ᵢ  $ 4) with ($4) in H44.
    rewrite Int.add_assoc in H44 at 1.
    change ($ 4 +ᵢ  $ 4) with ($8) in H44.
    rewrite <- addition_trans in H44 at 1.
    rewrite of_to_nat_unsignedv' in H44 at 1.
    rewrite Int.repr_unsigned in H44 at 1.
    sep auto.
    lia.
  }

  2:{
    intros.
    destruct_s s. simpl. split; eauto.
  }
  eapply eq_vptr.
  eauto.
  intros. eexists. sep cancel p_local.
  simpl. auto.
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
         sep_lifts_trms_in H44 (Alvarmapsto pCSpace2).
         sep cancel pCSpace2.
         eapply LV_to_Rv.
         3:{
           sep_lifts_trms_in H44 (Alvarmapsto func_capability).
           instantiate (2:=Z.to_nat(Int.unsigned v'6)).
           rewrite of_to_nat_unsignedv'.
           rewrite Int.repr_unsigned.
           exact H44.
         }
         auto.
         simpl. auto.
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
   simpl. eauto.
   unfold field_offset. simpl. eauto.
 }
 2:{
   rewrite Int.add_zero.
   rewrite Int.add_zero.
   rewrite Int.add_zero.
   rewrite Int.add_zero.
   rewrite Int.add_zero.
   rewrite Int.add_zero.
   rewrite Int.add_zero.
   rewrite Int.add_zero.
   simpl typelen.
   intros. split. intros.
   change ($ 4 +ᵢ  $ 4)  with ($8).
   rewrite <- addition_trans.
   rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
   sep lift 9%nat in H44.
   exact H44.
   lia.
   intros.
   change ($ 4 +ᵢ  $ 4)  with ($8) in H44.
   rewrite of_to_nat_unsignedv' in H44 at 1.
   rewrite Int.repr_unsigned in H44 at 1.
   rewrite <- addition_trans in H44 at 1.
   sep auto.
  Optimize Proof.
  Optimize Heap.
   lia.
 }
 2:{
   intros.
   destruct_s s. simpl. split; eauto.
 }
 eapply eq_int. auto.
 intros.
 eexists. sep cancel p_local. simpl. auto.
  (*RETURN 〈 char_t 〉 ′ CNODE_NONE_FAULT*)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl. split; eauto.
  intros.

  (*fold_ACSpaceAarray*)
  rewrite Int.add_zero in H44.
  rewrite Int.add_zero in H44.
  change ($ 4 +ᵢ  $ 4)  with ($8) in H44.
  simpl typelen in H44.
  sep lifts (5::4::11::3::nil)%nat in H44.
  sep lift 4%nat in H44. 
  rewrite Int.add_assoc in H44 at 1.
  change ($ 4 +ᵢ  $ 8)  with ($12) in H44.
  sep lifts (2::3::4::1::nil)%nat in H44.
  rewrite addition_trans in H44 at 1.
  rewrite of_to_nat_unsignedv' in H44.
  rewrite Int.repr_unsigned in H44.
  eapply fold_Cap in H44.
  sep lifts (8::3::1::9::nil)%nat in H44.
  rewrite <- addition_trans in H44.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'25++($ SLOT_NULL_CAP,($0,(($0, i17), Vnull)))::v'26))
  in H44; eauto.
  sep lifts (5::4::9::3::nil)%nat in H44.
  sep lift 4%nat in H44.
  change ($ 4 +ᵢ  $ 4) with ($8) in H44.
  rewrite Int.add_assoc in H44 at 1.
  change ($ 4 +ᵢ  $ 8) with ($12) in H44.
  sep lift 4%nat  in H44.
  rewrite <- addition_trans in H44 at 1.
  rewrite <- addition_trans in H44 at 1.
  rewrite <- addition_trans in H44 at 1.
  rewrite Z2Nat.id in H44. rewrite Int.unsigned_repr in H44.
  
  sep lifts (3::4::1::2::nil)%nat in H44.
  eapply fold_Cap in H44.
  sep lifts (5::6::1::7::nil)%nat in H44.
  rewrite <- addition_trans in H44.
  2: lia.
  2: auto.
  2: {
    clear -H34 H33.
    unfold OBJ_POSITION in *.
    rewrite max_unsigned_val. 
    int auto.
  }
  2:{
    clear -H34 H33.
    unfold OBJ_POSITION in *.
    int auto.
  }
  2: lia.
  2: lia.
  2: lia.
  eapply ASlots_fold_any_idx_frm with
  (slotsvl := (v'16++(v'19,($CAP_OBJECT_TYPE,((i16, i20), v1)))::v'17)) 
  in H44; eauto.
  
  sep lifts (8::6::9::nil)%nat in H44.
  eapply Aarray'_fold_any_idx_frm in H44; eauto.
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    assert(Z.to_nat (Int.unsigned v'28) < 64)%nat. lia.
    simpl typelen. 
    apply Z.le_trans with(m:= 64*4). simpl typelen.
    rewrite Nat2Z.inj_mul.
    clear -H61.
    lia.
  Optimize Proof.
  Optimize Heap.
    rewrite max_unsigned_val. lia. 
  }
  2:{
    simpl. rewrite max_unsigned_val. lia.
  }
  sep lifts (1::7::8::nil)%nat in H44.
  eapply Aarray'_fold_any_idx_frm in H44; eauto.
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
    
    rewrite S_add_sub_S.
    eapply le_plus_minus_r.
    clear -Hc1.
    lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (15::16::2::nil)%nat in H44.
  eapply fold_Acnode in H44; eauto.
  sep lifts (8::9::3::nil)%nat in H44.
  eapply fold_Acnode in H44; eauto.

  sep lifts (1::8::9::10::11::nil)%nat in H44.
  eapply fold_ACSpace in H44; eauto.
  sep lifts (2::9::10::11::12::nil)%nat in H44.
  eapply fold_ACSpace in H44; eauto.
  sep lifts (7::2::8::nil)%nat in H44.

  eapply ACSpaceAarray_fold_any_idx_frm in H44; eauto.
  2: clear -Hv'4range; lia. 
  2:{
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl. 
    rewrite H4, H7.
    rewrite S_add_sub_S.
    eapply le_plus_minus_r.
    clear -Hc1.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (1::2::7::nil)%nat in H44.
  eapply ACSpaceAarray_fold_any_idx_frm 
  with(cspacevl:=(v'15 ++
  (i5, i6,
  v'25 ++
  ($ SLOT_NULL_CAP, ($ 0, ($ 0, i17, Vnull)))
  :: v'26, i0, l, v, i) :: v'20) ++
 (i7, i8,
 v'16 ++
 (v'19, ($ CAP_OBJECT_TYPE, (i16, i20, v1)))
 :: v'17, i3, l0, v0, i2) :: v'21)
  in H44; eauto.
  2: lia. 
  2:{
    rewrite app_length.
    simpl.
    rewrite app_length. simpl.
    rewrite H4, H7, H9. 
    rewrite S_add_sub_S.
    rewrite S_add_sub_S.
    clear -Hc1 Hv'4range. lia.
    clear -Hv'4range.
    lia. 
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
    rewrite app_length.
    simpl.
    rewrite H4, H7.
    rewrite S_add_sub_S.
    clear -Hc1.
    lia. 
  Optimize Proof.
  Optimize Heap.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }

  unfold AOSCSpacePrioTbl. 
  sep normal. sep eexists. auto.
  sep lift 20%nat.
  eapply disj_split. right.
  sep normal. sep eexists.
  sep lift 4%nat. eapply disj_split.
  right.
  eapply disj_split. right.
  sep normal. sep eexists.
  sep lift 3%nat. eapply disj_split.
  right.
  sep normal.
  unfold GetObjSlotRetval.
  sep lift 7%nat. 
  eapply disj_split. left.
  sep lift 2%nat. 
  eapply disj_split. right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  left.
  sep cancel OSCSpacePrioTbl. 
  sep cancel ACSpaceAarrayTptr.
  unfold Aarray. 
  sep cancel Aarray'. 
  sep cancel Aop. sep cancel Aie. sep cancel Aier. sep cancel Aisr. sep cancel Acs.
  sep cancel Ais. sep cancel A_dom_lenv. sep auto.

  sep normal. sep eexists. sep split; eauto.
  rewrite app_assoc_reverse. auto.
  splits; try (rewrite app_length); try (rewrite app_length); simpl.
  rewrite H1, H10, H11.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S.
  clear -Hc1 Hv'4range. lia.
  clear -Hv'4range. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  rewrite H38, H7, H9. 
  rewrite S_add_sub_S.
  rewrite S_add_sub_S.
  clear -Hc1 Hv'4range. lia.
  clear -Hv'4range. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  
  rewrite app_assoc_reverse. auto.
  rewrite <- H54.
  rewrite list_trans_1.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  rewrite app_length. simpl.
  rewrite H4, H7. rewrite S_add_sub_S.
  clear -Hc1. lia.
  clear -Hc1. 
  eapply Z2Nat.inj_lt; (int auto).
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  splits.
  rewrite app_assoc_reverse. auto.
  rewrite app_assoc_reverse. auto. 

  clear -H12.
  unfold val_inj, bop_eval in H12.
  unfold val_eq in H12.
  destruct (Int.eq i15 ($ CAP_OBJECT_TYPE)) eqn: Heqn.
  eapply Inteq_true_is_Zeq in Heqn.
  rewrite Int.unsigned_repr in Heqn.
  auto.
  unfold CAP_OBJECT_TYPE. rewrite max_unsigned_val. lia.
  tryfalse.
  instantiate (2:= Some(V$ (v'7+OBJ_POSITION))).
  unfold val_inj.
  unfold Vint32_inj.
  rewrite Int.unsigned_repr.
  2:{
    rewrite max_unsigned_val.
    clear -H33 H34.
    unfold OBJ_POSITION in *. lia.
  }
  
  {
  unfold update_nth_cspace_slots_cap at 2.
  rewrite app_assoc.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  2:{
    rewrite app_length.
    simpl. 
    rewrite H4, H7.
    clear -Hc1. rewrite S_add_sub_S.
    lia.
  Optimize Proof.
  Optimize Heap.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }

  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  2:{
    rewrite app_length.
    simpl. 
    rewrite H4, H7.
    clear -Hc1. rewrite S_add_sub_S.
    lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  rewrite app_assoc_reverse.
  rewrite app_assoc_reverse.
  unfold update_nth_cspace_slots_cap.
  
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  simpl.
  rewrite update_nth_list_length_imp; eauto.
  unfold update_nth_cspace_slots_type.
  rewrite nth_cspace_length_imp; eauto.
  rewrite nth_slots_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  rewrite update_nth_list_length_imp; eauto.
  }
  clear -H33 H34.
  unfold val_inj, Vint32_inj.
  unfold OBJ_POSITION in *. unfold SLOT_NULL_CAP. int auto.
  eauto.
  splits; eauto. eauto.
  eauto. eauto. eauto.
  rewrite app_length. simpl.
  rewrite H37, H41. rewrite S_add_sub_S.
  clear -Hc1. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; (int auto).
  rewrite app_length. simpl.
  rewrite H52, H58. rewrite S_add_sub_S.
  clear -Hv'6range. unfold SLOT_NUM in *.
  lia.
  clear -Hv'6range.
  unfold SLOT_NUM in *. lia.
  rewrite app_length. simpl.
  rewrite H55, H57. rewrite S_add_sub_S.
  clear -H34. unfold SLOT_NUM. lia.
  unfold SLOT_NUM. 
  clear -H34 H33. 
  assert(Z.to_nat (v'7 + OBJ_POSITION) < Z.to_nat 255)%nat. 
  eapply Z2Nat.inj_lt; (int auto).
  unfold OBJ_POSITION in *. lia.
  lia.
  clear -H33 H34.
  unfold OBJ_POSITION in *. int auto.
  unfold SLOT_NUM. lia.
  rewrite app_length. simpl.
  rewrite H55, H57. rewrite S_add_sub_S.
  clear -H34. unfold SLOT_NUM. lia.
  unfold SLOT_NUM. 
  clear -H34 H33. 
  assert(Z.to_nat (v'7 + OBJ_POSITION) < Z.to_nat 255)%nat. 
  eapply Z2Nat.inj_lt; (int auto).
  unfold OBJ_POSITION in *. lia.
  lia.
  clear -Hv'6range. unfold SLOT_NUM in *. lia.
  rewrite app_length. simpl.
  rewrite H52, H58. rewrite S_add_sub_S.
  clear -Hv'6range. unfold SLOT_NUM in *.
  lia.
  clear -Hv'6range.
  unfold SLOT_NUM in *. lia.
  lia. unfolds. auto.
  lia.
Qed.