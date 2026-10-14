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
Lemma ucosCNodeCopyPart1_2proof:
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
        (Z.to_nat (Int.unsigned v'28)) v'36 =
      Vint32 v'4)
(H23: nth_val'
        (Z.to_nat (Int.unsigned v'28))
        ((v'22 ++ Vptr (b, i1) :: v'23) ++
         Vptr (b0, i4) :: v'24) <> Vnull)
(v'7: list slot_val_type)
(v'8: list slot_val_type)
(v'11: list slot_val_type)
(H25: get_slots
        (Z.to_nat (Int.unsigned v'28))
        (v'17 ++
         (i5, i6,
         v'25 ++
         (v'27, (i9, (i10, i11, v'29)))
         :: v'26, i0, l, v, i)
         :: v'20 ++
            (i7, i8,
            v'13 ++
            (v'18, (i12, (i13, i14, v2)))
            :: v'14, i3, l0, v0, i2) :: v'21) =
      Some (v'7 ++ v'8 ++ v'11))
(H26: length v'7 = Z.to_nat OBJ_POSITION)
(H27: length (v'7 ++ v'8) =
      Z.to_nat (Int.unsigned v'4))
(H28: Slots_neq_object v'8 v'29), 
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
(priotbl priotbl' : list cspace_val_type)
(cspacels : CSpaceptr2prioMod.map)
(pointervl : vallist)
(pointervl' : list val)
(captype_val categorycontent_val
categoryright_val : int32)
(categoryobject_val : val)
(origin_right : int32)
(origin_object : val),
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
AOSCSpacePrioTbl (b1, i15) ptrvl priotbl'
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
            (v'18, (i12, (i13, i14, v2)))
            :: v'14, i3, l0, v0, i2)
            :: v'21) 
          :: logic_lv v'36
            :: logic_code v'31
                :: logic_abscap v'39
                ::logic_lv
                (v'22 ++
                 (Vptr
                 (b ↝ {i1})
                 :: v'23) ++
                 Vptr
                 (b0 ↝ {i4})
                 :: v'24)
                  :: nil =
logic_cs cs
:: logic_isr isr
    :: logic_ier er
      :: logic_cspacel priotbl
          :: logic_lv pointervl
            :: logic_code s
                :: logic_abscap cspacels
                ::logic_lv ptrvl
                  :: nil|] **
p_local OSLInv ct init_lg **(
  [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl = Vnull \/
  nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl = Vnull|] ** [|v1 = Some(Vint32(Int.repr CNODE_COPY_FAILURE))/\priotbl' = priotbl /\ pointervl' = pointervl|] \\//
  ([|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) ptrvl <> Vnull /\
  nth_val' (Z.to_nat(Int.unsigned srcTask_Prio)) ptrvl <> Vnull|] **
  [|get_capability (Z.to_nat(Int.unsigned srcTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) 
  priotbl = Some(captype_val, (categorycontent_val, categoryright_val, categoryobject_val))|] **
  (
  ([|(Int.unsigned captype_val <> CAP_CATEGORY_TYPE) /\ (Int.unsigned captype_val <> CAP_OBJECT_TYPE)|]
  ** [|v1 = Some(Vint32 ($CNODE_COPY_FAILURE))|]
  ** [|priotbl' = priotbl /\ pointervl' = pointervl|]) \\//(
  [|(Int.unsigned captype_val = CAP_CATEGORY_TYPE)|] **
  [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat(Int.unsigned func_capability)) priotbl
  ($CAP_CATEGORY_TYPE , (categorycontent_val, categoryright_val, origin_object)))|] ** 
  [|pointervl' = pointervl|] ** [|v1 = Some(Vint32 ($CNODE_NONE_FAULT))|]
  ) \\// ([|(Int.unsigned captype_val = CAP_OBJECT_TYPE)|] **
    (EX idxval idxz,
    GetObjSlotRetval destTask_Prio ptrvl pointervl priotbl categoryobject_val idxval **
    [|idxz =Int.unsigned(Vint32_inj (val_inj idxval))|]**(
     [|idxz = SLOT_NULL_CAP|] ** (
      EX pointeridx, 
      [|nth_val' (Z.to_nat(Int.unsigned destTask_Prio)) pointervl = (Vint32 pointeridx)|] **
      (([|Int.unsigned pointeridx >= 255|] ** [|v1 = Some(Vint32 ($SLOT_RANGE_OVERFLOW)) /\ priotbl' = priotbl /\
      pointervl' = pointervl|])\\//
      ([|Int.unsigned pointeridx < 255|] **  [|v1 = Some(Vint32 ($CNODE_NONE_FAULT))|] **
      [|pointervl' = update_nth_val (Z.to_nat(Int.unsigned destTask_Prio)) pointervl (Vint32 (Int.add pointeridx (Int.repr 1)))|] **
      [|priotbl' = (update_nth_cspace_slots_cap (Z.to_nat(Int.unsigned destTask_Prio)) (Z.to_nat (Int.unsigned pointeridx)) priotbl
      ($CAP_OBJECT_TYPE , (categorycontent_val, origin_right, categoryobject_val)))|])))
       \\//[|idxz <> SLOT_NULL_CAP|] **(
      [|v1 = Some(Vint32 ($CNODE_NONE_FAULT))|] **
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
   (v'27, (i9, (i10, i11, v'29))) :: v'26, i0,
   l, v, i)
   :: v'20 ++
      (i7, i8,
      v'13 ++
      (v'18, (i12, (i13, i14, v2))) :: v'14,
      i3, l0, v0, i2) :: v'21) v'39 **
AOSCSpaceObjectPointer v'36 **
p_local OSLInv ct init_lg **
LV idx @ Tint32 |-> (V$ SLOT_NULL_CAP) **
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
                        RETURN 〈 char_t 〉 ′ CNODE_NONE_FAULT {{Afalse}}.
Proof.
  intros.
  rename H20 into Ha.
  rename H23 into H20.
  rename H25 into Hb.
  rename H26 into Hc.
  rename H27 into Hd.
  rename H28 into He.
  unfold AOSCSpaceObjectPointer.
  pure intro.
  assert(Z.to_nat(Int.unsigned v'28) < 64)%nat. 
  clear -Hv'4range.
  lia.
  
  lets Hexists: nthval'_has_value_Tint32 H23 H25 H27.
  destruct Hexists. 
  destruct H28.
  assert(x = v'4).
  rewrite H28 in Ha.
  inverts Ha. auto.
  subst v'4.
  assert(Int.unsigned x <= 255).
  clear -Hv'4range H25 H26 H28.
  assert((0 <= Z.to_nat (Int.unsigned v'28) < length v'36)%nat) by lia.

  unfold objectpointer in H26.
  eapply inline_bittblfunctions.nth_val'2nth_val in H28.
  lets Htmp: H26 H H28.
  lia. 
  rename H30 into Hxle255.
  eapply seq_rule.

  eapply ift_rule'.
  intros.
  eapply bop_rv.
  sep get rv.
  destruct_s s. unfold SLOT_NULL_CAP.
  simpl. split; eauto.
  eauto.
  
  unfold val_inj, bop_eval, val_eq. 
  destruct (Int.eq ($ SLOT_NULL_CAP)($ 0)); auto.
  simpl. eauto.

  Ltac p_local_go:= 
    try unfold p_local;
    try unfold CurTid;
    try unfold OSLInv;
    try unfold LINV;
    try unfold AOSCSpacePrioTbl;
    try unfold AOSExchandler;
    try good_frm_sovler;
    try go.

  (*idx ′ =ₑ OSCSpaceObjectPointer ′ [destTask_Prio ′];ₛ*)
  hoare forward.
  rewrite Hv'4. auto.
  simpl. rewrite H28. auto.
  rewrite H28.
  (*If (idx ′ ≥ ′ SLOT_NUM)
{RETURN ′ SLOT_RANGE_OVERFLOW};ₛ*)
  hoare forward.
  unfold SLOT_NUM.
  destruct (Int.ltu ($ 255) x); auto.
  destruct (Int.eq x ($ SLOT_NUM)); auto.
  destruct (Int.ltu ($ SLOT_NUM) x);
  destruct (Int.eq x ($ SLOT_NUM)); auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  sep get rv.
  intros. sep normal. sep eexists.
  sep lift 17%nat. 
  eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 3%nat. 
  eapply disj_split.
  right.
  eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 3%nat. 
  eapply disj_split.
  left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  left. 
  sep normal. sep eexists.
  unfold GetObjSlotRetval.
  sep lift 5%nat. 
  eapply disj_split. left.
  sep lift 2%nat. 
  eapply disj_split. right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split. right.
  sep auto.
  rewrite app_assoc_reverse. auto.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  splits; rewrite app_assoc_reverse; auto.
  1:{
    clear -H12.
    unfold val_inj, bop_eval, val_eq in H12.
    destruct (Int.eq i9 ($ CAP_OBJECT_TYPE)) eqn: Heq; tryfalse.
    rewrite Inteq_true_is_Zeq in Heq.
    rewrite Int.unsigned_repr in Heq.
    auto. unfold CAP_OBJECT_TYPE. rewrite max_unsigned_val.
    lia.
  }
  pauto.
  eauto.
  {
    clear -H31.
    unfold val_inj, bool_or, val_eq in H31.
    destruct H31.
    unfold SLOT_NUM in H.
    clear -H.
    destruct (Int.ltu ($ 255) x) eqn: Hlt;
    destruct (Int.eq x ($ 255))eqn: Heq;
    repeat(val_help_H H; simpl in H); tryfalse;
    try(rewrite Intlt_true_is_Zlt in Hlt);
    try(rewrite Inteq_true_is_Zeq in Heq);
    try(rewrite Int.unsigned_repr in Hlt);
    try(rewrite Int.unsigned_repr in Heq);
    try rewrite max_unsigned_val; try lia.
  }
  eapply H28.
  eauto. eauto. eauto. eauto.
  eapply disj_rule.
  hoare_split_pure_all. 
  eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hxlt255: Int.unsigned x < 255).
  {
    clear -H31.
    unfold val_inj, bool_or, val_eq in H31. 
    unfold SLOT_NUM in H31.
    destruct (Int.ltu ($ 255) x) eqn: Hlt;
    destruct (Int.eq x ($ 255))eqn: Heq;
    repeat(val_help_H H31; simpl in H31); destruct H31;tryfalse;
    try(rewrite Intlt_false_is_Zge in Hlt);
    try(rewrite Inteq_false_is_Zneq in Heq);
    try(rewrite Int.unsigned_repr in Hlt);
    try(rewrite Int.unsigned_repr in Heq);
    try rewrite max_unsigned_val; try lia.
  }
  clear H30 H31.
  rewrite Int.add_zero.
  instantiate(1:=<|| v'31 ||>  **
  A_dom_lenv
    ((func_capability, Tint32)
     :: (srcTask_Prio, Tint8)
        :: (destTask_Prio, Tint8)
           :: (idx, Tint32)
              :: (pCSpace1, Tptr CSPACE)
                 :: (pCSpace2, Tptr CSPACE)
                    :: (cap1, Tptr Cap)
                       :: (cap2, Tptr Cap) :: nil) **
  GAarray OSCSpaceObjectPointer (Tarray Tint32 64)
    (update_nth_val (Z.to_nat (Int.unsigned v'28))
       v'36
       (val_inj
          (add
             (nth_val'
                (Z.to_nat (Int.unsigned v'28))
                v'36) (V$ 1) Tint32 Tint32))) **
  LV idx @ Tint32 |-> Vint32 x **
  Aie false **
  Ais nil **
  Acs v'32 **
  Aisr v'33 **
  Aier v'30 **
  AOSCSpacePrioTbl (v'34, v'35)
    ((v'22 ++ Vptr (b, i1) :: v'23) ++
     Vptr (b0, i4) :: v'24)
    (v'17 ++
     (i5, i6,
     v'25 ++
     (v'27, (i9, (i10, i11, v'29))) :: v'26, i0,
     l, v, i)
     :: v'20 ++
        (i7, i8,
        v'13 ++
        (v'18, (i12, (i13, i14, v2))) :: v'14, i3,
        l0, v0, i2) :: v'21) v'39 **
  p_local OSLInv ct init_lg **
  LV cap2 @ Tptr Cap
  |-> Vptr
        (b,
        ((i1 +ᵢ  $ 8) +ᵢ
         Int.mul ($ Z.of_nat 20)
           ($
            Z.of_nat (Z.to_nat (Int.unsigned v'6))))
        +ᵢ  $ 4) **
  LV cap1 @ Tptr Cap
  |-> Vptr
        (b0,
        (((i4 +ᵢ  Int.zero) +ᵢ  $ 8) +ᵢ
         Int.mul ($ Z.of_nat 20)
           ($
            Z.of_nat (Z.to_nat (Int.unsigned v'6))))
        +ᵢ  $ 4) **
  LV pCSpace2 @ Tptr CSPACE |-> Vptr (b, i1) **
  LV pCSpace1 @ Tptr CSPACE |-> Vptr (b0, i4) **
  LV func_capability @ Tint32 |-> Vint32 v'6 **
  LV srcTask_Prio @ Tint8 |-> Vint32 v'5 **
  LV destTask_Prio @ Tint8 |-> Vint32 v'28 ** [|Int.unsigned x < 255|]).
  hoare forward.
  rewrite Hv'4. auto.
  rewrite H28. auto.
  rewrite H28. 
  unfold val_inj, add. auto.
  rewrite Hv'4. auto.
  eapply disj_rule.
  2:{
    hoare_split_pure_all.
    false.
    unfold val_inj, bop_eval, val_eq in H30.
    unfold SLOT_NULL_CAP in H30.
    rewrite Int.eq_true in H30.
    destruct H30; tryfalse.
  }
  hoare_split_pure_all.
  rename H30 into Hxlt255.
  (*这里需要展开AOSCSPrioTbl*)
  eapply backward_rule1.
  intros.
  sep lift 10%nat in H30.
  eapply AOSCSpacePrioTbl_unfold_any_two_idx_frm with (idx1:=Z.to_nat(Int.unsigned v'28)) (idx2:=Z.to_nat(Int.unsigned v'5))in H30; eauto.
  unfold AOSCSpacePrioTbl in H30. sep split in H30.
  rewrite Hv'14len. lia.
  clear -Hc1. 
  eapply Z2Nat.inj_lt; try (int auto).
  clear -Hnotnull2. rewrite app_assoc_reverse.
  simpl in *. auto.
  hoare_split_pure_all.
  simpljoin.
  (*变量一一对应*)
  eapply list_map_eq5 in H30.
  destruct H30. subst v'22.
  destruct H38. inverts H30.
  destruct H38. subst v'23.
  destruct H38. inverts H38. inverts H30.
 
  eapply eq_sym in H31.
  rewrite list_trans_1 in H31.
  eapply list_map_eq5 in H31.
  destruct H31. subst v'17.
  destruct H31. subst v'12.
  destruct H31. subst v'20.
  destruct H31. subst v'15.
  subst v'21.
  2:{
    rewrite H4, H33. auto.
  }
  2:{
    rewrite H7, H34. auto.
  }
  2:{
    rewrite H9, H35. auto.
  }
  2:{
    rewrite H1, H32. auto.
  }
  2:{
    rewrite H10, H36. auto.
  }
  2:{
    rewrite H11, H37. auto.
  }



  unfold ACSpace.

  unfold Acnode.
  pure intro.
  rename H47 into Hi2range.
  rename H48 into Hirange'.
  (*unfold two slots*)
  eapply backward_rule1.
  intros.
  sep lifts (10::18::nil)%nat in H39.
  eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned v'6)) in H39.
  sep lift 2%nat in H39.
  eapply ASlots_unfold_any_idx_frm with(idx:=Z.to_nat(Int.unsigned x)) in H39.
  exact H39.
  clear -Hxlt255.
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
  destruct v'20. destruct c. destruct p.
  destruct v'24. destruct c. destruct p.
  pure intro.
  rewrite H49 in *.
  rewrite H39 in *.
  eapply list_map_eq3 in H39.
  destruct H39. subst v'25.
  destruct H56. inverts H39. 
  subst v'26.
  2:{
    rewrite H47, H0. auto.
  }
  2:{
    rewrite H53, H16. auto.
  }
  (*cap1 ′ =ₑ&ₐ(((pCSpace1 ′ → cnode) .. slots) [idx ′])
            .. capability;ₛ*)
  hoare_lifts_trms_pre(Aop).
  eapply seq_rule.
  eapply assign_rule_lvar.
  split; intros.
  sep_lifts_trms_in H39 (Alvarmapsto cap1).
  exact H39.
  intros. sep auto.
  intros.
  eapply calculate_rv_expr_id_addr.

  3:{
    eapply expr_field_array_asrt_impl_frm.
    5:{
      eapply local_val_struct_member_addr_frm.
      4:{
        sep split in H39.
        sep cancel pCSpace1.
        sep_lifts_trms_in H39 (Alvarmapsto idx).
        eapply LV_to_Rv in H39; eauto.
        rewrite H28  in H39.
        instantiate(2:=Z.to_nat(Int.unsigned x)).
        rewrite of_to_nat_unsignedv'. rewrite Int.repr_unsigned.
        exact H39.
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
    exact H39.
    unfold Cap. eauto.
    unfold field_offset. simpl. eauto.
    simpl. eauto.
  }
  2:{
    split; intros. simpl typelen in *.
    rewrite Int.add_zero.
    rewrite Int.add_zero.
    rewrite of_to_nat_unsignedv'.
    rewrite Int.repr_unsigned.
    sep lift 11%nat in H39.
    rewrite <- addition_trans.
    exact H39.
    lia.
    intros.
    rewrite Int.add_zero in *.
    rewrite Int.add_zero in *.
    simpl typelen in *.
    rewrite of_to_nat_unsignedv' in H39 at 1.
    rewrite <- addition_trans in H39 at 1. 
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
    rewrite Int.unsigned_repr in H39 at 1.
    sep auto.
    clear -Hxlt255. rewrite max_unsigned_val. 
    splits. int auto. lia. lia.
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
        sep lift 2%nat in H39.
        exact H39.
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
  sep lift 12%nat in H39.
  rewrite <- addition_trans.
  rewrite Int.add_zero.
  exact H39. lia.
  simpl typelen in *.
  rewrite Int.add_zero in *.
  rewrite Int.add_zero in *.
  sep cancel cap2.
  sep cancel cap1.
  sep cancel ASlots.
  rewrite of_to_nat_unsignedv'.
  rewrite <- addition_trans.
  rewrite Int.unsigned_repr.
  rewrite <- addition_trans in H39.
  rewrite Int.unsigned_repr in H39.
  rewrite of_to_nat_unsignedv' in H39.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  rewrite Int.add_zero in H39.
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
          sep_lifts_trms_in H39 (Alvarmapsto cap2).
          exact H39.
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
    sep lift 6%nat in H39.
    unfold Aptrmapsto in H39 at 1.
    exact H39.
    clear -H9. int auto.
    lia.
  Optimize Proof.
  Optimize Heap.
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
        sep lift 3%nat in H39.
        exact H39.
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
  sep lift 14%nat in H39.
  rewrite <- addition_trans.
  change ($ 4 +ᵢ  $ 4) with ($8).
  rewrite Int.add_assoc.
  change ($ 4 +ᵢ  $ 8) with ($12).
  exact H39. lia.
  simpl typelen in *.
  rewrite Int.add_zero in *.
  rewrite Int.add_zero in *.
  sep cancel cap2.
  sep cancel cap1.
  sep cancel ASlots.
  rewrite of_to_nat_unsignedv'.
  rewrite <- addition_trans.
  rewrite Int.unsigned_repr.
  rewrite <- addition_trans in H39.
  rewrite Int.unsigned_repr in H39.
  rewrite of_to_nat_unsignedv' in H39.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 2%nat 1%nat.
  change ($ 4 +ᵢ  $ 4) with ($8) in H39.
  rewrite Int.add_assoc in H39 at 1.
  change ($ 4 +ᵢ  $ 8) with ($12) in H39.
  sep cancel 1%nat 3%nat.
  do 37(try (sep cancel 1%nat 1%nat)). auto.
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
          sep_lifts_trms_in H39 (Alvarmapsto cap2).
          exact H39.
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
    sep lift 9%nat in H39.
    unfold Aptrmapsto in H39 at 1.
    change ($ 4 +ᵢ  $ 4) with ($8).
    rewrite Int.add_assoc.
    change ($ 4 +ᵢ  $ 8) with ($12).
    exact H39.
    clear -H9. int auto.
    lia.
  }
    simpl. auto.
    clear -H54.
    unfold isptr in *.
    destruct H54. subst v3. auto.
    destruct H. subst v3. auto.
  }
  eapply eq_vptr. eauto.
  intros.
  eexists. sep cancel p_local. simpl. auto.

  (*RETURN 〈 char_t 〉 ′ CNODE_NONE_FAULT*)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl. split; eauto.
  intros.

  (*fold_ACSpaceAarray*)
  sep lifts (8::9::10::11::nil)%nat in H39.
  eapply fold_Cap in H39.
  sep lifts (7::8::1::9::nil)%nat in H39.
  eapply ASlots_fold_any_idx_frm with(slotsvl := (v'21++(v'23,(i18,((i19, i20), v3)))::v'22))
  in H39; eauto.
  sep lifts (5::4::9::3::nil)%nat in H39.
  rewrite Int.add_zero in H39.
  rewrite Int.add_zero in H39.
  rewrite Int.add_zero in H39.
  sep lift 4%nat in H39.
  change ($ 4 +ᵢ  $ 4) with ($8) in H39.
  rewrite Int.add_assoc in H39 at 1.
  change ($ 4 +ᵢ  $ 8) with ($12) in H39.
  sep lift 4%nat  in H39.
  rewrite addition_trans in H39 at 1.
  rewrite of_to_nat_unsignedv' in H39. rewrite Int.repr_unsigned in H39.
  rewrite of_to_nat_unsignedv' in H39. rewrite Int.repr_unsigned in H39.
  sep lifts (3::4::1::2::nil)%nat in H39.
  eapply fold_Cap in H39.
  sep lifts (5::6::1::7::nil)%nat in H39.
  rewrite <- addition_trans in H39.
  2: lia. 
  2: auto.
  2: lia.
  eapply ASlots_fold_any_idx_frm with(idx:= Z.to_nat(Int.unsigned x))
  (slotsvl := (v'12++(v'17,($CAP_OBJECT_TYPE,((i19, i17), v3)))::v'15)) 
  in H39; eauto.

  sep lifts (8::6::9::nil)%nat in H39.
  eapply Aarray'_fold_any_idx_frm in H39; eauto.
  2:{
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  }
  2:{
  assert(Z.to_nat (Int.unsigned v'28) < 64)%nat. lia.
  simpl typelen. 
  apply Z.le_trans with(m:= 64*4). simpl typelen.
  rewrite Nat2Z.inj_mul.
  clear -H56.
  lia.
  rewrite max_unsigned_val. lia. 
  }
  2:{
  simpl. rewrite max_unsigned_val. lia.
  }
  sep lifts (1::7::8::nil)%nat in H39.
  eapply Aarray'_fold_any_idx_frm in H39; eauto.
  2:{
  simpl. rewrite max_unsigned_val. lia.
  }
  2:{
  simpl. rewrite max_unsigned_val. lia.
  }
  2:{
    splits; auto. 
    rewrite app_length.
    simpl. rewrite H1, H10.
    rewrite S_add_sub_S.
    eapply le_plus_minus_r.
    clear -Hc1.
    lia.
  Optimize Proof.
  Optimize Heap.
    clear -Hc1.
    eapply Z2Nat.inj_lt; try (int auto).
  }
  sep lifts (15::16::2::nil)%nat in H39.
  eapply fold_Acnode in H39; eauto.
  sep lifts (8::9::3::nil)%nat in H39.
  eapply fold_Acnode in H39; eauto.

  sep lifts (1::8::9::10::11::nil)%nat in H39.
  eapply fold_ACSpace in H39; eauto.
  sep lifts (2::9::10::11::12::nil)%nat in H39.
  eapply fold_ACSpace in H39; eauto.
  sep lifts (7::2::8::nil)%nat in H39.

  eapply ACSpaceAarray_fold_any_idx_frm in H39; eauto.
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
  sep lifts (1::2::7::nil)%nat in H39.
  eapply ACSpaceAarray_fold_any_idx_frm 
  with(cspacevl:=(v'4 ++
  (i5, i6,
  v'21 ++
  (v'23, (i18, (i19, i20, v3))) :: v'22, i0,
  l, v, i) :: v'16) ++
 (i7, i8,
 v'12 ++
 (v'17, ($ CAP_OBJECT_TYPE, (i19, i17, v3)))
 :: v'15, i3, l0, v0, i2) :: v'19)in H39; eauto.
  2: lia. 
  2:{
  rewrite app_length.
  rewrite app_length.
  simpl.
  
  rewrite H33, H34, H35. 
  rewrite S_add_sub_S.
  rewrite S_add_sub_S.
  clear -Hc1 Hv'4range.
  lia. 
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
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  }

  unfold AOSCSpacePrioTbl. 
  sep normal. sep eexists. auto.
  sep lift 20%nat.
  eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 3%nat. 
  eapply disj_split.
  right.
  eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 3%nat. 
  eapply disj_split.
  left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. 
  unfold GetObjSlotRetval.
  sep lift 7%nat. 
  eapply disj_split. left.
  sep lift 2%nat. 
  eapply disj_split. right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split. right.
  sep normal. sep eexists.
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
  rewrite H33, H34, H35.
  rewrite S_add_sub_S.
  rewrite S_add_sub_S.
  clear -Hc1 Hv'4range. lia.
  clear -Hv'4range. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; try (int auto).
  
  rewrite app_assoc_reverse. auto.
  splits.
  eapply array_type_vallist_match_hold; auto.
  rewrite H25. auto.
  simpl.   unfold val_inj. unfold add.
  rewrite H28. auto.
  rewrite H28. auto.
  rewrite <- H25. eapply update_nth_val_len_eq.
  rewrite H28.
 
  eapply objectpointer_add_1_keep; eauto.
  rewrite H25. lia.
  rewrite get_capability_nth_mth_cspace_length_imp; eauto.
  splits.
  rewrite app_assoc_reverse. auto.
  rewrite app_assoc_reverse. auto. 

  clear -H12.
  unfold val_inj, bop_eval in H12.
  unfold val_eq in H12.
  destruct (Int.eq i18 ($ CAP_OBJECT_TYPE)) eqn: Heqn.
  eapply Inteq_true_is_Zeq in Heqn.
  rewrite Int.unsigned_repr in Heqn.
  auto.
  unfold CAP_OBJECT_TYPE. rewrite max_unsigned_val. lia.
  tryfalse.
  unfold val_inj. auto.
  eauto.
  
  {
    unfold update_nth_cspace_slots_cap.
    rewrite app_assoc.
    rewrite nth_cspace_length_imp; eauto.
    rewrite nth_slots_length_imp; eauto.
    
    rewrite update_nth_list_length_imp; eauto.
    rewrite update_nth_list_length_imp; eauto.
    rewrite app_length. simpl.
    rewrite H4, H7.
    rewrite S_add_sub_S.
    clear -Hc1. lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; (int auto).
    rewrite app_length. simpl.
    rewrite H4, H7.
    rewrite S_add_sub_S.
    clear -Hc1. lia.
    clear -Hc1.
    eapply Z2Nat.inj_lt; (int auto).
  }
  rewrite H28. unfold val_inj, add. auto.
  lia.
  all: eauto.
  rewrite app_length. simpl.
  rewrite H32, H36. rewrite S_add_sub_S.
  clear -Hc1. lia.
  clear -Hc1.
  eapply Z2Nat.inj_lt; (int auto).
  rewrite app_length. simpl.
  rewrite H50, H52. rewrite S_add_sub_S.
  clear -Hxlt255. unfold SLOT_NUM. lia.
  unfold SLOT_NUM. lia.
  clear -Hxlt255. unfold SLOT_NUM. lia.
  rewrite app_length. simpl.
  rewrite H50, H52. rewrite S_add_sub_S.
  clear -Hxlt255. unfold SLOT_NUM. lia.
  unfold SLOT_NUM. lia.
  clear -Hv'6range. unfold SLOT_NUM in *. lia.
  Unshelve.
  all: auto.
Qed.