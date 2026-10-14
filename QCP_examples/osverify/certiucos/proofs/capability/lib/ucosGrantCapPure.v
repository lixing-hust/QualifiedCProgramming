Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import include_frm.
Require Import sep_auto.
Require Import CapPure.
Require Import math_auto.
Require Import ACSpace_defs.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Set Implicit Arguments.
Notation "E '..' I" := (efield E I) (at level 10)  : code_scope.

  

Lemma cspace_to_capability_addr:
  forall 
  (ct: tid)
  (v': int32)
  (H3: Int.unsigned v' <= 255)
  (v'0: int32)
  (v'1: int32)
  (v'2: ier)
  (v'3: absop)
  (v'4: cs)
  (v'5: isr)
  (v'8: block)
  (v'9: int32)
  (v'10: CSpaceptr2prioMod.map)
  (v'14: vallist)
  (v'15: vallist)
  (b: block)
  (i1: int32)
  (v'11:  list cspace_val_type)
  (i2: int32)
  (i3: int32)
  (i0: int32)
  (l: list val)
  (v: val)
  (i: int32)
  (v'13: list cspace_val_type)
  (v'6: list (int32 * (int32 * cap_content_type)))
  (v'7: list (int32 * (int32 * cap_content_type)))
  (v'12: int32)
  (i4: int32)
  (i5: int32)
  (i6: int32)
  (v0: val)
  (s: RstateOP)
  (H: 
  s
    |= ASlots (b ↝ {i1 +ᵢ  $ 8})
         (Z.to_nat (Int.unsigned v'0)) v'6 **
       PV b
          ↝ {(i1 +ᵢ  $ 8) +ᵢ
             $
             Z.of_nat
               (Z.to_nat (Int.unsigned v'0) *
                typelen Slot)} @ long
       |-> Vint32 v'12 **
       PV b
          ↝ {((i1 +ᵢ  $ 8) +ᵢ
              $
              Z.of_nat
                (Z.to_nat
                   (Int.unsigned v'0) *
                 typelen Slot)) +ᵢ  
             $ 4} @ long |-> 
       Vint32 i4 **
       PV b
          ↝ {(((i1 +ᵢ  $ 8) +ᵢ
               $
               Z.of_nat
                 (Z.to_nat
                    (Int.unsigned v'0) *
                  typelen Slot)) +ᵢ  
              $ 4) +ᵢ  $ 4} @ long
       |-> Vint32 i5 **
       PV b
          ↝ {(((i1 +ᵢ  $ 8) +ᵢ
               $
               Z.of_nat
                 (Z.to_nat
                    (Int.unsigned v'0) *
                  typelen Slot)) +ᵢ  
              $ 4) +ᵢ  $ 8} @ long
       |-> Vint32 i6 **
       PV b
          ↝ {(((i1 +ᵢ  $ 8) +ᵢ
               $
               Z.of_nat
                 (Z.to_nat
                    (Int.unsigned v'0) *
                  typelen Slot)) +ᵢ  
              $ 4) +ᵢ  $ 12} @ 
       (Void) ∗ |-> v0 **
       [|isptr v0|] **
       ASlots
         (b
          ↝ {(i1 +ᵢ  $ 8) +ᵢ
             $
             Z.of_nat
               (S
                  (Z.to_nat
                     (Int.unsigned v'0)) *
                typelen Slot)})
         (Z.to_nat SLOT_NUM -
          S (Z.to_nat (Int.unsigned v'0)))
         v'7 **
       G& OSCSpacePrioTbl @
       Tarray CSPACE ∗ 64 == 
       (v'8 ↝ {v'9}) **
       PV v'8
          ↝ {v'9 +ᵢ
             $
             Z.of_nat
               (Z.to_nat (Int.unsigned v') *
                typelen CSPACE ∗)} @
       CSPACE ∗ |-> Vptr (b ↝ {i1}) **
       Aarray_rm (v'8 ↝ {v'9}) 64 
         CSPACE ∗
         (v'14 ++ Vptr (b ↝ {i1}) :: v'15)
         (Z.to_nat (Int.unsigned v')) **
       ACSpaceAarrayTptr
         (Z.to_nat (Int.unsigned v')) v'14
         v'11 v'10 **
       PV b ↝ {i1} @ long |-> Vint32 i2 **
       PV b ↝ {i1 +ᵢ  $ 4} @ long
       |-> Vint32 i3 **
       PV b
          ↝ {i1 +ᵢ
             $ Z.of_nat (typelen Cte)} @
       long |-> Vint32 i0 **
       Aarray
         (b
          ↝ {(i1 +ᵢ
              $ Z.of_nat (typelen Cte)) +ᵢ
             $ 4})
         (Tarray UNION cspace ⋆
            (Z.to_nat MaxChildNum)) l **
       PV b
          ↝ {((i1 +ᵢ
               $ Z.of_nat (typelen Cte))
              +ᵢ  $ 4) +ᵢ
             Int.mul ($ MaxChildNum)
               ($
                Z.of_nat
                  (typelen UNION cspace ⋆))} @
       CSPACE ∗ |-> v **
       PV b
          ↝ {(((i1 +ᵢ
                $ Z.of_nat (typelen Cte))
               +ᵢ  $ 4) +ᵢ
              Int.mul ($ MaxChildNum)
                ($
                 Z.of_nat
                   (typelen UNION cspace ⋆)))
             +ᵢ
             $ Z.of_nat (typelen CSPACE ∗)} @
       long |-> Vint32 i **
       ACSpaceAarrayTptr
         (64 -
          S (Z.to_nat (Int.unsigned v')))
         v'15 v'13 v'10 **
       Aier v'2 **
       Aie false **
       Ais nil **
       Acs v'4 **
       Aisr v'5 **
       p_local OSLInv ct init_lg **
       LV cap_Right @ long |-> Vint32 v'1 **
       LV cap_Class @ long |-> Vint32 v'0 **
       LV destTask_Prio @ char_t
       |-> Vint32 v' **
       A_dom_lenv
         ((cap_Right ↝ {long})
          :: (cap_Class ↝ {long})
             :: (destTask_Prio ↝ {char_t})
                :: nil)),
  s|=Lv ((((OSCSpacePrioTbl ′ [destTask_Prio ′])
  → cnode) .. slots) [cap_Class ′])
.. capability@ Cap == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4).
Proof.
    intros.
    sep normal in H.
    sep remember(9::29::10::28::nil)%nat in H.
    assert(s |= Lv OSCSpacePrioTbl ′ [destTask_Prio ′]→ cnode @ Cte == (b, i1) ** H0).
    rewrite <- Int.add_zero with (x := i1).
    eapply field_array_struct_impl_g_char_t.
    instantiate (1:=((cap_Right ↝ {long})
    :: (cap_Class ↝ {long})
       :: (destTask_Prio ↝ {char_t}) :: nil) ).
    simpl. auto.
    6:{   
      instantiate(3:=CSPACE ∗).
      unfold CSPACE. 
      eauto.
    }
    unfold field_offset. simpl.  auto.
    simpl. auto.
    3:{
      instantiate(1:=0%nat). 
      simpl. 
      auto.
    }
    instantiate (1:=Z.to_nat(Int.unsigned v')).
    rewrite ZifyInst.of_nat_to_nat_eq.
    assert(Int.unsigned v' >= 0). apply unsigned_ge0.
    rewrite Z.max_comm.
    assert(Z.max (Int.unsigned v') 0 = Int.unsigned v').
    eapply Zmax_left; eauto.
    rewrite H2. apply unsigned_ge0.
    rewrite ZifyInst.of_nat_to_nat_eq.
    assert(Int.unsigned v' >= 0). apply unsigned_ge0.
    rewrite Z.max_comm.
    assert(Z.max (Int.unsigned v') 0 = Int.unsigned v').
    eapply Zmax_left; eauto.
    rewrite H2. auto.
    {
      rewrite of_to_nat_unsignedv'.
      rewrite Int.repr_unsigned.
      assert($ Z.of_nat
      (Z.to_nat (Int.unsigned v') *
       typelen CSPACE ∗) = Int.mul ($ Z.of_nat (typelen CSPACE ∗)) v').
      simpl typelen.
      unfold Int.mul.
      assert(Z.of_nat (Z.to_nat (Int.unsigned v') * 4) = Int.unsigned($ Z.of_nat 4) * Int.unsigned v').
      rewrite Nat2Z.inj_mul.
      rewrite of_to_nat_unsignedv'.
      rewrite Int.unsigned_repr.
      rewrite Z.mul_comm. auto.
      rewrite max_unsigned_val. mauto.
      rewrite H1.  auto.
      rewrite H1 in H.
      sep cancel OSCSpacePrioTbl.
      sep cancel A_dom_lenv.
      sep cancel 2%nat 1%nat. 
      sep cancel 1%nat 1%nat. 
      auto.
    }
    subst H0.
    sep remember (1::26::nil)%nat in H1.
    assert(s |= Lv((((OSCSpacePrioTbl ′ [destTask_Prio ′]) → cnode) .. slots)
    [cap_Class ′])@Slot  == (b, (i1 +ᵢ  $ 8) +ᵢ 
    Int.mul ($ Z.of_nat (typelen Slot)) ($ Z.of_nat (Z.to_nat(Int.unsigned v'0)))) ** H0).
    eapply expr_field_array_asrt_impl_frm; eauto.
    4:{
      clear H.
      sep cancel H0.
      sep cancel 1%nat 1%nat. 
      destruct_s s.
      simpl.
      simpl in H1. simpljoin.
      rewrite H5.  splits; eauto.
      apply mapstoval_load in H6.
      apply join_emp_eq in H1. subst x1.
      rewrite of_to_nat_unsignedv'.
      rewrite Int.unsigned_zero in H6.
      rewrite Int.repr_unsigned.  auto.
      simpl. auto.
    }
    unfold field_offset. simpl. rewrite Int.add_zero.
    auto. instantiate(1:=2%nat). simpl. auto.
    simpl. eauto.
    simpl typelen in H2.  
    rewrite of_to_nat_unsignedv' in H2.
    rewrite Int.repr_unsigned in H2.
    assert(s
    |= Lv ((((OSCSpacePrioTbl ′ [destTask_Prio ′])
             → cnode) .. slots) [cap_Class ′])
          .. capability @ Cap == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4) ** H0).
    eapply field_asrt_impl_struct_aop'.
    3:{
      unfold Slot in H2.
      exact H2.
    }
    simpl. auto.
    unfold field_offset. simpl. rewrite Int.add_zero. auto.
    apply inline_tactics.monoasrt_mono in H4. auto.
    apply inline_tactics.Lv_mono.
Qed.

Lemma cspace_to_category_addr: 
forall 
(ct: tid)
(v': int32)
(H3: Int.unsigned v' <= 255)
(v'0: int32)
(v'1: int32)
(v'2: ier)
(v'3: absop)
(v'4: cs)
(v'5: isr)
(v'8: block)
(v'9: int32)
(v'10: CSpaceptr2prioMod.map)
(v'14: vallist)
(v'15: vallist)
(b: block)
(i1: int32)
(v'11:  list cspace_val_type)
(i2: int32)
(i3: int32)
(i0: int32)
(l: list val)
(v: val)
(i: int32)
(v'13: list cspace_val_type)
(v'6: list (int32 * (int32 * cap_content_type)))
(v'7: list (int32 * (int32 * cap_content_type)))
(v'12: int32)
(i4: int32)
(i5: int32)
(i6: int32)
(v0: val)
(s: RstateOP)
(H: 
s
  |= ASlots (b ↝ {i1 +ᵢ  $ 8})
       (Z.to_nat (Int.unsigned v'0)) v'6 **
     PV b
        ↝ {(i1 +ᵢ  $ 8) +ᵢ
           $
           Z.of_nat
             (Z.to_nat (Int.unsigned v'0) *
              typelen Slot)} @ long
     |-> Vint32 v'12 **
     PV b
        ↝ {((i1 +ᵢ  $ 8) +ᵢ
            $
            Z.of_nat
              (Z.to_nat
                 (Int.unsigned v'0) *
               typelen Slot)) +ᵢ  
           $ 4} @ long |-> 
     Vint32 i4 **
     PV b
        ↝ {(((i1 +ᵢ  $ 8) +ᵢ
             $
             Z.of_nat
               (Z.to_nat
                  (Int.unsigned v'0) *
                typelen Slot)) +ᵢ  
            $ 4) +ᵢ  $ 4} @ long
     |-> Vint32 i5 **
     PV b
        ↝ {(((i1 +ᵢ  $ 8) +ᵢ
             $
             Z.of_nat
               (Z.to_nat
                  (Int.unsigned v'0) *
                typelen Slot)) +ᵢ  
            $ 4) +ᵢ  $ 8} @ long
     |-> Vint32 i6 **
     PV b
        ↝ {(((i1 +ᵢ  $ 8) +ᵢ
             $
             Z.of_nat
               (Z.to_nat
                  (Int.unsigned v'0) *
                typelen Slot)) +ᵢ  
            $ 4) +ᵢ  $ 12} @ 
     (Void) ∗ |-> v0 **
     [|isptr v0|] **
     ASlots
       (b
        ↝ {(i1 +ᵢ  $ 8) +ᵢ
           $
           Z.of_nat
             (S
                (Z.to_nat
                   (Int.unsigned v'0)) *
              typelen Slot)})
       (Z.to_nat SLOT_NUM -
        S (Z.to_nat (Int.unsigned v'0)))
       v'7 **
     G& OSCSpacePrioTbl @
     Tarray CSPACE ∗ 64 == 
     (v'8 ↝ {v'9}) **
     PV v'8
        ↝ {v'9 +ᵢ
           $
           Z.of_nat
             (Z.to_nat (Int.unsigned v') *
              typelen CSPACE ∗)} @
     CSPACE ∗ |-> Vptr (b ↝ {i1}) **
     Aarray_rm (v'8 ↝ {v'9}) 64 
       CSPACE ∗
       (v'14 ++ Vptr (b ↝ {i1}) :: v'15)
       (Z.to_nat (Int.unsigned v')) **
     ACSpaceAarrayTptr
       (Z.to_nat (Int.unsigned v')) v'14
       v'11 v'10 **
     PV b ↝ {i1} @ long |-> Vint32 i2 **
     PV b ↝ {i1 +ᵢ  $ 4} @ long
     |-> Vint32 i3 **
     PV b
        ↝ {i1 +ᵢ
           $ Z.of_nat (typelen Cte)} @
     long |-> Vint32 i0 **
     Aarray
       (b
        ↝ {(i1 +ᵢ
            $ Z.of_nat (typelen Cte)) +ᵢ
           $ 4})
       (Tarray UNION cspace ⋆
          (Z.to_nat MaxChildNum)) l **
     PV b
        ↝ {((i1 +ᵢ
             $ Z.of_nat (typelen Cte))
            +ᵢ  $ 4) +ᵢ
           Int.mul ($ MaxChildNum)
             ($
              Z.of_nat
                (typelen UNION cspace ⋆))} @
     CSPACE ∗ |-> v **
     PV b
        ↝ {(((i1 +ᵢ
              $ Z.of_nat (typelen Cte))
             +ᵢ  $ 4) +ᵢ
            Int.mul ($ MaxChildNum)
              ($
               Z.of_nat
                 (typelen UNION cspace ⋆)))
           +ᵢ
           $ Z.of_nat (typelen CSPACE ∗)} @
     long |-> Vint32 i **
     ACSpaceAarrayTptr
       (64 -
        S (Z.to_nat (Int.unsigned v')))
       v'15 v'13 v'10 **
     Aier v'2 **
     Aie false **
     Ais nil **
     Acs v'4 **
     Aisr v'5 **
     p_local OSLInv ct init_lg **
     LV cap_Right @ long |-> Vint32 v'1 **
     LV cap_Class @ long |-> Vint32 v'0 **
     LV destTask_Prio @ char_t
     |-> Vint32 v' **
     A_dom_lenv
       ((cap_Right ↝ {long})
        :: (cap_Class ↝ {long})
           :: (destTask_Prio ↝ {char_t})
              :: nil)),
             s|=Lv ((((((OSCSpacePrioTbl ′ [destTask_Prio ′])
             → cnode) .. slots) [cap_Class ′])
           .. capability)..cap_content)..category@ Cap_Category == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 0).
Proof.
  intros.
  assert(s|=Lv ((((OSCSpacePrioTbl ′ [destTask_Prio ′])
  → cnode) .. slots) [cap_Class ′])
.. capability@ Cap == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4)).
  simpl typelen in H. 
  eapply cspace_to_capability_addr; eauto.
  assert(s|=Lv (((((OSCSpacePrioTbl ′ [destTask_Prio ′])
  → cnode) .. slots) [cap_Class ′])
.. capability)..cap_content@ Content == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 4 )).
  eapply field_asrt_impl_struct_aop; eauto.
  3:{
    instantiate (1:=Aemp).
    eapply astar_r_aemp_intro.
    unfold Cap in H0.
    exact H0.
  } 
  simpl. auto.
  unfold field_offset. simpl. rewrite Int.add_zero. auto.
  assert(s|=Lv ((((((OSCSpacePrioTbl ′ [destTask_Prio ′])
  → cnode) .. slots) [cap_Class ′])
.. capability)..cap_content)..category@ Cap_Category == (b, (i1 +ᵢ  $ 8) +ᵢ Int.mul ($ Z.of_nat 20) v'0 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 4 +ᵢ $ Z.of_nat 0)).
eapply field_asrt_impl_union_aop; eauto.
  2:{
    instantiate (1:=Aemp).
    eapply astar_r_aemp_intro.
    unfold Content in H1.
    exact H1.
  }
  simpl. auto.
  auto.
Qed.


    