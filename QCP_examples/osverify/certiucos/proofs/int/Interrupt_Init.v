(*
Definition Interrupt_Init_impl :=
Void ·Interrupt_Init·(⌞ eventID@Int32; IntNum@Int32⌟)··{
  ⌞ intmux@Int32; y@Int32 ⌟;
  intmux′ =ₑ IntNum′ ÷ ′4;ₛ
  If(intmux′ ==ₑ′1){
    y′ =ₑ (IntNum′ − (IntNum′ ÷ ′4) × ′4) × ′8;ₛ
    CGEM_regs_INTMUX1′ =ₑ (CGEM_regs_INTMUX1′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ
    (*IER′ =ₑ IER′ |ₑ (′1 ≪ IntNum′);ₛ -> int_enable_pic*)
    RINTP (IntNum);ₛ
    RETURN 
	};ₛ
  If(intmux′ ==ₑ′2){
    y′ =ₑ (IntNum′ − (IntNum′ ÷ ′4) × ′4 ) × ′8;ₛ
    CGEM_regs_INTMUX2′ =ₑ (CGEM_regs_INTMUX2′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ
    (*IER′ =ₑ IER′ |ₑ (′1 ≪ IntNum′);ₛ -> int_enable_pic*)
    RINTP (IntNum);ₛ
    RETURN 
	};ₛ
  If(intmux′ ==ₑ′3){
    y′ =ₑ (IntNum′ − (IntNum′ ÷ ′4) × ′4) × ′8;ₛ
    CGEM_regs_INTMUX3′ =ₑ (CGEM_regs_INTMUX3′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ
    (*IER′ =ₑ IER′ |ₑ (′1 ≪ IntNum′);ₛ -> int_enable_pic*)
    RINTP (IntNum);ₛ
    RETURN 
	};ₛ 
  RETURN
}·.
*)
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int. 
Require Import int_lock.
Require Import rintpProof.
Require Import Lia.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.

Lemma ltu_iwordsize1:
  forall (x:int32), (Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) -> 
    Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true.
  Proof.
    intros.
    assert (5 <= Int.unsigned x /\ Int.unsigned x <= 15) as Hq. int auto.
    assert(Int.unsigned x = 5 \/ Int.unsigned x = 6 \/ 
    Int.unsigned x = 7 \/ Int.unsigned x = 8 \/ 
    Int.unsigned x = 9 \/ Int.unsigned x = 10 \/ 
    Int.unsigned x = 11 \/ Int.unsigned x = 12 \/ 
    Int.unsigned x = 13 \/ Int.unsigned x = 14 \/ Int.unsigned x = 15). lia.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 5) = Int.unsigned (Int.repr 5)). auto. 
    assert (x = Int.repr 5).  assert (5 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 5 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 6) = Int.unsigned (Int.repr 6)). auto. 
    assert (x = Int.repr 6).  assert (6 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 6 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 7) = Int.unsigned (Int.repr 7)). auto. 
    assert (x = Int.repr 7).  assert (7 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 7 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 8) = Int.unsigned (Int.repr 8)). auto. 
    assert (x = Int.repr 8).  assert (8 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 8 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 9) = Int.unsigned (Int.repr 9)). auto. 
    assert (x = Int.repr 9).  assert (9 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 9 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 10) = Int.unsigned (Int.repr 10)). auto. 
    assert (x = Int.repr 10).  assert (10 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 10 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.
    
    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 11) = Int.unsigned (Int.repr 11)). auto. 
    assert (x = Int.repr 11).  assert (11 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 11 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 12) = Int.unsigned (Int.repr 12)). auto. 
    assert (x = Int.repr 12).  assert (12 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 12 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 13) = Int.unsigned (Int.repr 13)). auto. 
    assert (x = Int.repr 13).  assert (13 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 13 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    destruct H0. unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H1.
    assert (Int.signed (Int.repr 14) = Int.unsigned (Int.repr 14)). auto. 
    assert (x = Int.repr 14).  assert (14 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 14 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.

    unfold Int.sub. unfold Int.mul. unfold Int.divs.
    assert (Int.signed (Int.repr 4) = Int.unsigned (Int.repr 4)). auto. rewrite H0.
    assert (Int.signed (Int.repr 15) = Int.unsigned (Int.repr 15)). auto. 
    assert (x = Int.repr 15).  assert (15 = Int.unsigned x). auto. rewrite H3. int auto.
    assert (Int.repr 15 = x). auto. rewrite H4 in H2. rewrite H2. rewrite H0. auto.
  Qed.

Lemma ltu_iwordsize2:
  forall (x:int32), (Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) ->
    val_inj
    (if Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize
     then
      Some
        (Vint32 (Int.shl (Int.repr 255) (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8))))
     else None) <> Vundef.
Proof.
  intros.
  assert ((Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) -> 
    Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true).
  eapply ltu_iwordsize1.
  rewrite H0. auto. auto.
Qed.

Lemma ltu_iwordsize3:
  forall (x:int32), (Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) ->
    val_inj
    (negint
       (val_inj
          (if Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize
           then
            Some (Vint32 (Int.shl (Int.repr 255) (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8))))
           else None))) <> Vundef.
Proof.
  intros.
  assert ((Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) -> 
    Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true).
  eapply ltu_iwordsize1.
  rewrite H0. auto. auto.
Qed.

Lemma ltu_iwordsize4:
  forall (x v'13:int32), (Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) ->
    val_inj
    match
      val_inj
        (negint
           (val_inj
              (if Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize
               then
                Some (Vint32 (Int.shl (Int.repr 255) (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8))))
               else None)))
    with
    | Vint32 n2 => Some (Vint32 (Int.and v'13 n2))
    | _ => None
    end <> Vundef.
Proof.
  intros.
  assert ((Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) -> 
    Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true).
  eapply ltu_iwordsize1.
  rewrite H0. auto. auto.
Qed.

Lemma ltu_iwordsize5:
  forall (x i:int32), (Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) ->
    val_inj
    (if Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize
     then Some (Vint32 (Int.shl i (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8))))
     else None) <> Vundef.
Proof.
  intros.
  assert ((Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) -> 
    Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true).
  eapply ltu_iwordsize1.
  rewrite H0. auto. auto.
Qed.

Lemma ltu_iwordsize6:
  forall (x i v'13:int32), (Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) ->
    val_inj
    (or
       (val_inj
          match
            val_inj
              (negint
                 (val_inj
                    (if Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize
                     then
                      Some
                        (Vint32
                           (Int.shl (Int.repr 255) (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8))))
                     else None)))
          with
          | Vint32 n2 => Some (Vint32 (Int.and v'13 n2))
          | _ => None
          end)
       (val_inj
          (if Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize
           then Some (Vint32 (Int.shl i (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8))))
           else None))) <> Vundef.
Proof.
  intros.
  assert ((Int.ltu x (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) x = false) -> 
    Int.ltu (Int.mul (Int.sub x (Int.mul (Int.divs x (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true).
  eapply ltu_iwordsize1.
  rewrite H0. auto. auto.
Qed.

Lemma val_inj_solver:
  forall v'1, 
    match
      val_inj
        (mul
           (val_inj
              match
                val_inj
                  (mul
                     (val_inj
                        (if Int.eq (Int.repr 4) Int.zero || Int.eq v'1 (Int.repr Int.min_signed) && Int.eq (Int.repr 4) Int.mone
                         then None
                         else Some (Vint32 (Int.divs v'1 (Int.repr 4))))) (Vint32 (Int.repr 4)))
              with
              | Vint32 n2 => Some (Vint32 (Int.sub v'1 n2))
              | _ => None
              end) (Vint32 (Int.repr 8)))
    with
    | Vint32 _ => true
    | _ => false
    end = true.
Proof.
    intros.
    assert (Int.eq (Int.repr 4) Int.zero = false); auto.
    assert (Int.eq (Int.repr 4) Int.mone = false); auto.
    rewrite H0. rewrite H. simpl.
    destruct (Int.eq v'1 (Int.repr Int.min_signed)). simpl. auto. simpl. auto.
Qed.

Lemma conj_false:
  forall v a, val_inj (if false || v && false
                then None
                else Some a) = a.
Proof.
  intros.
  destruct (v); simpl; auto.
Qed.

Lemma Interrupt_Init_proof:
    forall vl p r logicl ct, 
      Some p = BuildPreI os_internal Interrupt_Init vl logicl Interrupt_InitPre ct->
      Some r = BuildRetI os_internal Interrupt_Init vl logicl Interrupt_InitPost ct->
      exists t d1 d2 s,
        os_internal Interrupt_Init = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
  init spec.
  hoare unfold.

  unfold INT_NUM_MIN in H1.
  unfold INT_NUM_MAX in H2.

  (*intmux′ =ₑ IntNum′ ÷ ′4;ₛ*)
  hoare forward.
  assert (Int.eq (Int.repr 4) Int.zero = false); auto.
  rewrite H0.
  assert (Int.eq (Int.repr 4) Int.mone = false); auto.
  rewrite H3.
  rewrite conj_false; auto.
  (*assert (Int.eq i0 (Int.repr Int.min_signed) && false = false).*)

  (*assert (Int.eq (Int.divs (Int.repr 5) (Int.repr 2)) (Int.repr 2) = true). auto.*)
  assert (Int.eq (Int.repr 4) Int.zero = false); auto.
  assert (Int.eq (Int.repr 4) Int.mone = false); auto.
  rewrite H. rewrite H0. rewrite conj_false.
  (*assert (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 1) = true \/
          Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 2) = true \/
          Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 3) = true \/
          (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 1) = false /\ 
          Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 2) = false /\
          Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 3) = false)).
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 1)). auto.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 2)). auto.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 3)). auto.
  right. right. right. auto.

  (*If (intmux ′ ==ₑ ′ 1)*)
  destruct H as [ Ha1 | [Ha2 | Ha3] ].*)
  hoare forward.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 1)); auto. 
  (*rewrite Ha1. auto. simpl.
  rewrite Ha1. auto.*)

  (*y′ =ₑ (IntNum′ − (IntNum′ ÷ ′4) × ′4) × ′8;ₛ*)
  instantiate (1:= Afalse).
  hoare forward.

  (*CGEM_regs_INTMUX1′ =ₑ (CGEM_regs_INTMUX1′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ*)
  pure intro.
  unfold AGVars.
  hoare forward.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 1)) in H3. simpl in H3.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 1)) in H4. simpl in H4.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 1)) in H5. simpl in H5.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize3; auto.
  eapply ltu_iwordsize4; auto.
  eapply ltu_iwordsize5; auto.
  eapply ltu_iwordsize6; auto.
  
  (*RINTP (IntNum);*)
  hoare forward prim.
  hoare unfold.
  assert ((Int.ltu v'1 (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) v'1 = false) -> 
    Int.ltu (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true).
  eapply ltu_iwordsize1.
  rewrite H8. simpl.
  eapply backward_rule1.
  intro.
  intros.
  instantiate (1 :=
    (<|| int_enable_pic_aop (|nil|);; v'2 ||>  **
        Aisr v'3 **
        Aier v'4 **
        Aie false **
        Ais v'5 **
        Acs v'6 **
        Hhier v'7 **
        (
        A_dom_lenv ((IntNum ↝ {Int32u}) :: (eventID ↝ {Int32u}) :: (intmux ↝ {Int32u}) :: (y ↝ {Int32u}) :: nil) **
        GV CGEM_regs_INTMUX1 @ Int32u
        |-> Vint32
              (Int.or
                 (Int.and v'13
                    (Int.not
                       (Int.shl (Int.repr 255) (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)))))
                 (Int.shl i (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)))) **
        GV OSLockNesting @ Int32u |-> Vint32 v'19 **
        GV OSIntNesting @ Int32u |-> Vint32 v'18 **
        GV INT_MUX_H @ Int32u |-> Vint32 v'17 **
        GV INT_MUX_L @ Int32u |-> Vint32 v'16 **
        GV CGEM_regs_INTMUX3 @ Int32u |-> Vint32 v'15 **
        GV CGEM_regs_INTMUX2 @ Int32u |-> Vint32 v'14 **
        GV OSIntExitY @ Int8u |-> Vint32 v'12 **
        GV OSPrioCur @ Int8u |-> Vint32 v'11 ** [| Int.unsigned v'11 <= 63 |] **
        GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v'10 **
        GV OSCtxSwCtr @ Int32u |-> Vint32 v'9 **
        GV OSPrioHighRdy @ Int8u |-> Vint32 v'8 ** [| Int.unsigned v'8 <= 63 |] **
        LV y @ Int32u |-> Vint32 (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) **
        LV intmux @ Int32u |-> Vint32 (Int.divs v'1 (Int.repr 4)) **
        GV OSRunning @ Int8u |-> Vint32 (Int.repr 1) **
        p_local OSLInv ct init_lg ** LV IntNum @ Int32u |-> Vint32 v'1 ** LV eventID @ Int32u |-> Vint32 i
        )
    )).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aier.
  sep pauto.
  
  hoare lifts(1::2::3::4::5::6::27::7::nil)%nat pre.
  eapply rintp_rule'; eauto.
  go.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.
  intro.
  intros.
  unfold CurLINV.
  unfold LINV.
  unfold CurTid.
(*   unfold p_local in H9. *)
  sep pauto.
(*   sep cancel LINV. *)
(*   simpl; auto.  *)
  pure_auto.
  auto.

  (*RETURN {{Afalse}}*)
  (*eapply backward_rule2.
  
  hoare forward.*)
  apply ret_rule'.
  intro. 
  intros.
  sep lift 6%nat.
  apply disj_split.
  left.
  sep auto.

  (*If (intmux ′ ==ₑ ′ 2)*)
  hoare forward.
  hoare forward.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 2)); auto. 
  (*rewrite Ha1. auto. simpl.
  rewrite Ha1. auto.*)

  (*y′ =ₑ (IntNum′ − (IntNum′ ÷ ′4) × ′4) × ′8;ₛ*)
  instantiate (1:= Afalse).
  hoare forward.

  (*CGEM_regs_INTMUX1′ =ₑ (CGEM_regs_INTMUX1′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ*)
  pure intro.
  unfold AGVars.
  hoare forward.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 2)) in H3. simpl in H3.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 2)) in H4. simpl in H4.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 2)) in H5. simpl in H5.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize3; auto.
  eapply ltu_iwordsize4; auto.
  eapply ltu_iwordsize5; auto.
  eapply ltu_iwordsize6; auto.
  
  (*RINTP (IntNum);*)
  hoare forward prim.
  hoare unfold.
  assert ((Int.ltu v'1 (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) v'1 = false) -> 
    Int.ltu (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true).
  eapply ltu_iwordsize1.
  rewrite H9. simpl.
  eapply backward_rule1.
  intro.
  intros.
  instantiate (1 :=
    (<|| int_enable_pic_aop (|nil|);; v'2 ||>  **
        Aisr v'3 **
        Aier v'4 **
        Aie false **
        Ais v'5 **
        Acs v'6 **
        Hhier v'7 **
        (
        A_dom_lenv ((IntNum ↝ {Int32u}) :: (eventID ↝ {Int32u}) :: (intmux ↝ {Int32u}) :: (y ↝ {Int32u}) :: nil) **
        GV CGEM_regs_INTMUX2 @ Int32u
         |-> Vint32
               (Int.or
                  (Int.and v'14
                     (Int.not (Int.shl (Int.repr 255) (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)))))
                  (Int.shl i (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)))) **
        GV OSLockNesting @ Int32u |-> Vint32 v'19 **
        GV OSIntNesting @ Int32u |-> Vint32 v'18 **
        GV INT_MUX_H @ Int32u |-> Vint32 v'17 **
        GV INT_MUX_L @ Int32u |-> Vint32 v'16 **
        GV CGEM_regs_INTMUX3 @ Int32u |-> Vint32 v'15 **
        GV CGEM_regs_INTMUX1 @ Int32u |-> Vint32 v'13 **
        GV OSIntExitY @ Int8u |-> Vint32 v'12 **
        GV OSPrioCur @ Int8u |-> Vint32 v'11 ** [| Int.unsigned v'11 <= 63 |] **
        GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v'10 **
        GV OSCtxSwCtr @ Int32u |-> Vint32 v'9 **
        GV OSPrioHighRdy @ Int8u |-> Vint32 v'8 ** [| Int.unsigned v'8 <= 63 |] **
        LV y @ Int32u |-> Vint32 (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) **
        LV intmux @ Int32u |-> Vint32 (Int.divs v'1 (Int.repr 4)) **
        GV OSRunning @ Int8u |-> Vint32 (Int.repr 1) **
        p_local OSLInv ct init_lg ** LV IntNum @ Int32u |-> Vint32 v'1 ** LV eventID @ Int32u |-> Vint32 i
        )
    )).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aier.
  sep pauto.
  
  hoare lifts(1::2::3::4::5::6::27::7::nil)%nat pre.
  eapply rintp_rule'; eauto.
  go.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.
  intro.
  intros.
  unfold CurLINV.
  unfold LINV.
  unfold CurTid.
(*   unfold p_local in H10. *)
  sep pauto.
(*   sep cancel LINV. *)
(*   simpl; auto.  *)
  pure_auto.
  auto.

  apply ret_rule'.
  intro. 
  intros.
  sep lift 6%nat.
  apply disj_split.
  left.
  sep auto.

  (*If (intmux ′ ==ₑ ′ 3)*)
  hoare forward.
  hoare forward.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 3)); auto. 
  (*rewrite Ha1. auto. simpl.
  rewrite Ha1. auto.*)

  (*y′ =ₑ (IntNum′ − (IntNum′ ÷ ′4) × ′4) × ′8;ₛ*)
  instantiate (1:= Afalse).
  hoare forward.

  (*CGEM_regs_INTMUX1′ =ₑ (CGEM_regs_INTMUX1′ &ₑ ∼(′255 ≪ y′) |ₑ (eventID′ ≪ y′));ₛ*)
  pure intro.
  unfold AGVars.
  hoare forward.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 3)) in H3. simpl in H3.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 3)) in H4. simpl in H4.
  destruct (Int.eq (Int.divs v'1 (Int.repr 4)) (Int.repr 3)) in H5. simpl in H5.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize2; auto.
  eapply ltu_iwordsize3; auto.
  eapply ltu_iwordsize4; auto.
  eapply ltu_iwordsize5; auto.
  eapply ltu_iwordsize6; auto.
  
  (*RINTP (IntNum);*)
  hoare forward prim.
  hoare unfold.
  assert ((Int.ltu v'1 (Int.repr 5) = false) /\ (Int.ltu (Int.repr 15) v'1 = false) -> 
    Int.ltu (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) Int.iwordsize = true).
  eapply ltu_iwordsize1.
  rewrite H10. simpl.
  eapply backward_rule1.
  intro.
  intros.
  instantiate (1 :=
    (<|| int_enable_pic_aop (|nil|);; v'2 ||>  **
        Aisr v'3 **
        Aier v'4 **
        Aie false **
        Ais v'5 **
        Acs v'6 **
        Hhier v'7 **
        (
        A_dom_lenv ((IntNum ↝ {Int32u}) :: (eventID ↝ {Int32u}) :: (intmux ↝ {Int32u}) :: (y ↝ {Int32u}) :: nil) **
        GV CGEM_regs_INTMUX3 @ Int32u
         |-> Vint32
               (Int.or
                  (Int.and v'15
                     (Int.not (Int.shl (Int.repr 255) (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)))))
                  (Int.shl i (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)))) **
        GV OSLockNesting @ Int32u |-> Vint32 v'19 **
        GV OSIntNesting @ Int32u |-> Vint32 v'18 **
        GV INT_MUX_H @ Int32u |-> Vint32 v'17 **
        GV INT_MUX_L @ Int32u |-> Vint32 v'16 **
        GV CGEM_regs_INTMUX2 @ Int32u |-> Vint32 v'14 **
        GV CGEM_regs_INTMUX1 @ Int32u |-> Vint32 v'13 **
        GV OSIntExitY @ Int8u |-> Vint32 v'12 **
        GV OSPrioCur @ Int8u |-> Vint32 v'11 ** [| Int.unsigned v'11 <= 63 |] **
        GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v'10 **
        GV OSCtxSwCtr @ Int32u |-> Vint32 v'9 **
        GV OSPrioHighRdy @ Int8u |-> Vint32 v'8 ** [| Int.unsigned v'8 <= 63 |] **
        LV y @ Int32u |-> Vint32 (Int.mul (Int.sub v'1 (Int.mul (Int.divs v'1 (Int.repr 4)) (Int.repr 4))) (Int.repr 8)) **
        LV intmux @ Int32u |-> Vint32 (Int.divs v'1 (Int.repr 4)) **
        GV OSRunning @ Int8u |-> Vint32 (Int.repr 1) **
        p_local OSLInv ct init_lg ** LV IntNum @ Int32u |-> Vint32 v'1 ** LV eventID @ Int32u |-> Vint32 i
        )
    )).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aier.
  sep pauto.
  
  hoare lifts(1::2::3::4::5::6::27::7::nil)%nat pre.
  eapply rintp_rule'; eauto.
  go.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.
  intro.
  intros.
  unfold CurLINV.
  unfold LINV.
  unfold CurTid.
(*   unfold p_local in H11. *)
  sep pauto.
(*   sep cancel LINV. *)
(*   simpl; auto.  *)
 pure_auto.
  auto.

  apply ret_rule'.
  intro. 
  intros.
  sep lift 6%nat.
  apply disj_split.
  left.
  sep auto.

  hoare forward.
  apply ret_rule'.
  intro. 
  intros.
  sep lift 6%nat.
  apply disj_split.
  right.
  sep auto.
Qed.

