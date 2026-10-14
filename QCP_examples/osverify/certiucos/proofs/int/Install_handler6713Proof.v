(*
Definition int_install_handler_6713_impl :=
Int32 ·int_install_handler_6713·(⌞ vecnum@Int32; prio@Int8u; handler@Int32; param@Int32; eventID@Int32 ⌟)··{
  ⌞ y@Int32 ⌟;
  If(vecnum′ <ₑ ′INT_NUM_MIN ||ₑ vecnum′ >ₑ ′INT_NUM_MAX){
    RETURN ′ENIVAL
	};ₛ 
  (*y′ =ₑ 〈Int32〉 handler′;ₛ*)
  y′ =ᶠ UserAddrCheck_6713(· handler′ ·);ₛ
  If(y′ !=ₑ ′1){
    RETURN ′ENIVAL
	};ₛ 
  ENTER_CRITICAL;ₛ
  IntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ handler′;ₛ
  IntHandlerParam′[vecnum′ − ′INT_NUM_MIN] =ₑ param′;ₛ
  INT_MUX_update(-eventID′, vecnum′ -);ₛ
	(*IER′ =ₑ IER′ |ₑ ′1 ≪ vecnum′;ₛ -> int_enable_pic*)
  RINTP (vecnum);ₛ
  EXIT_CRITICAL;ₛ
  RETURN ′0
}·.
*)
Require Import ucos_include.
Require Import ios_int.
Require Import int_lock.
Require Import ios_int_tac.
Require Import symbolic_lemmas.
Require Import rintpProof.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Lia.
Open Scope int_scope.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Local Open Scope int_scope.

Definition HinthandlerToInt (inthandler : Hinthandler) (num : int) : int32 :=
  match num with
  | _ => inthandler num 
  end.

Definition ZToInt (na : Z) : int:=
  match na with 
  | _ => Int.repr na
  end.

Fixpoint NatToInt (na : nat) : int:=
  match na with 
  | O => Int.zero
  | S n' => NatToInt n' 
  end.

Lemma ltu_iwordsize1:
  (*forall (i:int32), ((5 <= Int.unsigned i) /\ (Int.unsigned i < 10)) -> *)
    forall (i:int32), (5 <= Int.unsigned i) /\ (Int.ltu i ($ 10) = true) ->
    Int.ltu (Int.mul (i -ᵢ $ 4) ($ 5) +ᵢ  Int.one) Int.iwordsize = true.
Proof.
  intros.
  assert (Int.unsigned i < 10). int auto.
  assert (5 <= Int.unsigned i /\ Int.unsigned i < 10) as Hq. int auto. clear H0.
  assert(Int.unsigned i = 5 \/ Int.unsigned i = 6 \/ 
    Int.unsigned i = 7 \/ Int.unsigned i = 8 \/ 
    Int.unsigned i = 9). lia.
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 1)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto. 

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 2)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto. 
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 3)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto.
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 4)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto.
   
  unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 5)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto.
Qed.

Lemma ltu_iwordsize2:
  (*forall (i:int32), ((5 <= Int.unsigned i) /\ (Int.unsigned i < 10)) -> *)
    forall (i:int32), (5 <= Int.unsigned i) /\ (Int.ltu i ($ 10) = true) ->
    Int.ltu (Int.mul (i -ᵢ $ 4) ($ 5)) Int.iwordsize = true.
Proof.
  intros.
  assert (Int.unsigned i < 10). int auto.
  assert (5 <= Int.unsigned i /\ Int.unsigned i < 10) as Hq. int auto. clear H0.
  assert(Int.unsigned i = 5 \/ Int.unsigned i = 6 \/ 
    Int.unsigned i = 7 \/ Int.unsigned i = 8 \/ 
    Int.unsigned i = 9). lia.
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 1)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. 

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 2)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. 
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 3)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. 
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 4)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. 
   
  unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 4) = Int.unsigned ($ 5)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. 
Qed.

Lemma ltu_iwordsize3:
  (*forall (i:int32), ((5 <= Int.unsigned i) /\ (Int.unsigned i < 10)) -> *)
    forall (i:int32), (Int.unsigned i <= 15) /\ (Int.ltu i ($ 10) = false) ->
    Int.ltu (Int.mul (i -ᵢ $ 10) ($ 5) +ᵢ  $ 1) Int.iwordsize = true.
Proof.
  intros.
  assert (10 <= Int.unsigned i). int auto.
  assert (10 <= Int.unsigned i /\ Int.unsigned i <= 15) as Hq. int auto. clear H0.
   assert(Int.unsigned i = 10 \/ Int.unsigned i = 11 \/ 
    Int.unsigned i = 12 \/ Int.unsigned i = 13 \/ 
    Int.unsigned i = 14 \/ Int.unsigned i = 15). lia.

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 0)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto. 

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 1)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto. 
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 2)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto. 

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 3)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto. 

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 4)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto. 

  unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 5)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. clear H0. int auto. 
Qed.

Lemma ltu_iwordsize4:
    forall (i:int32), (Int.unsigned i <= 15) /\ (Int.ltu i ($ 10) = false) ->
    Int.ltu (Int.mul (i -ᵢ $ 10) ($ 5)) Int.iwordsize = true.
Proof.
  intros.
  assert (10 <= Int.unsigned i). int auto.
  assert (10 <= Int.unsigned i /\ Int.unsigned i <= 15) as Hq. int auto. clear H0.
  assert(Int.unsigned i = 10 \/ Int.unsigned i = 11 \/ 
    Int.unsigned i = 12 \/ Int.unsigned i = 13 \/ 
    Int.unsigned i = 14 \/ Int.unsigned i = 15). lia.
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 0)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto.

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 1)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto.  
  
  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 2)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto.

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 3)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. 

  destruct H0. unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 4)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. 

  unfold Int.mul.
  assert (Int.unsigned (i -ᵢ $ 10) = Int.unsigned ($ 5)). int auto. 
  rewrite H0. int auto.
  rewrite H1. clear H1. 
  int auto. 
Qed.

Lemma SmallerGreater4:
  forall i,
  (5 <= Int.unsigned i) /\ (Int.unsigned i <= 15)  -> 
  (0 <= Int.unsigned i - Int.unsigned ($ 4)<= 4294967295).
Proof.
  intros.
  int auto.
Qed.

Lemma SmallerGreater10:
  forall i,
  (10 <= Int.unsigned i) /\ (Int.unsigned i <= 15)  -> 
  (0 <= Int.unsigned i - Int.unsigned ($ 10)<= 4294967295).
Proof.
  intros.
  int auto.
Qed.

Lemma Greaterthan10:
  forall i,
  (val_inj (if Int.ltu i ($ 10) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
     val_inj (if Int.ltu i ($ 10) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vnull)->
  (10 <= Int.unsigned i).
Proof.
  intros.
  int auto.
  simpl in H.
  destruct H. tryfalse. tryfalse.
Qed.

Lemma val_inj1:
  forall i,
  (5 <= Int.unsigned i) /\ (Int.unsigned i <= 15) /\
  (val_inj (if Int.ltu ($ 2) (i -ᵢ $ 4) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <> Vint32 Int.zero) ->
    Int.ltu ($ 2) (i -ᵢ $ 4) = true.
Proof.
  intros. int auto. apply SmallerGreater4. auto.
  apply SmallerGreater4. auto. 
Qed.

Lemma val_inj2:
  forall i,
  (5 <= Int.unsigned i) /\ (Int.unsigned i <= 15) /\
  (val_inj (if Int.ltu ($ 2) (i -ᵢ $ 4) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
      val_inj (if Int.ltu ($ 2) (i -ᵢ $ 4) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vnull) ->
    Int.ltu ($ 2) (i -ᵢ $ 4) = false.
Proof.
  intros. int auto. simpl in H1.
  destruct H1. tryfalse. tryfalse. 
  apply SmallerGreater4. auto.
  apply SmallerGreater4. auto.
Qed.

Lemma val_inj3:
  forall i,
  (5 <= Int.unsigned i) /\ (Int.unsigned i <= 15) /\
  (val_inj (if Int.ltu i ($ 10) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
     val_inj (if Int.ltu i ($ 10) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vnull) ->
    Int.ltu i ($ 10) = false.
Proof.
  intros. int auto. simpl in H1.
  destruct H1. tryfalse. tryfalse. 
Qed.

Lemma Greater10:
  forall i,
  (Int.ltu i ($ 10) = false) -> (10 <= Int.unsigned i).
Proof.
  int auto.
Qed. 

Lemma val_inj4:
  forall i,
  (10 <= Int.unsigned i) /\ (Int.unsigned i <= 15) /\
  (val_inj (if Int.ltu ($ 2) (i -ᵢ $ 10) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) <> Vint32 Int.zero) ->
  Int.ltu ($ 2) (i -ᵢ $ 10) = true.
Proof.
  intros. 
  int auto.
  apply SmallerGreater10. auto.
  apply SmallerGreater10. auto.
Qed.

Lemma val_inj5:
  forall i,
  (10 <= Int.unsigned i) /\ (Int.unsigned i <= 15) /\
  (val_inj (if Int.ltu ($ 2) (i -ᵢ $ 10) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
      val_inj (if Int.ltu ($ 2) (i -ᵢ $ 10) then Some (Vint32 Int.one) else Some (Vint32 Int.zero)) = Vnull) ->
  Int.ltu ($ 2) (i -ᵢ $ 10) = false.
Proof.
  intros. int auto. simpl in H1.
  destruct H1. tryfalse. tryfalse. 
  apply SmallerGreater10. auto.
  apply SmallerGreater10. auto.
Qed.

(*Definition install_fail (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        (*exists vec,
        nth_val 0 vl = Some (Vint32 vec) /\ *)
        opv = Some (Vint32 (Int.repr ENIVAL)) /\ 
        O2 = Some O1
  end.

Definition install_handler_6713_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists vl' i prio handler param eventID inthandler newinthandler,
        vl = ((Vint32 i)::(Vint32 prio)::(Vint32 handler)::(param)::(Vint32 eventID)::vl') /\
        get O1 inthandlerid = Some (hinthandler inthandler) /\
        (forall x, if Int.eq x i then newinthandler x = Int.one else newinthandler x = inthandler x) /\
        O2 = Some(set O1 inthandlerid (hinthandler newinthandler)) /\
        opv = Some (Vint32 Int.zero) 
  end.

(*Definition install_handler_6713code (vl : vallist) :=
  install_fail (|vl|) ?? (int_enable_pic_aop(|nil|) ;; install_handler_6713_succ(|vl|) ;; install_handlerParam_6713_succ (|vl|)).*)

Definition install_handler_6713code (vl : vallist) :=
  install_fail (|vl|) ?? (int_enable_pic_aop(|nil|) ;; install_handler_6713_succ(|vl|)).

Definition install_handler_6713api:=(install_handler_6713code,(Tint32,Tint32::Tint32::Tint32::(Tptr Tvoid)::Tint32::nil)).*)

Lemma install_handler6713_err_return :
  forall P sch vec prio handler param eventID vl', 
    can_change_aop P ->
    isptr param ->
    absinfer sch ( <|| install_handler_6713code ((Vint32 vec)::(Vint32 prio)::(Vint32 handler)::(param)::(Vint32 eventID)::vl')||> ** P) 
            ( <|| END  (Some (Vint32 (Int.repr ENIVAL))) ||> ** P). 
Proof.
  intros.
  simpljoin.
  infer_solver 0%nat.
Qed.

Lemma install_handler6713_ier_return :
  forall P sch i i0 v'2 x0 i2 vl', 
    can_change_aop P ->
    absinfer sch ( <|| install_handler_6713code (Vint32 i :: Vint32 i0 :: Vint32 v'2 :: x0 :: Vint32 i2 :: vl') ||> ** P) 
            ( <|| int_enable_pic_aop(|nil|) ;; 
                  install_handler_6713_succ (|Vint32 i :: Vint32 i0 :: Vint32 v'2 :: x0 :: Vint32 i2 :: vl'|)||> ** P). 
Proof.
  unfold install_handler_6713code. intros.
  infer_branch 1%nat.
  (*eapply absinfer_trans.*)
  eapply absinfer_eq.
Qed.

Lemma install_handler6713_succ_return :
  forall P sch i i0 v'3 x0 i2 inthandler newinthandler vl', 
    can_change_aop P ->
    (forall x, if Int.eq x i then newinthandler x = Int.one else newinthandler x = inthandler x) ->
    absinfer sch ( <|| install_handler_6713_succ (|Vint32 i :: Vint32 i0 :: Vint32 v'3 :: x0 :: Vint32 i2 :: vl'|)||> ** 
                   Hhinthandler inthandler ** P) 
            ( <|| END  (Some (Vint32 Int.zero)) ||> ** 
              Hhinthandler newinthandler ** P).
Proof.
  intros. infer_part2.
Qed.

Lemma Install_handler6713Proof: 
  forall tid vl p r, 
    Some p = BuildPreA' os_api int_install_handler_6713 install_handler_6713api vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api int_install_handler_6713 install_handler_6713api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api int_install_handler_6713 = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init_spec. (*Initialize Specification*)

  (*L1~L3 IF语句*)
  unfold INT_NUM_MIN, INT_NUM_MAX.
  (*hoare unfold.*)
  hoare forward.
  destruct (Int.ltu i (Int.repr 5)); simpl; intro; tryfalse.
  destruct (Int.ltu (Int.repr 15) i); simpl; intro; tryfalse.
  destruct (Int.ltu i (Int.repr 5)); destruct (Int.ltu (Int.repr 15) i); simpl; intro; tryfalse.  
  unfold ENIVAL.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply install_handler6713_err_return; eauto.
  go.
  int auto.

  (*i < 5*)
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$ENIVAL)).
  destruct H3.
  symbolic_execution.
  sep pauto.
  sep cancel A_dom_lenv.
  sep cancel Aier.
  sep pauto.

  (*i > 15*)
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$ENIVAL)).
  destruct H3.
  symbolic_execution.
  sep pauto.
  sep cancel A_dom_lenv.
  sep cancel Aier.
  sep pauto.

  (*5 <= i <= 15*)
  assert (Int.ltu i ($ 5) = false /\ Int.ltu ($ 15) i = false) as Hq.
  int auto.
  destruct H.
  simpl.
  int auto.

  (*L5~L7: If (handler ′ <ₑ ′ 0){RETURN ′ ENIVAL};ₛ*)
  hoare forward.
  pure intro.
  hoare unfold.
  hoare normal pre.
  hoare unfold.
  assert (5 <= Int.unsigned i /\ Int.unsigned i <= 15) as Hq.
  clear -H.
  int auto. 
  destruct H; simpl in H; tryfalse.
  destruct H; simpl in H; tryfalse.

  unfold ENIVAL.
  hoare unfold.
  assert (Int.ltu i1 ($ 0) = true \/ Int.eq ($ 0) i1 = true \/ Int.ltu ($ 0) i1 = true). int auto.
  destruct H3.

  (*′0 > handler′情况*)
  (*eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.*)
  hoare unfold.
  hoare forward.
  rewrite H3. 
  auto.
  assert (Int.eq ($ 0) i1 = false). int auto.
  rewrite H5.
  auto.
  assert (Int.eq ($ 0) i1 = false). int auto.
  rewrite H5.
  rewrite H3.
  auto.
  hoare_split_pure_all.
  hoare abscsq.
  apply noabs_oslinv.
  apply install_handler6713_err_return; auto.
  go.
  hoare unfold.
  hoare forward.  
  hoare forward.
  hoare unfold.
  Local Open Scope int_scope.
  assert (Int.eq ($ 0) i1 = false). int auto.
  rewrite H3 in H4.
  rewrite H5 in H4.
  false; destruct H4; intros.
  inversion H4.
  inversion H4.

  (*′0 = handler′情况*)
  (*eapply backward_rule1.
  intros;eapply disj_star_elim.
  eauto.*)
  destruct H3.
  hoare unfold.
  hoare forward.
  assert (Int.ltu i1 ($ 0) = false). int auto.
  rewrite H5.
  auto.
  rewrite H3. 
  auto.
  assert (Int.ltu i1 ($ 0) = false). int auto.
  rewrite H5.
  rewrite H3.
  auto.
  hoare_split_pure_all.
  hoare abscsq.
  apply noabs_oslinv.
  apply install_handler6713_err_return; auto.
  go.
  hoare unfold.
  hoare forward.  
  hoare forward.
  hoare unfold.
  Local Open Scope int_scope.
  assert (Int.ltu i1 ($ 0) = false). int auto.
  rewrite H3 in H4.
  rewrite H5 in H4.
  false; destruct H4; intros.
  inversion H4.
  inversion H4.

  (*handler′ >= ′0情况*)
  hoare forward prim; pure_auto.
  hoare unfold.
  hoare forward.
  assert (Int.ltu i1 ($ 0) = false). int auto.
  rewrite H5.
  auto.
  assert (Int.eq ($ 0) i1 = false). int auto.
  rewrite H5.
  auto.
  assert (Int.ltu i1 ($ 0) = false). int auto.
  assert (Int.eq ($ 0) i1 = false). int auto.
  rewrite H5.
  rewrite H6.
  auto.
  assert (Int.ltu i1 ($ 0) = false). int auto.
  assert (Int.eq ($ 0) i1 = false). int auto.
  rewrite H5.
  rewrite H4.
  hoare unfold.
  unfold install_handler_6713code.
  eapply backward_rule1.
  intro.
  intros.
  sep lifts (3::nil)%nat in H9.

  exact H9.
  hoare abscsq.
  apply noabs_oslinv.
  apply install_handler6713_err_return.
  can_change_aop_solver.
  pauto.
  hoare forward.
  
  (*清除Afalse分支*)
  hoare forward.
  (*ENTER_CRITICAL;ₛ*)
  pure intro.
  hoare forward prim; pauto.
  hoare unfold.
  hoare normal pre.
  hoare unfold.

  (*IntHandler ′ [vecnum ′ − ′ 5] =ₑ handler ′;ₛ*)
  unfold IntInv.
  hoare unfold.
  hoare forward.
  unfold AOSInthandler.
  eapply forward_rule2;   [ idtac | first [ intros s H; exact H | sep pauto ] ].
  let s := fresh in
  let H := fresh in
  match goal with
    | |- {|_ ,_, _, _, _, _|}|- _ {{?P}}?x ′ [_] =ₑ _ {{_}} =>
      match find_lvararray P x with
        | some ?m => idtac 
        | none _ =>match find_dom_lenv P with
                     | (none _, _) => fail 2
                     | (some ?m, Some ?ls) =>
                       let ret1 := constr:(var_notin_dom x ls) in
                       let ret2 := eval compute in ret1 in
                           match ret2 with
                             | true =>
                               match find_aop P with
                                 | none _ => fail 1
                                 | some ?n =>
                                   match find_gvararray P x with
                                     | none _ => fail 3
                                     | some ?o =>
                                       hoare lifts (n :: m :: o :: nil) pre;
                                         eapply assign_rule_array_g_aop
                                   end
                               end
                             | false => fail
                           end
                   end
      end
  end.
  intros sss; split; intro HHH; exact HHH.
  simpl; auto.
  symbolic execution.
  symbolic execution.
  branch 3.
  auto.
  assert ( Z.of_nat 11 = 11).
  int auto.
  rewrite H7.
  int auto.
  int auto.
  clear; pauto.
  apply assign_type_match_true.
  simpl; auto.
  assert (Z.of_nat (length (HinthandlerToListval v'23)) = 11).
  int auto.
  rewrite H7.
  int auto.
  int auto.
  {
    intro; intros.
    sep normal in H7.
    sep destruct H7.
    sep eexists.
    sep cancel p_local.
    simpl; auto.
  }

  (*外层IF-ELSE*)
  hoare forward.
  destruct(Int.ltu i ($ 10)); auto.
  assert (Int.ltu i ($ 10) = false \/ Int.ltu i ($ 10) = true). int auto.
  destruct H7.
  pure intro.
  rewrite H7 in H8; tryfalse. 
  simpl in H8; tryfalse.
  pure intro.

  (*IF中的IF-ElSE*)
  hoare forward.
  destruct(Int.ltu ($ 2) (i -ᵢ $ 4)); auto.
  (*IF中的IF*)
  pure intro.
  hoare forward.
  (*IF中的ELSE*)
  pure intro.
  hoare forward.
  (*IF中IF-ELSE的两个分支*)
  unfold AGVars. 
  instantiate (1:= (([|Int.ltu ($ 2) (i -ᵢ $ 4) = true|] ** 
  LV y @ long |-> Vint32 (Int.mul (i -ᵢ $ 4) ($ 5) +ᵢ  $ 1) \\//
  [|Int.ltu ($ 2) (i -ᵢ $ 4) = false|] ** LV y @ long |-> Vint32 (Int.mul (i -ᵢ $ 4) ($ 5)))
  ** 
  <|| install_handler_6713code (Vint32 i :: Vint32 i0 :: Vint32 i1 :: x0 :: Vint32 i2 :: v') ||>  **
   A_dom_lenv
     ((eventID ↝ {long}) :: (param ↝ {(Void) ∗}) :: (handler ↝ {long}) :: (prio ↝ {long}) :: (vecnum ↝ {long}) :: (y ↝ {long}) :: nil) **
   GAarray IntHandler (Tarray Int32u 11) (update_nth_val (Z.to_nat (Int.unsigned (i -ᵢ $ 5))) (HinthandlerToListval v'23) (V$ 1)) **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSTCBPrioTbl v'2 v'8 v'11 v'16 v'13 **
   AOSTCBList v'3 v'4 v'5 (v'6 :: v'7) v'8 tid v'11 **
   AOSTCBFreeList v'14 v'15 **
   AOSRdyTblGrp v'8 v'9 **
   AOSTime (Vint32 v'12) **
   HTCBList v'11 **
   HTime v'12 **
   HCurTCB tid **
   (GV OSRunning @ char_t |-> (V$ 1) **
    (EX v : int32, GV OSPrioHighRdy @ char_t |-> Vint32 v ** [|Int.unsigned v <= 63|]) **
    (EX v : int32, GV OSCtxSwCtr @ long |-> Vint32 v) **
    (EX v : addrval, GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v) **
    (EX v : int32, GV OSPrioCur @ char_t |-> Vint32 v ** [|Int.unsigned v <= 63|]) **
    (EX v : int32, GV OSIntExitY @ char_t |-> Vint32 v) **
    (EX v : int32, GV CGEM_regs_INTMUX1 @ long |-> Vint32 v) **
    (EX v : int32, GV CGEM_regs_INTMUX2 @ long |-> Vint32 v) **
    (EX v : int32, GV CGEM_regs_INTMUX3 @ long |-> Vint32 v) **
    (EX v : int32, GV INT_MUX_L @ long |-> Vint32 v) **
    (EX v : int32, GV INT_MUX_H @ long |-> Vint32 v) **
    (EX v : int32, GV OSIntNesting @ long |-> Vint32 v) ** (EX v : int32, GV OSLockNesting @ long |-> Vint32 v)) **
  APthreadAttr v'17 **
  EvtInv v'10 v'3 (v'5 ++ v'6 :: v'7) v'11 v'13 v'19 v'20 v'21**
   A_isr_is_prop **
   TmrInv **
   CoreCommuInv v'10 **
   PartitionInv v'10 **
   CapabilityInv v'18 **
   Hhier v'22 **
   Hhinthandler v'23 **
   HhinthandlerParam v'24 **
   AOSInthandlerParam v'24 **
   AOSExchandler (Vint32 v'25) **
   Hhexchandler v'25 **
   tcbdllflag v'3 (v'5 ++ v'6 :: v'7) **
   p_local OSLInv tid
     (logic_val (V$ 1) :: logic_val (V$ inferules.__EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
   Aisr empisr **
   Aie false **
   Ais nil **
   Acs (true :: nil) **
   Aier v'1 **
   aemp_isr_is **
   LV eventID @ long |-> Vint32 i2 **
   LV param @ (Void) ∗ |-> x0 ** LV handler @ long |-> Vint32 i1 ** LV prio @ long |-> Vint32 i0 ** LV vecnum @ long |-> Vint32 i)).
  hoare forward.
  (*apply disj_rule.*)

  (*y′ =ₑ (vecnum′ − ′4)× ′5 +ₑ ′1即对应vecnum=7、8、9*)
  (*INT_MUX_L′ =ₑ (INT_MUX_L′ &ₑ ∼(′31 ≪ y′));ₛ*)
  pure intro.
  (*assert (Int.unsigned i < 10). auto.
  assert ((5 <= Int.unsigned i) /\ (Int.unsigned i < 10)).
  auto.*)
  assert (Int.ltu (Int.mul (i -ᵢ $ 4) ($ 5) +ᵢ  Int.one) Int.iwordsize = true).
  apply ltu_iwordsize1. auto.
  assert (Int.one = $ 1). auto. rewrite H17 in H16.
  hoare forward.
  rewrite H16. auto.
  rewrite H16. auto.
  rewrite H16. auto.
  (*INT_MUX_L′ =ₑ (INT_MUX_L′ |ₑ (eventID′ ≪ y′))*)
  hoare forward.
  rewrite H16. auto.
  rewrite H16. auto.
  rewrite H16. auto.
  apply disj_split.
  left.
  sep auto.
  apply val_inj1. auto.
  rewrite H16. simpl. auto.

  (*y′ =ₑ (vecnum′ − ′4)× ′5即vecnum=5、6*)
  (*INT_MUX_H′ =ₑ (INT_MUX_L′ &ₑ ∼(′31 ≪ y′));ₛ*)
  pure intro.
  unfold AGVars.
  assert (Int.ltu (Int.mul (i -ᵢ $ 4) ($ 5)) Int.iwordsize = true).
  apply ltu_iwordsize2. auto.
  hoare forward.  
  rewrite H14. auto.
  rewrite H14. auto.
  rewrite H14. auto.
  (*INT_MUX_L ′ =ₑ INT_MUX_L ′ |ₑ eventID ′ ≪ ios_int.y ′*) 
  hoare forward.
  rewrite H14. auto.
  rewrite H14. auto.
  rewrite H14. auto.
  apply disj_split.
  right.
  sep auto.
  apply val_inj2. auto.
  rewrite H14. simpl. auto.

  (*ELSE中的IF-ELSE*)
  pure intro.
  assert (Int.ltu i ($ 10) = false).
  apply val_inj3. auto.

  hoare forward.
  destruct(Int.ltu ($ 2) (i -ᵢ $ 10)); auto.
  (*IF中的IF*)
  pure intro.
  hoare forward.
  (*IF中的ELSE*)
  pure intro.
  hoare forward.
  (*ELSE中IF-ELSE的两个分支*)
  unfold AGVars.
  instantiate (1:= (([|Int.ltu ($ 2) (i -ᵢ $ 10) = true|] ** 
  LV y @ long |-> Vint32 (Int.mul (i -ᵢ $ 10) ($ 5) +ᵢ  $ 1) \\//
  [|Int.ltu ($ 2) (i -ᵢ $ 10) = false|] ** LV y @ long |-> Vint32 (Int.mul (i -ᵢ $ 10) ($ 5)))
  ** 
  <|| install_handler_6713code (Vint32 i :: Vint32 i0 :: Vint32 i1 :: x0 :: Vint32 i2 :: v') ||>  **
   A_dom_lenv
     ((eventID ↝ {long}) :: (param ↝ {(Void) ∗}) :: (handler ↝ {long}) :: (prio ↝ {long}) :: (vecnum ↝ {long}) :: (y ↝ {long}) :: nil) **
   GAarray IntHandler (Tarray long 11) (update_nth_val (Z.to_nat (Int.unsigned (i -ᵢ $ 5))) (HinthandlerToListval v'23) (V$ 1)) **
   AOSMapTbl **
   AOSUnMapTbl **
   AOSTCBPrioTbl v'2 v'8 v'11 v'16 v'13 **
   AOSTCBList v'3 v'4 v'5 (v'6 :: v'7) v'8 tid v'11 **
   AOSTCBFreeList v'14 v'15 **
   AOSRdyTblGrp v'8 v'9 **
   AOSTime (Vint32 v'12) **
   HTCBList v'11 **
   HTime v'12 **
   HCurTCB tid **
   (GV OSRunning @ char_t |-> (V$ 1) **
    (EX v : int32, GV OSPrioHighRdy @ char_t |-> Vint32 v ** [|Int.unsigned v <= 63|]) **
    (EX v : int32, GV OSCtxSwCtr @ long |-> Vint32 v) **
    (EX v : addrval, GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v) **
    (EX v : int32, GV OSPrioCur @ char_t |-> Vint32 v ** [|Int.unsigned v <= 63|]) **
    (EX v : int32, GV OSIntExitY @ char_t |-> Vint32 v) **
    (EX v : int32, GV CGEM_regs_INTMUX1 @ long |-> Vint32 v) **
    (EX v : int32, GV CGEM_regs_INTMUX2 @ long |-> Vint32 v) **
    (EX v : int32, GV CGEM_regs_INTMUX3 @ long |-> Vint32 v) **
    (EX v : int32, GV INT_MUX_L @ long |-> Vint32 v) **
    (EX v : int32, GV INT_MUX_H @ long |-> Vint32 v) **
    (EX v : int32, GV OSIntNesting @ long |-> Vint32 v) ** (EX v : int32, GV OSLockNesting @ long |-> Vint32 v)) **
   APthreadAttr v'17 **
   EvtInv v'10 v'3 (v'5 ++ v'6 :: v'7) v'11 v'13 v'19 v'20 v'21 **
   A_isr_is_prop **
   TmrInv **
   CoreCommuInv v'10 **
   PartitionInv v'10 **
   CapabilityInv v'18 **
   Hhier v'22 **
   Hhinthandler v'23 **
   HhinthandlerParam v'24 **
   AOSInthandlerParam v'24 **
   AOSExchandler (Vint32 v'25) **
   Hhexchandler v'25 **
   tcbdllflag v'3 (v'5 ++ v'6 :: v'7) **
   p_local OSLInv tid (logic_val (V$ 1) :: logic_val (V$ inferules.__EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
   Aisr empisr **
   Aie false **
   Ais nil **
   Acs (true :: nil) **
   Aier v'1 **
   aemp_isr_is **
   LV eventID @ long |-> Vint32 i2 **
   LV param @ (Void) ∗ |-> x0 ** LV handler @ long |-> Vint32 i1 ** LV prio @ long |-> Vint32 i0 ** LV vecnum @ long |-> Vint32 i)).
  hoare forward.

  (*ios_int.y ′ =ₑ (vecnum ′ − ′ 10) × ′ 5 +ₑ ′ 1即vecnum = 13、14、15*)
  (*INT_MUX_H ′ =ₑ INT_MUX_L ′ &ₑ ∼ (′ 31 ≪ ios_int.y ′);ₛ*)
  pure intro.
  assert (Int.ltu (Int.mul (i -ᵢ $ 10) ($ 5) +ᵢ  $ 1) Int.iwordsize = true).
  apply ltu_iwordsize3. auto.
  hoare forward.
  rewrite H14. auto.
  rewrite H14. auto.
  rewrite H14. auto.
  (*INT_MUX_H ′ =ₑ INT_MUX_L ′ |ₑ eventID ′ ≪ ios_int.y ′*)
  hoare forward.
  rewrite H14. auto.
  rewrite H14. auto.
  apply disj_split.
  left.
  sep auto.
  Focus 1.
  assert(10 <= Int.unsigned i).
  apply Greater10. auto.
  apply val_inj4. auto.
  rewrite H14. simpl. auto.

  (*ios_int.y ′ =ₑ (vecnum ′ − ′ 10) × ′ 5即vecnum = 10、11、12*)
  (*INT_MUX_H ′ =ₑ INT_MUX_L ′ &ₑ ∼ (′ 31 ≪ ios_int.y ′);ₛ*)
  pure intro.
  assert (Int.ltu (Int.mul (i -ᵢ $ 10) ($ 5)) Int.iwordsize = true).
  apply ltu_iwordsize4. auto.
  hoare forward.
  rewrite H12. auto.
  rewrite H12. auto.
  rewrite H12. auto.
  (*INT_MUX_H ′ =ₑ INT_MUX_L ′ |ₑ eventID ′ ≪ ios_int.y ′*)
  hoare forward.
  rewrite H12. auto.
  rewrite H12. auto.
  apply disj_split.
  right.
  sep auto.
  assert(10 <= Int.unsigned i).
  apply Greater10. auto.
  apply val_inj5. auto.
  rewrite H12. simpl. auto.

  hoare forward.

  (*vecnum < 10对应的分支*)
  pure intro.
  eapply backward_rule1.
  intros.
  sep lift 13%nat in H12.
  apply disj_split in H12.
  exact H12.
  apply disj_rule.
  (*hoare forward.*)

  (*Int.ltu ($ 2) (i -ᵢ $ 4) = true即vennum为7、8、9对应的分支*)
  pure intro.
  rename H12 into H789.

  (*RINTP (vecnum);ₛ*)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.  
  eapply install_handler6713_ier_return.
  go.
  (*can_change_aop_solver.*)
  unfold AOSInthandlerParam. go.
  unfold AOSExchandler. go.
  (*unfold aemp_isr_is. go.*)

  eapply backward_rule1.
  intro.
  intros.
  sep lifts(43::45::30::48::1::44::46::47::53::nil)%nat in H12.
  eapply elim_a_isr_is_prop in H12.
  eapply elim_aemp_isr_is_prop in H12.
  exact H12.

  eapply seq_rule.
  hoare lifts(3::1::6::4::2::5::7::40::nil)%nat pre.
  eapply rintp_rule'; eauto.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.

  intro.
  intros.
  unfold CurLINV.
  unfold p_local in H12.
  sep pauto.
  sep cancel LINV.
  simpl; auto.

  (*EXIT_CRITICAL;ₛ*)
  pure_auto.
  hoare unfold pre.
  hoare lifts(1::41::nil)%nat pre.
  new_hoare_abscsq.
  apply noabs_oslinv.
  eapply install_handler6713_succ_return.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold aemp_isr_is.
  can_change_aop_solver.
  
  instantiate (1:= (fun (x : int32) => if Int.eq x i then Int.one else v'23 x)).
  intros.
  assert (Int.eq x i = true \/ Int.eq x i = false) as Hx.  
  int auto.
  apply SmallerGreater4. auto. 
  int auto.
  apply SmallerGreater4. auto.

  eapply backward_rule1.
  intro; intros.
  sep lifts (3::6::nil)%nat in H12.
  eapply add_a_isr_is_prop in H12.
  sep lifts (1::2::6::nil)%nat in H12.
  eapply add_aemp_isr_is_prop in H12.
  eauto.
  hoare lift 6%nat pre.

  hoare normal pre. 
  hoare_ex_intro.
  eapply seq_rule.
  hoare_forward_prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel EvtInv.
  sep cancel p_local.
  unfold IntInv.
  unfold AOSInthandler.
  unfold AOSExchandler in *.
  sep cancel Aier.
  unfold AGVars.
  sep pauto.

  unfold ierupd.
  unfold HinthandlerToListval.
  unfold update_nth_val.
  unfold vecMin.
  unfold os_inv.ZToInt.
  unfold Int.ltu in H12.
  apply MatchHandler1. auto.
  pure_auto.
  go.
  hoare forward.

  (*Int.ltu ($ 2) (i -ᵢ $ 4) = false即vennum为5、6对应的分支*)
  pure intro.
  rename H12 into H56.

  (*RINTP (vecnum);ₛ*)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.  
  eapply install_handler6713_ier_return.
  go.
  (*can_change_aop_solver.*)
  unfold AOSInthandlerParam. go.
  unfold AOSExchandler. go.
  (*unfold aemp_isr_is. go.*)

  eapply backward_rule1.
  intro.
  intros.

  sep lifts(43::45::30::48::1::44::46::47::53::nil)%nat in H12.
  eapply elim_a_isr_is_prop in H12.
  eapply elim_aemp_isr_is_prop in H12.
  exact H12.

  eapply seq_rule.
  (*hoare lifts(1::2::3::4::5::6::50::7::nil)%nat pre.*)
  hoare lifts(3::1::6::4::2::5::7::40::nil)%nat pre.
  eapply rintp_rule'; eauto.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.

  intro.
  intros.
  unfold CurLINV.
  unfold p_local in H12.
  sep pauto.
  sep cancel LINV.
  simpl; auto.

  (*EXIT_CRITICAL;ₛ*)
  pure_auto.
  hoare unfold pre.
  hoare lifts(1::41::nil)%nat pre.
  new_hoare_abscsq.
  apply noabs_oslinv.
  eapply install_handler6713_succ_return.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold aemp_isr_is.
  can_change_aop_solver.
  
  instantiate (1:= (fun (x : int32) => if Int.eq x i then Int.one else v'23 x)).
  intros.
  assert (Int.eq x i = true \/ Int.eq x i = false) as Hx.  
  (*unfold vecMin.*) 
  int auto.
  apply SmallerGreater4. auto. 
  int auto.
  apply SmallerGreater4. auto.

  eapply backward_rule1.
  intro; intros.
  sep lifts (3::6::nil)%nat in H12.
  eapply add_a_isr_is_prop in H12.
  sep lifts (1::2::6::nil)%nat in H12.
  eapply add_aemp_isr_is_prop in H12.
  eauto.
  hoare lift 6%nat pre.

  hoare normal pre. 
  hoare_ex_intro.
  eapply seq_rule.
  hoare_forward_prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel EvtInv.
  sep cancel p_local.
  unfold IntInv.
  unfold AOSInthandler.
  unfold AOSExchandler in *.
  sep cancel Aier.
  unfold AGVars.
  sep pauto.

  unfold ierupd.
  unfold HinthandlerToListval.
  unfold update_nth_val.
  unfold vecMin.
  unfold os_inv.ZToInt.
  unfold Int.ltu in H12.
  apply MatchHandler1. auto.
  pure_auto.
  go.
  hoare forward.

  (*10 <= vecnum对应的分支*)
  pure intro.
  eapply backward_rule1.
  intros.
  sep lift 13%nat in H10.
  apply disj_split in H10.
  exact H10.
  apply disj_rule.

  (*Int.ltu ($ 2) (i -ᵢ $ 10) = true即vennum为13、14、15对应的分支*)
  pure intro.
  rename H10 into H131415.
  (*apply disj_split.
  left.*)

  (*RINTP (vecnum);ₛ*)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.  
  eapply install_handler6713_ier_return.
  go.
  (*can_change_aop_solver.*)
  unfold AOSInthandlerParam. go.
  unfold AOSExchandler. go.
  (*unfold aemp_isr_is. go.*)

  eapply backward_rule1.
  intro.
  intros.

  sep lifts(43::45::30::48::1::44::46::47::53::nil)%nat in H10.
  eapply elim_a_isr_is_prop in H10.
  eapply elim_aemp_isr_is_prop in H10.
  exact H10.

  eapply seq_rule.
  (*hoare lifts(1::2::3::4::5::6::50::7::nil)%nat pre.*)
  hoare lifts(3::1::6::4::2::5::7::40::nil)%nat pre.
  eapply rintp_rule'; eauto.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler in *.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.

  intro.
  intros.
  unfold CurLINV.
  unfold p_local in H10.
  sep pauto.
  sep cancel LINV.
  simpl; auto.

  (*EXIT_CRITICAL;ₛ*)
  pure_auto.
  hoare unfold pre.
  hoare lifts(1::41::nil)%nat pre.
  new_hoare_abscsq.
  apply noabs_oslinv.
  eapply install_handler6713_succ_return.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold aemp_isr_is.
  can_change_aop_solver.
  
  instantiate (1:= (fun (x : int32) => if Int.eq x i then Int.one else v'23 x)).
  intros.
  assert (10 <= Int.unsigned i).
  apply Greaterthan10. auto.
  assert (Int.eq x i = true \/ Int.eq x i = false) as Hx.  
  (*unfold vecMin.*) 
  int auto.
  apply SmallerGreater10. auto. 
  int auto.
  apply SmallerGreater10. auto.

  eapply backward_rule1.
  intro; intros.
  sep lifts (3::6::nil)%nat in H10.
  eapply add_a_isr_is_prop in H10.
  sep lifts (1::2::6::nil)%nat in H10.
  eapply add_aemp_isr_is_prop in H10.
  eauto.
  hoare lift 6%nat pre.

  hoare normal pre. 
  hoare_ex_intro.
  eapply seq_rule.
  hoare_forward_prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel EvtInv.
  sep cancel p_local.
  unfold IntInv.
  unfold AOSInthandler.
  unfold AOSExchandler in *.
  sep cancel Aier.
  unfold AGVars.
  sep pauto.

  unfold ierupd.
  unfold HinthandlerToListval.
  unfold update_nth_val.
  unfold vecMin.
  unfold os_inv.ZToInt.
  unfold Int.ltu in H10.
  apply MatchHandler1. auto.
  pure_auto.
  go.
  hoare forward.  
  
  (*Int.ltu ($ 2) (i -ᵢ $ 10) = true即vennum为10、11、12对应的分支*)
  pure intro.
  rename H10 into H101112.
  (*apply disj_split.
  left.*)

  (*RINTP (vecnum);ₛ*)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.  
  eapply install_handler6713_ier_return.
  go.
  (*can_change_aop_solver.*)
  unfold AOSInthandlerParam. go.
  unfold AOSExchandler. go.
  (*unfold aemp_isr_is. go.*)

  eapply backward_rule1.
  intro.
  intros.

  sep lifts(43::45::30::48::1::44::46::47::53::nil)%nat in H10.
  eapply elim_a_isr_is_prop in H10.
  eapply elim_aemp_isr_is_prop in H10.
  exact H10.

  eapply seq_rule.
  (*hoare lifts(1::2::3::4::5::6::50::7::nil)%nat pre.*)
  hoare lifts(3::1::6::4::2::5::7::40::nil)%nat pre.
  eapply rintp_rule'; eauto.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.

  intro.
  intros.
  unfold CurLINV.
  unfold p_local in H10.
  sep pauto.
  sep cancel LINV.
  simpl; auto.

  (*EXIT_CRITICAL;ₛ*)
  pure_auto.
  hoare unfold pre.
  hoare lifts(1::41::nil)%nat pre.
  new_hoare_abscsq.
  apply noabs_oslinv.
  eapply install_handler6713_succ_return.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold aemp_isr_is.
  can_change_aop_solver.
  
  instantiate (1:= (fun (x : int32) => if Int.eq x i then Int.one else v'23 x)).
  intros.
  assert (10 <= Int.unsigned i).
  apply Greaterthan10. auto.
  assert (Int.eq x i = true \/ Int.eq x i = false) as Hx.  
  (*unfold vecMin.*) 
  int auto.
  apply SmallerGreater10. auto. 
  int auto.
  apply SmallerGreater10. auto.

  eapply backward_rule1.
  intro; intros.
  sep lifts (3::6::nil)%nat in H10.
  eapply add_a_isr_is_prop in H10.
  sep lifts (1::2::6::nil)%nat in H10.
  eapply add_aemp_isr_is_prop in H10.
  eauto.
  hoare lift 6%nat pre.

  hoare normal pre. 
  hoare_ex_intro.
  eapply seq_rule.
  hoare_forward_prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel EvtInv.
  sep cancel p_local.
  unfold IntInv.
  unfold AOSInthandler.
  unfold AOSExchandler in *.
  sep cancel Aier.
  unfold AGVars.
  sep pauto.

  unfold ierupd.
  unfold HinthandlerToListval.
  unfold update_nth_val.
  unfold vecMin.
  unfold os_inv.ZToInt.
  unfold Int.ltu in H10.
  apply MatchHandler1. auto.
  pure_auto.
  go.
  hoare forward. 
Qed.

Close Scope list_scope.
Close Scope Z_scope.
Local Close Scope int_scope.
Close Scope code_scope.



