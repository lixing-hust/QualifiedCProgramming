(*
Definition int_install_handler_6678_impl :=
Int32 ·int_install_handler_6678·(⌞ vecnum@Int32; prio@Int32; handler@ Int32; param@(Ptr Void); eventID@Int32⌟)··{
  ⌞ y@Int32 ⌟; 
  If(eventID′ ==ₑ ′CSL_GEM_IPC_LOCAL ||ₑ eventID′ ==ₑ ′CSL_GEM_TINTLN){
    RETURN ′ENIVAL
	};ₛ
  If(vecnum′ <ₑ ′INT_NUM_MIN ||ₑ vecnum′ >ₑ ′INT_NUM_MAX){
    RETURN ′ENIVAL
	};ₛ 
  (*y′ =ₑ 〈Int32〉 handler′;ₛ
  y′ =ᶠ UserAddrCheck_6678(· y′ ·);ₛ*)
  If(handler′ <ₑ ′0){
    RETURN ′ENIVAL
	};ₛ 
  ENTER_CRITICAL;ₛ 
  (*Interrupt_Init(-eventID′, vecnum′ -);ₛ*)
  IntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ ′1;ₛ
  (*IntHandlerParam′[vecnum′ − ′INT_NUM_MIN] =ₑ param′;ₛ*)
  RINTP (vecnum);ₛ
  EXIT_CRITICAL;ₛ
  RETURN ′0
}·.
*)
Require Import ucos_include.
Require Import int_lock.
Require Import ios_int.
Require Import ios_int_tac.
Require Import symbolic_lemmas.
Require Import rintpProof.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
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

(*Definition install_fail (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        (*exists vec,
        nth_val 0 vl = Some (Vint32 vec) /\ *)
        opv = Some (Vint32 (Int.repr ENIVAL)) /\ 
        O2 = Some O1
  end.

Definition install_handler_6678_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
        exists vl' i prio handler param eventID inthandler newinthandler,
        vl = ((Vint32 i)::(Vint32 prio)::(Vint32 handler)::(param)::(Vint32 eventID)::vl') /\
        get O1 inthandlerid = Some (hinthandler inthandler) /\
        (forall x, if Int.eq x i then newinthandler x = Int.one else newinthandler x = inthandler x) /\
        O2 = Some(set O1 inthandlerid (hinthandler newinthandler)) /\
        opv = Some (Vint32 Int.zero) 
  end.

Definition install_handler_6678code (vl : vallist) :=
  install_fail (|vl|) ?? (int_enable_pic_aop(|nil|) ;; install_handler_6678_succ(|vl|)).

Definition install_handler_6678api:=(install_handler_6678code,(Tint32,Tint32::Tint32::Tint32::(Tptr Tvoid)::Tint32::nil)).*)

Lemma install_handler6678_err_return :
  forall P sch vec prio handler param eventID vl', 
    can_change_aop P ->
    isptr param ->
    absinfer sch ( <|| install_handler_6678code ((Vint32 vec)::(Vint32 prio)::(Vint32 handler)::(param)::(Vint32 eventID)::vl')||> ** P) 
            ( <|| END  (Some (Vint32 (Int.repr ENIVAL))) ||> ** P). 
Proof.
  intros.
  simpljoin.
  infer_solver 0%nat.
Qed.

Lemma install_handler6678_ier_return :
  forall P sch i i0 v'2 x0 i2 vl', 
    can_change_aop P ->
    absinfer sch ( <|| install_handler_6678code (Vint32 i :: Vint32 i0 :: Vint32 v'2 :: x0 :: Vint32 i2 :: vl') ||> ** P) 
            ( <|| int_enable_pic_aop(|nil|) ;; 
                  install_handler_6678_succ (|Vint32 i :: Vint32 i0 :: Vint32 v'2 :: x0 :: Vint32 i2 :: vl'|)||> ** P). 
Proof.
  unfold install_handler_6678code. intros.
  infer_branch 1%nat.
  (*eapply absinfer_trans.*)
  eapply absinfer_eq.
Qed.

Lemma install_handler6678_succ_return :
  forall P sch vl' i i0 v'3 x0 i2 inthandler newinthandler, 
    can_change_aop P ->
    (forall x, if Int.eq x i then newinthandler x = Int.one else newinthandler x = inthandler x) ->
    absinfer sch ( <|| install_handler_6678_succ (|Vint32 i :: Vint32 i0 :: Vint32 v'3 :: x0 :: Vint32 i2 :: vl'|)||> ** Hhinthandler inthandler ** P) 
            ( <|| END  (Some (Vint32 Int.zero)) ||> ** Hhinthandler newinthandler ** P).
Proof.
  intros. infer_part2.
Qed.

Lemma Install_handler6678Proof: 
  forall tid vl p r, 
    Some p = BuildPreA' os_api int_install_handler_6678 install_handler_6678api vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api int_install_handler_6678 install_handler_6678api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api int_install_handler_6678 = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init spec. (*Initialize Specification*)

  (*L1~L3 IF语句*)
  unfold CSL_GEM_IPC_LOCAL, CSL_GEM_TINTLN.
  hoare forward.
  destruct (Int.eq i2 ($ 1031)); simpl; intro; tryfalse.
  destruct (Int.eq i2 ($ 1032)); simpl; intro; tryfalse.
  destruct (Int.eq i2 ($ 1031)); destruct (Int.eq i2 ($ 1032)); simpl; intro; tryfalse.
  unfold ENIVAL.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply install_handler6678_err_return; eauto.
  go.
  eauto.
  int auto.

  (*i2 = 1031*)
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$ENIVAL)).
  destruct H3.
  symbolic_execution.
  sep pauto.
  sep cancel A_dom_lenv.
  sep cancel Aier.
  sep pauto.

  (*i2 = 1032*)
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$ENIVAL)).
  destruct H3.
  symbolic_execution.
  sep pauto.
  sep cancel A_dom_lenv.
  sep cancel Aier.
  sep pauto.

  (*i2 <> 1031 /\ i2 <> 1032*)
  assert (Int.unsigned i2 <> 1031 /\ Int.unsigned i2 <> 1032) as Hq.
  int auto.
  destruct H.
  simpl.
  int auto.

  (*L4~L6 IF语句*)
  hoare forward.
  pure intro. clear H.
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
  (*unfold isptr in H2.
  destruct H2. tryfalse. subst. *)
  eapply install_handler6678_err_return; eauto.
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

  (*L7~L9: If (handler ′ <ₑ ′ 0){RETURN ′ ENIVAL};ₛ*)
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
  apply install_handler6678_err_return; auto.
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
  apply install_handler6678_err_return; auto.
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

  (*handler′ > ′0情况*)
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
  eapply backward_rule1.
  intro.
  intros.
  clear H7 H8.
  sep lifts (3::nil)%nat in H9.

  exact H9.
  hoare abscsq.
  apply noabs_oslinv.
  apply install_handler6678_err_return.
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

  (*IntHandler ′ [vecnum ′ − ′ 5] =ₑ 1′;ₛ*)
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

  (*RINTP (vecnum);ₛ*)
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply install_handler6678_ier_return.
  go.
  unfold AOSInthandlerParam. go.
  unfold AOSExchandler. go.
  (*unfold aemp_isr_is. go.*)

  eapply backward_rule1.
  intro.
  intros.

  sep lifts(30::32::23::35::1::31::33::34::41::nil)%nat in H7.
  eapply elim_a_isr_is_prop in H7.
  eapply elim_aemp_isr_is_prop in H7.
  exact H7.

  eapply seq_rule.
  (*hoare lifts(1::2::3::4::5::6::38::7::nil)%nat pre.*)
  hoare lifts(3::1::6::4::2::5::7::10::nil)%nat pre.
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
  unfold p_local in H7.
  sep pauto.
  sep cancel LINV.
  simpl; auto.

  (*EXIT_CRITICAL;ₛ*)
  pure_auto.
  hoare unfold pre.
  hoare lifts(1::11::nil)%nat pre.
  new_hoare_abscsq.
  apply noabs_oslinv.
  eapply install_handler6678_succ_return.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold aemp_isr_is.
  can_change_aop_solver.
  
  instantiate (1:= (fun (x : int32) => if Int.eq x i then Int.one else v'23 x)).
  intros.
  assert (Int.eq x i = true \/ Int.eq x i = false) as Hx.  
  unfold vecMin. int auto. int auto.

  eapply backward_rule1.
  intro; intros.
  sep lifts (3::6::nil)%nat in H7.
  eapply add_a_isr_is_prop in H7.
  sep lifts (1::2::6::nil)%nat in H7.
  eapply add_aemp_isr_is_prop in H7.
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
  sep pauto.

  unfold ierupd.
  unfold HinthandlerToListval.
  unfold update_nth_val.
  unfold vecMin.
  unfold os_inv.ZToInt.
  unfold Int.ltu in H7.
  apply MatchHandler1. auto.
  pure_auto.
  go.
  hoare forward.
Qed.

Close Scope list_scope.
Close Scope Z_scope.
Local Close Scope int_scope.
Close Scope code_scope.



