(*
Definition int_unstall_handler_6678_impl :=
Int32 ·int_unstall_handler_6678·(⌞ vecnum @ Int32 ⌟)··{
  ⌞  ⌟;
  If(vecnum′ <ₑ ′INT_NUM_MIN ||ₑ vecnum′ >ₑ ′INT_NUM_MAX){
    RETURN ′ENIVAL(*返回ENIVAL(定义为22)，表示安装中断失败*)
	};ₛ 
  ENTER_CRITICAL;ₛ
  OSIntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ NULL;ₛ
  EXIT_CRITICAL;ₛ
  RETURN ′0
}·.
*)
Require Import ucos_include.
Require Import ios_int.
Require Import ios_int_tac.
Require Import symbolic_lemmas.
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

Lemma Unstall_handler6678_err_return :
  forall P sch i vl', 
    can_change_aop P ->
    (*((Int.ltu i vecMin = true) \/ (Int.ltu vecMax i = true)) ->*)
    absinfer sch ( <|| unstall_handler_6678code (Vint32 i :: vl')||> ** P) 
            ( <|| END  (Some (Vint32 (Int.repr ENIVAL))) ||> ** P). 
Proof.
  intros.
  simpljoin.
  infer_solver 0%nat.
  exists i. auto.
Qed.

Lemma Unstall_handler6678_succ_return :
  forall P sch i inthandler newinthandler vl', 
    can_change_aop P ->
    (*(Int.ltu i vecMin = false) /\ (Int.ltu vecMax i = false) -> *)
    (*newinthandler = (fun (x : int32) => if Int.eq x (i -ᵢ vecMin) then Int.zero else inthandler x) -> *)
    (forall x, if Int.eq x i then newinthandler x = Int.zero else newinthandler x = inthandler x) ->
    (*update_nth_val (Z.to_nat (Int.unsigned (i -ᵢ vecMin))) (HinthandlerToListval inthandler) (V$ 0) = HinthandlerToListval newinthandler -> *)
    absinfer sch ( <|| unstall_handler_6678code (Vint32 i :: vl')||> ** Hhinthandler inthandler ** P) 
                 ( <|| END  (Some (Vint32 Int.zero)) ||> ** Hhinthandler newinthandler ** P). 
Proof.
  intros.
  simpljoin.
  infer_solver 1%nat.
Qed.

Definition vl : vallist := V$0::V$1::nil.
Definition V (vl:vallist) := nth_val 0 vl.
Definition vl' := update_nth_val 1 vl (V$0).
Definition x := nth_val 1 vl'.

Lemma Unstall_handler6678Proof: 
  forall tid vl p r, 
    Some p = BuildPreA' os_api int_unstall_handler_6678 unstall_handler_6678api vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api int_unstall_handler_6678 unstall_handler_6678api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api int_unstall_handler_6678 = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  init spec. (*Initialize Specification*)

  (*L1:  OS_ENTER_CRITICAL();
  hoare forward prim; pauto.*)

  (*L1~L3 IF语句*)
  unfold INT_NUM_MIN, INT_NUM_MAX.
  hoare unfold.
  hoare forward.
  destruct (Int.ltu i (Int.repr 5)); simpl; intro; tryfalse.
  destruct (Int.ltu (Int.repr 15) i); simpl; intro; tryfalse.
  destruct (Int.ltu i (Int.repr 5)); destruct (Int.ltu (Int.repr 15) i); simpl; intro; tryfalse.  
  unfold ENIVAL.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply Unstall_handler6678_err_return; eauto.
  go.
  int auto.

  (*i < 5*)
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$ENIVAL)).
  destruct H2.
  symbolic_execution.
  sep pauto.
  (* sep cancel A_dom_lenv. *)
  sep cancel Aier.
  sep pauto.

  (*i > 15*)
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$ENIVAL)).
  destruct H2.
  symbolic_execution.
  sep pauto.
  (* sep cancel A_dom_lenv. *)
  sep cancel Aier.
  sep pauto.

  (*5 <= i <= 15*)
  assert (Int.ltu i ($ 5) = false /\ Int.ltu ($ 15) i = false) as Hq.
  int auto.
  destruct H.
  simpl.
  int auto.

  (*L4:  OS_ENTER_CRITICAL();*)
  (*清除Afalse分支*)
  hoare forward. 
  pure intro.
  hoare forward prim; pauto.
  hoare unfold.
  hoare normal pre.
  hoare unfold.
  assert (5 <= Int.unsigned i /\ Int.unsigned i <= 15) as Hq.
  clear -H.
  int auto. 
  destruct H; simpl in H; tryfalse.
  destruct H; simpl in H; tryfalse.

  (*L5：IntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ NULL;ₛ*)
  (*destruct H as [Ha1 | Ha2].
  destruct Ha1 as [Ha3 | Ha4].*)
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
  rewrite H4.
  int auto.
  int auto.
  clear; pauto.
  apply assign_type_match_true.
  simpl; auto.
  assert (Z.of_nat (length (HinthandlerToListval v'22)) = 11).
  int auto.
  rewrite H4.
  int auto.
  int auto.
  {
    intro; intros.
    sep normal in H4.
    sep destruct H4.
    sep eexists.
    sep cancel p_local.
    simpl; auto.
  }

  (*L6: EXIT_CRITICAL;ₛ*)
  pure_auto.
  hoare lifts (1::5::nil)%nat pre.
  hoare unfold pre.
  new_hoare_abscsq.
  apply noabs_oslinv.
  eapply Unstall_handler6678_succ_return.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold aemp_isr_is.
  can_change_aop_solver.

  instantiate (1:= (fun (x : int32) => if Int.eq x i then Int.zero else v'22 x)).
  intros.
  assert (Int.eq x0 i = true \/ Int.eq x0 i = false) as Hx.  
  unfold vecMin. int auto. int auto.

  hoare normal pre. hoare_ex_intro.
  eapply seq_rule.
  (*hoare_forward_prim'.*)
  hoare_forward_prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel EvtInv.
  unfold IntInv.
  unfold AOSInthandler.
  sep cancel p_local.
  sep cancel Aier.
  sep pauto.
  unfold HinthandlerToListval.
  unfold update_nth_val.
  unfold vecMin.
  unfold os_inv.ZToInt. 
  unfold Int.ltu in H2. 

  apply MatchHandler0. auto.
  auto.
  pure_auto.
  hoare forward.
Qed.

Close Scope list_scope.
Close Scope Z_scope.
Local Close Scope int_scope.
Close Scope code_scope.
