(*
Definition int_unstall_handler_6678_impl :=
Int32 ·int_unstall_handler_6678·(⌞ vecnum @ Int32 ⌟)··{
  ⌞  ⌟;
  If(vecnum′ <ₑ ′INT_NUM_MIN ||ₑ vecnum′ >ₑ ′INT_NUM_MAX){
    RETURN ′ENIVAL(*返回ENIVAL(定义为22)，表示安装中断失败*)
	};ₛ 
  ENTER_CRITICAL;ₛ
  OSIntHandler′[vecnum′ − ′INT_NUM_MIN] =ₑ NULL;ₛ
  DINTP (vecnum);ₛ
  EXIT_CRITICAL;ₛ
  RETURN ′0
}·.
*)
Require Import ucos_include.
Require Import ios_int.
Require Import int_lock.
(*Require Import oscore_common.*)
Require Import ios_int_tick.
Require Import ios_int_tac.
Require Import symbolic_lemmas.
Require Import dintpProof.
(*Require Import ios_int_tick_ifunspec.*)
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

Lemma Unstall_handler6713_err_return :
  forall P sch i vl', 
    can_change_aop P ->
    absinfer sch ( <|| unstall_handler_6713code (Vint32 i :: vl')||> ** P) 
            ( <|| END  (Some (Vint32 (Int.repr ENIVAL))) ||> ** P). 
Proof.
  intros.
  simpljoin.
  infer_solver 0%nat.
  exists i. auto.
Qed.

Lemma Unstall_handler6713_ier_return :
  forall P sch i vl', 
    can_change_aop P ->
    absinfer sch ( <|| unstall_handler_6713code (Vint32 i :: vl') ||> ** P) 
            ( <|| int_disable_pic_aop (|nil|);; unstall_6713_succ (|Vint32 i :: vl'|)||> ** P). 
Proof.
  unfold unstall_handler_6713code. intros.
  infer_branch 1%nat.
  (*eapply absinfer_trans.*)
  eapply absinfer_eq.
Qed.

Lemma Unstall_handler6713_succ_return :
  forall P sch i inthandler newinthandler vl', 
    can_change_aop P ->
    (forall x, if Int.eq x i then newinthandler x = Int.zero else newinthandler x = inthandler x) ->
    absinfer sch ( <|| unstall_6713_succ (|Vint32 i :: vl'|) ||> ** Hhinthandler inthandler ** P) 
            ( <|| END  (Some (Vint32 Int.zero))||> ** Hhinthandler newinthandler ** P). 
Proof.
  intros.
  infer_part2.
Qed.

Lemma FiveEqual:
  forall i, (Int.unsigned i = 5) -> (Int.unsigned ($ 5) = 5).
Proof.
  intros. auto.
Qed.

Lemma Unstall_handler6713Proof: 
  forall tid vl p r, 
    Some p = BuildPreA' os_api int_unstall_handler_6713 unstall_handler_6713api vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api int_unstall_handler_6713 unstall_handler_6713api vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api int_unstall_handler_6713 = Some (t, d1, d2, s) /\
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
  eapply Unstall_handler6713_err_return; eauto.
  go.
  int auto.

  (*i < 5*)
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$ENIVAL)).
  destruct H2.
  symbolic_execution.
  sep pauto.
  sep cancel A_dom_lenv.
  sep cancel Aier.
  sep pauto.

  (*i > 15*)
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$ENIVAL)).
  destruct H2.
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
  
  (*L6: DINTP (vecnum);ₛ*)
  (*unfold unstall_handler_6713code.*)
  hoare abscsq.
  apply noabs_oslinv.
  eapply Unstall_handler6713_ier_return.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold aemp_isr_is. go.

  eapply backward_rule1.
  intro.
  intros.
  sep lifts (15::36::nil)%nat in H4.

  instantiate(1:=(
    <|| int_disable_pic_aop (|nil|);; unstall_6713_succ (|Vint32 i :: v'|) ||> **
      Aisr empisr **
      Aier v'0 **
      Aie false **
      Ais nil **
      Acs (true :: nil) **
      Hhier v'21 **    
    (
        AOSRdyTblGrp v'7 v'8 **
        LV vecnum @ long |-> Vint32 i **
        A_dom_lenv ((vecnum ↝ {long}) :: nil) **
        GAarray IntHandler (Tarray long 11) (update_nth_val (Z.to_nat (Int.unsigned (i -ᵢ $ 5))) (HinthandlerToListval v'22) (V$ 0)) **
        Hhinthandler v'22 **
        HhinthandlerParam v'23 **
        AOSInthandlerParam v'23 **
        AOSExchandler (Vint32 v'24) **
        Hhexchandler v'24 **
        AOSMapTbl **
        AOSUnMapTbl **
        AOSTCBPrioTbl v'1 v'7 v'10 v'15 v'12 **
        AOSTCBList v'2 v'3 v'4 (v'5 :: v'6) v'7 tid v'10 **
        AOSTCBFreeList v'13 v'14 **
        AOSTime (Vint32 v'11) **
        HTCBList v'10 **
        HTime v'11 **
        HCurTCB tid **
        AGVars **
        APthreadAttr v'16 **
        EvtInv v'9 v'2 (v'4 ++ v'5 :: v'6) v'10 v'12 v'18 v'19 v'20 **
        TmrInv **
        CoreCommuInv v'9 **
        PartitionInv v'9 **
        CapabilityInv v'17 **
        tcbdllflag v'2 (v'4 ++ v'5 :: v'6) **
        p_local OSLInv tid
          (logic_val (V$ 1) :: logic_val (V$ inferules.__EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) 
    )
  )).

  sep lifts (2::5:: nil)%nat.
  eapply elim_a_isr_is_prop.
  eapply elim_aemp_isr_is_prop.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aier.
  sep cancel A_isr_is_prop.
  sep cancel aemp_isr_is.
  sep cancel A_dom_lenv.
  sep pauto.

  eapply seq_rule.
  hoare lifts(1::2::3::4::5::6::9::7::nil)%nat pre.
  eapply dintp_rule'; eauto.
  go.
  (*unfold AOSInthandler. go.*)
  unfold AOSInthandlerParam. go.
  unfold AOSExchandler. go.
  unfold p_local. go.
  unfold CurTid. go.
  unfold LINV. go.
  unfold OSLInv. go.
  intro. intros.
  unfold CurLINV.
  unfold LINV.
  unfold CurTid.
(*   unfold p_local in H4. *)
  sep pauto.
(*   sep cancel LINV. *)
(*   simpl; auto. *)

  (*L7: EXIT_CRITICAL;ₛ*)
  pure_auto.
  hoare lifts(12 :: nil)%nat pre.
  hoare unfold pre.
  new_hoare_abscsq.
  apply noabs_oslinv.
  
  eapply Unstall_handler6713_succ_return.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold aemp_isr_is.
  can_change_aop_solver.

  instantiate (1:= (fun (x : int32) => if Int.eq x i then Int.zero else v'22 x)).
  intros.
  assert (Int.eq x i = true \/ Int.eq x i = false) as Hx.  
  unfold vecMin. int auto. int auto.

  eapply backward_rule1.
  intro; intros.
  sep lifts (3::6::nil)%nat in H4.
  eapply add_a_isr_is_prop in H4.
  sep lifts (1::2::6::nil)%nat in H4.
  eapply add_aemp_isr_is_prop in H4.
  eauto.
  hoare lift 6%nat pre.

  hoare normal pre. hoare_ex_intro.
  eapply seq_rule.
  (*hoare_forward_prim'.*)
  hoare_forward_prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold IntInv.
  unfold AOSInthandler.
  sep cancel EvtInv.
  sep cancel Aier.
  sep cancel p_local.
  sep pauto.
  unfold ierupd.
  unfold HinthandlerToListval.
  unfold update_nth_val.
  unfold vecMin.
  unfold os_inv.ZToInt. 
  unfold Int.ltu in H4. 
  apply MatchHandler0. auto.
  auto.
  pure_auto.
  hoare forward.
Qed.

Close Scope list_scope.
Close Scope Z_scope.
Local Close Scope int_scope.
Close Scope code_scope.



