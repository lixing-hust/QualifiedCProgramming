(*
Definition user_nmi_ISR_impl := 
  (*Void ·user_nmi_ISR·(⌞⌟)··{ *)
  user_nmi_ISR ↝ {
    (*⌞ y @ Int32 ⌟;*)

    (*DSP_C6x_Save(­);ₛ*)
    OSIntEnter(­);ₛ
    If(OSIntNesting′ ==ₑ ′1){
      (*y′ =ᶠ  DSP_C6x_GetCurrentSP(·);ₛ
      OSTCBCur′ → OSTCBStkPtr =ₑ 〈OS_STK ∗〉y′*)
       OSIntNesting′=ₑ′1
    };ₛ

    IF(exception_handler′ ==ₑ ′0){
      (*OSTaskSuspend(­ ′OS_PRIO_SELF ­)*)
      exception_handler′ =ₑ ′0(*;ₛ
      EOI(1)*)
    }ELSE{
      EXC_HANDLER(­)(*;ₛ
      Skip
      exception_handler′ =ₑ exception_handler′ +ₑ ′0*)
    };ₛ
    EOI(1);ₛ
    OSIntExit(­);ₛ
    (*DSP_C6x_Resume(­);ₛ*)
    IRET
}.
*)
Require Import ucos_include.
Require Import ios_int.
Require Import oscore_common.
Require Import ios_int_nmi.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Lia.
Require Import ios_int_tac.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Lemma isrupd_true_false:
  forall ir i,
    isrupd (isrupd ir i true) i false = isrupd ir i false.
Proof.
  intros.
  unfold isrupd.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_nat i x);auto.
Qed.

Lemma absimp_nmiisr:
forall P s sch,
  can_change_aop P ->
  absinfer sch
            ( <||usernmi_isr_spec (|nil|) ;; s||> ** P)
            ( <||END None;;s ||> ** P).
Proof.
intros.
apply absinfer_seq.
can_change_aop_solver.
can_change_aop_solver.
infer_solver 0%nat.
Qed.

Lemma usernmi_isr_proof:
forall ir er si p r ct lg,
  Some p = BuildintPre 1 int_spec ir er si I OSLInv ct lg->
  Some r = BuildintRet 1 int_spec ir er si I OSLInv ct lg->
  exists s,
    os_interrupt user_nmi_ISR = Some s /\ {| OS_spec , GetHPrio, OSLInv, I, retfalse, r |} |-ct
    {{p}} s {{Afalse}}.
Proof.
  intros.
  unfold BuildintPre in H.
  simpl in H.
  unfold ipreasrt' in H.
  inverts H.
  unfold  BuildintRet in H0.
  simpl in H0.
  unfold iretasrt' in H0.
  inverts H0.
  unfold os_interrupt.
  simpl.
  eexists.
  split.
  auto.
  unfold invlth_noisr.
  unfold starinv_noisr.
  simpl.

  hoare lifts (2::4::5::6::3::nil)%nat pre.
  eapply backward_rule1.
  intros.
  sep lifts (6::nil)%nat in H.
  apply disj_split in H.
  exact H.
  apply disj_rule.
  Focus 2.
  pure intro.
  try false.
  unfold p_local.
  unfold LINV.
  unfold OSLInv.
  hoare unfold.

  (*OSIntEnter (­)*)
  hoare forward.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep lift 8%nat.
  apply disj_split.
  left.
  instantiate (1:= A_dom_lenv nil).

  assert(ct = v'10).
  unfold CurTid, AOSTCBList' in H.
  sep lift 8%nat in H.
  apply disj_split in H.
  destruct H.
  sep normal in H. sep destruct H.
  sep lift 6%nat in H. sep split in H.
  destruct H1.
  rewrite H19 in H.
  sep lift 4%nat in H.
  eapply read_only_merge_vptr in H.
  destruct H. auto.
  sep normal in H. sep destruct H.
  sep lift 7%nat in H. sep split in H.
  destruct H1. rewrite H16 in H.
  sep lifts (1::3::nil)%nat in H.
  eapply read_only_merge_vptr in H.
  destruct H. auto.
  rewrite <- H1 in H.
  clear H1.
  sep lifts (18::15::13::nil)%nat in H.
  apply a_isr_is_prop_split in H.
  (* unfold APthreadAttr. *)
  (* sep cancel APthreadAttr. *)
  sep_cancel_unfold_solver.
  sep auto. apply H8.
  split; eauto.
  
  assert(ct = v'10).
  unfold CurTid, AOSTCBList' in H.
  sep lift 9%nat in H.
  apply disj_split in H.
  destruct H.
  sep normal in H. sep destruct H.
  sep lift 6%nat in H. sep split in H.
  destruct H1.
  rewrite H19 in H.
  sep lift 4%nat in H.
  eapply read_only_merge_vptr in H.
  destruct H. auto.
  sep normal in H. sep destruct H.
  sep lift 7%nat in H. sep split in H.
  destruct H1. rewrite H16 in H.
  sep lifts (1::3::nil)%nat in H.
  eapply read_only_merge_vptr in H.
  destruct H. auto.
  rewrite <- H1.
  auto. auto.
  (*isr_is_prop*)
  isr_is_prop_help (1%nat) (si) (ir).
  clear H14.
  sep lifts(1::2::44::nil)%nat in H15.
  apply a_isr_is_prop_split in H15.
  sep split in H15.
  apply H22. 
  auto.
  good_frm_sovler.

  intros.
  sep auto.
  intros.
  sep auto.
  (*开始第一个if*)
  hoare unfold.
  unfold AGVars.
  pure intro.
  rename H6 into HPrio.
  rename H7 into HPrioC.
  hoare forward.
  destruct (Int.eq v'66($ 1)); auto.
  pure intro.
  hoare forward.
  eapply disj_rule.
  pure intro.
  inversion H1.
  unfold IntInv.

  (*开始证明IF-ESLE*)  
  hoare forward.
  hoare_abscsq.
  apply noabs_oslinv.
  unfold usernmi_isr.
  eapply absimp_nmiisr.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  can_change_aop_solver.
  simpl; auto.
  unfold AOSExchandler.
  hoare forward;pure_auto.

  (*OSTaskSuspend*)
  hoare forward.
  instantiate(1:= A_dom_lenv nil).
  unfold AGVars.
  unfold IntInv.
  sep normal. sep eexists.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  sep lifts(39%nat::nil).
  eapply disj_split.
  left.
  sep normal.
  sep lifts(38%nat::nil) in H13.
  eapply disj_split in H13.
  destruct H13.
  sep normal in H13.
  sep cancel Aier.
  sep auto.
  sep normal in H13.
  sep split in H13.
  tryfalse.
  auto.
  auto.
  apply H.
  good_frm_sovler.
  intros.
  sep auto.
  intros.
  sep auto.

  (*开始证明ELSE中内容*)
  hoare forward.
  instantiate(1:= A_dom_lenv nil).
  unfold AOSExchandler.
  unfold AGVars.
  unfold IntInv.
  sep normal. sep eexists.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  sep auto.
  auto.
  auto.
  apply H.
  good_frm_sovler.
  intros.
  sep auto.
  intros.
  sep auto.

  (*EOI*)
  apply disj_rule.
  hoare unfold.
  unfold OSTaskSuspendPost.
  unfold OSTaskSuspendPost'.
  unfold getasrt.
  pure intro.
  inversion H14.
  hoare lifts (24::nil)%nat pre.
  hoare forward.
  eapply eoi_ieoff_rule'.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  auto. 
  intros.
  sep lift 20%nat in H17.
  eapply disj_split in H17.
  destruct H17.
  sep normal in H17.
  sep lifts(21::2::22::23::24::nil)%nat in H17.
  exact H17.
  sep split in H17.
  tryfalse.
  apply GoodI_I. 
  good_frm_sovler.
(*   unfold p_local.
  good_frm_sovler.
  unfold CurTid; good_frm_sovler.
  unfold LINV; unfold OSLInv;
  good_frm_sovler. *)

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  go.
  go.
  hoare forward.
  instantiate(1:= A_dom_lenv nil).
  sep cancel Aop.
  sep cancel Acs.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Aisr.
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep cancel Aier.
  sep lifts(2%nat::nil).
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep auto.
  auto.
  rewrite isrupd_true_false.
  clear -H15.
  unfold isr_is_prop in *.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))).
  auto.
  rewrite H in H15.
  clear H.
  intro.
  intro. 
  apply H15 in H.
  unfold isrupd in *.
  destruct ( beq_nat (Z.to_nat (Int.unsigned ($ 1))) x);auto.
  auto.
  good_frm_sovler.
  intro.
  intro.
  sep normal in H17.
  sep destruct H17.
  sep lifts (3::nil)%nat in H17.
  eapply disj_split in H17.
  destruct H17.
  sep split in H17.
  sep auto.
  sep split in H17.
  inversion H20.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))) by auto.
  tryfalse.
  sep auto.

  (*IRET*)
  unfold OSIntExitIntPost.
  unfold OSIntExitPost_int.
  unfold getasrt.
  pure intro.

  eapply backward_rule1.
  intros.
  sep lift 7%nat in H14.
  apply disj_split in H14.
  destruct H14.
  sep lift 4%nat in H14.
  apply disj_split in H14.
  destruct H14.
  exact H14.
  inversion H17. rewrite <- H22 in H14.
  sep split in H14.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))) by auto.
  tryfalse.
  sep normal in H14. sep split in H14.
  inverts H17. 
  apply astar_l_afalse_elim in H14. simpl in H14. tryfalse.

  eapply iret_rule'.
  intros.
  inverts H17.
  unfold p_local in H14.
  unfold OSLInv in H14.
  unfold LINV in H14.
  unfold AGVars in H14.
  unfold IntInv in H14.
  sep normal in H14. sep destruct H14. sep split in H14.
  sep normal.
  sep eexists.
  sep split.
  sep lift 7%nat.
  eapply disj_split.
  right.
  sep lift 8%nat.
  eapply disj_split.
  left.
  destruct H17.
  inversion e.
  unfold A_isr_is_prop.
  sep normal.
  sep eexists.
  sep split.
  sep auto.
  rewrite H22 in H28.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  rewrite H27.
  rewrite H29.
  auto.
  auto.
  auto.
  auto.
  rewrite H27.
  apply isrupd_true_false.
  auto.
  auto.
  auto.

  (*开始证明ELSE对应分支*)
  hoare unfold.
  unfold EXC_HANDLERPost.
  unfold EXC_HANDLERPost'.
  unfold getasrt.
  pure intro.
  inversion H14.
  hoare lifts (24::nil)%nat pre.
  hoare forward.
  eapply eoi_ieoff_rule'.
  unfold INUM.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  auto. 
  intros.
  sep lift 20%nat in H17.
  eapply disj_split in H17.
  destruct H17.
  sep normal in H17.
  sep lifts(21::2::22::23::24::nil)%nat in H17.
  exact H17.
  sep split in H17.
  tryfalse.
  apply GoodI_I. 
  good_frm_sovler.
(*   unfold p_local.
  good_frm_sovler.
  unfold CurTid. good_frm_sovler.
  unfold LINV. unfold OSLInv.
  good_frm_sovler. *)

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  go.
  go.
  hoare forward.
  instantiate(1:= A_dom_lenv nil).

  sep normal. sep eexists.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  sep lifts(6::nil)%nat.
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep cancel Aier.
  sep lifts(2::nil)%nat.
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep auto.
  auto.
  rewrite isrupd_true_false.
  clear -H8.
  unfold isr_is_prop in *.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))).
  auto.
  rewrite H in H8.
  clear H.
  intro.
  intro. 
  apply H8 in H.
  unfold isrupd in *.
  destruct ( beq_nat (Z.to_nat (Int.unsigned ($ 1))) x);auto.
  good_frm_sovler.
  intro.
  intro.
  sep normal in H17.
  sep destruct H17.
  sep split in H17.
  sep auto.
  sep auto.
  
  (*IRET*)
  unfold OSIntExitIntPost.
  unfold OSIntExitPost_int .
  unfold getasrt.
  pure intro.

  eapply backward_rule1.
  intros.
  sep lift 7%nat in H14.
  apply disj_split in H14.
  destruct H14.
  sep lift 4%nat in H14.
  apply disj_split in H14.
  destruct H14.
  exact H14.
  inversion H17. rewrite <- H22 in H14.
  sep split in H14.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))) by auto.
  tryfalse.
  sep normal in H14. sep split in H14.
  inverts H17. 
  apply astar_l_afalse_elim in H14. simpl in H14. tryfalse.

  hoare unfold.
  inversion H17.
  eapply iret_rule'.
  intros.
  unfold A_isr_is_prop.
  unfold p_local in H18.
  unfold OSLInv in H18.
  unfold LINV in H18.
  unfold AGVars in H18.
  unfold IntInv in H18.
  sep normal in H18. sep destruct H18. sep split in H18.
  sep normal.
  sep eexists.
  sep split.
  sep lift 7%nat.
  eapply disj_split.
  right.
  sep lift 8%nat.
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep split.
  sep auto.
  auto.
  auto.
  auto.
  auto.
  lia.
  auto.
  auto.
  auto.
  rewrite H35.
  rewrite H37.
  inversion H17.
  rewrite H42.
  auto.
  auto.
  auto.
  auto.
  rewrite H35.
  eapply isrupd_true_false.
  auto.
  auto. 
  auto.

  (*OSIntNesting != 1*)
  inversion H1.
  unfold IntInv.
  pure intro.
  hoare forward.
  hoare_abscsq.
  apply noabs_oslinv.
  unfold usernmi_isr.
  eapply absimp_nmiisr.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  can_change_aop_solver.
  simpl.
  auto.
  unfold AOSExchandler.
  hoare forward;pure_auto.

  (*开始证明IF中内容*)
  hoare forward.
  instantiate(1:= A_dom_lenv nil).
  unfold AGVars.
  unfold IntInv.
  sep normal. sep eexists.
  sep auto.
  apply H21.
  apply H24.
  apply H22.
  auto.
  auto.
  auto.
  good_frm_sovler.
  intros.
  sep auto.
  intros.
  sep auto.

  (*开始证明ELSE中内容*)
  hoare forward.
  instantiate(1:= A_dom_lenv nil).
  unfold AGVars.
  unfold IntInv.
  sep normal.
  sep eexists.
  sep auto.
  apply H19.
  apply H22.
  apply H20.
  auto.
  auto.
  apply H.
  good_frm_sovler.
  intros.
  sep auto.
  intros.
  sep auto.
  apply disj_rule.

  (*IF对应分支*)
  hoare unfold.
  unfold OSTaskSuspendPost.
  unfold OSTaskSuspendPost'.
  unfold getasrt.
  pure intro.
  inversion H14.
  hoare lifts (24::nil)%nat pre.
  hoare forward.
  eapply eoi_ieoff_rule'.
  unfold INUM.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  auto. 
  intros.
  sep lifts(20::nil)%nat in H17.
  eapply disj_split in H17.
  destruct H17.
  sep normal in H17.
  sep lifts(21::2::22::23::24::nil)%nat in H17.
  exact H17.
  sep split in H17.
  tryfalse.
  apply GoodI_I. 
  good_frm_sovler.
(*   unfold p_local.
  good_frm_sovler.
  unfold CurTid. good_frm_sovler.
  unfold LINV. unfold OSLInv.
  good_frm_sovler.   *)

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  go.
  go.
  hoare forward.
  instantiate(1:= A_dom_lenv nil).
  sep normal. sep eexists.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  sep lifts (6::nil)%nat.
  eapply disj_split.
  left.
  sep normal.
  sep cancel Aier.
  sep lifts(2::nil)%nat.
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep auto.
  auto.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))) by auto.
  rewrite <-H25.
  rewrite isrupd_true_false.
  clear -H15.
  unfold isr_is_prop in *.
  intro.
  intro. 
  apply H15 in H.
  unfold isrupd in *.
  destruct ( beq_nat 1%nat x);auto.
  good_frm_sovler.
  intro.
  intro.
  sep normal in H17.
  sep destruct H17.
  sep split in H17.
  sep auto.
  sep auto.

  unfold OSIntExitIntPost.
  unfold OSIntExitPost_int .
  unfold getasrt.
  pure intro.

  eapply backward_rule1.
  intros.
  sep lift 7%nat in H14.
  apply disj_split in H14.
  destruct H14.
  sep lift 4%nat in H14.
  apply disj_split in H14.
  destruct H14.
  exact H14.
  inversion H17. rewrite <- H22 in H14.
  sep split in H14.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))) by auto.
  tryfalse.
  sep normal in H14. sep split in H14.
  inverts H17. 
  apply astar_l_afalse_elim in H14. simpl in H14. tryfalse.

  hoare unfold.
  inversion H17.
  eapply iret_rule'.
  intros.
  unfold A_isr_is_prop.
  unfold p_local in H18.
  unfold OSLInv in H18.
  unfold LINV in H18.
  unfold AGVars in H18.
  unfold IntInv in H18.
  sep normal in H18. sep destruct H18. sep split in H18.
  sep normal.
  sep eexists.
  sep split.
  sep lift 7%nat.
  eapply disj_split.
  right.
  sep lift 8%nat.
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep auto.
  rewrite H35.
  rewrite H37.
  auto.
  auto.
  auto.
  auto.
  rewrite isrupd_true_false in H35.
  auto.
  auto.
  auto.
  auto.

  (*ELSE对应分支*)
  hoare unfold.
  unfold EXC_HANDLERPost.
  unfold EXC_HANDLERPost'.
  unfold getasrt.
  pure intro.
  inversion H12.
  hoare lifts (24::nil)%nat pre.
  hoare forward.
  eapply eoi_ieoff_rule'.
  unfold INUM.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  auto. 
  intros.
  sep lifts(20::nil)%nat in H15.
  eapply disj_split in H15.
  destruct H15.
  sep normal in H15.
  sep lifts(21::2::22::23::24::nil)%nat in H15.
  exact H15.
  sep split in H15.
  tryfalse.
  apply GoodI_I. 
  good_frm_sovler.
(*   unfold p_local.
  good_frm_sovler.
  unfold CurTid. good_frm_sovler.
  unfold LINV. unfold OSLInv.
  good_frm_sovler. *)

  (*OSIntExit*)
  eapply abscsq_rule'.
  apply noabs_oslinv.
  inversion H12.
  eapply absinfer_seq_end;eauto.
  go.
  go.
  hoare forward.
  instantiate(1:= A_dom_lenv nil).

  sep normal. sep eexists.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  sep lifts(6::nil)%nat.
  eapply disj_split.
  left.
  sep cancel Aier.
  sep lifts(2::nil)%nat.
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep auto.
  auto.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))); auto.
  rewrite <-H23.
  rewrite isrupd_true_false.
  clear -H13.
  unfold isr_is_prop in *.
  intro.
  intro. 
  apply H13 in H.
  unfold isrupd in *.
  destruct ( beq_nat 1%nat x);auto.
  auto.
  good_frm_sovler.
  intro.
  intro.
  sep normal in H15.
  sep destruct H15.
  sep split in H15.
  sep auto.
  sep auto.
  
  (*IRET*)
  unfold OSIntExitIntPost.
  unfold OSIntExitPost_int .
  unfold getasrt.
  pure intro.

  eapply backward_rule1.
  intros.
  sep lift 7%nat in H12.
  apply disj_split in H12.
  destruct H12.
  sep lift 4%nat in H12.
  apply disj_split in H12.
  destruct H12.
  exact H12.
  inversion H15. rewrite <- H22 in H12.
  sep split in H12.
  assert(1%nat = Z.to_nat (Int.unsigned ($ 1))) by auto.
  tryfalse.
  sep normal in H12. sep split in H12.
  inverts H17. 
  apply astar_l_afalse_elim in H12. simpl in H12. tryfalse.

  hoare unfold.
  inversion H15.
  hoare unfold.
  eapply iret_rule'.
  intros.
  unfold A_isr_is_prop.
  unfold p_local in H16.
  unfold OSLInv in H16.
  unfold LINV in H16.
  unfold AGVars in H16.
  unfold IntInv in H16.
  sep normal in H16. sep destruct H16. sep split in H16.
  sep normal.
  sep eexists.
  sep split.
  sep lift 7%nat.
  eapply disj_split.
  right.
  sep lift 8%nat.
  eapply disj_split.
  left.
  sep normal.
  sep eexists.
  sep auto.
  rewrite H22.
  rewrite H24.
  apply H26.
  auto.
  auto.
  auto.
  rewrite isrupd_true_false in H22.
  auto.
  auto.
  auto.
  auto.
  Unshelve.
  all :exact spec_abort.
Qed.

Close Scope code_scope.
Close Scope list_scope.
Close Scope Z_scope.
