Require Import ucos_include.
Require Import ios_int_ipc.
Require Import ios_int.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import ios_int_tac.
Require Import Lia.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Lemma dispatchisr_proof:
forall i ir er si p r ct lg,
  Some p = BuildintPre i int_spec ir er si I OSLInv ct lg->
  Some r = BuildintRet i int_spec ir er si I OSLInv ct lg->
  exists s,
    os_interrupt OSDispatchISR = Some s /\
    {| OS_spec , GetHPrio, OSLInv, I, retfalse, r ** (EX v, GV IntNumCurrent @ Tint32 |-r-> v)|}
    |-ct {{p **[|(Z.of_nat i) >= 5 /\ (Z.of_nat i) <= 15|] ** 
    GV IntNumCurrent @ Tint32 |-r-> Vint32(Int.repr (Z.of_nat i))}}s {{Afalse}}.
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
  pure intro.
  assert(i = 5%nat \/ i = 6%nat 
  \/ i = 7%nat \/ i = 8%nat
  \/ i = 9%nat \/ i = 10%nat
  \/ i = 11%nat \/ i = 12%nat
  \/ i = 13%nat \/ i = 14%nat
  \/ i = 15%nat ).
  lia.
  assert(int_spec i = Some userisr).
  destruct H3. rewrite H3. unfolds; auto.
  destruct H3. rewrite H3. unfolds; auto.
  destruct H3. rewrite H3. unfolds; auto.
  destruct H3. rewrite H3.  unfolds; auto.
  destruct H3. rewrite H3. unfolds; auto.
  destruct H3. rewrite H3. unfolds; auto.
  destruct H3. rewrite H3. unfolds; auto.
  destruct H3. rewrite H3. unfolds; auto.
  destruct H3. rewrite H3. unfolds; auto.
  destruct H3. rewrite H3. unfolds; auto.
  rewrite H3. unfolds; auto.


  (*i <> 6*)
  rewrite H4 in H1, H2.
  inverts H1.
  inverts H2.
  unfold invlth_noisr.
  unfold starinv_noisr.
  simpl.
  clear H3 H4.
  hoare lifts (1::3::4::5::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H1.
  exact H1.
  apply disj_rule.
  (*中断号为1的情况是false*)
  pure intro.
  assert(~(5 <= 1)) by auto.
  simpl in H.
  lia.
  (*中断号不为1*)
  pure intro.
  rename H1 into Hi_not_eq_1.
  unfold p_local.
  unfold LINV.
  unfold OSLInv.
  hoare unfold.
  rename v'16 into vcspace.
  rename v'17 into v17. 
  rename v'18 into v18. 
  rename v'19 into v19.
  
  rename v'20 into v'16. 
  rename v'21 into v'17. 
  rename v'22 into v'18. 
  rename v'23 into v'19. 
  rename v'24 into v'20. 
  

  hoare forward.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep lift 7%nat.
  apply disj_split.
  right.
  instantiate (1:=A_dom_lenv nil
        ** GV IntNumCurrent @ Int32u
        |-r-> Vint32 (Int.repr (Z.of_nat i))).
  Focus 4.

  isr_is_prop_help (i%nat) (si) (ir).
  clear H12.
  sep lifts (1::2::44::nil)%nat in H17.
  apply a_isr_is_prop_split in H17.
  sep split in H17.
  apply H24.
  assert(ct = v'10).
  unfold CurTid, AOSTCBList' in H1.
  sep lift 8%nat in H1.
  apply disj_split in H1.
  destruct H1.
  sep normal in H1. sep destruct H1.
  sep lift 6%nat in H1. sep split in H1.
  destruct H9. rewrite H21 in H1.

  sep lift 4%nat in H1.
  eapply read_only_merge_vptr in H1.
  destruct H1. auto.
  sep normal in H1. sep destruct H1.
  sep lift 7%nat in H1. sep split in H1.
  destruct H9. rewrite H18 in H1.
  sep lifts (1::3::nil)%nat in H1.
  eapply read_only_merge_vptr in H1.
  destruct H1. auto.
  rewrite <- H9 in H1. clear H9.
  sep lifts (14::15::12::nil)%nat in H1.
  apply a_isr_is_prop_split in H1.
  unfold p_local. unfold OSLInv.
  sep_cancel_unfold_solver.
  sep auto. apply H10.
  split;eauto.

  assert(ct = v'10).
  unfold CurTid, AOSTCBList' in H1.
  sep lift 9%nat in H1.
  apply disj_split in H1.
  destruct H1.
  sep normal in H1. sep destruct H1.
  sep lift 6%nat in H1. sep split in H1.
  destruct H9. rewrite H21 in H1.
  sep lift 4%nat in H1.
  eapply read_only_merge_vptr in H1.
  destruct H1. auto.

  sep normal in H1. sep destruct H1.
  sep lift 7%nat in H1. sep split in H1.
  destruct H9. rewrite H18 in H1.
  sep lift 3%nat in H1.
  eapply read_only_merge_vptr in H1.
  destruct H1. auto.
  rewrite H9. auto.
  auto. auto. good_frm_better_sovler.
  intros.
  sep auto.
  intros.
  sep auto.
  hoare unfold.
  rename v'51 into vcspace1.
  rename v'46 into v46. 
  rename v'47 into v47. 
  rename v'48 into v48.

  rename v'49 into v'46. 
  rename v'50 into v'47. 

  unfold AGVars.
  hoare forward.
  destruct (Int.eq v'58 (Int.repr 1)); auto.
  hoare forward.
  eapply disj_rule.
  pure intro.
  clear  H14 H15 H16 H17 H18 H19.
  inversion H9.
  unfold INT_NUM_MIN, INT_NUM_MAX.
  unfold IntInv.
  unfold AOSInthandler.
  hoare forward.
  int auto.
  int auto.
  int auto.
  int auto.
  int auto.
  apply v_leq_15_sub_5_le_11 . auto. auto.
  apply v_leq_15_sub_5_le_11. auto. auto.
  apply rule_type_val_match_help. auto. auto.
  apply val_inj_help1. auto. auto.
  apply val_inj_help2. auto. auto.
  apply val_inj_help3. auto. auto.
  hoare forward.
  instantiate(1:= A_dom_lenv nil ** 
  GV IntNumCurrent @ Int32u
  |-r-> (Vint32 (Int.repr (Z.of_nat v'25)))).
  clear H15 H16 H17.
  sep lift 27%nat in H14.
  unfold IntInv.
  sep normal. sep eexists.
  unfold_sep_cancel_helper.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  auto.
  auto.
  auto.
  good_frm_better_sovler.
  intros.
  sep auto.
  intros.
  sep auto.

  apply disj_rule.
  pure intro.
  clear H12 H13 H14 H25 H26.
  unfold fnullPost.
  unfold fnullPost'.
  unfold getasrt.
  pure intro.
  unfold IntInv.
  inversion H12.
  rewrite <- H19 in H13. rewrite H19 in Hi_not_eq_1.
  rename H19 into Hv28_neq_v70.
  clear H12 H16  H17 H18 H20 H21 H22 H23 H24 H25.
  unfold EvtInv.
  pure intro.
  eapply backward_rule1.
  intros.
  sep lift 49%nat in H15.
  apply disj_split in H15.
  destruct H15.
  sep split in H15. tryfalse.
  exact H15.
  pure intro.
  clear H15.
  (*change aop*)
  hoare_abscsq.

  apply noabs_oslinv.
  unfold userisr.
  eapply absimp_userisr.
  can_change_aop_solver'.
  eapply seq_rule.
  eapply eoint_ieoff_rule' with (id := (Int.repr (Z.of_nat v'19))).
  unfold INUM.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  auto.
  intros.
  sep lifts (49::9::50::51::52::55::nil)%nat in H15.
  assert(Z.to_nat
  (Int.intval (Int.repr (Z.of_nat v'19))) = v'19).
  apply Z_to_nat_help.
  auto. auto.
  rewrite H22.
  clear H22.
  exact H15.

  apply GoodI_I. 
  good_frm_sovler'.
  assert(Z.to_nat
  (Int.intval (Int.repr (Z.of_nat v'19))) = v'19).
  apply Z_to_nat_help.
  auto. auto.
  rewrite H15.
  rewrite  isrupd_true_false.
  clear H15.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  can_change_aop_solver'.
  can_change_aop_solver'.
  hoare forward.


  instantiate(1:= A_dom_lenv nil **  GV IntNumCurrent @ Int32u
  |-r-> Vint32 (Int.repr (Z.of_nat v'19)) ).
  sep lift 7%nat.
  apply disj_split.
  instantiate(9:=v'19).
  instantiate(11:=false).
  left.
  (*v'19*)
  unfold p_local in H15.
  unfold LINV in H15. unfold OSLInv in H15.
  sep normal in H15. sep destruct H15.
  sep_cancel_unfold_solver.
  unfold IntInv. unfold EvtInv.
  sep normal. sep eexists.
  sep lifts (64::nil)%nat. apply disj_split.
  right.
  unfold_sep_cancel_helper.
  sep semiauto; eauto.
  split; eauto.
  auto.
  clear -H13.
  unfold isr_is_prop in *.
  intros.
  apply H13 in H.
  unfold isrupd in *.
  destruct ( beq_nat v'19 x);auto.
  good_frm_sovler'.
  intros.
  sep auto.
  intros.
  sep auto.

  unfold OSIntExitIntPost.
  unfold OSIntExitPost_int .
  unfold getasrt.
  pure intro.

  eapply backward_rule1.
  intros.
  sep lift 7%nat in H24.
  apply disj_split in H24.
  destruct H24.
  sep lift 4%nat in H24.
  apply disj_split in H24.
  destruct H24.
  inversion H15. rewrite <- H29 in H24.
  sep split in H24. tryfalse.
  exact H24.
  sep normal in H24. sep split in H24.
  inverts H15. 
  apply astar_l_afalse_elim in H24. simpl in H24. tryfalse.
  eapply iret_rule'.
  intros.
  inverts H15.
  unfold p_local in H24.
  unfold OSLInv in H24.
  unfold LINV in H24.
  unfold AGVars in H24.
  unfold IntInv in H24.
  unfold EvtInv in H24.
  sep normal in H24. sep destruct H24. sep split in H24.
  sep normal. sep eexists. sep split.

  destruct H15. inversion e.
  rewrite <- H46 in H24.
  rewrite <- H46.
  clear H46 H47 H48 H49 H50.
  sep lift 8%nat.
  apply disj_split. right.
  sep lift 9%nat.
  apply disj_split. right.
  unfold A_isr_is_prop.
  sep normal. sep eexists.
  unfold AOSInthandler in H24.
  sep semiauto; eauto.
  rewrite H40, H42.
  auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto.
  auto. auto. auto.
  unfold EvtInv.
  pure intro.
  rename H12 into Hx. rename H13 into Hy. rename H14 into Hz.
  clear H32.
  hoare forward.

  pure intro.
  eapply backward_rule1.
  intros.
  sep lift 63%nat in H9.
  apply disj_split in H9.
  destruct H9.
  sep split in H9. tryfalse.
  exact H9.
  pure intro.
  clear H9.
  (*change aop*)
  hoare_abscsq.

  apply noabs_oslinv.
  unfold userisr.
  eapply absimp_userisr.


  can_change_aop_solver'.
  eapply eoint_ieoff_rule' with (id := (Int.repr (Z.of_nat v'25))).
  unfold INUM.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  Optimize Proof.
  Optimize Heap.
  rewrite max_unsigned_val.
  lia.
  auto.
  intros.
  sep lifts (62::9::63::64::65::67::nil)%nat in H9.
  assert(Z.to_nat
  (Int.intval (Int.repr (Z.of_nat v'25))) = v'25).
  apply Z_to_nat_help.
  auto. auto.
  rewrite H12.
  clear H12.
  exact H9.

  apply GoodI_I. 
  good_frm_sovler'.
  assert(Z.to_nat
  (Int.intval (Int.repr (Z.of_nat v'25))) = v'25).
  apply Z_to_nat_help.
  auto. auto.
  rewrite H9.
  rewrite  isrupd_true_false.
  clear H9.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  can_change_aop_solver'.
  can_change_aop_solver'.
  hoare forward.

  instantiate(1:= A_dom_lenv nil ** 
  GV IntNumCurrent @ Int32u |-r-> Vint32 (Int.repr (Z.of_nat v'25))).
  sep lift 7%nat.
  apply disj_split.
  instantiate(9:=v'25).
  instantiate(11:=false).
  left.
  unfold p_local in H9.
  unfold LINV in H9. unfold OSLInv in H9.
  unfold AGVars in H9.
  unfold IntInv. unfold EvtInv.
  sep normal in H9. sep destruct H9.
  sep_cancel_unfold_solver.
  sep normal. sep eexists.
  sep lift 64%nat. apply disj_split.
  right.
  unfold_sep_cancel_helper.
  sep semiauto; eauto.
  split; eauto.
  auto.
  clear -H10.
  unfold isr_is_prop in *.
  intros.
  apply H10 in H.
  unfold isrupd in *.
  destruct ( beq_nat v'25 x);auto.
  good_frm_sovler'.
  intros.
  sep auto.
  intros.
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
  inversion H9. rewrite <- H19 in H14.
  sep split in H14. tryfalse.
  exact H14.
  sep normal in H14. sep split in H14.
  inverts H9.
  apply astar_l_afalse_elim in H14. simpl in H14. tryfalse.
  eapply iret_rule'.
  intros.
  inverts H9.
  sep normal. sep eexists.
  sep lift 8%nat.
  apply disj_split. right.
  sep lift 14%nat.
  apply disj_split. right.
  unfold A_isr_is_prop.
  unfold p_local in H14.
  unfold OSLInv in H14.
  unfold LINV in H14.
  unfold AGVars in H14.
  unfold IntInv in H14.
  unfold EvtInv in H14.
  sep normal in H14. sep destruct H14. sep split in H14.
  rewrite H33 in H37.
  sep normal. sep eexists. sep split.
  sep_cancel_unfold_solver.
  destruct H9. inversion e.
  rewrite <- H43 in H14.
  rewrite <- H43.
  clear H43 H44 H45 H46 H47.
  unfold AOSInthandler in H14.
  sep semiauto; eauto.
  auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
  split; auto.
  auto. auto. auto. auto.
  auto. auto. auto. auto. auto.
  auto.  auto. auto.

  rewrite H36. rewrite H38. 
  auto.


  (*OSIntNesting != 1*)
  inversion H9.
  unfold INT_NUM_MIN, INT_NUM_MAX.
  unfold IntInv.
  unfold AOSInthandler.
  hoare forward.
  int auto.
  int auto.
  int auto.
  int auto.
  int auto.
  apply v_leq_15_sub_5_le_11 . auto. auto.
  apply v_leq_15_sub_5_le_11. auto. auto.
  apply rule_type_val_match_help. auto. auto.
  apply val_inj_help1. auto. auto.
  apply val_inj_help2. auto. auto.
  apply val_inj_help3. auto. auto.
  hoare forward.
  instantiate(1:= A_dom_lenv nil ** 
  GV IntNumCurrent @ Int32u
  |-r-> (Vint32 (Int.repr (Z.of_nat v'25)))).
  clear H13 H14 H15.
  sep lift 27%nat in H12.
  unfold IntInv.
  sep normal. sep eexists.
  unfold_sep_cancel_helper.
  sep auto.
  auto.
  auto.
  auto.
  good_frm_better_sovler.
  intros.
  sep auto.
  intros.
  sep auto.

  apply disj_rule.
  pure intro.
  clear H12 H23 H24.
  unfold fnullPost.
  unfold fnullPost'.
  unfold getasrt.
  pure intro.
  unfold IntInv.
  inversion H12.
  rewrite <- H19 in H13. rewrite H19 in Hi_not_eq_1.
  rename H19 into Hv28_neq_v70.
  clear H12 H16  H17 H18 H20 H21 H22 H23 H24 H25.
  unfold EvtInv.
  pure intro.
  eapply backward_rule1.
  intros.
  sep lift 49%nat in H15.
  apply disj_split in H15.
  destruct H15.
  sep split in H15. tryfalse.
  exact H15.
  pure intro.
  clear H15.
  (*change aop*)
  hoare_abscsq.

  apply noabs_oslinv.
  unfold userisr.
  eapply absimp_userisr.
  can_change_aop_solver'.
  eapply seq_rule.
  eapply eoint_ieoff_rule' with (id := (Int.repr (Z.of_nat v'19))).
  unfold INUM.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  Optimize Proof.
  Optimize Heap.
  rewrite max_unsigned_val.
  lia.
  auto.
  intros.
  sep lifts (49::9::50::51::52::55::nil)%nat in H15.
  assert(Z.to_nat
  (Int.intval (Int.repr (Z.of_nat v'19))) = v'19).
  apply Z_to_nat_help.
  auto. auto.
  rewrite H22.
  clear H22.
  exact H15.

  apply GoodI_I. 
  good_frm_sovler'.
  assert(Z.to_nat
  (Int.intval (Int.repr (Z.of_nat v'19))) = v'19).
  apply Z_to_nat_help.
  auto. auto.
  rewrite H15.
  rewrite  isrupd_true_false.
  clear H15.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  can_change_aop_solver'.
  can_change_aop_solver'.
  hoare forward.


  instantiate(1:= A_dom_lenv nil **  GV IntNumCurrent @ Int32u
  |-r-> Vint32 (Int.repr (Z.of_nat v'19)) ).
  sep lift 7%nat.
  apply disj_split.
  instantiate(9:=v'19).
  instantiate(11:=false).
  left.
  (*v'19*)
  unfold p_local in H15.
  unfold LINV in H15. unfold OSLInv in H15.
  sep normal in H15. sep destruct H15.
  sep_cancel_unfold_solver.
  unfold IntInv. unfold EvtInv.
  sep normal. sep eexists.
  sep lifts (64::nil)%nat. apply disj_split.
  right.
  unfold_sep_cancel_helper.
  sep semiauto; eauto.
  split; eauto.
  auto.
  clear -H13.
  unfold isr_is_prop in *.
  intros.
  apply H13 in H.
  unfold isrupd in *.
  destruct ( beq_nat v'19 x);auto.
  good_frm_sovler'.
  intros.
  sep auto.
  intros.
  sep auto.

  unfold OSIntExitIntPost.
  unfold OSIntExitPost_int .
  unfold getasrt.
  pure intro.

  eapply backward_rule1.
  intros.
  sep lift 7%nat in H24.
  apply disj_split in H24.
  destruct H24.
  sep lift 4%nat in H24.
  apply disj_split in H24.
  destruct H24.
  inversion H15. rewrite <- H29 in H24.
  sep split in H24. tryfalse.
  exact H24.
  sep normal in H24. sep split in H24.
  inverts H15. 
  apply astar_l_afalse_elim in H24. simpl in H24. tryfalse.
  eapply iret_rule'.
  intros.
  inverts H15.
  unfold p_local in H24.
  unfold OSLInv in H24.
  unfold LINV in H24.
  unfold AGVars in H24.
  unfold IntInv in H24.
  unfold EvtInv in H24.
  sep normal in H24. sep destruct H24. sep split in H24.
  sep normal. sep eexists. sep split.

  destruct H15. inversion e.
  rewrite <- H46 in H24.
  rewrite <- H46.
  clear H46 H47 H48 H49 H50.
  sep lift 8%nat.
  apply disj_split. right.
  sep lift 9%nat.
  apply disj_split. right.
  unfold A_isr_is_prop.
  sep normal. sep eexists.
  unfold AOSInthandler in H24.
  sep semiauto; eauto.
  rewrite H40, H42.
  auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto.
  auto. auto. auto.
  unfold EvtInv.
  pure intro.
  rename H30 into Hx. rename H31 into Hy. rename H12 into Hz.
  clear H32.
  hoare forward.

  pure intro.
  eapply backward_rule1.
  intros.
  sep lifts (61::nil)%nat in H9.
  apply disj_split in H9.
  destruct H9.
  sep split in H9. tryfalse.
  exact H9.
  pure intro.
  clear H9.
  (*change aop*)
  hoare_abscsq.

  apply noabs_oslinv.
  unfold userisr.
  eapply absimp_userisr.


  can_change_aop_solver'.
  eapply eoint_ieoff_rule' with (id := (Int.repr (Z.of_nat v'25))).
  unfold INUM.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  auto.
  intros.
  sep lifts (61::9::62::63::64::67::nil)%nat in H9.
  assert(Z.to_nat
  (Int.intval (Int.repr (Z.of_nat v'25))) = v'25).
  apply Z_to_nat_help.
  auto. auto.
  rewrite H12.
  clear H12.
  exact H9.

  apply GoodI_I. 
  good_frm_sovler'.
  assert(Z.to_nat
  (Int.intval (Int.repr (Z.of_nat v'25))) = v'25).
  apply Z_to_nat_help.
  auto. auto.
  rewrite H9.
  rewrite  isrupd_true_false.
  clear H9.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  can_change_aop_solver'.
  can_change_aop_solver'.
  hoare forward.

  instantiate(1:= A_dom_lenv nil ** 
  GV IntNumCurrent @ Int32u |-r-> Vint32 (Int.repr (Z.of_nat v'25))).
  sep lift 7%nat.
  apply disj_split.
  instantiate(9:=v'25).
  instantiate(11:=false).
  left.
  unfold p_local in H9.
  unfold LINV in H9. unfold OSLInv in H9.
  unfold AGVars in H9.
  unfold IntInv. unfold EvtInv.
  sep normal in H9. sep destruct H9.
  sep_cancel_unfold_solver.
  sep normal. sep eexists.
  sep lift 64%nat. apply disj_split.
  right.
  unfold_sep_cancel_helper.
  sep semiauto; eauto.
  split; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  clear -H10.
  unfold isr_is_prop in *.
  intros.
  apply H10 in H.
  unfold isrupd in *.
  destruct ( beq_nat v'25 x);auto.
  good_frm_sovler'.
  intros.
  sep auto.
  intros.
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
  inversion H9. rewrite <- H19 in H14.
  sep split in H14. tryfalse.
  exact H14.
  sep normal in H14. sep split in H14.
  inverts H9.
  apply astar_l_afalse_elim in H14. simpl in H14. tryfalse.
  eapply iret_rule'.
  intros.
  inverts H9.
  sep normal. sep eexists.
  sep lift 8%nat.
  apply disj_split. right.
  sep lift 14%nat.
  apply disj_split. right.
  unfold A_isr_is_prop.
  unfold p_local in H14.
  unfold OSLInv in H14.
  unfold LINV in H14.
  unfold AGVars in H14.
  unfold IntInv in H14.
  unfold EvtInv in H14.
  sep normal in H14. sep destruct H14. sep split in H14.
  rewrite H34 in H38.
  sep normal. sep eexists. sep split.
  sep_cancel_unfold_solver.
  destruct H9. inversion e.
  rewrite <- H44 in H14.
  rewrite <- H44.
  clear H44 H45 H46 H47 H48.
  unfold AOSInthandler in H14.
  sep semiauto; eauto.
  auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
  split; auto.
  auto. auto. auto. auto.
  auto. auto. auto. auto. auto.
  auto.  auto. auto.

  rewrite H37. rewrite H39. 
  auto. 
  Unshelve.
  all :exact spec_abort.
Qed.