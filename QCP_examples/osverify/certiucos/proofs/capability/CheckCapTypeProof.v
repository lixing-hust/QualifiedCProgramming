Require Import gjb_common.
Require Import Aarray_new_common.
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import Lia.
Require Import ACSpace_defs.
Require Import seplog_trm_tacs.
Require Import CapSpec.
Require Import CheckCapTypePure.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Set Nested Proofs Allowed.



Lemma Check_Cap_Type_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal Check_Cap_Type
                  vl logicl Check_Cap_TypePre ct->
      Some r =
      BuildRetI os_internal Check_Cap_Type vl logicl Check_Cap_TypePost ct->
      exists t d1 d2 s,
      os_internal Check_Cap_Type = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
  init spec.
  rename H8 into Hv'2range.
  simpl in H, H0, H4.
  inverts H.
  inverts H0.
  inverts H4.

  (*If (func_capType ′ ==ₑ ′ CAP_FUNCTION_TYPE)*)  
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop).
  eapply ift_rule'.
  intros.
  sep_lifts_trms_in H (Alvarmapsto func_capType). 
  eapply bop_rv.
  eapply LV_to_Rv in H. 
  eapply inline_tactics.monoasrt_mono in H.
  exact H. eapply inline_tactics.Rv_mono.
  auto. simpl. 
  change Byte.max_unsigned with 255.
  assert(Int.unsigned v'1 <=? 255 = true). int auto.
  rewrite H0. auto.
  destruct_s s. simpl. split; eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq. 
  destruct (Int.eq v'1 ($ CAP_FUNCTION_TYPE)); eauto.
  simpl. eauto.

  hoare_split_pure_all.
  (*IF (func_capability ′ ≤ ′ CAP_CHANNEL_CLASS)
  {RETURN ′ func_capability}
  ELSE {RETURN 〈 long 〉 ′ SLOT_NUM}*)
  eapply if_rule2'.
  intros.
  eapply bop_rv.
  eapply bop_rv.
  sep_lifts_trms_in H0 (Alvarmapsto func_capability).
  eapply LV_to_Rv in H0. 
  eapply inline_tactics.monoasrt_mono in H0.
  exact H0.
  eapply inline_tactics.Rv_mono.
  auto. simpl. auto.
  destruct_s s.
  simpl. split; eauto.
  eauto.
  unfold val_inj, bop_eval, cmp_val, cmpu.
  destruct (Int.ltu v'0 ($ CAP_CHANNEL_CLASS)); auto.
  simpl. eauto.
  eapply bop_rv.
  sep_lifts_trms_in H0 (Alvarmapsto func_capability).
  eapply LV_to_Rv in H0. 
  eapply inline_tactics.monoasrt_mono in H0.
  exact H0.
  eapply inline_tactics.Rv_mono.
  auto. simpl. auto.
  destruct_s s.
  simpl. split; eauto.
  eauto.
  unfold bop_eval, val_inj, val_eq. 
  destruct (Int.eq v'0 ($ CAP_CHANNEL_CLASS)); auto.
  simpl. eauto.
  eauto.
  unfold val_inj, bop_eval, cmp_val.
  unfold cmpu, val_eq, bool_or.
  destruct (Int.ltu v'0 ($ CAP_CHANNEL_CLASS));
  destruct (Int.eq v'0 ($ CAP_CHANNEL_CLASS));auto.
  simpl. eauto.

  
  (*RETURN func_capability′ *)
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  sep get rv.
  intros.
  sep normal. sep eexists.
  sep lift 20%nat. 
  eapply disj_split.
  left.
  sep normal.  sep lift 2%nat. 
  eapply disj_split.
  left.

  sep auto; simpl; eauto.
  eapply if_imply_true; eauto.
  unfold CAP_FUNCTION_TYPE. lia.
  destruct H0.
  clear -H0. 
  unfold val_inj, bop_eval, cmp_val, cmpu, val_eq, bool_or in H0.
  destruct (Int.ltu v'0
  ($ CAP_CHANNEL_CLASS)) eqn: Hlt;
  destruct(Int.eq v'0
  ($ CAP_CHANNEL_CLASS)) eqn: Heq; repeat(simpl in H0; val_help_H H0); tryfalse.
  eapply Intlt_true_is_Zlt in Hlt.
  rewrite Int.unsigned_repr in Hlt. lia.
  unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
  eapply Intlt_true_is_Zlt in Hlt.
  rewrite Int.unsigned_repr in Hlt. lia.
  unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
  eapply Inteq_true_is_Zeq in Heq.
  rewrite Int.unsigned_repr in Heq.
  rewrite Heq. lia.
  unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val.
  lia. 
  
  (*RETURN 〈 long 〉 ′ SLOT_NUM*)
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  destruct_s s. 
  simpl. split; eauto.
  intros.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  left. sep normal. sep lift 2%nat. 
  eapply disj_split. right.

  sep auto; simpl; eauto.
  eapply if_imply_true; eauto.
  unfolds CAP_FUNCTION_TYPE. lia.
  clear -H0.
  unfold val_inj, bop_eval, cmp_val, cmpu, val_eq, bool_or in H0.
  destruct (Int.ltu v'0
  ($ CAP_CHANNEL_CLASS)) eqn: Hlt;
  destruct(Int.eq v'0
  ($ CAP_CHANNEL_CLASS)) eqn: Heq; repeat(simpl in H0; val_help_H H0); destruct H0; tryfalse.
  eapply Intlt_false_is_Zge in Hlt.
  eapply Inteq_false_is_Zneq in Heq.
  rewrite Int.unsigned_repr in Hlt, Heq.
  lia.
  unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.
  unfold CAP_CHANNEL_CLASS. rewrite max_unsigned_val. lia.

  eapply disj_rule.
  eapply disj_rule.
  hoare_split_pure_all.
  eapply pfalse_rule.
  hoare_split_pure_all.
  eapply pfalse_rule.
  hoare_split_pure_all.

  
  (*If ((func_capType ′ ==ₑ ′ CAP_SEM_TYPE
     ||ₑ func_capType ′ ==ₑ ′ CAP_MUTEX_TYPE
     ||ₑ func_capType ′ ==ₑ ′ CAP_Q_TYPE) &&ₑ
    ebinop odiv OS_USER_MAX_EVENTS ′ ′ 3 >ₑ
    func_capability ′)*)
  eapply seq_rule. 
  eapply ift_rule'.
  intros. eapply bop_rv.
  eapply bop_rv. eapply bop_rv.
  eapply bop_rv.
  sep_lifts_trms_in H0 (Alvarmapsto func_capType).
  eapply LV_to_Rv in H0. 
  eapply inline_tactics.monoasrt_mono in H0.
  exact H0.
  eapply inline_tactics.Rv_mono.
  auto. simpl. auto.
  change Byte.max_unsigned with 255.
  assert(Int.unsigned v'1 <=? 255 = true). int auto.
  rewrite H3. auto.
  destruct_s s. simpl. split; eauto.
  eauto. 
  unfold val_inj, bop_eval, val_eq.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE)); auto.
  simpl. eauto.
  eapply bop_rv.
  sep_lifts_trms_in H0 (Alvarmapsto func_capType).
  eapply LV_to_Rv in H0. 
  eapply inline_tactics.monoasrt_mono in H0.
  exact H0.
  eapply inline_tactics.Rv_mono.
  auto. simpl. auto.
  change Byte.max_unsigned with 255.
  assert(Int.unsigned v'1 <=? 255 = true). int auto.
  rewrite H3. auto.
  destruct_s s. simpl. split; eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE)); eauto.
  simpl; eauto.
  eauto.
  unfold bop_eval, val_inj, val_eq.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE));
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE)); auto.
  simpl. eauto.
  eapply bop_rv.
  sep_lifts_trms_in H0 (Alvarmapsto func_capType).
  eapply LV_to_Rv in H0. 
  eapply inline_tactics.monoasrt_mono in H0.
  exact H0.
  eapply inline_tactics.Rv_mono.
  auto. simpl. auto.
  change Byte.max_unsigned with 255.
  assert(Int.unsigned v'1 <=? 255 = true). int auto.
  rewrite H3. auto.
  destruct_s s. simpl. split; eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)); auto.
  simpl. eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq, bool_or.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE));
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE));
  destruct (Int.eq v'1 ($ CAP_Q_TYPE));
  repeat(val_help; simpl; eauto).
  simpl. eauto.
  eapply bop_rv.
  sep_lifts_trms_in H0 (Alvarmapsto func_capability).
  eapply LV_to_Rv in H0. 
  eapply inline_tactics.monoasrt_mono in H0.
  exact H0.
  eapply inline_tactics.Rv_mono.
  auto. simpl. auto.
  eapply bop_rv.
  destruct_s s.
  simpl. split; eauto.
  destruct_s s.
  simpl. split; eauto.
  eauto.
  unfold bop_eval, val_inj.
  unfold divs.
  assert(Int.eq ($ OS_USER_MAX_EVENTS)
  ($ Int.min_signed) = false).
  eapply int_min_neq_maxevents.
  rewrite H3.
  change (Int.eq ($ 3) Int.zero) with false. 
  simpl. eauto.
  simpl. eauto.
  simpl. eauto.
  eauto. unfold val_inj, bop_eval.
  unfold cmp_val, cmpu. 
  unfold divs.
  rewrite int_min_neq_maxevents.
  change (Int.eq ($ 3) Int.zero) with false. 
  change (Int.eq ($ 3) Int.mone) with false.
  simpl.
  destruct(Int.ltu v'0
  (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))); eauto.
  simpl. eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq, bool_and, bool_or, bool_or.
  unfold cmp_val, cmpu.
  rewrite int_min_neq_maxevents.
  change (Int.eq ($ 3) Int.zero) with false. 
  change (Int.eq ($ 3) Int.mone) with false.
  simpl.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE));
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE));
  destruct (Int.eq v'1 ($ CAP_Q_TYPE));
  destruct (Int.ltu v'0
  (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)));
  repeat(simpl; val_help; (try rewrite H3));
  tryfalse; auto.
  simpl. eauto.
  Lemma  OS_USER_MAX_EVENTS_div:
    forall v'0 , 
  Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = true ->
  Int.unsigned v'0 < OS_USER_MAX_EVENTS / 3.
  Proof.
      intros.
      eapply Intlt_true_is_Zlt in H.
      lets Hrgn': usr_max_evts_rgn'.
      destruct Hrgn' as (Hrgn5 & Hrgn6).
      assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
      clear -Hrgn5 Hrgn6.
      int auto.
      assert (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3)).
      { unfold Int.divs in *.
        rewrite zdiv_equiv in *.
        rewrite Hsieq in *.
        auto.
        clear -Hrgn5 Hrgn6. int auto.
        clear. int auto.
        clear -Hrgn5 Hrgn6. int auto.
        clear. int auto.
      }
      rewrite H0 in H.
      rewrite Int.unsigned_repr in H. auto.
      rewrite max_unsigned_val.
      lets Hx: usr_max_evts_rgn.
      lia. 
  Qed.

  
  hoare_split_pure_all.
  assert(Hv'0range: Int.unsigned v'0 < OS_USER_MAX_EVENTS / 3).
  unfold val_inj, bop_eval, val_eq, bool_and, bool_or, bool_or in H0.
  unfold cmp_val, cmpu in H0.
  rewrite int_min_neq_maxevents in H0.

  destruct H0.  clear -H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  

  instantiate(1:=Afalse).

  (*If (func_capType ′ ==ₑ ′ CAP_SEM_TYPE)*)
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat ASeminfo.
  eapply ASeminfo_unfold_any_idx_frm with (idx:=∘(Int.unsigned v'0)); eauto.
  unfold ASeminfo in Hsat.
  sep split in Hsat.
  destruct H3. rewrite H14. 
  clear -Hv'0range.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt; try (int auto).
  lets Hx: usr_max_evts_rgn.
  lia.
  hoare_split_pure_all.
  eapply seq_rule.

  eapply ift_rule'.
  intros.
  eapply bop_rv.
  
  sep_lifts_trms_in H11 (Alvarmapsto func_capType). 
  eapply LV_to_Rv in H11. 
  eapply inline_tactics.monoasrt_mono in H11.
  exact H11. eapply inline_tactics.Rv_mono.
  auto. simpl. 
  change Byte.max_unsigned with 255.
  assert(Int.unsigned v'1 <=? 255 = true). 
  clear -H2.
  int auto.
  rewrite H12. auto.
  destruct_s s. simpl. split; eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE)); auto.
  simpl. eauto.

  hoare_split_pure_all.
  assert(Hisptr: isptr(nth_val' 7 v'29)).
  {
    clear -H3 H8.
    subst v'18.
    eapply new_array_type_vallist_match_split in H3; eauto.
    simpljoin.  
    eapply struct_type_vallist_match_sem_info_t_ptr in H1.
    auto.
  }
  instantiate(1:= Afalse \\// Afalse).
  (*If ((Sem_info ′ [func_capability ′])
    .. pevent ==ₑ NULL)*)
  eapply seq_rule.
  eapply ift_rule'.
  intros. 
  eapply bop_rv.
  eapply struct_array_member_rv; try eauto.
  symbolic_execution.
  symbolic_execution.
  fold sem_info_t.
  sep cancel Astruct.
  eauto.
  simpl; auto.
  clear -Hv'0range.
  int auto.
  assert(Int.unsigned v'0 >=0).
  int auto.
  lia. 
  clear -Hv'0range.
  lets Hx: usr_max_evts_rgn.
  int auto.
  simpl.
  2:{
    eapply new_array_type_vallist_match_split in H3; eauto.
    fold sem_info_t.
    pure_auto.
  }
  2:{
    simpl. eauto.
  }
  2:{
    clear -H4.
    split; pure_auto; do 2 destruct H; tryfalse.
  }
  simpl. clear -Hv'0range. int auto.
  unfold id_nth. simpl. eauto.
  symbolic_execution.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  clear -Hisptr.
  unfold isptr in Hisptr.
  destruct Hisptr. rewrite H. auto.
  destruct H. rewrite H. destruct x. auto.
  simpl. eauto.

  hoare_split_pure_all.
  (*RETURN 〈 long 〉 ′ SLOT_NUM*)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl; split; eauto.
  intros.
  eapply ASeminfo_select_sn_strong in H13; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat. 
  eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  left. sep auto; simpl; eauto.
  splits. 
  clear -H11. 
  eapply if_imply_true in H11. auto.
  unfold CAP_SEM_TYPE. lia.
  destruct H0.
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  simpl in H0.
  rewrite int_min_neq_maxevents in H0. simpl in H0. 
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H11; auto.
  unfolds CAP_SEM_TYPE. lia.
  unfolds. 
  destruct H9. 
  assert (length v'27 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H9.
  clear H9.
  rewrite nth_vallist_get_idx.
  destruct H12. 
  clear -H9 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H9.
  destruct (nth_val' 7 v'29); destruct Hisptr; destruct H; tryfalse; auto.
  destruct a. tryfalse.
  subst v'18. auto.
  subst v'18. auto.
  eapply disj_rule.
  eapply pfalse_rule.
  (*ret ′ =ᶠ Get_Obj_Slot (·prio ′,(Sem_info ′ [func_capability ′]).. pevent·)*)
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec. simpl. unfold Get_Obj_Slot_spec.
  eauto.
  intros.
  eapply rvl_elim.
  symbolic_execution.
  change Byte.max_unsigned with 255.
  clear -H1.
  assert(Int.unsigned v'2 <=? 255 = true) by (int auto).
  rewrite H. auto.
  eapply rvl_elim.
  eapply cast_rv_ptr.
  eapply struct_array_member_rv; try eauto.
  symbolic_execution.
  symbolic_execution.
  fold sem_info_t.
  sep cancel Astruct.
  eauto.
  simpl; auto.
  clear -Hv'0range.
  int auto.
  assert(Int.unsigned v'0 >=0).
  int auto.
  lia. 
  lets Hx: usr_max_evts_rgn.
  clear -Hv'0range Hx.
  int auto.
  simpl.
  2:{
    eapply new_array_type_vallist_match_split in H3; eauto.
    fold sem_info_t.
    pure_auto.
  }
  2:{
    simpl. eauto.
  }
  2:{
    clear -H4.
    split; pure_auto; do 2 destruct H; tryfalse.
  }
  simpl. clear -Hv'0range. int auto.
  unfold id_nth. simpl. eauto.
  clear -Hisptr.
  unfold isptr in Hisptr.
  destruct Hisptr. rewrite H. auto.
  destruct H. rewrite H. destruct x. auto.
  unfold OS_EVENT. eauto.
  eapply rvl_nil.
  intros.
  unfold getasrt.
  unfold Get_Obj_SlotPre.
  unfold Get_Obj_SlotPre'.
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aisr.
  sep cancel Ais. sep cancel Acs. sep cancel Aier.
  sep cancel Aop. sep cancel AOSCSpacePrioTbl.
  sep split. sep cancel AOSCSpaceObjectPointer.
  sep cancel p_local. sep cancel ret.
  exact H12.
  8: simpl; eauto.
  
  auto.
  auto.
  instantiate(1:=nth_val' 7 v'29). auto.
  auto.
  eauto.
  simpl. auto. auto. auto. auto.
  auto. go. eapply retpost_GetObjSlotPost.
  simpl.
  assert(Int.unsigned v'2 <=? Byte.max_unsigned = true).
  clear -H1.
  change Byte.max_unsigned with 255.
  int auto.
  rewrite H12.
  clear -H3 H8 Hisptr.
  subst v'18.
  eapply new_array_type_vallist_match_split in H3; eauto.
  simpljoin.
  eapply struct_type_vallist_match_sem_info_t_vl in H1.
  do 9 destruct H1.
  rewrite H1.
  simpl in Hisptr.
  unfold isptr in Hisptr.
  destruct Hisptr. rewrite H1 in H2.
  rewrite H2. auto.
  rewrite H1 in H2.
  destruct H2. rewrite H2. auto.
  intros.
  unfold getasrt in H12.
  unfold Get_Obj_SlotPost in H12.
  unfold Get_Obj_SlotPost' in H12.
  sep destruct H12.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt.
  unfold Get_Obj_SlotPre.
  unfold Get_Obj_SlotPre'.
  intros. sep destruct H12.
  eexists. sep cancel p_local. simpl. auto.

  
  unfold getasrt.
  unfold Get_Obj_SlotPost.
  unfold Get_Obj_SlotPost'.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lift 10%nat in H19.
  eapply disj_split in H19.
  exact H19.

  eapply disj_rule.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H20.
  exact H20. eapply disj_rule.
  hoare_split_pure_all.
  3:{
    hoare_split_pure_all.
    simpl in H12.
    inverts H12.
    clear -H19 Hv'2range.
    false.
  }
  simpl in H12.
  inverts H12.
  inverts H21.
  eapply if_rule2.
  intros.
  symbolic_execution.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  destruct_s s. unfold SLOT_NUM.
  simpl; eauto.
  intros.
  sep lifts (11::12::13::14::nil)%nat in H21.
  eapply ASeminfo_select_sn_strong in H21; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. left.
  sep normal. eexists. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  sep lift 3%nat. eapply disj_split.
  left.
  unfold GetObjSlotRetval.
  sep lift 3%nat. 
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  left.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  subst logicl. auto.
  inverts H16. subst v'18. auto.
  simpl; eauto. simpl; eauto.
  inverts H16.
  subst v'18. auto.
  simpl. auto.
  simpl; eauto.
  simpl; eauto.
  splits; eauto.
  left.
  clear -H11.
  destruct H11.
  unfold val_inj, bop_eval, val_eq in H.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE)) eqn: Heq;tryfalse.
  rewrite Inteq_true_is_Zeq in Heq.
  rewrite Int.unsigned_repr in Heq.
  auto. unfold CAP_SEM_TYPE. rewrite max_unsigned_val. lia.
  clear -H11.
  destruct H11.
  unfold val_inj, bop_eval, val_eq in H.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE)) eqn: Heq;tryfalse.
  rewrite Inteq_true_is_Zeq in Heq.
  rewrite Int.unsigned_repr in Heq.
  auto. unfold CAP_SEM_TYPE. rewrite max_unsigned_val. lia.
  unfold nth_seminfo_pevent.
  destruct H9. 
  unfold nat_of_Z in H9.
  rewrite <- H9. 
  rewrite nth_vallist_get_idx; eauto.
  clear -H18.
  unfold val_inj, bop_eval, val_eq in H18.
  destruct (nth_val' 7 v'29); destruct H18; tryfalse; auto.
  pauto.
  subst v'18. auto.
  subst v'18. auto.
  hoare_split_pure_all.
  false.
  rewrite Int.eq_true in H12.
  unfold val_inj in H12.
  destruct H12; tryfalse.

  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep normal in H20.
  eapply disj_split in H22.
  exact H22.
  eapply disj_rule.
  hoare_split_pure_all.




  destruct H26.
  (*IF (ret ′ ==ₑ ′ SLOT_NULL_CAP)*)
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H26. auto.
  inverts H26. unfold val_inj, val_eq.
  destruct ( Int.eq ($ (v'44 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)); eauto.
  hoare_split_pure_all.
  false.
  inverts H26.
  clear -H28 H27.
  destruct H28.
  unfold val_inj, val_eq in H.
  destruct (Int.eq ($ (v'44 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)) eqn: Heq.
  unfold SLOT_NULL_CAP in Heq.
  unfold OBJ_POSITION in *. int auto.
  tryfalse.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  eapply ecast_long2long.
  2:{
    sep_lifts_trms_in H29 (Alvarmapsto ret).
    exact H29.
  }
  inverts H26. simpl. auto.
  intros.
  sep lifts (11::12::13::14::nil)%nat in H29.
  eapply ASeminfo_select_sn_strong in H29; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. left.
  sep normal. eexists. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  sep lift 3%nat. eapply disj_split.
  right.
  unfold GetObjSlotRetval.
  sep lift 3%nat. 
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split. left.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  subst logicl. auto.
  simpl; eauto. simpl; eauto.
  inverts H16. subst v'18. auto.
  simpl; eauto. simpl; eauto.
  splits. eapply if_imply_true in H11.
  clear -H11. auto.
  unfold CAP_SEM_TYPE. lia. 
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H.
  rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H11. auto.
  unfold CAP_SEM_TYPE. lia. 
  unfold nth_seminfo_pevent.
  destruct H9. 
  assert (length v'27 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H31.
  clear H31.
  rewrite nth_vallist_get_idx.
  clear -H18 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H18.
  destruct (nth_val' 7 v'29); destruct Hisptr; destruct H18; tryfalse; auto.
  unfold val_inj. eauto.
  clear -H27. 
  unfold OBJ_POSITION in H27.
  unfold OBJ_POSITION, SLOT_NULL_CAP.
  lia. 
  unfold nth_seminfo_pevent.
  destruct H9. 
  assert (length v'27 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H31.
  clear H31.
  rewrite nth_vallist_get_idx.
  simpl in H13. inverts H13. auto.
  
  subst v'18. eauto.
  subst v'18. eauto.

  hoare_split_pure_all.
  (*IF (ret ′ ==ₑ ′ SLOT_NULL_CAP)*)
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H26. auto.
  inverts H26. unfold val_inj, val_eq.
  rewrite Int.eq_true. auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros. destruct_s s. simpl; eauto.
  intros.
  sep lifts (11::12::13::14::nil)%nat in H28.
  eapply ASeminfo_select_sn_strong in H28; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. left.
  sep normal. eexists. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  sep lift 3%nat. eapply disj_split.
  left.
  unfold GetObjSlotRetval.
  sep lift 3%nat. 
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split. 
  right.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  inverts H16. subst v'18. auto.
  simpl; eauto. simpl; eauto.
  splits. eapply if_imply_true in H11.
  clear -H11. auto.
  unfold CAP_SEM_TYPE. lia. 
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H.
  rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H11. auto.
  unfold CAP_SEM_TYPE. lia. 
  unfold nth_seminfo_pevent.
  destruct H9. 
  assert (length v'27 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H30.
  clear H30.
  rewrite nth_vallist_get_idx.
  clear -H18 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H18.
  destruct (nth_val' 7 v'29); destruct Hisptr; destruct H18; tryfalse; auto.
  inverts H26. unfold val_inj. auto.
  unfold nth_seminfo_pevent.
  destruct H9. 
  assert (length v'27 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H30.
  clear H30.
  rewrite nth_vallist_get_idx.
  simpl in H13; inverts H13; auto.
  rewrite <- H8. auto. 
  rewrite <- H8. auto.

  hoare_split_pure_all. 
  inverts H26. 
  clear -H27. false.
  unfold val_inj, val_eq in H27.  rewrite Int.eq_true in H27.
  destruct H27; tryfalse.
  
  eapply disj_rule.
  eapply disj_rule. eapply pfalse_rule.
  eapply pfalse_rule.
  
  
  (*If (func_capType ′ ==ₑ ′ CAP_MUTEX_TYPE)*)
  hoare_split_pure_all.

  eapply backward_rule1.
  introv Hsat.
  (*先把ASeminfo折叠起来*)
  eapply ASeminfo_select_sn_strong in Hsat. 
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm with (idx:=∘(Int.unsigned v'0)); eauto.
  unfold APthreadMutex in Hsat.
  sep split in Hsat.
  destruct H12. rewrite H20. 
  clear -Hv'0range.
  eapply Z2Nat.inj_lt; int auto.
  lets Hx: usr_max_evts_rgn.
  lia.
  auto.  rewrite <- H8. auto. 
  rewrite <- H8. auto. 
  hoare_split_pure_all.
  eapply seq_rule.

  eapply ift_rule'.
  intros.
  eapply bop_rv.
  
  sep_lifts_trms_in H17 (Alvarmapsto func_capType). 
  eapply LV_to_Rv in H17. 
  eapply inline_tactics.monoasrt_mono in H17.
  exact H17. eapply inline_tactics.Rv_mono.
  auto. simpl. 
  change Byte.max_unsigned with 255.
  assert(Int.unsigned v'1 <=? 255 = true). 
  clear -H2.
  int auto.
  rewrite H18. auto.
  destruct_s s. simpl. split; eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE)); auto.
  simpl. eauto.

  hoare_split_pure_all.
  assert(Hisptr: isptr(nth_val' 8 v'32)).
  {
    clear -H12 H14.
    subst v'19.
    eapply new_array_type_vallist_match_split1 in H12; eauto.
    simpljoin.  
    eapply struct_type_vallist_match_mutex_info_t_imp in H1.
    do 10 destruct H1. 
    destruct H1. rewrite H1. simpl. 
    auto.
  }
  instantiate(1:= Afalse \\// Afalse).
  (*If ((Pthread_Mutex ′ [func_capability ′])
    .. pevent ==ₑ NULL)*)
  eapply seq_rule.
  eapply ift_rule'.
  intros. 
  eapply bop_rv.
  eapply struct_array_member_rv; try eauto.
  symbolic_execution.
  symbolic_execution.
  fold pthread_mutex_info_t.
  sep cancel Astruct.
  eauto.
  simpl; auto.
  clear -Hv'0range.
  int auto.
  assert(Int.unsigned v'0 >=0).
  int auto.
  lia. 
  lets Hx: usr_max_evts_rgn.
  clear -Hx Hv'0range. 
  int auto.
  simpl. 
  2:{
    eapply new_array_type_vallist_match_split1 in H12; eauto.
    fold pthread_mutex_info_t.
    pure_auto.
  }
  2:{
    simpl. eauto.
  }
  2:{
    clear -H4.
    split; pure_auto; do 2 destruct H; tryfalse.
  }
  simpl. clear -Hv'0range. int auto.
  unfold id_nth. simpl. eauto.
  symbolic_execution.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  clear -Hisptr.
  unfold isptr in Hisptr.
  destruct Hisptr. rewrite H. auto.
  destruct H. rewrite H. destruct x. auto.
  simpl. eauto.

  hoare_split_pure_all.
  (*RETURN 〈 long 〉 ′ SLOT_NUM*)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl; split; eauto.
  intros.
  eapply APthreadMutex_select_sn_strong in H19; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat. 
  eapply disj_split. right.
  sep normal. sep eexists.
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split. left.
  sep auto; simpl; eauto.
  splits. 
  clear -H17. 
  eapply if_imply_true in H17. auto.
  unfold CAP_MUTEX_TYPE. lia.
  
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H.
  rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H17. auto.
  unfolds CAP_MUTEX_TYPE. lia.
  unfolds. 
  
  assert (length v'30 = Z.to_nat (Int.unsigned v'0)).
  destruct H15. auto.
  rewrite <- H7.
  clear H7.
  rewrite nth_vallist_get_idx.
  destruct H18. 
  clear -H7 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H7.
  destruct (nth_val' 8 v'32); destruct Hisptr; destruct H; tryfalse; auto.
  destruct a. tryfalse.
  sep auto; simpl; eauto.
  subst v'19. auto.
  subst v'19. auto.
  eapply disj_rule.
  eapply pfalse_rule.
  (*ret ′ =ᶠ Get_Obj_Slot (·prio ′,(Pthread_Mutex ′ [func_capability ′]).. pevent·)*)
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec. simpl. unfold Get_Obj_Slot_spec.
  eauto.
  intros.
  eapply rvl_elim.
  symbolic_execution.
  change Byte.max_unsigned with 255.
  clear -H1.
  assert(Int.unsigned v'2 <=? 255 = true) by (int auto).
  rewrite H. auto.
  eapply rvl_elim.
  eapply cast_rv_ptr.
  eapply struct_array_member_rv; try eauto.
  symbolic_execution.
  symbolic_execution.
  fold pthread_mutex_info_t.
  sep cancel Astruct.
  eauto.
  simpl; auto.
  clear -Hv'0range.
  int auto.
  assert(Int.unsigned v'0 >=0).
  int auto.
  lia. 
  clear -Hv'0range.
  lets Hx: usr_max_evts_rgn.
  int auto.
  simpl.
  2:{
    eapply new_array_type_vallist_match_split1 in H12; eauto.
    fold sem_info_t.
    pure_auto.
  }
  2:{
    simpl. eauto.
  }
  2:{
    clear -H4.
    split; pure_auto; do 2 destruct H; tryfalse.
  }
  simpl. clear -Hv'0range. int auto.
  unfold id_nth. simpl. eauto.
  clear -Hisptr.
  unfold isptr in Hisptr.
  destruct Hisptr. rewrite H. auto.
  destruct H. rewrite H. destruct x. auto.
  unfold OS_EVENT. eauto.
  eapply rvl_nil.
  intros.
  unfold getasrt.
  unfold Get_Obj_SlotPre.
  unfold Get_Obj_SlotPre'.
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aisr.
  sep cancel Ais. sep cancel Acs. sep cancel Aier.
  sep cancel Aop. sep cancel AOSCSpacePrioTbl.
  sep split. sep cancel AOSCSpaceObjectPointer.
  sep cancel p_local. sep cancel ret.
  exact H14.
  8: simpl; eauto.
  
  auto.
  auto.
  instantiate(1:=nth_val' 8 v'32). auto.
  auto.
  eauto.
  simpl. auto. auto. auto. auto.
  auto. go. eapply retpost_GetObjSlotPost.
  simpl.
  assert(Int.unsigned v'2 <=? Byte.max_unsigned = true).
  clear -Hv'2range.
  unfold OS_LOWEST_PRIO in Hv'2range.
  change Byte.max_unsigned with 255.
  int auto.
  rewrite H14.
  clear -H12 Hisptr.
  eapply new_array_type_vallist_match_split1 in H12; eauto.
  simpljoin.
  eapply struct_type_vallist_match_mutex_info_t_imp in H1.
  do 10 destruct H1.
  destruct H1. 
  rewrite H1.
  unfolds in H2. destruct H2. subst x7. auto. 
  destruct H2. subst x7. auto. 
  intros.
  unfold getasrt in H14.
  unfold Get_Obj_SlotPost in H14.
  unfold Get_Obj_SlotPost' in H14.
  sep destruct H14.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt.
  unfold Get_Obj_SlotPre.
  unfold Get_Obj_SlotPre'.
  intros. sep destruct H14.
  eexists. sep cancel p_local. simpl. auto.

  
  unfold getasrt.
  unfold Get_Obj_SlotPost.
  unfold Get_Obj_SlotPost'.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lift 10%nat in H24.
  eapply disj_split in H24.
  exact H24.

  eapply disj_rule.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H25.
  exact H25. eapply disj_rule.
  hoare_split_pure_all.
  3:{
    hoare_split_pure_all.
    simpl in H14.
    inverts H14.
    clear -H24 Hv'2range.
    false.
  } 
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H26. auto.
  inverts H26. unfold val_inj, val_eq.
  rewrite Int.eq_true. auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  destruct_s s; simpl; eauto.
  
  inverts H26. intros.
  sep lifts (11::12::13::14::nil)%nat in H26.
  eapply APthreadMutex_select_sn_strong in H26; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists. sep lift 3%nat.
  eapply disj_split. left.
  unfold GetObjSlotRetval.
  sep normal. sep eexists.
  sep lift 3%nat. eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  left.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  inverts H21. subst v'18.
  simpl; eauto. simpl; eauto.
  simpl; eauto.
  split.
  eapply if_imply_true in H17.
  clear -H17. auto.
  unfold CAP_MUTEX_TYPE. lia. 
  unfold nth_mutex_pevent.
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H.
  rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H17. auto.
  unfolds CAP_MUTEX_TYPE. lia.
  unfold nth_mutex_pevent.
  assert (length v'30 = Z.to_nat (Int.unsigned v'0)).
  destruct H15. auto.
  
  rewrite <- H28.
  clear H28.
  rewrite nth_vallist_get_idx.

  clear -H23 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H23.
  destruct (nth_val' 8 v'32); destruct Hisptr; destruct H23; tryfalse; auto.
  unfold val_inj. eauto.
  hoare_split_pure_all.
  inverts  H26.
  false.
  unfold val_inj, val_eq in H27.
  rewrite Int.eq_true in H27.
  destruct H27; tryfalse.


  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H27.
  exact H27.
  eapply disj_rule.
  hoare_split_pure_all.
  destruct H31.
  (*IF (ret ′ ==ₑ ′ SLOT_NULL_CAP)*)
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H31. auto.
  inverts H31. unfold val_inj, val_eq.
  destruct ( Int.eq ($ (v'46 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)); eauto.
  hoare_split_pure_all.
  false.
  inverts H31.
  clear -H33 H32.
  destruct H33.
  unfold val_inj, val_eq in H.
  destruct (Int.eq ($ (v'46 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)) eqn: Heq.
  unfold SLOT_NULL_CAP in Heq.
  unfold OBJ_POSITION in *. int auto.
  tryfalse.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  eapply ecast_long2long.
  2:{
    sep_lifts_trms_in H34 (Alvarmapsto ret).
    exact H34.
  }
  inverts H31. simpl. auto.
  intros.
  sep lifts (11::12::13::14::nil)%nat in H34.
  eapply APthreadMutex_select_sn_strong in H34; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists. sep lift 3%nat.
  eapply disj_split. right.
  unfold GetObjSlotRetval.
  sep normal. sep eexists.
  sep lift 3%nat. eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  left.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  inverts H21. subst v'18. auto.
  simpl; eauto. simpl; eauto.
  splits.
  eapply if_imply_true in H17.
  clear -H17. auto.
  unfold CAP_MUTEX_TYPE. lia. 
  unfold nth_mutex_pevent.
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H.
  rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H17. auto.
  unfolds CAP_MUTEX_TYPE. lia.
  unfold nth_mutex_pevent.
  assert (length v'30 = Z.to_nat (Int.unsigned v'0)).
  destruct H15. auto.
  
  rewrite <- H35.
  clear H35.
  rewrite nth_vallist_get_idx.

  clear -H23 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H23.
  destruct (nth_val' 8 v'32); destruct Hisptr; destruct H23; tryfalse; auto.
  unfold val_inj. eauto.
  clear -H32. 
  unfold OBJ_POSITION in H32.
  unfold OBJ_POSITION, SLOT_NULL_CAP.
  lia. 
  unfold nth_mutex_pevent.
  destruct H15. 
  assert (length v'30 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H36.
  clear H36.
  rewrite nth_vallist_get_idx.
  simpl in H18. inverts H18. auto.

  

  hoare_split_pure_all.
  (*IF (ret ′ ==ₑ ′ SLOT_NULL_CAP)*)
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H31. auto.
  inverts H31. unfold val_inj, val_eq.
  rewrite Int.eq_true. auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros. destruct_s s. simpl; eauto.
  intros.
  sep lifts (11::12::13::14::nil)%nat in H33.
  eapply APthreadMutex_select_sn_strong in H33; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. right.
  eapply disj_split. left.
  sep normal. eexists. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  sep lift 3%nat. eapply disj_split.
  left.
  unfold GetObjSlotRetval.
  sep lift 3%nat. 
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  inverts H21. subst v'18. auto.
  simpl; eauto. simpl; eauto.
  
  splits. eapply if_imply_true in H17.
  clear -H17. auto.
  unfold CAP_MUTEX_TYPE. lia. 
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H.
  rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H17. auto.
  unfold CAP_MUTEX_TYPE. lia. 
  unfold nth_mutex_pevent.
  destruct H15. 
  assert (length v'30 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H35.
  clear H35.
  rewrite nth_vallist_get_idx.
  clear -H23 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H23.
  destruct (nth_val' 8 v'32); destruct Hisptr; destruct H23; tryfalse; auto.
  inverts H31. unfold val_inj. auto.
  unfold nth_mutex_pevent.
  destruct H15. 
  assert (length v'30 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H35.
  clear H35.
  rewrite nth_vallist_get_idx.
  simpl in H18; inverts H18; auto.


  hoare_split_pure_all. 
  inverts H31. 
  clear -H32. false.
  unfold val_inj, val_eq in H32.  rewrite Int.eq_true in H32.
  destruct H32; tryfalse.
  
  eapply disj_rule.
  eapply disj_rule. eapply pfalse_rule.
  eapply pfalse_rule.


  (*If (func_capType ′ ==ₑ ′ CAP_Q_TYPE)*)
  hoare_split_pure_all.

  eapply backward_rule1.
  introv Hsat.
  (*先把APthreadMutex折叠起来*)
  eapply APthreadMutex_select_sn_strong in Hsat. 
  sep_lift_context_in Hsat AMqAttr.
  eapply AMqAttr_unfold_any_idx_frm with (idx:=∘(Int.unsigned v'0)); eauto.
  unfold AMqAttr in Hsat.
  sep split in Hsat.
  destruct H18. rewrite H26. 
  clear -Hv'0range.  
  eapply Z2Nat.inj_lt; int auto.
  lets Hx: usr_max_evts_rgn.
  lia.
  auto.  rewrite <- H14. auto. 
  rewrite <- H14. auto. 
  hoare_split_pure_all.
  eapply seq_rule.

  eapply ift_rule'.
  intros.
  eapply bop_rv.
  
  sep_lifts_trms_in H23 (Alvarmapsto func_capType). 
  eapply LV_to_Rv in H23. 
  eapply inline_tactics.monoasrt_mono in H23.
  exact H23. eapply inline_tactics.Rv_mono.
  auto. simpl. 
  change Byte.max_unsigned with 255.
  assert(Int.unsigned v'1 <=? 255 = true). 
  clear -H2.
  int auto.
  rewrite H24. auto.
  destruct_s s. simpl. split; eauto.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)); auto.
  simpl. eauto.

  hoare_split_pure_all.
  assert(Hisptr: isptr(nth_val' 5 v'35)).
  {
    clear -H18 H20.
    subst v'20.
    eapply new_array_type_vallist_match_split' in H18; eauto.
    simpljoin.  
    eapply struct_type_vallist_match_mq_attr_t_ptr in H1.
    auto.
  }
  instantiate(1:= Afalse \\// Afalse).
  (*If ((Mq_Attr ′ [func_capability ′])
    .. pevent ==ₑ NULL)*)
  eapply seq_rule.
  eapply ift_rule'.
  intros. 
  eapply bop_rv.
  eapply struct_array_member_rv; try eauto.
  symbolic_execution.
  symbolic_execution.
  fold AMqAttr.
  sep cancel Astruct.
  eauto.
  simpl; auto.
  clear -Hv'0range.
  int auto.
  assert(Int.unsigned v'0 >=0).
  int auto.
  lia. 
  clear -Hv'0range.
  lets Hx: usr_max_evts_rgn.
  int auto.
  simpl.
  2:{
    eapply new_array_type_vallist_match_split' in H18; eauto.
    fold mq_attr_t.
    pure_auto.
  }
  2:{
    simpl. eauto.
  }
  2:{
    clear -H4.
    split; pure_auto; do 2 destruct H; tryfalse.
  }
  simpl. clear -Hv'0range. int auto.
  unfold id_nth. simpl. eauto.
  symbolic_execution.
  eauto.
  unfold val_inj, bop_eval, val_eq.
  clear -Hisptr.
  unfold isptr in Hisptr.
  destruct Hisptr. rewrite H. auto.
  destruct H. rewrite H. destruct x. auto.
  simpl. eauto.

  hoare_split_pure_all.
  (*RETURN 〈 long 〉 ′ SLOT_NUM*)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl; split; eauto.
  intros.
  eapply AMqAttr_select_sn_strong in H25; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat. 
  eapply disj_split. right.
  sep normal. sep eexists.
  eapply disj_split.
  right. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split. left.
  sep auto; simpl; eauto.
  splits. 
  clear -H23. 
  eapply if_imply_true in H23. auto.
  unfold CAP_Q_TYPE. lia.
  
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H.
  rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H23. auto.
  unfolds CAP_Q_TYPE. lia.
  unfolds. 
  
  assert (length v'33 = Z.to_nat (Int.unsigned v'0)).
  destruct H21. auto.
  rewrite <- H7.
  clear H7.
  rewrite nth_vallist_get_idx.
  destruct H24. 
  clear -H7 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H7.
  destruct (nth_val' 5 v'35); destruct Hisptr; destruct H; tryfalse; auto.
  destruct a. tryfalse.
  subst v'20. auto.
  subst v'20. auto.
  eapply disj_rule.
  eapply pfalse_rule.
  (*ret ′ =ᶠ Get_Obj_Slot (·prio ′,(Mq_Attr ′ [func_capability ′]).. pevent·)*)
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec. simpl. unfold Get_Obj_Slot_spec.
  eauto.
  intros.
  eapply rvl_elim.
  symbolic_execution.
  change Byte.max_unsigned with 255.
  clear -H1.
  assert(Int.unsigned v'2 <=? 255 = true) by (int auto).
  rewrite H. auto.
  eapply rvl_elim.
  eapply cast_rv_ptr.
  eapply struct_array_member_rv; try eauto.
  symbolic_execution.
  symbolic_execution.
  fold mq_attr_t.
  sep cancel Astruct.
  eauto.
  simpl; auto.
  clear -Hv'0range.
  int auto.
  assert(Int.unsigned v'0 >=0).
  int auto.
  lia. 
  clear -Hv'0range.
  lets Hx: usr_max_evts_rgn.
  int auto.
  simpl.
  2:{
    eapply new_array_type_vallist_match_split' in H18; eauto.
    fold sem_info_t.
    pure_auto.
  }
  2:{
    simpl. eauto.
  }
  2:{
    clear -H4.
    split; pure_auto; do 2 destruct H; tryfalse.
  }
  simpl. clear -Hv'0range. int auto.
  unfold id_nth. simpl. eauto.
  clear -Hisptr.
  unfold isptr in Hisptr.
  destruct Hisptr. rewrite H. auto.
  destruct H. rewrite H. destruct x. auto.
  unfold OS_EVENT. eauto.
  eapply rvl_nil.
  intros.
  unfold getasrt.
  unfold Get_Obj_SlotPre.
  unfold Get_Obj_SlotPre'.
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aisr.
  sep cancel Ais. sep cancel Acs. sep cancel Aier.
  sep cancel Aop. sep cancel AOSCSpacePrioTbl.
  sep split. sep cancel AOSCSpaceObjectPointer.
  sep cancel p_local. sep cancel ret.
  exact H24.
  8: simpl; eauto.
  
  auto.
  auto.
  instantiate(1:=nth_val' 5 v'35). auto.
  auto.
  eauto.
  simpl. auto. auto. auto. auto.
  auto. go. eapply retpost_GetObjSlotPost.
  simpl.
  assert(Int.unsigned v'2 <=? Byte.max_unsigned = true).
  clear -Hv'2range.
  unfold OS_LOWEST_PRIO in Hv'2range.
  change Byte.max_unsigned with 255.
  int auto.
  rewrite H24.
  rewrite H20 in H18.
  clear -H18 Hisptr.
  eapply new_array_type_vallist_match_split' in H18; eauto.
  simpljoin.
  eapply struct_type_vallist_match_mq_attr_t_vl in H1.
  do 7 destruct H1.
  rewrite H1.
  rewrite H1 in Hisptr. simpl in Hisptr.
  unfolds in Hisptr. destruct Hisptr. subst x4. auto.
  destruct H2. subst x4. auto.
  intros.
  unfold getasrt in H24.
  unfold Get_Obj_SlotPost in H24.
  unfold Get_Obj_SlotPost' in H24.
  sep destruct H24.
  eexists.
  sep cancel p_local. simpl. auto.
  unfold getasrt.
  unfold Get_Obj_SlotPre.
  unfold Get_Obj_SlotPre'.
  intros. sep destruct H24.
  eexists. sep cancel p_local. simpl. auto.

  
  unfold getasrt.
  unfold Get_Obj_SlotPost.
  unfold Get_Obj_SlotPost'.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lift 10%nat in H31.
  eapply disj_split in H31.
  exact H31.

  eapply disj_rule.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H32.
  exact H32. eapply disj_rule.
  hoare_split_pure_all.
  3:{
    hoare_split_pure_all.
    simpl in H24.
    inverts H24.
    clear -H31 Hv'2range.
    false.
  } 
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H33. auto.
  inverts H33. unfold val_inj, val_eq.
  rewrite Int.eq_true. auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  destruct_s s; simpl; eauto.
  
  inverts H33. intros.
  sep lifts (11::12::13::14::nil)%nat in H33.
  eapply AMqAttr_select_sn_strong in H33; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  eapply disj_split.
  right. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists. sep lift 3%nat.
  eapply disj_split. left.
  unfold GetObjSlotRetval.
  sep normal. sep eexists.
  sep lift 3%nat. eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  left.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  subst logicl.
  inverts H28. subst v'20.
  subst v'19. subst v'18. auto.
  simpl; eauto. simpl; eauto.
  simpl; eauto.
  split.
  eapply if_imply_true in H23.
  clear -H23. auto.
  unfold CAP_Q_TYPE. lia. 
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H.
  rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H23. auto.
  unfolds CAP_Q_TYPE. lia.
  unfold nth_q_pevent.
  assert (length v'33 = Z.to_nat (Int.unsigned v'0)).
  destruct H21. auto.
  
  rewrite <- H35.
  clear H35.
  rewrite nth_vallist_get_idx.

  clear -H30 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H30.
  destruct (nth_val' 5 v'35); destruct Hisptr; destruct H30; tryfalse; auto.
  unfold val_inj. eauto.
  subst v'20. auto.
  subst v'20. auto.
  hoare_split_pure_all.
  inverts  H33.
  false.
  unfold val_inj, val_eq in H34.
  rewrite Int.eq_true in H34.
  destruct H34; tryfalse.
  
  hoare_split_pure_all.
  eapply backward_rule1. intros.
  eapply disj_split in H34.
  exact H34.
  eapply disj_rule.
  hoare_split_pure_all.
  destruct H38.
  (*IF (ret ′ ==ₑ ′ SLOT_NULL_CAP)*)
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H38. auto.
  inverts H38. unfold val_inj, val_eq.
  destruct ( Int.eq ($ (v'50 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)); eauto.
  hoare_split_pure_all.
  false.
  inverts H38.
  clear -H39 H40.
  destruct H40.
  unfold val_inj, val_eq in H.
  destruct (Int.eq ($ (v'50 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)) eqn: Heq.
  unfold SLOT_NULL_CAP in Heq.
  unfold OBJ_POSITION in *. int auto.
  tryfalse.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  eapply ecast_long2long.
  2:{
    sep_lifts_trms_in H41 (Alvarmapsto ret).
    exact H41.
  }
  inverts H38. simpl. auto.
  intros.
  sep lifts (11::12::13::14::nil)%nat in H41.
  eapply AMqAttr_select_sn_strong in H41; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. right.
  eapply disj_split. right.
  sep normal. eexists. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  sep lift 3%nat. eapply disj_split.
  right.
  unfold GetObjSlotRetval.
  sep lift 3%nat. 
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  left.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  subst logicl. subst v'18. subst v'19. subst v'20. 
  inverts H28. auto.
  simpl; eauto. simpl; eauto.
  splits. eapply if_imply_true in H23.
  clear -H23. auto.
  unfold CAP_Q_TYPE. lia. 
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H. rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H23. auto.
  unfold CAP_Q_TYPE. lia. 
  unfold nth_q_pevent.
  destruct H21. 
  assert (length v'33 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H43.
  clear H43.
  rewrite nth_vallist_get_idx.
  clear -H30 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H30.
  destruct (nth_val' 5 v'35); destruct Hisptr; destruct H30; tryfalse; auto.
  unfold val_inj. auto.
  clear -H39. unfold OBJ_POSITION in *. unfold SLOT_NULL_CAP.
  lia.
  unfold nth_q_pevent.
  destruct H21. 
  assert (length v'33 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H43.
  clear H43.
  rewrite nth_vallist_get_idx.
  simpl in H25; inverts H25; auto. 
  subst v'20. auto.
  subst v'20. auto.
  hoare_split_pure_all.
  (*IF (ret ′ ==ₑ ′ SLOT_NULL_CAP)*)
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H38. auto.
  inverts H38. unfold val_inj, val_eq.
  rewrite Int.eq_true. auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros. destruct_s s. simpl; eauto.
  intros.
  sep lifts (11::12::13::14::nil)%nat in H40.
  eapply AMqAttr_select_sn_strong in H40; eauto.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right. eapply disj_split. left.
  sep normal. sep lift 2%nat.
  eapply disj_split. right.
  eapply disj_split. right.
  sep normal. eexists. sep lift 2%nat.
  eapply disj_split. right.
  sep normal.  sep eexists.
  sep lift 3%nat. eapply disj_split.
  left.
  unfold GetObjSlotRetval.
  sep lift 3%nat. 
  eapply disj_split.
  left. sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr. sep cancel AOSTCBPrioTbl.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  subst logicl. 
  inverts H28. subst v'18. subst v'19. subst v'20.
  auto.
  simpl; eauto. simpl; eauto.
  splits. eapply if_imply_true in H23.
  clear -H23. auto.
  unfold CAP_Q_TYPE. lia. 
  clear -H0. unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  destruct H0.  clear -H. rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE))eqn: Heq1;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE))eqn: Heq2;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Heq3;
  destruct (Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn : Heq4;
  repeat(simpl in H0; val_help_H H0);
  try (eapply OS_USER_MAX_EVENTS_div); auto;
  tryfalse.
  eapply if_imply_true in H23. auto.
  unfold CAP_Q_TYPE. lia. 
  unfold nth_q_pevent.
  destruct H21. 
  assert (length v'33 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H42.
  clear H42.
  rewrite nth_vallist_get_idx.
  clear -H30 Hisptr.
  unfolds in Hisptr.
  unfold val_inj, bop_eval, val_eq in H30.
  destruct (nth_val' 5 v'35); destruct Hisptr; destruct H30; tryfalse; auto.
  inverts H38. unfold val_inj. auto.
  unfold nth_q_pevent.
  destruct H21. 
  assert (length v'33 = Z.to_nat (Int.unsigned v'0)) by auto.
  rewrite <- H42.
  clear H42.
  rewrite nth_vallist_get_idx.
  simpl in H25; inverts H25; auto.
  subst v'20. auto.
  subst v'20. auto.

  hoare_split_pure_all. 
  inverts H38. 
  clear -H39. false.
  unfold val_inj, val_eq in H39.  rewrite Int.eq_true in H39.
  destruct H39; tryfalse.
  
  eapply disj_rule.
  eapply disj_rule. eapply pfalse_rule.
  eapply pfalse_rule.

  hoare_split_pure_all.
  eapply backward_rule1.
  introv Hsat.
  (*先把AMqAttr折叠起来*)
  eapply AMqAttr_select_sn_strong in Hsat. 
  exact Hsat. auto. subst v'20. auto.
  subst v'20. auto.
  (*return EINVAL是到达不了的*)
  false.
  clear -H0 H11 H17 H23.
  unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H0.
  eapply if_imply_false in H11, H17, H23.
  rewrite H11, H17, H23 in H0.
  destruct H0. clear -H. rename H into H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0.
  repeat(simpl in H0; val_help_H H0).
  destruct (Int.ltu v'0
  (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))); tryfalse.
  eapply seq_rule.
  (*If (func_capType ′ ==ₑ ′ CAP_TASK_TYPE &&ₑ
    ′ OS_STAT_PRIO >ₑ func_capability ′ &&ₑ
    func_capability ′ >ₑ ′ 0)*)
  hoare forward.
  hoare forward.
  assert(Int.unsigned v'1 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H2.
  int auto.
  rewrite H4. auto.
  unfold val_inj, bop_eval, val_eq.
  destruct(Int.eq v'1 ($ CAP_TASK_TYPE)); eauto.
  simpl. eauto.
  unfold val_inj, bop_eval, cmp_val, cmpu.
  destruct (Int.ltu v'0 ($ OS_STAT_PRIO)); auto.  
  unfold val_inj, bop_eval, val_eq, cmp_val, cmpu.
  destruct (Int.eq v'1 ($ CAP_TASK_TYPE));
  destruct (Int.ltu v'0 ($ OS_STAT_PRIO)); auto.
  
  unfold bop_eval, val_inj, cmp_val, cmpu.
  destruct (Int.ltu ($ 0) v'0); auto.
  simpl. eauto. eauto.
  unfold val_inj, bop_eval, val_eq, cmp_val, cmpu, bool_and, bool_or.
  destruct (Int.eq v'1 ($ CAP_TASK_TYPE));
  destruct ( Int.ltu v'0 ($ OS_STAT_PRIO));
  destruct (Int.ltu ($ 0) v'0);
  repeat(simpl; val_help); auto.
  simpl. eauto.
  hoare_split_pure_all.
  instantiate(1:=Afalse \\// Afalse).
  assert(Hlen: Int.unsigned v'0 < OS_STAT_PRIO).
  destruct (Int.eq v'1 ($ CAP_TASK_TYPE));
  destruct ( Int.ltu v'0 ($ OS_STAT_PRIO)) eqn: Hlt;
  destruct (Int.ltu ($ 0) v'0);
  repeat(val_help_H H3; simpl in H3); destruct H3; tryfalse.
  rewrite Intlt_true_is_Zlt in Hlt.
  rewrite Int.unsigned_repr in Hlt.
  lia.
  unfold OS_STAT_PRIO. rewrite max_unsigned_val.
  lia.
  unfold OS_STAT_PRIO in Hlen.
  (*If (OSTCBPrioTbl ′ [func_capability ′] ==ₑ
    〈 OS_TCB ∗ 〉 ′  NULL)*)
  hoare unfold.
  assert(Hisptr: rule_type_val_match OS_TCB ∗ (nth_val' (Z.to_nat (Int.unsigned v'0))
  v'22) = true).
  eapply array_type_vallist_match_nth_val'; eauto.
  rewrite H11.
  clear -Hlen. 
  lia. 
  hoare forward; auto.
  unfold rule_type_val_match in Hisptr.
  unfold val_inj, val_eq. 
  destruct (nth_val'
  (Z.to_nat (Int.unsigned v'0))v'22); tryfalse.
  auto. destruct a. auto.
  hoare_split_pure_all.
  (*RETURN 〈 long 〉 ′ SLOT_NUM*)
  eapply rete_rule'.
  intros.
  destruct_s s. simpl; eauto.
  intros.
  unfold AOSTCBPrioTbl in H14. 
  sep normal. sep eexists. sep lift 27%nat.
  eapply disj_split. right.
  eapply disj_split. right.
  sep normal. sep eexists.
  eapply disj_split.
  left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split. left. 
  sep auto; eauto.
  clear -H3.
  unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H3.
  destruct (Int.eq v'1 ($ CAP_TASK_TYPE)) eqn: Heq;
  destruct ( Int.ltu v'0 ($ OS_STAT_PRIO)) eqn: Hlt;
  destruct (Int.ltu ($ 0) v'0) eqn: Hgt; repeat(val_help_H H3; simpl in H3); tryfalse.
  splits. rewrite Inteq_true_is_Zeq in Heq. auto.
  rewrite Intlt_true_is_Zlt in Hlt. auto.
  eapply Intlt_true_is_Zlt in Hgt. rewrite Int.unsigned_repr in Hgt.
  lia.
  rewrite max_unsigned_val. lia.
  clear -H7 Hisptr.
  unfold val_inj, val_eq in H7.
  destruct H7.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'0)) v'22); simpl in Hisptr; tryfalse; auto.
  destruct a. tryfalse.
  (*ret ′ =ᶠ Get_Obj_Slot (·prio ′,
〈 (Void) ∗
〉 OSTCBPrioTbl ′ [func_capability ′]·);ₛ*)
  eapply disj_rule.
  hoare_split_pure_all.
  eapply pfalse_rule.
  hoare_split_pure_all.
  eapply seq_rule.
  eapply calle_rule_lvar'.
  unfold Cap_spec. simpl. unfold Get_Obj_Slot_spec.
  eauto.
  intros.
  eapply rvl_elim.
  symbolic_execution.
  change Byte.max_unsigned with 255.
  clear -H1.
  assert(Int.unsigned v'2 <=? 255 = true) by (int auto).
  rewrite H. auto.
  eapply rvl_elim.
  eapply cast_rv_ptr.
  symbolic_execution.
  eapply array_type_vallist_match_imp_rule_type_val_match.
  rewrite H11.
  lia. auto.
  eapply array_type_vallist_match_imp_rule_type_val_match.
  rewrite H11.
  lia. auto.
  right. left. eauto.
  eapply rvl_nil.
  intros.
  unfold getasrt.
  unfold Get_Obj_SlotPre.
  unfold Get_Obj_SlotPre'.
  sep normal. sep eexists.
  sep cancel Aie. sep cancel Aisr.
  sep cancel Ais. sep cancel Acs. sep cancel Aier.
  sep cancel Aop. sep cancel AOSCSpacePrioTbl.
  sep split. sep cancel AOSCSpaceObjectPointer.
  sep cancel p_local. sep cancel ret.
  exact H14.
  all: auto.
  2: simpl; eauto.
  2: simpl; eauto.

  unfolds in Hisptr. unfold isptr.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned v'0)) v'22); tryfalse.
  auto. eauto. 
  go. eapply retpost_GetObjSlotPost.
  simpl. 
  
  assert(Int.unsigned v'2 <=? Byte.max_unsigned = true).
  clear -H1.
  change Byte.max_unsigned with 255.
  int auto.
  rewrite H14. 
  clear -Hisptr.
  unfolds in Hisptr.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'0))
  v'22); tryfalse; auto. 
  unfold getasrt.
  unfold Get_Obj_SlotPost.
  unfold Get_Obj_SlotPost'.
  intros. sep destruct H14.
  eexists. sep cancel p_local. simpl. auto.
  unfold getasrt.
  unfold Get_Obj_SlotPre.
  unfold Get_Obj_SlotPre'.
  intros. sep destruct H14.
  eexists. sep cancel p_local. simpl. auto.


  unfold getasrt.
  unfold Get_Obj_SlotPost.
  unfold Get_Obj_SlotPost'.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  sep lift 10%nat in H20.
  eapply disj_split in H20.
  exact H20.

  eapply disj_rule.
  hoare_split_pure_all.
  eapply backward_rule1.
  intros.
  eapply disj_split in H21.
  exact H21. eapply disj_rule.
  hoare_split_pure_all.
  3:{
    hoare_split_pure_all.
    simpl in H14.
    inverts H14.
    clear -H20 Hv'2range.
    false.
  } 
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H22. auto.
  inverts H22. unfold val_inj, val_eq.
  rewrite Int.eq_true. auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  destruct_s s; simpl; eauto.
  
  inverts H22. intros.
  sep normal. sep eexists.
  sep lift 27%nat. eapply disj_split.
  right. eapply disj_split. right.
  sep normal.
  eapply disj_split. left.
  sep normal.  sep eexists.
  sep lift 2%nat. 
  eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 3%nat. eapply disj_split.
  left.
  unfold GetObjSlotRetval.
  sep normal. sep eexists.
  sep lift 3%nat. 
  eapply disj_split. left.
  sep normal. sep lift 2%nat. 
  eapply disj_split. left.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep normal. sep eexists.
  sep split; eauto.
  inverts H18. auto.
  clear -H3.
  unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H3.
  destruct (Int.eq v'1 ($ CAP_TASK_TYPE)) eqn: Heq;
  destruct ( Int.ltu v'0 ($ OS_STAT_PRIO)) eqn: Hlt;
  destruct (Int.ltu ($ 0) v'0) eqn: Hgt; repeat(val_help_H H3; simpl in H3); tryfalse.
  splits. rewrite Inteq_true_is_Zeq in Heq. auto.
  rewrite Intlt_true_is_Zlt in Hlt. auto.
  eapply Intlt_true_is_Zlt in Hgt. rewrite Int.unsigned_repr in Hgt.
  lia. rewrite max_unsigned_val. lia.
  clear -H7.
  unfold val_inj, val_eq in H7.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'0)) v'22);destruct H7; tryfalse; auto.
  pauto.
  hoare_split_pure_all.
  inverts H22.
  unfold val_inj, val_eq in H23.
  rewrite Int.eq_true in H23.
  destruct H23; tryfalse.
  hoare_split_pure_all.
  eapply backward_rule1. intros.
  eapply disj_split in H23. exact H23.
  eapply disj_rule. hoare_split_pure_all.
  destruct H27.
  (*IF (ret ′ ==ₑ ′ SLOT_NULL_CAP)*)
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H27. auto.
  inverts H27. unfold val_inj, val_eq.
  destruct ( Int.eq ($ (v'42 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)); eauto.
  hoare_split_pure_all.
  false.
  inverts H27.
  clear -H28 H29.
  destruct H29.
  unfold val_inj, val_eq in H.
  destruct (Int.eq ($ (v'42 + OBJ_POSITION))
  ($ SLOT_NULL_CAP)) eqn: Heq.
  unfold SLOT_NULL_CAP in Heq.
  unfold OBJ_POSITION in *. int auto.
  tryfalse.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  eapply ecast_long2long.
  2:{
    sep_lifts_trms_in H30 (Alvarmapsto ret).
    exact H30.
  }
  inverts H27. simpl. auto.
  intros.
  sep normal. sep eexists.
  sep lift 27%nat. 
  eapply disj_split. right.
  eapply disj_split. right.
  eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 2%nat.
  eapply disj_split. right.
  unfold GetObjSlotRetval.
  sep normal. sep eexists.
  eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 2%nat. 
  eapply disj_split. eapply disj_split.
  eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 10%nat. eapply disj_split. right.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep auto; eauto.
  inverts H18. auto.
  clear -H3.
  unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H3.
  destruct (Int.eq v'1 ($ CAP_TASK_TYPE)) eqn: Heq;
  destruct ( Int.ltu v'0 ($ OS_STAT_PRIO)) eqn: Hlt;
  destruct (Int.ltu ($ 0) v'0) eqn: Hgt; repeat(val_help_H H3; simpl in H3); tryfalse.
  splits. rewrite Inteq_true_is_Zeq in Heq. auto.
  rewrite Intlt_true_is_Zlt in Hlt. auto.
  eapply Intlt_true_is_Zlt in Hgt. rewrite Int.unsigned_repr in Hgt.
  lia. rewrite max_unsigned_val. lia.
  clear -H7 Hisptr. unfold val_inj, val_eq in H7.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'0)) v'22); simpl in Hisptr; tryfalse; destruct H7; tryfalse.
  destruct a. auto. auto.
  unfold val_inj.
  inverts H27. eauto.
  simpl in H14. inverts H14. auto.
  simpl in H14. inverts H14. auto.
  simpl in H15. inverts H15. auto.
  simpl in H14. inverts H14. eauto.
  clear -H28.
  unfold OBJ_POSITION in *.
  unfold SLOT_NULL_CAP. lia.

  hoare_split_pure_all.
  (*IF (ret ′ ==ₑ ′ SLOT_NULL_CAP)*)
  eapply if_rule2.
  intros.
  symbolic_execution. inverts H27. auto.
  inverts H27. unfold val_inj, val_eq.
  rewrite Int.eq_true. auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros. destruct_s s. simpl; eauto.
  intros.
  sep normal. sep eexists.
  sep lift 27%nat. 
  eapply disj_split. right.
  eapply disj_split. right.
  eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 2%nat.
  eapply disj_split. right.
  unfold GetObjSlotRetval.
  sep normal. sep eexists.
  eapply disj_split. left.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 2%nat. eapply disj_split.
  right.
  sep normal. sep eexists.
  sep lift 10%nat. eapply disj_split. left.
  sep cancel Aie. sep cancel Ais. sep cancel Acs.
  sep cancel Aisr. sep cancel Aier.
  sep cancel AOSCSpacePrioTbl. sep cancel ASeminfo.
  sep cancel APthreadMutex. sep cancel AMqAttr.
  sep cancel p_local. sep cancel ret. 
  sep cancel Aop. sep cancel AOSCSpaceObjectPointer.
  sep cancel func_capability. sep cancel func_capType.
  sep cancel prio. sep cancel A_dom_lenv.
  sep auto; eauto.
  inverts H18. auto.

  clear -H3.
  unfold val_inj, bop_eval, val_eq, cmpu, cmp_val, divs, 
  bool_and, bool_or in H3.
  destruct (Int.eq v'1 ($ CAP_TASK_TYPE)) eqn: Heq;
  destruct ( Int.ltu v'0 ($ OS_STAT_PRIO)) eqn: Hlt;
  destruct (Int.ltu ($ 0) v'0) eqn: Hgt; repeat(val_help_H H3; simpl in H3); tryfalse.
  splits. rewrite Inteq_true_is_Zeq in Heq. auto.
  rewrite Intlt_true_is_Zlt in Hlt. auto.
  eapply Intlt_true_is_Zlt in Hgt. rewrite Int.unsigned_repr in Hgt.
  lia. rewrite max_unsigned_val. lia.
  clear -H7 Hisptr. unfold val_inj, val_eq in H7.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'0)) v'22); simpl in Hisptr; tryfalse; destruct H7; tryfalse.
  destruct a. auto. auto.
  unfold val_inj.
  eauto.
  simpl in H14. inverts H14. auto.
  simpl in H14. inverts H14. auto.
  simpl in H15. inverts H15. auto.
  simpl in H14. inverts H14. eauto.

  hoare_split_pure_all.
  false.
  inverts H27.
  unfold val_inj, val_eq in H28.
  rewrite Int.eq_true in H28. destruct H28; tryfalse.
  eapply disj_rule.
  hoare_split_pure_all.
  eapply disj_rule. eapply pfalse_rule.
  eapply pfalse_rule.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  destruct_s s. simpl; eauto.
  intros.  
  sep normal. sep eexists.
  sep lift 20%nat. 
  eapply disj_split. right.
  eapply disj_split. right.
  eapply disj_split. right.
  sep auto; eauto.
  simpl. eauto. simpl. eauto.
  simpl. eauto.
  clear -H H0 H3.
  Lemma  OS_USER_MAX_EVENTS_div_false:
    forall v'0 , 
  Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3)) = false ->
  ~(Int.unsigned v'0 < OS_USER_MAX_EVENTS / 3).
  Proof.
      intros.
      eapply Intlt_false_is_Zge in H.
      lets Hrgn': usr_max_evts_rgn'.
      destruct Hrgn' as (Hrgn5 & Hrgn6).
      assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
      clear -Hrgn5 Hrgn6.
      int auto.
      assert (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3)).
      { unfold Int.divs in *.
        rewrite zdiv_equiv in *.
        rewrite Hsieq in *.
        auto.
        clear -Hrgn5 Hrgn6. int auto.
        clear. int auto.
        clear -Hrgn5 Hrgn6. int auto.
        clear. int auto.
      }
      rewrite H0 in H.
      rewrite Int.unsigned_repr in H. auto.
      rewrite max_unsigned_val.
      lets Hx: usr_max_evts_rgn.
      lia. 
  Qed.
  unfold val_inj, bop_eval, val_eq, bool_and, bool_or, cmp_val, cmpu, divs in *.
  assert(Int.eq ($ OS_USER_MAX_EVENTS)
  ($ Int.min_signed) = false).
  assert(Int.eq ($ 3) Int.zero
  || Int.eq ($ OS_USER_MAX_EVENTS)
       ($ Int.min_signed) &&
     Int.eq ($ 3) Int.mone = false).
  rewrite int_min_neq_maxevents.
  auto.
  rewrite H1 in H0. clear H1.
 rewrite int_min_neq_maxevents. auto.
  assert(Int.unsigned v'1 <> CAP_FUNCTION_TYPE).
  destruct (Int.eq v'1 ($ CAP_FUNCTION_TYPE)) eqn: Hfunc; destruct H; tryfalse.
  rewrite Inteq_false_is_Zneq in Hfunc. auto.
  assert(~
  ((Int.unsigned v'1 = CAP_SEM_TYPE \/
    Int.unsigned v'1 = CAP_MUTEX_TYPE \/
    Int.unsigned v'1 = CAP_Q_TYPE) /\
   Int.unsigned v'0 < OS_USER_MAX_EVENTS / 3)).
  clear -H0.
  change (Int.eq ($ 3) Int.zero) with false in H0.
  change (Int.eq ($ 3) Int.mone) with false in H0.
  rewrite int_min_neq_maxevents in H0. simpl in H0.
  destruct (Int.eq v'1 ($ CAP_SEM_TYPE)) eqn: Hsem;
  destruct (Int.eq v'1 ($ CAP_MUTEX_TYPE)) eqn: Hmutex;
  destruct (Int.eq v'1 ($ CAP_Q_TYPE)) eqn: Hq;
  destruct ( Int.ltu v'0 (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3))) eqn: Hltv'0;

  repeat(val_help_H H0; simpl in H0); 
  try(destruct H0; tryfalse);
  try (eapply Classical_Prop.or_not_and; right; eapply Intlt_false_is_Zge in Hltv'0;
  rewrite Int.unsigned_repr in Hltv'0; [lia| rewrite max_unsigned_val; lia]);

  eapply Classical_Prop.or_not_and;unfold not; intros.
  
  
  right; eapply OS_USER_MAX_EVENTS_div_false; auto.
  right. eapply OS_USER_MAX_EVENTS_div_false; auto.
  right. eapply OS_USER_MAX_EVENTS_div_false; auto.
  right. eapply OS_USER_MAX_EVENTS_div_false; auto.
  right. eapply OS_USER_MAX_EVENTS_div_false; auto.
  right; eapply OS_USER_MAX_EVENTS_div_false; auto.
  right. eapply OS_USER_MAX_EVENTS_div_false; auto.
  left.
  rewrite Inteq_false_is_Zneq in *. rewrite Int.unsigned_repr in *.
  intros. lia.
  unfold CAP_SEM_TYPE. rewrite max_unsigned_val. lia.
  unfold CAP_MUTEX_TYPE. rewrite max_unsigned_val. lia.
  unfold CAP_Q_TYPE. rewrite max_unsigned_val. lia.

  left.
  rewrite Inteq_false_is_Zneq in *. rewrite Int.unsigned_repr in *.
  intros. lia.
  unfold CAP_SEM_TYPE. rewrite max_unsigned_val. lia.
  unfold CAP_MUTEX_TYPE. rewrite max_unsigned_val. lia.
  unfold CAP_Q_TYPE. rewrite max_unsigned_val. lia.
  assert(~
  (Int.unsigned v'1 = CAP_TASK_TYPE /\
   Int.unsigned v'0 < OS_STAT_PRIO /\
   Int.unsigned v'0 > 0)).
   clear -H3.
   destruct (Int.eq v'1 ($ CAP_TASK_TYPE)) eqn: Htask;
   destruct (Int.ltu v'0 ($ OS_STAT_PRIO)) eqn: Hltstat;
   destruct (Int.ltu ($ 0) v'0) eqn: Hlt0;
   repeat(val_help_H H3; simpl in H3); destruct H3; tryfalse;
   (unfold not; intros; destruct H0; destruct H1;
   try rewrite Inteq_true_is_Zeq in *; try rewrite Inteq_false_is_Zneq in *;
   try rewrite Intlt_false_is_Zge in *; try rewrite Intlt_true_is_Zlt in *;
   try rewrite Int.unsigned_repr in *; [lia|
   unfold CAP_TASK_TYPE; rewrite max_unsigned_val; lia |
   unfold OS_STAT_PRIO; rewrite max_unsigned_val; lia |
   rewrite max_unsigned_val; lia]).
   splits; eauto.

  Unshelve.
  all: (exact 0%nat).
Qed.  


  
  