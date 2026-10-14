Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import Lia.
Require Import ACSpace_defs.
Require Import CapSpec.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Set Nested Proofs Allowed.
Lemma ucos_CNode_Revoke_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal ucos_CNode_Revoke
                  vl logicl ucos_CNode_RevokePre ct->
      Some r =
      BuildRetI os_internal ucos_CNode_Revoke vl logicl ucos_CNode_RevokePost ct->
      exists t d1 d2 s,
      os_internal ucos_CNode_Revoke = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.  
  init spec.
  simpl in H, H0, H4. 
  inverts H.
  inverts H0. 
  inverts H4.
  Require Import seplog_trm_tacs.
  hoare_lifts_trms_pre (Aop).
  Ltac p_local_go:= 
      try unfold p_local;
      try unfold CurTid;
      try unfold OSLInv;
      try unfold LINV;
      try unfold AOSExchandler;
      try good_frm_sovler;
      try go.
  assert(Hv'0: Int.unsigned v'0 <=? Byte.max_unsigned = true).
  clear -H3. change Byte.max_unsigned with 255.
  int auto.
  hoare forward.
  rewrite Hv'0. auto.
  destruct (Int.ltu ($ 64) v'0); auto.
  rewrite Hv'0. auto.
  destruct (Int.eq v'0 ($ 64)); auto.
  destruct (Int.ltu ($ 64) v'0); 
  destruct (Int.eq v'0 ($ 64)); auto.
  hoare_split_pure_all. 
  hoare forward; [idtac|simpl; eauto..].
  sep cancel ASeminfo.
  sep cancel APthreadMutex.
  sep cancel AMqAttr.
  sep cancel AOSCSpaceObjectPointer.
  sep cancel AOSTCBPrioTbl.
  sep lift 2%nat. 
  eapply disj_split. left.
  sep cancel AOSCSpacePrioTbl.
  sep split; eauto.
  unfold val_inj, bool_or in H.
  destruct (Int.ltu ($ 64) v'0) eqn: Hlt; 
  destruct (Int.eq v'0 ($ 64)) eqn: Heq;
  repeat(val_help_H H; simpl in H); tryfalse; auto;
  try(rewrite Intlt_true_is_Zlt in Hlt);
  try(rewrite Inteq_true_is_Zeq in Heq);
  try(rewrite Int.unsigned_repr in Hlt);
  try(rewrite Int.unsigned_repr in Heq); try lia;
  try(rewrite max_unsigned_val); lia.
  eapply disj_rule.
  hoare_split_pure_all.
  eapply pfalse_rule.
  hoare_split_pure_all.
  assert(Hv'0range: Int.unsigned v'0 < 64).
  destruct (Int.ltu ($ 64) v'0) eqn: Hlt; 
  destruct (Int.eq v'0 ($ 64)) eqn: Heq;
  repeat(val_help_H H; simpl in H); destruct H;tryfalse; auto;
  try(rewrite Intlt_false_is_Zge in Hlt);
  try(rewrite Inteq_false_is_Zneq in Heq);
  try(rewrite Int.unsigned_repr in Hlt);
  try(rewrite Int.unsigned_repr in Heq); try lia;
  try(rewrite max_unsigned_val); lia.
  unfold AOSCSpacePrioTbl at 2.
  hoare_split_pure_all.
  assert(Hv'7len: length v'7 = 64%nat).
  simpljoin. auto.
  assert(Hv'8len: length v'8 = 64%nat).
  simpljoin. auto.
  assert(Harraytype: array_type_vallist_match CSPACE ∗ v'7).
  simpljoin. auto.
  eapply backward_rule1 with(p:= <|| v'4 ||>  **
  Aie false **
  Ais nil **
  Acs v'5 **
  Aisr v'6 **
  Aier v'3 **
  AOSCSpacePrioTbl (v'9 ↝ {v'10}) v'7 v'8 v'11 **
  ASeminfo (v'13 ↝ {v'14}) v'15 **
  APthreadMutex (v'16 ↝ {v'17}) v'18 **
  AMqAttr (v'19 ↝ {v'20}) v'21 **
  AOSCSpaceObjectPointer v'22 **
  AOSTCBPrioTbl v'23 v'24 v'25 v'26 v'27 **
  p_local OSLInv ct init_lg **
  LV pCSpace @ CSPACE ∗ |-> v' **
  LV func_capability @ long |-> Vint32 v'2 **
  LV func_capType @ char_t |-> Vint32 v'1 **
  LV destTask_Prio @ char_t |-> Vint32 v'0 **
  A_dom_lenv
    ((func_capability ↝ {long})
     :: (func_capType ↝ {char_t})
        :: (destTask_Prio ↝ {char_t})
           :: (pCSpace ↝ {CSPACE ∗}) :: nil)).
  intros. unfold AOSCSpacePrioTbl. sep auto.
  clear H0.
  eapply seq_rule.
  eapply assign_rule_lvar.
  intros. splits; intros.
  sep cancel pCSpace. eauto.
  sep auto.
  intros.
  unfold AOSCSpacePrioTbl in H0.
  sep normal in H0. sep destruct H0.
  eapply array_member_rv_g.
  unfold GAarray.
  sep normal. sep eexists.
  sep cancel OSCSpacePrioTbl.
  sep cancel Aarray. sep cancel A_dom_lenv.
  eauto.
  simpl. auto.
  eauto. sep get rv. rewrite Hv'0. auto.
  eauto. auto. auto. lia.
  auto. rewrite Hv'7len. auto.
  2: eauto.
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'7len. auto.
  lia. eapply eq_vptr. eauto.
  intros. eexists. sep cancel p_local. simpl. auto.

  assert(Hmatch: rule_type_val_match (Tptr CSPACE) 
  (nth_val'
  (Z.to_nat (Int.unsigned v'0)) v'7) = true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'7len. lia. 

  

  (*IF (pCSpace′ !=ₑ NULL)*)
  
  eapply seq_rule.
  eapply if_rule2'.
  intros.
  eapply uop_rv.
  eapply bop_rv.
  sep get rv.
  sep get rv.
  eauto. 
  unfold val_inj, bop_eval, val_eq.
  clear -Hmatch.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'0)) v'7).
  simpl in Hmatch. tryfalse. auto.
  simpl in Hmatch. tryfalse.
  destruct a; auto.
  simpl. eauto.
  eauto.
  unfold val_inj, uop_eval, bop_eval, val_eq.
  clear -Hmatch. destruct (nth_val' (Z.to_nat (Int.unsigned v'0)) v'7);simpl in Hmatch; tryfalse; auto.
  destruct a. unfold notint, Int.notbool. rewrite Int.eq_true.
  auto. 
  simpl. eauto.

  hoare_split_pure_all.
  assert(exists addr, nth_val'
  (Z.to_nat (Int.unsigned v'0)) v'7 = (Vptr addr)).
  clear -Hmatch H0.
  unfold val_inj, uop_eval, bop_eval, notint, val_eq in H0.
  destruct (nth_val'
  (Z.to_nat (Int.unsigned v'0)) v'7); simpl in Hmatch; tryfalse.
  unfold Int.notbool in H0. 
  assert(Int.eq Int.one Int.zero = false) by auto.
  rewrite H in H0. destruct H0. tryfalse.
  eauto.
  destruct H1.
  rename H1 into Hvptr.
  eapply call_rule'.
  unfold Cap_spec. simpl. 
  unfold CNode_delete_recursive_spec. 
  eauto.
  introv Hsat.
  eapply rvl_elim.
  sep_lift_context_in Hsat (Alvarmapsto pCSpace).
  eapply LV_to_Rv in Hsat.
  eapply inline_tactics.monoasrt_mono in Hsat.
  exact Hsat.
  eapply inline_tactics.Rv_mono.
  clear -Hmatch.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'0)) v'7); simpl in Hmatch; tryfalse; auto.
  auto.
  eapply rvl_elim.
  sep_lift_context_in Hsat (Alvarmapsto func_capType).
  eapply LV_to_Rv in Hsat.
  eapply inline_tactics.monoasrt_mono in Hsat.
  
  exact Hsat.
  eapply inline_tactics.Rv_mono.
  auto. simpl. auto.
  assert(Int.unsigned v'1<=?Byte.max_unsigned = true).
  clear -H2.
  change Byte.max_unsigned with 255.
  int auto.
  rewrite H1. auto.
  eapply rvl_elim.
  sep get rv.
  eapply rvl_nil.
  intros. 
  unfold getasrt.
  unfold CNode_delete_recursivePre.
  unfold CNode_delete_recursivePre'.
 
  sep normal. sep eexists. 
  sep cancel Aie. sep cancel Ais.
  sep cancel Acs. sep cancel Aisr.
  sep cancel Aier. sep cancel Aop.
  sep split.
  sep cancel AOSCSpacePrioTbl.
  sep cancel p_local. 
  sep cancel ASeminfo.
  sep cancel APthreadMutex.
  sep cancel AMqAttr. sep cancel AOSCSpaceObjectPointer.
  sep cancel AOSTCBPrioTbl. exact H1.
  eauto.
  
  auto.
  auto. auto. 
  5: simpl; eauto.
  5: simpl; eauto.
  5: simpl; eauto.
  
  auto. eauto.
  auto.
  {
    unfold ptrvl_to_cspace_to_ptrvl in H7.
    destruct H7.
    assert(Hx: 0 <= Int.unsigned v'0 < 64).
    int auto. 
    assert(Hy: nth_val ∘ (Int.unsigned v'0) v'7 =
    Some (Vptr x) ).
    unfold nat_of_Z.
    rewrite nth_val_imp_nth_val'_2.
    rewrite Hvptr. auto.
    rewrite Hv'7len. lia.

    lets Hz: e Hy. eauto.
  }
  simpl. eauto.
  rewrite Hvptr. auto.
  p_local_go.
  unfold getasrt. unfold CNode_delete_recursivePost.
  unfold CNode_delete_recursivePost'.
  intros. sep destruct H1.
  eexists. sep cancel p_local. simpl. auto.
  unfold getasrt. unfold CNode_delete_recursivePre.
  unfold CNode_delete_recursivePre'.
  intros. sep destruct H1.
  eexists. sep cancel p_local. simpl. auto.
  simpl. auto. 
  rewrite Hvptr. auto.
  assert(Int.unsigned v'1 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H2. int auto.
  rewrite H1. auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  destruct_s s. simpl; eauto.
  intros. 
  sep normal. sep eexists.
  sep lift 20%nat.
  eapply disj_split.
  right.
  sep normal.  sep lift 3%nat. 
  eapply disj_split. right.
  sep cancel A_dom_lenv.
  sep cancel AOSCSpacePrioTbl.
  sep cancel Aie.
  sep cancel Ais. sep cancel Aisr. sep cancel Acs.
  sep cancel Aier. sep cancel pCSpace. sep cancel destTask_Prio.
  sep cancel func_capability. sep cancel Aop.
  sep cancel p_local.
  sep split; eauto.
  simpl; eauto.
  simpl; eauto.
  simpl; eauto.
  clear -Hmatch H0.
  unfold val_inj, uop_eval, bop_eval, notint, val_eq in H0.
  destruct (nth_val'(Z.to_nat (Int.unsigned v'0))v'7); simpl in Hmatch; tryfalse; auto.
  destruct a. unfold Int.notbool in H0.
  rewrite Int.eq_true in H0. destruct H0; tryfalse.
  
  unfold getasrt.
  unfold CNode_delete_recursivePost.
  unfold CNode_delete_recursivePost'.
  eapply disj_rule.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros.
  destruct_s s. simpl; eauto.
  unfold getasrt. unfold CNode_delete_recursivePost.
  unfold CNode_delete_recursivePost'.
  intros.
  unfold ucos_CNode_RevokePost'.
  sep normal. sep eexists.
  sep lift 20%nat. eapply disj_split.
  right.
  sep normal.
  sep lift 3%nat. eapply disj_split. left.
  
  sep cancel A_dom_lenv. 
  sep cancel Aie.
  sep cancel Ais. sep cancel Aisr. sep cancel Acs.
  sep cancel Aier. sep cancel pCSpace. sep cancel destTask_Prio.
  sep cancel func_capability. sep cancel Aop.
  sep cancel p_local.
  sep split in H15.
  sep split; eauto.
  simpl in H1, H4, H9. 
  inverts H1.  inverts H4. inverts H9.
  subst.
  inverts H13. eauto.
  simpl. auto. inverts H13. auto.
  
  simpl in H1. inverts H1.
  simpl in H4. inverts H4.
  simpl in H9. inverts H9.
  inverts H16.
  assert(v'0 = v'42).
  unfolds in H11.
  assert(0 <= Int.unsigned v'0 < 64).
  clear -Hv'0range. int auto.
  destruct H11.
  Lemma nth_val'2nth_val_ptr:
  forall n rtbl x,
    nth_val' n rtbl = Vptr x ->
    nth_val n rtbl = Some (Vptr x).
    Proof.
    intros.
    inductions n;
    simpl in *;  destruct rtbl; simpl in *;tryfalse; try subst; auto.
  Qed.
  unfold nat_of_Z in H4.
  eapply nth_val'2nth_val_ptr in H13.
  lets Hx: H4 H13.
  rewrite H0 in Hx.
  inverts Hx. auto.
  subst v'42.
  auto.
  inverts H13.
  inverts H16.
  clear -Hmatch H14.
  unfold val_inj, uop_eval, bop_eval, val_eq in H14.
  destruct (nth_val'
  (Z.to_nat
     (Int.unsigned v'0)) v'36); simpl in Hmatch; tryfalse; auto.
  unfold notint, Int.notbool in H14.
  assert(Int.eq Int.one Int.zero = false) by auto.
  rewrite H in H14.
  destruct H14; tryfalse.
  hoare_split_pure_all.
  eapply pfalse_rule.
  Unshelve. auto.
Qed.