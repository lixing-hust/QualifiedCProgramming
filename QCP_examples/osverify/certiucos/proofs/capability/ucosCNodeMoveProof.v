Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import ios_cap_defs.
Require Import ios_cap.
Require Import CapPure.
Require Import CapSpec.
Require Import Lia.
Require Import ACSpace_defs.
Require Import seplog_trm_tacs.
Require Import ucosCNodeCopyPure.

Open Scope list_scope.
Open Scope Z_scope.
Open Scope code_scope.
Set Nested Proofs Allowed.

Set Keyed Unification.
Lemma ucos_CNode_Move_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal ucos_CNode_Move
                  vl logicl ucos_CNode_MovePre ct->
      Some r =
      BuildRetI os_internal ucos_CNode_Move vl logicl ucos_CNode_MovePost ct->
      exists t d1 d2 s,
      os_internal ucos_CNode_Move = Some (t, d1, d2, s) /\
        {|Cap_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
  init spec.
  rename H9 into Hv'4range.
  rename H10 into Hv'5range.
  rename H11 into Hv'6range.
  unfold nth_val in H, H0, H4.

  inverts H.
  inverts H0.
  inverts H4.

  rename H7 into Hneq.
  unfold AOSCSpacePrioTbl at 2.
  hoare_split_pure_all.
  assert(Hv'13len: length v'13 = 64%nat).
  simpljoin. auto.
  assert(Hv'14len: length v'14 = 64%nat).
  simpljoin. auto.
  assert(Htypematch: array_type_vallist_match CSPACE ∗ v'13).
  simpljoin. auto.
  eapply backward_rule1 with (p:=<|| v'8 ||>  **
  LV cap2 @ Cap ∗ |-> v'3 **
  LV cap1 @ Cap ∗ |-> v'2 **
  Aie false **
  Ais nil **
  Acs v'11 **
  Aisr v'12 **
  Aier v'7 **
  AOSCSpaceObjectPointer v'16 **
  AOSCSpacePrioTbl (v'9 ↝ {v'10}) v'13 v'14
    v'15 **
  p_local OSLInv ct init_lg **
  LV pCSpace2 @ CSPACE ∗ |-> v'1 **
  LV pCSpace1 @ CSPACE ∗ |-> v'0 **
  LV idx @ long |-> v' **
  LV func_capability @ long |-> Vint32 v'6 **
  LV srcTask_Prio @ char_t |-> Vint32 v'5 **
  LV destTask_Prio @ char_t |-> Vint32 v'4 **
  A_dom_lenv
    ((func_capability ↝ {long})
    :: (srcTask_Prio ↝ {char_t})
        :: (destTask_Prio ↝ {char_t})
          :: (idx ↝ {long})
              :: (pCSpace1 ↝ {CSPACE ∗})
                :: (pCSpace2 ↝ {CSPACE ∗})
                    :: (cap1 ↝ {Cap ∗})
                      :: (cap2 ↝ {Cap ∗})
                          :: nil)).
  intros. unfold AOSCSpacePrioTbl.
  sep auto.
  clear H.

  hoare forward.
  destruct (Int.ltu ($ SLOT_NUM) v'6); auto.
  destruct (Int.eq v'6 ($ SLOT_NUM)); auto.
  destruct (Int.ltu ($ SLOT_NUM) v'6);
  destruct (Int.eq v'6 ($ SLOT_NUM)); auto.
  hoare_split_pure_all.
  instantiate(1:=Afalse).
  false.
  destruct H.
  unfold val_inj, bool_or in H.
  destruct (Int.ltu ($ SLOT_NUM) v'6) eqn: Hlt;
  destruct (Int.eq v'6 ($ SLOT_NUM)) eqn: Heq;
  (val_help_H H; simpl in H); tryfalse.
  rewrite Intlt_true_is_Zlt in Hlt.
  rewrite Int.unsigned_repr in Hlt. lia.
  unfold SLOT_NUM. rewrite max_unsigned_val. lia.
  rewrite Intlt_true_is_Zlt in Hlt.
  rewrite Int.unsigned_repr in Hlt. lia.
  unfold SLOT_NUM. rewrite max_unsigned_val. lia.
  rewrite Inteq_true_is_Zeq in Heq.
  rewrite Int.unsigned_repr in Heq.
  lia.  unfold SLOT_NUM. rewrite max_unsigned_val. lia.
  eapply disj_rule.
  hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all. clear H. 
  assert(Hv'4: Int.unsigned v'4 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H3. int auto.
  assert(Hv'5: Int.unsigned v'5 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -H2. int auto.
  hoare forward.
  rewrite Hv'4. auto.
  destruct (Int.ltu ($ 64) v'4); auto.
  rewrite Hv'4. auto.
  destruct (Int.eq v'4 ($ 64)); auto.
  destruct (Int.ltu ($ 64) v'4);
  destruct (Int.eq v'4 ($ 64)); auto.
  rewrite Hv'5. auto.
  destruct (Int.ltu ($ 64) v'5); auto.
  rewrite Hv'5. auto.
  destruct (Int.eq v'5 ($ 64)); auto.
  destruct (Int.ltu ($ 64) v'5);
  destruct (Int.eq v'5 ($ 64)); auto.
  destruct (Int.ltu ($ 64) v'4);
  destruct (Int.eq v'4 ($ 64)); 
  destruct (Int.ltu ($ 64) v'5);
  destruct (Int.eq v'5 ($ 64)); auto.
  instantiate(1:=Afalse).

  hoare_split_pure_all. false.
  destruct H.
  unfold OS_LOWEST_PRIO in Hv'4range, Hv'5range.
  unfold val_inj, bool_or in H.
  destruct (Int.ltu ($ 64) v'4) eqn: Hv'4lt;
  destruct (Int.eq v'4 ($ 64)) eqn: Hv'4eq; 
  destruct (Int.ltu ($ 64) v'5) eqn: Hv'5lt;
  destruct (Int.eq v'5 ($ 64))eqn: Hv'5eq;
  repeat(val_help_H H; simpl in H); tryfalse;
  try(rewrite Intlt_true_is_Zlt in Hv'4lt);
  try(rewrite Inteq_true_is_Zeq in Hv'4eq);
  try(rewrite Intlt_true_is_Zlt in Hv'5lt);
  try(rewrite Inteq_true_is_Zeq in Hv'5eq);
  try(rewrite Int.unsigned_repr in Hv'4lt);
  try(rewrite Int.unsigned_repr in Hv'4eq);
  try(rewrite Int.unsigned_repr in Hv'5lt);
  try(rewrite Int.unsigned_repr in Hv'5eq);
  try lia.
  all: try(rewrite max_unsigned_val; lia).
  eapply disj_rule. hoare_split_pure_all.
  eapply pfalse_rule.
  hoare_split_pure_all.
  clear H.

  unfold OS_LOWEST_PRIO in Hv'4range, Hv'5range.
  eapply seq_rule.
  eapply assign_rule_lvar.
  intros. splits; intros.
  sep cancel pCSpace1. eauto.
  sep auto.
  intros.
  unfold AOSCSpacePrioTbl in H.
  sep normal in H. sep destruct H.
  eapply array_member_rv_g.
  unfold GAarray.
  sep normal. sep eexists.
  sep cancel OSCSpacePrioTbl.
  sep cancel Aarray. sep cancel A_dom_lenv.
  eauto.
  simpl. auto. eauto.
  sep get rv. rewrite Hv'4. auto.
  eauto. auto.
  lia. 
  unfold OS_LOWEST_PRIO in Hv'4range. lia.
  rewrite Hv'13len. 
  unfold OS_LOWEST_PRIO in Hv'4range. lia.
  2: eauto.
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'13len. lia.
  eapply eq_vptr. eauto.
  intros. eexists. sep cancel p_local. simpl; auto.

  eapply seq_rule.
  eapply assign_rule_lvar.
  intros. splits; intros.
  sep cancel pCSpace2. eauto.
  sep auto.
  intros.
  unfold AOSCSpacePrioTbl in H.
  sep normal in H. sep destruct H.
  eapply array_member_rv_g.
  unfold GAarray.
  sep normal. sep eexists.
  sep cancel OSCSpacePrioTbl.
  sep cancel Aarray. sep cancel A_dom_lenv.
  eauto.
  simpl. auto. eauto.
  sep get rv. rewrite Hv'5. auto.
  eauto. auto.
  lia. 
  unfold OS_LOWEST_PRIO in Hv'4range. lia.
  rewrite Hv'13len. 
  unfold OS_LOWEST_PRIO in Hv'4range. lia.
  2: eauto.
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'13len. lia.
  eapply eq_vptr. eauto.
  intros. eexists. sep cancel p_local. simpl; auto.
  assert(HpCSpace1type: rule_type_val_match CSPACE ∗ (nth_val' (Z.to_nat (Int.unsigned v'4)) v'13) =
  true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'13len. lia.
  assert(HpCSpace2type: rule_type_val_match CSPACE ∗ (nth_val' (Z.to_nat (Int.unsigned v'5)) v'13) =
  true).
  eapply array_type_vallist_match_imp_rule_type_val_match; eauto.
  rewrite Hv'13len. lia.

  hoare forward.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'4)) v'13); auto.
  destruct a. auto.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'5)) v'13); auto.
  destruct a. auto.
  unfold val_inj, bool_or, val_eq.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'4)) v'13); 
  destruct (nth_val' (Z.to_nat (Int.unsigned v'5)) v'13); try destruct a; try destruct a0; auto.
  hoare_split_pure_all.
  eapply rete_rule'.
  intros. sep get rv.
  intros. sep normal. sep eexists.
  sep lift 16%nat.  eapply disj_split.
  left. sep auto; simpl; eauto.
  unfold val_inj, bool_or, val_eq in H.
  destruct H.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'4)) v'13);
  destruct (nth_val' (Z.to_nat (Int.unsigned v'5)) v'13); 
  repeat(val_help_H H; simpl in H); tryfalse; auto.
  destruct a. destruct a0.
  val_help_H H. 
  simpl in H. tryfalse.

  eapply disj_rule. hoare_split_pure_all. eapply pfalse_rule.
  hoare_split_pure_all.
  assert(nth_val' (Z.to_nat (Int.unsigned v'4)) v'13 <> Vnull /\ nth_val' (Z.to_nat (Int.unsigned v'5)) v'13 <> Vnull).
  clear -HpCSpace1type HpCSpace2type H.
  unfold rule_type_val_match in HpCSpace1type.
  unfold rule_type_val_match in HpCSpace2type.
  unfold val_inj, bool_or, val_eq in H.
  destruct (nth_val' (Z.to_nat (Int.unsigned v'4)) v'13);
  destruct (nth_val' (Z.to_nat (Int.unsigned v'5)) v'13); (val_help_H H; simpl in H); destruct H; try destruct a;
  try destruct a0; tryfalse; auto.
  destruct H0.
  clear H.
  rename H0 into Hnotnull1.
  rename H1 into Hnotnull2.

  (*由于要进行数组的拆分得到元素的位置，所以需要进行分类讨论
  destTask_Prio 和 srcTask_Prio的大小*)
  assert(Hc1: (Int.unsigned v'4 > Int.unsigned v'5) ).
  lia.
  Require Import ucosCNodeMovePart1Proof.
  (*第一种情况，当srcTaskPrio位于destTask_Prio的左边时*)
  eapply ucosCNodeMovePart1_proof; eauto.
  (* Require Import ucosCNodeCopyPart2Proof.
  (*第二种情况，当srcTaskPrio位于destTask_Prio的右边时*)
  eapply ucosCNodeCopyPart2_proof; eauto. *)
  Unshelve.
  all: auto.
Qed.



