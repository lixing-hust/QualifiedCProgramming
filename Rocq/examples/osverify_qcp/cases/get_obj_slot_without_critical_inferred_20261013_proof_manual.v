Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.osverify_qcp.cases Require Import get_obj_slot_without_critical_inferred_20261013_goal.
From SimpleC.EE.osverify_qcp.cases Require Import get_obj_slot_without_critical_inferred_20261013_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.osverify_qcp.cases.get_obj_slot_without_critical_inferred_20261013_lib.
Local Open Scope sac.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_1 : Get_Obj_Slot_without_critical_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_no_match; intros; lia.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_2 : Get_Obj_Slot_without_critical_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : gos_input _ _ _ _ _ _ _ _ |- _ =>
    unfold gos_input in H; destruct H as [Hrange Hinput]
  end.
  rewrite unsigned_last_nbits_eq in * by (cbn; lia).
  destruct Hinput as [Hbad | [Hprio [He [Hu [Hp Hcases]]]]]; [lia |].
  destruct Hcases as [[Hz _] | [_ [Hsafe _]]]; [contradiction | exact Hsafe].
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_3 : Get_Obj_Slot_without_critical_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : gos_input _ _ _ _ _ _ _ _ |- _ =>
    unfold gos_input in H; destruct H as [Hrange Hinput]
  end.
  rewrite unsigned_last_nbits_eq in * by (cbn; lia).
  destruct Hinput as [Hbad | [Hprio [He [Hu [Hp Hcases]]]]]; [lia |].
  destruct Hcases as [[Hz _] | [_ [Hsafe _]]]; [contradiction |].
  destruct Hsafe as [Hex | [r Hfirst]].
  - destruct Hex as [[_ Hnil] | [Heb [Hlim _]]].
    + subst xs; unfold gos_limit; cbn; lia.
    + lia.
  - unfold gos_first_match in Hfirst; lia.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_4 : Get_Obj_Slot_without_critical_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_limit; pose proof (Nat2Z.is_nonneg (List.length xs)); lia.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_5 : Get_Obj_Slot_without_critical_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : gos_input _ _ _ _ _ _ _ _ |- _ =>
    unfold gos_input in H; destruct H as [Hrange Hinput]
  end.
  rewrite unsigned_last_nbits_eq in * by (cbn; lia).
  destruct Hinput as [Hbad | [Hprio [He [Hu [Hp Hcases]]]]]; [lia |].
  lia.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_6 : Get_Obj_Slot_without_critical_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : gos_input _ _ _ _ _ _ _ _ |- _ =>
    unfold gos_input in H; destruct H as [Hrange Hinput]
  end.
  rewrite unsigned_last_nbits_eq in * by (cbn; lia).
  destruct Hinput as [Hbad | [Hprio [He [Hu [Hp Hcases]]]]]; [lia |].
  lia.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_7 : Get_Obj_Slot_without_critical_entail_wit_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : gos_input _ _ _ _ _ _ _ _ |- _ =>
    unfold gos_input in H; destruct H as [Hrange Hinput]
  end.
  rewrite unsigned_last_nbits_eq in * by (cbn; lia).
  assumption.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_8 : Get_Obj_Slot_without_critical_entail_wit_1_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_input in *; tauto.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_1 : Get_Obj_Slot_without_critical_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_6.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_7.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_1_split_goal_8.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_2_split_goal_1 : Get_Obj_Slot_without_critical_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_no_match in *.
  intros k Hk.
  destruct (Z_lt_ge_dec k i) as [Hki | Hki].
  - apply PreH15. lia.
  - assert (k = j) by lia. subst k. exact PreH2.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_2_split_goal_2 : Get_Obj_Slot_without_critical_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (gos_frontier_bound__search_step xs e func_object_pre i
    PreH14 PreH15 PreH10 PreH4). lia.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_entail_wit_2 : Get_Obj_Slot_without_critical_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_return_wit_1_split_goal_1 : Get_Obj_Slot_without_critical_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_result. right. right. repeat split; try assumption.
  unfold gos_search_result. right. split; [reflexivity |].
  destruct PreH11 as [Hex | [r Hr]]; [exact Hex |].
  destruct Hr as [Hrange [Hbyte [Hlen [Heq Hprefix]]]].
  exfalso. apply (PreH12 r); [lia | exact Heq].
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_return_wit_1 : Get_Obj_Slot_without_critical_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_return_wit_2_split_goal_1 : Get_Obj_Slot_without_critical_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst j. subst j_2.
  unfold gos_result. right. right. repeat split; try assumption.
  unfold gos_search_result. left.
  destruct PreH14 as [Hex | [r Hr]].
  - destruct Hex as [[He Hnil] | [He [Hlen Hnone]]].
    + lia.
    + exfalso. apply (Hnone i); [lia | exact PreH2].
  - assert (r = i) as Hri.
    { destruct Hr as [Hrange [Hbyte [Hlen [Heq Hprefix]]]].
      destruct (Z.lt_trichotomy r i) as [Hlt | [Heqri | Hgt]]; [|exact Heqri|].
      - exfalso. apply (PreH15 r); [lia | exact Heq].
      - exfalso. apply (Hprefix i); [lia | exact PreH2]. }
    subst r. exact Hr.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_return_wit_2 : Get_Obj_Slot_without_critical_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_return_wit_3_split_goal_1 : Get_Obj_Slot_without_critical_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH3 as [Hprio Hinput].
  assert (unsigned_last_nbits prio_pre 32 = prio_pre) as Hcast.
  { unfold unsigned_last_nbits. apply Z.mod_small. lia. }
  unfold gos_result. right. left. repeat split; try reflexivity; lia.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_return_wit_3 : Get_Obj_Slot_without_critical_return_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_return_wit_4_split_goal_1 : Get_Obj_Slot_without_critical_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH2 as [Hprio Hinput].
  assert (unsigned_last_nbits prio_pre 32 = prio_pre) as Hcast.
  { unfold unsigned_last_nbits. apply Z.mod_small. lia. }
  unfold gos_result. left. split; [lia | reflexivity].
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_return_wit_4 : Get_Obj_Slot_without_critical_return_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_2_pure_split_goal_1 : Get_Obj_Slot_without_critical_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : gos_input _ _ _ _ _ _ _ _ |- _ =>
    unfold gos_input in H; destruct H as [Hrange Hinput]
  end.
  rewrite unsigned_last_nbits_eq in * by (cbn; lia).
  destruct Hinput as [Hbad | [Hprio [He [Hu [Hp Hcases]]]]]; [lia |].
  dump_pre_spatial.
  cbn. rewrite Z.mul_comm. exact Hu.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_2_pure : Get_Obj_Slot_without_critical_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_2_pure_split_goal_1.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_4_pure_split_goal_1 : Get_Obj_Slot_without_critical_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with H : gos_input _ _ _ _ _ _ _ _ |- _ =>
    unfold gos_input in H; destruct H as [Hrange Hinput]
  end.
  rewrite unsigned_last_nbits_eq in * by (cbn; lia).
  destruct Hinput as [Hbad | [Hprio [He [Hu [Hp Hcases]]]]]; [lia |].
  dump_pre_spatial.
  change (gos_read_ptr h ( &( "OSCSpacePrioTbl" ) + prio_pre * ptr_size_Z) p).
  rewrite Z.mul_comm. exact Hp.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_4_pure : Get_Obj_Slot_without_critical_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_4_pure_split_goal_1.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_6_pure_split_goal_1 : Get_Obj_Slot_without_critical_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (gos_frontier_bound__search_step xs e func_object_pre i
    PreH15 PreH16 PreH11 PreH5) as Hbound.
  destruct PreH14 as [_ [Hinvalid | [_ [_ [_ [_ [[Hnull _] | [_ [_ Hobjects]]]]]]]]]; try lia.
  apply (Hobjects i). lia.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_6_pure : Get_Obj_Slot_without_critical_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_partial_solve_wit_6_pure_split_goal_1.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_1_split_goal_spatial : Get_Obj_Slot_without_critical_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_exact, gos_preserved, gos_heap_equiv, derivable1.
  intros m Hm. subst m.
  split.
  - intro a. unfold gos_cell_equiv.
    destruct (ConAssertion.s_mem h a); try exact I.
    apply Byte.eqm_refl.
  - split; reflexivity.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_1 : Get_Obj_Slot_without_critical_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_which_implies_wit_1_split_goal_spatial.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_2_split_goal_spatial : Get_Obj_Slot_without_critical_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply gos_read_uint_extract__read_extract; assumption.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_2 : Get_Obj_Slot_without_critical_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_which_implies_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_3_split_goal_spatial : Get_Obj_Slot_without_critical_which_implies_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_restore_uint.
  apply derivable1_wand_elim2.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_3 : Get_Obj_Slot_without_critical_which_implies_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_which_implies_wit_3_split_goal_spatial.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_4_split_goal_spatial : Get_Obj_Slot_without_critical_which_implies_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply gos_read_ptr_extract__read_extract; assumption.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_4 : Get_Obj_Slot_without_critical_which_implies_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_which_implies_wit_4_split_goal_spatial.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_5_split_goal_spatial : Get_Obj_Slot_without_critical_which_implies_wit_5_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_restore_ptr.
  apply derivable1_wand_elim2.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_5 : Get_Obj_Slot_without_critical_which_implies_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_which_implies_wit_5_split_goal_spatial.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_6_split_goal_spatial : Get_Obj_Slot_without_critical_which_implies_wit_6_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply gos_read_ptr_extract__read_extract; assumption.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_6 : Get_Obj_Slot_without_critical_which_implies_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_which_implies_wit_6_split_goal_spatial.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_7_split_goal_spatial : Get_Obj_Slot_without_critical_which_implies_wit_7_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_restore_ptr.
  apply derivable1_wand_elim2.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_7 : Get_Obj_Slot_without_critical_which_implies_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_which_implies_wit_7_split_goal_spatial.
Qed. 

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_8_split_goal_spatial : Get_Obj_Slot_without_critical_which_implies_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold gos_restore_ptr.
  apply derivable1_wand_elim2.
Qed.

Lemma proof_of_Get_Obj_Slot_without_critical_which_implies_wit_8 : Get_Obj_Slot_without_critical_which_implies_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_Get_Obj_Slot_without_critical_which_implies_wit_8_split_goal_spatial.
Qed. 

