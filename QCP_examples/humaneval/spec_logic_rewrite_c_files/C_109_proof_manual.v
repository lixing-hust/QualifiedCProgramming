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
From SimpleC.EE Require Import C_109_goal.
From SimpleC.EE Require Import C_109_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_109.
Local Open Scope sac.

Lemma proof_of_move_one_ball_entail_wit_1_split_goal_1 : move_one_ball_entail_wit_1_split_goal_1.
Proof.
  pre_process.
  entailer!.
  apply move_one_ball_prefix_109_init.
  lia.
Qed.

Lemma proof_of_move_one_ball_entail_wit_1 : move_one_ball_entail_wit_1.
Proof.
  left.
  pre_process.
  entailer!.
  apply move_one_ball_prefix_109_init.
  lia.
Qed.

Lemma proof_of_move_one_ball_entail_wit_2_split_goal_1 : move_one_ball_entail_wit_2_split_goal_1.
Proof.
  pre_process.
  entailer!.
  eapply move_one_ball_prefix_109_step_drop; eauto; lia.
Qed.

Lemma proof_of_move_one_ball_entail_wit_2 : move_one_ball_entail_wit_2.
Proof.
  left.
  pre_process.
  entailer!.
  eapply move_one_ball_prefix_109_step_drop; eauto; lia.
Qed.

Lemma proof_of_move_one_ball_entail_wit_3_split_goal_1 : move_one_ball_entail_wit_3_split_goal_1.
Proof.
  pre_process.
  entailer!.
  eapply move_one_ball_prefix_109_step_nodrop; eauto; lia.
Qed.

Lemma proof_of_move_one_ball_entail_wit_3 : move_one_ball_entail_wit_3.
Proof.
  left.
  pre_process.
  entailer!.
  eapply move_one_ball_prefix_109_step_nodrop; eauto; lia.
Qed.

Lemma proof_of_move_one_ball_entail_wit_5_1_split_goal_1 : move_one_ball_entail_wit_5_1_split_goal_1.
Proof.
  pre_process.
  entailer!.
  assert (Hi_eq : i = arr_size_pre) by lia.
  subst i.
  eapply move_one_ball_wrap_109_step_nodrop.
  - rewrite <- PreH5. lia.
  - exact PreH7.
  - rewrite <- PreH5. exact PreH12.
  - rewrite <- PreH5. exact PreH1.
Qed.

Lemma proof_of_move_one_ball_entail_wit_5_1 : move_one_ball_entail_wit_5_1.
Proof.
  left.
  pre_process.
  entailer!.
  assert (Hi_eq : i = arr_size_pre) by lia.
  subst i.
  eapply move_one_ball_wrap_109_step_nodrop.
  - rewrite <- PreH5. lia.
  - exact PreH7.
  - rewrite <- PreH5. exact PreH12.
  - rewrite <- PreH5. exact PreH1.
Qed.

Lemma proof_of_move_one_ball_entail_wit_5_2_split_goal_1 : move_one_ball_entail_wit_5_2_split_goal_1.
Proof.
  pre_process.
  entailer!.
  assert (Hi_eq : i = arr_size_pre) by lia.
  subst i.
  eapply move_one_ball_wrap_109_step_drop.
  - rewrite <- PreH5. lia.
  - exact PreH7.
  - rewrite <- PreH5. exact PreH12.
  - rewrite <- PreH5. exact PreH1.
Qed.

Lemma proof_of_move_one_ball_entail_wit_5_2_split_goal_2 : move_one_ball_entail_wit_5_2_split_goal_2.
Proof.
  pre_process.
  entailer!.
  assert (Hi_eq : i = arr_size_pre) by lia.
  subst i.
  pose proof (move_one_ball_prefix_109_bound _ _ _ PreH12).
  lia.
Qed.

Lemma proof_of_move_one_ball_entail_wit_5_2 : move_one_ball_entail_wit_5_2.
Proof.
  left.
  pre_process.
  entailer!.
  - assert (Hi_eq : i = arr_size_pre) by lia.
    subst i.
    eapply move_one_ball_wrap_109_step_drop.
    + rewrite <- PreH5. lia.
    + exact PreH7.
    + rewrite <- PreH5. exact PreH12.
    + rewrite <- PreH5. exact PreH1.
  - pose proof (move_one_ball_prefix_109_bound _ _ _ PreH12).
    lia.
Qed.

Lemma proof_of_move_one_ball_return_wit_1 : move_one_ball_return_wit_1.
Proof.
  pre_process.
  left.
  entailer!.
  split; [unfold coq_prop; simpl; lia |].
  split.
  - unfold coq_prop.
    apply move_one_ball_wrap_109_false with (num := num); auto; lia.
  - exact H.
Qed.

Lemma proof_of_move_one_ball_return_wit_2 : move_one_ball_return_wit_2.
Proof.
  pre_process.
  right.
  entailer!.
  split; [unfold coq_prop; simpl; lia |].
  split.
  - unfold coq_prop.
    apply move_one_ball_wrap_109_true with (num := num); auto; lia.
  - exact H.
Qed.

Lemma proof_of_move_one_ball_return_wit_3 : move_one_ball_return_wit_3.
Proof.
  pre_process.
  right.
  entailer!.
  split; [unfold coq_prop; simpl; lia |].
  split.
  2: exact H.
  unfold coq_prop.
  subst arr_size_pre.
  destruct input_l as [|h t].
  - apply problem_109_empty_true.
  - rewrite Zlength_cons in PreH5.
    pose proof (Zlength_nonneg t).
    lia.
Qed.
