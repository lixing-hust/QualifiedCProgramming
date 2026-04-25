Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_109_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_109.
Local Open Scope sac.

Lemma proof_of_move_one_ball_safety_wit_5 : move_one_ball_safety_wit_5.
Proof.
  pre_process.
  subst num.
  match goal with
  | H: descents_int_range input_l |- _ =>
      destruct H as [Hrange _];
      pose proof (Hrange i ltac:(lia)) as Hsafe
  end.
  entailer!.
Qed. 

Lemma proof_of_move_one_ball_safety_wit_12 : move_one_ball_safety_wit_12.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  match goal with
  | H: descents_int_range input_l |- _ =>
      destruct H as [_ Hrange]
  end.
  assert (Hgt : Znth (Zlength input_l - 1) input_l 0 > Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  rewrite (cyclic_descents_tail_gt input_l ltac:(lia) Hgt) in Hrange.
  replace arr_size_pre with (Zlength input_l) by lia.
  entailer!.
Qed. 

Lemma proof_of_move_one_ball_entail_wit_1 : move_one_ball_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_move_one_ball_entail_wit_2_1 : move_one_ball_entail_wit_2_1.
Proof.
  pre_process.
  subst num.
  rewrite count_descents_prefix_step_lt by lia.
  entailer!.
Qed. 

Lemma proof_of_move_one_ball_entail_wit_2_2 : move_one_ball_entail_wit_2_2.
Proof.
  pre_process.
  subst num.
  rewrite count_descents_prefix_step_ge by lia.
  entailer!.
Qed. 

Lemma proof_of_move_one_ball_return_wit_1 : move_one_ball_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  entailer!.
  unfold problem_109_spec_z.
  right.
  split.
  - lia.
  - 
  assert (Hle : Znth (Zlength input_l - 1) input_l 0 <= Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  rewrite cyclic_descents_tail_le by lia.
  replace (Zlength input_l) with arr_size_pre by lia.
  lia.
Qed. 

Lemma proof_of_move_one_ball_return_wit_2 : move_one_ball_return_wit_2.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  entailer!.
  unfold problem_109_spec_z.
  right.
  split.
  - lia.
  - 
  assert (Hgt : Znth (Zlength input_l - 1) input_l 0 > Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  rewrite cyclic_descents_tail_gt by lia.
  replace (Zlength input_l) with arr_size_pre by lia.
  lia.
Qed. 

Lemma proof_of_move_one_ball_return_wit_3 : move_one_ball_return_wit_3.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  entailer!.
  unfold problem_109_spec_z.
  left.
  split.
  - lia.
  - 
  assert (Hle : Znth (Zlength input_l - 1) input_l 0 <= Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  rewrite cyclic_descents_tail_le by lia.
  replace (Zlength input_l) with arr_size_pre by lia.
  lia.
Qed. 

Lemma proof_of_move_one_ball_return_wit_4 : move_one_ball_return_wit_4.
Proof.
  pre_process.
  assert (Hi : i = arr_size_pre) by lia.
  subst i num.
  entailer!.
  unfold problem_109_spec_z.
  left.
  split.
  - lia.
  - 
  assert (Hgt : Znth (Zlength input_l - 1) input_l 0 > Znth 0 input_l 0).
  { replace (Zlength input_l) with arr_size_pre by lia; lia. }
  rewrite cyclic_descents_tail_gt by lia.
  replace (Zlength input_l) with arr_size_pre by lia.
  lia.
Qed. 
