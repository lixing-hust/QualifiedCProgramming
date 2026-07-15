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
From SimpleC.EE Require Import C_67_goal.
From SimpleC.EE Require Import C_67_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_67.
Local Open Scope sac.

Ltac solve_fruit_67 :=
  pre_process; entailer!;
  repeat match goal with
  | H : digit_value_z_67 ?ch = ?rhs |- context[?rhs] => rewrite <- H
  | H : ?ch = Znth ?i (c_string ?s) 0 |- context[digit_value_z_67 ?ch] => rewrite H
  | H : ?ch = Znth ?i (c_string ?s) 0 |- context[is_digit_z_67 ?ch] => rewrite H
  | H : ?x = ?y |- context[problem_67_spec_z _ ?x _] => rewrite H
  | H : ?x = ?y |- context[problem_67_pre_z _ ?x] => rewrite H
  | H : ?x = ?y |- context[fruit_safe_input_67 _ ?x] => rewrite H
  | H : ?x = ?y |- context[fruit_scan_state_67 _ ?x _ _ _ _] => rewrite H
  end;
  repeat match goal with
  | H1 : ?i >= ?len, H2 : ?i <= ?len |- _ =>
      assert (i = len) by lia; subst i
  end;
  repeat match goal with
  | H : ?len = string_length ?s |- context[?len] => rewrite H
  end;
  repeat match goal with
  | H : ?len = string_length ?s |- _ => subst len
  end;
  repeat match goal with
  | H : fruit_scan_state_67 _ _ (string_length _) _ _ _ |- _ =>
      unfold string_length in H
  end;
  try solve [eapply fruit_scan_initial_67; eauto];
  try solve [eapply fruit_digit_reset_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_digit_accum_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_nondigit_skip_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_nondigit_commit_first_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_nondigit_commit_second_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_nondigit_drop_extra_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_tail_no_cur_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_tail_commit_first_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_tail_commit_second_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_tail_drop_extra_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_default_num1_zero_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [eapply fruit_default_num2_zero_67; eauto;
    unfold string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; lia];
  try solve [pose proof (fruit_final_spec_67 _ _ _ _ _ ltac:(eauto) ltac:(eauto) ltac:(lia) ltac:(lia));
    unfold int_max_67 in *; tauto];
  try solve [unfold string_length; apply Zlength_nonneg];
  try solve [subst; unfold string_length; apply Zlength_nonneg];
  try solve [unfold fruit_scan_state_67, bounded_parse_value_67,
    string_length, is_digit_z_67, digit_value_z_67, int_max_67 in *; intuition lia];
  try solve [unfold is_digit_z_67, digit_value_z_67, int_max_67 in *; lia].

Lemma proof_of_fruit_distribution_entail_wit_1 : fruit_distribution_entail_wit_1.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_2 : fruit_distribution_entail_wit_2.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_3_1 : fruit_distribution_entail_wit_3_1.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_3_2 : fruit_distribution_entail_wit_3_2.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_4 : fruit_distribution_entail_wit_4.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_5_1 : fruit_distribution_entail_wit_5_1.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_5_2 : fruit_distribution_entail_wit_5_2.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_6_1 : fruit_distribution_entail_wit_6_1.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_6_2 : fruit_distribution_entail_wit_6_2.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_7_1 : fruit_distribution_entail_wit_7_1.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_7_2 : fruit_distribution_entail_wit_7_2.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_8_1 : fruit_distribution_entail_wit_8_1.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_8_2 : fruit_distribution_entail_wit_8_2.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_10 : fruit_distribution_entail_wit_10.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_11 : fruit_distribution_entail_wit_11.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_12 : fruit_distribution_entail_wit_12.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_13 : fruit_distribution_entail_wit_13.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_14_1 : fruit_distribution_entail_wit_14_1.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_14_2 : fruit_distribution_entail_wit_14_2.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_14_3 : fruit_distribution_entail_wit_14_3.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_15_1 : fruit_distribution_entail_wit_15_1.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_15_2 : fruit_distribution_entail_wit_15_2.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_15_3 : fruit_distribution_entail_wit_15_3.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_15_4 : fruit_distribution_entail_wit_15_4.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_15_5 : fruit_distribution_entail_wit_15_5.
Proof. solve_fruit_67. Qed.

Lemma proof_of_fruit_distribution_entail_wit_15_6 : fruit_distribution_entail_wit_15_6.
Proof. solve_fruit_67. Qed.
