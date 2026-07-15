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
From SimpleC.EE Require Import C_108_goal.
From SimpleC.EE Require Import C_108_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_108.
Local Open Scope sac.

Ltac solve_108_pures :=
  unfold Zabs in *;
  repeat match goal with
  | H : ?x = ?y |- _ => subst x || subst y
  end;
  repeat match goal with
  | |- context[Z.abs ?x] => rewrite Z.abs_neq by lia
  | H : context[Z.abs ?x] |- _ => rewrite Z.abs_neq in H by lia
  | |- context[Z.abs ?x] => rewrite Z.abs_eq by lia
  | H : context[Z.abs ?x] |- _ => rewrite Z.abs_eq in H by lia
  end;
  try match goal with
  | Hsafe : count_nums_safe_108 ?l,
    Hi : 0 <= ?i,
    Hlt : ?i < Zlength ?l |- context[Znth ?i ?l 0] =>
      let H := fresh "Hrange" in
      pose proof (count_nums_safe_108_Znth l i Hsafe ltac:(lia)) as H
  end;
  try match goal with
  | Hsafe : count_nums_safe_108 ?l,
    Hi : 0 <= ?i,
    Hlt : ?i < Zlength ?l,
    Hpos : 0 < Znth ?i ?l 0 |- context[sum_digits (Znth ?i ?l 0)] =>
      let H := fresh "Hpos_sum" in
      pose proof (count_nums_safe_108_Znth_pos_sum l i Hsafe ltac:(lia) Hpos) as H
  end;
  try match goal with
  | Hsafe : count_nums_safe_108 ?l,
    Hi : 0 <= ?i,
    Hlt : ?i < Zlength ?l,
    Hnonpos : Znth ?i ?l 0 <= 0 |- context[signed_digit_sum_state_108 (Znth ?i ?l 0) (Z.abs (Znth ?i ?l 0)) 0] =>
      let H := fresh "Hinit_state" in
      pose proof (count_nums_safe_108_Znth_nonpos_state l i Hsafe ltac:(lia) Hnonpos) as H
  end;
  try match goal with
  | Hsafe : count_nums_safe_108 ?l,
    Hi : 0 <= ?i,
    Hlt : ?i < Zlength ?l,
    Hnonpos : Znth ?i ?l 0 <= 0 |- context[signed_digit_sum_state_108 (Znth ?i ?l 0) (- Znth ?i ?l 0) 0] =>
      let H := fresh "Hinit_state" in
      pose proof (count_nums_safe_108_Znth_nonpos_state l i Hsafe ltac:(lia) Hnonpos) as H;
      unfold Zabs in H;
      rewrite Z.abs_neq in H by lia
  end;
  try match goal with
  | Hstate : signed_digit_sum_state_108 ?current ?w ?sum,
    Hw : ?w >= 10 |- context[signed_digit_sum_state_108 ?current (?w ÷ 10) (?sum + (?w % 10))] =>
      let H := fresh "Hstep_state" in
      pose proof (signed_digit_sum_state_108_step current w sum Hstate ltac:(lia)) as H
  end;
  try match goal with
  | Hstate : signed_digit_sum_state_108 ?current ?w ?sum,
    Hw : ?w >= 10 |- context[?sum + (?w % 10)] =>
      let H := fresh "Hstep_bounds" in
      pose proof (signed_digit_sum_state_108_step_bounds current w sum Hstate ltac:(lia)) as H
  end;
  try match goal with
  | Hstate : signed_digit_sum_state_108 ?current ?w ?sum,
    Hw : ?w >= 10 |- context[?w ÷ 10] =>
      let H := fresh "Hstep_bounds" in
      pose proof (signed_digit_sum_state_108_step_bounds current w sum Hstate ltac:(lia)) as H
  end;
  try match goal with
  | Hstate : signed_digit_sum_state_108 ?current ?w ?sum,
    Hw : ?w < 10 |- context[signed_digit_sum_positive_108 ?current (?sum - ?w)] =>
      let H := fresh "Hfinal_state" in
      pose proof (signed_digit_sum_state_108_final current w sum Hstate Hw) as H
  end;
  try match goal with
  | Hstate : signed_digit_sum_state_108 ?current ?w ?sum,
    Hw : ?w < 10 |- context[?sum - ?w] =>
      let H := fresh "Hfinal_bounds" in
      pose proof (signed_digit_sum_state_108_final_bounds current w sum Hstate Hw) as H
  end;
  try match goal with
  | Hprefix : count_nums_prefix_108 ?input ?i ?num,
    Hi_ge : ?i >= Zlength ?input,
    Hi_le : ?i <= Zlength ?input |- problem_108_spec_z ?input ?num =>
      replace i with (Zlength input) in Hprefix by lia;
      exact (count_nums_prefix_108_final input num Hprefix)
  end;
  repeat match goal with
  | |- (_ && _) _ => split
  end;
  try assumption;
  try reflexivity;
  try lia;
  repeat match goal with
  | |- coq_prop _ _ => unfold coq_prop; simpl; solve_108_pures
  end.

Ltac solve_108_vc :=
  try (right; intros);
  pre_process; entailer!;
  solve_108_pures;
  try eapply count_nums_prefix_108_init;
  try (eapply count_nums_prefix_108_step_positive; eauto; lia);
  try (eapply count_nums_prefix_108_step_nonpos_true; eauto; lia);
  try (eapply count_nums_prefix_108_step_nonpos_false; eauto; lia);
  try (eapply count_nums_prefix_108_final; eauto; lia);
  try (eapply signed_digit_sum_state_108_step; eauto; lia);
  try (eapply signed_digit_sum_state_108_final; eauto; lia);
  solve_108_pures;
  try (eapply count_nums_prefix_108_final; eauto; lia);
  solve_108_pures.

Lemma proof_of_abs_return_wit_1_split_goal_1 : abs_return_wit_1_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_abs_return_wit_2_split_goal_1 : abs_return_wit_2_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_safety_wit_8_split_goal_1 : count_nums_safety_wit_8_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_safety_wit_8_split_goal_2 : count_nums_safety_wit_8_split_goal_2.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_safety_wit_8 : count_nums_safety_wit_8.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_safety_wit_13_split_goal_1 : count_nums_safety_wit_13_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_safety_wit_13_split_goal_2 : count_nums_safety_wit_13_split_goal_2.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_safety_wit_13 : count_nums_safety_wit_13.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_1_split_goal_1 : count_nums_entail_wit_1_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_1 : count_nums_entail_wit_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_2_split_goal_1 : count_nums_entail_wit_2_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_2_split_goal_2 : count_nums_entail_wit_2_split_goal_2.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_2_split_goal_3 : count_nums_entail_wit_2_split_goal_3.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_2 : count_nums_entail_wit_2.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_3_split_goal_1 : count_nums_entail_wit_3_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_3 : count_nums_entail_wit_3.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_4 : count_nums_entail_wit_4.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_6_split_goal_1 : count_nums_entail_wit_6_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_6_split_goal_2 : count_nums_entail_wit_6_split_goal_2.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_6_split_goal_3 : count_nums_entail_wit_6_split_goal_3.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_6_split_goal_4 : count_nums_entail_wit_6_split_goal_4.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_6_split_goal_5 : count_nums_entail_wit_6_split_goal_5.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_6 : count_nums_entail_wit_6.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_7 : count_nums_entail_wit_7.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_8_split_goal_1 : count_nums_entail_wit_8_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_8 : count_nums_entail_wit_8.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_9_split_goal_1 : count_nums_entail_wit_9_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_entail_wit_9 : count_nums_entail_wit_9.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_return_wit_1_split_goal_1 : count_nums_return_wit_1_split_goal_1.
Proof. solve_108_vc. Qed.

Lemma proof_of_count_nums_return_wit_1 : count_nums_return_wit_1.
Proof. solve_108_vc. Qed.
