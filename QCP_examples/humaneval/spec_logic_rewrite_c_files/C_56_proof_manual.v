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
From SimpleC.EE Require Import C_56_goal.
From SimpleC.EE Require Import C_56_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_56.
Local Open Scope sac.

Lemma proof_of_correct_bracketing_entail_wit_1 : correct_bracketing_entail_wit_1.
Proof.
  unfold correct_bracketing_entail_wit_1. right.
  pre_process_default.
  pose proof (bracket_state_nil_56 input_l) as Hstate.
  pose proof (Zlength_nonneg input_l) as Hlen.
  subst brackets0.
  unfold string_lib.string_length in *.
  entailer!.
Qed.

Lemma proof_of_correct_bracketing_entail_wit_2_1 : correct_bracketing_entail_wit_2_1.
Proof.
  unfold correct_bracketing_entail_wit_2_1. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_lib.string_length input_l) by (subst n; lia).
  assert (Hinside : Znth i (c_string input_l) 0 = Znth i input_l 0).
  { apply Znth_c_string_56. exact Hi. }
  destruct (problem_56_pre_code_at input_l i PreH12 PreH11 Hi)
    as [Hopen | Hclose]; rewrite Hinside in PreH3, PreH4; congruence.
Qed.

Lemma proof_of_correct_bracketing_entail_wit_2_2 : correct_bracketing_entail_wit_2_2.
Proof.
  unfold correct_bracketing_entail_wit_2_2. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_lib.string_length input_l) by (subst n; lia).
  assert (Hinside : Znth i (c_string input_l) 0 = Znth i input_l 0).
  { apply Znth_c_string_56. exact Hi. }
  assert (Hraw : Znth i input_l 0 = 60) by congruence.
  pose proof (bracket_state_open_56 input_l i level PreH14 Hi Hraw) as Hstep.
  entailer!; eauto; lia.
Qed.

Lemma proof_of_correct_bracketing_entail_wit_2_3 : correct_bracketing_entail_wit_2_3.
Proof.
  unfold correct_bracketing_entail_wit_2_3. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_lib.string_length input_l) by (subst n; lia).
  assert (Hinside : Znth i (c_string input_l) 0 = Znth i input_l 0).
  { apply Znth_c_string_56. exact Hi. }
  assert (Hraw : Znth i input_l 0 = 62) by congruence.
  assert (Hpositive : 0 < level) by lia.
  pose proof (bracket_state_close_56 input_l i level PreH14 Hi Hraw Hpositive)
    as Hstep.
  entailer!; eauto; lia.
Qed.

Lemma proof_of_correct_bracketing_return_wit_1 : correct_bracketing_return_wit_1.
Proof.
  unfold correct_bracketing_return_wit_1. right.
  pre_process_default.
  subst level.
  assert (Hdone : i >= string_lib.string_length input_l) by (subst n; lia).
  pose proof (bracket_state_zero_spec_56 input_l i PreH12 Hdone) as Hspec.
  entailer!.
Qed.

Lemma proof_of_correct_bracketing_return_wit_2 : correct_bracketing_return_wit_2.
Proof.
  unfold correct_bracketing_return_wit_2. right.
  pre_process_default.
  assert (Hdone : i >= string_lib.string_length input_l) by (subst n; lia).
  pose proof (bracket_state_nonzero_spec_56 input_l i level PreH12 Hdone PreH2)
    as Hspec.
  entailer!.
Qed.

Lemma proof_of_correct_bracketing_return_wit_3 : correct_bracketing_return_wit_3.
Proof.
  unfold correct_bracketing_return_wit_3. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_lib.string_length input_l) by (subst n; lia).
  assert (Hinside : Znth i (c_string input_l) 0 = Znth i input_l 0).
  { apply Znth_c_string_56. exact Hi. }
  assert (Hraw : Znth i input_l 0 = 62) by congruence.
  assert (Hlevel : level = 0) by lia.
  subst level.
  pose proof (bracket_state_negative_spec_56 input_l i PreH14 Hi Hraw) as Hspec.
  entailer!.
Qed.
