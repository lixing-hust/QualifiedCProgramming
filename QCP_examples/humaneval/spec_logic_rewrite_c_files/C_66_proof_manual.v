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
From SimpleC.EE Require Import C_66_goal.
From SimpleC.EE Require Import C_66_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_66.
Local Open Scope sac.

Lemma proof_of_digitSum_safety_wit_5 : digitSum_safety_wit_5.
Proof.
  unfold digitSum_safety_wit_5. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input) by (subst n; lia).
  assert (Hinside : Znth i (c_string input) 0 = Znth i input 0).
  { apply c_string_Znth_inside. exact Hi. }
  assert (Hupper : 65 <= Znth i input 0 <= 90) by (rewrite <- Hinside; lia).
  pose proof (upper_sum_prefix_step_upper_66 i input
    ltac:(unfold string_length in Hi; exact Hi) Hupper) as Hstep.
  unfold upper_sum_safe_66 in PreH8.
  specialize (PreH8 (i + 1) ltac:(unfold string_length in *; lia)).
  entailer!; lia.
Qed.

Lemma proof_of_digitSum_entail_wit_1 : digitSum_entail_wit_1.
Proof.
  unfold digitSum_entail_wit_1. right.
  pre_process_default.
  pose proof (string_length_nonneg input).
  unfold upper_sum_prefix_66, upper_sum_list_z_66.
  simpl.
  entailer!.
Qed.

Lemma proof_of_digitSum_entail_wit_2_1 : digitSum_entail_wit_2_1.
Proof.
  unfold digitSum_entail_wit_2_1. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input) by (subst n; lia).
  assert (Hinside : Znth i (c_string input) 0 = Znth i input 0).
  { apply c_string_Znth_inside. exact Hi. }
  assert (Hupper : 65 <= Znth i input 0 <= 90) by (rewrite <- Hinside; lia).
  pose proof (upper_sum_prefix_step_upper_66 i input
    ltac:(unfold string_length in Hi; exact Hi) Hupper) as Hstep.
  entailer!; lia.
Qed.

Lemma proof_of_digitSum_entail_wit_2_2 : digitSum_entail_wit_2_2.
Proof.
  unfold digitSum_entail_wit_2_2. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input) by (subst n; lia).
  assert (Hinside : Znth i (c_string input) 0 = Znth i input 0).
  { apply c_string_Znth_inside. exact Hi. }
  assert (Hother : Znth i input 0 < 65 \/ 90 < Znth i input 0).
  { left. rewrite <- Hinside. exact PreH2. }
  pose proof (upper_sum_prefix_step_other_66 i input
    ltac:(unfold string_length in Hi; exact Hi) Hother) as Hstep.
  entailer!; lia.
Qed.

Lemma proof_of_digitSum_entail_wit_2_3 : digitSum_entail_wit_2_3.
Proof.
  unfold digitSum_entail_wit_2_3. right.
  pre_process_default.
  assert (Hi : 0 <= i < string_length input) by (subst n; lia).
  assert (Hinside : Znth i (c_string input) 0 = Znth i input 0).
  { apply c_string_Znth_inside. exact Hi. }
  assert (Hother : Znth i input 0 < 65 \/ 90 < Znth i input 0).
  { right. rewrite <- Hinside. lia. }
  pose proof (upper_sum_prefix_step_other_66 i input
    ltac:(unfold string_length in Hi; exact Hi) Hother) as Hstep.
  entailer!; lia.
Qed.

Lemma proof_of_digitSum_return_wit_1 : digitSum_return_wit_1.
Proof.
  unfold digitSum_return_wit_1. right.
  pre_process_default.
  assert (Hdone : i = n) by lia.
  assert (Hsum : sum = upper_sum_prefix_66 (string_length input) input).
  { rewrite PreH10, Hdone, PreH3. reflexivity. }
  pose proof (problem_66_spec_z_of_sum_66 input sum PreH4 Hsum) as Hspec.
  entailer!.
Qed.
