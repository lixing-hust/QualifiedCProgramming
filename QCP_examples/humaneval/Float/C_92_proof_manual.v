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
From SimpleC.EE Require Import C_92_goal.
From SimpleC.EE Require Import C_92_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_92.
Local Open Scope sac.

Lemma proof_of_any_int_safety_wit_7 : any_int_safety_wit_7.
Proof.
  pre_process; try (unfold problem_92_pre in *; entailer!).
Qed.

Lemma proof_of_any_int_safety_wit_8 : any_int_safety_wit_8.
Proof.
  pre_process; try (unfold problem_92_pre in *; entailer!).
Qed.

Lemma proof_of_any_int_safety_wit_10 : any_int_safety_wit_10.
Proof.
  pre_process; try (unfold problem_92_pre in *; entailer!).
Qed.

Lemma proof_of_any_int_safety_wit_11 : any_int_safety_wit_11.
Proof.
  pre_process; try (unfold problem_92_pre in *; entailer!).
Qed.

Lemma proof_of_any_int_safety_wit_13 : any_int_safety_wit_13.
Proof.
  pre_process; try (unfold problem_92_pre in *; entailer!).
Qed.

Lemma proof_of_any_int_safety_wit_14 : any_int_safety_wit_14.
Proof.
  pre_process; try (unfold problem_92_pre in *; entailer!).
Qed.

Lemma proof_of_any_int_return_wit_1 : any_int_return_wit_1.
Proof.
  pre_process.
  unfold problem_92_spec, fp32_sum_relation_92.
  entailer!.
  right; split; [reflexivity|].
  unfold fp32_ne in *.
  tauto.
Qed.

Lemma proof_of_any_int_return_wit_2 : any_int_return_wit_2.
Proof.
  pre_process.
  unfold problem_92_spec, fp32_sum_relation_92.
  entailer!.
  left; split; [reflexivity|].
  split.
  - eapply (roundf_observed_eq_integer_92
      a_bits result_bits a_pre retval); eassumption.
  - split.
    + eapply (roundf_observed_eq_integer_92
        b_bits result_bits_2 b_pre retval_2); eassumption.
    + split.
      * eapply (roundf_observed_eq_integer_92
          c_bits result_bits_3 c_pre retval_3); eassumption.
      * right; right; assumption.
Qed.

Lemma proof_of_any_int_return_wit_3 : any_int_return_wit_3.
Proof.
  pre_process.
  unfold problem_92_spec, fp32_sum_relation_92.
  entailer!.
  left; split; [reflexivity|].
  split.
  - eapply (roundf_observed_eq_integer_92
      a_bits result_bits a_pre retval); eassumption.
  - split.
    + eapply (roundf_observed_eq_integer_92
        b_bits result_bits_2 b_pre retval_2); eassumption.
    + split.
      * eapply (roundf_observed_eq_integer_92
          c_bits result_bits_3 c_pre retval_3); eassumption.
      * right; left; assumption.
Qed.

Lemma proof_of_any_int_return_wit_4 : any_int_return_wit_4.
Proof.
  pre_process.
  unfold problem_92_spec, fp32_sum_relation_92.
  entailer!.
  left; split; [reflexivity|].
  split.
  - eapply (roundf_observed_eq_integer_92
      a_bits result_bits a_pre retval); eassumption.
  - split.
    + eapply (roundf_observed_eq_integer_92
        b_bits result_bits_2 b_pre retval_2); eassumption.
    + split.
      * eapply (roundf_observed_eq_integer_92
          c_bits result_bits_3 c_pre retval_3); eassumption.
      * left; assumption.
Qed.

Lemma proof_of_any_int_return_wit_5 : any_int_return_wit_5.
Proof.
  pre_process.
  unfold problem_92_spec, fp32_sum_relation_92.
  entailer!.
  right; split; [reflexivity|].
  intros [_ [_ [Hc _]]].
  eapply (roundf_observed_ne_not_integer_92
    c_bits result_bits_3 c_pre retval_3); eassumption.
Qed.

Lemma proof_of_any_int_return_wit_6 : any_int_return_wit_6.
Proof.
  pre_process.
  unfold problem_92_spec, fp32_sum_relation_92.
  entailer!.
  right; split; [reflexivity|].
  intros [_ [Hb _]].
  eapply (roundf_observed_ne_not_integer_92
    b_bits result_bits_2 b_pre retval_2); eassumption.
Qed.

Lemma proof_of_any_int_return_wit_7 : any_int_return_wit_7.
Proof.
  pre_process.
  unfold problem_92_spec, fp32_sum_relation_92.
  entailer!.
  right; split; [reflexivity|].
  intros [Ha _].
  eapply (roundf_observed_ne_not_integer_92
    a_bits result_bits a_pre retval); eassumption.
Qed.
