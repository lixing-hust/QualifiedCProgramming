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
From SimpleC.EE Require Import C_146_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_146.
Local Open Scope sac.

Lemma proof_of_specialFilter_safety_wit_15 : specialFilter_safety_wit_15.
Proof.
  pre_process.
  match goal with
  | H : special_filter_prefix i input_l num |- _ =>
      pose proof (special_filter_prefix_count_bounds i input_l num H)
  end.
  entailer!.
Qed. 

Lemma proof_of_specialFilter_entail_wit_1 : specialFilter_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply special_filter_prefix_0.
Qed. 

Lemma proof_of_specialFilter_entail_wit_2 : specialFilter_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  - apply first_digit_state_init. lia.
  - pose proof (last_digit_rem_bounds (Znth i input_l 0) ltac:(lia)); lia.
  - pose proof (last_digit_rem_bounds (Znth i input_l 0) ltac:(lia)); lia.
Qed. 

Lemma proof_of_specialFilter_entail_wit_3 : specialFilter_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  apply first_digit_state_step; try assumption; lia.
Qed. 

Lemma proof_of_specialFilter_entail_wit_4 : specialFilter_entail_wit_4.
Proof.
  pre_process.
  entailer!.
  pose proof H14 as Hstate.
  destruct Hstate as [fuel [[Hfirst_lo Hfirst_hi] [Hpow Hfd]]].
  apply special_number_intro_from_digits
    with (x := Znth i input_l 0) (first := first) (last := last);
    try assumption; lia.
Qed. 

Lemma proof_of_specialFilter_entail_wit_5_1 : specialFilter_entail_wit_5_1.
Proof.
  pre_process.
  entailer!.
  eapply special_filter_prefix_snoc_special; eauto; lia.
Qed. 

Lemma proof_of_specialFilter_entail_wit_5_2 : specialFilter_entail_wit_5_2.
Proof.
  pre_process.
  entailer!.
  match goal with
  | Hs : first_digit_state _ first |- _ =>
      pose proof Hs as Hstate;
      destruct Hstate as [fuel [[Hfirst_lo Hfirst_hi] [Hpow Hfd]]]
  end.
  eapply special_filter_prefix_snoc_not_special; eauto; try lia.
  eapply special_number_false_first_even; eauto; lia.
Qed. 

Lemma proof_of_specialFilter_entail_wit_5_3 : specialFilter_entail_wit_5_3.
Proof.
  pre_process.
  entailer!.
  match goal with
  | Hs : first_digit_state _ first |- _ =>
      pose proof Hs as Hstate;
      destruct Hstate as [fuel [[Hfirst_lo Hfirst_hi] [Hpow Hfd]]]
  end.
  eapply special_filter_prefix_snoc_not_special; eauto; try lia.
  eapply special_number_false_last_even; eauto; lia.
Qed. 

Lemma proof_of_specialFilter_entail_wit_6_2 : specialFilter_entail_wit_6_2.
Proof.
  pre_process.
  entailer!.
  eapply special_filter_prefix_snoc_not_special; eauto; try lia.
  apply special_number_false_of_le10; lia.
Qed. 

Lemma proof_of_specialFilter_return_wit_1 : specialFilter_return_wit_1.
Proof.
  pre_process.
  replace i with nums_size_pre by lia.
  match goal with
  | Hlen : nums_size_pre = Zlength input_l |- _ => rewrite Hlen in *
  end.
  replace i with (Zlength input_l) in * by lia.
  entailer!.
  apply problem_146_spec_z_of_prefix_full.
  assumption.
Qed. 
