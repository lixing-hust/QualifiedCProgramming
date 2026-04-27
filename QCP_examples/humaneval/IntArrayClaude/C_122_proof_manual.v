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
From SimpleC.EE Require Import C_122_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_122.
Local Open Scope sac.

Lemma proof_of_add_elements_safety_wit_6 : add_elements_safety_wit_6.
Proof.
  pre_process.
  subst s.
  match goal with
  | H: sum_two_digit_int_range k_pre lv |- _ =>
      destruct (H i ltac:(lia) ltac:(lia)) as [_ Hsum]
  end.
  entailer!.
Qed. 

Lemma proof_of_add_elements_entail_wit_1 : add_elements_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_add_elements_entail_wit_2_1 : add_elements_entail_wit_2_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_two_digit_upto_step_in by lia.
  lia.
Qed. 

Lemma proof_of_add_elements_entail_wit_2_2 : add_elements_entail_wit_2_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_two_digit_upto_step_lo by lia.
  assumption.
Qed. 

Lemma proof_of_add_elements_entail_wit_2_3 : add_elements_entail_wit_2_3.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_two_digit_upto_step_hi by lia.
  assumption.
Qed. 

Lemma proof_of_add_elements_return_wit_1 : add_elements_return_wit_1.
Proof.
  pre_process.
  assert (Hi : i = k_pre) by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_122_spec_z_of_exit with (i := i); auto.
Qed. 
