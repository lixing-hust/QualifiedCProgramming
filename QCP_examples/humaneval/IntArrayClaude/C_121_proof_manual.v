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
From SimpleC.EE Require Import C_121_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_121.
Local Open Scope sac.

Lemma proof_of_solutions_safety_wit_10 : solutions_safety_wit_10.
Proof.
  pre_process.
  subst s.
  match goal with
  | H: sum_odd_at_even_int_range lv |- _ =>
      destruct (H i ltac:(lia) ltac:(lia)) as [_ Hsum]
  end.
  entailer!;
  replace (i * 2) with (2 * i) by lia;
  lia.
Qed. 

Lemma proof_of_solutions_entail_wit_1 : solutions_entail_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_solutions_entail_wit_2_1 : solutions_entail_wit_2_1.
Proof.
  pre_process.
  replace (i * 2) with (2 * i) in * by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_odd_at_even_upto_step_odd by lia.
  lia.
Qed. 

Lemma proof_of_solutions_entail_wit_2_2 : solutions_entail_wit_2_2.
Proof.
  pre_process.
  replace (i * 2) with (2 * i) in * by lia.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  rewrite sum_odd_at_even_upto_step_not_odd by lia.
  assumption.
Qed. 

Lemma proof_of_solutions_return_wit_1 : solutions_return_wit_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply problem_121_spec_z_of_exit with (i := i); auto; lia.
Qed. 
