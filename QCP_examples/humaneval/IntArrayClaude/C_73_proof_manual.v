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
From SimpleC.EE Require Import C_73_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_73.
Local Open Scope sac.

Lemma proof_of_smallest_change_safety_wit_9 : smallest_change_safety_wit_9.
Proof.
  pre_process.
  subst out.
  match goal with
  | H: smallest_change_int_range lv |- _ =>
      destruct (H i ltac:(lia) ltac:(lia)) as [_ Hnext]
  end.
  entailer!.
Qed.

Lemma proof_of_smallest_change_entail_wit_1 : smallest_change_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_smallest_change_entail_wit_2_1 : smallest_change_entail_wit_2_1.
Proof.
  pre_process.
  subst out.
  rewrite count_half_mismatches_upto_step_neq.
  entailer!.
  - lia.
  - rewrite <- H3. exact H.
Qed.

Lemma proof_of_smallest_change_entail_wit_2_2 : smallest_change_entail_wit_2_2.
Proof.
  pre_process.
  subst out.
  rewrite count_half_mismatches_upto_step_eq.
  entailer!.
  - lia.
  - rewrite <- H3. exact H.
Qed.

Lemma proof_of_smallest_change_return_wit_1 : smallest_change_return_wit_1.
Proof.
  pre_process.
  entailer!.
  apply problem_73_spec_z_of_exit with (i := i); auto; lia.
Qed.
