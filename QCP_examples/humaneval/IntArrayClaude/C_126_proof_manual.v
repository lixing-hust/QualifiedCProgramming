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
From SimpleC.EE Require Import C_126_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_126.
Local Open Scope sac.

Lemma proof_of_is_sorted_entail_wit_1 : is_sorted_entail_wit_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  apply sorted_no_triple_prefix_1.
Qed. 

Lemma proof_of_is_sorted_entail_wit_2_1 : is_sorted_entail_wit_2_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  eapply sorted_no_triple_prefix_step.
  - lia.
  - eassumption.
  - lia.
  - intros [_ [Heq _]]. contradiction.
Qed. 

Lemma proof_of_is_sorted_entail_wit_2_2 : is_sorted_entail_wit_2_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  eapply sorted_no_triple_prefix_step.
  - lia.
  - eassumption.
  - lia.
  - intros [Hge _]. lia.
Qed. 

Lemma proof_of_is_sorted_entail_wit_2_3 : is_sorted_entail_wit_2_3.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  eapply sorted_no_triple_prefix_step.
  - lia.
  - eassumption.
  - lia.
  - intros [_ [_ Heq]]. contradiction.
Qed. 

Lemma proof_of_is_sorted_return_wit_1 : is_sorted_return_wit_1.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  right.
  split.
  - hnf. lia.
  - split.
    + hnf. apply problem_126_spec_true_of_exit with (i := i); auto; lia.
    + assumption.
Qed. 

Lemma proof_of_is_sorted_return_wit_2 : is_sorted_return_wit_2.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  left.
  split.
  - hnf. reflexivity.
  - split.
    + hnf. apply problem_126_spec_false_of_triple with (i := i); auto; lia.
    + assumption.
Qed. 

Lemma proof_of_is_sorted_return_wit_3 : is_sorted_return_wit_3.
Proof.
  pre_process.
  asrt_simpl_pure; sepcon_assoc_change; andp_cancel; simpl_entail.
  left.
  split.
  - hnf. reflexivity.
  - split.
    + hnf. apply problem_126_spec_false_of_desc with (i := i); auto; lia.
    + assumption.
Qed. 
