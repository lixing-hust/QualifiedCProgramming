Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import int_array_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.

From SimpleC.EE.LLM_friendly_cases Require Import sll_merge_rel_lib.
Local Open Scope monad.
From SimpleC.EE.LLM_friendly_cases Require Import int_array_merge_rel_lib.
Local Open Scope sac.

Lemma proof_of_merge_safety_wit_5 : merge_safety_wit_5.
Admitted.

Lemma proof_of_merge_safety_wit_8 : merge_safety_wit_8.
Admitted.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Admitted.

Lemma proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Proof. 
Admitted.

Lemma proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Proof. 
Admitted.

Lemma proof_of_merge_entail_wit_3_1 : merge_entail_wit_3_1.
Admitted.

Lemma proof_of_merge_entail_wit_3_2 : merge_entail_wit_3_2.
Admitted.

Lemma proof_of_merge_entail_wit_4 : merge_entail_wit_4.
Admitted.

Lemma proof_of_merge_entail_wit_5_1 : merge_entail_wit_5_1.
Admitted.

Lemma proof_of_merge_entail_wit_5_2 : merge_entail_wit_5_2.
Admitted.

Lemma proof_of_merge_entail_wit_6 : merge_entail_wit_6.
Admitted.

Lemma proof_of_merge_return_wit_1 : merge_return_wit_1.
Admitted.

Lemma proof_of_mergeSort_safety_wit_1 : mergeSort_safety_wit_1.
Admitted.

Lemma proof_of_mergeSort_entail_wit_1 : mergeSort_entail_wit_1.
Admitted.

Lemma proof_of_mergeSort_entail_wit_2 : mergeSort_entail_wit_2.
Admitted.

Lemma proof_of_mergeSort_entail_wit_3 : mergeSort_entail_wit_3.
Admitted.

Lemma proof_of_mergeSort_return_wit_1 : mergeSort_return_wit_1.
Admitted.

Lemma proof_of_mergeSort_partial_solve_wit_1_pure : mergeSort_partial_solve_wit_1_pure.
Admitted.


Lemma proof_of_mergeSort_derive_low_level_spec_aux_by_low_level_spec : mergeSort_derive_low_level_spec_aux_by_low_level_spec.
Admitted.

