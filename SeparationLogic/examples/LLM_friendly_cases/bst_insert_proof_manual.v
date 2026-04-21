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
From SimpleC.EE.LLM_friendly_cases Require Import bst_insert_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
From SimpleC.EE.LLM_friendly_cases Require Import bst_lib.
Import get_right_most.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_insert_entail_wit_1 : insert_entail_wit_1.
Admitted.

Lemma proof_of_insert_entail_wit_2 : insert_entail_wit_2.
Admitted.

Lemma proof_of_insert_return_wit_1 : insert_return_wit_1.
Admitted.

Lemma proof_of_insert_return_wit_2 : insert_return_wit_2.
Admitted.

Lemma proof_of_insert_entail_wit_3_1 : insert_entail_wit_3_1.
Admitted.

Lemma proof_of_insert_entail_wit_3_2 : insert_entail_wit_3_2.
Admitted.

Lemma proof_of_insert_derive_high_level_spec_by_low_level_spec : insert_derive_high_level_spec_by_low_level_spec.
Admitted.
