Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_friendly_cases Require Import sortArray_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
From SimpleC.EE.LLM_friendly_cases Require Import sortArray_lib.
Local Open Scope sac.

Lemma proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Admitted.

Lemma proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Admitted.

Lemma proof_of_sortArray_entail_wit_3 : sortArray_entail_wit_3.
Admitted.

Lemma proof_of_sortArray_entail_wit_4_1 : sortArray_entail_wit_4_1.
Admitted.

Lemma proof_of_sortArray_entail_wit_4_2 : sortArray_entail_wit_4_2.
Admitted.

Lemma proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Admitted.

