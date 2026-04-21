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
From SimpleC.EE.LLM_friendly_cases.simple_arith Require Import Always_pos_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.LLM_friendly_cases.simple_arith Require Import Apos_lib.
Local Open Scope sac.

Lemma proof_of_Always_positive_simple_return_wit_1 : Always_positive_simple_return_wit_1.
Admitted.

Lemma proof_of_Always_positive_simple_return_wit_2 : Always_positive_simple_return_wit_2.
Admitted.

Lemma proof_of_Always_positive_simple_return_wit_3 : Always_positive_simple_return_wit_3.
Admitted.

Lemma proof_of_Always_positive_simple_return_wit_4 : Always_positive_simple_return_wit_4.
Admitted. 

Lemma proof_of_Always_positive_simple_safety_wit_4 : Always_positive_simple_safety_wit_4.
Proof.
  pre_process.
Qed. 

Lemma proof_of_Always_positive_simple_safety_wit_6 : Always_positive_simple_safety_wit_6.
Proof. pre_process. Qed.  

Lemma proof_of_Always_positive_entail_wit_2 : Always_positive_entail_wit_2.
Proof. 
  pre_process.
Qed.  

Lemma proof_of_Always_positive_return_wit_1 : Always_positive_return_wit_1.
Admitted.  

Lemma proof_of_Always_positive_return_wit_2 : Always_positive_return_wit_2.
Admitted. 

Lemma proof_of_Always_positive_return_wit_3 : Always_positive_return_wit_3.
Admitted.

Lemma proof_of_Always_positive_return_wit_4 : Always_positive_return_wit_4.
Admitted.  

Lemma proof_of_Always_positive_return_wit_5 : Always_positive_return_wit_5.
Admitted.

Lemma proof_of_Always_positive_safety_wit_3 : Always_positive_safety_wit_3.
Proof. pre_process. Qed. 

Lemma proof_of_Always_positive_safety_wit_4 : Always_positive_safety_wit_4.
Proof. pre_process. Qed. 

Lemma proof_of_Always_positive_safety_wit_8 : Always_positive_safety_wit_8.
Proof. pre_process. Qed. 