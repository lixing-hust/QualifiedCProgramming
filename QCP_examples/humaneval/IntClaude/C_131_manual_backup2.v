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
From SimpleC.EE Require Import C_131_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_131.
Local Open Scope sac.

Lemma proof_of_digits_safety_wit_12 : digits_safety_wit_12.
Proof.
	admit.
Admitted. 

Lemma proof_of_digits_entail_wit_2_1 : digits_entail_wit_2_1.
Proof.
	unfold digits_entail_wit_2_1.
	intros.
	Intros.
	entailer!; try apply Z.quot_pos; lia.
Qed. 

Lemma proof_of_digits_entail_wit_2_2 : digits_entail_wit_2_2.
Proof.
	unfold digits_entail_wit_2_2.
	intros.
	Intros.
	entailer!.
	- apply Z.div_pos; lia.
	- assert (Hmod10 : 0 <= n % 10 < 10) by (apply Z.mod_pos_bound; lia).
	  assert (Hmod2 : 0 <= (n % 10) % 2 < 2) by (apply Z.mod_pos_bound; lia).
	  lia.
	- assert (Hmod10 : 0 <= n % 10 < 10) by (apply Z.mod_pos_bound; lia).
	  nia.
Qed. 

Lemma proof_of_digits_return_wit_1 : digits_return_wit_1.
Proof.
	unfold digits_return_wit_1.
	intros.
	Intros.
	entailer!.
	unfold problem_131_spec_z, problem_131_spec.
	lia.
Qed. 

