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
From SimpleC.EE Require Import C_150_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_150.
Local Open Scope sac.

Lemma proof_of_x_or_y_safety_wit_9 : x_or_y_safety_wit_9.
Proof.
	unfold x_or_y_safety_wit_9.
	intros.
	Intros.
	entailer!.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H0.
	assert (Hi_sq : i * i <= n_pre).
	{ apply square_le_from_loop_guard; lia. }
	nia.
Qed. 

Lemma proof_of_x_or_y_safety_wit_10 : x_or_y_safety_wit_10.
Proof.
	unfold x_or_y_safety_wit_10.
	intros.
	Intros.
	entailer!.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H0.
	assert (Hi_sq : i * i <= n_pre).
	{ apply square_le_from_loop_guard; lia. }
	nia.
Qed. 

Lemma proof_of_x_or_y_entail_wit_1 : x_or_y_entail_wit_1.
Proof.
	unfold x_or_y_entail_wit_1.
	intros.
	Intros.
	entailer!.
Qed. 

Lemma proof_of_x_or_y_entail_wit_2_1 : x_or_y_entail_wit_2_1.
Proof.
	unfold x_or_y_entail_wit_2_1.
	intros.
	Intros.
	entailer!.
	Focus 1.
	intros.
	exists i.
	repeat split; lia.
	Focus 1.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H0.
	assert (Hi_sq : i * i <= n_pre) by (apply square_le_from_loop_guard; lia).
	nia.
Qed. 

Lemma proof_of_x_or_y_entail_wit_2_2 : x_or_y_entail_wit_2_2.
Proof.
	unfold x_or_y_entail_wit_2_2.
	intros.
	Intros.
	entailer!.
	Focus 1.
	intros.
	specialize (H4 H12).
	destruct H4 as [k [[Hk2 Hklt] Hkdiv]].
	exists k.
	lia.
	Focus 1.
	intros.
	assert (k < i \/ k = i) by lia.
	destruct H14 as [Hlt|Heq]; [apply (H3 H12); lia | subst k; exact H].
	Focus 1.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H0.
	assert (Hi_sq : i * i <= n_pre) by (apply square_le_from_loop_guard; lia).
	nia.
Qed. 

Lemma proof_of_x_or_y_return_wit_1 : x_or_y_return_wit_1.
Proof.
	unfold x_or_y_return_wit_1.
	intros.
	Intros.
	entailer!.
	apply problem_150_spec_z_prime; try lia.
	assert (Hquot : n_pre ÷ i = n_pre / i) by (apply Z.quot_div_nonneg; lia).
	rewrite Hquot in H.
	apply prime_of_no_divisors_upto_sqrt with (i := i); try lia.
	- pose proof (div_square_lt_from_exit n_pre i H0 H) as Hlt.
		lia.
	- intros k Hk.
		apply (H2 H11 k Hk).
Qed. 

Lemma proof_of_x_or_y_return_wit_2 : x_or_y_return_wit_2.
Proof.
	unfold x_or_y_return_wit_2.
	intros.
	Intros.
	entailer!.
	apply problem_150_spec_z_not_prime; try lia.
	specialize (H3 H11).
	destruct H3 as [k [[Hk2 Hklt] Hkdiv]].
	eapply (not_prime_of_small_divisor n_pre k); eauto.
	lia.
Qed. 
