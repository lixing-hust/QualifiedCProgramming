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
	unfold digits_safety_wit_12.
	intros.
	Intros.
	entailer!.
	- assert (Hdigit_nonneg : 0 <= n % 10).
		{
			rewrite Z.rem_mod_nonneg by lia.
			apply Z.mod_pos_bound; lia.
		}
		nia.
	- assert (Hdigit_le : n % 10 <= tail_odd_prod_z n).
		{ apply tail_odd_prod_z_ge_rem_digit; lia. }
		assert (Hdigit_nonneg : 0 <= n % 10).
		{
			rewrite Z.rem_mod_nonneg by lia.
			apply Z.mod_pos_bound; lia.
		}
		nia.
Qed. 

Lemma proof_of_digits_entail_wit_1 : digits_entail_wit_1.
Proof.
	unfold digits_entail_wit_1.
	intros.
	Intros.
	entailer!.
	apply digits_state_init_spec.
	lia.
Qed. 

Lemma proof_of_digits_entail_wit_2_1 : digits_entail_wit_2_1.
Proof.
	unfold digits_entail_wit_2_1.
	intros.
	Intros.
	entailer!.
	- assert (Hstate_step :
			digits_state_z n prod has = digits_state_z (n ÷ 10) (prod * (n % 10)) 1).
		{
			apply digits_state_step_odd_preserve; try lia.
		}
		rewrite <- Hstate_step.
		exact H8.
	- pose proof H7 as Hbound.
		pose proof (tail_step_odd_cstyle n ltac:(lia) H) as Htail.
		rewrite Htail in Hbound.
		nia.
	- assert (Hdigit_le : n % 10 <= tail_odd_prod_z n).
		{ apply tail_odd_prod_z_ge_rem_digit; lia. }
		assert (Hdigit_nonneg : 0 <= n % 10).
		{
			rewrite Z.rem_mod_nonneg by lia.
			apply Z.mod_pos_bound; lia.
		}
		nia.
	- assert (Hdigit_nonneg : 0 <= n % 10).
		{
			rewrite Z.rem_mod_nonneg by lia.
			apply Z.mod_pos_bound; lia.
		}
		assert (Hdigit_nz : n % 10 <> 0).
		{
			intro Hz.
			rewrite Hz in H.
			vm_compute in H.
			discriminate.
		}
		nia.
	- rewrite Zquot_eq_Zdiv_pos by lia.
		assert (0 <= n / 10) by (apply Z.div_pos; lia).
		lia.
Qed. 

Lemma proof_of_digits_entail_wit_2_2 : digits_entail_wit_2_2.
Proof.
	unfold digits_entail_wit_2_2.
	intros.
	Intros.
	entailer!.
	- assert (Hstate_step :
			digits_state_z n prod has = digits_state_z (n ÷ 10) prod has).
		{
			apply digits_state_step_even_preserve; try lia.
		}
		rewrite <- Hstate_step.
		exact H8.
	- pose proof H7 as Hbound.
		pose proof (tail_step_even_cstyle n ltac:(lia) H) as Htail.
		rewrite Htail in Hbound.
		exact Hbound.
	- rewrite Zquot_eq_Zdiv_pos by lia.
		assert (0 <= n / 10) by (apply Z.div_pos; lia).
		lia.
Qed. 

Lemma proof_of_digits_return_wit_1 : digits_return_wit_1.
Proof.
	unfold digits_return_wit_1.
	intros.
	Intros.
	entailer!.
	assert (n = 0) by lia.
	assert (has = 1) by lia.
	subst n has.
	unfold digits_state_z in H8.
	simpl in H8.
	replace (prod * tail_odd_prod_z 0) with prod in H8.
	- exact H8.
	- unfold tail_odd_prod_z, tail_odd_prod_nat.
		simpl.
		ring.
Qed. 

Lemma proof_of_digits_return_wit_2 : digits_return_wit_2.
Proof.
	unfold digits_return_wit_2.
	intros.
	Intros.
	entailer!.
	assert (n = 0) by lia.
	subst n.
	unfold digits_state_z in H8.
	rewrite H in H8.
	rewrite Z.eqb_refl in H8.
	simpl in H8.
	exact H8.
Qed. 
