Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
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
From SimpleC.EE Require Import C_59_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_59.
Local Open Scope sac.

Lemma proof_of_largest_prime_factor_safety_wit_5 : largest_prime_factor_safety_wit_5.
Proof.
	unfold largest_prime_factor_safety_wit_5.
	intros.
	Intros.
	entailer!.
	match goal with
	| Hinv : lpf_while_inv _ _ _ |- _ =>
		unfold lpf_while_inv in Hinv
	end.
	lia.
Qed.

Lemma proof_of_largest_prime_factor_safety_wit_6 : largest_prime_factor_safety_wit_6.
Proof.
	unfold largest_prime_factor_safety_wit_6.
	intros.
	Intros.
	entailer!.
	unfold lpf_while_inv in H1.
	lia.
Qed.

Lemma proof_of_largest_prime_factor_entail_wit_2 : largest_prime_factor_entail_wit_2.
Proof.
	unfold largest_prime_factor_entail_wit_2.
	intros.
	Intros.
	entailer!.
	unfold lpf_inv in H1.
	destruct H1 as (Hn_ge2 & Hmod & Hsmall & Hbound & Hlarge).
	assert (Hi_ge2 : 2 <= i) by lia.
	assert (Hnpre_ge2 : 2 <= n_pre) by lia.
	assert (Hnpre_max : n_pre <= INT_MAX) by lia.
	pose proof (Zquot_Zdiv_pos n i ltac:(lia) ltac:(lia)) as Hq.
	rewrite Hq in H.
	assert (Hn_le_npre : n <= n_pre).
	{
		destruct (Z_le_gt_dec n n_pre) as [Hle | Hgt].
		- exact Hle.
		- assert (0 <= n_pre < n) by lia.
		  rewrite Z.mod_small in Hmod by lia.
		  lia.
	}
	assert (Hi1_le_n : i + 1 <= n).
	{
		assert (Hi_pos : 0 < i) by lia.
		assert (Hdiv_mul_le : (n / i) * i <= n).
		{
			pose proof (Z.div_mod n i ltac:(lia)) as Hdiv.
			rewrite Z.mul_comm in Hdiv.
			assert (0 <= n mod i) by (apply Z.mod_pos_bound; lia).
			lia.
		}
		assert (Hi_mul_le : i * i <= (n / i) * i).
		{
			apply Z.mul_le_mono_nonneg_r; lia.
		}
		assert (Hi2_le_n : i * i <= n) by lia.
		assert (Hi1_le_i2 : i + 1 <= i * i) by nia.
		lia.
	}
	unfold lpf_while_inv.
	split.
	- lia.
	- split.
	  + exact Hn_ge2.
	  + split.
	    * exact Hmod.
	    * split.
	      { exact Hsmall. }
	      split.
	      { exact Hbound. }
	      intros q Hprime Hqi Hdiv.
	      eapply Hlarge; eauto; lia.
Qed.

Lemma proof_of_largest_prime_factor_return_wit_1 : largest_prime_factor_return_wit_1.
Proof.
	unfold largest_prime_factor_return_wit_1.
	intros.
	Intros.
	entailer!.
	pose proof H1 as Hinv.
	unfold lpf_inv in Hinv.
	destruct Hinv as (Hn_ge2 & _).
	pose proof (Zquot_Zdiv_pos n i ltac:(lia) ltac:(lia)) as Hq.
	rewrite Hq in H.
	eapply (lpf_spec_from_exit n_pre n i); eauto.
Qed.

