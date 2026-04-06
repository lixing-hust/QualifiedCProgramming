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
From SimpleC.EE Require Import C_102_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_102.
Local Open Scope sac.

Lemma mod2_eq1_even_false : forall z : Z,
  z mod 2 = 1 -> Z.even z = false.
Proof.
	intros z Hmod.
	apply Bool.not_true_is_false.
	intro Heven.
	apply Z.even_spec in Heven.
	destruct Heven as [k Hk].
	rewrite Hk in Hmod.
	rewrite Z.mul_comm in Hmod.
	rewrite Z.mod_mul in Hmod by lia.
	lia.
Qed.

Lemma mod2_ne1_pos_even_true : forall z : Z,
  1 <= z -> z mod 2 <> 1 -> Z.even z = true.
Proof.
	intros z Hz_pos Hmod_ne1.
	assert (Hmod_rng : 0 <= z mod 2 < 2) by (apply Z.mod_pos_bound; lia).
	assert (Hmod0 : z mod 2 = 0) by lia.
	apply Z.even_spec.
	exists (z / 2).
	pose proof (Z.div_mod z 2 ltac:(lia)) as Hdiv.
	rewrite Hmod0 in Hdiv.
	rewrite Z.mul_comm in Hdiv.
	lia.
Qed.

Lemma proof_of_choose_num_return_wit_1 : choose_num_return_wit_1.
Proof.
	unfold choose_num_return_wit_1.
	intros.
	Intros.
	entailer!.
	unfold problem_102_spec.
	split.
	- intros [z [Hxz [Hzy _]]].
		lia.
	- intros _.
		reflexivity.
Qed.

Lemma proof_of_choose_num_return_wit_2 : choose_num_return_wit_2.
Proof.
	unfold choose_num_return_wit_2.
	intros.
	Intros.
	entailer!.
	repeat rewrite Z.rem_mod_nonneg in * by lia.
	unfold problem_102_spec.
	split.
	- intros Hex.
		exfalso.
		destruct Hex as [z [Hxz [Hzy Hevenz]]].
		assert (z = y_pre) by lia.
		subst z.
		assert (Hodd : Z.even y_pre = false).
		{
			apply mod2_eq1_even_false.
			assumption.
		}
		rewrite Hodd in Hevenz.
		discriminate.
	- intros _.
		reflexivity.
Qed.

Lemma proof_of_choose_num_return_wit_3 : choose_num_return_wit_3.
Proof.
	unfold choose_num_return_wit_3.
	intros.
	Intros.
	entailer!.
	repeat rewrite Z.rem_mod_nonneg in * by lia.
	unfold problem_102_spec.
	split.
	- intros _.
		repeat split.
		+	assert (Hmod : y_pre mod 2 = 1) by assumption.
			apply Z.even_spec.
			exists (y_pre / 2).
			pose proof (Z.div_mod y_pre 2 ltac:(lia)) as Hdiv.
			rewrite Hmod in Hdiv.
			rewrite Z.mul_comm in Hdiv.
			lia.
		+ lia.
		+ lia.
		+ intros z' Hz'.
			assert (z' = y_pre) by lia.
			subst z'.
			apply mod2_eq1_even_false.
			assumption.
	- intros Hno_even.
		exfalso.
		apply Hno_even.
		exists (y_pre - 1).
		split.
		+ lia.
		+ split.
		  * lia.
		  * assert (Hmod : y_pre mod 2 = 1) by assumption.
		    apply Z.even_spec.
		    exists (y_pre / 2).
		    pose proof (Z.div_mod y_pre 2 ltac:(lia)) as Hdiv.
		    rewrite Hmod in Hdiv.
		    rewrite Z.mul_comm in Hdiv.
		    lia.
Qed.

Lemma proof_of_choose_num_return_wit_4 : choose_num_return_wit_4.
Proof.
	unfold choose_num_return_wit_4.
	intros.
	Intros.
	entailer!.
	repeat rewrite Z.rem_mod_nonneg in * by lia.
	unfold problem_102_spec.
	split.
	- intros _.
		repeat split.
		+ apply mod2_ne1_pos_even_true.
		  * lia.
		  * assumption.
		+ lia.
		+ lia.
		+ intros z' Hz'.
			exfalso.
			lia.
	- intros Hno_even.
		exfalso.
		apply Hno_even.
		exists y_pre.
		split.
		+ lia.
		+ split.
		  * lia.
		  * apply mod2_ne1_pos_even_true; [lia | assumption].
Qed.

Lemma proof_of_choose_num_return_wit_5 : choose_num_return_wit_5.
Proof.
	unfold choose_num_return_wit_5.
	intros.
	Intros.
	entailer!.
	repeat rewrite Z.rem_mod_nonneg in * by lia.
	unfold problem_102_spec.
	split.
	- intros _.
		repeat split.
		+ apply mod2_ne1_pos_even_true.
		  * lia.
		  * assumption.
		+ lia.
		+ lia.
		+ intros z' Hz'.
			exfalso.
			lia.
	- intros Hno_even.
		exfalso.
		apply Hno_even.
		exists y_pre.
		split.
		+ lia.
		+ split.
		  * lia.
		  * apply mod2_ne1_pos_even_true; [lia | assumption].
Qed.

