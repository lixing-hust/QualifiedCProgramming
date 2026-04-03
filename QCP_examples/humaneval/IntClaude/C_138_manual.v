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
From SimpleC.EE Require Import C_138_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_138.
Local Open Scope sac.

Lemma proof_of_is_equal_to_sum_even_return_wit_1 : is_equal_to_sum_even_return_wit_1.
Proof.
	unfold is_equal_to_sum_even_return_wit_1.
	intros.
	Intros.
	entailer!.
	unfold problem_138_spec_z.
	split.
	-	intros _.
		pose proof H0 as Hrem.
		apply Z.rem_divide in Hrem.
		2: { lia. }
		destruct Hrem as [q Hq].
		exists 2, 2, 2, (n_pre - 6).
		repeat split.
		+	exists 1. split; lia.
		+	exists 1. split; lia.
		+	exists 1. split; lia.
		+	exists (q - 3).
			split.
			*	lia.
			*	lia.
		+	lia.
	-	intros _. lia.
Qed.

Lemma proof_of_is_equal_to_sum_even_return_wit_2 : is_equal_to_sum_even_return_wit_2.
Proof.
	unfold is_equal_to_sum_even_return_wit_2.
	intros.
	Intros.
	entailer!.
	unfold problem_138_spec_z.
	split.
	-	intros Hnz. exfalso. apply Hnz. reflexivity.
	-	intros (e1 & e2 & e3 & e4 & He1 & He2 & He3 & He4 & Hsum).
		destruct He1 as [k1 [Heq1 Hk1]].
		destruct He2 as [k2 [Heq2 Hk2]].
		destruct He3 as [k3 [Heq3 Hk3]].
		destruct He4 as [k4 [Heq4 Hk4]].
		assert (Hge1 : e1 >= 2) by lia.
		assert (Hge2 : e2 >= 2) by lia.
		assert (Hge3 : e3 >= 2) by lia.
		assert (Hge4 : e4 >= 2) by lia.
		exfalso.
		lia.
Qed.

Lemma proof_of_is_equal_to_sum_even_return_wit_3 : is_equal_to_sum_even_return_wit_3.
Proof.
	unfold is_equal_to_sum_even_return_wit_3.
	intros.
	Intros.
	entailer!.
	unfold problem_138_spec_z.
	split.
	-	intros Hnz. exfalso. apply Hnz. reflexivity.
	-	intros (e1 & e2 & e3 & e4 & He1 & He2 & He3 & He4 & Hsum).
		destruct He1 as [k1 [Heq1 Hk1]].
		destruct He2 as [k2 [Heq2 Hk2]].
		destruct He3 as [k3 [Heq3 Hk3]].
		destruct He4 as [k4 [Heq4 Hk4]].
		assert (Heven : n_pre % 2 = 0).
		{
			rewrite Hsum.
			rewrite Heq1, Heq2, Heq3, Heq4.
			replace (2 * k1 + 2 * k2 + 2 * k3 + 2 * k4) with (2 * (k1 + k2 + k3 + k4)) by lia.
			rewrite Z.mul_comm.
			rewrite Z.rem_mul by lia.
			reflexivity.
		}
		exfalso.
		apply H.
		exact Heven.
Qed.

