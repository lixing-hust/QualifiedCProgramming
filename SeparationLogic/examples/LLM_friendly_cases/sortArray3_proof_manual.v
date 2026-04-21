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
From SimpleC.EE.LLM_friendly_cases Require Import sortArray3_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_friendly_cases.sortArray_lib.
Local Open Scope sac.

Lemma increasing_cons_local :
	forall x l,
		lowerbound x l ->
		increasing l ->
		increasing (x :: l).
Proof.
	intros x l Hlb Hinc.
	destruct l; simpl; auto.
	destruct Hlb as [Hxy _].
	split; [exact Hxy | exact Hinc].
Qed.

Lemma prefix_suffix_sorted_perm_local :
	forall l1 l2 l3,
		prefix_suffix_sorted l1 l2 ->
		Permutation l2 l3 ->
		prefix_suffix_sorted l1 l3.
Proof.
	intros l1 l2 l3 Hsorted Hperm.
	unfold prefix_suffix_sorted in *.
	intros x Hinx.
	apply (lowerbound_perm x l2 l3 Hperm).
	apply Hsorted.
	exact Hinx.
Qed.

Lemma prefix_suffix_sorted_prefix_perm_local :
	forall l1 l2 l3,
		Permutation l1 l2 ->
		prefix_suffix_sorted l1 l3 ->
		prefix_suffix_sorted l2 l3.
Proof.
	intros l1 l2 l3 Hperm Hsorted.
	unfold prefix_suffix_sorted in *.
	intros x Hinx.
	apply Hsorted.
	eapply Permutation_in.
	- apply Permutation_sym. exact Hperm.
	- exact Hinx.
Qed.

Lemma prefix_suffix_sorted_singleton_le_local :
	forall l x y,
		prefix_suffix_sorted l [x] ->
		x <= y ->
		prefix_suffix_sorted l [y].
Proof.
	intros l x y Hsorted Hxy.
	unfold prefix_suffix_sorted in *.
	intros z Hz.
	specialize (Hsorted z Hz).
	simpl in Hsorted.
	simpl.
	destruct Hsorted as [Hzx _].
	split; [lia | easy].
Qed.

Lemma prefix_suffix_sorted_snoc_singleton_local :
	forall l x y,
		prefix_suffix_sorted l [y] ->
		x <= y ->
		prefix_suffix_sorted (l ++ [x]) [y].
Proof.
	intros l x y Hsorted Hxy.
	unfold prefix_suffix_sorted in *.
	intros z Hz.
	apply in_app_or in Hz.
	destruct Hz as [Hz | Hz].
	- apply Hsorted. exact Hz.
	- simpl in Hz.
		destruct Hz as [Hz | Hz].
		+ subst z. simpl. split; [lia | easy].
		+ contradiction.
Qed.

Lemma prefix_suffix_sorted_extend_suffix_local :
	forall l x l2,
		prefix_suffix_sorted l [x] ->
		prefix_suffix_sorted l l2 ->
		prefix_suffix_sorted l (x :: l2).
Proof.
	intros l x l2 Hsingle Hrest.
	unfold prefix_suffix_sorted in *.
	intros y Hy.
	specialize (Hsingle y Hy).
	specialize (Hrest y Hy).
	simpl in Hsingle.
	simpl.
	destruct Hsingle as [Hyx _].
	split; [exact Hyx | exact Hrest].
Qed.

Lemma replace_Znth_length_local {A: Type}:
	forall (l: list A) n a,
		Zlength (replace_Znth n a l) = Zlength l.
Proof.
	intros l n.
	unfold replace_Znth.
	remember (Z.to_nat n) as k; clear Heqk.
	revert k; induction l; intros.
	- destruct k; simpl; easy.
	- destruct k; simpl; repeat rewrite Zlength_cons; auto.
		rewrite IHl; auto.
Qed.

Lemma replace_Znth_boundary_local {A: Type} :
	forall (prefix tail: list A) x y,
		replace_Znth (Zlength prefix) x (prefix ++ y :: tail) = prefix ++ x :: tail.
Proof.
	induction prefix; intros tail x y.
	- reflexivity.
	- simpl.
		rewrite Zlength_cons.
		pose proof (Zlength_nonneg prefix) as Hlen.
		assert (Hpos : Z.succ (Zlength prefix) > 0) by lia.
		rewrite (replace_Znth_cons (Z.succ (Zlength prefix)) x a (prefix ++ y :: tail)) by exact Hpos.
		replace (Z.succ (Zlength prefix) - 1) with (Zlength prefix) by lia.
		simpl.
		f_equal.
		apply IHprefix.
Qed.

Lemma replace_Znth_boundary_app_local {A: Type} :
	forall (prefix middle tail: list A) x y,
		replace_Znth (Zlength prefix) x ((prefix ++ y :: middle) ++ tail) =
		(prefix ++ x :: middle) ++ tail.
Proof.
	intros prefix middle tail x y.
	replace ((prefix ++ y :: middle) ++ tail) with (prefix ++ y :: (middle ++ tail)) by (rewrite <- app_assoc; reflexivity).
	replace ((prefix ++ x :: middle) ++ tail) with (prefix ++ x :: (middle ++ tail)) by (rewrite <- app_assoc; reflexivity).
	apply replace_Znth_boundary_local.
Qed.

Lemma proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Proof.
	pre_process.
	Exists l nil l.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
		cancel ((returnSize_pre) # Int |-> numsSize_pre).
	- split_pures.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. simpl. rewrite app_nil_r. reflexivity.
		+ dump_pre_spatial. symmetry. exact H0.
		+ dump_pre_spatial. simpl. reflexivity.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. rewrite H0. lia.
		+ dump_pre_spatial. apply Permutation_refl.
		+ dump_pre_spatial.
			unfold prefix_suffix_sorted.
			intros x HIn.
			simpl.
			auto.
Qed.

Lemma proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Proof.
	pre_process.
	destruct l1_2.
	- rewrite Zlength_nil in H7. lia.
	- Exists nil z l1_2 l2_2 l3_2.
		split_pure_spatial.
		+ cancel ((returnSize_pre) # Int |-> numsSize_pre).
			cancel (IntArray.full nums_pre numsSize_pre l3_2).
		+ assert (Hlen_unsorted : numsSize_pre - i = Zlength (app nil (cons z l1_2))).
			{ simpl.
				assert (Heqsum : numsSize_pre = Zlength (z :: l1_2) + i).
				{ pose proof (Permutation_length H8) as Hperm.
					apply f_equal with (f := Z.of_nat) in Hperm.
					repeat rewrite <- Zlength_correct in Hperm.
					rewrite <- H3 in Hperm.
					rewrite H2 in Hperm.
					rewrite Zlength_app in Hperm.
					rewrite <- H4 in Hperm.
					exact Hperm. }
				lia. }
			assert (Hnil_ps : prefix_suffix_sorted nil (cons z nil)).
			{ unfold prefix_suffix_sorted.
				intros x HIn.
				inversion HIn. }
			split_pures.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. rewrite H2. simpl. reflexivity.
			* dump_pre_spatial. exact H3.
			* dump_pre_spatial. exact H4.
			* dump_pre_spatial. exact H5.
			* dump_pre_spatial. exact H6.
			* dump_pre_spatial. exact H.
			* dump_pre_spatial. simpl. reflexivity.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. exact Hlen_unsorted.
			* dump_pre_spatial. exact H8.
			* dump_pre_spatial. exact H9.
			* dump_pre_spatial. exact H10.
			* dump_pre_spatial. exact Hnil_ps.
Qed.

Lemma proof_of_sortArray_entail_wit_3_1 : sortArray_entail_wit_3_1.
Proof.
	pre_process.
	destruct l2_2.
	- rewrite H9 in H0.
		rewrite H12 in H0.
		rewrite Zlength_app in H0.
		rewrite Zlength_cons in H0.
		rewrite Zlength_nil in H0.
		simpl in H0.
		lia.
	- assert (Hjkey : Znth j l3_2 0 = key_2).
		{ rewrite H3.
			rewrite app_Znth1 by (rewrite <- H12; lia).
			rewrite H9.
			rewrite app_Znth2 by lia.
			replace (Zlength l1_2 - Zlength l1_2) with 0 by lia.
			simpl.
			reflexivity. }
		assert (Hj1z : Znth (j + 1) l3_2 0 = z).
		{ rewrite H3.
			rewrite app_Znth1 by (rewrite <- H12; lia).
			rewrite H9.
			rewrite app_Znth2 by lia.
			replace (Zlength l1_2 + 1 - Zlength l1_2) with 1 by lia.
			change (Znth 1 (key_2 :: z :: l2_2) 0) with z.
			reflexivity. }
		assert (Hz : z < key_2) by (rewrite Hjkey, Hj1z in H; lia).
		assert (Hsorted : prefix_suffix_sorted (l1_2 ++ z :: key_2 :: l2_2) l4_2).
		{ eapply prefix_suffix_sorted_prefix_perm_local.
			- apply (perm_swap_with_prefix l1_2 nil l2_2 key_2 z).
			- exact H15. }
		Exists (l1_2 ++ [z]) key_2 l2_2 l4_2 (replace_Znth (j + 1) key_2 (replace_Znth j z l3_2)).
		assert (Harray :
			replace_Znth (j + 1) key_2 (replace_Znth j z l3_2) =
			(l1_2 ++ [z]) ++ key_2 :: l2_2 ++ l4_2).
		{ rewrite H3.
			rewrite H9.
			assert (Hfirst :
				replace_Znth (Zlength l1_2) z ((l1_2 ++ key_2 :: z :: l2_2) ++ l4_2) =
				(l1_2 ++ z :: z :: l2_2) ++ l4_2).
			{ apply (replace_Znth_boundary_app_local l1_2 (z :: l2_2) l4_2 z key_2). }
			rewrite Hfirst.
			assert (Hprefix_len : Zlength (l1_2 ++ [z]) = Zlength l1_2 + 1).
			{ change [z] with (z :: nil).
				rewrite Zlength_app.
				rewrite Zlength_cons.
				rewrite Zlength_nil.
				lia. }
			replace ((l1_2 ++ z :: z :: l2_2) ++ l4_2) with (((l1_2 ++ [z]) ++ z :: l2_2) ++ l4_2) by (simpl; rewrite <- !app_assoc; reflexivity).
			rewrite <- Hprefix_len.
			replace ((l1_2 ++ [z]) ++ key_2 :: l2_2 ++ l4_2) with (((l1_2 ++ [z]) ++ key_2 :: l2_2) ++ l4_2) by (rewrite <- !app_assoc; reflexivity).
			apply (replace_Znth_boundary_app_local (l1_2 ++ [z]) l2_2 l4_2 key_2 z). }
		split_pure_spatial.
		+ cancel ((returnSize_pre) # Int |-> numsSize_pre).
			rewrite Hjkey, Hj1z.
			cancel (IntArray.full nums_pre numsSize_pre (replace_Znth (j + 1) key_2 (replace_Znth j z l3_2))).
		+ split_pures.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. rewrite Harray. simpl. rewrite <- !app_assoc. reflexivity.
			* dump_pre_spatial. exact H4.
			* dump_pre_spatial. exact H5.
			* dump_pre_spatial. exact H6.
			* dump_pre_spatial. exact H7.
			* dump_pre_spatial. exact H8.
			* dump_pre_spatial. rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial.
				rewrite H12.
				rewrite !Zlength_app.
				rewrite !Zlength_cons.
				rewrite Zlength_nil.
				simpl.
				lia.
			* dump_pre_spatial.
				rewrite H3 in H13.
				rewrite Harray.
				replace ((l1_2 ++ [z]) ++ key_2 :: l2_2 ++ l4_2) with ((l1_2 ++ z :: key_2 :: l2_2) ++ l4_2) by (simpl; rewrite <- !app_assoc; reflexivity).
				eapply Permutation_trans.
				{ exact H13. }
				{
					replace ((l1_2 ++ key_2 :: z :: l2_2) ++ l4_2) with (l1_2 ++ key_2 :: nil ++ z :: (l2_2 ++ l4_2)) by (simpl; rewrite <- !app_assoc; reflexivity).
					replace ((l1_2 ++ z :: key_2 :: l2_2) ++ l4_2) with (l1_2 ++ z :: nil ++ key_2 :: (l2_2 ++ l4_2)) by (simpl; rewrite <- !app_assoc; reflexivity).
					apply (perm_swap_with_prefix l1_2 nil (l2_2 ++ l4_2) key_2 z).
				}
			* dump_pre_spatial. exact H14.
			* dump_pre_spatial.
				replace (((l1_2 ++ [z]) ++ key_2 :: l2_2)) with (l1_2 ++ z :: key_2 :: l2_2) by (simpl; rewrite <- !app_assoc; reflexivity).
				exact Hsorted.
			* dump_pre_spatial.
				apply prefix_suffix_sorted_snoc_singleton_local.
				{ exact H16. }
				{ lia. }
Qed.

Lemma proof_of_sortArray_entail_wit_3_2 : sortArray_entail_wit_3_2.
Proof.
	pre_process.
	destruct l2_2.
	- rewrite H9 in H0.
		rewrite H12 in H0.
		rewrite Zlength_app in H0.
		rewrite Zlength_cons in H0.
		rewrite Zlength_nil in H0.
		simpl in H0.
		lia.
	- assert (Hz : key_2 <= z).
		{ assert (Hjkey : Znth j l3_2 0 = key_2).
			{ rewrite H3.
				rewrite app_Znth1 by (rewrite <- H12; lia).
				rewrite H9.
				rewrite app_Znth2 by lia.
				replace (Zlength l1_2 - Zlength l1_2) with 0 by lia.
				simpl.
				reflexivity. }
			assert (Hj1z : Znth (j + 1) l3_2 0 = z).
			{ rewrite H3.
				rewrite app_Znth1 by (rewrite <- H12; lia).
				rewrite H9.
				rewrite app_Znth2 by lia.
				replace (Zlength l1_2 + 1 - Zlength l1_2) with 1 by lia.
				change (Znth 1 (key_2 :: z :: l2_2) 0) with z.
				reflexivity. }
			rewrite Hjkey, Hj1z in H.
			lia. }
		Exists (l1_2 ++ [key_2]) z l2_2 l4_2 l3_2.
		split_pure_spatial.
		+ cancel ((returnSize_pre) # Int |-> numsSize_pre).
			cancel (IntArray.full nums_pre numsSize_pre l3_2).
		+ split_pures.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. rewrite H3. simpl. rewrite <- !app_assoc. reflexivity.
			* dump_pre_spatial. exact H4.
			* dump_pre_spatial. exact H5.
			* dump_pre_spatial. exact H6.
			* dump_pre_spatial. exact H7.
			* dump_pre_spatial. exact H8.
			* dump_pre_spatial. rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial.
				rewrite H12.
				rewrite !Zlength_app.
				rewrite !Zlength_cons.
				rewrite Zlength_nil.
				simpl.
				lia.
			* dump_pre_spatial. exact H13.
			* dump_pre_spatial. exact H14.
			* dump_pre_spatial.
				replace (((l1_2 ++ [key_2]) ++ z :: l2_2)) with (l1_2 ++ key_2 :: z :: l2_2) by (simpl; rewrite <- !app_assoc; reflexivity).
				exact H15.
			* dump_pre_spatial.
				eapply prefix_suffix_sorted_snoc_singleton_local.
				{ eapply prefix_suffix_sorted_singleton_le_local.
					- exact H16.
					- exact Hz. }
				{ exact Hz. }
Qed.

Lemma proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Proof.
	pre_process.
	assert (Heq : j + 1 = numsSize_pre - i) by lia.
	assert (Hl2 : Zlength l2_2 = 0).
	{ rewrite H8 in Heq.
		rewrite H11 in Heq.
		rewrite Zlength_app in Heq.
		rewrite Zlength_cons in Heq.
		simpl in Heq.
		lia. }
	apply Zlength_nil_inv in Hl2.
	subst l2_2.
	assert (Hlb_key : lowerbound key l4).
	{ unfold prefix_suffix_sorted in H14.
		specialize (H14 key).
		simpl in H14.
		apply H14.
		rewrite in_app_iff.
		right.
		simpl.
		auto. }
	assert (Hinc : increasing (key :: l4)).
	{ apply increasing_cons_local; assumption. }
	assert (Hps : prefix_suffix_sorted l1_2 (key :: l4)).
	{ apply prefix_suffix_sorted_extend_suffix_local.
		- exact H15.
		- unfold prefix_suffix_sorted in *.
			intros x Hx.
			apply H14.
			simpl.
			rewrite in_app_iff.
			left.
			exact Hx. }
	Exists l1_2 (key :: l4) l3_2.
	split_pure_spatial.
	- cancel ((returnSize_pre) # Int |-> numsSize_pre).
		cancel (IntArray.full nums_pre numsSize_pre l3_2).
	- split_pures.
		+ dump_pre_spatial. exact H0.
		+ dump_pre_spatial. exact H1.
		+ dump_pre_spatial. rewrite H2. simpl. rewrite <- app_assoc. reflexivity.
		+ dump_pre_spatial. exact H3.
		+ dump_pre_spatial. rewrite H4. rewrite Zlength_cons. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. rewrite <- H8. lia.
		+ dump_pre_spatial. exact H12.
		+ dump_pre_spatial. exact Hinc.
		+ dump_pre_spatial. exact Hps.
Qed.

Lemma proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Proof.
	pre_process.
	assert (numsSize_pre = 1) by lia.
	subst numsSize_pre.
	destruct l.
	- rewrite Zlength_nil in *. lia.
	- destruct l.
		+ Exists [z].
			split_pure_spatial.
			* cancel (IntArray.full nums_pre 1 [z]).
				cancel ((returnSize_pre) # Int |-> 1).
			* split_pures; [dump_pre_spatial; apply Permutation_refl | dump_pre_spatial; simpl; auto].
		+ pose proof (Zlength_nonneg l) as Hl_nonneg.
			repeat rewrite Zlength_cons in H3.
			simpl in H3.
			lia.
Qed.

Lemma proof_of_sortArray_return_wit_2 : sortArray_return_wit_2.
Proof.
	pre_process.
	assert (Hi : i = numsSize_pre - 1) by lia.
	assert (Hlen_l3 : Zlength l3 = numsSize_pre).
	{ pose proof (Permutation_length H8) as Hperm.
		apply f_equal with (f := Z.of_nat) in Hperm.
		repeat rewrite <- Zlength_correct in Hperm.
		rewrite <- H3 in Hperm.
		symmetry.
		exact Hperm. }
	assert (Hlen_l1 : Zlength l1_2 = 1).
	{ rewrite H2 in Hlen_l3.
		rewrite Zlength_app in Hlen_l3.
		rewrite <- H4 in Hlen_l3.
		rewrite Hi in Hlen_l3.
		lia. }
	destruct l1_2.
	- rewrite Zlength_nil in H7. lia.
	- assert (Hlen_tail : Zlength l1_2 = 0).
		{ rewrite Zlength_cons in Hlen_l1. simpl in Hlen_l1. lia. }
		apply Zlength_nil_inv in Hlen_tail.
		subst l1_2.
		assert (Hlb : lowerbound z l2).
		{ unfold prefix_suffix_sorted in H10.
			apply H10.
			simpl.
			auto. }
		assert (Hinc : increasing (z :: l2)).
		{ apply increasing_cons_local; assumption. }
		Exists (z :: l2).
		split_pure_spatial.
		+ rewrite H2.
			simpl.
			cancel (IntArray.full nums_pre numsSize_pre (z :: l2)).
			cancel ((returnSize_pre) # Int |-> numsSize_pre).
		+ split_pures.
			* dump_pre_spatial. rewrite H2 in H8. simpl in H8. exact H8.
			* dump_pre_spatial. exact Hinc.
			* dump_pre_spatial. rewrite H2 in Hlen_l3. simpl in Hlen_l3. exact Hlen_l3.
Qed.

