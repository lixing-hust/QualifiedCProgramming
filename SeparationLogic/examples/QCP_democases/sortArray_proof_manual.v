Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_democases Require Import sortArray_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
From SimpleC.EE.QCP_democases Require Import sortArray_lib.
Local Open Scope sac.

Lemma proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Proof.
	pre_process.
	destruct l as [ | a l']; simpl in H; [ rewrite Zlength_nil in H ;  lia | ].
	rewrite (IntArray.full_unfold nums_pre numsSize_pre l' a).
	Exists (a :: nil) (a :: nil) l'.
	entailer!.
	sep_apply (IntArray.seg_single nums_pre 0 a).
	entailer!.
Qed.

Lemma proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Proof.
	pre_process.
	prop_apply (IntArray.seg_length nums_pre i numsSize_pre l2).
	Intros.
	destruct l2 as [ | a l4]; [simpl in H8; lia | ].
	replace (i - i) with 0 by lia.
	replace (i - 1 + 1) with i by lia.
	rewrite Znth0_cons.
	rewrite (IntArray.seg_unfold nums_pre i numsSize_pre l4 a).
	Exists l0_2 nil l0_2 l1_2 l4.
	entailer!.
	sep_apply store_int_undef_store_int.
	rewrite (IntArray.missing_i_unfold nums_pre i i (i + 1) nil a); try lia.
	Left.
	rewrite (IntArray.seg_empty nums_pre (i + 1) (i + 1)).
	entailer!.
	+ rewrite Zlength_correct in *. erewrite Permutation_length.
	  eauto. apply Permutation_sym. auto.
	+ rewrite app_nil_r. auto.
Qed.

Lemma proof_of_sortArray_entail_wit_3 : sortArray_entail_wit_3.
Proof.
	pre_process.
	Exists l3_2 l0_2 l1_2 l4_2.
	Exists (sublist 0 j l2_2) l2_2.
	replace (j - 0) with j in * by lia .
	assert (l2_2 = sublist 0 (Zlength l2_2) l2_2).
	{ rewrite sublist_self ; auto. }
	assert (l2_2 = sublist 0 j l2_2 ++ sublist j (Zlength l2_2) l2_2).
	{ rewrite <- sublist_split with (lo := 0) (mid := j) (hi := Zlength l2_2); auto; try lia.
	  rewrite <- Zlength_correct. lia.
	}
	rewrite <- H10 in H14.
	rewrite (sublist_single j l2_2 0) in H14.
	entailer!.
	sep_apply (IntArray.seg_split_to_seg nums_pre 0 j (j + 1) l2_2); try lia.
	replace (j - 0) with j by lia.
	replace (j + 1 - 0) with (j + 1) by lia.
	entailer!.
	rewrite (sublist_single j l2_2 0).
	rewrite IntArray.seg_unfold.
	sep_apply (IntArray.seg_nil).
	entailer!.
	+ rewrite <- Zlength_correct. lia. 
	+ rewrite Zlength_sublist. lia. lia.
	+ rewrite <- Zlength_correct. lia. 
Qed.

Lemma proof_of_sortArray_entail_wit_4 : sortArray_entail_wit_4.
Proof.
	pre_process.
	Exists l3_2 l0_2 l1_2 l4_2.
	Exists l5_2 l2_2.
	entailer!.
	rewrite (IntArray.missing_i_unfold nums_pre (j + 1) (j + 1) (i + 1) l3_2 key); try lia.
	Split.
	- Intros. 
	  sep_apply (IntArray.seg_single nums_pre (j + 1) (Znth j l2_2 0)).
	  sep_apply (IntArray.seg_merge_to_seg nums_pre (j + 1) (j + 1 + 1) (i + 1)); try lia.
	  rewrite (IntArray.missing_i_unfold nums_pre j j (i + 1) ((Znth j l2_2 0) :: l3_2) key); try lia.
	  Left.
	  sep_apply store_int_undef_store_int.
	  entailer!.
	- Intros. lia.
Qed.

Lemma proof_of_sortArray_entail_wit_5 : sortArray_entail_wit_5.
Proof.
	pre_process.
	Exists l5 ((Znth j l2_2 0) :: l3_2) l0_2 l1_2 l4_2.
	entailer!.
	- rewrite H5. rewrite H.
	  replace (j - 1 + 1) with j by lia.
	  entailer!.
	- simpl. split; [lia | exact H11].
	- rewrite H10. rewrite H. rewrite <- app_assoc.
	  rewrite app_Znth2 ; try lia.
	  replace (j - Zlength l5) with 0 by lia.
	  rewrite Znth0_cons.
	  simpl.
	  reflexivity.
Qed.

Lemma proof_of_sortArray_entail_wit_6_1 : sortArray_entail_wit_6_1.
Proof.
	pre_process.
	prop_apply (IntArray.seg_length nums_pre (i + 1) numsSize_pre l4). Intros.
	rewrite <- Zlength_correct in H13.
	destruct l2_2 using rev_ind.
	- rewrite Zlength_nil in H10. lia.
	- assert (j = Zlength l2_2). 
	  { rewrite Zlength_app in H10; simpl in H10.
	    rewrite Zlength_cons in H10; simpl in H10.
	    lia. }
		subst j.
		rewrite app_Znth2 in H by (rewrite Zlength_correct; simpl; lia).
		replace (Zlength l2_2 - 0 - Zlength l2_2) with 0 in H by lia.
		rewrite Znth0_cons in H.
		rewrite (IntArray.missing_i_unfold nums_pre (Zlength l2_2 + 1) (Zlength l2_2 + 1) (i + 1) l3 key); try lia.
		Split ; Intros ; try lia.
		Exists (l2_2 ++ x :: key :: l3) (l1_2 ++ key :: nil) l4.
		entailer!.
		+ sep_apply (IntArray.seg_single nums_pre (Zlength l2_2 + 1) key).
		  sep_apply (IntArray.seg_merge_to_seg nums_pre (Zlength l2_2 + 1) (Zlength l2_2 + 1 + 1) (i + 1)); try lia.
		  sep_apply (IntArray.seg_merge_to_seg nums_pre 0 (Zlength l2_2 + 1) (i + 1)); try lia.
		  simpl.
		  rewrite <- app_assoc.
		  entailer!.
		+ rewrite H9 in H8. rewrite <- app_assoc in H8. simpl in H8.
		  apply increasing_middle ; auto.
		+ eapply Permutation_trans.
		  * apply Permutation_app_tail. exact H7.
		  * rewrite H9. rewrite <- app_assoc. 
		  	rewrite <- app_assoc. simpl.
			apply Permutation_app_head.
			constructor.
			apply Permutation_sym.
			apply Permutation_cons_append.
		+ assert (0 <= Zlength l4).
		  { apply Zlength_nonneg. }
		  lia.
		+ rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
		+ rewrite <- app_assoc. simpl. auto. 
Qed.

Lemma proof_of_sortArray_entail_wit_6_2 : sortArray_entail_wit_6_2.
Proof.
	pre_process.
	assert (l2_2 = nil).
	{ destruct l2_2 as [ | z l2_2].
	  - reflexivity.
	  - pose proof (Zlength_nonneg l2_2) as Hlen. 
	    rewrite Zlength_cons in H9. simpl in H9. lia.
	}
	subst l2_2.
	rewrite Zlength_nil in *.
	replace (j + 1) with 0 by lia.
	prop_apply (IntArray.seg_length nums_pre (i + 1) numsSize_pre l4). Intros.
	rewrite <- Zlength_correct in H12.
	rewrite (IntArray.seg_empty nums_pre 0 0).
	rewrite (IntArray.missing_i_unfold nums_pre 0 0 (i + 1) l3 key); try lia.
	Split ; Intros ; try lia.
	Exists (key :: l3) (l1_2 ++ key :: nil) l4.
	entailer!.
	- destruct l3.
	  + simpl. auto.
	  + rewrite H8 in H7. simpl in *. split ; auto. lia.
	- rewrite H8 in H6. simpl in H6.
		eapply Permutation_trans.
		* apply Permutation_app_tail. exact H6.
		* apply Permutation_sym. apply Permutation_cons_append.
	- assert (0 <= Zlength l4).
	  { apply Zlength_nonneg. }
	  lia.
	- rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
	- rewrite <- app_assoc. simpl. auto.
Qed.

Lemma proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Proof.
	pre_process.
	assert (i = numsSize_pre) by lia.
	subst i.
	rewrite H8.
	prop_apply (IntArray.seg_length nums_pre numsSize_pre numsSize_pre l2).
	Intros.
	destruct l2 as [ | a l2']; [ | simpl in H3; lia].
	rewrite (IntArray.seg_empty nums_pre numsSize_pre numsSize_pre).
	Exists l0. Intros.
	prop_apply (IntArray.seg_length nums_pre 0 numsSize_pre l0). Intros.
	rewrite <- Zlength_correct in H10.
	entailer!.
	rewrite app_nil_r in H2. subst. auto.
Qed.

