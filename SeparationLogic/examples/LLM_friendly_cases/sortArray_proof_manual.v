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
Proof.
	pre_process.
	destruct l.
	- rewrite Zlength_nil in H. lia.
	- Exists (z :: nil) (z :: l) (z :: nil) l.
	entailer!.
Qed.

Lemma proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Proof.
	pre_process.
	pose proof (Permutation_length H8) as H10.
	assert (i = Zlength l0_2).
	{ rewrite Zlength_correct in H5.
	  rewrite Zlength_correct.
	  lia. }
	destruct l2_2.
	- rewrite app_nil_r in H2. rewrite H2 in H4. lia.
	- assert (Znth i l3 0 = z) as Hz3.
	  { rewrite H3.
	    rewrite app_Znth2 by lia.
	    replace (i - Zlength l0_2) with 0 by lia.
	    rewrite Znth0_cons.
	    reflexivity. }
	  Exists l3.
	  Exists l0_2.
	  Exists nil.
	  Exists l0_2.
	  Exists l1_2.
	  Exists l2_2.
	  rewrite app_nil_r.
	  rewrite Hz3.
	  replace (i - 1 + 1) with i by lia.
	  assert (Znth i l0_2 z = z) as Hz0.
	  { rewrite H11.
	    unfold Znth.
	    rewrite nth_overflow.
	    - reflexivity.
	    - pose proof Zlength_correct l0_2. lia. }
	  rewrite Hz0.
	  change (z :: l2_2) with ([z] ++ l2_2) in H3.
	  entailer!.
	  rewrite app_assoc in H3.
	  exact H3.
Qed.

Lemma proof_of_sortArray_entail_wit_3 : sortArray_entail_wit_3.
Proof.
	pre_process.
	destruct l2_2 using rev_ind.
	- rewrite Zlength_nil in H13. lia.
	- assert (j = Zlength l2_2) as Hj.
	  { rewrite Zlength_app in H13.
	    simpl in H13.
	    rewrite Zlength_cons in H13.
	    simpl in H13.
	    lia. }
	  assert (Znth j l5_2 0 = x) as Hzx.
	  { rewrite H11.
	    assert (0 <= j < Zlength ((l2_2 ++ [x]) ++ Znth (j + 1) l0_2 key :: l3_2)) as Hjlt.
	    { split.
	      - lia.
	      - rewrite Zlength_app.
	        pose proof (Zlength_nonneg (Znth (j + 1) l0_2 key :: l3_2)) as Hlen.
	        nia.
	    }
	    assert (Znth j ((((l2_2 ++ [x]) ++ Znth (j + 1) l0_2 key :: l3_2) ++ l4_2)) 0 =
	            Znth j (((l2_2 ++ [x]) ++ Znth (j + 1) l0_2 key :: l3_2)) 0) as Houter.
	    { apply app_Znth1. exact Hjlt. }
	    rewrite Houter.
	    assert (0 <= j < Zlength (l2_2 ++ [x])) as Hjmid.
	    { split.
	      - lia.
	      - rewrite Zlength_app.
	        rewrite Zlength_cons.
	        rewrite Zlength_nil.
	        simpl.
	        lia.
	    }
	    assert (Znth j (((l2_2 ++ [x]) ++ Znth (j + 1) l0_2 key :: l3_2)) 0 =
	            Znth j (l2_2 ++ [x]) 0) as Hinner.
	    { apply app_Znth1. exact Hjmid. }
	    rewrite Hinner.
	    rewrite app_Znth2 by lia.
	    replace (j - Zlength l2_2) with 0 by lia.
	    rewrite Znth0_cons.
	    reflexivity.
	  }
	  assert (Znth j l0_2 key = x) as Hz0.
	  { rewrite H10.
	    assert (0 <= j < Zlength (l2_2 ++ [x])) as Hjmid.
	    { split.
	      - lia.
	      - rewrite Zlength_app.
	        rewrite Zlength_cons.
	        rewrite Zlength_nil.
	        simpl.
	        lia.
	    }
	    assert (Znth j (((l2_2 ++ [x]) ++ l3_2)) key = Znth j (l2_2 ++ [x]) key) as Houter.
	    { apply app_Znth1. exact Hjmid. }
	    rewrite Houter.
	    rewrite app_Znth2 by lia.
	    replace (j - Zlength l2_2) with 0 by lia.
	    rewrite Znth0_cons.
	    reflexivity.
	  }
	  Exists (replace_Znth (j + 1) (Znth j l5_2 0) l5_2).
	  Exists l2_2.
	  Exists (x :: l3_2).
	  Exists l0_2.
	  Exists l1_2.
	  Exists l4_2.
	  rewrite H10 in Hz0.
	  rewrite H10.
	  replace (j - 1 + 1) with j by lia.
	  rewrite Hz0.
	  assert (((l2_2 ++ [x]) ++ l3_2) = l2_2 ++ (x :: l3_2)) as Happ.
	  { clear - l2_2 x l3_2.
	    induction l2_2; simpl.
	    - reflexivity.
	    - rewrite IHl2_2.
	      reflexivity. }
	  entailer!.
	  all: try (rewrite <- H10; exact H8).
	  all: try (rewrite <- H10; exact H9).
	  all: try (simpl; reflexivity).
	  all: try exact Happ.
	  + rewrite Hzx in H.
	    simpl.
	    split; [lia | exact H16].
	  + rewrite H11.
	    rewrite H11 in Hzx.
	    rewrite Hzx.
	    rewrite <- app_assoc.
	    rewrite replace_Znth_app_r by (rewrite H13; lia).
	    assert (replace_Znth (j + 1) x (l2_2 ++ [x]) = l2_2 ++ [x]) as Hleft.
	    { apply replace_Znth_nothing.
	      rewrite H13.
	      lia.
	    }
	    rewrite Hleft.
	    replace (j + 1 - Zlength (l2_2 ++ [x])) with 0 by lia.
	    unfold replace_Znth.
	    simpl.
	    repeat rewrite <- app_assoc.
	    reflexivity.
Qed.

Lemma proof_of_sortArray_entail_wit_4_1 : sortArray_entail_wit_4_1.
Proof.
	pre_process.
	destruct l2_2 using rev_ind.
	- rewrite Zlength_nil in *; lia.
	- assert (j = Zlength l2_2).
	  { rewrite Zlength_app in H13; simpl in H13.
	    rewrite Zlength_cons in H13; simpl in H13.
	    lia. }
	  subst j.
	  assert (x <= key).
	  { rewrite H11 in H.
	    assert (0 <= Zlength l2_2 < Zlength (((l2_2 ++ [x]) ++ Znth (Zlength l2_2 + 1) l0_2 key :: l3_2))) as Hjlt by
	      (split;
	       [apply Zlength_nonneg |
	        rewrite Zlength_app;
	        pose proof (Zlength_nonneg (Znth (Zlength l2_2 + 1) l0_2 key :: l3_2)) as Hlen;
	        nia]).
	    rewrite app_Znth1 in H by exact Hjlt.
	    assert (0 <= Zlength l2_2 < Zlength (l2_2 ++ [x])) as Hjmid by
	      (split;
	       [apply Zlength_nonneg |
	        rewrite Zlength_app;
	        rewrite Zlength_cons;
	        rewrite Zlength_nil;
	        simpl;
	        lia]).
	    rewrite app_Znth1 in H by exact Hjmid.
	    rewrite app_Znth2 in H by lia.
	    replace (Zlength l2_2 - Zlength l2_2) with 0 in H by lia.
	    simpl in H.
	    exact H. }
	Exists (l2_2 ++ x :: key :: l3_2).
	Exists ((l2_2 ++ x :: key :: l3_2) ++ l4).
	Exists (l1_2 ++ key :: nil).
	Exists l4.
	  assert (increasing (l2_2 ++ x :: key :: l3_2)) as Hinc.
	  { rewrite H10 in H9.
	    rewrite <- app_assoc in H9.
	    simpl in H9.
	    apply increasing_middle; auto. }
	  assert (Permutation (l1_2 ++ key :: nil) (l2_2 ++ x :: key :: l3_2)) as Hperm.
	  { eapply Permutation_trans.
	    - apply Permutation_app_tail. exact H8.
	    - rewrite H10.
	      rewrite <- app_assoc.
	      rewrite <- app_assoc.
	      simpl.
	      apply Permutation_app_head.
	      constructor.
	      apply Permutation_sym.
	      apply Permutation_cons_append. }
	  assert (replace_Znth (Zlength l2_2 + 1) key l5 = (l2_2 ++ x :: key :: l3_2) ++ l4) as Harray.
	  { rewrite H11.
	    rewrite <- app_assoc.
	    rewrite replace_Znth_app_r.
	    2: {
	      rewrite H13.
	      lia.
	    }
	    rewrite replace_Znth_nothing by (rewrite H13; lia).
	    rewrite <- H13.
	    replace (Zlength l2_2 + 1 - (Zlength l2_2 + 1)) with 0 by lia.
	    unfold replace_Znth.
	    simpl.
	    repeat rewrite <- app_assoc.
	    reflexivity. }
	entailer!.
	+ rewrite Harray. reflexivity.
	+ rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
	+ rewrite <- app_assoc. simpl. exact H3.
Qed.

Lemma proof_of_sortArray_entail_wit_4_2 : sortArray_entail_wit_4_2.
Proof.
	pre_process.
	assert (l2_2 = nil).
	{ destruct l2_2.
	  - reflexivity.
	  - rewrite Zlength_cons in H12. simpl in H12.
	    pose proof (Zlength_nonneg l2_2).
	    lia. }
	subst l2_2.
	rewrite Zlength_nil in *.
	replace (j + 1) with 0 by lia.
	Exists (key :: l3_2).
	Exists ((key :: l3_2) ++ l4).
	Exists (l1_2 ++ key :: nil).
	Exists l4.
	entailer!.
	- rewrite H10. simpl. reflexivity.
	- destruct l3_2.
	  + simpl. auto.
	  + rewrite H9 in H8. simpl in *. split; auto. lia.
	- rewrite H9 in H7. simpl in H7.
	  eapply Permutation_trans.
	  + apply Permutation_app_tail. exact H7.
	  + apply Permutation_sym. apply Permutation_cons_append.
	- rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
	- rewrite <- app_assoc. simpl. exact H2.
Qed.

Lemma proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Proof.
	pre_process.
	assert (Hi : i = numsSize_pre) by lia.
	rewrite Hi in *.
	rewrite H2 in H4.
	rewrite Zlength_app in H4.
	rewrite H5 in H4.
	assert (l2 = nil).
	{ destruct l2.
	  - reflexivity.
	  - rewrite Zlength_cons in H4. simpl in H4.
	    pose proof (Zlength_nonneg l2).
	    lia. }
	subst l2.
	rewrite app_nil_r in H3.
	rewrite app_nil_r in H2.
	subst l3.
	Exists l0.
	entailer!.
	- rewrite H5.
	  repeat rewrite Zlength_correct.
	  f_equal.
	  symmetry.
	  apply Permutation_length.
	  exact H8.
	- rewrite H2. exact H8.
Qed.

