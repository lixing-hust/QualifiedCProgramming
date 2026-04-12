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
From SimpleC.EE.QCP_democases Require Import majorityElement_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_democases Require Import majorityElement_lib.
Local Open Scope sac.

Ltac grab H pat :=
	match goal with
	| H0 : pat |- _ => pose proof H0 as H
	end.

Lemma proof_of_majorityElement_entail_wit_1 : majorityElement_entail_wit_1.
Proof.
	unfold majorityElement_entail_wit_1.
	intros.
	Exists x_2 (@nil Z) l.
	rewrite app_nil_l.
	rewrite Zlength_nil.
	entailer!.
	apply majority_on_reduced_init.
	auto.
Qed. 

Lemma proof_of_majorityElement_entail_wit_2_1 : majorityElement_entail_wit_2_1.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength; Intros.
	let Hlen := fresh "Hlen" in grab Hlen (Zlength l = numsSize_pre).
	let Happ := fresh "Happ" in grab Happ (l = app l1_2 l2_2).
	let Hi := fresh "Hi" in grab Hi (i = Zlength l1_2).
	assert (exists h t, l2_2 = h :: t /\ Znth i l 0 = h) as Hsplit.
	{
		pose proof (app_Znth_suffix_cons l1_2 l2_2 i 0 Hi) as Hsplit0.
		specialize (Hsplit0 ltac:(rewrite <- Happ, Hlen; lia)).
		rewrite <- Happ in Hsplit0.
		exact Hsplit0.
	}
	destruct Hsplit as [h [t [Hl2 Hz]]].
	let Hcand := fresh "Hcand" in grab Hcand (Znth i l 0 = candidate).
	assert (h = candidate) by (rewrite Hcand in Hz; symmetry; exact Hz).
	subst l2_2 h.
	rewrite Hcand in H2, H11.
	pose proof H11 as Hmor.
	Exists x_2 (l1_2 ++ candidate :: nil) t.
	rewrite <- app_assoc.
	rewrite Zlength_app, Zlength_cons, Zlength_nil.
	entailer!.
	unfold MajorityOnReduced in Hmor.
	destruct Hmor as [_ Hmor].
	apply majority_on_reduced_same; try lia.
	exact Hmor.
	all: try lia; try easy.
Qed. 

Lemma proof_of_majorityElement_entail_wit_2_2 : majorityElement_entail_wit_2_2.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength; Intros.
	let Hlen := fresh "Hlen" in grab Hlen (Zlength l = numsSize_pre).
	let Happ := fresh "Happ" in grab Happ (l = app l1_2 l2_2).
	let Hi := fresh "Hi" in grab Hi (i = Zlength l1_2).
	assert (exists h t, l2_2 = h :: t /\ Znth i l 0 = h) as Hsplit.
	{
		pose proof (app_Znth_suffix_cons l1_2 l2_2 i 0 Hi) as Hsplit0.
		specialize (Hsplit0 ltac:(rewrite <- Happ, Hlen; lia)).
		rewrite <- Happ in Hsplit0.
		exact Hsplit0.
	}
	destruct Hsplit as [h [t [Hl2 Hz]]].
	let Hneq := fresh "Hneq" in grab Hneq (Znth i l 0 <> candidate).
	assert (h <> candidate).
	{
		intro Heq.
		apply Hneq.
		rewrite Hz.
		exact Heq.
	}
	subst l2_2.
	pose proof H11 as Hmor.
	Exists x_2 (l1_2 ++ h :: nil) t.
	rewrite <- app_assoc.
	rewrite Zlength_app, Zlength_cons, Zlength_nil.
	entailer!.
	unfold MajorityOnReduced in Hmor.
	destruct Hmor as [_ Hmor].
	eapply majority_on_reduced_cancel with (a := h); try lia; eauto.
	all: try lia; try easy.
Qed. 

Lemma proof_of_majorityElement_entail_wit_2_3 : majorityElement_entail_wit_2_3.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength; Intros.
	let Hlen := fresh "Hlen" in grab Hlen (Zlength l = numsSize_pre).
	let Happ := fresh "Happ" in grab Happ (l = app l1_2 l2_2).
	let Hi := fresh "Hi" in grab Hi (i = Zlength l1_2).
	assert (exists h t, l2_2 = h :: t /\ Znth i l 0 = h) as Hsplit.
	{
		pose proof (app_Znth_suffix_cons l1_2 l2_2 i 0 Hi) as Hsplit0.
		specialize (Hsplit0 ltac:(rewrite <- Happ, Hlen; lia)).
		rewrite <- Happ in Hsplit0.
		exact Hsplit0.
	}
	destruct Hsplit as [h [t [Hl2 Hz]]].
	subst l2_2.
	Exists x_2 (l1_2 ++ Znth i l 0 :: nil) t.
	rewrite Hz.
	rewrite <- app_assoc.
	rewrite Zlength_app, Zlength_cons, Zlength_nil.
	entailer!.
	let Hv := fresh "Hv" in grab Hv (vote = 0).
	unfold MajorityOnReduced in H10.
	rewrite Hv in H10.
	destruct H10 as [_ Hred].
	rewrite Hv.
	eapply majority_on_reduced_reset with (candidate := candidate) (a := h).
	exact Hred.
	all: try lia; try easy.
Qed. 

Lemma proof_of_majorityElement_return_wit_1 : majorityElement_return_wit_1.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength; Intros.
	let Hlen := fresh "Hlen" in grab Hlen (Zlength l = numsSize_pre).
	let Happ := fresh "Happ" in grab Happ (l = app l1 l2).
	pose proof Zlength_app l1 l2 as HappLen.
	assert (i = numsSize_pre) by lia.
	assert (Hl2nil_len : Zlength l2 = 0) by (rewrite Happ in Hlen; lia).
	apply Zlength_nil_inv in Hl2nil_len.
	subst l2.
	pose proof H9 as Hmor.
	unfold MajorityOnReduced in Hmor.
	assert (Hvote0 : 0 <= vote) by exact (proj1 Hmor).
	assert (Hred : IsMajorityElement x (repeated candidate vote ++ nil)) by exact (proj2 Hmor).
	rewrite app_nil_r in Hred.
	pose proof (majority_of_repeated_eq x candidate vote Hvote0 Hred) as Heq.
	subst x.
	entailer!.
	all: try lia; try easy.
Qed. 

