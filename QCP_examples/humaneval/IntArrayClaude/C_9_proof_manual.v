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
From SimpleC.EE Require Import C_9_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_9.
Local Open Scope sac.

Lemma proof_of_rolling_max_entail_wit_1 : rolling_max_entail_wit_1.
Proof.
	pre_process.
	subst numbers_pre numbers_size_pre out_pre out_size_pre.
	rewrite (sublist_nil lv 0 0) by lia.
	simpl.
	replace ((- INT_MAX) - 1) with INT_MIN by lia.
	sep_apply (IntArray.undef_full_split_to_undef_seg out0 0 out_size0).
	2: {
		rewrite H5.
		lia.
	}
	rewrite (IntArray.undef_seg_empty out0 0).
	rewrite (IntArray.seg_empty out0 0 0).
	entailer!.
Qed.

Lemma proof_of_rolling_max_entail_wit_2_1 : rolling_max_entail_wit_2_1.
Proof.
	pre_process.
	prop_apply (IntArray.full_length numbers0 numbers_size0 lv).
	Intros.
	assert (Hi : 0 <= i < Zlength lv).
	{
		match goal with
		| Hlen : Z.of_nat (Datatypes.length lv) = numbers_size0 |- _ =>
				rewrite Zlength_correct, Hlen
		end;
		lia.
	}
	assert (Hnext : running_max_val INT_MIN (sublist 0 (i + 1) lv) = max).
	{
		rewrite running_max_val_sublist_snoc by exact Hi.
		match goal with
		| Hmax : max = running_max_val INT_MIN (sublist 0 i lv) |- _ => rewrite Hmax
		end;
		apply Z.max_l.
		lia.
	}
	rewrite rolling_max_f_sublist_snoc by exact Hi.
	sep_apply (IntArray.seg_single out0 i max).
	sep_apply (IntArray.seg_merge_to_seg out0 0 i (i + 1)).
	2: { lia. }
	rewrite Hnext.
	entailer!.
Qed.

Lemma proof_of_rolling_max_entail_wit_2_2 : rolling_max_entail_wit_2_2.
Proof.
	pre_process.
	prop_apply (IntArray.full_length numbers0 numbers_size0 lv).
	Intros.
	assert (Hi : 0 <= i < Zlength lv).
	{
		match goal with
		| Hlen : Z.of_nat (Datatypes.length lv) = numbers_size0 |- _ =>
				rewrite Zlength_correct, Hlen
		end;
		lia.
	}
	assert (Hnext : running_max_val INT_MIN (sublist 0 (i + 1) lv) = Znth i lv 0).
	{
		rewrite running_max_val_sublist_snoc by exact Hi.
		assert (Hgt : running_max_val INT_MIN (sublist 0 i lv) < Znth i lv 0).
		{
			match goal with
			| Hmax : max = running_max_val INT_MIN (sublist 0 i lv) |- _ => rewrite <- Hmax
			end;
			lia.
		}
		apply Z.max_r.
		lia.
	}
	rewrite rolling_max_f_sublist_snoc by exact Hi.
	sep_apply (IntArray.seg_single out0 i (Znth i lv 0)).
	sep_apply (IntArray.seg_merge_to_seg out0 0 i (i + 1)).
	2: { lia. }
	rewrite Hnext.
	entailer!.
Qed.

Lemma proof_of_rolling_max_return_wit_1 : rolling_max_return_wit_1.
Proof.
	pre_process.
	prop_apply (IntArray.full_length numbers0 numbers_size0 lv).
	Intros.
	assert (Hi : i = numbers_size0) by lia.
	subst i.
	assert (Hsl : sublist 0 numbers_size0 lv = lv).
	{
		apply sublist_self.
		match goal with
		| Hlen : Z.of_nat (Datatypes.length lv) = numbers_size0 |- _ =>
				rewrite Zlength_correct;
				symmetry;
				exact Hlen
		end.
	}
	rewrite Hsl.
	Exists (rolling_max_f INT_MIN lv).
	rewrite <- H0.
	rewrite (IntArray.undef_seg_empty out0 out_size0).
	sep_apply (IntArray.seg_to_full out0 0 out_size0).
	replace (out0 + 0 * sizeof (INT)) with out0 by lia.
	replace (out_size0 - 0) with out_size0 by lia.
	entailer!.
	apply problem_9_spec_rolling_max_f.
	match goal with
	| Hrange : list_int_range lv |- _ => exact Hrange
	end.
Qed.

