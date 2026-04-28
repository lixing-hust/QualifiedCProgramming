Load "../spec/120".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac.

Definition problem_120_pre_z (arr : list Z) (k : Z) : Prop :=
  1 <= Zlength arr <= 1000 /\
  Forall (fun z => -1000 <= z <= 1000) arr /\
  0 <= k <= Zlength arr.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition copy_prefix (input : list Z) (i : Z) : list Z :=
  sublist 0 i input.

Definition maximum_output_prefix (sorted_l : list Z) (size k i : Z) : list Z :=
  sublist (size - k) (size - k + i) sorted_l.

Definition problem_120_spec_z (input : list Z) (k : Z) (output : list Z) : Prop :=
  (k = 0 /\ output = []) \/
  exists sorted_l,
    0 < k <= Zlength input /\
    k = Zlength output /\
    Zlength sorted_l = Zlength input /\
    sorted_int_list_by 1 sorted_l /\
    Permutation input sorted_l /\
    output = maximum_output_prefix sorted_l (Zlength input) k k.

Lemma problem_120_pre_z_k_bounds : forall input k,
  problem_120_pre_z input k ->
  0 <= k <= Zlength input.
Proof.
  intros input k Hpre.
  unfold problem_120_pre_z in Hpre.
  tauto.
Qed.

Lemma problem_120_pre_z_Znth_range : forall input k i,
  problem_120_pre_z input k ->
  0 <= i < Zlength input ->
  -1000 <= Znth i input 0 <= 1000.
Proof.
  intros input k i Hpre Hi.
  unfold problem_120_pre_z in Hpre.
  destruct Hpre as [_ [Hforall _]].
  rewrite Forall_forall in Hforall.
  apply Hforall.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma copy_prefix_nil : forall input,
  copy_prefix input 0 = [].
Proof.
  intros.
  unfold copy_prefix.
  apply sublist_nil.
  lia.
Qed.

Lemma copy_prefix_snoc : forall input i,
  0 <= i < Zlength input ->
  copy_prefix input (i + 1) = copy_prefix input i ++ [Znth i input 0].
Proof.
  intros input i Hi.
  unfold copy_prefix.
  rewrite (sublist_split 0 (i + 1) i input).
  replace (sublist i (i + 1) input) with (Znth i input 0 :: nil).
  replace (i + 1 - 0) with (i + 1) by lia.
  replace (i - 0) with i by lia.
  reflexivity.
  - symmetry. apply sublist_single.
    rewrite <- Zlength_correct.
    lia.
  - lia.
  - rewrite <- Zlength_correct. lia.
Qed.

Lemma copy_prefix_full : forall input size,
  size = Zlength input ->
  copy_prefix input size = input.
Proof.
  intros input size Hsize.
  unfold copy_prefix.
  apply sublist_self.
  lia.
Qed.

Lemma maximum_output_prefix_nil : forall sorted_l size k,
  maximum_output_prefix sorted_l size k 0 = [].
Proof.
  intros.
  unfold maximum_output_prefix.
  apply sublist_nil.
  lia.
Qed.

Lemma maximum_output_prefix_snoc : forall sorted_l size k i,
  size = Zlength sorted_l ->
  0 < k <= size ->
  0 <= i < k ->
  maximum_output_prefix sorted_l size k (i + 1) =
    maximum_output_prefix sorted_l size k i ++ [Znth (size - k + i) sorted_l 0].
Proof.
  intros sorted_l size k i Hsize Hk Hi.
  unfold maximum_output_prefix.
  rewrite (sublist_split (size - k) (size - k + (i + 1)) (size - k + i) sorted_l).
  replace (size - k + (i + 1)) with (size - k + i + 1) by lia.
  replace (sublist (size - k + i) (size - k + i + 1) sorted_l)
    with (Znth (size - k + i) sorted_l 0 :: nil).
  reflexivity.
  - symmetry. apply sublist_single.
    rewrite <- Zlength_correct.
    lia.
  - lia.
  - rewrite <- Zlength_correct. lia.
Qed.

Lemma maximum_output_prefix_Zlength : forall sorted_l size k i,
  size = Zlength sorted_l ->
  0 <= i <= k ->
  0 <= k <= size ->
  Zlength (maximum_output_prefix sorted_l size k i) = i.
Proof.
  intros sorted_l size k i Hsize Hi Hk.
  unfold maximum_output_prefix.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma problem_120_spec_z_nil : forall input,
  problem_120_spec_z input 0 [].
Proof.
  intros.
  unfold problem_120_spec_z.
  left.
  split; reflexivity.
Qed.

Lemma IntArray_undef_full_0_to_full_nil : forall p,
  IntArray.undef_full p 0 |-- IntArray.full p 0 (@nil Z).
Proof.
  intros.
  rewrite IntArray.undef_full_empty.
  unfold IntArray.full, store_array, store_array_rec.
  entailer!.
Qed.

Lemma problem_120_spec_z_of_sorted : forall input k output sorted_l,
  0 < k <= Zlength input ->
  k = Zlength output ->
  Zlength sorted_l = Zlength input ->
  sorted_int_list_by 1 sorted_l ->
  Permutation input sorted_l ->
  output = maximum_output_prefix sorted_l (Zlength input) k k ->
  problem_120_spec_z input k output.
Proof.
  intros input k output sorted_l Hk Hout_len Hsorted_len Hsorted Hperm Houtput.
  unfold problem_120_spec_z.
  right.
  exists sorted_l.
  destruct Hk as [Hk_pos Hk_le].
  repeat split; try assumption.
Qed.
