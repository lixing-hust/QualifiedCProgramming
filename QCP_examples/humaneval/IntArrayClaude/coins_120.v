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
  problem_120_spec input (Z.to_nat k) output.

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
  unfold problem_120_spec_z, problem_120_spec.
  split.
  - reflexivity.
  - split.
    + constructor.
    + exists input.
      split.
      * reflexivity.
      * intros x y Hx _.
        contradiction.
Qed.

Lemma IntArray_undef_full_0_to_full_nil : forall p,
  IntArray.undef_full p 0 |-- IntArray.full p 0 (@nil Z).
Proof.
  intros.
  rewrite IntArray.undef_full_empty.
  unfold IntArray.full, store_array, store_array_rec.
  entailer!.
Qed.

Lemma Sorted_cons_all_le_120 : forall x l y,
  Sorted Z.le (x :: l) ->
  In y (x :: l) ->
  x <= y.
Proof.
  intros x l.
  revert x.
  induction l; intros x y Hsorted Hin.
  - simpl in Hin.
    destruct Hin as [-> | []].
    lia.
  - simpl in Hin.
    destruct Hin as [-> | Hin].
    + lia.
    + pose proof (Sorted_inv Hsorted) as [Htail Hhd].
      assert (x <= a).
      {
        inversion Hhd; subst.
        assumption.
      }
      assert (a <= y).
      {
        apply IHl.
        - exact Htail.
        - simpl. exact Hin.
      }
      lia.
Qed.

Lemma nth_sorted_le_nat_120 : forall l n m d,
  Sorted Z.le l ->
  (n <= m < length l)%nat ->
  nth n l d <= nth m l d.
Proof.
  induction l; intros n m d Hsorted Hrange.
  - simpl in Hrange. lia.
  - destruct n; destruct m; simpl.
    + lia.
    + apply (Sorted_cons_all_le_120 a l (nth m l d)).
      * exact Hsorted.
      * right. apply nth_In. simpl in Hrange. lia.
    + lia.
    + pose proof (Sorted_inv Hsorted) as [Htail _].
      apply IHl.
      * exact Htail.
      * simpl in Hrange. lia.
Qed.

Lemma Sorted_app_right_120 : forall l1 l2,
  Sorted Z.le (l1 ++ l2) ->
  Sorted Z.le l2.
Proof.
  induction l1; intros l2 Hsorted.
  - simpl in Hsorted. exact Hsorted.
  - apply IHl1.
    pose proof (Sorted_inv Hsorted) as [Htail _].
    exact Htail.
Qed.

Lemma Sorted_app_all_le_120 : forall l1 l2 x y,
  Sorted Z.le (l1 ++ l2) ->
  In y l1 ->
  In x l2 ->
  y <= x.
Proof.
  intros l1 l2 x y Hsorted Hy Hx.
  destruct (In_nth l1 y 0 Hy) as [i [Hi Hy_nth]].
  destruct (In_nth l2 x 0 Hx) as [j [Hj Hx_nth]].
  subst y x.
  replace (nth i l1 0) with (nth i (l1 ++ l2) 0).
  replace (nth j l2 0) with (nth (length l1 + j) (l1 ++ l2) 0).
  - apply nth_sorted_le_nat_120.
    + exact Hsorted.
    + rewrite app_length.
      lia.
  - rewrite app_nth2 by lia.
    replace (length l1 + j - length l1)%nat with j by lia.
    reflexivity.
  - rewrite app_nth1 by lia.
    reflexivity.
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
  destruct Hk as [Hk_pos Hk_le].
  subst output.
  assert (Hsorted_list : Sorted Z.le sorted_l).
  {
    unfold sorted_int_list_by in Hsorted.
    simpl in Hsorted.
    exact Hsorted.
  }
  set (rest := sublist 0 (Zlength input - k) sorted_l).
  set (output := maximum_output_prefix sorted_l (Zlength input) k k).
  assert (Hsplit : sorted_l = rest ++ output).
  {
    subst rest output.
    unfold maximum_output_prefix.
    replace (Zlength input - k + k) with (Zlength input) by lia.
    rewrite <- (sublist_split 0 (Zlength input) (Zlength input - k) sorted_l).
    - symmetry. apply sublist_self.
      lia.
    - lia.
    - rewrite <- Zlength_correct.
      lia.
  }
  unfold problem_120_spec_z, problem_120_spec.
  repeat split.
  - apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    subst output.
    rewrite maximum_output_prefix_Zlength by lia.
    lia.
  - apply (Sorted_app_right_120 rest).
    rewrite <- Hsplit.
    exact Hsorted_list.
  - exists rest.
    split.
    + eapply Permutation_trans.
      * apply Permutation_app_comm.
      * eapply Permutation_trans.
        -- rewrite <- Hsplit.
           reflexivity.
        -- apply Permutation_sym.
           exact Hperm.
    + intros x y Hx Hy.
      apply (Sorted_app_all_le_120 rest output); auto.
      rewrite <- Hsplit.
      exact Hsorted_list.
Qed.
