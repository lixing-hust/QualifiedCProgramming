Load "../spec/116".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition Zabs (x : Z) : Z := Z.abs x.

Definition bit_fuel_116 : nat := 31%nat.

Fixpoint bit_count_loop_116 (fuel : nat) (n acc : Z) : Z :=
  match fuel with
  | O => acc
  | S fuel' =>
      if Z.leb n 0
      then acc
      else bit_count_loop_116 fuel' (n ÷ 2) (acc + Z.rem n 2)
  end.

Definition bit_count_116 (x : Z) : Z :=
  bit_count_loop_116 bit_fuel_116 x 0.

Definition sort_array_116_int_range (input : list Z) : Prop :=
  forall i, 0 <= i < Zlength input -> 0 <= Znth i input 0 < INT_MAX.

Definition bit_count_state_116 (x n b : Z) : Prop :=
  0 <= x < INT_MAX /\
  0 <= n < INT_MAX /\
  0 <= b <= 31 /\
  exists fuel,
    n < 2 ^ Z.of_nat fuel /\
    bit_count_loop_116 fuel n b = bit_count_116 x.

Definition bit_count_state_at_116 (i : Z) (input : list Z) (n b : Z) : Prop :=
  bit_count_state_116 (Znth i input 0) n b.

Definition bit_count_result_116 (x r : Z) : Prop :=
  0 <= x < INT_MAX /\
  0 <= r <= 31 /\
  r = bit_count_116 x.

Definition should_swap_116 (a b : Z) : bool :=
  if bit_count_116 b <? bit_count_116 a then true
  else if bit_count_116 b =? bit_count_116 a then b <? a
  else false.

Definition swap_adjacent_116 (j : nat) (l : list Z) : list Z :=
  match nth_error l j, nth_error l (S j) with
  | Some a, Some b =>
      if should_swap_116 a b
      then firstn j l ++ b :: a :: skipn (S (S j)) l
      else l
  | _, _ => l
  end.

Fixpoint bubble_pass_116_from (fuel j : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l
  | S fuel' => bubble_pass_116_from fuel' (S j) (swap_adjacent_116 j l)
  end.

Definition bubble_pass_116 (l : list Z) : list Z :=
  bubble_pass_116_from (length l - 1)%nat 0 l.

Fixpoint bubble_sort_116_fuel (fuel : nat) (l : list Z) : list Z :=
  match fuel with
  | O => l
  | S fuel' => bubble_sort_116_fuel fuel' (bubble_pass_116 l)
  end.

Definition bubble_sort_116 (l : list Z) : list Z :=
  bubble_sort_116_fuel (length l) l.

Definition problem_116_pre_z (input : list Z) : Prop :=
  problem_116_pre (map Z.to_nat input).

Definition problem_116_spec_z (input output : list Z) : Prop :=
  problem_116_spec (map Z.to_nat input) (map Z.to_nat output).

Definition sort_copy_prefix_116
  (i : Z) (input output : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = i /\
  output = sublist 0 i input.

Definition sort_score_prefix_116
  (i : Z) (input scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength scores = i /\
  scores = map bit_count_116 (sublist 0 i input).

Definition bubble_outer_prefix_116 (i : Z) (input : list Z) : list Z :=
  bubble_sort_116_fuel (Z.to_nat i) input.

Definition bubble_inner_prefix_116 (i j : Z) (input : list Z) : list Z :=
  bubble_pass_116_from (Z.to_nat (j - 1)) 0%nat (bubble_outer_prefix_116 i input).

Definition sort_outer_state_116
  (i : Z) (input output scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  output = bubble_outer_prefix_116 i input /\
  scores = map bit_count_116 output.

Definition sort_inner_state_116
  (i j : Z) (input output scores : list Z) : Prop :=
  0 <= i < Zlength input /\
  1 <= j <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  output = bubble_inner_prefix_116 i j input /\
  scores = map bit_count_116 output.

Lemma sort_array_116_int_range_at : forall input i,
  sort_array_116_int_range input ->
  0 <= i < Zlength input ->
  0 <= Znth i input 0 < INT_MAX.
Proof. auto. Qed.

Lemma bit_count_loop_116_bound : forall fuel n acc,
  0 <= n ->
  0 <= acc ->
  bit_count_loop_116 fuel n acc <= acc + Z.of_nat fuel.
Proof.
  induction fuel; intros n acc Hn Hacc; simpl.
  - lia.
  - destruct (Z.leb n 0) eqn:Hle.
    + lia.
    + apply Z.leb_gt in Hle.
      assert (Hrem: 0 <= Z.rem n 2 <= 1).
      { rewrite Z.rem_mod_nonneg by lia. pose proof (Z.mod_pos_bound n 2 ltac:(lia)); lia. }
      assert (Hquot: 0 <= n ÷ 2).
      { rewrite Z.quot_div_nonneg by lia. apply Z.div_pos; lia. }
      specialize (IHfuel (n ÷ 2) (acc + Z.rem n 2) Hquot ltac:(lia)).
      lia.
Qed.

Lemma bit_count_loop_116_nonneg : forall fuel n acc,
  0 <= n ->
  0 <= acc ->
  0 <= bit_count_loop_116 fuel n acc.
Proof.
  induction fuel; intros n acc Hn Hacc; simpl.
  - lia.
  - destruct (Z.leb n 0) eqn:Hle.
    + lia.
    + apply Z.leb_gt in Hle.
      assert (Hrem: 0 <= Z.rem n 2 <= 1).
      { rewrite Z.rem_mod_nonneg by lia. pose proof (Z.mod_pos_bound n 2 ltac:(lia)); lia. }
      assert (Hquot: 0 <= n ÷ 2).
      { rewrite Z.quot_div_nonneg by lia. apply Z.div_pos; lia. }
      apply IHfuel; lia.
Qed.

Lemma bit_count_loop_116_acc_lower : forall fuel n acc,
  0 <= n ->
  acc <= bit_count_loop_116 fuel n acc.
Proof.
  induction fuel; intros n acc Hn; simpl.
  - lia.
  - destruct (Z.leb n 0) eqn:Hle.
    + lia.
    + apply Z.leb_gt in Hle.
      assert (Hrem: 0 <= Z.rem n 2).
      { rewrite Z.rem_mod_nonneg by lia. pose proof (Z.mod_pos_bound n 2 ltac:(lia)); lia. }
      assert (Hquot: 0 <= n ÷ 2).
      { rewrite Z.quot_div_nonneg by lia. apply Z.div_pos; lia. }
      specialize (IHfuel (n ÷ 2) (acc + Z.rem n 2) Hquot).
      lia.
Qed.

Lemma bit_count_116_bounds : forall x,
  0 <= x < INT_MAX ->
  0 <= bit_count_116 x <= 31.
Proof.
  intros x Hx.
  unfold bit_count_116, bit_fuel_116.
  split.
  - apply bit_count_loop_116_nonneg; lia.
  - pose proof (bit_count_loop_116_bound 31%nat x 0 ltac:(lia) ltac:(lia)).
    change (Z.of_nat 31) with 31 in H.
    lia.
Qed.

Lemma bit_count_state_116_init : forall x n,
  0 <= x < INT_MAX ->
  n = Z.abs x ->
  bit_count_state_116 x n 0.
Proof.
  intros x n Hx Hn.
  subst n.
  rewrite Z.abs_eq by lia.
  unfold bit_count_state_116.
  repeat split; try lia.
  exists bit_fuel_116.
  split.
  - unfold bit_fuel_116.
    change (2 ^ Z.of_nat 31) with 2147483648.
    lia.
  - reflexivity.
Qed.

Lemma bit_count_state_116_step : forall x n b,
  bit_count_state_116 x n b ->
  n > 0 ->
  bit_count_state_116 x (n ÷ 2) (b + Z.rem n 2).
Proof.
  intros x n b [Hx [Hn [Hb [fuel [Hpow Hrun]]]]] Hpos.
  destruct fuel as [|fuel'].
  - simpl in Hpow; lia.
  - unfold bit_count_state_116.
    assert (Hrem: 0 <= Z.rem n 2 <= 1).
    { rewrite Z.rem_mod_nonneg by lia. pose proof (Z.mod_pos_bound n 2 ltac:(lia)); lia. }
    assert (Hquot: 0 <= n ÷ 2).
    { rewrite Z.quot_div_nonneg by lia. apply Z.div_pos; lia. }
    assert (Hquot_lt: n ÷ 2 < INT_MAX).
    { rewrite Z.quot_div_nonneg by lia. pose proof (Z.div_le_upper_bound n 2 n ltac:(lia) ltac:(nia)); lia. }
    split; [lia|].
    split; [lia|].
    simpl in Hrun.
    assert (Hleb: (n <=? 0) = false) by (apply Z.leb_gt; lia).
    rewrite Hleb in Hrun.
    split.
    {
      pose proof (bit_count_loop_116_acc_lower fuel' (n ÷ 2) (b + Z.rem n 2) Hquot).
      rewrite Hrun in H.
      pose proof (bit_count_116_bounds x Hx).
      lia.
    }
    exists fuel'.
    split; [|exact Hrun].
    rewrite Z.quot_div_nonneg by lia.
    apply Z.div_lt_upper_bound; try lia.
    replace (2 ^ Z.of_nat (S fuel')) with (2 * 2 ^ Z.of_nat fuel') in Hpow
      by (rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r by lia; reflexivity).
    exact Hpow.
Qed.

Lemma bit_count_state_116_final : forall x n b,
  bit_count_state_116 x n b ->
  n <= 0 ->
  bit_count_result_116 x b.
Proof.
  intros x n b [Hx [Hn [Hb [fuel [_ Hrun]]]]] Hle.
  assert (Hn0: n = 0) by lia.
  subst n.
  unfold bit_count_result_116.
  split; [exact Hx|].
  split; [exact Hb|].
  destruct fuel; simpl in Hrun.
  - assumption.
  - destruct (0 <=? 0) eqn:H; [assumption|apply Z.leb_gt in H; lia].
Qed.

Lemma bit_count_state_at_116_init : forall i input n,
  sort_array_116_int_range input ->
  0 <= i < Zlength input ->
  n = Z.abs (Znth i input 0) ->
  bit_count_state_at_116 i input n 0.
Proof.
  intros.
  unfold bit_count_state_at_116.
  eapply bit_count_state_116_init; eauto using sort_array_116_int_range_at.
Qed.

Lemma bit_count_state_at_116_step : forall i input n b,
  bit_count_state_at_116 i input n b ->
  n > 0 ->
  bit_count_state_at_116 i input (n ÷ 2) (b + Z.rem n 2).
Proof.
  intros.
  unfold bit_count_state_at_116 in *.
  eapply bit_count_state_116_step; eauto.
Qed.

Lemma bit_count_state_at_116_final : forall i input n b,
  bit_count_state_at_116 i input n b ->
  n <= 0 ->
  bit_count_result_116 (Znth i input 0) b.
Proof.
  intros.
  unfold bit_count_state_at_116 in H.
  eapply bit_count_state_116_final; eauto.
Qed.

Lemma Zlength_map_116 : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_116 : forall {A B : Type} (f : A -> B) (l : list A) i d d',
  0 <= i < Zlength l ->
  Znth i (map f l) d' = f (Znth i l d).
Proof.
  intros A B f l i d d' Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f d)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - rewrite (@map_nth A B f l d (Z.to_nat i)).
    reflexivity.
Qed.

Lemma map_replace_Znth_116 : forall {A B : Type} (f : A -> B) l i x,
  map f (replace_Znth i x l) =
  replace_Znth i (f x) (map f l).
Proof.
  intros A B f l i x.
  assert (Hrep: forall n (l0 : list A),
    map f (@replace_nth A n l0 x) = @replace_nth B n (map f l0) (f x)).
  {
    induction n; intros [|a l0]; simpl; try reflexivity.
    rewrite IHn; reflexivity.
  }
  unfold replace_Znth.
  apply Hrep.
Qed.

Lemma replace_Znth_length_116 : forall {A : Type} (l : list A) i x,
  Zlength (replace_Znth i x l) = Zlength l.
Proof.
  intros A l i x.
  unfold replace_Znth.
  repeat rewrite Zlength_correct.
  f_equal.
  revert l.
  generalize (Z.to_nat i) as n.
  induction n; intros [|a l0]; simpl; try reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Lemma sublist_snoc_Znth_116 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l).
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  reflexivity.
  - symmetry. apply sublist_single.
    lia.
  - lia.
  - lia.
Qed.

Lemma sort_copy_prefix_116_init : forall input,
  sort_copy_prefix_116 0 input nil.
Proof.
  intros.
  unfold sort_copy_prefix_116.
  split.
  - split; [lia|apply Zlength_nonneg].
  - split.
    + rewrite Zlength_nil. reflexivity.
    + symmetry. apply sublist_nil. lia.
Qed.

Lemma sort_copy_prefix_116_step : forall i input output x,
  sort_copy_prefix_116 i input output ->
  0 <= i < Zlength input ->
  x = Znth i input 0 ->
  sort_copy_prefix_116 (i + 1) input (output ++ x :: nil).
Proof.
  intros i input output x [Hi [Hout Houtput]] Hrange Hx.
  subst x.
  unfold sort_copy_prefix_116.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  repeat split; try lia.
  rewrite Houtput.
  rewrite sublist_snoc_Znth_116 by lia.
  reflexivity.
Qed.

Lemma sort_copy_prefix_116_self : forall input,
  sort_copy_prefix_116 (Zlength input) input input.
Proof.
  intros input.
  unfold sort_copy_prefix_116.
  split.
  - split; [apply Zlength_nonneg|lia].
  - split; [reflexivity|].
    symmetry. apply sublist_self; lia.
Qed.

Lemma sort_copy_prefix_116_final : forall i input output,
  sort_copy_prefix_116 i input output ->
  i >= Zlength input ->
  output = input.
Proof.
  intros i input output [Hi [_ Houtput]] Hge.
  assert (Hi_eq: i = Zlength input) by lia.
  subst i.
  rewrite Houtput.
  apply sublist_self; lia.
Qed.

Lemma sort_score_prefix_116_init : forall input,
  sort_score_prefix_116 0 input nil.
Proof.
  intros.
  unfold sort_score_prefix_116.
  split.
  - split; [lia|apply Zlength_nonneg].
  - split.
    + rewrite Zlength_nil. reflexivity.
    + symmetry.
      simpl. reflexivity.
Qed.

Lemma sort_score_prefix_116_step : forall i input scores b,
  sort_score_prefix_116 i input scores ->
  0 <= i < Zlength input ->
  bit_count_result_116 (Znth i input 0) b ->
  sort_score_prefix_116 (i + 1) input (scores ++ b :: nil).
Proof.
  intros i input scores b [Hi [Hscores Hscore]] Hrange [_ [_ Hb]].
  unfold sort_score_prefix_116.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  repeat split; try lia.
  rewrite Hscore.
  rewrite sublist_snoc_Znth_116 by lia.
  rewrite map_app.
  simpl.
  rewrite Hb.
  reflexivity.
Qed.

Lemma sort_outer_state_116_init : forall input output scores,
  sort_copy_prefix_116 (Zlength input) input output ->
  sort_score_prefix_116 (Zlength input) input scores ->
  sort_outer_state_116 0 input output scores.
Proof.
  intros input output scores [_ [Hout Houtput]] [_ [Hscores Hscore]].
  unfold sort_outer_state_116, bubble_outer_prefix_116.
  simpl.
  rewrite sublist_self in Houtput by lia.
  rewrite sublist_self in Hscore by lia.
  split.
  - split; [lia|apply Zlength_nonneg].
  - split.
    + exact Hout.
    + split.
      * exact Hscores.
      * split.
        -- exact Houtput.
        -- rewrite Houtput. exact Hscore.
Qed.

Lemma sort_inner_state_116_init : forall i input output scores,
  sort_outer_state_116 i input output scores ->
  0 <= i < Zlength input ->
  sort_inner_state_116 i 1 input output scores.
Proof.
  intros i input output scores Hstate Hi.
  unfold sort_outer_state_116, sort_inner_state_116, bubble_inner_prefix_116 in *.
  destruct Hstate as [H_i [Hout_len [Hscore_len [Houtput Hscore]]]].
  simpl.
  repeat split; try lia; assumption.
Qed.

Lemma bubble_pass_116_from_compose : forall n m start l,
  bubble_pass_116_from (n + m) start l =
  bubble_pass_116_from m (start + n)%nat
    (bubble_pass_116_from n start l).
Proof.
  induction n; intros m start l; simpl.
  - replace (start + 0)%nat with start by lia.
    reflexivity.
  - rewrite IHn.
    replace (start + S n)%nat with (S (start + n))%nat by lia.
    reflexivity.
Qed.

Lemma bubble_pass_116_from_next : forall n start l,
  bubble_pass_116_from (S n) start l =
  swap_adjacent_116 (start + n)%nat
    (bubble_pass_116_from n start l).
Proof.
  intros n start l.
  replace (S n) with (n + 1)%nat by lia.
  rewrite bubble_pass_116_from_compose.
  simpl.
  reflexivity.
Qed.

Lemma bubble_sort_116_fuel_snoc : forall n l,
  bubble_sort_116_fuel (S n) l =
  bubble_pass_116 (bubble_sort_116_fuel n l).
Proof.
  induction n; intros l.
  - reflexivity.
  - change (bubble_sort_116_fuel (S n) (bubble_pass_116 l) =
      bubble_pass_116 (bubble_sort_116_fuel (S n) l)).
    rewrite (IHn (bubble_pass_116 l)).
    reflexivity.
Qed.

Lemma swap_adjacent_116_length : forall j l,
  length (swap_adjacent_116 j l) = length l.
Proof.
  intros j l.
  unfold swap_adjacent_116.
  destruct (nth_error l j) as [a|] eqn:Ha;
    destruct (nth_error l (S j)) as [b|] eqn:Hb; try reflexivity.
  destruct (should_swap_116 a b); try reflexivity.
  assert (Hlen: (S j < length l)%nat).
  {
    apply (proj1 (nth_error_Some l (S j))).
    rewrite Hb; discriminate.
  }
  rewrite length_app.
  change (length (b :: a :: skipn (S (S j)) l))
    with (S (S (length (skipn (S (S j)) l)))).
  rewrite length_firstn, length_skipn.
  rewrite Nat.min_l by lia.
  lia.
Qed.

Lemma bubble_pass_116_from_length : forall fuel j l,
  length (bubble_pass_116_from fuel j l) = length l.
Proof.
  induction fuel; intros j l; simpl.
  - reflexivity.
  - rewrite IHfuel.
    apply swap_adjacent_116_length.
Qed.

Lemma bubble_pass_116_length : forall l,
  length (bubble_pass_116 l) = length l.
Proof.
  intros l.
  unfold bubble_pass_116.
  apply bubble_pass_116_from_length.
Qed.

Lemma bubble_sort_116_fuel_length : forall fuel l,
  length (bubble_sort_116_fuel fuel l) = length l.
Proof.
  induction fuel; intros l; simpl.
  - reflexivity.
  - rewrite IHfuel.
    apply bubble_pass_116_length.
Qed.

Lemma nth_error_Znth_116 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  nth_error l (Z.to_nat i) = Some (Znth i l d).
Proof.
  intros l i d Hi.
  unfold Znth.
  apply (@nth_error_nth' Z).
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma replace_nth_adjacent_116 : forall n (l : list Z),
  (S n < length l)%nat ->
  firstn n l ++ nth (S n) l 0 :: nth n l 0 :: skipn (S (S n)) l =
  replace_nth n
    (replace_nth (S n) l (nth n l 0))
    (nth (S n) l 0).
Proof.
  induction n; intros l Hlen; destruct l as [|x xs]; simpl in *; try lia.
  - destruct xs as [|y ys]; simpl in *; try lia.
    reflexivity.
  - f_equal.
    apply IHn.
    lia.
Qed.

Lemma replace_Znth_adjacent_116 : forall (l : list Z) j,
  0 <= j ->
  j + 1 < Zlength l ->
  firstn (Z.to_nat j) l ++
    Znth (j + 1) l 0 :: Znth j l 0 :: skipn (S (S (Z.to_nat j))) l =
  replace_Znth j (Znth (j + 1) l 0)
    (replace_Znth (j + 1) (Znth j l 0) l).
Proof.
  intros l j Hj Hjlen.
  unfold replace_Znth, Znth.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  apply replace_nth_adjacent_116.
  rewrite Zlength_correct in Hjlen.
  lia.
Qed.

Lemma should_swap_116_false : forall a b,
  ~ (bit_count_116 b < bit_count_116 a \/
      bit_count_116 b = bit_count_116 a /\ b < a) ->
  should_swap_116 a b = false.
Proof.
  intros a b H.
  unfold should_swap_116.
  destruct (bit_count_116 b <? bit_count_116 a) eqn:Hlt.
  - apply Z.ltb_lt in Hlt; exfalso; apply H; left; lia.
  - destruct (bit_count_116 b =? bit_count_116 a) eqn:Heq.
    + apply Z.eqb_eq in Heq.
      destruct (b <? a) eqn:Hba.
      * apply Z.ltb_lt in Hba; exfalso; apply H; right; lia.
      * reflexivity.
    + reflexivity.
Qed.

Lemma should_swap_116_true : forall a b,
  bit_count_116 b < bit_count_116 a \/
  bit_count_116 b = bit_count_116 a /\ b < a ->
  should_swap_116 a b = true.
Proof.
  intros a b H.
  unfold should_swap_116.
  destruct H as [Hlt|[Heq Hval]].
  - apply Z.ltb_lt in Hlt. rewrite Hlt. reflexivity.
  - assert (Hltb: (bit_count_116 b <? bit_count_116 a) = false) by (apply Z.ltb_ge; lia).
    rewrite Hltb.
    apply Z.eqb_eq in Heq.
    rewrite Heq.
    apply Z.ltb_lt in Hval.
    rewrite Hval.
    reflexivity.
Qed.

Lemma swap_adjacent_116_keep : forall l j,
  0 <= j ->
  j + 1 < Zlength l ->
  ~ (bit_count_116 (Znth (j + 1) l 0) < bit_count_116 (Znth j l 0) \/
      bit_count_116 (Znth (j + 1) l 0) = bit_count_116 (Znth j l 0) /\
      Znth (j + 1) l 0 < Znth j l 0) ->
  swap_adjacent_116 (Z.to_nat j) l = l.
Proof.
  intros l j Hj Hjlen Hkeep.
  unfold swap_adjacent_116.
  rewrite (nth_error_Znth_116 l j 0) by lia.
  replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) by lia.
  rewrite (nth_error_Znth_116 l (j + 1) 0) by lia.
  rewrite should_swap_116_false; auto.
Qed.

Lemma swap_adjacent_116_swap : forall l j,
  0 <= j ->
  j + 1 < Zlength l ->
  bit_count_116 (Znth (j + 1) l 0) < bit_count_116 (Znth j l 0) \/
  bit_count_116 (Znth (j + 1) l 0) = bit_count_116 (Znth j l 0) /\
  Znth (j + 1) l 0 < Znth j l 0 ->
  swap_adjacent_116 (Z.to_nat j) l =
    replace_Znth j (Znth (j + 1) l 0)
      (replace_Znth (j + 1) (Znth j l 0) l).
Proof.
  intros l j Hj Hjlen Hswap.
  unfold swap_adjacent_116.
  rewrite (nth_error_Znth_116 l j 0) by lia.
  replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) by lia.
  rewrite (nth_error_Znth_116 l (j + 1) 0) by lia.
  rewrite should_swap_116_true by exact Hswap.
  replace (S (Z.to_nat (j + 1))) with (S (S (Z.to_nat j))) by lia.
  apply replace_Znth_adjacent_116; lia.
Qed.

Lemma sort_inner_state_116_step_keep : forall i j input output scores,
  sort_inner_state_116 i j input output scores ->
  1 <= j < Zlength input ->
  ~ (Znth j scores 0 < Znth (j - 1) scores 0 \/
      Znth j scores 0 = Znth (j - 1) scores 0 /\
      Znth j output 0 < Znth (j - 1) output 0) ->
  sort_inner_state_116 i (j + 1) input output scores.
Proof.
  intros i j input output scores Hstate Hj Hkeep.
  unfold sort_inner_state_116 in *.
  destruct Hstate as [Hi [Hj0 [Hout_len [Hscore_len [Houtput Hscore]]]]].
  repeat split; try lia.
  - unfold bubble_inner_prefix_116 in *.
    replace (Z.to_nat (j + 1 - 1)) with (S (Z.to_nat (j - 1))) by lia.
    rewrite bubble_pass_116_from_next.
    rewrite <- Houtput.
    replace (0 + Z.to_nat (j - 1))%nat with (Z.to_nat (j - 1)) by lia.
    assert (Hkeep_bits:
      ~ (bit_count_116 (Znth (j - 1 + 1) output 0) <
          bit_count_116 (Znth (j - 1) output 0) \/
          bit_count_116 (Znth (j - 1 + 1) output 0) =
          bit_count_116 (Znth (j - 1) output 0) /\
          Znth (j - 1 + 1) output 0 < Znth (j - 1) output 0)).
    {
      replace (j - 1 + 1) with j by lia.
      rewrite Hscore in Hkeep.
      rewrite (Znth_map_116 bit_count_116 output j 0 0) in Hkeep by lia.
      rewrite (Znth_map_116 bit_count_116 output (j - 1) 0 0) in Hkeep by lia.
      exact Hkeep.
    }
    rewrite swap_adjacent_116_keep by (try lia; exact Hkeep_bits).
    reflexivity.
  - assumption.
Qed.

Lemma sort_inner_state_116_step_swap : forall i j input output scores,
  sort_inner_state_116 i j input output scores ->
  1 <= j < Zlength input ->
  Znth j scores 0 < Znth (j - 1) scores 0 \/
  Znth j scores 0 = Znth (j - 1) scores 0 /\
  Znth j output 0 < Znth (j - 1) output 0 ->
  sort_inner_state_116 i (j + 1) input
    (replace_Znth (j - 1) (Znth j output 0)
      (replace_Znth j (Znth (j - 1) output 0) output))
    (replace_Znth (j - 1) (Znth j scores 0)
      (replace_Znth j (Znth (j - 1) scores 0) scores)).
Proof.
  intros i j input output scores Hstate Hj Hswap.
  unfold sort_inner_state_116 in *.
  destruct Hstate as [Hi [Hj0 [Hout_len [Hscore_len [Houtput Hscore]]]]].
  repeat split; try lia.
  - rewrite (@replace_Znth_length_116 Z
      (replace_Znth j (Znth (j - 1) output 0) output)
      (j - 1) (Znth j output 0)).
    rewrite (@replace_Znth_length_116 Z output j (Znth (j - 1) output 0)).
    exact Hout_len.
  - rewrite (@replace_Znth_length_116 Z
      (replace_Znth j (Znth (j - 1) scores 0) scores)
      (j - 1) (Znth j scores 0)).
    rewrite (@replace_Znth_length_116 Z scores j (Znth (j - 1) scores 0)).
    exact Hscore_len.
  - unfold bubble_inner_prefix_116 in *.
    replace (Z.to_nat (j + 1 - 1)) with (S (Z.to_nat (j - 1))) by lia.
    rewrite bubble_pass_116_from_next.
    rewrite <- Houtput.
    replace (0 + Z.to_nat (j - 1))%nat with (Z.to_nat (j - 1)) by lia.
    assert (Hswap_bits:
      bit_count_116 (Znth (j - 1 + 1) output 0) <
      bit_count_116 (Znth (j - 1) output 0) \/
      bit_count_116 (Znth (j - 1 + 1) output 0) =
      bit_count_116 (Znth (j - 1) output 0) /\
      Znth (j - 1 + 1) output 0 < Znth (j - 1) output 0).
    {
      replace (j - 1 + 1) with j by lia.
      rewrite Hscore in Hswap.
      rewrite (Znth_map_116 bit_count_116 output j 0 0) in Hswap by lia.
      rewrite (Znth_map_116 bit_count_116 output (j - 1) 0 0) in Hswap by lia.
      exact Hswap.
    }
    rewrite swap_adjacent_116_swap by (try lia; exact Hswap_bits).
    replace (j - 1 + 1) with j by lia.
    reflexivity.
  - rewrite map_replace_Znth_116.
    rewrite map_replace_Znth_116.
    rewrite Hscore.
    rewrite (Znth_map_116 bit_count_116 output j 0 0) by lia.
    rewrite (Znth_map_116 bit_count_116 output (j - 1) 0 0) by lia.
    reflexivity.
Qed.

Lemma sort_outer_state_116_step : forall i input output scores,
  sort_inner_state_116 i (Zlength input) input output scores ->
  0 <= i < Zlength input ->
  sort_outer_state_116 (i + 1) input output scores.
Proof.
  intros i input output scores Hstate Hi.
  unfold sort_inner_state_116, sort_outer_state_116 in *.
  destruct Hstate as [_ [Hj [Hout_len [Hscore_len [Houtput Hscore]]]]].
  repeat split; try lia.
  - unfold bubble_inner_prefix_116, bubble_outer_prefix_116 in *.
    replace (Z.to_nat (Zlength input - 1)) with (length input - 1)%nat in Houtput.
    + replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite bubble_sort_116_fuel_snoc.
      unfold bubble_pass_116.
      rewrite bubble_sort_116_fuel_length.
      exact Houtput.
    + rewrite Zlength_correct.
      rewrite Z2Nat.inj_sub by lia.
      rewrite Nat2Z.id.
      reflexivity.
  - assumption.
Qed.

Lemma Z_ltb_of_nat_116 : forall a b,
  (Z.of_nat a <? Z.of_nat b) = (a <? b)%nat.
Proof.
  intros a b.
  destruct (Z.of_nat a <? Z.of_nat b) eqn:Hz;
    destruct (a <? b)%nat eqn:Hn; try reflexivity.
  - apply Z.ltb_lt in Hz. apply Nat.ltb_ge in Hn. lia.
  - apply Z.ltb_ge in Hz. apply Nat.ltb_lt in Hn. lia.
Qed.

Lemma Z_ltb_to_nat_nonneg_116 : forall a b,
  0 <= a ->
  0 <= b ->
  (a <? b) = (Z.to_nat a <? Z.to_nat b)%nat.
Proof.
  intros a b Ha Hb.
  destruct (a <? b) eqn:Hz; destruct (Z.to_nat a <? Z.to_nat b)%nat eqn:Hn;
    try reflexivity.
  - apply Z.ltb_lt in Hz. apply Nat.ltb_ge in Hn. lia.
  - apply Z.ltb_ge in Hz. apply Nat.ltb_lt in Hn.
    assert ((Z.to_nat b <= Z.to_nat a)%nat) by (apply Z2Nat.inj_le; lia).
    lia.
Qed.

Lemma Z_eqb_of_nat_116 : forall a b,
  (Z.of_nat a =? Z.of_nat b) = (a =? b)%nat.
Proof.
  intros a b.
  destruct (Z.of_nat a =? Z.of_nat b) eqn:Hz;
    destruct (a =? b)%nat eqn:Hn; try reflexivity.
  - apply Z.eqb_eq in Hz. apply Nat.eqb_neq in Hn. lia.
  - apply Z.eqb_neq in Hz. apply Nat.eqb_eq in Hn. lia.
Qed.

Definition should_swap_custom_bool (a b : nat) : bool :=
  if (count_ones b <? count_ones a)%nat then true
  else if (count_ones b =? count_ones a)%nat then (b <? a)%nat
  else false.

Definition swap_adjacent_custom (j : nat) (l : list nat) : list nat :=
  match nth_error l j, nth_error l (S j) with
  | Some a, Some b =>
      if should_swap_custom_bool a b
      then firstn j l ++ b :: a :: skipn (S (S j)) l
      else l
  | _, _ => l
  end.

Fixpoint bubble_pass_custom_from (fuel j : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S fuel' => bubble_pass_custom_from fuel' (S j) (swap_adjacent_custom j l)
  end.

Definition bubble_pass_custom (l : list nat) : list nat :=
  match l with
  | [] => []
  | _ :: xs => bubble_pass_custom_from (length xs) 0 l
  end.

Fixpoint bubble_sort_custom_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | O => l
  | S fuel' => bubble_sort_custom_fuel fuel' (bubble_pass_custom l)
  end.

Definition sort_array_impl (l : list nat) : list nat :=
  bubble_sort_custom_fuel (length l) l.

Local Opaque count_ones.

Lemma le_custom_trans_116 : forall a b c,
  le_custom a b ->
  le_custom b c ->
  le_custom a c.
Proof.
  intros a b c Hab Hbc.
  unfold le_custom in *.
  set (abits := count_ones a) in *.
  set (bbits := count_ones b) in *.
  set (cbits := count_ones c) in *.
  destruct Hab as [Hab | [Hab Hable]];
    destruct Hbc as [Hbc | [Hbc Hbcle]]; lia.
Qed.

Lemma le_custom_refl_116 : forall a,
  le_custom a a.
Proof.
  intros a.
  unfold le_custom.
  right. split; lia.
Qed.

Lemma should_swap_custom_bool_false_le_116 : forall a b,
  should_swap_custom_bool a b = false ->
  le_custom a b.
Proof.
  intros a b H.
  unfold should_swap_custom_bool in H.
  unfold le_custom.
  set (abits := count_ones a) in *.
  set (bbits := count_ones b) in *.
  destruct (bbits <? abits)%nat eqn:Hlt.
  - discriminate.
  - apply Nat.ltb_ge in Hlt.
    destruct (bbits =? abits)%nat eqn:Heq.
    + apply Nat.eqb_eq in Heq.
      apply Nat.ltb_ge in H.
      right. split; lia.
    + apply Nat.eqb_neq in Heq.
      left. lia.
Qed.

Lemma le_custom_should_swap_custom_bool_false_116 : forall a b,
  le_custom a b ->
  should_swap_custom_bool a b = false.
Proof.
  intros a b H.
  unfold le_custom in H.
  unfold should_swap_custom_bool.
  set (abits := count_ones a) in *.
  set (bbits := count_ones b) in *.
  destruct H as [Hlt | [Heq Hle]].
  - assert ((bbits <? abits)%nat = false) by (apply Nat.ltb_ge; lia).
    rewrite H.
    assert ((bbits =? abits)%nat = false) by (apply Nat.eqb_neq; lia).
    rewrite H0. reflexivity.
  - assert ((bbits <? abits)%nat = false) by (apply Nat.ltb_ge; lia).
    rewrite H.
    assert ((bbits =? abits)%nat = true) by (apply Nat.eqb_eq; lia).
    rewrite H0.
    apply Nat.ltb_ge. lia.
Qed.

Lemma should_swap_custom_bool_true_le_116 : forall a b,
  should_swap_custom_bool a b = true ->
  le_custom b a.
Proof.
  intros a b H.
  unfold should_swap_custom_bool in H.
  unfold le_custom.
  set (abits := count_ones a) in *.
  set (bbits := count_ones b) in *.
  destruct (bbits <? abits)%nat eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    left. exact Hlt.
  - destruct (bbits =? abits)%nat eqn:Heq; try discriminate.
    apply Nat.eqb_eq in Heq.
    apply Nat.ltb_lt in H.
    right. split; lia.
Qed.

Local Opaque should_swap_custom_bool.

Lemma swap_adjacent_custom_perm : forall j l,
  Permutation l (swap_adjacent_custom j l).
Proof.
  induction j as [|j IH]; intros [|x xs]; simpl; try constructor.
  - destruct xs as [|y ys]; simpl.
    + unfold swap_adjacent_custom; simpl.
      reflexivity.
    + unfold swap_adjacent_custom; simpl.
      destruct (should_swap_custom_bool x y); simpl.
      * apply perm_swap.
      * reflexivity.
  - destruct xs as [|y ys]; simpl.
    + unfold swap_adjacent_custom; simpl.
      rewrite nth_error_nil. reflexivity.
    + destruct (nth_error (y :: ys) j) eqn:Ha;
        destruct (nth_error (y :: ys) (S j)) eqn:Hb; simpl.
      * unfold swap_adjacent_custom; simpl.
        simpl in Hb.
        rewrite Ha, Hb.
        destruct (should_swap_custom_bool n n0) eqn:Hsw; simpl.
        -- apply perm_skip.
           specialize (IH (y :: ys)).
           unfold swap_adjacent_custom in IH.
           simpl in IH.
           rewrite Ha, Hb in IH.
           rewrite Hsw in IH.
           exact IH.
        -- reflexivity.
      * unfold swap_adjacent_custom; simpl.
        simpl in Hb.
        rewrite Ha, Hb. reflexivity.
      * unfold swap_adjacent_custom; simpl.
        rewrite Ha. reflexivity.
      * unfold swap_adjacent_custom; simpl.
        rewrite Ha. reflexivity.
Qed.

Lemma bubble_pass_custom_from_perm : forall fuel j l,
  Permutation l (bubble_pass_custom_from fuel j l).
Proof.
  induction fuel as [|fuel IH]; intros j l; simpl.
  - reflexivity.
  - eapply Permutation_trans.
    + apply swap_adjacent_custom_perm.
    + apply IH.
Qed.

Lemma bubble_pass_custom_perm : forall l,
  Permutation l (bubble_pass_custom l).
Proof.
  intros [|x xs].
  - reflexivity.
  - simpl.
  unfold bubble_pass_custom.
  simpl.
  apply bubble_pass_custom_from_perm.
Qed.

Lemma swap_adjacent_custom_length_116 : forall j l,
  length (swap_adjacent_custom j l) = length l.
Proof.
  intros j l.
  symmetry.
  apply Permutation_length.
  apply swap_adjacent_custom_perm.
Qed.

Lemma bubble_pass_custom_from_length_116 : forall fuel j l,
  length (bubble_pass_custom_from fuel j l) = length l.
Proof.
  induction fuel as [|fuel IH]; intros j l; simpl.
  - reflexivity.
  - rewrite IH.
    apply swap_adjacent_custom_length_116.
Qed.

Lemma bubble_sort_custom_fuel_perm : forall fuel l,
  Permutation l (bubble_sort_custom_fuel fuel l).
Proof.
  induction fuel as [|fuel IH]; intros l; simpl.
  - reflexivity.
  - eapply Permutation_trans.
    + apply bubble_pass_custom_perm.
    + apply IH.
Qed.

Lemma sort_array_impl_perm : forall l,
  Permutation (sort_array_impl l) l.
Proof.
  intros l.
  unfold sort_array_impl.
  symmetry.
  apply bubble_sort_custom_fuel_perm.
Qed.

Lemma Forall_permutation_116 : forall {A : Type} (P : A -> Prop) l1 l2,
  Permutation l1 l2 ->
  Forall P l1 ->
  Forall P l2.
Proof.
  intros A P l1 l2 Hperm Hall.
  eapply Permutation_Forall; eauto.
Qed.

Lemma swap_adjacent_custom_cons_116 : forall j x l,
  swap_adjacent_custom (S j) (x :: l) =
  x :: swap_adjacent_custom j l.
Proof.
  intros j x l.
  destruct l as [|y ys].
  - unfold swap_adjacent_custom. simpl.
    rewrite nth_error_nil. reflexivity.
  - unfold swap_adjacent_custom. simpl.
    destruct (nth_error (y :: ys) j);
      destruct (nth_error ys j);
      try destruct (should_swap_custom_bool n n0);
      reflexivity.
Qed.

Lemma bubble_pass_custom_from_cons_116 : forall fuel j x l,
  bubble_pass_custom_from fuel (S j) (x :: l) =
  x :: bubble_pass_custom_from fuel j l.
Proof.
  induction fuel as [|fuel IH]; intros j x l; simpl.
  - reflexivity.
  - rewrite swap_adjacent_custom_cons_116.
    rewrite IH.
    reflexivity.
Qed.

Lemma bubble_pass_custom_from_cons0_116 : forall fuel x l,
  bubble_pass_custom_from fuel 1 (x :: l) =
  x :: bubble_pass_custom_from fuel 0 l.
Proof.
  intros fuel x l.
  change 1%nat with (S 0%nat).
  apply bubble_pass_custom_from_cons_116.
Qed.

Lemma bubble_pass_custom_from_step_116 : forall fuel j l,
  bubble_pass_custom_from (S fuel) j l =
  bubble_pass_custom_from fuel (S j) (swap_adjacent_custom j l).
Proof.
  reflexivity.
Qed.

Lemma swap_adjacent_custom_zero_true_116 : forall x y ys,
  should_swap_custom_bool x y = true ->
  swap_adjacent_custom 0 (x :: y :: ys) = y :: x :: ys.
Proof.
  intros x y ys Hsw.
  unfold swap_adjacent_custom.
  simpl.
  rewrite Hsw.
  reflexivity.
Qed.

Lemma swap_adjacent_custom_zero_false_116 : forall x y ys,
  should_swap_custom_bool x y = false ->
  swap_adjacent_custom 0 (x :: y :: ys) = x :: y :: ys.
Proof.
  intros x y ys Hsw.
  unfold swap_adjacent_custom.
  simpl.
  rewrite Hsw.
  reflexivity.
Qed.

Local Opaque bubble_pass_custom_from.

Fixpoint bubble_pass_custom_prefix_116 (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | y :: ys =>
      if should_swap_custom_bool x y
      then y :: bubble_pass_custom_prefix_116 x ys
      else x :: bubble_pass_custom_prefix_116 y ys
  end.

Fixpoint bubble_pass_custom_max_116 (x : nat) (l : list nat) : nat :=
  match l with
  | [] => x
  | y :: ys =>
      if should_swap_custom_bool x y
      then bubble_pass_custom_max_116 x ys
      else bubble_pass_custom_max_116 y ys
  end.

Lemma bubble_pass_custom_cons_true_116 : forall x y ys,
  should_swap_custom_bool x y = true ->
  bubble_pass_custom (x :: y :: ys) =
  y :: bubble_pass_custom (x :: ys).
Proof.
  abstract (
    intros x y ys Hsw;
    unfold bubble_pass_custom;
    cbn [length];
    rewrite bubble_pass_custom_from_step_116;
    rewrite (swap_adjacent_custom_zero_true_116 x y ys Hsw);
    rewrite bubble_pass_custom_from_cons0_116;
    reflexivity
  ).
Qed.

Lemma bubble_pass_custom_cons_false_116 : forall x y ys,
  should_swap_custom_bool x y = false ->
  bubble_pass_custom (x :: y :: ys) =
  x :: bubble_pass_custom (y :: ys).
Proof.
  abstract (
    intros x y ys Hsw;
    unfold bubble_pass_custom;
    cbn [length];
    rewrite bubble_pass_custom_from_step_116;
    rewrite (swap_adjacent_custom_zero_false_116 x y ys Hsw);
    rewrite bubble_pass_custom_from_cons0_116;
    reflexivity
  ).
Qed.

Lemma bubble_pass_custom_prefix_eq_116 : forall x l,
  bubble_pass_custom (x :: l) =
  bubble_pass_custom_prefix_116 x l ++
  [bubble_pass_custom_max_116 x l].
Proof.
  intros x l.
  revert x.
  induction l as [|y ys IH]; intros x.
  - reflexivity.
  - destruct (should_swap_custom_bool x y) eqn:Hsw.
    + rewrite bubble_pass_custom_cons_true_116 by exact Hsw.
      cbn [bubble_pass_custom_prefix_116 bubble_pass_custom_max_116].
      rewrite Hsw.
      rewrite IH.
      reflexivity.
    + rewrite bubble_pass_custom_cons_false_116 by exact Hsw.
      cbn [bubble_pass_custom_prefix_116 bubble_pass_custom_max_116].
      rewrite Hsw.
      rewrite IH.
      reflexivity.
Defined.

Local Transparent bubble_pass_custom_from.

Lemma bubble_pass_custom_max_forall_116 : forall x l,
  Forall (fun y => le_custom y (bubble_pass_custom_max_116 x l)) (x :: l).
Proof.
  intros x l.
  revert x.
  induction l as [|y ys IH]; intros x.
  - simpl.
    constructor; [apply le_custom_refl_116 | constructor].
  - simpl.
    destruct (should_swap_custom_bool x y) eqn:Hsw.
    + 
      specialize (IH x).
      inversion_clear IH as [|? ? Hxm Htail].
      constructor.
      * exact Hxm.
      * constructor.
        -- eapply (le_custom_trans_116 y x (bubble_pass_custom_max_116 x ys)).
           ++ apply should_swap_custom_bool_true_le_116. exact Hsw.
           ++ exact Hxm.
        -- exact Htail.
    +
      specialize (IH y).
      inversion_clear IH as [|? ? Hym Htail].
      constructor.
      * eapply (le_custom_trans_116 x y (bubble_pass_custom_max_116 y ys)).
        -- apply should_swap_custom_bool_false_le_116. exact Hsw.
        -- exact Hym.
      * constructor; [exact Hym | exact Htail].
Qed.

Lemma bubble_pass_custom_app_last_116 : forall p m,
  Forall (fun y => le_custom y m) p ->
  bubble_pass_custom (p ++ [m]) =
  bubble_pass_custom p ++ [m].
Proof.
  intros p m Hall.
  destruct p as [|x xs].
  - reflexivity.
  - simpl in Hall.
    revert x Hall.
    induction xs as [|y ys IH]; intros x Hall.
    + simpl in Hall.
      inversion Hall as [|? ? Hxm _]; subst.
      change (bubble_pass_custom (x :: m :: []) =
        bubble_pass_custom (x :: []) ++ [m]).
      rewrite bubble_pass_custom_cons_false_116
        by (apply le_custom_should_swap_custom_bool_false_116; exact Hxm).
      reflexivity.
    + simpl in Hall.
      inversion Hall as [|? ? Hxm Hall_tail]; subst.
      inversion Hall_tail as [|? ? Hym Hys]; subst.
      change (bubble_pass_custom (x :: y :: (ys ++ [m])) =
        bubble_pass_custom (x :: y :: ys) ++ [m]).
      destruct (should_swap_custom_bool x y) eqn:Hsw.
      * rewrite bubble_pass_custom_cons_true_116 by exact Hsw.
        rewrite bubble_pass_custom_cons_true_116 by exact Hsw.
        change (bubble_pass_custom (x :: ys ++ [m])) with
          (bubble_pass_custom ((x :: ys) ++ [m])).
        rewrite IH.
        -- reflexivity.
        -- constructor; assumption.
      * rewrite bubble_pass_custom_cons_false_116 by exact Hsw.
        rewrite bubble_pass_custom_cons_false_116 by exact Hsw.
        change (bubble_pass_custom (y :: ys ++ [m])) with
          (bubble_pass_custom ((y :: ys) ++ [m])).
        rewrite IH.
        -- reflexivity.
        -- exact Hall_tail.
Qed.

Lemma bubble_sort_custom_fuel_app_last_116 : forall fuel p m,
  Forall (fun y => le_custom y m) p ->
  bubble_sort_custom_fuel fuel (p ++ [m]) =
  bubble_sort_custom_fuel fuel p ++ [m].
Proof.
  induction fuel as [|fuel IH]; intros p m Hall; simpl.
  - reflexivity.
  - rewrite bubble_pass_custom_app_last_116 by exact Hall.
    rewrite IH.
    + reflexivity.
    + eapply Forall_permutation_116.
      * apply bubble_pass_custom_perm.
      * exact Hall.
Qed.

Lemma HdRel_snoc_116 : forall a l m,
  HdRel le_custom a l ->
  le_custom a m ->
  HdRel le_custom a (l ++ [m]).
Proof.
  intros a l m Hhd Ham.
  induction l as [|x xs IH].
  - simpl. constructor. exact Ham.
  - simpl.
    inversion Hhd; subst.
    constructor. assumption.
Qed.

Lemma Sorted_snoc_116 : forall l m,
  Sorted le_custom l ->
  Forall (fun x => le_custom x m) l ->
  Sorted le_custom (l ++ [m]).
Proof.
  induction l as [|x xs IH]; intros m Hsorted Hall.
  - simpl. constructor; [constructor | constructor].
  - simpl.
    inversion Hsorted as [|? ? Hsorted_tail Hhd]; subst.
    inversion Hall as [|? ? Hxm Hall_tail]; subst.
    constructor.
    + apply IH; assumption.
    + apply HdRel_snoc_116; assumption.
Qed.

Local Opaque bubble_pass_custom.

Lemma bubble_sort_custom_fuel_sorted_length_116 : forall n l,
  length l = n ->
  Sorted le_custom (bubble_sort_custom_fuel n l).
Proof.
  induction n as [|n IH]; intros l Hlen.
  - destruct l; simpl in Hlen; try lia.
    simpl. constructor.
  - destruct l as [|x xs].
    + simpl in Hlen. lia.
    + simpl.
      set (p := bubble_pass_custom_prefix_116 x xs).
      set (m := bubble_pass_custom_max_116 x xs).
      pose proof (bubble_pass_custom_prefix_eq_116 x xs) as Hpass.
      fold p in Hpass.
      fold m in Hpass.
      pose proof (bubble_pass_custom_max_forall_116 x xs) as Hall.
      fold m in Hall.
      pose proof (bubble_pass_custom_perm (x :: xs)) as Hperm.
      rewrite Hpass in Hperm.
      rewrite Hpass.
      assert (Hp_forall : Forall (fun y => le_custom y m) p).
      {
        pose proof (Forall_permutation_116
          (fun y => le_custom y m) (x :: xs) (p ++ [m]) Hperm Hall) as Hall_pm.
        apply Forall_app in Hall_pm.
        tauto.
      }
      rewrite bubble_sort_custom_fuel_app_last_116 by exact Hp_forall.
      apply Sorted_snoc_116.
      * apply IH.
        apply Permutation_length in Hperm.
        rewrite app_length in Hperm.
        simpl in Hperm.
        simpl in Hlen.
        lia.
      * eapply Forall_permutation_116.
        -- apply bubble_sort_custom_fuel_perm.
        -- exact Hp_forall.
Qed.

Lemma sort_array_impl_spec_116 : forall l,
  Permutation (sort_array_impl l) l /\
  Sorted le_custom (sort_array_impl l).
Proof.
  intros l.
  split.
  - apply sort_array_impl_perm.
  - unfold sort_array_impl.
    apply bubble_sort_custom_fuel_sorted_length_116.
    reflexivity.
Qed.

Local Transparent bubble_pass_custom.
Local Transparent should_swap_custom_bool.

Local Transparent count_ones.

Fixpoint count_ones_helper (n fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' => (n mod 2 + count_ones_helper (n / 2) fuel')%nat
  end.

Lemma count_ones_helper_zero_116 : forall fuel,
  count_ones_helper 0 fuel = 0%nat.
Proof.
  induction fuel; simpl; auto.
Qed.

Lemma div2_pow_116 : forall n p,
  ((n / 2) / Nat.pow 2 p = n / Nat.pow 2 (S p))%nat.
Proof.
  intros.
  rewrite Nat.div_div by (try lia; apply Nat.pow_nonzero; lia).
  rewrite Nat.pow_succ_r'.
  reflexivity.
Qed.

Lemma length_filter_map_116 : forall {A B : Type} (p : B -> bool) (f : A -> B) l,
  length (filter p (map f l)) = length (filter (fun x => p (f x)) l).
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (p (f a)); simpl; lia.
Qed.

Lemma count_ones_filter_tail_116 : forall fuel n,
  length (filter (fun p => Nat.eqb (((n / Nat.pow 2 p) mod 2)%nat) 1) (seq 1 fuel)) =
  length (filter (fun p => Nat.eqb ((((n / 2) / Nat.pow 2 p) mod 2)%nat) 1) (seq 0 fuel)).
Proof.
  intros.
  rewrite <- (seq_shift fuel 0).
  rewrite length_filter_map_116.
  apply f_equal.
  apply filter_ext.
  intro p.
  rewrite div2_pow_116.
  reflexivity.
Qed.

Lemma count_ones_helper_spec_116 : forall fuel n,
  count_ones_helper n fuel =
  length (filter (fun p => Nat.eqb (((n / Nat.pow 2 p) mod 2)%nat) 1) (seq 0 fuel)).
Proof.
  induction fuel as [|fuel IH]; intros n; [reflexivity|].
  change (count_ones_helper n (S fuel)) with
    ((n mod 2) + count_ones_helper (n / 2) fuel)%nat.
  change (seq 0%nat (S fuel)) with (0%nat :: seq 1%nat fuel).
  cbn [filter].
  change (Nat.pow 2 0) with 1%nat.
  rewrite Nat.div_1_r.
  destruct (Nat.eqb (n mod 2) 1) eqn:Hbit.
  - apply Nat.eqb_eq in Hbit.
    rewrite Hbit.
    change (1 + count_ones_helper (n / 2) fuel =
      S (length (filter (fun p => Nat.eqb (((n / Nat.pow 2 p) mod 2)%nat) 1) (seq 1 fuel))))%nat.
    rewrite IH.
    rewrite count_ones_filter_tail_116.
    lia.
  - apply Nat.eqb_neq in Hbit.
    assert (Hmod: (n mod 2 = 0)%nat).
    { pose proof (Nat.mod_upper_bound n 2 ltac:(lia)); lia. }
    rewrite Hmod.
    change (0 + count_ones_helper (n / 2) fuel =
      length (filter (fun p => Nat.eqb (((n / Nat.pow 2 p) mod 2)%nat) 1) (seq 1 fuel)))%nat.
    rewrite IH.
    rewrite count_ones_filter_tail_116.
    lia.
Qed.

Lemma bit_count_loop_116_to_nat : forall fuel n acc,
  0 <= n ->
  0 <= acc ->
  Z.to_nat (bit_count_loop_116 fuel n acc) =
  (Z.to_nat acc + count_ones_helper (Z.to_nat n) fuel)%nat.
Proof.
  induction fuel as [|fuel IH]; intros n acc Hn Hacc.
  - simpl. lia.
  - simpl.
    destruct (n <=? 0) eqn:Hle.
    + apply Z.leb_le in Hle.
      assert (n = 0) by lia.
      subst n.
      rewrite count_ones_helper_zero_116. simpl. lia.
    + apply Z.leb_gt in Hle.
      assert (Hrem: 0 <= Z.rem n 2).
      { rewrite Z.rem_mod_nonneg by lia.
        pose proof (Z.mod_pos_bound n 2 ltac:(lia)); lia. }
      assert (Hquot: 0 <= n ÷ 2).
      { rewrite Z.quot_div_nonneg by lia. apply Z.div_pos; lia. }
      rewrite IH by lia.
      rewrite Z2Nat.inj_add by lia.
      rewrite Z.quot_div_nonneg by lia.
      rewrite Z.rem_mod_nonneg by lia.
      rewrite Z2Nat.inj_div by lia.
      rewrite Z2Nat.inj_mod by lia.
      change (Z.to_nat 2) with 2%nat.
      destruct (Z.to_nat n) as [|n'] eqn:Hnat; [lia|].
      simpl.
      lia.
Qed.

Lemma bit_count_116_to_nat : forall x,
  0 <= x ->
  Z.to_nat (bit_count_116 x) = count_ones (Z.to_nat x).
Proof.
  intros x Hx.
  pose proof (bit_count_loop_116_to_nat bit_fuel_116 x 0 Hx ltac:(lia)) as H.
  unfold bit_count_116, count_ones, bit_fuel_116.
  unfold bit_fuel_116 in H.
  rewrite H.
  change (Z.to_nat 0) with 0%nat.
  rewrite Nat.add_0_l.
  apply count_ones_helper_spec_116.
Qed.

Lemma bit_count_116_of_nat : forall x,
  0 <= x ->
  bit_count_116 x = Z.of_nat (count_ones (Z.to_nat x)).
Proof.
  intros x Hx.
  pose proof (bit_count_116_to_nat x Hx) as Hto.
  apply (f_equal Z.of_nat) in Hto.
  rewrite Z2Nat.id in Hto.
  - exact Hto.
  - unfold bit_count_116.
    apply bit_count_loop_116_nonneg; lia.
Qed.

Lemma should_swap_116_to_nat : forall a b,
  0 <= a ->
  0 <= b ->
  should_swap_116 a b =
  should_swap_custom_bool (Z.to_nat a) (Z.to_nat b).
Proof.
  intros a b Ha Hb.
  unfold should_swap_116, should_swap_custom_bool.
  rewrite (bit_count_116_of_nat a Ha).
  rewrite (bit_count_116_of_nat b Hb).
  repeat rewrite Z_ltb_of_nat_116.
  repeat rewrite Z_eqb_of_nat_116.
  rewrite Z_ltb_to_nat_nonneg_116 by lia.
  reflexivity.
Qed.

Lemma map_firstn_116 : forall {A B : Type} (f : A -> B) n l,
  map f (firstn n l) = firstn n (map f l).
Proof.
  induction n as [|n IH]; intros [|x xs]; simpl; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma map_skipn_116 : forall {A B : Type} (f : A -> B) n l,
  map f (skipn n l) = skipn n (map f l).
Proof.
  induction n as [|n IH]; intros [|x xs]; simpl; try reflexivity.
  apply IH.
Qed.

Lemma in_firstn_116 : forall {A : Type} (x : A) n l,
  In x (firstn n l) -> In x l.
Proof.
  induction n as [|n IH]; intros [|y ys] Hin; simpl in *; try contradiction.
  destruct Hin as [Hin | Hin].
  - left. assumption.
  - right. eapply IH; eauto.
Qed.

Lemma in_skipn_116 : forall {A : Type} (x : A) n l,
  In x (skipn n l) -> In x l.
Proof.
  induction n as [|n IH]; intros [|y ys] Hin; simpl in *; try assumption.
  right. eapply IH; eauto.
Qed.

Lemma Forall_firstn_116 : forall {A : Type} (P : A -> Prop) n l,
  Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l Hforall.
  rewrite Forall_forall in *.
  intros x Hin.
  apply Hforall.
  eapply in_firstn_116; eauto.
Qed.

Lemma Forall_skipn_116 : forall {A : Type} (P : A -> Prop) n l,
  Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n l Hforall.
  rewrite Forall_forall in *.
  intros x Hin.
  apply Hforall.
  eapply in_skipn_116; eauto.
Qed.

Lemma Forall_nth_error_nonneg_116 : forall l n x,
  Forall (fun z => 0 <= z) l ->
  nth_error l n = Some x ->
  0 <= x.
Proof.
  intros l n x Hforall Hnth.
  rewrite Forall_forall in Hforall.
  apply Hforall.
  eapply nth_error_In; eauto.
Qed.

Lemma swap_adjacent_116_Forall_nonneg : forall j l,
  Forall (fun z => 0 <= z) l ->
  Forall (fun z => 0 <= z) (swap_adjacent_116 j l).
Proof.
  intros j l Hforall.
  unfold swap_adjacent_116.
  destruct (nth_error l j) as [a|] eqn:Ha;
    destruct (nth_error l (S j)) as [b|] eqn:Hb; try assumption.
  destruct (should_swap_116 a b); try assumption.
  apply Forall_app.
  split.
  - apply Forall_firstn_116. assumption.
  - constructor.
    + eapply Forall_nth_error_nonneg_116; eauto.
    + constructor.
      * eapply Forall_nth_error_nonneg_116; eauto.
      * apply Forall_skipn_116. assumption.
Qed.

Lemma swap_adjacent_116_map : forall j l,
  Forall (fun z => 0 <= z) l ->
  map Z.to_nat (swap_adjacent_116 j l) =
  swap_adjacent_custom j (map Z.to_nat l).
Proof.
  intros j l Hforall.
  unfold swap_adjacent_116.
  destruct (nth_error l j) as [a|] eqn:Ha;
    destruct (nth_error l (S j)) as [b|] eqn:Hb.
  - unfold swap_adjacent_custom.
    rewrite (@nth_error_map Z nat Z.to_nat j l), Ha.
    rewrite (@nth_error_map Z nat Z.to_nat (S j) l), Hb.
    simpl.
    assert (Ha_nonneg : 0 <= a) by
      (eapply Forall_nth_error_nonneg_116; eauto).
    assert (Hb_nonneg : 0 <= b) by
      (eapply Forall_nth_error_nonneg_116; eauto).
    rewrite should_swap_116_to_nat by lia.
    destruct (should_swap_custom_bool (Z.to_nat a) (Z.to_nat b)).
    + rewrite map_app, map_firstn_116.
      simpl.
      try rewrite map_skipn_116.
      change (map Z.to_nat
        match l with
        | _ :: _ :: l0 => skipn j l0
        | _ => []
        end) with (map Z.to_nat (skipn (S (S j)) l)).
      rewrite map_skipn_116.
      reflexivity.
    + reflexivity.
  - unfold swap_adjacent_custom.
    rewrite (@nth_error_map Z nat Z.to_nat j l), Ha.
    rewrite (@nth_error_map Z nat Z.to_nat (S j) l), Hb.
    reflexivity.
  - unfold swap_adjacent_custom.
    rewrite (@nth_error_map Z nat Z.to_nat j l), Ha.
    reflexivity.
  - unfold swap_adjacent_custom.
    rewrite (@nth_error_map Z nat Z.to_nat j l), Ha.
    reflexivity.
Qed.

Lemma bubble_pass_116_from_map : forall fuel j l,
  Forall (fun z => 0 <= z) l ->
  map Z.to_nat (bubble_pass_116_from fuel j l) =
    bubble_pass_custom_from fuel j (map Z.to_nat l) /\
  Forall (fun z => 0 <= z) (bubble_pass_116_from fuel j l).
Proof.
  induction fuel as [|fuel IH]; intros j l Hforall.
  - simpl. split; reflexivity || assumption.
  - simpl.
    pose proof (swap_adjacent_116_map j l Hforall) as Hmap.
    pose proof (swap_adjacent_116_Forall_nonneg j l Hforall) as Hforall_swap.
    specialize (IH (S j) (swap_adjacent_116 j l) Hforall_swap) as [IHmap IHforall].
    rewrite IHmap.
    rewrite Hmap.
    split; reflexivity || exact IHforall.
Qed.

Lemma bubble_pass_116_map : forall l,
  Forall (fun z => 0 <= z) l ->
  map Z.to_nat (bubble_pass_116 l) =
  bubble_pass_custom (map Z.to_nat l) /\
  Forall (fun z => 0 <= z) (bubble_pass_116 l).
Proof.
  intros [|x xs] Hforall.
  unfold bubble_pass_116, bubble_pass_custom.
  - simpl. split; [reflexivity | assumption].
  - unfold bubble_pass_116, bubble_pass_custom.
    simpl map.
    cbn [length Nat.sub].
    rewrite map_length.
    rewrite Nat.sub_0_r.
    apply bubble_pass_116_from_map.
    assumption.
Qed.

Lemma bubble_sort_116_fuel_map : forall fuel l,
  Forall (fun z => 0 <= z) l ->
  map Z.to_nat (bubble_sort_116_fuel fuel l) =
    bubble_sort_custom_fuel fuel (map Z.to_nat l) /\
  Forall (fun z => 0 <= z) (bubble_sort_116_fuel fuel l).
Proof.
  induction fuel as [|fuel IH]; intros l Hforall.
  - simpl. split; reflexivity || assumption.
  - simpl.
    pose proof (bubble_pass_116_map l Hforall) as [Hpass_map Hpass_forall].
    specialize (IH (bubble_pass_116 l) Hpass_forall) as [IHmap IHforall].
    rewrite IHmap.
    rewrite Hpass_map.
    split; reflexivity || exact IHforall.
Qed.

Lemma bubble_sort_116_map_sort_array_impl : forall input,
  Forall (fun z => 0 <= z) input ->
  map Z.to_nat (bubble_sort_116 input) =
  sort_array_impl (map Z.to_nat input).
Proof.
  intros input Hforall.
  unfold bubble_sort_116, sort_array_impl.
  rewrite map_length.
  apply bubble_sort_116_fuel_map.
  assumption.
Qed.

Lemma sort_array_116_int_range_Forall_nonneg : forall input,
  sort_array_116_int_range input ->
  Forall (fun z => 0 <= z) input.
Proof.
  intros input Hrange.
  rewrite Forall_forall.
  intros x Hin.
  destruct (In_nth_error input x Hin) as [n Hnth].
  assert (Hsome : (n < length input)%nat).
  { apply (proj1 (nth_error_Some input n)).
    rewrite Hnth. discriminate. }
  specialize (Hrange (Z.of_nat n)).
  rewrite Zlength_correct in Hrange.
  assert (0 <= Z.of_nat n < Z.of_nat (length input)) by lia.
  specialize (Hrange H).
  unfold Znth in Hrange.
  rewrite Nat2Z.id in Hrange.
  rewrite (nth_error_nth input n 0 Hnth) in Hrange.
  lia.
Qed.

Lemma sort_outer_state_116_final_spec : forall input output scores,
  sort_array_116_int_range input ->
  sort_outer_state_116 (Zlength input) input output scores ->
  problem_116_spec_z input output.
Proof.
  intros input output scores Hrange Hstate.
  unfold sort_outer_state_116 in Hstate.
  destruct Hstate as [_ [_ [_ [Houtput _]]]].
  unfold problem_116_spec_z, problem_116_spec.
  rewrite Houtput.
  unfold bubble_outer_prefix_116.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  pose proof (sort_array_116_int_range_Forall_nonneg input Hrange) as Hnonneg.
  fold (bubble_sort_116 input).
  rewrite (bubble_sort_116_map_sort_array_impl input Hnonneg).
  apply sort_array_impl_spec_116.
Qed.
