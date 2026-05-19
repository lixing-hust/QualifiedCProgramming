Load "../spec/116".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
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
    map f (@replace_nth A n x l0) = @replace_nth B n (f x) (map f l0)).
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
    rewrite <- Zlength_correct. lia.
  - lia.
  - rewrite <- Zlength_correct. lia.
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
      rewrite sublist_nil by lia.
      reflexivity.
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
  replace_nth n (nth (S n) l 0)
    (replace_nth (S n) (nth n l 0) l).
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
      simpl. lia.
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
  change (Z.to_nat (bit_count_loop_116 31 x 0) =
          count_ones_helper (Z.to_nat x) 31).
  rewrite H.
  reflexivity.
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
  intros l Hforall.
  unfold bubble_pass_116, bubble_pass_custom.
  rewrite map_length.
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
  apply bubble_sort_116_map_sort_array_impl.
  apply sort_array_116_int_range_Forall_nonneg.
  assumption.
Qed.
