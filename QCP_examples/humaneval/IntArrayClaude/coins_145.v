Load "../spec/145".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition Zabs (x : Z) : Z := Z.abs x.

Definition first_digit_value_145 (n : Z) : Z :=
  msd_fuel digit_fuel_145 n.

Definition first_digit_state_145 (original current : Z) : Prop :=
  exists fuel,
    0 <= current <= original /\
    current < 10 ^ Z.of_nat fuel /\
    first_digit_value_145 original = msd_fuel fuel current.

Fixpoint signed_digit_tail_loop (fuel : nat) (t sum : Z) : Z :=
  match fuel with
  | O => sum
  | S fuel' =>
      if Z.leb t 0
      then sum
      else signed_digit_tail_loop fuel' (t / 10) (sum + t mod 10)
  end.

Definition signed_digit_tail_state (x t sum : Z) : Prop :=
  0 <= t < 100000000 /\
  -100 <= sum /\
  exists fuel,
    t < 10 ^ Z.of_nat fuel /\
    0 <= sum_digits_pos_fuel fuel t /\
    sum + sum_digits_pos_fuel fuel t <= 100 /\
    signed_digit_tail_loop fuel t sum = sum_digits x.

Definition highest_power10_state (x t p sum : Z) : Prop :=
  t = Z.abs x /\
  10 <= t < 100000000 /\
  1 <= p <= t /\
  -100 <= sum <= 100 /\
  exists fuel,
    (highest_power10_loop_145 fuel t p) * 10 > t /\
    signed_digit_tail_state x (Z.rem t (highest_power10_loop_145 fuel t p)) sum.

Definition signed_digit_score_result (x r : Z) : Prop :=
  INT_MIN < x < INT_MAX /\
  Z.abs x < 100000000 /\
  INT_MIN < r < INT_MAX /\
  r = sum_digits x.

Definition order_by_points_int_range (nums : list Z) : Prop :=
  forall i, 0 <= i < Zlength nums ->
    INT_MIN < Znth i nums 0 < INT_MAX /\
    Z.abs (Znth i nums 0) < 100000000.

Lemma signed_digit_tail_state_bounds : forall x t sum,
  signed_digit_tail_state x t sum ->
  0 <= t < 100000000 /\ -100 <= sum.
Proof.
  intros x t sum [Ht [Hsum _]].
  auto.
Qed.

Lemma signed_digit_tail_state_sum_upper : forall x t sum,
  signed_digit_tail_state x t sum ->
  sum <= 100.
Proof.
  intros x t sum [_ [_ [fuel [_ [Htail_nonneg [Htotal_bound _]]]]]].
  lia.
Qed.

Lemma first_digit_state_145_init : forall x,
  0 <= x < 100000000 ->
  first_digit_state_145 x x.
Proof.
  intros x Hx.
  unfold first_digit_state_145, first_digit_value_145.
  exists digit_fuel_145.
  repeat split; try lia.
  unfold digit_fuel_145.
  cbn.
  lia.
Qed.

Lemma highest_power10_loop_pos_145 : forall fuel t p,
  0 < p ->
  0 < highest_power10_loop_145 fuel t p.
Proof.
  induction fuel; intros t p Hp; simpl.
  - exact Hp.
  - destruct (Z.leb (p * 10) t); [apply IHfuel; lia|lia].
Qed.

Lemma highest_power10_loop_le_145 : forall fuel t p,
  1 <= p <= t ->
  highest_power10_loop_145 fuel t p <= t.
Proof.
  induction fuel; intros t p Hp; simpl.
  - lia.
  - destruct (Z.leb (p * 10) t) eqn:Hleb.
    + apply Z.leb_le in Hleb.
      apply IHfuel; lia.
    + lia.
Qed.

Lemma highest_power10_loop_final_145 : forall t,
  10 <= t < 100000000 ->
  highest_power10_loop_145 digit_fuel_145 t 1 * 10 > t.
Proof.
  intros t Ht.
  unfold digit_fuel_145.
  cbn.
  destruct (Z.leb 10 t) eqn:H10; [apply Z.leb_le in H10|apply Z.leb_gt in H10; lia].
  destruct (Z.leb 100 t) eqn:H100; [apply Z.leb_le in H100|apply Z.leb_gt in H100; lia].
  destruct (Z.leb 1000 t) eqn:H1000; [apply Z.leb_le in H1000|apply Z.leb_gt in H1000; lia].
  destruct (Z.leb 10000 t) eqn:H10000; [apply Z.leb_le in H10000|apply Z.leb_gt in H10000; lia].
  destruct (Z.leb 100000 t) eqn:H100000; [apply Z.leb_le in H100000|apply Z.leb_gt in H100000; lia].
  destruct (Z.leb 1000000 t) eqn:H1000000; [apply Z.leb_le in H1000000|apply Z.leb_gt in H1000000; lia].
  destruct (Z.leb 10000000 t) eqn:H10000000; [apply Z.leb_le in H10000000|apply Z.leb_gt in H10000000; lia].
  destruct (Z.leb 100000000 t) eqn:H100000000; [apply Z.leb_le in H100000000|apply Z.leb_gt in H100000000]; lia.
Qed.

Lemma highest_power10_loop_exit_145 : forall fuel t p,
  p * 10 > t ->
  highest_power10_loop_145 fuel t p = p.
Proof.
  induction fuel; intros t p Hexit; simpl.
  - reflexivity.
  - destruct (Z.leb (p * 10) t) eqn:Hleb.
    + apply Z.leb_le in Hleb; lia.
    + reflexivity.
Qed.

Lemma sum_digits_pos_fuel_bound_by_fuel_145 : forall fuel n,
  0 <= n ->
  sum_digits_pos_fuel fuel n <= 9 * Z.of_nat fuel.
Proof.
  induction fuel; intros n Hn; simpl.
  - lia.
  - destruct (Z_le_gt_dec n 0).
    + lia.
    + pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
      assert (Hdiv_nonneg: 0 <= n / 10) by (apply Z.div_pos; lia).
      specialize (IHfuel (n / 10) Hdiv_nonneg).
      lia.
Qed.

Lemma sum_digits_pos_fuel_nonneg_pre_145 : forall fuel n,
  0 <= n ->
  0 <= sum_digits_pos_fuel fuel n.
Proof.
  induction fuel; intros n Hn; simpl.
  - lia.
  - destruct (Z_le_gt_dec n 0).
    + lia.
    + pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
      assert (Hdiv_nonneg: 0 <= n / 10) by (apply Z.div_pos; lia).
      specialize (IHfuel (n / 10) Hdiv_nonneg).
      lia.
Qed.

Lemma signed_digit_tail_state_from_sum_digits_145 : forall x t p msd sum,
  t = Z.abs x ->
  10 <= t < 100000000 ->
  0 <= msd < 10 ->
  first_digit_state_145 (Z.abs x) msd ->
  p = highest_power10_loop_145 digit_fuel_145 t 1 ->
  sum = (if Z_ge_dec x 0 then msd else - msd) ->
  signed_digit_tail_state x (Z.rem t p) sum.
Proof.
  intros x t p msd sum Ht Hrange Hmsd Hfirst Hp Hsum.
  unfold first_digit_state_145, first_digit_value_145 in Hfirst.
  destruct Hfirst as [fuel [_ [_ Hfirst]]].
  assert (Hmsd_small: msd_fuel fuel msd = msd).
  {
    clear Hfirst.
    induction fuel; simpl.
    - rewrite Z.mod_small by lia. reflexivity.
    - destruct (Z_lt_le_dec msd 10); lia.
  }
  assert (Hmsd_value: msd = msd_fuel digit_fuel_145 t).
  {
    subst t.
    symmetry.
    rewrite Hfirst.
    exact Hmsd_small.
  }
  subst p sum.
  unfold signed_digit_tail_state.
  assert (Hposp: 0 < highest_power10_loop_145 digit_fuel_145 t 1)
    by (apply highest_power10_loop_pos_145; lia).
  assert (Hlep: highest_power10_loop_145 digit_fuel_145 t 1 <= t)
    by (apply highest_power10_loop_le_145; lia).
  assert (Hrem_mod: Z.rem t (highest_power10_loop_145 digit_fuel_145 t 1) =
                    t mod highest_power10_loop_145 digit_fuel_145 t 1).
  { apply Z.rem_mod_nonneg; lia. }
  assert (Hrem_bounds:
    0 <= Z.rem t (highest_power10_loop_145 digit_fuel_145 t 1) < 100000000).
  {
    rewrite Hrem_mod.
    pose proof (Z.mod_pos_bound t (highest_power10_loop_145 digit_fuel_145 t 1) ltac:(lia)).
    lia.
  }
  split; [exact Hrem_bounds|].
  split; [destruct (Z_ge_dec x 0); lia|].
  exists digit_fuel_145.
  split.
  - unfold digit_fuel_145.
    change (10 ^ Z.of_nat 8) with 100000000.
    exact (proj2 Hrem_bounds).
  - split.
    + apply sum_digits_pos_fuel_nonneg_pre_145.
    exact (proj1 Hrem_bounds).
    + split.
      * pose proof (sum_digits_pos_fuel_bound_by_fuel_145
      digit_fuel_145
      (Z.rem t (highest_power10_loop_145 digit_fuel_145 t 1))
      (proj1 Hrem_bounds)).
        unfold digit_fuel_145 in *.
        destruct (Z_ge_dec x 0); lia.
      * unfold sum_digits.
        rewrite <- Ht.
        rewrite Hmsd_value.
        destruct (Z.leb 10 t) eqn:Hleb; [|apply Z.leb_gt in Hleb; lia].
        rewrite Hrem_mod.
        destruct (Z_ge_dec x 0); reflexivity.
Qed.

Lemma highest_power10_state_init_nonneg : forall x t msd sum,
  t = Z.abs x ->
  10 <= t < 100000000 ->
  0 <= msd < 10 ->
  first_digit_state_145 (Z.abs x) msd ->
  0 <= x ->
  sum = msd ->
  highest_power10_state x t 1 sum.
Proof.
  intros x t msd sum Ht Hrange Hmsd Hfirst Hx Hsum.
  unfold highest_power10_state.
  repeat split; try lia.
  exists digit_fuel_145.
  split.
  - apply highest_power10_loop_final_145; assumption.
  - eapply signed_digit_tail_state_from_sum_digits_145; eauto.
    destruct (Z_ge_dec x 0); lia.
Qed.

Lemma highest_power10_state_init_neg : forall x t msd sum,
  t = Z.abs x ->
  10 <= t < 100000000 ->
  0 <= msd < 10 ->
  first_digit_state_145 (Z.abs x) msd ->
  x < 0 ->
  sum = - msd ->
  highest_power10_state x t 1 sum.
Proof.
  intros x t msd sum Ht Hrange Hmsd Hfirst Hx Hsum.
  unfold highest_power10_state.
  repeat split; try lia.
  exists digit_fuel_145.
  split.
  - apply highest_power10_loop_final_145; assumption.
  - eapply signed_digit_tail_state_from_sum_digits_145; eauto.
    destruct (Z_ge_dec x 0); lia.
Qed.

Lemma highest_power10_state_step : forall x t p sum,
  highest_power10_state x t p sum ->
  p * 10 <= t ->
  highest_power10_state x t (p * 10) sum.
Proof.
  intros x t p sum [Ht [Hrange [Hp [Hsum [fuel [Hfinal Htail]]]]]] Hstep.
  unfold highest_power10_state.
  repeat split; try lia.
  destruct fuel as [|fuel'].
  - simpl in Hfinal; lia.
  - exists fuel'.
    simpl in Hfinal, Htail.
    assert (Hleb: (p * 10 <=? t) = true) by (apply Z.leb_le; lia).
    rewrite Hleb in Hfinal, Htail.
    split; assumption.
Qed.

Lemma highest_power10_state_final : forall x t p sum,
  highest_power10_state x t p sum ->
  p * 10 > t ->
  signed_digit_tail_state x (Z.rem t p) sum.
Proof.
  intros x t p sum Hstate Hexit.
  destruct Hstate as [_ Hstate].
  destruct Hstate as [_ Hstate].
  destruct Hstate as [_ Hstate].
  destruct Hstate as [_ [fuel [_ Htail]]].
  rewrite (highest_power10_loop_exit_145 fuel t p Hexit) in Htail.
  exact Htail.
Qed.

Lemma msd_fuel_small_145 : forall fuel n,
  0 <= n < 10 ->
  msd_fuel fuel n = n.
Proof.
  induction fuel; intros n Hn; simpl.
  - rewrite Z.mod_small by lia. reflexivity.
  - destruct (Z_lt_le_dec n 10); lia.
Qed.

Lemma first_digit_value_145_small : forall n,
  0 <= n < 10 ->
  first_digit_value_145 n = n.
Proof.
  intros n Hn.
  unfold first_digit_value_145.
  apply msd_fuel_small_145; assumption.
Qed.

Lemma first_digit_state_145_step : forall original current,
  first_digit_state_145 original current ->
  10 <= current ->
  first_digit_state_145 original (current ÷ 10).
Proof.
  intros original current [fuel [Hrange [Hpow Hval]]] Hcur.
  destruct fuel as [|fuel].
  - simpl in Hpow; lia.
  - unfold first_digit_state_145.
    exists fuel.
    split.
    + rewrite Z.quot_div_nonneg by lia.
      pose proof (Z.div_pos current 10 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound current 10 current ltac:(lia) ltac:(nia)).
      lia.
    + split.
      * rewrite Z.quot_div_nonneg by lia.
        apply Z.div_lt_upper_bound; try lia.
        replace (10 ^ Z.of_nat (S fuel)) with (10 * 10 ^ Z.of_nat fuel) in Hpow
          by (rewrite Nat2Z.inj_succ; rewrite Z.pow_succ_r by lia; reflexivity).
        exact Hpow.
      * rewrite Hval.
        simpl.
        destruct (Z_lt_le_dec current 10); [lia|].
        rewrite Z.quot_div_nonneg by lia.
        reflexivity.
Qed.

Lemma first_digit_state_145_final : forall original current,
  first_digit_state_145 original current ->
  0 <= current < 10 ->
  first_digit_value_145 original = current.
Proof.
  intros original current [fuel [_ [_ Hval]]] Hcur.
  rewrite Hval.
  apply msd_fuel_small_145; assumption.
Qed.

Lemma sum_digits_pos_fuel_zero_145 : forall fuel,
  sum_digits_pos_fuel fuel 0 = 0.
Proof.
  destruct fuel; simpl; reflexivity.
Qed.

Lemma sum_digits_pos_fuel_small_145 : forall fuel n,
  fuel <> O ->
  0 < n < 10 ->
  sum_digits_pos_fuel fuel n = n.
Proof.
  destruct fuel as [|fuel]; intros n Hfuel Hn; [contradiction|].
  simpl.
  destruct (Z_le_gt_dec n 0); [lia|].
  rewrite Z.mod_small by lia.
  assert (n / 10 = 0) by (apply Z.div_small; lia).
  rewrite H.
  rewrite sum_digits_pos_fuel_zero_145.
  lia.
Qed.

Lemma sum_digits_small_nonneg_145 : forall x,
  0 <= x < 10 ->
  sum_digits x = x.
Proof.
  intros x Hx.
  unfold sum_digits.
  rewrite Z.abs_eq by lia.
  destruct (Z_ge_dec x 0); [|lia].
  destruct (Z.leb 10 x) eqn:Hleb.
  - apply Z.leb_le in Hleb; lia.
  - apply msd_fuel_small_145; lia.
Qed.

Lemma sum_digits_small_neg_145 : forall x,
  -10 < x < 0 ->
  sum_digits x = x.
Proof.
  intros x Hx.
  unfold sum_digits.
  rewrite Z.abs_neq by lia.
  destruct (Z_ge_dec x 0); [lia|].
  destruct (Z.leb 10 (- x)) eqn:Hleb.
  - apply Z.leb_le in Hleb; lia.
  - rewrite msd_fuel_small_145 by lia.
  lia.
Qed.

Lemma signed_digit_tail_state_zero : forall x sum,
  -100 <= sum <= 100 ->
  sum = sum_digits x ->
  signed_digit_tail_state x 0 sum.
Proof.
  intros x sum Hsum Hspec.
  unfold signed_digit_tail_state.
  repeat split; try lia.
  exists O.
  simpl.
  repeat split; try lia.
Qed.

Lemma sum_digits_pos_fuel_nonneg_145 : forall fuel n,
  0 <= n ->
  0 <= sum_digits_pos_fuel fuel n.
Proof.
  induction fuel; intros n Hn; simpl.
  - lia.
  - destruct (Z_le_gt_dec n 0).
    + lia.
    + pose proof (Z.mod_pos_bound n 10 ltac:(lia)).
      pose proof (IHfuel (n / 10)).
      assert (0 <= n / 10) by (apply Z.div_pos; lia).
      lia.
Qed.

Lemma signed_digit_tail_state_step : forall x t sum,
  signed_digit_tail_state x t sum ->
  t > 0 ->
  signed_digit_tail_state x (t ÷ 10) (sum + t % 10).
Proof.
  intros x t sum [Ht [Hsum [fuel [Hpow [Htail_nonneg [Htotal_bound Hrun]]]]]] Hpos.
  destruct fuel as [|fuel'].
  - simpl in Hpow; lia.
  - assert (Hrem: t % 10 = t mod 10).
    { apply Z.rem_mod_nonneg; lia. }
    assert (Hquot: t ÷ 10 = t / 10).
    { apply Z.quot_div_nonneg; lia. }
    assert (Hmod_bounds: 0 <= t mod 10 < 10).
    { apply Z.mod_pos_bound; lia. }
    assert (Hdiv_bounds: 0 <= t / 10 < 100000000).
    {
      split.
      - apply Z.div_pos; lia.
      - assert (t / 10 <= t) by (apply Z.div_le_upper_bound; lia).
        lia.
    }
    assert (Hpow_step: t / 10 < 10 ^ Z.of_nat fuel').
    {
      assert (Hcur_lt: t < 10 * 10 ^ Z.of_nat fuel').
      {
        replace (10 ^ Z.of_nat (S fuel')) with (10 * 10 ^ Z.of_nat fuel') in Hpow.
        - exact Hpow.
        - rewrite Nat2Z.inj_succ.
          rewrite Z.pow_succ_r by lia.
          lia.
      }
      apply Z.div_lt_upper_bound; nia.
    }
    simpl in Hrun.
    destruct (t <=? 0) eqn:Hleb.
    { apply Z.leb_le in Hleb; lia. }
    rewrite <- Hrem, <- Hquot in *.
    split.
    + exact Hdiv_bounds.
    + split.
      * pose proof (Z.mod_pos_bound t 10 ltac:(lia)).
        rewrite Hrem.
        lia.
      * exists fuel'.
        split; [exact Hpow_step|].
        assert (Htail_step_nonneg:
          0 <= sum_digits_pos_fuel fuel' (t ÷ 10)).
        {
          apply sum_digits_pos_fuel_nonneg_145.
          rewrite Hquot.
          apply Z.div_pos; lia.
        }
        split; [exact Htail_step_nonneg|].
        split.
        -- simpl in Htotal_bound.
           destruct (Z_le_gt_dec t 0); [lia|].
           rewrite <- Hrem, <- Hquot in Htotal_bound.
           lia.
        -- exact Hrun.
Qed.

Lemma signed_digit_tail_state_final : forall x sum,
  INT_MIN < x < INT_MAX ->
  Z.abs x < 100000000 ->
  signed_digit_tail_state x 0 sum ->
  signed_digit_score_result x sum.
Proof.
  intros x sum Hx Habs [_ [Hsum [fuel [_ [Htail_nonneg [Htotal_bound Hrun]]]]]].
  unfold signed_digit_score_result.
  destruct fuel; simpl in Hrun.
  - simpl in Htotal_bound.
    repeat split; try lia; assumption.
  - simpl in Htotal_bound.
    destruct (0 <=? 0) eqn:Hleb; [|apply Z.leb_gt in Hleb; lia].
    repeat split; try lia; assumption.
Qed.

Definition problem_145_pre_z (nums : list Z) : Prop :=
  problem_145_pre nums.

Definition problem_145_spec_z (nums output : list Z) : Prop :=
  problem_145_spec nums output.

Definition order_copy_prefix
  (i : Z) (input output scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = i /\
  Zlength scores = i /\
  output = sublist 0 i input /\
  scores = map sum_digits output.

Definition bubble_outer_prefix_145 (i : Z) (input : list Z) : list Z :=
  bubble_sort_points_fuel (Z.to_nat i) input.

Definition bubble_inner_prefix_145 (i j : Z) (input : list Z) : list Z :=
  bubble_pass_points_from (Z.to_nat (j - 1)) 0%nat (bubble_outer_prefix_145 i input).

Definition order_sort_outer_state
  (i : Z) (input output scores : list Z) : Prop :=
  0 <= i <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  output = bubble_outer_prefix_145 i input /\
  scores = map sum_digits output.

Definition order_sort_inner_state
  (i j : Z) (input output scores : list Z) : Prop :=
  0 <= i < Zlength input /\
  1 <= j <= Zlength input /\
  Zlength output = Zlength input /\
  Zlength scores = Zlength input /\
  output = bubble_inner_prefix_145 i j input /\
  scores = map sum_digits output.

Lemma Zlength_map_145 : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_145 : forall {A B : Type} (f : A -> B) (l : list A) i d d',
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

Lemma map_replace_Znth_145 : forall {A B : Type} (f : A -> B) l i x,
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

Lemma replace_Znth_length_145 : forall {A : Type} (l : list A) i x,
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

Lemma sublist_snoc_Znth_145 : forall (l : list Z) i,
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

Lemma order_copy_prefix_init : forall input,
  order_copy_prefix 0 input nil nil.
Proof.
  intros.
  unfold order_copy_prefix.
  rewrite !Zlength_nil.
  rewrite Zlength_correct.
  simpl.
  rewrite sublist_nil by lia.
  repeat split; try lia; reflexivity.
Qed.

Lemma order_copy_prefix_step : forall i input output scores x s,
  order_copy_prefix i input output scores ->
  0 <= i < Zlength input ->
  x = Znth i input 0 ->
  s = sum_digits x ->
  order_copy_prefix (i + 1) input (output ++ x :: nil) (scores ++ s :: nil).
Proof.
  intros i input output scores x s [Hi [Hout [Hscores [Houtput Hscore]]]] Hrange Hx Hs.
  subst x; subst s.
  unfold order_copy_prefix.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
  repeat split; try lia.
  - rewrite Houtput.
    rewrite sublist_snoc_Znth_145 by lia.
    reflexivity.
  - rewrite Hscore, Houtput.
    rewrite map_app.
    simpl.
    reflexivity.
Qed.

Lemma order_sort_outer_state_init : forall input output scores,
  order_copy_prefix (Zlength input) input output scores ->
  order_sort_outer_state 0 input output scores.
Proof.
  intros input output scores [Hi [Hout [Hscores [Houtput Hscore]]]].
  unfold order_sort_outer_state, bubble_outer_prefix_145.
  simpl.
  rewrite Houtput in Hscore.
  rewrite sublist_self in Hscore by lia.
  rewrite Houtput, sublist_self by lia.
  repeat split; try lia; try reflexivity; assumption.
Qed.

Lemma order_sort_inner_state_init : forall i input output scores,
  order_sort_outer_state i input output scores ->
  0 <= i < Zlength input ->
  order_sort_inner_state i 1 input output scores.
Proof.
  intros i input output scores Hstate Hi.
  unfold order_sort_outer_state, order_sort_inner_state, bubble_inner_prefix_145 in *.
  destruct Hstate as [H_i [Hout_len [Hscore_len [Houtput Hscore]]]].
  simpl.
  repeat split; try lia; assumption.
Qed.

Lemma bubble_pass_points_from_compose : forall n m start l,
  bubble_pass_points_from (n + m) start l =
  bubble_pass_points_from m (start + n)%nat
    (bubble_pass_points_from n start l).
Proof.
  induction n; intros m start l; simpl.
  - replace (start + 0)%nat with start by lia.
    reflexivity.
  - rewrite IHn.
    replace (start + S n)%nat with (S (start + n))%nat by lia.
    reflexivity.
Qed.

Lemma bubble_pass_points_from_next : forall n start l,
  bubble_pass_points_from (S n) start l =
  swap_adjacent_points (start + n)%nat
    (bubble_pass_points_from n start l).
Proof.
  intros n start l.
  replace (S n) with (n + 1)%nat by lia.
  rewrite bubble_pass_points_from_compose.
  simpl.
  reflexivity.
Qed.

Lemma bubble_sort_points_fuel_snoc : forall n l,
  bubble_sort_points_fuel (S n) l =
  bubble_pass_points (bubble_sort_points_fuel n l).
Proof.
  induction n; intros l.
  - reflexivity.
  - change (bubble_sort_points_fuel (S n) (bubble_pass_points l) =
      bubble_pass_points (bubble_sort_points_fuel (S n) l)).
    rewrite (IHn (bubble_pass_points l)).
    reflexivity.
Qed.

Lemma swap_adjacent_points_length : forall j l,
  length (swap_adjacent_points j l) = length l.
Proof.
  intros j l.
  unfold swap_adjacent_points.
  destruct (nth_error l j) as [a|] eqn:Ha;
    destruct (nth_error l (S j)) as [b|] eqn:Hb; try reflexivity.
  destruct (Z.gtb (sum_digits a) (sum_digits b)); try reflexivity.
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

Lemma bubble_pass_points_from_length : forall fuel j l,
  length (bubble_pass_points_from fuel j l) = length l.
Proof.
  induction fuel; intros j l; simpl.
  - reflexivity.
  - rewrite IHfuel.
    apply swap_adjacent_points_length.
Qed.

Lemma bubble_pass_points_length : forall l,
  length (bubble_pass_points l) = length l.
Proof.
  intros l.
  unfold bubble_pass_points.
  apply bubble_pass_points_from_length.
Qed.

Lemma bubble_sort_points_fuel_length : forall fuel l,
  length (bubble_sort_points_fuel fuel l) = length l.
Proof.
  induction fuel; intros l; simpl.
  - reflexivity.
  - rewrite IHfuel.
    apply bubble_pass_points_length.
Qed.

Lemma nth_error_Znth_145 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  nth_error l (Z.to_nat i) = Some (Znth i l d).
Proof.
  intros l i d Hi.
  unfold Znth.
  apply (@nth_error_nth' Z).
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma replace_nth_adjacent_145 : forall n (l : list Z),
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

Lemma replace_Znth_adjacent_145 : forall (l : list Z) j,
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
  apply replace_nth_adjacent_145.
  rewrite Zlength_correct in Hjlen.
  lia.
Qed.

Lemma swap_adjacent_points_keep : forall l j,
  0 <= j ->
  j + 1 < Zlength l ->
  Znth j (map sum_digits l) 0 <= Znth (j + 1) (map sum_digits l) 0 ->
  swap_adjacent_points (Z.to_nat j) l = l.
Proof.
  intros l j Hj Hjlen Hle.
  unfold swap_adjacent_points.
  rewrite (nth_error_Znth_145 l j 0) by lia.
  replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) by lia.
  rewrite (nth_error_Znth_145 l (j + 1) 0) by lia.
  rewrite (Znth_map_145 sum_digits l j 0 0) in Hle by lia.
  rewrite (Znth_map_145 sum_digits l (j + 1) 0 0) in Hle by lia.
  assert (Hgtb: (sum_digits (Znth j l 0) >? sum_digits (Znth (j + 1) l 0)) = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_ge.
    lia.
  }
  rewrite Hgtb.
  reflexivity.
Qed.

Lemma swap_adjacent_points_swap : forall l j,
  0 <= j ->
  j + 1 < Zlength l ->
  Znth j (map sum_digits l) 0 > Znth (j + 1) (map sum_digits l) 0 ->
  swap_adjacent_points (Z.to_nat j) l =
    replace_Znth j (Znth (j + 1) l 0)
      (replace_Znth (j + 1) (Znth j l 0) l).
Proof.
  intros l j Hj Hjlen Hgt.
  unfold swap_adjacent_points.
  rewrite (nth_error_Znth_145 l j 0) by lia.
  replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) by lia.
  rewrite (nth_error_Znth_145 l (j + 1) 0) by lia.
  rewrite (Znth_map_145 sum_digits l j 0 0) in Hgt by lia.
  rewrite (Znth_map_145 sum_digits l (j + 1) 0 0) in Hgt by lia.
  assert (Hgtb: (sum_digits (Znth j l 0) >? sum_digits (Znth (j + 1) l 0)) = true)
    by (apply Z.gtb_lt; lia).
  rewrite Hgtb.
  replace (S (Z.to_nat (j + 1))) with (S (S (Z.to_nat j))) by lia.
  apply replace_Znth_adjacent_145; lia.
Qed.

Lemma order_sort_inner_state_step_keep : forall i j input output scores,
  order_sort_inner_state i j input output scores ->
  1 <= j < Zlength input ->
  Znth (j - 1) scores 0 <= Znth j scores 0 ->
  order_sort_inner_state i (j + 1) input output scores.
Proof.
  intros i j input output scores Hstate Hj Hle.
  unfold order_sort_inner_state in *.
  destruct Hstate as [Hi [Hj0 [Hout_len [Hscore_len [Houtput Hscore]]]]].
  repeat split; try lia.
  - unfold bubble_inner_prefix_145 in *.
    replace (Z.to_nat (j + 1 - 1)) with (S (Z.to_nat (j - 1))) by lia.
    rewrite bubble_pass_points_from_next.
    rewrite <- Houtput.
    replace (0 + Z.to_nat (j - 1))%nat with (Z.to_nat (j - 1)) by lia.
    rewrite swap_adjacent_points_keep
      by (try lia; replace (j - 1 + 1) with j by lia; rewrite <- Hscore; exact Hle).
    reflexivity.
  - assumption.
Qed.

Lemma order_sort_inner_state_step_swap : forall i j input output scores,
  order_sort_inner_state i j input output scores ->
  1 <= j < Zlength input ->
  Znth (j - 1) scores 0 > Znth j scores 0 ->
  order_sort_inner_state i (j + 1) input
    (replace_Znth (j - 1) (Znth j output 0)
      (replace_Znth j (Znth (j - 1) output 0) output))
    (replace_Znth (j - 1) (Znth j scores 0)
      (replace_Znth j (Znth (j - 1) scores 0) scores)).
Proof.
  intros i j input output scores Hstate Hj Hgt.
  unfold order_sort_inner_state in *.
  destruct Hstate as [Hi [Hj0 [Hout_len [Hscore_len [Houtput Hscore]]]]].
  repeat split; try lia.
  - rewrite (@replace_Znth_length_145 Z
      (replace_Znth j (Znth (j - 1) output 0) output)
      (j - 1) (Znth j output 0)).
    rewrite (@replace_Znth_length_145 Z output j (Znth (j - 1) output 0)).
    exact Hout_len.
  - rewrite (@replace_Znth_length_145 Z
      (replace_Znth j (Znth (j - 1) scores 0) scores)
      (j - 1) (Znth j scores 0)).
    rewrite (@replace_Znth_length_145 Z scores j (Znth (j - 1) scores 0)).
    exact Hscore_len.
  - unfold bubble_inner_prefix_145 in *.
    replace (Z.to_nat (j + 1 - 1)) with (S (Z.to_nat (j - 1))) by lia.
    rewrite bubble_pass_points_from_next.
    rewrite <- Houtput.
    replace (0 + Z.to_nat (j - 1))%nat with (Z.to_nat (j - 1)) by lia.
    rewrite swap_adjacent_points_swap; try lia.
    + replace (j - 1 + 1) with j by lia.
      reflexivity.
    + replace (j - 1 + 1) with j by lia.
      rewrite <- Hscore.
      exact Hgt.
  - rewrite map_replace_Znth_145.
    rewrite map_replace_Znth_145.
    rewrite Hscore.
    rewrite (Znth_map_145 sum_digits output j 0 0) by lia.
    rewrite (Znth_map_145 sum_digits output (j - 1) 0 0) by lia.
    reflexivity.
Qed.

Lemma order_sort_outer_state_step : forall i input output scores,
  order_sort_inner_state i (Zlength input) input output scores ->
  0 <= i < Zlength input ->
  order_sort_outer_state (i + 1) input output scores.
Proof.
  intros i input output scores Hstate Hi.
  unfold order_sort_inner_state, order_sort_outer_state in *.
  destruct Hstate as [_ [Hj [Hout_len [Hscore_len [Houtput Hscore]]]]].
  repeat split; try lia.
  - unfold bubble_inner_prefix_145, bubble_outer_prefix_145 in *.
    replace (Z.to_nat (Zlength input - 1)) with (length input - 1)%nat in Houtput.
    + replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite bubble_sort_points_fuel_snoc.
      unfold bubble_pass_points.
      rewrite bubble_sort_points_fuel_length.
      exact Houtput.
    + rewrite Zlength_correct.
      rewrite Z2Nat.inj_sub by lia.
      rewrite Nat2Z.id.
      reflexivity.
  - assumption.
Qed.

Lemma order_sort_outer_state_final_spec : forall input output scores,
  order_sort_outer_state (Zlength input) input output scores ->
  problem_145_spec_z input output.
Proof.
  intros input output scores Hstate.
  unfold order_sort_outer_state in Hstate.
  destruct Hstate as [_ [_ [_ [Houtput _]]]].
  unfold problem_145_spec_z, problem_145_spec, order_by_points_impl.
  rewrite Houtput.
  unfold bubble_outer_prefix_145, bubble_sort_points.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma signed_digit_score_result_intro : forall x r,
  INT_MIN < x < INT_MAX ->
  Z.abs x < 100000000 ->
  INT_MIN < r < INT_MAX ->
  r = sum_digits x ->
  signed_digit_score_result x r.
Proof.
  unfold signed_digit_score_result; auto.
Qed.

Lemma order_by_points_int_range_at : forall nums i,
  order_by_points_int_range nums ->
  0 <= i < Zlength nums ->
  INT_MIN < Znth i nums 0 < INT_MAX /\
  Z.abs (Znth i nums 0) < 100000000.
Proof.
  intros; apply H; assumption.
Qed.
