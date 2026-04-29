Load "../spec/107".

From AUXLib Require Import List_lemma ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.
Open Scope Z_scope.

Definition problem_107_pre_z (n : Z) : Prop :=
  problem_107_pre n.

Definition problem_107_spec_z (n : Z) (output : list Z) : Prop :=
  problem_107_spec n output.

Definition is_pal_z (x : Z) : Z :=
  if is_palindrome_z x then 1 else 0.

Definition pal_reverse_loop_state (x t r : Z) : Prop :=
  1 <= x <= 1000 /\
  exists fuel : nat,
    0 <= t <= x /\
    ((fuel = 4%nat /\ r = 0) \/
     (fuel = 3%nat /\ 0 <= r <= 9) \/
     (fuel = 2%nat /\ 0 <= r <= 99) \/
     (fuel = 1%nat /\ 0 <= r <= 999) \/
     (fuel = 0%nat /\ 0 <= r <= 9999)) /\
    t < 10 ^ Z.of_nat fuel /\
    reverse_digits_loop fuel t r = reverse_digits_loop 4 x 0.

Definition pal_count_prefix (k n even_count odd_count : Z) : Prop :=
  0 <= k <= n /\
  even_count = count_even_pal_upto k /\
  odd_count = count_odd_pal_upto k.

Lemma pal_reverse_loop_state_init : forall x,
  1 <= x <= 1000 ->
  pal_reverse_loop_state x x 0.
Proof.
  intros.
  unfold pal_reverse_loop_state.
  split.
  - lia.
  - exists 4%nat.
    repeat split; try lia.
Qed.

Lemma pal_reverse_loop_state_step : forall x t r,
  pal_reverse_loop_state x t r ->
  t > 0 ->
  pal_reverse_loop_state x (t / 10) (r * 10 + t mod 10).
Proof.
  intros x t r Hstate Ht.
  unfold pal_reverse_loop_state in *.
  destruct Hstate as [Hx [fuel [Ht_bounds [Hr_bounds [Hpow Heq]]]]].
  destruct fuel.
  {
    simpl in Hpow.
    lia.
  }
  simpl in Heq.
  assert ((t >? 0) = true) as Hgt by (apply Z.gtb_lt; lia).
  rewrite Hgt in Heq.
  split.
  - lia.
  - exists fuel.
    split.
    + split.
      * apply Z.div_pos; lia.
      * assert (t / 10 <= t) by (apply Z.div_le_upper_bound; lia).
        lia.
    + split.
      * destruct Hr_bounds as [[Hfuel Hr] | [[Hfuel Hr] | [[Hfuel Hr] | [[Hfuel Hr] | [Hfuel Hr]]]]];
          inversion Hfuel; subst; simpl in Hpow; try lia;
          assert (0 <= t mod 10 < 10) by (apply Z.mod_pos_bound; lia);
          try (left; split; lia);
          try (right; left; split; nia);
          try (right; right; left; split; nia);
          try (right; right; right; left; split; nia);
          try (right; right; right; right; split; nia).
      * split.
        -- assert (Hcur_lt: t < 10 * 10 ^ Z.of_nat fuel).
        {
          replace (10 ^ Z.of_nat (S fuel)) with (10 * 10 ^ Z.of_nat fuel) in Hpow.
          exact Hpow.
          rewrite Nat2Z.inj_succ.
          rewrite Z.pow_succ_r by lia.
          lia.
        }
           apply Z.div_lt_upper_bound.
           ++ lia.
           ++ nia.
        -- exact Heq.
Qed.

Lemma pal_reverse_loop_state_final : forall x r,
  pal_reverse_loop_state x 0 r ->
  r = reverse_digits_loop 4 x 0.
Proof.
  intros x r Hstate.
  unfold pal_reverse_loop_state in Hstate.
  destruct Hstate as [_ [fuel [[Ht_nonneg Ht_upper] [_ [_ Heq]]]]].
  destruct fuel.
  - simpl in Heq. exact Heq.
  - simpl in Heq.
    exact Heq.
Qed.

Lemma is_pal_z_correct_true : forall x,
  1 <= x <= 1000 ->
  reverse_digits_loop 4 x 0 = x ->
  is_pal_z x = 1.
Proof.
  intros.
  unfold is_pal_z, is_palindrome_z.
  assert ((x <=? 0) = false) by (apply Z.leb_gt; lia).
  rewrite H1.
  assert ((reverse_digits_loop 4 x 0 =? x) = true) by (apply Z.eqb_eq; lia).
  rewrite H2.
  reflexivity.
Qed.

Lemma is_pal_z_correct_false : forall x,
  1 <= x <= 1000 ->
  reverse_digits_loop 4 x 0 <> x ->
  is_pal_z x = 0.
Proof.
  intros.
  unfold is_pal_z, is_palindrome_z.
  assert ((x <=? 0) = false) by (apply Z.leb_gt; lia).
  rewrite H1.
  assert ((reverse_digits_loop 4 x 0 =? x) = false) by (apply Z.eqb_neq; lia).
  rewrite H2.
  reflexivity.
Qed.

Lemma count_even_pal_upto_step : forall k,
  0 <= k ->
  count_even_pal_upto (k + 1) =
    count_even_pal_upto k +
    (if andb (is_palindrome_z (k + 1)) (is_even_z (k + 1)) then 1 else 0).
Proof.
  intros.
  unfold count_even_pal_upto.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  simpl.
  change (Z.pos (Pos.of_succ_nat (Z.to_nat k))) with (Z.of_nat (S (Z.to_nat k))).
  replace (Z.of_nat (S (Z.to_nat k))) with (k + 1) by lia.
  reflexivity.
Qed.

Lemma count_odd_pal_upto_step : forall k,
  0 <= k ->
  count_odd_pal_upto (k + 1) =
    count_odd_pal_upto k +
    (if andb (is_palindrome_z (k + 1)) (negb (is_even_z (k + 1))) then 1 else 0).
Proof.
  intros.
  unfold count_odd_pal_upto.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  simpl.
  change (Z.pos (Pos.of_succ_nat (Z.to_nat k))) with (Z.of_nat (S (Z.to_nat k))).
  replace (Z.of_nat (S (Z.to_nat k))) with (k + 1) by lia.
  reflexivity.
Qed.

Lemma pal_count_prefix_init : forall n,
  1 <= n <= 1000 ->
  pal_count_prefix 0 n 0 0.
Proof.
  intros.
  unfold pal_count_prefix, count_even_pal_upto, count_odd_pal_upto.
  simpl.
  lia.
Qed.

Lemma pal_count_prefix_step_odd_hit : forall k n even_count odd_count,
  pal_count_prefix k n even_count odd_count ->
  0 <= k < n ->
  is_pal_z (k + 1) <> 0 ->
  (k + 1) mod 2 = 1 ->
  pal_count_prefix (k + 1) n even_count (odd_count + 1).
Proof.
  intros.
  unfold pal_count_prefix in *.
  destruct H as [Hbounds [Heven Hodd]].
  subst even_count odd_count.
  repeat split; try lia.
  - rewrite count_even_pal_upto_step by lia.
    assert (Hpal: is_palindrome_z (k + 1) = true).
    { unfold is_pal_z in H1. destruct (is_palindrome_z (k + 1)); lia. }
    assert (Hevenb: is_even_z (k + 1) = false).
    { unfold is_even_z. apply Z.eqb_neq. lia. }
    rewrite Hpal, Hevenb. simpl. lia.
  - rewrite count_odd_pal_upto_step by lia.
    assert (Hpal: is_palindrome_z (k + 1) = true).
    { unfold is_pal_z in H1. destruct (is_palindrome_z (k + 1)); lia. }
    assert (Hevenb: is_even_z (k + 1) = false).
    { unfold is_even_z. apply Z.eqb_neq. lia. }
    rewrite Hpal, Hevenb. simpl. lia.
Qed.

Lemma pal_count_prefix_step_even_hit : forall k n even_count odd_count,
  pal_count_prefix k n even_count odd_count ->
  0 <= k < n ->
  is_pal_z (k + 1) <> 0 ->
  (k + 1) mod 2 = 0 ->
  pal_count_prefix (k + 1) n (even_count + 1) odd_count.
Proof.
  intros.
  unfold pal_count_prefix in *.
  destruct H as [Hbounds [Heven Hodd]].
  subst even_count odd_count.
  repeat split; try lia.
  - rewrite count_even_pal_upto_step by lia.
    assert (Hpal: is_palindrome_z (k + 1) = true).
    { unfold is_pal_z in H1. destruct (is_palindrome_z (k + 1)); lia. }
    assert (Hevenb: is_even_z (k + 1) = true).
    { unfold is_even_z. apply Z.eqb_eq. lia. }
    rewrite Hpal, Hevenb. simpl. lia.
  - rewrite count_odd_pal_upto_step by lia.
    assert (Hpal: is_palindrome_z (k + 1) = true).
    { unfold is_pal_z in H1. destruct (is_palindrome_z (k + 1)); lia. }
    assert (Hevenb: is_even_z (k + 1) = true).
    { unfold is_even_z. apply Z.eqb_eq. lia. }
    rewrite Hpal, Hevenb. simpl. lia.
Qed.

Lemma pal_count_prefix_step_miss : forall k n even_count odd_count,
  pal_count_prefix k n even_count odd_count ->
  0 <= k < n ->
  is_pal_z (k + 1) = 0 ->
  pal_count_prefix (k + 1) n even_count odd_count.
Proof.
  intros.
  unfold pal_count_prefix in *.
  destruct H as [Hbounds [Heven Hodd]].
  subst even_count odd_count.
  repeat split; try lia.
  - rewrite count_even_pal_upto_step by lia.
    assert (Hpal: is_palindrome_z (k + 1) = false).
    { unfold is_pal_z in H1. destruct (is_palindrome_z (k + 1)); lia. }
    rewrite Hpal. simpl. lia.
  - rewrite count_odd_pal_upto_step by lia.
    assert (Hpal: is_palindrome_z (k + 1) = false).
    { unfold is_pal_z in H1. destruct (is_palindrome_z (k + 1)); lia. }
    rewrite Hpal. simpl. lia.
Qed.

Lemma count_even_pal_upto_nat_bounds : forall k,
  0 <= count_even_pal_upto_nat k <= Z.of_nat k.
Proof.
  induction k; simpl.
  - lia.
  - change (Z.pos (Pos.of_succ_nat k)) with (Z.of_nat (S k)).
    rewrite Nat2Z.inj_succ.
    destruct (is_palindrome_z (Z.succ (Z.of_nat k)) &&
      is_even_z (Z.succ (Z.of_nat k))); lia.
Qed.

Lemma count_odd_pal_upto_nat_bounds : forall k,
  0 <= count_odd_pal_upto_nat k <= Z.of_nat k.
Proof.
  induction k; simpl.
  - lia.
  - change (Z.pos (Pos.of_succ_nat k)) with (Z.of_nat (S k)).
    rewrite Nat2Z.inj_succ.
    destruct (is_palindrome_z (Z.succ (Z.of_nat k)) &&
      negb (is_even_z (Z.succ (Z.of_nat k)))); lia.
Qed.

Lemma count_even_pal_upto_bounds : forall k,
  0 <= k ->
  0 <= count_even_pal_upto k <= k.
Proof.
  intros.
  unfold count_even_pal_upto.
  pose proof (count_even_pal_upto_nat_bounds (Z.to_nat k)).
  rewrite Z2Nat.id in H0 by lia.
  exact H0.
Qed.

Lemma count_odd_pal_upto_bounds : forall k,
  0 <= k ->
  0 <= count_odd_pal_upto k <= k.
Proof.
  intros.
  unfold count_odd_pal_upto.
  pose proof (count_odd_pal_upto_nat_bounds (Z.to_nat k)).
  rewrite Z2Nat.id in H0 by lia.
  exact H0.
Qed.

Lemma pal_count_prefix_bounds : forall k n even_count odd_count,
  pal_count_prefix k n even_count odd_count ->
  0 <= even_count <= k /\ 0 <= odd_count <= k.
Proof.
  intros.
  unfold pal_count_prefix in H.
  destruct H as [Hbounds [Heven Hodd]].
  subst.
  split.
  - apply count_even_pal_upto_bounds; lia.
  - apply count_odd_pal_upto_bounds; lia.
Qed.

Lemma problem_107_spec_z_of_prefix : forall n even_count odd_count,
  pal_count_prefix n n even_count odd_count ->
  problem_107_spec_z n [even_count; odd_count].
Proof.
  intros.
  unfold pal_count_prefix, problem_107_spec_z, problem_107_spec in *.
  destruct H as [_ [Heven Hodd]].
  subst.
  reflexivity.
Qed.
