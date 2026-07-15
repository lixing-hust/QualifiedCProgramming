Load "../spec/73".

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Logic.LogicGenerator.demo932.Interface.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_73_pre_z (arr : list Z) : Prop :=
  problem_73_pre arr.

Definition problem_73_spec_z (arr : list Z) (out : Z) : Prop :=
  problem_73_spec arr out.

Definition half_73 (arr : list Z) : Z :=
  Z.of_nat (length arr / 2)%nat.

Definition mismatch_at_73 (arr : list Z) (i : Z) : Z :=
  if Z.eqb (Znth i arr 0) (Znth (Zlength arr - 1 - i) arr 0)
  then 0
  else 1.

Definition INT_MIN_73 : Z := -2147483648.

Definition pair_indices_73 (i : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat i)).

Definition count_half_mismatches_upto (i : Z) (arr : list Z) : Z :=
  fold_left Z.add (map (mismatch_at_73 arr) (pair_indices_73 i)) 0.

Definition smallest_change_int_range (arr : list Z) : Prop :=
  Forall (fun x => INT_MIN_73 <= x <= INT_MAX) arr /\
  half_73 arr + 1 <= INT_MAX.

Lemma fold_left_Zadd_acc_73 : forall l acc,
  fold_left Z.add l acc = acc + fold_left Z.add l 0.
Proof.
  induction l as [| x xs IH]; intros acc.
  - cbn. lia.
  - cbn. rewrite IH. rewrite (IH x). lia.
Qed.

Lemma pair_indices_73_snoc : forall i,
  0 <= i ->
  pair_indices_73 (i + 1) = pair_indices_73 i ++ [i].
Proof.
  intros i Hi.
  unfold pair_indices_73.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_S.
  rewrite map_app.
  cbn.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma count_half_mismatches_upto_0 : forall arr,
  count_half_mismatches_upto 0 arr = 0.
Proof.
  intros arr; reflexivity.
Qed.

Lemma count_half_mismatches_upto_step : forall arr i,
  0 <= i ->
  count_half_mismatches_upto (i + 1) arr =
  count_half_mismatches_upto i arr + mismatch_at_73 arr i.
Proof.
  intros arr i Hi.
  unfold count_half_mismatches_upto.
  rewrite pair_indices_73_snoc by lia.
  rewrite map_app.
  rewrite fold_left_app.
  cbn [map fold_left].
  rewrite fold_left_Zadd_acc_73.
  lia.
Qed.

Lemma count_half_mismatches_upto_step_eq : forall arr i,
  0 <= i ->
  Znth i arr 0 = Znth (Zlength arr - 1 - i) arr 0 ->
  count_half_mismatches_upto (i + 1) arr =
    count_half_mismatches_upto i arr.
Proof.
  intros arr i Hi Heq.
  rewrite count_half_mismatches_upto_step by lia.
  unfold mismatch_at_73.
  rewrite Heq, Z.eqb_refl.
  lia.
Qed.

Lemma count_half_mismatches_upto_step_neq : forall arr i,
  0 <= i ->
  Znth i arr 0 <> Znth (Zlength arr - 1 - i) arr 0 ->
  count_half_mismatches_upto (i + 1) arr =
    count_half_mismatches_upto i arr + 1.
Proof.
  intros arr i Hi Hneq.
  rewrite count_half_mismatches_upto_step by lia.
  unfold mismatch_at_73.
  destruct (Z.eqb (Znth i arr 0) (Znth (Zlength arr - 1 - i) arr 0)) eqn:Heq.
  - apply Z.eqb_eq in Heq; contradiction.
  - lia.
Qed.

Lemma mismatch_at_73_bounds : forall arr i,
  0 <= mismatch_at_73 arr i <= 1.
Proof.
  intros arr i.
  unfold mismatch_at_73.
  destruct (Z.eqb _ _); lia.
Qed.

Lemma count_half_mismatches_upto_bounds : forall arr i,
  0 <= i ->
  0 <= count_half_mismatches_upto i arr <= i.
Proof.
  intros arr i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  induction (Z.to_nat i) as [| n IH].
  - cbn. lia.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite count_half_mismatches_upto_step by lia.
    pose proof (mismatch_at_73_bounds arr (Z.of_nat n)).
    lia.
Qed.

Lemma smallest_change_int_range_current : forall arr i,
  smallest_change_int_range arr ->
  0 <= i ->
  i <= half_73 arr ->
  INT_MIN_73 <= count_half_mismatches_upto i arr <= INT_MAX /\
  INT_MIN_73 <= count_half_mismatches_upto i arr + 1 <= INT_MAX.
Proof.
  intros arr i [_ Hhalf] Hi Hle.
  pose proof (count_half_mismatches_upto_bounds arr i Hi).
  unfold INT_MIN_73 in *.
  lia.
Qed.

Lemma loop_index_le_half_73 : forall arr i,
  0 <= i ->
  2 * i <= Zlength arr ->
  i <= half_73 arr.
Proof.
  intros arr i Hi Hle.
  unfold half_73.
  rewrite Nat2Z.inj_div.
  change (Z.of_nat 2) with 2.
  rewrite <- Zlength_correct.
  apply Z.div_le_lower_bound; lia.
Qed.

Lemma length_firstn_half_73 : forall arr : list Z,
  length (firstn (length arr / 2) arr) = (length arr / 2)%nat.
Proof.
  intros arr.
  rewrite firstn_length.
  apply Nat.min_l.
  apply Nat.div_le_upper_bound; lia.
Qed.

Lemma count_diff_acc_shift_73 : forall (l1 l2 : list Z) acc,
  count_diff l1 l2 acc = acc + count_diff l1 l2 0.
Proof.
  intros l1 l2 acc.
  unfold count_diff.
  lia.
Qed.

Lemma count_diff_snoc_73 : forall (l1 l2 : list Z) a b,
  length l1 = length l2 ->
  count_diff (l1 ++ [a]) (l2 ++ [b]) 0 =
  count_diff l1 l2 0 + (if Z.eqb a b then 0 else 1).
Proof.
  intros l1 l2 a b Hlen.
  unfold count_diff.
  rewrite combine_app by exact Hlen.
  rewrite filter_app, app_length.
  cbn [combine filter length fst snd].
  destruct (Z.eqb a b); rewrite Nat2Z.inj_add; cbn; lia.
Qed.

Lemma firstn_succ_snoc_73 : forall {A : Type} n (l : list A) d,
  (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n as [| n IH]; intros l d Hn.
  - destruct l; cbn in *; try lia; reflexivity.
  - destruct l; cbn in *; try lia.
    rewrite (IH l d) by lia.
    reflexivity.
Qed.

Lemma rev_skipn_succ_snoc_73 : forall n (l : list Z) d,
  (n < length l)%nat ->
  rev (skipn (length l - S n) l) =
  rev (skipn (length l - n) l) ++ [nth (length l - S n) l d].
Proof.
  intros n l d Hn.
  rewrite <- (firstn_rev (S n) l).
  rewrite <- (firstn_rev n l).
  rewrite firstn_succ_snoc_73 with (d := d) by (rewrite length_rev; lia).
  rewrite rev_nth by lia.
  reflexivity.
Qed.

Lemma count_half_mismatches_upto_nat_spec_73 : forall n arr,
  (n <= length arr)%nat ->
  count_half_mismatches_upto (Z.of_nat n) arr =
  count_diff (firstn n arr) (rev (skipn (length arr - n) arr)) 0.
Proof.
  induction n as [| n IH]; intros arr Hn.
  - reflexivity.
  - assert (Hnlt : (n < length arr)%nat) by lia.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite count_half_mismatches_upto_step by lia.
    rewrite IH by lia.
    rewrite firstn_succ_snoc_73 with (d := 0) by exact Hnlt.
    rewrite rev_skipn_succ_snoc_73 with (d := 0) by exact Hnlt.
    rewrite count_diff_snoc_73.
    + unfold mismatch_at_73.
      unfold Znth.
      rewrite Nat2Z.id.
      replace (Z.to_nat (Zlength arr - 1 - Z.of_nat n))
        with (length arr - S n)%nat by (rewrite Zlength_correct; lia).
      reflexivity.
    + rewrite length_firstn.
      rewrite length_rev, length_skipn.
      lia.
Qed.

Lemma loop_exit_half_73 : forall arr i,
  0 <= i ->
  2 * i <= Zlength arr ->
  i >= Zlength arr - 1 - i ->
  i = half_73 arr.
Proof.
  intros arr i Hi Hlow Hhigh.
  unfold half_73.
  assert (Hnat : Z.to_nat i = (length arr / 2)%nat).
  {
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_div.
    change (Z.of_nat 2) with 2.
    rewrite <- Zlength_correct.
    apply Z.div_unique with (r := Zlength arr - 2 * i).
    - left; lia.
    - lia.
  }
  rewrite <- Hnat.
  lia.
Qed.

Lemma problem_73_spec_z_of_exit : forall arr i out,
  0 <= i ->
  2 * i <= Zlength arr ->
  i >= Zlength arr - 1 - i ->
  out = count_half_mismatches_upto i arr ->
  problem_73_spec_z arr out.
Proof.
  intros arr i out Hi Hbound Hexit Hout.
  unfold problem_73_spec_z, problem_73_spec.
  subst out.
  unfold smallest_change_impl, half_73 in *.
  pose proof (loop_exit_half_73 arr i Hi Hbound Hexit) as Hidx.
  rewrite Hidx.
  apply count_half_mismatches_upto_nat_spec_73.
  apply Nat.div_le_upper_bound; lia.
Qed.
