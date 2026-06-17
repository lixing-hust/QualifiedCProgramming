Load "../spec/115".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Fixpoint sum_z (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_z xs
  end.

Definition nat_row_of_z (row : list Z) : list nat :=
  map Z.to_nat row.

Definition nat_grid_of_z (rows : list (list Z)) : list (list nat) :=
  map nat_row_of_z rows.

Definition problem_115_pre_z (rows : list (list Z)) (capacity : Z) : Prop :=
  problem_115_pre (nat_grid_of_z rows) (Z.to_nat capacity).

Definition problem_115_spec_z (rows : list (list Z)) (capacity ret : Z) : Prop :=
  problem_115_spec (nat_grid_of_z rows) (Z.to_nat capacity) (Z.to_nat ret).

Definition row_sum_prefix_z (row : list Z) (j : Z) : Z :=
  sum_z (firstn (Z.to_nat j) row).

Definition row_trip_z (row : list Z) (capacity : Z) : Z :=
  let s := sum_z row in
  if s =? 0 then 0 else Z.quot (s - 1) capacity + 1.

Definition trips_prefix_z (rows : list (list Z)) (i capacity : Z) : Z :=
  fold_left Z.add
    (map (fun row => row_trip_z row capacity) (firstn (Z.to_nat i) rows))
    0.

Lemma row_sum_prefix_z_0 : forall row,
  row_sum_prefix_z row 0 = 0.
Proof.
  intros row. unfold row_sum_prefix_z. reflexivity.
Qed.

Lemma sum_z_app : forall a b,
  sum_z (a ++ b) = sum_z a + sum_z b.
Proof.
  induction a as [| x xs IH]; intros b; simpl; [lia | rewrite IH; lia].
Qed.

Lemma firstn_succ_snoc_115 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n as [| n IH]; intros l d Hn.
  - destruct l; simpl in *; try lia. reflexivity.
  - destruct l; simpl in *; try lia.
    rewrite (IH l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_115 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ [Znth i l d].
Proof.
  intros A l i d Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_115 with (d := d) by (rewrite Zlength_correct in Hi; lia).
  reflexivity.
Qed.

Lemma row_sum_prefix_z_step : forall row j,
  0 <= j < Zlength row ->
  row_sum_prefix_z row (j + 1) =
  row_sum_prefix_z row j + Znth j row 0.
Proof.
  intros row j Hj.
  unfold row_sum_prefix_z.
  rewrite (firstn_succ_Znth_115 row j 0) by lia.
  rewrite sum_z_app. simpl. lia.
Qed.

Lemma row_sum_prefix_z_full : forall row n,
  Zlength row = n ->
  row_sum_prefix_z row n = sum_z row.
Proof.
  intros row n Hn.
  unfold row_sum_prefix_z.
  assert (Z.to_nat n = length row).
  { rewrite Zlength_correct in Hn. lia. }
  rewrite H.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma row_sum_prefix_z_nonneg_bound : forall row j n,
  0 <= j <= n ->
  Zlength row = n ->
  (forall c, 0 <= c < n -> 0 <= Znth c row 0 <= 1) ->
  0 <= row_sum_prefix_z row j <= j.
Proof.
  intros row j n Hj Hlen Hcell.
  assert (Hj' : j <= Zlength row) by lia.
  unfold row_sum_prefix_z.
  remember (Z.to_nat j) as k eqn:Hk.
  assert (Z.of_nat k = j) by (subst k; rewrite Z2Nat.id; lia).
  clear Hk; subst j.
  clear Hj.
  revert row n Hlen Hcell Hj'.
  induction k as [| k IH]; intros row n Hlen Hcell Hj'; simpl.
  - lia.
  - destruct row as [| x xs].
    + rewrite Zlength_correct in Hj'. simpl in Hj'. lia.
    + simpl.
      assert (Hx : 0 <= x <= 1).
      { specialize (Hcell 0). simpl in Hcell. apply Hcell.
        rewrite <- Hlen. rewrite Zlength_correct. simpl. lia. }
      assert (Hxs_len : Zlength xs = n - 1).
      { rewrite Zlength_correct in *. simpl in Hlen. lia. }
      assert (Hxs_cell : forall c : Z, 0 <= c < n - 1 -> 0 <= Znth c xs 0 <= 1).
      { intros c Hc.
        specialize (Hcell (c + 1)).
        simpl in Hcell.
        rewrite Znth_cons in Hcell by lia.
        replace (c + 1 - 1) with c in Hcell by lia.
        apply Hcell. lia. }
      assert (Hk_bound : Z.of_nat k <= n - 1).
      { simpl in Hj'. lia. }
      specialize (IH xs (n - 1) Hxs_len Hxs_cell ltac:(rewrite Hxs_len; exact Hk_bound)).
      lia.
Qed.

Lemma fold_left_Zadd_app : forall l x,
  fold_left Z.add l x = x + fold_left Z.add l 0.
Proof.
  induction l as [| a l IH]; intros x; simpl.
  - lia.
  - rewrite IH. rewrite (IH a). lia.
Qed.

Lemma trips_prefix_z_0 : forall rows capacity,
  trips_prefix_z rows 0 capacity = 0.
Proof.
  intros rows capacity. unfold trips_prefix_z. reflexivity.
Qed.

Lemma trips_prefix_z_step : forall rows i capacity,
  0 <= i < Zlength rows ->
  trips_prefix_z rows (i + 1) capacity =
  trips_prefix_z rows i capacity + row_trip_z (Znth i rows nil) capacity.
Proof.
  intros rows i capacity Hi.
  unfold trips_prefix_z.
  rewrite (firstn_succ_Znth_115 rows i nil) by lia.
  rewrite map_app. simpl.
  rewrite fold_left_app. simpl.
  rewrite fold_left_Zadd_app. lia.
Qed.

Lemma row_trip_z_of_sum_prefix : forall row n capacity sum,
  Zlength row = n ->
  sum = row_sum_prefix_z row n ->
  row_trip_z row capacity =
  if sum =? 0 then 0 else Z.quot (sum - 1) capacity + 1.
Proof.
  intros row n capacity sum Hlen Hsum.
  unfold row_trip_z.
  rewrite <- (row_sum_prefix_z_full row n Hlen).
  subst sum. reflexivity.
Qed.

Lemma trips_prefix_z_step_from_sum : forall rows i n capacity sum,
  0 <= i < Zlength rows ->
  Zlength (Znth i rows nil) = n ->
  sum = row_sum_prefix_z (Znth i rows nil) n ->
  trips_prefix_z rows (i + 1) capacity =
  trips_prefix_z rows i capacity +
  (if sum =? 0 then 0 else Z.quot (sum - 1) capacity + 1).
Proof.
  intros rows i n capacity sum Hi Hlen Hsum.
  rewrite trips_prefix_z_step by lia.
  rewrite (row_trip_z_of_sum_prefix _ n _ sum Hlen Hsum).
  reflexivity.
Qed.

Lemma row_trip_z_nonneg_bound : forall row n capacity,
  1 <= capacity ->
  0 <= n ->
  Zlength row = n ->
  0 <= row_sum_prefix_z row n ->
  row_sum_prefix_z row n <= n ->
  0 <= row_trip_z row capacity <= n.
Proof.
  intros row n capacity Hcap Hn Hlen Hsum_nonneg Hsum_bound.
  unfold row_trip_z.
  destruct (sum_z row =? 0) eqn:Hzero.
  - lia.
  - apply Z.eqb_neq in Hzero.
    rewrite <- (row_sum_prefix_z_full row n Hlen) in Hzero.
    rewrite <- (row_sum_prefix_z_full row n Hlen).
    assert (0 < row_sum_prefix_z row n) by lia.
    assert (0 <= Z.quot (row_sum_prefix_z row n - 1) capacity <= row_sum_prefix_z row n - 1).
    { split.
      - apply Z.quot_pos; lia.
      - apply Z.quot_le_upper_bound; nia. }
    lia.
Qed.

Lemma trips_prefix_z_nonneg_bound_step : forall i n capacity out sum,
  0 <= i ->
  1 <= capacity ->
  0 <= n ->
  0 <= out <= i * n ->
  0 <= sum <= n ->
  0 <= out + (if sum =? 0 then 0 else Z.quot (sum - 1) capacity + 1) <= (i + 1) * n.
Proof.
  intros i n capacity out sum Hi Hcap Hn Hout Hsum.
  destruct (sum =? 0) eqn:Hzero.
  - lia.
  - apply Z.eqb_neq in Hzero.
    assert (0 < sum) by lia.
    assert (0 <= Z.quot (sum - 1) capacity <= sum - 1).
    { split.
      - apply Z.quot_pos; lia.
      - apply Z.quot_le_upper_bound; nia. }
    nia.
Qed.

Lemma fold_left_nat_add_start : forall l x,
  fold_left Nat.add l x = (x + fold_left Nat.add l 0)%nat.
Proof.
  induction l as [| a l IH]; intros x; simpl.
  - lia.
  - rewrite IH. rewrite (IH a). lia.
Qed.

Lemma sum_z_nat_row_of_z : forall row,
  (forall c, 0 <= c < Zlength row -> 0 <= Znth c row 0) ->
  Z.of_nat (fold_left Nat.add (nat_row_of_z row) 0%nat) = sum_z row.
Proof.
  induction row as [| x xs IH]; intros Hnonneg; simpl.
  - reflexivity.
  - assert (Hx : 0 <= x).
    { specialize (Hnonneg 0). simpl in Hnonneg. apply Hnonneg.
      rewrite Zlength_correct. simpl. lia. }
    assert (Hxs : forall c : Z, 0 <= c < Zlength xs -> 0 <= Znth c xs 0).
    { intros c Hc.
      specialize (Hnonneg (c + 1)).
      simpl in Hnonneg.
      rewrite Znth_cons in Hnonneg by lia.
      replace (c + 1 - 1) with c in Hnonneg by lia.
      apply Hnonneg. rewrite Zlength_correct in *. simpl in *. lia. }
    rewrite <- IH by exact Hxs.
    rewrite fold_left_nat_add_start.
    rewrite Nat2Z.inj_add.
    rewrite Z2Nat.id by lia.
    lia.
Qed.

Lemma nat_div_trip_bridge : forall s cap,
  0 <= s ->
  1 <= cap ->
  Z.of_nat ((Z.to_nat s + Z.to_nat cap - 1) / Z.to_nat cap)%nat =
  (if s =? 0 then 0 else Z.quot (s - 1) cap + 1).
Proof.
  intros s cap Hs Hcap.
  destruct (s =? 0) eqn:Hs0.
  - apply Z.eqb_eq in Hs0. subst s. simpl. rewrite Nat.div_small; lia.
  - apply Z.eqb_neq in Hs0.
    assert (Hspos : 0 < s) by lia.
    rewrite Nat2Z.inj_div by lia.
    rewrite Nat2Z.inj_sub by lia.
    rewrite Nat2Z.inj_add.
    rewrite !Z2Nat.id by lia.
    rewrite Z.quot_div_nonneg by lia.
    change (Z.of_nat 1) with 1.
    replace (cap + s - 1) with (s + cap - 1) by lia.
    replace ((s + cap - 1) / cap) with (1 + (s - 1) / cap).
    + rewrite Z.add_comm. reflexivity.
    + replace (s + cap - 1) with (1 * cap + (s - 1)) by lia.
      symmetry. apply Z.div_add_l. lia.
Qed.

Lemma row_trip_z_nat_bridge : forall row capacity,
  1 <= capacity ->
  (forall c, 0 <= c < Zlength row -> 0 <= Znth c row 0) ->
  Z.of_nat ((count_water (nat_row_of_z row) + Z.to_nat capacity - 1) / Z.to_nat capacity)%nat =
  row_trip_z row capacity.
Proof.
  intros row capacity Hcap Hnonneg.
  assert (Hsum : Z.of_nat (count_water (nat_row_of_z row)) = sum_z row).
  { unfold count_water. apply sum_z_nat_row_of_z. exact Hnonneg. }
  assert (Hsum_nonneg : 0 <= sum_z row) by lia.
  replace (count_water (nat_row_of_z row)) with (Z.to_nat (sum_z row)).
  2:{ apply Nat2Z.inj.
      rewrite Hsum. rewrite Z2Nat.id by lia. reflexivity. }
  unfold row_trip_z.
  rewrite nat_div_trip_bridge; try lia.
Qed.

Lemma required_trips_bridge_acc : forall rows capacity acc_nat acc_z,
  1 <= capacity ->
  Z.of_nat acc_nat = acc_z ->
  (forall r c, 0 <= r < Zlength rows -> 0 <= c < Zlength (Znth r rows nil) -> 0 <= Znth c (Znth r rows nil) 0) ->
  Z.of_nat
    (fold_left
      (fun acc well => (acc + (count_water well + Z.to_nat capacity - 1) / Z.to_nat capacity)%nat)
      (nat_grid_of_z rows)
      acc_nat) =
  fold_left Z.add (map (fun row => row_trip_z row capacity) rows) acc_z.
Proof.
  induction rows as [| row rest IH]; intros capacity acc_nat acc_z Hcap Hacc Hnonneg.
  - simpl. exact Hacc.
  - simpl.
    assert (Hacc' :
      Z.of_nat
        (acc_nat + (count_water (nat_row_of_z row) + Z.to_nat capacity - 1) /
         Z.to_nat capacity)%nat =
      acc_z + row_trip_z row capacity).
    { rewrite Nat2Z.inj_add.
      rewrite Hacc.
      rewrite row_trip_z_nat_bridge; try lia.
      intros c Hc. apply (Hnonneg 0 c).
      - rewrite Zlength_correct. simpl. lia.
      - exact Hc. }
    assert (Htail : forall r c : Z,
      0 <= r < Zlength rest ->
      0 <= c < Zlength (Znth r rest nil) ->
      0 <= Znth c (Znth r rest nil) 0).
    { intros r c Hr Hc.
      replace (Znth r rest nil) with (Znth (r + 1) (row :: rest) nil).
      2:{ rewrite Znth_cons by lia.
          replace (r + 1 - 1) with r by lia.
          reflexivity. }
      apply (Hnonneg (r + 1) c).
      * rewrite Zlength_correct in *. simpl in *. lia.
      * rewrite Znth_cons by lia.
        replace (r + 1 - 1) with r by lia.
        exact Hc. }
    rewrite (IH capacity
      (acc_nat + (count_water (nat_row_of_z row) + Z.to_nat capacity - 1) /
       Z.to_nat capacity)%nat
      (acc_z + row_trip_z row capacity)
      Hcap Hacc' Htail).
    reflexivity.
Qed.

Lemma required_trips_all_bridge : forall rows capacity,
  1 <= capacity ->
  (forall r c, 0 <= r < Zlength rows -> 0 <= c < Zlength (Znth r rows nil) -> 0 <= Znth c (Znth r rows nil) 0) ->
  Z.of_nat (required_trips_impl (nat_grid_of_z rows) (Z.to_nat capacity)) =
  trips_prefix_z rows (Zlength rows) capacity.
Proof.
  intros rows capacity Hcap Hnonneg.
  unfold required_trips_impl.
  unfold trips_prefix_z.
  replace (Z.to_nat (Zlength rows)) with (length rows)
    by (rewrite Zlength_correct; lia).
  rewrite firstn_all.
  apply required_trips_bridge_acc; try lia; try reflexivity.
  exact Hnonneg.
Qed.

Lemma problem_115_spec_z_of_trips_prefix : forall rows capacity ret,
  problem_115_pre_z rows capacity ->
  1 <= capacity ->
  ret = trips_prefix_z rows (Zlength rows) capacity ->
  (forall r c, 0 <= r < Zlength rows -> 0 <= c < Zlength (Znth r rows nil) -> 0 <= Znth c (Znth r rows nil) 0) ->
  problem_115_spec_z rows capacity ret.
Proof.
  intros rows capacity ret Hpre Hcap Hret Hnonneg.
  unfold problem_115_spec_z.
  unfold problem_115_spec.
  subst ret.
  pose proof (required_trips_all_bridge rows capacity Hcap Hnonneg) as Hbridge.
  apply Nat2Z.inj.
  rewrite Z2Nat.id.
  - symmetry. exact Hbridge.
  - rewrite <- Hbridge. lia.
Qed.
