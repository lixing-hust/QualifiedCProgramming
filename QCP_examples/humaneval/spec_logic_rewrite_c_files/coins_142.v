Load "../spec/142".

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_142_pre_z (lst : list Z) : Prop :=
  problem_142_pre lst.

Definition problem_142_spec_z (lst : list Z) (out : Z) : Prop :=
  problem_142_spec lst out.

Definition z_indices_142 (len : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat len)).

Definition transformed_entry_z_142 (i x : Z) : Z :=
  if Z.eqb (Z.rem i 3) 0 then x * x
  else if Z.eqb (Z.rem i 4) 0 then (x * x) * x
  else x.

Definition sum_prefix_142 (i : Z) (lst : list Z) : Z :=
  fold_left
    Z.add
    (map (fun p => transformed_entry (fst p) (snd p))
      (combine (seq 0 (Z.to_nat i)) (firstn (Z.to_nat i) lst)))
    0.

Definition sum_squares_int_range_142 (lst : list Z) : Prop :=
  Forall (fun x => INT_MIN <= x <= INT_MAX) lst /\
  forall i,
    0 <= i ->
    i < Zlength lst ->
    INT_MIN <= Znth i lst 0 * Znth i lst 0 <= INT_MAX /\
    INT_MIN <= (Znth i lst 0 * Znth i lst 0) * Znth i lst 0 <= INT_MAX /\
    INT_MIN <= sum_prefix_142 i lst <= INT_MAX /\
    INT_MIN <= sum_prefix_142 i lst + transformed_entry_z_142 i (Znth i lst 0) <= INT_MAX /\
    INT_MIN <= sum_prefix_142 (i + 1) lst <= INT_MAX.

Lemma fold_left_Zadd_acc_142 : forall l acc,
  fold_left Z.add l acc = acc + fold_left Z.add l 0.
Proof.
  induction l as [| x xs IH]; intros acc.
  - cbn. lia.
  - cbn. rewrite IH. rewrite (IH x). lia.
Qed.

Lemma z_indices_142_snoc : forall i,
  0 <= i ->
  z_indices_142 (i + 1) = z_indices_142 i ++ [i].
Proof.
  intros i Hi.
  unfold z_indices_142.
  rewrite Z2Nat.inj_add by lia.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  rewrite Nat.add_1_r, seq_S, map_app.
  cbn.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma sum_prefix_142_0 : forall lst,
  sum_prefix_142 0 lst = 0.
Proof.
  intros lst. reflexivity.
Qed.

Lemma transformed_entry_z_142_of_nat : forall n x,
  transformed_entry_z_142 (Z.of_nat n) x = transformed_entry n x.
Proof.
  intros n x.
  unfold transformed_entry_z_142, transformed_entry.
  assert (Hrem3 : Z.rem (Z.of_nat n) 3 = Z.of_nat (n mod 3)%nat).
  {
    rewrite Z.rem_mod_nonneg by lia.
    change 3 with (Z.of_nat 3%nat).
    rewrite <- Nat2Z.inj_mod by lia.
    reflexivity.
  }
  assert (Hrem4 : Z.rem (Z.of_nat n) 4 = Z.of_nat (n mod 4)%nat).
  {
    rewrite Z.rem_mod_nonneg by lia.
    change 4 with (Z.of_nat 4%nat).
    rewrite <- Nat2Z.inj_mod by lia.
    reflexivity.
  }
  rewrite Hrem3, Hrem4.
  destruct (n mod 3 =? 0)%nat eqn:H3.
  - apply Nat.eqb_eq in H3.
    assert (Hz3 : (Z.of_nat (n mod 3) =? 0) = true).
    { apply Z.eqb_eq. lia. }
    rewrite Hz3.
    reflexivity.
  - apply Nat.eqb_neq in H3.
    assert (Hz3 : (Z.of_nat (n mod 3) =? 0) = false).
    { apply Z.eqb_neq. lia. }
    rewrite Hz3.
    destruct (n mod 4 =? 0)%nat eqn:H4.
    + apply Nat.eqb_eq in H4.
      assert (Hz4 : (Z.of_nat (n mod 4) =? 0) = true).
      { apply Z.eqb_eq. lia. }
      rewrite Hz4.
      reflexivity.
    + apply Nat.eqb_neq in H4.
      assert (Hz4 : (Z.of_nat (n mod 4) =? 0) = false).
      { apply Z.eqb_neq. lia. }
      rewrite Hz4.
      reflexivity.
Qed.

Lemma firstn_succ_snoc_142 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_142 : forall (lst : list Z) i,
  0 <= i < Zlength lst ->
  firstn (Z.to_nat (i + 1)) lst =
    firstn (Z.to_nat i) lst ++ [Znth i lst 0].
Proof.
  intros lst i Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_142 with (d := 0)
    by (rewrite Zlength_correct in Hi; lia).
  unfold Znth.
  reflexivity.
Qed.

Lemma sum_prefix_142_step : forall lst i,
  0 <= i ->
  i < Zlength lst ->
  sum_prefix_142 (i + 1) lst =
    sum_prefix_142 i lst + transformed_entry_z_142 i (Znth i lst 0).
Proof.
  intros lst i Hi Hlt.
  unfold sum_prefix_142.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_S.
  rewrite firstn_succ_snoc_142 with (d := 0)
    by (rewrite Zlength_correct in Hlt; lia).
  replace (nth (Z.to_nat i) lst 0) with (Znth i lst 0)
    by (unfold Znth; reflexivity).
  rewrite combine_app.
  rewrite map_app.
  cbn [map fold_left].
  rewrite fold_left_app.
  cbn [fold_left].
  rewrite fold_left_Zadd_acc_142.
  replace (Z.of_nat (0 + Z.to_nat i)) with i by lia.
  cbn [combine map fold_left fst snd].
  rewrite <- transformed_entry_z_142_of_nat.
  replace (Z.of_nat (0 + Z.to_nat i)) with i by lia.
  lia.
  rewrite seq_length.
  rewrite firstn_length_le by (rewrite Zlength_correct in Hlt; lia).
  lia.
Qed.

Lemma sum_prefix_142_step_mod3 : forall lst i,
  0 <= i ->
  i < Zlength lst ->
  Z.rem i 3 = 0 ->
  sum_prefix_142 (i + 1) lst =
    sum_prefix_142 i lst + Znth i lst 0 * Znth i lst 0.
Proof.
  intros lst i Hi Hlt Hrem.
  rewrite sum_prefix_142_step by lia.
  unfold transformed_entry_z_142.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma sum_prefix_142_step_mod4_not3 : forall lst i,
  0 <= i ->
  i < Zlength lst ->
  Z.rem i 3 <> 0 ->
  Z.rem i 4 = 0 ->
  sum_prefix_142 (i + 1) lst =
    sum_prefix_142 i lst + (Znth i lst 0 * Znth i lst 0) * Znth i lst 0.
Proof.
  intros lst i Hi Hlt Hrem3 Hrem4.
  rewrite sum_prefix_142_step by lia.
  unfold transformed_entry_z_142.
  destruct (Z.rem i 3 =? 0) eqn:H3.
  - apply Z.eqb_eq in H3. contradiction.
  - rewrite Hrem4. reflexivity.
Qed.

Lemma sum_prefix_142_step_plain : forall lst i,
  0 <= i ->
  i < Zlength lst ->
  Z.rem i 3 <> 0 ->
  Z.rem i 4 <> 0 ->
  sum_prefix_142 (i + 1) lst =
    sum_prefix_142 i lst + Znth i lst 0.
Proof.
  intros lst i Hi Hlt Hrem3 Hrem4.
  rewrite sum_prefix_142_step by lia.
  unfold transformed_entry_z_142.
  destruct (Z.rem i 3 =? 0) eqn:H3.
  - apply Z.eqb_eq in H3. contradiction.
  - destruct (Z.rem i 4 =? 0) eqn:H4.
    + apply Z.eqb_eq in H4. contradiction.
    + reflexivity.
Qed.

Lemma sum_squares_int_range_step : forall lst i,
  sum_squares_int_range_142 lst ->
  0 <= i ->
  i < Zlength lst ->
  INT_MIN <= sum_prefix_142 i lst <= INT_MAX /\
  INT_MIN <= sum_prefix_142 i lst + transformed_entry_z_142 i (Znth i lst 0) <= INT_MAX /\
  INT_MIN <= sum_prefix_142 (i + 1) lst <= INT_MAX.
Proof.
  intros lst i [_ Hrange] Hi Hlt.
  specialize (Hrange i Hi Hlt) as (_ & _ & Hsum & Hadd & Hnext).
  tauto.
Qed.

Lemma sum_squares_int_range_square : forall lst i,
  sum_squares_int_range_142 lst ->
  0 <= i ->
  i < Zlength lst ->
  INT_MIN <= Znth i lst 0 * Znth i lst 0 <= INT_MAX.
Proof.
  intros lst i [_ Hrange] Hi Hlt.
  specialize (Hrange i Hi Hlt) as (Hsq & _).
  exact Hsq.
Qed.

Lemma sum_squares_int_range_cube : forall lst i,
  sum_squares_int_range_142 lst ->
  0 <= i ->
  i < Zlength lst ->
  INT_MIN <= (Znth i lst 0 * Znth i lst 0) * Znth i lst 0 <= INT_MAX.
Proof.
  intros lst i [_ Hrange] Hi Hlt.
  specialize (Hrange i Hi Hlt) as (_ & Hcube & _).
  exact Hcube.
Qed.

Lemma sum_prefix_142_exit_range : forall lst i,
  sum_squares_int_range_142 lst ->
  0 <= i ->
  i <= Zlength lst ->
  INT_MIN <= sum_prefix_142 i lst <= INT_MAX.
Proof.
  intros lst i [Hall Hrange] Hi Hle.
  destruct (Z.eq_dec i 0) as [-> | Hnz].
  - rewrite sum_prefix_142_0. replace INT_MIN with (-2147483648) by reflexivity. lia.
  - assert (Hprev0 : 0 <= i - 1) by lia.
    assert (Hprevlt : i - 1 < Zlength lst) by lia.
    specialize (Hrange (i - 1) Hprev0 Hprevlt) as (_ & _ & _ & _ & Hnext).
    replace (i - 1 + 1) with i in Hnext by lia.
    exact Hnext.
Qed.

Lemma Znth_map_142 : forall {A B : Type} (f : A -> B) (l : list A) i d d',
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

Lemma Znth_seq_142 : forall start len i d,
  0 <= i < Z.of_nat len ->
  Znth i (seq start len) d = (start + Z.to_nat i)%nat.
Proof.
  intros start len i d Hi.
  unfold Znth.
  rewrite nth_indep with (d' := (start + Z.to_nat i)%nat).
  - apply seq_nth. lia.
  - rewrite seq_length. lia.
Qed.

Lemma sum_prefix_142_full_spec : forall lst,
  problem_142_spec_z lst (sum_prefix_142 (Zlength lst) lst).
Proof.
  intros lst.
  unfold problem_142_spec_z, problem_142_spec, sum_squares_impl.
  unfold sum_prefix_142, sum_transformed.
  rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length lst))) with (length lst) by lia.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma problem_142_spec_z_of_exit : forall lst i,
  i = Zlength lst ->
  problem_142_spec_z lst (sum_prefix_142 i lst).
Proof.
  intros lst i ->.
  apply sum_prefix_142_full_spec.
Qed.
