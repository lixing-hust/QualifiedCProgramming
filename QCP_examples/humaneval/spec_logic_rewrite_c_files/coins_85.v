Load "../spec/85".

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_85_pre_z (lst : list Z) : Prop :=
  problem_85_pre lst.

Definition problem_85_spec_z (lst : list Z) (out : Z) : Prop :=
  problem_85_spec lst out.

Definition odd_index_values_85 (i : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat i)).

Definition add_term_85 (lst : list Z) (k : Z) : Z :=
  let x := Znth (2 * k + 1) lst 0 in
  if Z.even x then x else 0.

Definition add_prefix_sum_85 (i : Z) (lst : list Z) : Z :=
  fold_left Z.add (map (add_term_85 lst) (odd_index_values_85 i)) 0.

Definition INT_MIN_85 : Z := -2147483648.

Definition add_sum_int_range_85 (lst : list Z) : Prop :=
  Forall (fun x => INT_MIN_85 <= x <= INT_MAX) lst /\
  forall i,
    0 <= i ->
    2 * i + 1 < Zlength lst ->
    INT_MIN_85 <= add_prefix_sum_85 i lst <= INT_MAX /\
    INT_MIN_85 <= add_prefix_sum_85 i lst + Znth (2 * i + 1) lst 0 <= INT_MAX /\
    INT_MIN_85 <= add_prefix_sum_85 (i + 1) lst <= INT_MAX.

Lemma fold_left_Zadd_acc_85 : forall l acc,
  fold_left Z.add l acc = acc + fold_left Z.add l 0.
Proof.
  induction l as [| x xs IH]; intros acc.
  - cbn. lia.
  - cbn. rewrite IH. rewrite (IH x). lia.
Qed.

Lemma odd_index_values_85_snoc : forall i,
  0 <= i ->
  odd_index_values_85 (i + 1) = odd_index_values_85 i ++ [i].
Proof.
  intros i Hi.
  unfold odd_index_values_85.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_S.
  rewrite map_app.
  cbn.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma add_prefix_sum_85_0 : forall lst,
  add_prefix_sum_85 0 lst = 0.
Proof.
  intros lst. reflexivity.
Qed.

Lemma add_prefix_sum_85_step : forall lst i,
  0 <= i ->
  add_prefix_sum_85 (i + 1) lst =
    add_prefix_sum_85 i lst + add_term_85 lst i.
Proof.
  intros lst i Hi.
  unfold add_prefix_sum_85.
  rewrite odd_index_values_85_snoc by lia.
  rewrite map_app.
  rewrite fold_left_app.
  cbn [map fold_left].
  rewrite fold_left_Zadd_acc_85.
  lia.
Qed.

Lemma zeven_rem_0_85 : forall x,
  Z.rem x 2 = 0 ->
  Z.even x = true.
Proof.
  intros x Hrem.
  apply Z.even_spec.
  exists (Z.quot x 2).
  pose proof (Z.quot_rem' x 2) as Hqr.
  rewrite Hrem in Hqr.
  lia.
Qed.

Lemma zeven_false_rem_nonzero_85 : forall x,
  Z.rem x 2 <> 0 ->
  Z.even x = false.
Proof.
  intros x Hrem.
  destruct (Z.even x) eqn:Heven; [| reflexivity].
  apply Z.even_spec in Heven.
  destruct Heven as [k Hx].
  exfalso.
  apply Hrem.
  subst x.
  replace (2 * k) with (k * 2) by lia.
  rewrite Z.rem_mul by lia.
  reflexivity.
Qed.

Lemma add_prefix_sum_85_step_even : forall lst i,
  0 <= i ->
  Z.rem (Znth (2 * i + 1) lst 0) 2 = 0 ->
  add_prefix_sum_85 (i + 1) lst =
    add_prefix_sum_85 i lst + Znth (2 * i + 1) lst 0.
Proof.
  intros lst i Hi Hrem.
  rewrite add_prefix_sum_85_step by lia.
  unfold add_term_85.
  rewrite zeven_rem_0_85 by exact Hrem.
  reflexivity.
Qed.

Lemma add_prefix_sum_85_step_odd : forall lst i,
  0 <= i ->
  Z.rem (Znth (2 * i + 1) lst 0) 2 <> 0 ->
  add_prefix_sum_85 (i + 1) lst =
    add_prefix_sum_85 i lst.
Proof.
  intros lst i Hi Hrem.
  rewrite add_prefix_sum_85_step by lia.
  unfold add_term_85.
  rewrite zeven_false_rem_nonzero_85 by exact Hrem.
  lia.
Qed.

Lemma add_prefix_sum_85_nonneg_range : forall lst i,
  add_sum_int_range_85 lst ->
  0 <= i ->
  2 * i + 1 < Zlength lst ->
  INT_MIN_85 <= add_prefix_sum_85 i lst <= INT_MAX /\
  INT_MIN_85 <= add_prefix_sum_85 i lst + Znth (2 * i + 1) lst 0 <= INT_MAX /\
  INT_MIN_85 <= add_prefix_sum_85 (i + 1) lst <= INT_MAX.
Proof.
  intros lst i [_ Hrange] Hi Hbound.
  apply Hrange; lia.
Qed.

Lemma add_prefix_sum_85_exit_range : forall lst i,
  add_sum_int_range_85 lst ->
  0 <= i ->
  2 * i <= Zlength lst ->
  2 * i + 1 >= Zlength lst ->
  INT_MIN_85 <= add_prefix_sum_85 i lst <= INT_MAX.
Proof.
  intros lst i [Hall Hrange] Hi Hlow Hexit.
  destruct (Z.eq_dec i 0) as [-> | Hnz].
  - rewrite add_prefix_sum_85_0. unfold INT_MIN_85. lia.
  - assert (Hprev : 0 <= i - 1) by lia.
    assert (Hlt : 2 * (i - 1) + 1 < Zlength lst) by lia.
    specialize (Hrange (i - 1) Hprev Hlt) as (_ & _ & Hnext).
    replace (i - 1 + 1) with i in Hnext by lia.
    exact Hnext.
Qed.

Lemma add_term_85_cons2 : forall a b xs k,
  0 <= k ->
  add_term_85 (a :: b :: xs) (k + 1) = add_term_85 xs k.
Proof.
  intros a b xs k Hk.
  unfold add_term_85.
  replace (2 * (k + 1) + 1) with (2 * k + 3) by lia.
  unfold Znth.
  replace (Z.to_nat (2 * k + 3)) with (S (S (Z.to_nat (2 * k + 1)))) by lia.
  reflexivity.
Qed.

Lemma add_prefix_sum_85_cons2 : forall a b xs i,
  0 <= i ->
  add_prefix_sum_85 (i + 1) (a :: b :: xs) =
    (if Z.even b then b else 0) + add_prefix_sum_85 i xs.
Proof.
  intros a b xs i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  induction (Z.to_nat i) as [| n IH].
  - change (Z.of_nat 0) with 0.
    vm_compute.
    destruct b as [| p | p]; try reflexivity; destruct p; reflexivity.
  - replace (Z.of_nat (S n) + 1) with (Z.of_nat (S n) + 1) by reflexivity.
    rewrite add_prefix_sum_85_step by lia.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite IH.
    rewrite add_prefix_sum_85_step by lia.
    rewrite add_term_85_cons2 by lia.
    destruct (Z.even b); lia.
Qed.

Fixpoint add_pairs_fix_85 (lst : list Z) : Z :=
  match lst with
  | _ :: b :: xs => (if Z.even b then b else 0) + add_pairs_fix_85 xs
  | _ => 0
  end.

Definition add_index_term_nat_85 (idx : nat) (x : Z) : Z :=
  if andb (Nat.odd idx) (Z.even x) then x else 0.

Lemma sum_even_at_odd_indices_cons_85 : forall x xs n,
  sum_even_at_odd_indices (x :: xs) n =
    add_index_term_nat_85 n x + sum_even_at_odd_indices xs (S n).
Proof.
  intros x xs n.
  unfold sum_even_at_odd_indices, add_index_term_nat_85.
  cbn [length seq combine map fst snd fold_left].
  rewrite fold_left_Zadd_acc_85.
  reflexivity.
Qed.

Lemma Nat_odd_plus_2_85 : forall n,
  Nat.odd (n + 2) = Nat.odd n.
Proof.
  intros n.
  replace (n + 2)%nat with (S (S n)) by lia.
  reflexivity.
Qed.

Lemma sum_even_at_odd_indices_shift2_85 : forall xs n,
  sum_even_at_odd_indices xs (n + 2) = sum_even_at_odd_indices xs n.
Proof.
  induction xs as [| x xs IH]; intros n.
  - reflexivity.
  - rewrite !sum_even_at_odd_indices_cons_85.
    unfold add_index_term_nat_85.
    rewrite Nat_odd_plus_2_85.
    replace (S (n + 2)) with (S n + 2)%nat by lia.
    rewrite IH.
    reflexivity.
Qed.

Lemma add_impl_cons2_85 : forall a b xs,
  add_impl (a :: b :: xs) =
    (if Z.even b then b else 0) + add_impl xs.
Proof.
  intros a b xs.
  unfold add_impl at 1.
  rewrite sum_even_at_odd_indices_cons_85.
  rewrite sum_even_at_odd_indices_cons_85.
  unfold add_index_term_nat_85.
  cbn [Nat.odd andb].
  rewrite sum_even_at_odd_indices_shift2_85 with (n := 0%nat).
  reflexivity.
Qed.

Lemma add_impl_fix_85 : forall lst,
  add_impl lst = add_pairs_fix_85 lst.
Proof.
  fix IH 1.
  intros [| a [| b xs]].
  - reflexivity.
  - reflexivity.
  - rewrite add_impl_cons2_85.
    cbn [add_pairs_fix_85].
    rewrite IH.
    reflexivity.
Qed.

Lemma add_prefix_sum_85_exit_fix : forall lst i,
  0 <= i ->
  2 * i <= Zlength lst ->
  2 * i + 1 >= Zlength lst ->
  add_prefix_sum_85 i lst = add_pairs_fix_85 lst.
Proof.
  intros lst i Hi Hlow Hexit.
  remember (Z.to_nat i) as n eqn:Hn.
  assert (Hi_eq : i = Z.of_nat n) by lia.
  rewrite Hi_eq in Hlow, Hexit |- *.
  clear Hi Hi_eq Hn i.
  generalize dependent lst.
  induction n as [| n IH]; intros lst Hlow Hexit.
  - change (Z.of_nat 0) with 0.
    rewrite add_prefix_sum_85_0.
    destruct lst as [| a [| b xs]]; cbn [add_pairs_fix_85] in *; try reflexivity.
    rewrite Zlength_correct in Hexit.
    cbn [length] in Hexit.
    lia.
  - destruct lst as [| a rest].
    + rewrite Zlength_correct in Hlow. cbn [length] in Hlow. lia.
    + destruct rest as [| b xs].
      * rewrite Zlength_correct in Hlow. cbn [length] in Hlow. lia.
      * cbn [add_pairs_fix_85].
        replace (add_prefix_sum_85 (Z.of_nat (S n)) (a :: b :: xs))
          with (add_prefix_sum_85 (Z.of_nat n + 1) (a :: b :: xs))
          by (replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia; reflexivity).
        rewrite add_prefix_sum_85_cons2 by lia.
        rewrite (IH xs).
        2,3: rewrite Zlength_correct in *; cbn [length] in *; lia.
        reflexivity.
Qed.

Lemma problem_85_spec_z_of_exit : forall lst i out,
  0 <= i ->
  2 * i <= Zlength lst ->
  2 * i + 1 >= Zlength lst ->
  out = add_prefix_sum_85 i lst ->
  problem_85_spec_z lst out.
Proof.
  intros lst i out Hi Hlow Hexit Hout.
  unfold problem_85_spec_z, problem_85_spec.
  subst out.
  rewrite add_prefix_sum_85_exit_fix by lia.
  rewrite <- add_impl_fix_85.
  reflexivity.
Qed.
