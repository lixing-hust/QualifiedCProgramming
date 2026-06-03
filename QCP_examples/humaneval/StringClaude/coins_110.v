Load "../spec/110".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition yesno_of_z_110 (z : Z) : string :=
  if Z.eqb z 1 then "YES" else "NO".

Definition list_Z_to_nat_110 (l : list Z) : list nat :=
  map Z.to_nat l.

Definition nonnegative_list_z (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0.

Definition problem_110_pre_z (lst1 lst2 : list Z) : Prop :=
  problem_110_pre (list_Z_to_nat_110 lst1) (list_Z_to_nat_110 lst2).

Definition problem_110_spec_z (lst1 lst2 : list Z) (output : Z) : Prop :=
  problem_110_spec (list_Z_to_nat_110 lst1) (list_Z_to_nat_110 lst2) (yesno_of_z_110 output).

Definition even_zb (x : Z) : bool :=
  Z.eqb (Z.rem x 2) 0.

Fixpoint count_even_list_z (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if even_zb x then 1 else 0) + count_even_list_z xs
  end.

Definition count_even_upto (i : Z) (l : list Z) : Z :=
  count_even_list_z (sublist 0 i l).

Lemma count_even_list_z_nonneg : forall l,
  0 <= count_even_list_z l.
Proof.
  induction l; simpl; try lia.
  destruct (even_zb a); lia.
Qed.

Lemma count_even_list_z_le_len : forall l,
  count_even_list_z l <= Zlength l.
Proof.
  induction l; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (even_zb a); lia.
Qed.

Lemma count_even_list_z_app_single : forall l x,
  count_even_list_z (l ++ [x]) =
  count_even_list_z l + if even_zb x then 1 else 0.
Proof.
  induction l as [| y ys IH]; intros x; simpl.
  - lia.
  - rewrite IH.
    destruct (even_zb y); destruct (even_zb x); lia.
Qed.

Lemma count_even_upto_bounds : forall i l,
  0 <= i <= Zlength l ->
  0 <= count_even_upto i l <= i.
Proof.
  intros i l Hi.
  unfold count_even_upto.
  split.
  - apply count_even_list_z_nonneg.
  - pose proof (count_even_list_z_le_len (sublist 0 i l)).
    rewrite Zlength_sublist in H by lia.
    lia.
Qed.

Lemma count_even_upto_0 : forall l,
  count_even_upto 0 l = 0.
Proof.
  intros l.
  unfold count_even_upto.
  rewrite sublist_nil by lia.
  reflexivity.
Qed.

Lemma count_even_upto_full : forall l n,
  n = Zlength l ->
  count_even_upto n l = count_even_list_z l.
Proof.
  intros l n Hn.
  subst n.
  unfold count_even_upto.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma count_even_upto_step_even : forall i l,
  0 <= i < Zlength l ->
  even_zb (Znth i l 0) = true ->
  count_even_upto (i + 1) l = count_even_upto i l + 1.
Proof.
  intros i l Hi Heven.
  unfold count_even_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    (rewrite Zlength_correct in Hi; lia).
  rewrite (sublist_single i l 0) by (rewrite Zlength_correct in Hi; lia).
  rewrite count_even_list_z_app_single.
  rewrite Heven.
  lia.
Qed.

Lemma count_even_upto_step_not_even : forall i l,
  0 <= i < Zlength l ->
  even_zb (Znth i l 0) = false ->
  count_even_upto (i + 1) l = count_even_upto i l.
Proof.
  intros i l Hi Heven.
  unfold count_even_upto.
  rewrite (sublist_split 0 (i + 1) i l) by
    (rewrite Zlength_correct in Hi; lia).
  rewrite (sublist_single i l 0) by (rewrite Zlength_correct in Hi; lia).
  rewrite count_even_list_z_app_single.
  rewrite Heven.
  lia.
Qed.

Lemma even_zb_rem_true : forall x,
  Z.rem x 2 = 0 ->
  even_zb x = true.
Proof.
  intros x H.
  unfold even_zb.
  apply Z.eqb_eq.
  exact H.
Qed.

Lemma even_zb_rem_false : forall x,
  Z.rem x 2 <> 0 ->
  even_zb x = false.
Proof.
  intros x H.
  unfold even_zb.
  apply Z.eqb_neq.
  exact H.
Qed.

Lemma count_even_upto_step_rem_even : forall i l,
  0 <= i < Zlength l ->
  Z.rem (Znth i l 0) 2 = 0 ->
  count_even_upto (i + 1) l = count_even_upto i l + 1.
Proof.
  intros.
  apply count_even_upto_step_even; auto.
  apply even_zb_rem_true; assumption.
Qed.

Lemma count_even_upto_step_rem_not_even : forall i l,
  0 <= i < Zlength l ->
  Z.rem (Znth i l 0) 2 <> 0 ->
  count_even_upto (i + 1) l = count_even_upto i l.
Proof.
  intros.
  apply count_even_upto_step_not_even; auto.
  apply even_zb_rem_false; assumption.
Qed.

Lemma even_zb_true_iff_nat_even : forall z,
  0 <= z ->
  even_zb z = true <-> Nat.even (Z.to_nat z) = true.
Proof.
  intros z Hz.
  unfold even_zb.
  rewrite Z.eqb_eq.
  split; intro H.
  - apply Nat.even_spec.
    apply Z.rem_divide in H; try lia.
    destruct H as [q Hq].
    assert (0 <= q) by nia.
    exists (Z.to_nat q).
    rewrite Hq.
    rewrite Z2Nat.inj_mul by lia.
    simpl.
    lia.
  - apply Nat.even_spec in H.
    destruct H as [q Hq].
    rewrite <- (Z2Nat.id z) by lia.
    rewrite Hq.
    replace (Z.of_nat (2 * q)) with (Z.of_nat q * 2) by lia.
    apply Z.rem_mul.
    lia.
Qed.

Lemma nat_odd_true_iff_even_false : forall n,
  Nat.odd n = true <-> Nat.even n = false.
Proof.
  intro n.
  rewrite <- Nat.negb_even.
  destruct (Nat.even n); simpl; split; congruence.
Qed.

Lemma count_even_list_z_nat_even : forall l,
  nonnegative_list_z l ->
  count_even_list_z l =
    Z.of_nat (List.length (filter Nat.even (list_Z_to_nat_110 l))).
Proof.
  induction l as [| x xs IH]; intros Hnonneg; simpl.
  - reflexivity.
  - assert (Hx : 0 <= x).
    { change x with (Znth 0 (x :: xs) 0).
      apply Hnonneg.
      rewrite Zlength_correct. simpl. lia. }
    assert (Hxs : nonnegative_list_z xs).
    { intros i Hi.
      pose proof (Hnonneg (i + 1)) as Htail.
      rewrite Znth_cons in Htail by lia.
      replace (i + 1 - 1) with i in Htail by lia.
      apply Htail.
      rewrite Zlength_correct in *. simpl. lia. }
    rewrite IH by exact Hxs.
    destruct (even_zb x) eqn:Heven.
    + pose proof (proj1 (even_zb_true_iff_nat_even x Hx) Heven) as Hnat.
      rewrite Hnat.
      change (1 + Z.of_nat (List.length (filter Nat.even (list_Z_to_nat_110 xs))) =
        Z.of_nat (S (List.length (filter Nat.even (list_Z_to_nat_110 xs))))).
      rewrite Nat2Z.inj_succ.
      lia.
    + destruct (Nat.even (Z.to_nat x)) eqn:Hnat.
      * apply (proj2 (even_zb_true_iff_nat_even x Hx)) in Hnat.
        congruence.
      * simpl. lia.
Qed.

Lemma count_odd_nat_as_len_minus_even : forall l,
  Z.of_nat (List.length (filter Nat.odd (list_Z_to_nat_110 l))) =
  Zlength l -
  Z.of_nat (List.length (filter Nat.even (list_Z_to_nat_110 l))).
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite Zlength_cons.
    destruct (Nat.even (Z.to_nat x)) eqn:Heven.
    + rewrite <- Nat.negb_even in *.
      rewrite Heven.
      simpl.
      lia.
    + rewrite <- Nat.negb_even in *.
      rewrite Heven.
      simpl.
      lia.
Qed.

Lemma problem_110_spec_z_true : forall lst1 lst2 total_even,
  problem_110_pre_z lst1 lst2 ->
  nonnegative_list_z lst1 ->
  nonnegative_list_z lst2 ->
  total_even = count_even_list_z lst1 + count_even_list_z lst2 ->
  Zlength lst1 <= total_even ->
  problem_110_spec_z lst1 lst2 1.
Proof.
  intros lst1 lst2 total_even Hpre Hnon1 Hnon2 Htotal Hcmp.
  unfold problem_110_spec_z, problem_110_spec, yesno_of_z_110.
  replace (Z.eqb 1 1) with true by reflexivity.
  pose proof (count_even_list_z_nat_even lst1 Hnon1) as Heven1.
  pose proof (count_even_list_z_nat_even lst2 Hnon2) as Heven2.
  pose proof (count_odd_nat_as_len_minus_even lst1) as Hodd1.
  destruct (Nat.leb_spec
    (List.length (filter Nat.odd (list_Z_to_nat_110 lst1)))
    (List.length (filter Nat.even (list_Z_to_nat_110 lst2)))) as [Hle | Hgt].
  - reflexivity.
  - exfalso.
    rewrite Zlength_correct in Hcmp.
    rewrite Zlength_correct in Hodd1.
    apply Nat2Z.inj_lt in Hgt.
    nia.
Qed.

Lemma problem_110_spec_z_false : forall lst1 lst2 total_even,
  problem_110_pre_z lst1 lst2 ->
  nonnegative_list_z lst1 ->
  nonnegative_list_z lst2 ->
  total_even = count_even_list_z lst1 + count_even_list_z lst2 ->
  total_even < Zlength lst1 ->
  problem_110_spec_z lst1 lst2 0.
Proof.
  intros lst1 lst2 total_even Hpre Hnon1 Hnon2 Htotal Hcmp.
  unfold problem_110_spec_z, problem_110_spec, yesno_of_z_110.
  replace (Z.eqb 0 1) with false by reflexivity.
  pose proof (count_even_list_z_nat_even lst1 Hnon1) as Heven1.
  pose proof (count_even_list_z_nat_even lst2 Hnon2) as Heven2.
  pose proof (count_odd_nat_as_len_minus_even lst1) as Hodd1.
  destruct (Nat.leb_spec
    (List.length (filter Nat.odd (list_Z_to_nat_110 lst1)))
    (List.length (filter Nat.even (list_Z_to_nat_110 lst2)))) as [Hle | Hgt].
  - exfalso.
    rewrite Zlength_correct in Hcmp.
    rewrite Zlength_correct in Hodd1.
    apply Nat2Z.inj_le in Hle.
    nia.
  - reflexivity.
Qed.
