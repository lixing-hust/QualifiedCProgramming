Load "../spec/142".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition transformed_value (i x : Z) : Z :=
  if Z.rem i 3 =? 0 then x * x
  else if Z.rem i 4 =? 0 then x * x * x
  else x.

Fixpoint transformed_sum_from (l : list Z) (start : Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => transformed_value start x + transformed_sum_from xs (start + 1)
  end.

Definition transformed_prefix_sum (i : Z) (l : list Z) : Z :=
  transformed_sum_from (sublist 0 i l) 0.

Definition problem_142_pre_z (l : list Z) : Prop :=
  problem_142_pre l.

Definition problem_142_spec_z (l : list Z) (out : Z) : Prop :=
  problem_142_spec l out.

Definition sum_squares_int_range (l : list Z) : Prop :=
  (forall i,
     0 <= i < Zlength l ->
     let x := Znth i l 0 in
     INT_MIN <= x * x <= INT_MAX /\
     INT_MIN <= x * x * x <= INT_MAX /\
     INT_MIN <= transformed_prefix_sum i l + transformed_value i x <= INT_MAX) /\
  (forall i, 0 <= i <= Zlength l -> INT_MIN <= transformed_prefix_sum i l <= INT_MAX).

Lemma transformed_sum_from_app_single : forall xs x start,
  transformed_sum_from (xs ++ x :: nil) start =
  transformed_sum_from xs start + transformed_value (start + Zlength xs) x.
Proof.
  induction xs; intros x start; simpl.
  - change (Zlength (@nil Z)) with 0.
    rewrite Z.add_0_r.
    rewrite Z.add_0_r.
    reflexivity.
  - rewrite IHxs.
    rewrite Zlength_cons.
    replace (Z.succ (Zlength xs)) with (1 + Zlength xs) by lia.
    replace (start + 1 + Zlength xs) with (start + (1 + Zlength xs)) by lia.
    rewrite Z.add_assoc.
    reflexivity.
Qed.

Lemma transformed_prefix_sum_0 : forall l,
  transformed_prefix_sum 0 l = 0.
Proof.
  intros l.
  unfold transformed_prefix_sum.
  rewrite sublist_nil by lia.
  reflexivity.
Qed.

Lemma transformed_prefix_sum_snoc : forall l i,
  0 <= i < Zlength l ->
  transformed_prefix_sum (i + 1) l =
  transformed_prefix_sum i l + transformed_value i (Znth i l 0).
Proof.
  intros l i Hi.
  unfold transformed_prefix_sum.
  rewrite (sublist_split 0 (i + 1) i l)
    by (try rewrite <- Zlength_correct; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  rewrite transformed_sum_from_app_single.
  rewrite Zlength_sublist by lia.
  replace (0 + (i - 0)) with i by lia.
  reflexivity.
Qed.

Lemma sum_squares_next_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= transformed_prefix_sum i l + transformed_value i (Znth i l 0) <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [_ [_ Hsum]].
  exact Hsum.
Qed.

Lemma sum_squares_square_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= Znth i l 0 * Znth i l 0 <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [Hsq _].
  exact Hsq.
Qed.

Lemma sum_squares_cube_range : forall l i,
  sum_squares_int_range l ->
  0 <= i < Zlength l ->
  INT_MIN <= Znth i l 0 * Znth i l 0 * Znth i l 0 <= INT_MAX.
Proof.
  intros l i [Hstep _] Hi.
  pose proof (Hstep i Hi) as [_ [Hcube _]].
  exact Hcube.
Qed.

Lemma Nat_even_of_Z_nonneg : forall z n,
  z = Z.of_nat n ->
  Nat.modulo n 3 = 0%nat <-> Z.rem z 3 = 0.
Proof.
  intros z n Hz.
  subst z.
  rewrite Z.rem_mod_nonneg by lia.
  replace 3 with (Z.of_nat 3) by reflexivity.
  rewrite <- Nat2Z.inj_mod by lia.
  split; intro H.
  - rewrite H. reflexivity.
  - change 0 with (Z.of_nat 0) in H.
    apply Nat2Z.inj in H.
    exact H.
Qed.

Lemma Nat_mod4_of_Z_nonneg : forall z n,
  z = Z.of_nat n ->
  Nat.modulo n 4 = 0%nat <-> Z.rem z 4 = 0.
Proof.
  intros z n Hz.
  subst z.
  rewrite Z.rem_mod_nonneg by lia.
  replace 4 with (Z.of_nat 4) by reflexivity.
  rewrite <- Nat2Z.inj_mod by lia.
  split; intro H.
  - rewrite H. reflexivity.
  - change 0 with (Z.of_nat 0) in H.
    apply Nat2Z.inj in H.
    exact H.
Qed.

Lemma transformed_value_of_nat : forall n x,
  transformed_value (Z.of_nat n) x =
  if (Nat.modulo n 3 =? 0)%nat then x * x
  else if andb (Nat.modulo n 4 =? 0)%nat (negb (Nat.modulo n 3 =? 0)%nat)
       then x * x * x
       else x.
Proof.
  intros n x.
  unfold transformed_value.
  destruct (Nat.modulo n 3 =? 0)%nat eqn:H3.
  - apply Nat.eqb_eq in H3.
    apply Nat_even_of_Z_nonneg with (z := Z.of_nat n) in H3; [|reflexivity].
    apply Z.eqb_eq in H3.
    rewrite H3.
    reflexivity.
  - apply Nat.eqb_neq in H3.
    assert (HZ3 : Z.rem (Z.of_nat n) 3 <> 0).
    {
      intro Hcontra.
      apply H3.
      apply Nat_even_of_Z_nonneg with (z := Z.of_nat n); [reflexivity|assumption].
    }
    apply Z.eqb_neq in HZ3.
    rewrite HZ3.
    destruct (Nat.modulo n 4 =? 0)%nat eqn:H4.
    + apply Nat.eqb_eq in H4.
      apply Nat_mod4_of_Z_nonneg with (z := Z.of_nat n) in H4; [|reflexivity].
      apply Z.eqb_eq in H4.
      rewrite H4.
      simpl.
      reflexivity.
    + apply Nat.eqb_neq in H4.
      assert (HZ4 : Z.rem (Z.of_nat n) 4 <> 0).
      {
        intro Hcontra.
        apply H4.
        apply Nat_mod4_of_Z_nonneg with (z := Z.of_nat n); [reflexivity|assumption].
      }
      apply Z.eqb_neq in HZ4.
      rewrite HZ4.
      simpl.
      reflexivity.
Qed.

Lemma transformed_sum_from_spec : forall l n,
  transformed_sum_from l (Z.of_nat n) = sum_transformed l n.
Proof.
  induction l; intros n; simpl.
  - reflexivity.
  - rewrite transformed_value_of_nat.
    replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
    rewrite IHl.
    reflexivity.
Qed.

Lemma transformed_prefix_sum_full_spec : forall l,
  transformed_prefix_sum (Zlength l) l = sum_squares_impl l.
Proof.
  intros l.
  unfold transformed_prefix_sum, sum_squares_impl.
  rewrite sublist_self by reflexivity.
  change 0 with (Z.of_nat 0).
  apply transformed_sum_from_spec.
Qed.

Lemma problem_142_spec_z_of_prefix_full : forall l out,
  out = transformed_prefix_sum (Zlength l) l ->
  problem_142_spec_z l out.
Proof.
  intros l out Hout.
  unfold problem_142_spec_z, problem_142_spec.
  rewrite Hout.
  apply transformed_prefix_sum_full_spec.
Qed.

Lemma transformed_value_square : forall i x,
  Z.rem i 3 = 0 ->
  transformed_value i x = x * x.
Proof.
  intros i x H.
  unfold transformed_value.
  apply Z.eqb_eq in H.
  rewrite H.
  reflexivity.
Qed.

Lemma transformed_value_cube : forall i x,
  Z.rem i 3 <> 0 ->
  Z.rem i 4 = 0 ->
  transformed_value i x = x * x * x.
Proof.
  intros i x H3 H4.
  unfold transformed_value.
  apply Z.eqb_neq in H3.
  apply Z.eqb_eq in H4.
  rewrite H3, H4.
  reflexivity.
Qed.

Lemma transformed_value_plain : forall i x,
  Z.rem i 3 <> 0 ->
  Z.rem i 4 <> 0 ->
  transformed_value i x = x.
Proof.
  intros i x H3 H4.
  unfold transformed_value.
  apply Z.eqb_neq in H3.
  apply Z.eqb_neq in H4.
  rewrite H3, H4.
  reflexivity.
Qed.
