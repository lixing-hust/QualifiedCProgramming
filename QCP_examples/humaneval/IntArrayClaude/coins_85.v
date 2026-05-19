Load "../spec/85".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint sum_even_at_odd_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := sum_even_at_odd_upto_nat n' l in
      let i := Z.of_nat n' in
      let x := Znth (2 * i + 1) l 0 in
      if Z.eqb (Z.rem x 2) 0 then s + x else s
  end.

Definition sum_even_at_odd_upto (i : Z) (l : list Z) : Z :=
  sum_even_at_odd_upto_nat (Z.to_nat i) l.

Definition problem_85_pre_z (lst : list Z) : Prop :=
  problem_85_pre lst.

Definition problem_85_spec_z (lst : list Z) (output : Z) : Prop :=
  problem_85_spec lst output.

Definition add_int_range (lst : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i + 1 < Zlength lst ->
    INT_MIN <= sum_even_at_odd_upto i lst <= INT_MAX /\
    INT_MIN <= sum_even_at_odd_upto i lst + Znth (2 * i + 1) lst 0 <= INT_MAX.

Lemma sum_even_at_odd_upto_0 : forall l,
  sum_even_at_odd_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_even_at_odd_upto.
  reflexivity.
Qed.

Lemma sum_even_at_odd_upto_step_even : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i + 1) l 0) 2 = 0 ->
  sum_even_at_odd_upto (i + 1) l =
  sum_even_at_odd_upto i l + Znth (2 * i + 1) l 0.
Proof.
  intros i l Hi Heven.
  unfold sum_even_at_odd_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change ((match i with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0
           | Z.neg y' => Z.neg y'~0
           end) + 1) with (2 * i + 1).
  destruct (Z.eqb (Z.rem (Znth (2 * i + 1) l 0) 2) 0) eqn:Heq.
  - reflexivity.
  - apply Z.eqb_neq in Heq. congruence.
Qed.

Lemma sum_even_at_odd_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i + 1) l 0) 2 <> 0 ->
  sum_even_at_odd_upto (i + 1) l =
  sum_even_at_odd_upto i l.
Proof.
  intros i l Hi Hodd.
  unfold sum_even_at_odd_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change ((match i with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0
           | Z.neg y' => Z.neg y'~0
           end) + 1) with (2 * i + 1).
  destruct (Z.eqb (Z.rem (Znth (2 * i + 1) l 0) 2) 0) eqn:Heq.
  - apply Z.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

Lemma Z_rem_0_even : forall x,
  Z.rem x 2 = 0 <-> Z.even x = true.
Proof.
  intros x.
  rewrite Z.even_spec.
  split.
  - intros Hrem.
    apply Z.rem_divide in Hrem; [|lia].
    destruct Hrem as [q Hq].
    exists q. lia.
  - intros [q Hq].
    subst x.
    replace (2 * q) with (q * 2) by lia.
    rewrite Z.rem_mul by lia.
    reflexivity.
Qed.

Lemma Z_rem_eqb_0_even : forall x,
  Z.eqb (Z.rem x 2) 0 = Z.even x.
Proof.
  intros x.
  destruct (Z.eqb (Z.rem x 2) 0) eqn:Hrem.
  - apply Z.eqb_eq in Hrem.
    apply Z_rem_0_even in Hrem.
    rewrite Hrem. reflexivity.
  - apply Z.eqb_neq in Hrem.
    destruct (Z.even x) eqn:Heven; [|reflexivity].
    apply Z_rem_0_even in Heven.
    contradiction.
Qed.

Lemma sum_even_at_odd_indices_plus2 : forall l n,
  sum_even_at_odd_indices l (S (S n)) =
  sum_even_at_odd_indices l n.
Proof.
  induction l as [|x xs IH]; intros n; simpl.
  - reflexivity.
  - rewrite Nat.odd_succ, Nat.even_succ.
    rewrite IH.
    reflexivity.
Qed.

Lemma sum_even_at_odd_upto_nat_cons2 : forall n a b t,
  sum_even_at_odd_upto_nat (S n) (a :: b :: t) =
  (if Z.eqb (Z.rem b 2) 0 then b else 0) +
  sum_even_at_odd_upto_nat n t.
Proof.
  induction n as [|n IH]; intros a b t.
  - simpl.
    change (Znth 1 (a :: b :: t) 0) with b.
    destruct (Z.eqb (Z.rem b 2) 0); lia.
  - change (sum_even_at_odd_upto_nat (S (S n)) (a :: b :: t)) with
      (let s := sum_even_at_odd_upto_nat (S n) (a :: b :: t) in
       let i := Z.of_nat (S n) in
       let x := Znth (2 * i + 1) (a :: b :: t) 0 in
       if Z.eqb (Z.rem x 2) 0 then s + x else s).
    rewrite (IH a b t).
    change (sum_even_at_odd_upto_nat (S n) t) with
      (let s := sum_even_at_odd_upto_nat n t in
       let i := Z.of_nat n in
       let x := Znth (2 * i + 1) t 0 in
       if Z.eqb (Z.rem x 2) 0 then s + x else s).
    unfold Znth.
    replace (Z.to_nat (2 * Z.of_nat (S n) + 1))
      with (S (S (Z.to_nat (2 * Z.of_nat n + 1)))) by lia.
    simpl.
    set (c := if Z.rem b 2 =? 0 then b else 0).
    set (s := sum_even_at_odd_upto_nat n t).
    match goal with
    | |- context [if ?B then _ else _] => destruct B
    end; lia.
Qed.

Lemma sum_even_at_odd_indices_upto_exit : forall n l,
  (2 * n <= length l)%nat ->
  (length l <= 2 * n + 1)%nat ->
  sum_even_at_odd_indices l 0 =
  sum_even_at_odd_upto_nat n l.
Proof.
  induction n as [|n IH]; intros l Hlow Hhigh.
  - destruct l as [|x [|y ys]]; simpl in *; try lia; reflexivity.
  - destruct l as [|a [|b t]].
    + simpl in *; lia.
    + simpl in *; lia.
    + simpl in Hlow, Hhigh.
      cbn [sum_even_at_odd_indices Nat.odd Nat.even andb].
    rewrite sum_even_at_odd_indices_plus2.
    rewrite sum_even_at_odd_upto_nat_cons2.
    rewrite Z_rem_eqb_0_even.
    assert (Hlow_t : (2 * n <= length t)%nat) by lia.
    assert (Hhigh_t : (length t <= 2 * n + 1)%nat) by lia.
    rewrite (IH t Hlow_t Hhigh_t).
    change (Nat.odd 0) with false.
    change (Nat.odd 1) with true.
    simpl.
    destruct (Z.even b); lia.
Qed.

Lemma problem_85_spec_z_of_exit : forall l i s,
  0 <= i ->
  2 * i <= Zlength l ->
  2 * i + 1 >= Zlength l ->
  s = sum_even_at_odd_upto i l ->
  problem_85_spec_z l s.
Proof.
  intros l i s Hi Hbound Hexit Hs.
  unfold problem_85_spec_z, problem_85_spec, add_impl.
  subst s.
  unfold sum_even_at_odd_upto.
  rewrite <- sum_even_at_odd_indices_upto_exit.
  - reflexivity.
  - rewrite Zlength_correct in Hbound.
    lia.
  - rewrite Zlength_correct in Hexit.
    lia.
Qed.
