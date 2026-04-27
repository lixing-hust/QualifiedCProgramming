Load "../spec/121".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint sum_odd_at_even_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := sum_odd_at_even_upto_nat n' l in
      let i := Z.of_nat n' in
      let x := Znth (2 * i) l 0 in
      if Z.eqb (Z.rem x 2) 1 then s + x else s
  end.

Definition sum_odd_at_even_upto (i : Z) (l : list Z) : Z :=
  sum_odd_at_even_upto_nat (Z.to_nat i) l.

Definition problem_121_pre_z (lst : list Z) : Prop :=
  lst <> [].

Definition problem_121_spec_z (lst : list Z) (output : Z) : Prop :=
  exists i,
    0 <= i /\
    2 * i <= Zlength lst + 1 /\
    Zlength lst <= 2 * i /\
    output = sum_odd_at_even_upto i lst.

Definition sum_odd_at_even_int_range (lst : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i < Zlength lst ->
    INT_MIN <= sum_odd_at_even_upto i lst <= INT_MAX /\
    INT_MIN <= sum_odd_at_even_upto i lst + Znth (2 * i) lst 0 <= INT_MAX.

Lemma sum_odd_at_even_upto_0 : forall l,
  sum_odd_at_even_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_odd_at_even_upto.
  reflexivity.
Qed.

Lemma sum_odd_at_even_upto_step_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i) l 0) 2 = 1 ->
  sum_odd_at_even_upto (i + 1) l =
  sum_odd_at_even_upto i l + Znth (2 * i) l 0.
Proof.
  intros i l Hi Hodd.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  destruct (Z.eqb (Z.rem (Znth (2 * i) l 0) 2) 1) eqn:Heq.
  - reflexivity.
  - apply Z.eqb_neq in Heq. congruence.
Qed.

Lemma sum_odd_at_even_upto_step_not_odd : forall i l,
  0 <= i ->
  Z.rem (Znth (2 * i) l 0) 2 <> 1 ->
  sum_odd_at_even_upto (i + 1) l =
  sum_odd_at_even_upto i l.
Proof.
  intros i l Hi Hnot.
  unfold sum_odd_at_even_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  change (match i with
          | 0 => 0
          | Z.pos y' => Z.pos y'~0
          | Z.neg y' => Z.neg y'~0
          end) with (2 * i).
  destruct (Z.eqb (Z.rem (Znth (2 * i) l 0) 2) 1) eqn:Heq.
  - apply Z.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

Lemma problem_121_spec_z_of_exit : forall l i s,
  0 <= i ->
  2 * i <= Zlength l + 1 ->
  Zlength l <= 2 * i ->
  s = sum_odd_at_even_upto i l ->
  problem_121_spec_z l s.
Proof.
  intros l i s Hi Hbound Hexit Hs.
  exists i.
  repeat split; try assumption.
Qed.
