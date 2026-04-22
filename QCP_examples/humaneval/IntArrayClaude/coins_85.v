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
  exists i,
    0 <= i /\
    2 * i <= Zlength lst /\
    2 * i + 1 >= Zlength lst /\
    output = sum_even_at_odd_upto i lst.

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

Lemma problem_85_spec_z_of_exit : forall l i s,
  0 <= i ->
  2 * i <= Zlength l ->
  2 * i + 1 >= Zlength l ->
  s = sum_even_at_odd_upto i l ->
  problem_85_spec_z l s.
Proof.
  intros l i s Hi Hbound Hexit Hs.
  exists i.
  repeat split; try assumption.
Qed.
