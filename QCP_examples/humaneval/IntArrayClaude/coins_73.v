Load "../spec/73".

From AUXLib Require Import List_lemma ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.

Import naive_C_Rules.
Local Open Scope Z_scope.

Definition problem_73_pre_z (arr : list Z) : Prop :=
  problem_73_pre arr.

Fixpoint count_half_mismatches_upto_nat (n : nat) (arr : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let i := Z.of_nat n' in
      count_half_mismatches_upto_nat n' arr +
      (if Z.eqb (Znth i arr 0) (Znth (Zlength arr - 1 - i) arr 0)
       then 0
       else 1)
  end.

Definition count_half_mismatches_upto (i : Z) (arr : list Z) : Z :=
  count_half_mismatches_upto_nat (Z.to_nat i) arr.

Definition problem_73_spec_z (arr : list Z) (out : Z) : Prop :=
  exists i,
    0 <= i /\
    2 * i <= Zlength arr /\
    i >= Zlength arr - 1 - i /\
    out = count_half_mismatches_upto i arr.

Definition smallest_change_int_range (arr : list Z) : Prop :=
  forall i,
    0 <= i ->
    2 * i < Zlength arr ->
    INT_MIN <= count_half_mismatches_upto i arr <= INT_MAX /\
    INT_MIN <= count_half_mismatches_upto i arr + 1 <= INT_MAX.

Lemma count_half_mismatches_upto_0 : forall arr,
  count_half_mismatches_upto 0 arr = 0.
Proof.
  reflexivity.
Qed.

Lemma count_half_mismatches_upto_step_eq : forall arr i,
  0 <= i ->
  Znth i arr 0 = Znth (Zlength arr - 1 - i) arr 0 ->
  count_half_mismatches_upto (i + 1) arr =
    count_half_mismatches_upto i arr.
Proof.
  intros arr i Hi Heq.
  unfold count_half_mismatches_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite Heq.
  rewrite Z.eqb_refl.
  lia.
Qed.

Lemma count_half_mismatches_upto_step_neq : forall arr i,
  0 <= i ->
  Znth i arr 0 <> Znth (Zlength arr - 1 - i) arr 0 ->
  count_half_mismatches_upto (i + 1) arr =
    count_half_mismatches_upto i arr + 1.
Proof.
  intros arr i Hi Hneq.
  unfold count_half_mismatches_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  destruct (Z.eqb (Znth i arr 0) (Znth (Zlength arr - 1 - i) arr 0)) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - lia.
Qed.

Lemma problem_73_spec_z_of_exit : forall arr i out,
  0 <= i ->
  2 * i <= Zlength arr ->
  i >= Zlength arr - 1 - i ->
  out = count_half_mismatches_upto i arr ->
  problem_73_spec_z arr out.
Proof.
  intros arr i out Hi Hbound Hexit Hout.
  exists i.
  auto.
Qed.
