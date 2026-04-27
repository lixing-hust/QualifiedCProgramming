Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint sum_two_digit_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' =>
      let s := sum_two_digit_upto_nat n' l in
      let i := Z.of_nat n' in
      let x := Znth i l 0 in
      if Z.leb (-99) x && Z.leb x 99 then s + x else s
  end.

Definition sum_two_digit_upto (i : Z) (l : list Z) : Z :=
  sum_two_digit_upto_nat (Z.to_nat i) l.

Definition problem_122_pre_z (arr : list Z) (k : Z) : Prop :=
  arr <> [] /\ 1 <= k <= Zlength arr.

Definition problem_122_spec_z (arr : list Z) (k result : Z) : Prop :=
  result = sum_two_digit_upto k arr.

Definition sum_two_digit_int_range (k : Z) (arr : list Z) : Prop :=
  forall i,
    0 <= i ->
    i < k ->
    INT_MIN <= sum_two_digit_upto i arr <= INT_MAX /\
    INT_MIN <= sum_two_digit_upto i arr + Znth i arr 0 <= INT_MAX.

Lemma sum_two_digit_upto_0 : forall l,
  sum_two_digit_upto 0 l = 0.
Proof.
  intros l.
  unfold sum_two_digit_upto.
  reflexivity.
Qed.

Lemma sum_two_digit_upto_step_in : forall i l,
  0 <= i ->
  -99 <= Znth i l 0 ->
  Znth i l 0 <= 99 ->
  sum_two_digit_upto (i + 1) l =
  sum_two_digit_upto i l + Znth i l 0.
Proof.
  intros i l Hi Hlo Hhi.
  unfold sum_two_digit_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  assert ((-99 <=? Znth i l 0) = true) as Hleb_lo by (apply Z.leb_le; lia).
  assert ((Znth i l 0 <=? 99) = true) as Hleb_hi by (apply Z.leb_le; lia).
  rewrite Hleb_lo, Hleb_hi.
  reflexivity.
Qed.

Lemma sum_two_digit_upto_step_hi : forall i l,
  0 <= i ->
  Znth i l 0 > 99 ->
  sum_two_digit_upto (i + 1) l =
  sum_two_digit_upto i l.
Proof.
  intros i l Hi Hhi.
  unfold sum_two_digit_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  assert ((Znth i l 0 <=? 99) = false) as Hleb_hi by (apply Z.leb_gt; lia).
  rewrite Hleb_hi.
  destruct (-99 <=? Znth i l 0); reflexivity.
Qed.

Lemma sum_two_digit_upto_step_lo : forall i l,
  0 <= i ->
  Znth i l 0 < -99 ->
  sum_two_digit_upto (i + 1) l =
  sum_two_digit_upto i l.
Proof.
  intros i l Hi Hlo.
  unfold sum_two_digit_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  assert ((-99 <=? Znth i l 0) = false) as Hleb_lo by (apply Z.leb_gt; lia).
  rewrite Hleb_lo.
  reflexivity.
Qed.

Lemma problem_122_spec_z_of_exit : forall l k i s,
  i = k ->
  s = sum_two_digit_upto i l ->
  problem_122_spec_z l k s.
Proof.
  intros l k i s Hi Hs.
  subst i.
  unfold problem_122_spec_z.
  assumption.
Qed.
