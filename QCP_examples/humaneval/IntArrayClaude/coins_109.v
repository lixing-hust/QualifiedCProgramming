Load "../spec/109".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_109_pre_z (arr : list Z) : Prop :=
  problem_109_pre arr.

Fixpoint count_descents_prefix_nat (n : nat) (arr : list Z) : Z :=
  match n with
  | O => 0
  | S O => 0
  | S n' =>
      count_descents_prefix_nat n' arr +
      (if Z.ltb (Znth (Z.of_nat n') arr 0) (Znth (Z.of_nat n' - 1) arr 0)
       then 1
       else 0)
  end.

Definition count_descents_prefix (i : Z) (arr : list Z) : Z :=
  count_descents_prefix_nat (Z.to_nat i) arr.

Definition cyclic_descents (arr : list Z) : Z :=
  count_descents_prefix (Zlength arr) arr +
  (if Z.ltb (Znth 0 arr 0) (Znth (Zlength arr - 1) arr 0)
   then 1
   else 0).

Definition problem_109_spec_z (arr : list Z) (result : Z) : Prop :=
  (result <> 0 /\ cyclic_descents arr < 2) \/
  (result = 0 /\ cyclic_descents arr >= 2).

Definition descents_int_range (arr : list Z) : Prop :=
  (forall i,
      1 <= i < Zlength arr ->
      INT_MIN <= count_descents_prefix i arr + 1 <= INT_MAX) /\
  INT_MIN <= cyclic_descents arr <= INT_MAX.

Lemma count_descents_prefix_1 : forall arr,
  count_descents_prefix 1 arr = 0.
Proof.
  reflexivity.
Qed.

Lemma count_descents_prefix_step_lt : forall arr i,
  1 <= i ->
  Znth i arr 0 < Znth (i - 1) arr 0 ->
  count_descents_prefix (i + 1) arr =
    count_descents_prefix i arr + 1.
Proof.
  intros arr i Hi Hlt.
  unfold count_descents_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  change match Pos.of_succ_nat n with
         | (p~1)%positive => Z.pos p~0
         | (p~0)%positive => Z.pos (Pos.pred_double p)
         | 1%positive => 0
         end with (Z.of_nat (S n) - 1).
  replace (Z.of_nat (S n)) with i by lia.
  apply Z.ltb_lt in Hlt.
  rewrite Hlt.
  reflexivity.
Qed.

Lemma count_descents_prefix_step_ge : forall arr i,
  1 <= i ->
  Znth i arr 0 >= Znth (i - 1) arr 0 ->
  count_descents_prefix (i + 1) arr =
    count_descents_prefix i arr.
Proof.
  intros arr i Hi Hge.
  unfold count_descents_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  change match Pos.of_succ_nat n with
         | (p~1)%positive => Z.pos p~0
         | (p~0)%positive => Z.pos (Pos.pred_double p)
         | 1%positive => 0
         end with (Z.of_nat (S n) - 1).
  replace (Z.of_nat (S n)) with i by lia.
  assert ((Znth i arr 0 <? Znth (i - 1) arr 0) = false) as Hfalse.
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse.
  lia.
Qed.

Lemma cyclic_descents_tail_gt : forall arr,
  1 <= Zlength arr ->
  Znth (Zlength arr - 1) arr 0 > Znth 0 arr 0 ->
  cyclic_descents arr =
    count_descents_prefix (Zlength arr) arr + 1.
Proof.
  intros arr Hlen Hgt.
  unfold cyclic_descents.
  assert ((Znth 0 arr 0 <? Znth (Zlength arr - 1) arr 0) = true) as Htrue.
  { apply Z.ltb_lt. lia. }
  rewrite Htrue.
  reflexivity.
Qed.

Lemma cyclic_descents_tail_le : forall arr,
  1 <= Zlength arr ->
  Znth (Zlength arr - 1) arr 0 <= Znth 0 arr 0 ->
  cyclic_descents arr =
    count_descents_prefix (Zlength arr) arr.
Proof.
  intros arr Hlen Hle.
  unfold cyclic_descents.
  assert ((Znth 0 arr 0 <? Znth (Zlength arr - 1) arr 0) = false) as Hfalse.
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse.
  lia.
Qed.
