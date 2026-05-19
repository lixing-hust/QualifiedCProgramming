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
  (result = 1 /\ problem_109_spec arr true) \/
  (result = 0 /\ problem_109_spec arr false).

Definition cyclic_result_bool (arr : list Z) : bool :=
  if Z.ltb (cyclic_descents arr) 2 then true else false.

Definition descents_int_range (arr : list Z) : Prop :=
  (forall i,
      1 <= i < Zlength arr ->
      INT_MIN <= count_descents_prefix i arr + 1 <= INT_MAX) /\
  INT_MIN <= cyclic_descents arr <= INT_MAX /\
  problem_109_spec arr (cyclic_result_bool arr).

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

Lemma problem_109_spec_z_of_cyclic_true : forall arr,
  descents_int_range arr ->
  cyclic_descents arr < 2 ->
  problem_109_spec_z arr 1.
Proof.
  intros arr Hrange Hcyc.
  unfold problem_109_spec_z.
  left.
  split; [reflexivity |].
  unfold descents_int_range in Hrange.
  destruct Hrange as [_ [_ Hspec]].
  unfold cyclic_result_bool in Hspec.
  assert ((cyclic_descents arr <? 2) = true) as Hltb by (apply Z.ltb_lt; exact Hcyc).
  rewrite Hltb in Hspec.
  exact Hspec.
Qed.

Lemma problem_109_spec_z_of_cyclic_false : forall arr,
  descents_int_range arr ->
  cyclic_descents arr >= 2 ->
  problem_109_spec_z arr 0.
Proof.
  intros arr Hrange Hcyc.
  unfold problem_109_spec_z.
  right.
  split; [reflexivity |].
  unfold descents_int_range in Hrange.
  destruct Hrange as [_ [_ Hspec]].
  unfold cyclic_result_bool in Hspec.
  assert ((cyclic_descents arr <? 2) = false) as Hltb by (apply Z.ltb_ge; lia).
  rewrite Hltb in Hspec.
  exact Hspec.
Qed.
