Load "../spec/114".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition LLONG_MIN : Z := -9223372036854775808.
Definition LLONG_MAX : Z := 9223372036854775807.

Definition problem_114_pre_z (nums : list Z) : Prop :=
  problem_114_pre nums.

Fixpoint min_suffix_prefix_nat (n : nat) (nums : list Z) : Z :=
  match n with
  | O => 0
  | S O => Znth 0 nums 0
  | S n' =>
      let prev := min_suffix_prefix_nat n' nums in
      let x := Znth (Z.of_nat n') nums 0 in
      if Z.ltb prev 0 then prev + x else x
  end.

Definition min_suffix_prefix (i : Z) (nums : list Z) : Z :=
  min_suffix_prefix_nat (Z.to_nat i) nums.

Fixpoint min_subarray_prefix_nat (n : nat) (nums : list Z) : Z :=
  match n with
  | O => 0
  | S O => Znth 0 nums 0
  | S n' =>
      let prev_min := min_subarray_prefix_nat n' nums in
      let cur := min_suffix_prefix_nat (S n') nums in
      if Z.ltb cur prev_min then cur else prev_min
  end.

Definition min_subarray_prefix (i : Z) (nums : list Z) : Z :=
  min_subarray_prefix_nat (Z.to_nat i) nums.

Definition problem_114_spec_z (nums : list Z) (result : Z) : Prop :=
  result = min_subarray_prefix (Zlength nums) nums.

Definition list_int64_range (nums : list Z) : Prop :=
  forall i, 0 <= i < Zlength nums -> LLONG_MIN <= Znth i nums 0 <= LLONG_MAX.

Definition kadane_int64_range (nums : list Z) : Prop :=
  list_int64_range nums /\
  (forall i,
      1 <= i < Zlength nums ->
      LLONG_MIN <= min_suffix_prefix i nums + Znth i nums 0 <= LLONG_MAX) /\
  (forall i,
      1 <= i <= Zlength nums ->
      LLONG_MIN <= min_suffix_prefix i nums <= LLONG_MAX /\
      LLONG_MIN <= min_subarray_prefix i nums <= LLONG_MAX).

Lemma min_suffix_prefix_1 : forall nums,
  min_suffix_prefix 1 nums = Znth 0 nums 0.
Proof.
  reflexivity.
Qed.

Lemma min_subarray_prefix_1 : forall nums,
  min_subarray_prefix 1 nums = Znth 0 nums 0.
Proof.
  reflexivity.
Qed.

Lemma min_suffix_prefix_step_lt : forall nums i,
  1 <= i ->
  min_suffix_prefix i nums < 0 ->
  min_suffix_prefix (i + 1) nums =
    min_suffix_prefix i nums + Znth i nums 0.
Proof.
  intros nums i Hi Hlt.
  unfold min_suffix_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  replace (Z.of_nat (S n)) with i by lia.
  change match n with
         | O => Znth 0 nums 0
         | S _ =>
             if min_suffix_prefix_nat n nums <? 0
             then min_suffix_prefix_nat n nums + Znth (Z.of_nat n) nums 0
             else Znth (Z.of_nat n) nums 0
         end with (min_suffix_prefix_nat (S n) nums).
  assert ((min_suffix_prefix_nat (S n) nums <? 0) = true) as Htrue.
  { apply Z.ltb_lt. unfold min_suffix_prefix in Hlt.
    replace (Z.to_nat i) with (S n) in Hlt by lia. exact Hlt. }
  rewrite Htrue.
  reflexivity.
Qed.

Lemma min_suffix_prefix_step_ge : forall nums i,
  1 <= i ->
  min_suffix_prefix i nums >= 0 ->
  min_suffix_prefix (i + 1) nums = Znth i nums 0.
Proof.
  intros nums i Hi Hge.
  unfold min_suffix_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  replace (Z.of_nat (S n)) with i by lia.
  change match n with
         | O => Znth 0 nums 0
         | S _ =>
             if min_suffix_prefix_nat n nums <? 0
             then min_suffix_prefix_nat n nums + Znth (Z.of_nat n) nums 0
             else Znth (Z.of_nat n) nums 0
         end with (min_suffix_prefix_nat (S n) nums).
  assert ((min_suffix_prefix_nat (S n) nums <? 0) = false) as Hfalse.
  { apply Z.ltb_ge. unfold min_suffix_prefix in Hge.
    replace (Z.to_nat i) with (S n) in Hge by lia. lia. }
  rewrite Hfalse.
  reflexivity.
Qed.

Lemma min_subarray_prefix_nat_step_lt : forall nums n cur,
  cur = min_suffix_prefix_nat (S (S n)) nums ->
  cur < min_subarray_prefix_nat (S n) nums ->
  min_subarray_prefix_nat (S (S n)) nums = cur.
Proof.
  intros nums n cur Hcur Hlt.
  cbn [min_subarray_prefix_nat].
  rewrite <- Hcur.
  set (prev :=
    match n with
    | O => Znth 0 nums 0
    | S _ =>
        if min_suffix_prefix_nat (S n) nums <? min_subarray_prefix_nat n nums
        then min_suffix_prefix_nat (S n) nums
        else min_subarray_prefix_nat n nums
    end).
  change (min_subarray_prefix_nat (S n) nums) with prev in Hlt.
  assert ((cur <? prev) = true) as Htrue.
  { apply Z.ltb_lt. exact Hlt. }
  rewrite Htrue.
  reflexivity.
Qed.

Lemma min_subarray_prefix_nat_step_ge : forall nums n cur,
  cur = min_suffix_prefix_nat (S (S n)) nums ->
  cur >= min_subarray_prefix_nat (S n) nums ->
  min_subarray_prefix_nat (S (S n)) nums = min_subarray_prefix_nat (S n) nums.
Proof.
  intros nums n cur Hcur Hge.
  cbn [min_subarray_prefix_nat].
  rewrite <- Hcur.
  set (prev :=
    match n with
    | O => Znth 0 nums 0
    | S _ =>
        if min_suffix_prefix_nat (S n) nums <? min_subarray_prefix_nat n nums
        then min_suffix_prefix_nat (S n) nums
        else min_subarray_prefix_nat n nums
    end).
  change (min_subarray_prefix_nat (S n) nums) with prev in Hge.
  assert ((cur <? prev) = false) as Hfalse.
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse.
  reflexivity.
Qed.

Lemma min_subarray_prefix_step_lt : forall nums i cur,
  1 <= i ->
  cur = min_suffix_prefix (i + 1) nums ->
  cur < min_subarray_prefix i nums ->
  min_subarray_prefix (i + 1) nums = cur.
Proof.
  intros nums i cur Hi Hcur Hlt.
  unfold min_subarray_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  apply (min_subarray_prefix_nat_step_lt nums n cur).
  - replace (Z.of_nat (S n)) with i by lia.
    unfold min_suffix_prefix in Hcur.
    replace (Z.to_nat (i + 1)) with (S (S n)) in Hcur by lia.
    exact Hcur.
  - unfold min_subarray_prefix in Hlt.
    replace (Z.to_nat i) with (S n) in Hlt by lia.
    exact Hlt.
Qed.

Lemma min_subarray_prefix_step_ge : forall nums i cur,
  1 <= i ->
  cur = min_suffix_prefix (i + 1) nums ->
  cur >= min_subarray_prefix i nums ->
  min_subarray_prefix (i + 1) nums = min_subarray_prefix i nums.
Proof.
  intros nums i cur Hi Hcur Hge.
  unfold min_subarray_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  apply (min_subarray_prefix_nat_step_ge nums n cur).
  - replace (Z.of_nat (S n)) with i by lia.
    unfold min_suffix_prefix in Hcur.
    replace (Z.to_nat (i + 1)) with (S (S n)) in Hcur by lia.
    exact Hcur.
  - unfold min_subarray_prefix in Hge.
    replace (Z.to_nat i) with (S n) in Hge by lia.
    lia.
Qed.
