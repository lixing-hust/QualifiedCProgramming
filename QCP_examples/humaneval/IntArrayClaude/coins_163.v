Load "../spec/163".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition digit_candidates : list Z := [2; 4; 6; 8].

Definition generate_prefix_list (lo i : Z) : list Z :=
  filter (fun d => andb (lo <=? d) (d <? i)) digit_candidates.

Definition generate_list (lo hi : Z) : list Z :=
  generate_prefix_list lo (hi + 1).

Definition generate_bounds (a0 b0 a b : Z) : Prop :=
  a = Z.min a0 b0 /\ b = Z.max a0 b0.

Definition z_min (a b : Z) : Z := Z.min a b.

Definition z_max (a b : Z) : Z := Z.max a b.

Definition generate_prefix (lo i hi : Z) (output : list Z) : Prop :=
  lo <= i <= hi + 1 /\
  output = generate_prefix_list lo i.

Lemma filter_length_le_nat : forall {A: Type} (f: A -> bool) (l: list A),
  (length (filter f l) <= length l)%nat.
Proof.
  intros A f l.
  induction l as [| x xs IH]; simpl; [lia|].
  destruct (f x); simpl; lia.
Qed.

Lemma generate_prefix_length_le_4 : forall lo i hi output,
  generate_prefix lo i hi output ->
  Zlength output <= 4.
Proof.
  intros lo i hi output [_ Hout].
  rewrite Hout.
  unfold generate_prefix_list, digit_candidates.
  simpl.
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  end;
  simpl;
  repeat (rewrite Zlength_cons || rewrite Zlength_nil);
  lia.
Qed.

Definition problem_163_pre_z (a b : Z) : Prop :=
  problem_163_pre (Z.to_nat a) (Z.to_nat b).

Definition problem_163_spec_z (a b : Z) (output : list Z) : Prop :=
  output = generate_list (Z.min a b) (Z.max a b).

Lemma generate_prefix_init : forall lo hi,
  0 < lo ->
  lo <= hi + 1 ->
  generate_prefix lo lo hi nil.
Proof.
  intros.
  unfold generate_prefix, generate_prefix_list, digit_candidates.
  split; [lia|].
  simpl.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
  end; simpl; try reflexivity; lia.
Qed.

Lemma positive_even_digit_cases : forall i,
  0 < i ->
  i < 10 ->
  Z.even i = true ->
  i = 2 \/ i = 4 \/ i = 6 \/ i = 8.
Proof.
  intros i Hpos Hlt Heven.
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  assert (1 <= k <= 4) by lia.
  lia.
Qed.

Lemma generate_prefix_take : forall lo i hi output,
  0 < lo ->
  generate_prefix lo i hi output ->
  lo <= i <= hi ->
  i < 10 ->
  Z.even i = true ->
  generate_prefix lo (i + 1) hi (output ++ [i]).
Proof.
  intros lo i hi output Hlo [Hbounds Hout] Hi Hlt Heven.
  subst output.
  pose proof (positive_even_digit_cases i ltac:(lia) Hlt Heven) as Hcases.
  unfold generate_prefix, generate_prefix_list, digit_candidates in *.
  split; [lia|].
  destruct Hcases as [-> | [-> | [-> | ->]]];
    simpl;
    repeat match goal with
    | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
    | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
    end;
    simpl; try lia; reflexivity.
Qed.

Lemma generate_prefix_skip : forall lo i hi output,
  0 < lo ->
  generate_prefix lo i hi output ->
  lo <= i <= hi ->
  ~ (i < 10 /\ Z.even i = true) ->
  generate_prefix lo (i + 1) hi output.
Proof.
  intros lo i hi output Hlo [Hbounds Hout] Hi Hskip.
  subst output.
  unfold generate_prefix, generate_prefix_list, digit_candidates in *.
  split; [lia|].
  simpl.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
  end;
  simpl; try reflexivity;
  exfalso; apply Hskip; split; try lia;
  assert (i = 2 \/ i = 4 \/ i = 6 \/ i = 8) by lia;
  destruct H as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma generate_prefix_full_spec : forall a0 b0 lo hi output,
  generate_bounds a0 b0 lo hi ->
  generate_prefix lo (hi + 1) hi output ->
  problem_163_spec_z a0 b0 output.
Proof.
  intros a0 b0 lo hi output [Hlo Hhi] [_ Hout].
  subst lo hi output.
  unfold problem_163_spec_z, generate_list.
  reflexivity.
Qed.

Lemma mod2_zero_even_true : forall i,
  i mod 2 = 0 ->
  Z.even i = true.
Proof.
  intros i Hmod.
  rewrite Zeven_mod.
  apply Zeq_is_eq_bool.
  exact Hmod.
Qed.

Lemma mod2_nonzero_even_false : forall i,
  i mod 2 <> 0 ->
  Z.even i <> true.
Proof.
  intros i Hmod Heven.
  apply Hmod.
  rewrite Zmod_even.
  rewrite Heven.
  reflexivity.
Qed.
