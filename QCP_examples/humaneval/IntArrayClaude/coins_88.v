Load "../spec/88".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import List_lemma ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import naive_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.

Definition problem_88_pre_z (input : list Z) : Prop :=
  problem_88_pre (map Z.to_nat input).

Definition sort_array_input_range (input : list Z) : Prop :=
  (forall i, 0 <= i < Zlength input -> 0 <= Znth i input 0 <= INT_MAX) /\
  (0 < Zlength input ->
   Znth 0 input 0 + Znth (Zlength input - 1) input 0 <= INT_MAX).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then Sorted Z.ge l else Sorted Z.le l.

Definition problem_88_spec_z (input output : list Z) : Prop :=
  Permutation input output /\
  match input with
  | [] => output = []
  | [x] => output = [x]
  | h :: _ =>
      let last_elem := last input h in
      if Z.eqb ((h + last_elem) mod 2) 1 then
        Sorted Z.le output
      else
        Sorted Z.ge output
  end.

Fixpoint copy_prefix_nat (n : nat) (input : list Z) : list Z :=
  match n with
  | O => []
  | S n' => copy_prefix_nat n' input ++ [Znth (Z.of_nat n') input 0]
  end.

Definition copy_prefix (n : Z) (input : list Z) : list Z :=
  copy_prefix_nat (Z.to_nat n) input.

Definition reverse_step (size i : Z) (l : list Z) : list Z :=
  replace_Znth (size - 1 - i) (Znth i l 0)
    (replace_Znth i (Znth (size - 1 - i) l 0) l).

Fixpoint reverse_loop_nat (size : Z) (n : nat) (l : list Z) : list Z :=
  match n with
  | O => l
  | S n' => reverse_step size (Z.of_nat n') (reverse_loop_nat size n' l)
  end.

Definition reverse_loop (size i : Z) (l : list Z) : list Z :=
  reverse_loop_nat size (Z.to_nat i) l.

Lemma reverse_loop_0 : forall size l,
  reverse_loop size 0 l = l.
Proof.
  reflexivity.
Qed.

Lemma replace_Znth_length_local {A : Type} :
  forall (l : list A) n a,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros l n a.
  unfold replace_Znth.
  remember (Z.to_nat n) as k; clear Heqk.
  revert k; induction l; intros k.
  - destruct k; simpl; reflexivity.
  - destruct k; simpl; repeat rewrite Zlength_cons; try rewrite IHl; lia.
Qed.

Lemma copy_prefix_Zlength : forall n input,
  0 <= n ->
  Zlength (copy_prefix n input) = n.
Proof.
  intros n input Hn.
  unfold copy_prefix.
  rewrite Zlength_correct.
  replace n with (Z.of_nat (Z.to_nat n)) at 2 by lia.
  revert input.
  induction (Z.to_nat n); intros; simpl.
  - reflexivity.
  - 
  rewrite app_length.
  simpl.
  rewrite Nat2Z.inj_add.
  simpl.
  rewrite IHn0.
  lia.
Qed.

Lemma copy_prefix_snoc : forall i input,
  0 <= i ->
  copy_prefix (i + 1) input = copy_prefix i input ++ [Znth i input 0].
Proof.
  intros i input Hi.
  unfold copy_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma sublist_snoc_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite Zlength_correct in Hi.
  pose proof (@sublist_split Z 0 (i + 1) i l ltac:(lia) ltac:(lia)) as Hsplit.
  rewrite Hsplit.
  rewrite (@sublist_single Z i l 0) by lia.
  reflexivity.
Qed.

Lemma copy_prefix_eq_sublist_nat : forall n input,
  Z.of_nat n <= Zlength input ->
  copy_prefix (Z.of_nat n) input = sublist 0 (Z.of_nat n) input.
Proof.
  induction n; intros input Hle.
  - reflexivity.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite copy_prefix_snoc by lia.
    rewrite sublist_snoc_Znth by lia.
    rewrite IHn by lia.
    reflexivity.
Qed.

Lemma copy_prefix_eq_sublist : forall input i,
  0 <= i <= Zlength input ->
  copy_prefix i input = sublist 0 i input.
Proof.
  intros input i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply copy_prefix_eq_sublist_nat.
  lia.
Qed.

Lemma copy_prefix_full : forall input,
  copy_prefix (Zlength input) input = input.
Proof.
  intros input.
  pose proof (Zlength_nonneg input).
  rewrite copy_prefix_eq_sublist by lia.
  apply sublist_self.
  reflexivity.
Qed.

Lemma reverse_step_Zlength : forall size i l,
  Zlength (reverse_step size i l) = Zlength l.
Proof.
  intros.
  unfold reverse_step.
  rewrite (@replace_Znth_length_local Z
             (replace_Znth i (Znth (size - 1 - i) l 0) l)
             (size - 1 - i) (Znth i l 0)).
  rewrite (@replace_Znth_length_local Z l i (Znth (size - 1 - i) l 0)).
  reflexivity.
Qed.

Lemma reverse_loop_Zlength : forall size i l,
  0 <= i ->
  Zlength (reverse_loop size i l) = Zlength l.
Proof.
  intros size i l Hi.
  unfold reverse_loop.
  replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia.
  revert size l.
  induction (Z.to_nat i); intros; simpl.
  - reflexivity.
  - rewrite reverse_step_Zlength.
    rewrite IHn.
    reflexivity.
Qed.

Lemma reverse_loop_snoc : forall size i l,
  0 <= i ->
  reverse_loop size (i + 1) l =
  reverse_step size i (reverse_loop size i l).
Proof.
  intros size i l Hi.
  unfold reverse_loop.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma problem_88_spec_nil :
  problem_88_spec_z [] [].
Proof.
  unfold problem_88_spec_z.
  split; constructor.
Qed.
