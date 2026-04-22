Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260421_035821_ways_to_reach Require Import ways_to_reach_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import ways_to_reach.
Local Open Scope sac.

Lemma ways_to_reach_nat_step : forall n,
  ways_to_reach_nat (S (S n)) =
  ways_to_reach_nat n + ways_to_reach_nat (S n).
Proof.
  intros n.
  unfold ways_to_reach_nat.
  simpl.
  destruct (ways_to_reach_pair n) as [a b].
  simpl.
  lia.
Qed.

Lemma ways_to_reach_z_step : forall z,
  2 <= z ->
  ways_to_reach_z z =
  ways_to_reach_z (z - 2) + ways_to_reach_z (z - 1).
Proof.
  intros z Hz.
  unfold ways_to_reach_z.
  pose (n := Z.to_nat (z - 2)).
  assert (Hn: Z.of_nat n = z - 2).
  { subst n. rewrite Z2Nat.id by lia. reflexivity. }
  assert (Hz2: z = Z.of_nat (S (S n))) by (simpl; lia).
  rewrite Hz2.
  replace (Z.to_nat (Z.of_nat (S (S n)))) with (S (S n)) by lia.
  replace (Z.to_nat (Z.of_nat (S (S n)) - 2)) with n by lia.
  replace (Z.to_nat (Z.of_nat (S (S n)) - 1)) with (S n) by lia.
  apply ways_to_reach_nat_step.
Qed.

Ltac split_ways_to_reach_index_0_45 z :=
  assert (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/
          z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/ z = 10 \/
          z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/
          z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/ z = 20 \/
          z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/
          z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/ z = 30 \/
          z = 31 \/ z = 32 \/ z = 33 \/ z = 34 \/ z = 35 \/
          z = 36 \/ z = 37 \/ z = 38 \/ z = 39 \/ z = 40 \/
          z = 41 \/ z = 42 \/ z = 43 \/ z = 44 \/ z = 45) by lia;
  repeat match goal with
  | H : z = _ \/ _ |- _ => destruct H as [H | H]; [subst z | idtac]
  | H : z = _ |- _ => subst z
  end.

Lemma ways_to_reach_z_int_bound_0_45 :
  forall z, 0 <= z <= 45 -> -2147483648 <= ways_to_reach_z z <= 2147483647.
Proof.
  intros z Hz.
  split_ways_to_reach_index_0_45 z; vm_compute; split; try discriminate; try reflexivity; try lia.
Qed.

Lemma proof_of_ways_to_reach_safety_wit_6 : ways_to_reach_safety_wit_6.
Proof.
  pre_process.
  entailer!.
  all:
    rewrite H2 in *;
    rewrite H3 in *;
    rewrite <- (ways_to_reach_z_step i) by lia;
    pose proof (ways_to_reach_z_int_bound_0_45 i) as Hbound;
    lia.
Qed.

Lemma proof_of_ways_to_reach_entail_wit_1 : ways_to_reach_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_ways_to_reach_entail_wit_2 : ways_to_reach_entail_wit_2.
Proof.
  pre_process.
  sep_apply store_int_undef_store_int.
  entailer!.
  - rewrite H2 in *.
    rewrite H3 in *.
    replace (i + 1 - 1) with i by lia.
    rewrite <- (ways_to_reach_z_step i) by lia.
    reflexivity.
  - rewrite H3 in *.
    replace (i + 1 - 2) with (i - 1) by lia.
    reflexivity.
Qed.

Lemma proof_of_ways_to_reach_return_wit_1 : ways_to_reach_return_wit_1.
Proof.
  pre_process.
  entailer!.
  subst n_pre.
  reflexivity.
Qed.
