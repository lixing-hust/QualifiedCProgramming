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
From SimpleC.EE.CAV.verify_20260420_221428_tribonacci Require Import tribonacci_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import tribonacci.
Local Open Scope sac.

Lemma tribonacci_nat_step : forall n,
  tribonacci_nat (S (S (S n))) =
    tribonacci_nat n + tribonacci_nat (S n) + tribonacci_nat (S (S n)).
Proof.
  intros n.
  unfold tribonacci_nat.
  simpl.
  destruct (tribonacci_triple n) as [[a b] c].
  simpl.
  lia.
Qed.

Lemma tribonacci_z_step : forall z,
  3 <= z ->
  tribonacci_z z =
    tribonacci_z (z - 3) + tribonacci_z (z - 2) + tribonacci_z (z - 1).
Proof.
  intros z Hz.
  unfold tribonacci_z.
  pose (n := Z.to_nat (z - 3)).
  assert (Hn: Z.of_nat n = z - 3).
  { subst n. rewrite Z2Nat.id by lia. reflexivity. }
  assert (Hz3: z = Z.of_nat (S (S (S n)))) by (simpl; lia).
  rewrite Hz3.
  replace (Z.to_nat (Z.of_nat (S (S (S n))))) with (S (S (S n))) by lia.
  replace (Z.to_nat (Z.of_nat (S (S (S n))) - 3)) with n by lia.
  replace (Z.to_nat (Z.of_nat (S (S (S n))) - 2)) with (S n) by lia.
  replace (Z.to_nat (Z.of_nat (S (S (S n))) - 1)) with (S (S n)) by lia.
  apply tribonacci_nat_step.
Qed.

Ltac split_trib_index_0_37 z :=
  assert (z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/
          z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/ z = 10 \/
          z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/
          z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/ z = 20 \/
          z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/
          z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/ z = 30 \/
          z = 31 \/ z = 32 \/ z = 33 \/ z = 34 \/ z = 35 \/
          z = 36 \/ z = 37) by lia;
  repeat match goal with
  | H : z = _ \/ _ |- _ => destruct H as [H | H]; [subst z | idtac]
  | H : z = _ |- _ => subst z
  end.

Lemma tribonacci_z_triple_sum_int_bound_3_37 :
  forall z,
    3 <= z <= 37 ->
    -2147483648 <=
      tribonacci_z (z - 3) + tribonacci_z (z - 2) + tribonacci_z (z - 1) <=
      2147483647.
Proof.
  intros z Hz.
  split_trib_index_0_37 z; vm_compute; split; try discriminate; try reflexivity; try lia.
Qed.

Lemma tribonacci_z_pair_sum_int_bound_3_37 :
  forall z,
    3 <= z <= 37 ->
    -2147483648 <= tribonacci_z (z - 3) + tribonacci_z (z - 2) <= 2147483647.
Proof.
  intros z Hz.
  split_trib_index_0_37 z; vm_compute; split; try discriminate; try reflexivity; try lia.
Qed.

Lemma proof_of_tribonacci_safety_wit_9 : tribonacci_safety_wit_9.
Proof.
  pre_process.
  entailer!.
  all:
    rewrite H2 in *;
    rewrite H3 in *;
    rewrite H4 in *;
    pose proof (tribonacci_z_triple_sum_int_bound_3_37 i) as Hbound;
    lia.
Qed.

Lemma proof_of_tribonacci_safety_wit_10 : tribonacci_safety_wit_10.
Proof.
  pre_process.
  entailer!.
  all:
    rewrite H2 in *;
    rewrite H3 in *;
    pose proof (tribonacci_z_pair_sum_int_bound_3_37 i) as Hbound;
    lia.
Qed.

Lemma proof_of_tribonacci_entail_wit_1 : tribonacci_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_tribonacci_entail_wit_2 : tribonacci_entail_wit_2.
Proof.
  pre_process.
  sep_apply store_int_undef_store_int.
  entailer!.
  - replace (i + 1 - 1) with i by lia.
    rewrite H2.
    rewrite H3.
    rewrite H4.
    pose proof (tribonacci_z_step i H0) as Hstep.
    rewrite Hstep.
    lia.
  - rewrite H4.
    replace (i + 1 - 2) with (i - 1) by lia.
    reflexivity.
  - rewrite H3.
    replace (i + 1 - 3) with (i - 2) by lia.
    reflexivity.
Qed.

Lemma proof_of_tribonacci_return_wit_1 : tribonacci_return_wit_1.
Proof.
  pre_process.
  entailer!.
  subst n_pre.
  reflexivity.
Qed.

Lemma proof_of_tribonacci_return_wit_2 : tribonacci_return_wit_2.
Proof.
  pre_process.
  entailer!.
  subst n_pre.
  reflexivity.
Qed.
