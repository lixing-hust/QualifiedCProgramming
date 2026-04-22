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
From SimpleC.EE.CAV.verify_20260421_045730_count_multiples Require Import count_multiples_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import count_multiples.
Local Open Scope sac.

Lemma count_multiples_spec_0_local :
  forall k, count_multiples_spec 0 k = 0.
Proof.
  intros.
  unfold count_multiples_spec.
  simpl.
  reflexivity.
Qed.

Lemma count_multiples_nat_pred_succ_local :
  forall i, 1 <= i -> Z.to_nat i = S (Z.to_nat (i - 1)).
Proof.
  intros i Hi.
  symmetry.
  rewrite <- Z2Nat.inj_succ by lia.
  f_equal.
  lia.
Qed.

Lemma count_multiples_last_index_local :
  forall i, 1 <= i -> Z.of_nat (S (Z.to_nat (i - 1))) = i.
Proof.
  intros i Hi.
  rewrite Nat2Z.inj_succ.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma count_multiples_spec_step_eq_local :
  forall i k,
    1 <= i ->
    Z.rem i k = 0 ->
    count_multiples_spec i k = count_multiples_spec (i - 1) k + 1.
Proof.
  intros i k Hi Hrem.
  unfold count_multiples_spec.
  rewrite (count_multiples_nat_pred_succ_local i Hi).
  simpl.
  change (Z.pos (Pos.of_succ_nat (Z.to_nat (i - 1))))
    with (Z.of_nat (S (Z.to_nat (i - 1)))).
  rewrite (count_multiples_last_index_local i Hi).
  destruct (Z.eq_dec (Z.rem i k) 0); lia.
Qed.

Lemma count_multiples_spec_step_neq_local :
  forall i k,
    1 <= i ->
    Z.rem i k <> 0 ->
    count_multiples_spec i k = count_multiples_spec (i - 1) k.
Proof.
  intros i k Hi Hrem.
  unfold count_multiples_spec.
  rewrite (count_multiples_nat_pred_succ_local i Hi).
  simpl.
  change (Z.pos (Pos.of_succ_nat (Z.to_nat (i - 1))))
    with (Z.of_nat (S (Z.to_nat (i - 1)))).
  rewrite (count_multiples_last_index_local i Hi).
  destruct (Z.eq_dec (Z.rem i k) 0); lia.
Qed.

Lemma proof_of_count_multiples_entail_wit_1 : count_multiples_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_count_multiples_entail_wit_2_1 : count_multiples_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  replace ((i + 1) - 1) with i by lia.
  rewrite count_multiples_spec_step_eq_local by lia.
  lia.
Qed.

Lemma proof_of_count_multiples_entail_wit_2_2 : count_multiples_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  replace ((i + 1) - 1) with i by lia.
  rewrite count_multiples_spec_step_neq_local by lia.
  lia.
Qed.
