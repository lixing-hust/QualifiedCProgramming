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
From SimpleC.EE.CAV.verify_20260421_143138_two_sum_sorted Require Import two_sum_sorted_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_two_sum_sorted_safety_wit_4 : two_sum_sorted_safety_wit_4.
Proof.
  pre_process; entailer!; try lia.
  all:
    match goal with
    | H : forall i j : Z,
          0 <= i < j /\ j < _ ->
          _ <= Znth i _ _ + Znth j _ _ <= _ |- _ =>
        pose proof (H left right ltac:(lia)) as Hrange;
        lia
    end.
Qed.

Lemma proof_of_two_sum_sorted_entail_wit_1 : two_sum_sorted_entail_wit_1.
Proof.
  pre_process; entailer!; try lia.
Qed.

Lemma proof_of_two_sum_sorted_entail_wit_2 : two_sum_sorted_entail_wit_2.
Proof.
  pre_process; entailer!; try lia.
Qed.

Lemma proof_of_two_sum_sorted_entail_wit_3 : two_sum_sorted_entail_wit_3.
Proof.
  pre_process; entailer!; try lia.
Qed.

Lemma proof_of_two_sum_sorted_entail_wit_4 : two_sum_sorted_entail_wit_4.
Proof.
  pre_process; entailer!; try lia.
Qed.

Lemma proof_of_two_sum_sorted_entail_wit_5_1 : two_sum_sorted_entail_wit_5_1.
Proof.
  pre_process; entailer!; try lia.
  - apply store_int_undef_store_int.
  - intros i j [[Hij Hj_bound] Hright].
    destruct (Z_lt_ge_dec right j) as [Hright_lt | Hright_ge].
    + apply H12. lia.
    + assert (j = right) by lia.
      subst j.
      destruct (Z_lt_ge_dec i left) as [Hi_left | Hleft_i].
      * apply H11. lia.
      * assert (Znth left l 0 <= Znth i l 0) as Hmono.
        {
          apply H9. lia.
        }
        lia.
Qed.

Lemma proof_of_two_sum_sorted_entail_wit_5_2 : two_sum_sorted_entail_wit_5_2.
Proof.
  pre_process; entailer!; try lia.
  - apply store_int_undef_store_int.
  - intros i j [[Hij Hj_bound] Hleft].
    destruct (Z_lt_ge_dec i left) as [Hi_left | Hleft_i].
    + apply H11. lia.
    + assert (i = left) by lia.
      subst i.
      destruct (Z_lt_ge_dec right j) as [Hright_j | Hj_right].
      * apply H12. lia.
      * assert (Znth j l 0 <= Znth right l 0) as Hmono.
        {
          apply H9. lia.
        }
        lia.
Qed.

Lemma proof_of_two_sum_sorted_return_wit_2 : two_sum_sorted_return_wit_2.
Proof.
  unfold two_sum_sorted_return_wit_2.
  intros. Intros.
  left.
  entailer!.
  split.
  - reflexivity.
  - split.
    + intros i j Hij.
      destruct (Z_lt_ge_dec i left) as [Hi_left | Hleft_i].
      * apply H9. lia.
      * apply H10. lia.
    + exact H16.
Qed.
