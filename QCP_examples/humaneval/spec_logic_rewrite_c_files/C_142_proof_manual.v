Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_142_goal.
From SimpleC.EE Require Import C_142_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_142.
Local Open Scope sac.

Lemma proof_of_sum_squares_safety_wit_6 : sum_squares_safety_wit_6.
Proof.
  right. pre_process. entailer!.
  subst sum.
  pose proof (sum_squares_int_range_step input_l i PreH7 PreH8 ltac:(lia))
    as (_ & Hadd & _).
  unfold transformed_entry_z_142 in Hadd.
  rewrite PreH1 in Hadd.
  cbn in Hadd.
  lia.
Qed.

Lemma proof_of_sum_squares_safety_wit_7 : sum_squares_safety_wit_7.
Proof.
  right. pre_process. entailer!.
  pose proof (sum_squares_int_range_square input_l i PreH7 PreH8 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_sum_squares_safety_wit_11 : sum_squares_safety_wit_11.
Proof.
  right. pre_process. entailer!.
  all:
    subst sum;
    pose proof (sum_squares_int_range_step input_l i PreH8 PreH9 ltac:(lia))
      as (_ & Hadd & _);
    unfold transformed_entry_z_142 in Hadd;
    destruct (Z.eqb (Z.rem i 3) 0) eqn:H3;
    [apply Z.eqb_eq in H3; contradiction|rewrite PreH1 in Hadd; cbn in Hadd; lia].
Qed.

Lemma proof_of_sum_squares_safety_wit_12 : sum_squares_safety_wit_12.
Proof.
  right. pre_process. entailer!.
  all:
    pose proof (sum_squares_int_range_cube input_l i PreH8 PreH9 ltac:(lia));
    lia.
Qed.

Lemma proof_of_sum_squares_safety_wit_13 : sum_squares_safety_wit_13.
Proof.
  right. pre_process. entailer!.
  all:
    pose proof (sum_squares_int_range_square input_l i PreH8 PreH9 ltac:(lia));
    lia.
Qed.

Lemma proof_of_sum_squares_safety_wit_14 : sum_squares_safety_wit_14.
Proof.
  right. pre_process. entailer!.
  all:
    subst sum;
    pose proof (sum_squares_int_range_step input_l i PreH8 PreH9 ltac:(lia))
      as (_ & Hadd & _);
    unfold transformed_entry_z_142 in Hadd;
    destruct (Z.eqb (Z.rem i 3) 0) eqn:H3;
    [apply Z.eqb_eq in H3; contradiction|];
    destruct (Z.eqb (Z.rem i 4) 0) eqn:H4;
    [apply Z.eqb_eq in H4; contradiction|cbn in Hadd; lia].
Qed.

Lemma proof_of_sum_squares_entail_wit_1 : sum_squares_entail_wit_1.
Proof.
  right. pre_process.
Qed.

Lemma proof_of_sum_squares_entail_wit_2_1 : sum_squares_entail_wit_2_1.
Proof.
  right. pre_process. entailer!.
  - entailer!.
    subst sum.
    symmetry. apply sum_prefix_142_step_plain; lia.
  - entailer!.
    subst sum.
    pose proof (sum_squares_int_range_step input_l i PreH8 PreH9 ltac:(lia))
      as (_ & Hadd & _).
    unfold transformed_entry_z_142 in Hadd.
    destruct (Z.eqb (Z.rem i 3) 0) eqn:H3.
    + apply Z.eqb_eq in H3. contradiction.
    + destruct (Z.eqb (Z.rem i 4) 0) eqn:H4.
      * apply Z.eqb_eq in H4. contradiction.
      * cbn in Hadd. lia.
  - entailer!.
    subst sum.
    pose proof (sum_squares_int_range_step input_l i PreH8 PreH9 ltac:(lia))
      as (_ & Hadd & _).
    unfold transformed_entry_z_142 in Hadd.
    destruct (Z.eqb (Z.rem i 3) 0) eqn:H3.
    + apply Z.eqb_eq in H3. contradiction.
    + destruct (Z.eqb (Z.rem i 4) 0) eqn:H4.
      * apply Z.eqb_eq in H4. contradiction.
      * cbn in Hadd. lia.
Qed.

Lemma proof_of_sum_squares_entail_wit_2_2 : sum_squares_entail_wit_2_2.
Proof.
  right. pre_process. entailer!.
  - entailer!.
    subst sum.
    symmetry. apply sum_prefix_142_step_mod4_not3; lia.
  - entailer!.
    subst sum.
    pose proof (sum_squares_int_range_step input_l i PreH8 PreH9 ltac:(lia))
      as (_ & Hadd & _).
    unfold transformed_entry_z_142 in Hadd.
    destruct (Z.eqb (Z.rem i 3) 0) eqn:H3.
    + apply Z.eqb_eq in H3. contradiction.
    + rewrite PreH1 in Hadd. cbn in Hadd. lia.
  - entailer!.
    subst sum.
    pose proof (sum_squares_int_range_step input_l i PreH8 PreH9 ltac:(lia))
      as (_ & Hadd & _).
    unfold transformed_entry_z_142 in Hadd.
    destruct (Z.eqb (Z.rem i 3) 0) eqn:H3.
    + apply Z.eqb_eq in H3. contradiction.
    + rewrite PreH1 in Hadd. cbn in Hadd. lia.
Qed.

Lemma proof_of_sum_squares_entail_wit_2_3 : sum_squares_entail_wit_2_3.
Proof.
  right. pre_process. entailer!.
  - entailer!.
    subst sum.
    symmetry. apply sum_prefix_142_step_mod3; lia.
  - entailer!.
    subst sum.
    pose proof (sum_squares_int_range_step input_l i PreH7 PreH8 ltac:(lia))
      as (_ & Hadd & _).
    unfold transformed_entry_z_142 in Hadd.
    rewrite PreH1 in Hadd. cbn in Hadd. lia.
Qed.

Lemma proof_of_sum_squares_return_wit_1 : sum_squares_return_wit_1.
Proof.
  right. pre_process. entailer!.
  subst sum.
  assert (i = Zlength input_l) by lia.
  subst i.
  apply sum_prefix_142_full_spec.
Qed.
