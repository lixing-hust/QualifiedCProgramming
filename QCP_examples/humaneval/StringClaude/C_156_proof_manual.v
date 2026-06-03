Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_156_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_156.
Local Open Scope sac.

Lemma proof_of_append_roman_digit_return_wit_1 : append_roman_digit_return_wit_1.
Proof.
  unfold append_roman_digit_return_wit_1.
  intros. pre_process.
  assert (digit_pre = 9) by lia; subst digit_pre.
  Exists (one_pre :: ten_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1) with (pos_pre + 2) by lia.
  rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_2 : append_roman_digit_return_wit_2.
Proof.
  unfold append_roman_digit_return_wit_2.
  intros. pre_process. subst digit_pre.
  Exists (five_pre :: one_pre :: one_pre :: one_pre :: nil).
  entailer!.
  replace (((pos_pre + 1 + 1 + 1) + 1)) with (pos_pre + 4) by lia.
  replace (pos_pre + 3 + 1) with (pos_pre + 4) by lia.
  repeat rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_3 : append_roman_digit_return_wit_3.
Proof.
  unfold append_roman_digit_return_wit_3.
  intros. pre_process. subst digit_pre.
  Exists (five_pre :: one_pre :: one_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1 + 1) with (pos_pre + 3) by lia.
  replace (pos_pre + 2 + 1) with (pos_pre + 3) by lia.
  repeat rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_4 : append_roman_digit_return_wit_4.
Proof.
  unfold append_roman_digit_return_wit_4.
  intros. pre_process. subst digit_pre.
  Exists (five_pre :: one_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1) with (pos_pre + 2) by lia.
  rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_5 : append_roman_digit_return_wit_5.
Proof.
  unfold append_roman_digit_return_wit_5.
  intros. pre_process. subst digit_pre.
  Exists (five_pre :: nil).
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_6 : append_roman_digit_return_wit_6.
Proof.
  unfold append_roman_digit_return_wit_6.
  intros. pre_process. subst digit_pre.
  Exists (one_pre :: five_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1) with (pos_pre + 2) by lia.
  rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_7 : append_roman_digit_return_wit_7.
Proof.
  unfold append_roman_digit_return_wit_7.
  intros. pre_process. subst digit_pre.
  Exists (one_pre :: one_pre :: one_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1 + 1) with (pos_pre + 3) by lia.
  replace (pos_pre + 2 + 1) with (pos_pre + 3) by lia.
  repeat rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_8 : append_roman_digit_return_wit_8.
Proof.
  unfold append_roman_digit_return_wit_8.
  intros. pre_process. subst digit_pre.
  Exists (one_pre :: one_pre :: nil).
  entailer!.
  replace (pos_pre + 1 + 1) with (pos_pre + 2) by lia.
  rewrite <- app_assoc. simpl.
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_9 : append_roman_digit_return_wit_9.
Proof.
  unfold append_roman_digit_return_wit_9.
  intros. pre_process. subst digit_pre.
  Exists (one_pre :: nil).
  entailer!.
Qed. 

Lemma proof_of_append_roman_digit_return_wit_10 : append_roman_digit_return_wit_10.
Proof.
  unfold append_roman_digit_return_wit_10.
  intros. pre_process. subst digit_pre.
  Exists (@nil Z).
  rewrite app_nil_r.
  entailer!.
  cbn; lia.
Qed. 

Lemma proof_of_int_to_mini_romank_entail_wit_1_1 : int_to_mini_romank_entail_wit_1_1.
Proof.
  unfold int_to_mini_romank_entail_wit_1_1.
  intros. pre_process. subst number_pre.
  unfold roman_thousand_z, roman_thousand_list_z.
  rewrite Z.eqb_refl.
  entailer!.
  rewrite (CharArray.full_unfold retval 1 nil 109).
  replace (0 + 1) with 1 by lia.
  rewrite (CharArray.seg_empty retval 1 1).
  entailer!.
Qed. 

Lemma proof_of_int_to_mini_romank_entail_wit_1_2 : int_to_mini_romank_entail_wit_1_2.
Proof.
  unfold int_to_mini_romank_entail_wit_1_2.
  intros. pre_process.
  unfold roman_thousand_z, roman_thousand_list_z.
  destruct (Z.eqb number_pre 1000) eqn:Hthousand.
  { apply Z.eqb_eq in Hthousand; lia. }
  rewrite (CharArray.full_empty retval 0).
  unfold CharArray.undef_full, CharArray.undef_seg, store_undef_array.
  replace (64 - 0) with 64 by lia.
  entailer!.
Qed. 

Lemma proof_of_int_to_mini_romank_entail_wit_2 : int_to_mini_romank_entail_wit_2.
Proof.
  unfold int_to_mini_romank_entail_wit_2.
  intros. pre_process.
  subst number.
  replace (number_pre ÷ 100) with (number_pre / 100) in H
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace ((number_pre / 100) % 10) with ((number_pre / 100) mod 10) in H
    by (symmetry; apply Z.rem_mod_nonneg; try apply Z.div_pos; lia).
  pose proof (roman_prefix1_step number_pre chunk ltac:(lia) H) as Hstep.
  unfold roman_prefix1_z.
  rewrite Hstep.
  entailer!.
  rewrite Zlength_app.
  unfold roman_digit_z in H; subst chunk.
  lia.
Qed. 

Lemma proof_of_int_to_mini_romank_entail_wit_3 : int_to_mini_romank_entail_wit_3.
Proof.
  unfold int_to_mini_romank_entail_wit_3.
  intros. pre_process.
  subst number.
  replace (number_pre ÷ 10) with (number_pre / 10) in H
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace ((number_pre / 10) % 10) with ((number_pre / 10) mod 10) in H
    by (symmetry; apply Z.rem_mod_nonneg; try apply Z.div_pos; lia).
  pose proof (roman_prefix2_step number_pre chunk ltac:(lia) H) as Hstep.
  unfold roman_prefix2_z.
  rewrite Hstep.
  entailer!.
  rewrite Zlength_app.
  unfold roman_digit_z in H; subst chunk.
  lia.
Qed. 

Lemma proof_of_int_to_mini_romank_entail_wit_4 : int_to_mini_romank_entail_wit_4.
Proof.
  unfold int_to_mini_romank_entail_wit_4.
  intros. pre_process.
  subst number.
  replace (number_pre % 10) with (number_pre mod 10) in H
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  pose proof (roman_output_step number_pre chunk H) as Hstep.
  unfold roman_output_z.
  rewrite Hstep.
  entailer!.
  - rewrite Zlength_app.
    lia.
  - pose proof (roman_output_z_length_bound number_pre
      (roman_output_list_z number_pre) ltac:(lia) ltac:(reflexivity)) as Hlen.
    rewrite Hstep in Hlen.
    rewrite Zlength_app in Hlen.
    unfold roman_digit_z in H; subst chunk.
    lia.
  - pose proof (roman_output_z_length_bound number_pre
      (roman_output_list_z number_pre) ltac:(lia) ltac:(reflexivity)) as Hlen.
    rewrite Hstep in Hlen.
    rewrite Zlength_app in Hlen.
    unfold roman_digit_z in H; subst chunk.
    lia.
Qed. 

Lemma proof_of_int_to_mini_romank_return_wit_1 : int_to_mini_romank_return_wit_1.
Proof.
  unfold int_to_mini_romank_return_wit_1.
  intros. pre_process.
  Exists (roman_output_list_z number_pre) k.
  entailer!.
  apply problem_156_spec_z_intro; try lia.
  assumption.
Qed. 

Lemma proof_of_int_to_mini_romank_partial_solve_wit_3_pure : int_to_mini_romank_partial_solve_wit_3_pure.
Proof.
  unfold int_to_mini_romank_partial_solve_wit_3_pure.
  intros. pre_process.
  subst number.
  replace ((number_pre ÷ 100) % 10) with ((number_pre / 100) mod 10)
    by (replace (number_pre ÷ 100) with (number_pre / 100)
          by (symmetry; apply Z.quot_div_nonneg; lia);
        symmetry; apply Z.rem_mod_nonneg; try apply Z.div_pos; lia).
  pose proof (roman_thousand_z_length_bound number_pre
    (roman_thousand_list_z number_pre) ltac:(lia) H6).
  pose proof (Z.mod_pos_bound (number_pre / 100) 10 ltac:(lia)).
  entailer!; try lia.
Qed. 

Lemma proof_of_int_to_mini_romank_partial_solve_wit_4_pure : int_to_mini_romank_partial_solve_wit_4_pure.
Proof.
  unfold int_to_mini_romank_partial_solve_wit_4_pure.
  intros. pre_process.
  subst number.
  replace ((number_pre ÷ 10) % 10) with ((number_pre / 10) mod 10)
    by (replace (number_pre ÷ 10) with (number_pre / 10)
          by (symmetry; apply Z.quot_div_nonneg; lia);
        symmetry; apply Z.rem_mod_nonneg; try apply Z.div_pos; lia).
  pose proof (roman_prefix1_z_length_bound number_pre
    (roman_prefix1_list_z number_pre) ltac:(lia) H6).
  pose proof (Z.mod_pos_bound (number_pre / 10) 10 ltac:(lia)).
  entailer!; try lia.
Qed. 

Lemma proof_of_int_to_mini_romank_partial_solve_wit_5_pure : int_to_mini_romank_partial_solve_wit_5_pure.
Proof.
  unfold int_to_mini_romank_partial_solve_wit_5_pure.
  intros. pre_process.
  subst number.
  replace (number_pre % 10) with (number_pre mod 10)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  pose proof (roman_prefix2_z_length_bound number_pre
    (roman_prefix2_list_z number_pre) ltac:(lia) H6).
  pose proof (Z.mod_pos_bound number_pre 10 ltac:(lia)).
  entailer!; try lia.
Qed. 
