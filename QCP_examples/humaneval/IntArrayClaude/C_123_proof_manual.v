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
From SimpleC.EE Require Import C_123_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_123.
Local Open Scope sac.

Lemma proof_of_get_odd_collatz_entail_wit_1 : get_odd_collatz_entail_wit_1.
Proof.
  pre_process.
  Exists (cons 1 nil).
  sep_apply (IntArray.seg_single retval_2 0 1).
  entailer!.
  - apply problem_123_pre_z_initial in H1.
    tauto.
  - apply problem_123_pre_z_initial in H1.
    lia.
  - apply problem_123_pre_z_initial in H1.
    lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_2 : get_odd_collatz_entail_wit_2.
Proof.
  pre_process.
  Exists output_l_2.
  pose proof (collatz_step_safe_of_pre n_pre n output_l_2 H2 H8) as [_ [Hnext [Hroom _]]].
  entailer!.
  all: try lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_4 : get_odd_collatz_entail_wit_4.
Proof.
  pre_process.
  Exists (output_l_2 ++ n :: nil).
  sep_apply (IntArray.seg_single data output_size n).
  sep_apply (IntArray.seg_merge_to_seg data 0 output_size (output_size + 1)); [ | lia].
  pose proof (collatz_step_safe_of_pre n_pre n output_l_2 H3 H12) as [_ [Hnext _]].
  entailer!.
  - apply odd_collatz_odd_quot_step; try assumption; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_5_1 : get_odd_collatz_entail_wit_5_1.
Proof.
  pre_process.
  Exists output_l_2.
  pose proof (collatz_step_safe_of_pre n_pre n output_l_2 H3 H15) as [_ [_ [_ Heven_bounds]]].
  assert (Hmod : n mod 2 = 0) by (apply Z_rem_2_neq_1_to_mod_0; lia).
  assert (Hdiv : n ÷ 2 = n / 2) by (apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply odd_collatz_even_quot_step; assumption.
Qed.

Lemma proof_of_get_odd_collatz_entail_wit_7 : get_odd_collatz_entail_wit_7.
Proof.
  pre_process.
  Exists sorted_full_l sorted_l_2 output_l_2.
  entailer!.
  apply problem_123_spec_z_of_sorted with (raw_l := output_l_2); assumption.
Qed.

Lemma proof_of_get_odd_collatz_return_wit_1 : get_odd_collatz_return_wit_1.
Proof.
  pre_process.
  Exists data_l_2 sorted_l output_size_2 data_2.
  entailer!.
Qed.
