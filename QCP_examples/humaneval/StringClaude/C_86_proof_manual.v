Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_86_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_86.
Local Open Scope sac.

Lemma proof_of_anti_shuffle_entail_wit_1 : anti_shuffle_entail_wit_1.
Proof.
  pre_process.
  subst retval.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval_2 0 (len + 1)).
  2: lia.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval_3 0 (len + 1)).
  2: lia.
  rewrite (CharArray.full_empty retval_2 0).
  rewrite (CharArray.full_empty retval_3 0).
  entailer!.
  all: unfold anti_out_prefix_z, anti_cur_prefix_z; simpl;
    rewrite Zlength_nil; lia.
Qed. 

Lemma proof_of_anti_shuffle_entail_wit_2_1 : anti_shuffle_entail_wit_2_1.
Proof.
  pre_process.
  repeat match goal with
  | H : context[Znth i (app l (cons 0 nil)) 0] |- _ =>
      rewrite Znth_app_l_0_86 in H by lia
  end.
  rewrite Znth_app_l_0_86 by lia.
  match goal with
  | Hneq : Znth i l 0 <> 32 |- _ =>
      pose proof (anti_prefix_step_nonspace_86 i l ltac:(lia)
        (is_space_z_eq_false_86 _ Hneq)) as [Hout Hcur]
  end.
  rewrite Hout, Hcur.
  entailer!.
  all: repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
    repeat rewrite Zlength_nil; try rewrite <- Hout; try rewrite <- Hcur; lia.
Qed. 

Lemma proof_of_anti_shuffle_entail_wit_2_2 : anti_shuffle_entail_wit_2_2.
Proof.
  pre_process.
  repeat match goal with
  | H : context[Znth i (app l (cons 0 nil)) 0] |- _ =>
      rewrite Znth_app_l_0_86 in H by lia
  end.
  match goal with
  | Hspace : Znth i l 0 = 32 |- _ =>
      pose proof (anti_prefix_step_space_86 i l ltac:(lia)
        (is_space_z_eq_true_86 _ Hspace)) as [Hout Hcur]
  end.
  rewrite Hout, Hcur.
  rewrite (CharArray.full_empty cur 0).
  entailer!.
  all: repeat rewrite Zlength_app; repeat rewrite Zlength_cons;
    repeat rewrite Zlength_nil; try rewrite Zlength_sort_chars_z; lia.
Qed. 

Lemma proof_of_anti_shuffle_entail_wit_3 : anti_shuffle_entail_wit_3.
Proof.
  pre_process.
  assert (i = len) by lia.
  subst i.
  unfold anti_shuffle_output_z.
  entailer!.
  - rewrite Zlength_app, Zlength_sort_chars_z.
    lia.
  - apply problem_86_spec_z_anti_shuffle_output_86.
    assumption.
Qed. 

Lemma proof_of_anti_shuffle_return_wit_1 : anti_shuffle_return_wit_1.
Proof.
  pre_process.
  Exists (anti_shuffle_output_z l).
  entailer!.
Qed. 

Lemma proof_of_anti_shuffle_partial_solve_wit_8_pure : anti_shuffle_partial_solve_wit_8_pure.
Proof.
  pre_process.
  entailer!.
  rewrite Zlength_sort_chars_z.
  lia.
Qed. 

Lemma proof_of_anti_shuffle_partial_solve_wit_11_pure : anti_shuffle_partial_solve_wit_11_pure.
Proof.
  pre_process.
  assert (i = len) by lia.
  subst i.
  entailer!.
  all: try rewrite Zlength_sort_chars_z; lia.
Qed. 

Lemma proof_of_anti_shuffle_partial_solve_wit_12_pure : anti_shuffle_partial_solve_wit_12_pure.
Proof.
  pre_process.
  assert (i = len) by lia.
  subst i.
  entailer!.
  rewrite Zlength_sort_chars_z.
  lia.
Qed. 
