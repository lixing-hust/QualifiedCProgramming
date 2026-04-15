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
From SimpleC.EE Require Import C_25_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_25.
Local Open Scope sac.

Lemma proof_of_factorize_entail_wit_1 : factorize_entail_wit_1.
Proof.
  pre_process.
  subst.
  Exists (@nil Z) 0.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite IntArray.seg_empty.
  entailer!.
  unfold factorize_loop_state.
  rewrite Zlength_nil.
  simpl.
  repeat split; try lia; try constructor.
  - destruct n0; reflexivity.
  - unfold no_small_factor.
    intros d Hd.
    lia.
Qed.

Lemma proof_of_factorize_entail_wit_2_1 : factorize_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hq_pos: 2 <= n ÷ i) by lia.
  assert (Hq_le_n0: n ÷ i <= n0).
  { assert (Hq_lt: n ÷ i < n) by (apply Z.quot_lt; lia).
    lia. }
  assert (Hsize_next: size_2 + 1 < n0).
  { assert (Hq_ge_1: 1 <= n ÷ i) by lia.
    lia. }
  assert (Hsum_next: size_2 + 1 + n ÷ i <= n0).
  { assert (Hquot_exact: n = i * (n ÷ i)).
    { apply Z.quot_exact; lia. }
    nia. }
  Exists (factors_2 ++ i :: nil) (size_2 + 1).
  entailer!.
  - sep_apply (IntArray.seg_single data size_2 i).
    sep_apply (IntArray.seg_merge_to_seg data 0 size_2 (size_2 + 1)
                 factors_2 (i :: nil)).
    entailer!.
    lia.
  - unfold factorize_loop_state in *.
    destruct H12 as
      [? [? [? [HForall [Hprod [Hsorted [Hprime [Hle_i [Hle_n Hsmall]]]]]]]]].
    assert (Hexact : n = i * (n ÷ i)).
    { apply Z.quot_exact; lia. }
    assert (Hi_prime : zprime i).
    { eapply divisor_prime_from_no_small; eauto; lia. }
    replace (i - 1 + 1) with i by lia.
    rewrite Zlength_app.
    change (Zlength (i :: nil)) with 1.
    repeat split; try lia.
    + apply Forall_app_intro_local; [exact HForall | constructor; [lia | constructor]].
    + rewrite zprod_app. simpl. rewrite Z.mul_1_r. nia.
    + apply sorted_append_last; assumption.
    + apply Forall_app_intro_local; [exact Hprime | constructor; [exact Hi_prime | constructor]].
    + apply Forall_app_intro_local; [exact Hle_i | constructor; [lia | constructor]].
    + apply Forall_app_intro_local.
      * apply Forall_le_bound_trans with (a := i); assumption.
      * constructor; [lia | constructor].
    + apply no_small_factor_after_div; assumption || lia.
  - rewrite Zlength_app.
    change (Zlength (i :: nil)) with 1.
    lia.
Qed.

Lemma proof_of_factorize_entail_wit_2_2 : factorize_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hi_next: i + 1 <= n0).
  { assert (Hq_lt: n ÷ i < n) by (apply Z.quot_lt; lia).
    lia. }
  Exists factors_2 size_2.
  entailer!.
  unfold factorize_loop_state in *.
  destruct H12 as
    [? [? [? [HForall [Hprod [Hsorted [Hprime [Hle_i [Hle_n Hsmall]]]]]]]]].
  repeat split; try lia; try assumption.
  - apply Forall_le_bound_trans with (a := i); assumption || lia.
  - apply no_small_factor_after_skip; assumption || lia.
Qed.

Lemma proof_of_factorize_return_wit_1 : factorize_return_wit_1.
Proof.
  pre_process.
  Exists data_2 (factors ++ n :: nil) (size + 1).
  entailer!.
  - sep_apply (IntArray.seg_single data_2 size n).
    sep_apply (IntArray.seg_merge_to_seg data_2 0 size (size + 1)
                 factors (n :: nil)).
    entailer!.
    lia.
  - unfold factorize_loop_state in H11.
    destruct H11 as
      [? [? [? [HForall [Hprod [Hsorted [Hprime [Hle_i [Hle_n Hsmall]]]]]]]]].
    apply problem_25_spec_z_of_state_exit; try assumption; try lia.
    apply final_prime_from_no_small_exit with (i := i); assumption || lia.
  - rewrite Zlength_app.
    change (Zlength (n :: nil)) with 1.
    lia.
Qed.
