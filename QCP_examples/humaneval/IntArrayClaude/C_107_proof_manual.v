Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_107_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_107.
Local Open Scope sac.

Lemma proof_of_is_pal_safety_wit_3 : is_pal_safety_wit_3.
Proof.
  pre_process.
  unfold pal_reverse_loop_state in H2.
  destruct H2 as [_ [fuel [[Ht_nonneg _] [Hr_bounds _]]]].
  assert (Hrem_bounds: 0 <= t % 10 < 10).
  { apply Z.rem_bound_pos; lia. }
  entailer!.
Qed.

Lemma proof_of_is_pal_safety_wit_5 : is_pal_safety_wit_5.
Proof.
  pre_process.
  unfold pal_reverse_loop_state in H2.
  destruct H2 as [_ [fuel [_ [Hr_bounds _]]]].
  entailer!.
Qed.

Lemma proof_of_is_pal_entail_wit_1 : is_pal_entail_wit_1.
Proof.
  pre_process.
  subst x_pre.
  entailer!.
  apply pal_reverse_loop_state_init.
  lia.
Qed.

Lemma proof_of_is_pal_entail_wit_2 : is_pal_entail_wit_2.
Proof.
  pre_process.
  assert (Ht_nonneg: 0 <= t)
    by (unfold pal_reverse_loop_state in H2;
        destruct H2 as [_ [fuel [[Ht_nonneg _] _]]]; lia).
  assert (t ÷ 10 = t / 10) as Hquot
    by (apply Z.quot_div_nonneg; lia).
  assert (t % 10 = t mod 10) as Hrem
    by (apply Z.rem_mod_nonneg; lia).
  rewrite Hquot, Hrem.
  entailer!.
  apply pal_reverse_loop_state_step; auto.
Qed.

Lemma proof_of_is_pal_return_wit_1 : is_pal_return_wit_1.
Proof.
  pre_process.
  assert (Ht0: t = 0)
    by (unfold pal_reverse_loop_state in H3;
        destruct H3 as [_ [fuel [[Ht_nonneg _] _]]]; lia).
  subst t.
  entailer!.
  symmetry.
  apply is_pal_z_correct_true; try lia.
  pose proof (pal_reverse_loop_state_final x0 r H3).
  lia.
Qed.

Lemma proof_of_is_pal_return_wit_2 : is_pal_return_wit_2.
Proof.
  pre_process.
  assert (Ht0: t = 0)
    by (unfold pal_reverse_loop_state in H3;
        destruct H3 as [_ [fuel [[Ht_nonneg _] _]]]; lia).
  subst t.
  entailer!.
  symmetry.
  apply is_pal_z_correct_false; try lia.
  intro Hrev.
  apply H.
  pose proof (pal_reverse_loop_state_final x0 r H3).
  lia.
Qed.

Lemma proof_of_even_odd_palindrome_safety_wit_7 : even_odd_palindrome_safety_wit_7.
Proof.
  pre_process.
  pose proof (pal_count_prefix_bounds _ _ _ _ H9).
  entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_safety_wit_23 : even_odd_palindrome_safety_wit_23.
Proof.
  pre_process.
  pose proof (pal_count_prefix_bounds _ _ _ _ H12).
  entailer!.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_1 : even_odd_palindrome_entail_wit_1.
Proof.
  pre_process.
  subst n_pre.
  entailer!.
  apply pal_count_prefix_init.
  lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_3_1 : even_odd_palindrome_entail_wit_3_1.
Proof.
  pre_process.
  entailer!.
  replace (i + 1 - 1) with ((i - 1) + 1) by lia.
  eapply pal_count_prefix_step_even_hit with (k := i - 1); eauto; try lia.
  - replace (i - 1 + 1) with i by lia.
    rewrite <- H1. exact H0.
  - replace (i - 1 + 1) with i by lia.
    rewrite <- (Z.rem_mod_nonneg i 2) by lia.
    exact H.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_3_2 : even_odd_palindrome_entail_wit_3_2.
Proof.
  pre_process.
  entailer!.
  replace (i + 1 - 1) with ((i - 1) + 1) by lia.
  eapply pal_count_prefix_step_miss with (k := i - 1); eauto; try lia.
  replace (i - 1 + 1) with i by lia.
  rewrite <- H2. exact H1.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_3_3 : even_odd_palindrome_entail_wit_3_3.
Proof.
  pre_process.
  entailer!.
  assert (0 <= i % 2 < 2) by (apply Z.rem_bound_pos; lia).
  lia.
Qed.

Lemma proof_of_even_odd_palindrome_entail_wit_3_4 : even_odd_palindrome_entail_wit_3_4.
Proof.
  pre_process.
  entailer!.
  replace (i + 1 - 1) with ((i - 1) + 1) by lia.
  eapply pal_count_prefix_step_odd_hit with (k := i - 1); eauto; try lia.
  - replace (i - 1 + 1) with i by lia.
    rewrite <- H4. exact H3.
  - replace (i - 1 + 1) with i by lia.
    rewrite <- (Z.rem_mod_nonneg i 2) by lia.
    exact H2.
Qed.

Lemma proof_of_even_odd_palindrome_return_wit_1 : even_odd_palindrome_return_wit_1.
Proof.
  pre_process.
  Exists (num2 :: num1 :: nil) 2 retval.
  unfold IntArray.full, store_array.
  simpl.
  entailer!.
  eapply problem_107_spec_z_of_prefix.
  assert (i - 1 = n0) by lia.
  rewrite H8 in H7.
  exact H7.
Qed.
