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
From SimpleC.EE Require Import C_143_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_143.
Local Open Scope sac.

Lemma proof_of_is_prime_len_entail_wit_1 : is_prime_len_entail_wit_1.
Proof.
  unfold is_prime_len_entail_wit_1.
  intros.
  pre_process.
  entailer!.
  unfold prime_loop_state_z.
  split.
  - intro Hbad. lia.
  - intros [d [Hd _]]. lia.
Qed.

Lemma proof_of_is_prime_len_entail_wit_2_1 : is_prime_len_entail_wit_2_1.
Proof.
  unfold is_prime_len_entail_wit_2_1.
  intros.
  pre_process.
  entailer!.
  unfold prime_loop_state_z.
  split.
  - intro Hdummy. exists j. split; lia.
  - intro Hdummy. reflexivity.
Qed.

Lemma proof_of_is_prime_len_entail_wit_2_2 : is_prime_len_entail_wit_2_2.
Proof.
  unfold is_prime_len_entail_wit_2_2.
  intros.
  pre_process.
  entailer!.
  unfold prime_loop_state_z in *.
  destruct H7 as [Hto Hfrom].
  split.
  - intro Hcomp.
    destruct (Hto Hcomp) as [d [Hd Hrem]].
    exists d. split; lia.
  - intros [d [Hd Hrem]].
    assert (d < j \/ d = j) as [Hdlt | ->] by lia.
    + apply Hfrom. exists d. split; lia.
    + contradiction.
Qed.

Lemma proof_of_is_prime_len_return_wit_1 : is_prime_len_return_wit_1.
Proof.
  unfold is_prime_len_return_wit_1.
  intros.
  pre_process.
  assert (composite = 0) by lia.
  subst composite.
  entailer!.
  symmetry.
  eapply (prime_loop_state_z_flag_1 len_pre j); eauto; lia.
Qed.

Lemma proof_of_is_prime_len_return_wit_2 : is_prime_len_return_wit_2.
Proof.
  unfold is_prime_len_return_wit_2.
  intros.
  pre_process.
  subst composite.
  entailer!.
  symmetry.
  eapply (prime_loop_state_z_flag_0 len_pre j); eauto; lia.
Qed.

Lemma proof_of_is_prime_len_return_wit_3 : is_prime_len_return_wit_3.
Proof.
  unfold is_prime_len_return_wit_3.
  intros.
  pre_process.
  assert (len_pre = 0 \/ len_pre = 1) as [-> | ->] by lia;
    unfold prime_len_flag_z, is_prime_bool; simpl; entailer!.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_1 : words_in_sentence_entail_wit_1.
Proof.
  unfold words_in_sentence_entail_wit_1.
  intros.
  pre_process; subst.
  Exists (@nil Z).
  assert (0 <= 0 <= Zlength l + 2) by lia.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength l + 2) H1).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  apply scan_ready_z_0.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_3 : words_in_sentence_entail_wit_3.
Proof.
  unfold words_in_sentence_entail_wit_3.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z i l).
  entailer!.
  - symmetry.
    apply words_in_sentence_prefix_z_skip_space; lia || assumption.
  - eapply scan_ready_z_step_space; eauto.
Qed. 

Lemma proof_of_words_in_sentence_entail_wit_4 : words_in_sentence_entail_wit_4.
Proof.
  unfold words_in_sentence_entail_wit_4.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z i l).
  entailer!.
  - apply word_chars_z_empty.
  - eapply scan_ready_z_nonspace_start; eauto.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_5 : words_in_sentence_entail_wit_5.
Proof.
  unfold words_in_sentence_entail_wit_5.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z start l).
  entailer!.
  eapply word_chars_z_step; eauto.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_6_1 : words_in_sentence_entail_wit_6_1.
Proof.
  unfold words_in_sentence_entail_wit_6_1.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z start l ++ (32 :: nil)).
  entailer!.
  all: try (symmetry; apply word_copy_prefix_z_0_nonempty; lia).
  all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  all: try (apply scan_ready_z_at_end; lia).
Qed.

Lemma proof_of_words_in_sentence_entail_wit_6_2 : words_in_sentence_entail_wit_6_2.
Proof.
  unfold words_in_sentence_entail_wit_6_2.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z start l ++ (32 :: nil)).
  entailer!.
  all: try (symmetry; apply word_copy_prefix_z_0_nonempty; lia).
  all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  all: try (apply scan_ready_z_at_space; assumption).
Qed.

Lemma proof_of_words_in_sentence_entail_wit_6_3 : words_in_sentence_entail_wit_6_3.
Proof.
  unfold words_in_sentence_entail_wit_6_3.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z start l).
  entailer!.
  all: try (symmetry; apply word_copy_prefix_z_0_empty; lia).
  all: try (apply scan_ready_z_at_end; lia).
Qed.

Lemma proof_of_words_in_sentence_entail_wit_6_4 : words_in_sentence_entail_wit_6_4.
Proof.
  unfold words_in_sentence_entail_wit_6_4.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z start l).
  entailer!.
  all: try (symmetry; apply word_copy_prefix_z_0_empty; lia).
  all: try (apply scan_ready_z_at_space; assumption).
Qed.

Lemma proof_of_words_in_sentence_entail_wit_7 : words_in_sentence_entail_wit_7.
Proof.
  unfold words_in_sentence_entail_wit_7.
  intros.
  pre_process; subst.
  Exists (word_copy_prefix_z start (k + 1) l).
  entailer!.
  - rewrite <- word_copy_prefix_z_step by lia.
    reflexivity.
  - rewrite word_copy_prefix_z_step by lia.
    rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_words_in_sentence_entail_wit_8_2 : words_in_sentence_entail_wit_8_2.
Proof.
  unfold words_in_sentence_entail_wit_8_2.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z start l).
  entailer!.
  - symmetry.
    eapply words_in_sentence_prefix_z_nonprime_word; eauto; lia.
  - apply scan_ready_z_at_end; lia.
Qed. 

Lemma proof_of_words_in_sentence_entail_wit_8_3 : words_in_sentence_entail_wit_8_3.
Proof.
  unfold words_in_sentence_entail_wit_8_3.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix_z start l).
  entailer!.
  - symmetry.
    eapply words_in_sentence_prefix_z_nonprime_word; eauto; lia.
  - apply scan_ready_z_at_space; assumption.
Qed. 

Lemma proof_of_words_in_sentence_entail_wit_8_4 : words_in_sentence_entail_wit_8_4.
Proof.
  unfold words_in_sentence_entail_wit_8_4.
  intros.
  pre_process; subst.
  assert (k = i - start) as Hk by lia.
  Exists (word_copy_prefix_z start k l).
  entailer!.
  - rewrite Hk.
    symmetry.
    eapply words_in_sentence_prefix_z_prime_word; eauto; lia.
  - rewrite Hk.
    rewrite <- (words_in_sentence_prefix_z_prime_word l start i) by (eauto; lia).
    pose proof (words_in_sentence_prefix_z_len_bound l i ltac:(lia)).
    lia.
Qed. 

Lemma proof_of_words_in_sentence_return_wit_1 : words_in_sentence_return_wit_1.
Proof.
  unfold words_in_sentence_return_wit_1.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_output_z l) (Zlength (words_in_sentence_output_z l)).
  assert (i = Zlength l) as Hi by lia.
  assert (words_in_sentence_prefix_z i l = words_in_sentence_output_z l) as Hpref.
  { apply words_in_sentence_prefix_z_full. exact Hi. }
    rewrite Hpref.
    entailer!.
    - apply words_in_sentence_output_z_spec; assumption.
  - rewrite <- Hpref. lia.
  - apply Zlength_nonneg.
Qed.
