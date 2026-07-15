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
From SimpleC.EE Require Import C_104_goal.
From SimpleC.EE Require Import C_104_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_104.
Local Open Scope sac.

Lemma proof_of_unique_digits_entail_wit_1_split_goal_1 : unique_digits_entail_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
  unfold unique_digits_prefix_104. simpl.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_unique_digits_entail_wit_1_split_goal_2 : unique_digits_entail_wit_1_split_goal_2.
Proof.
  pre_process; entailer!.
Qed.

Lemma proof_of_unique_digits_entail_wit_1 : unique_digits_entail_wit_1.
Proof.
  right. intros. entailer!.
  unfold unique_digits_prefix_104. simpl.
  split; [lia | reflexivity].
Qed.

Lemma proof_of_unique_digits_entail_wit_2_1 : unique_digits_entail_wit_2_1.
Proof.
  pre_process.
  pose proof (unique_digits_safe_104_Znth input_l i PreH9 ltac:(lia)).
  lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_2_2 : unique_digits_entail_wit_2_2.
Proof.
  intros xs xp il ol osz idx dat outp
    Hneq Hlt Hout Hdat Hxs0 Hxsmax Hlen Hpre Hsafe
    Hidx0 Hidxle Hosz0 Hoszle Hoszlen Hprefix.
  Left. Exists ol. entailer!.
  - apply odd_scan_init_104.
    assert (0 <= idx < Zlength il) as Hi by lia.
    pose proof (unique_digits_safe_104_Znth il idx Hsafe Hi); lia.
  - assert (0 <= idx < Zlength il) as Hi by lia.
    pose proof (unique_digits_safe_104_Znth il idx Hsafe Hi); lia.
  - assert (0 <= idx < Zlength il) as Hi by lia.
    pose proof (unique_digits_safe_104_Znth il idx Hsafe Hi); lia.
  - assert (0 <= idx < Zlength il) as Hi by lia.
    pose proof (unique_digits_safe_104_Znth il idx Hsafe Hi); lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_5_1 : unique_digits_entail_wit_5_1.
Proof.
  pre_process; Right. Exists output_l_2. entailer!.
  - subst u. eapply odd_scan_even_quot_104; eauto; lia.
  - pose proof (odd_digit_scan_state_104_bounds current num u ltac:(lia) PreH23) as [? _].
    replace (num ÷ 10) with (num / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
    assert (num / 10 <= num) by (apply Z.div_le_upper_bound; lia).
    lia.
  - replace (num ÷ 10) with (num / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
    apply Z.div_pos; lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_5_2 : unique_digits_entail_wit_5_2.
Proof.
  pre_process; Left. Exists output_l_2. entailer!.
  - subst u. eapply odd_scan_odd_quot_104; eauto; lia.
  - pose proof (odd_digit_scan_state_104_bounds current num u ltac:(lia) PreH23) as [? _].
    replace (num ÷ 10) with (num / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
    assert (num / 10 <= num) by (apply Z.div_le_upper_bound; lia).
    lia.
  - replace (num ÷ 10) with (num / 10) by (symmetry; apply Z.quot_div_nonneg; lia).
    apply Z.div_pos; lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_6_1 : unique_digits_entail_wit_6_1.
Proof.
  pre_process; Right. Exists output_l_2. entailer!.
  subst u. eapply odd_digit_scan_state_104_reject. exact PreH22.
Qed.

Lemma proof_of_unique_digits_entail_wit_6_2 : unique_digits_entail_wit_6_2.
Proof.
  pre_process.
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  Exists output_l_2. entailer!.
  subst u. eapply odd_digit_scan_state_104_accept; eauto; lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_6_3 : unique_digits_entail_wit_6_3.
Proof.
  pre_process; Right. Exists output_l_2. entailer!.
  subst u. eapply odd_digit_scan_state_104_reject. exact PreH21.
Qed.

Lemma proof_of_unique_digits_entail_wit_9_1_split_goal_1 : unique_digits_entail_wit_9_1_split_goal_1.
Proof.
  pre_process; entailer!.
  subst current.
  apply unique_digits_prefix_104_add_step; auto; lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_9_1_split_goal_2 : unique_digits_entail_wit_9_1_split_goal_2.
Proof.
  pre_process; entailer!.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in *.
  lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_9_1 : unique_digits_entail_wit_9_1.
Proof.
  right. intros. entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil in *.
    lia.
  - subst current.
    apply unique_digits_prefix_104_add_step; auto; lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_9_2_split_goal_1 : unique_digits_entail_wit_9_2_split_goal_1.
Proof.
  pre_process; entailer!.
  subst current.
  apply unique_digits_prefix_104_skip_step; auto; lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_9_2 : unique_digits_entail_wit_9_2.
Proof.
  right. intros. entailer!.
  subst current.
  apply unique_digits_prefix_104_skip_step; auto; lia.
Qed.

Lemma proof_of_unique_digits_entail_wit_10_split_goal_1 : unique_digits_entail_wit_10_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (i = x_size_pre) by lia.
  subst i. exact PreH14.
Qed.

Lemma proof_of_unique_digits_entail_wit_10 : unique_digits_entail_wit_10.
Proof.
  right. intros. entailer!.
  assert (i = x_size_pre) by lia.
  subst i. exact PreH14.
Qed.

Lemma proof_of_unique_digits_entail_wit_11 : unique_digits_entail_wit_11.
Proof.
  right. intros. Exists output_l_2. entailer!.
  - rewrite PreH7.
    apply problem_104_spec_z_of_sorted_104 with (filtered := output_l_2).
    + replace (Zlength input_l) with x_size_pre by lia.
      exact PreH20.
    + exact PreH8.
    + exact PreH9.
  - rewrite PreH7. exact PreH9.
  - rewrite PreH7. exact PreH8.
  - rewrite PreH7. exact PreH1.
Qed.

Lemma proof_of_unique_digits_return_wit_1 : unique_digits_return_wit_1.
Proof.
  left.
  intros xs xp il outl sorted datal outp datap outsz
    Hout Hdat Hxs0 Hxsmax Hlen Hpre Hsafe Hos0 Hosle
    Houtlen Hsortedlen Hdatalen Hsub Hprefix Hsorted Hperm Hspec.
  Exists datal sorted outsz datap.
  entailer!.
Qed.
