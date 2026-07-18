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
From SimpleC.EE Require Import C_154_goal.
From SimpleC.EE Require Import C_154_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_154.
Local Open Scope sac.

Lemma proof_of_cycpattern_check_safety_wit_17 : cycpattern_check_safety_wit_17.
Proof.
  right; pre_process; entailer!.
  all: unfold rotation_scan_state_154 in PreH8;
       destruct PreH8 as [[Hlo Hhi] Hrest];
       unfold string_length in *;
       pose proof (Zlength_nonneg b_l); lia.
Qed.

Lemma proof_of_cycpattern_check_entail_wit_1 : cycpattern_check_entail_wit_1.
Proof.
  right; pre_process; subst a_pre b_pre; entailer!.
  - subst retval; pose proof (Zlength_nonneg b_l);
      unfold string_length in *; entailer!.
  - pose proof (rotation_scan_state_154_zero a_l b_l); entailer!.
Qed.

Lemma proof_of_cycpattern_check_entail_wit_2 : cycpattern_check_entail_wit_2.
Proof.
  right; pre_process; entailer!.
  apply rotation_prefix_154_zero.
  unfold string_length in PreH11; lia.
Qed.

Lemma proof_of_cycpattern_check_entail_wit_3_1 : cycpattern_check_entail_wit_3_1.
Proof.
  right; pre_process; entailer!.
  rewrite Z.rem_small by lia; reflexivity.
Qed.

Lemma proof_of_cycpattern_check_entail_wit_3_2 : cycpattern_check_entail_wit_3_2.
Proof.
  right; pre_process; entailer!.
  replace (i + j) with ((j - (n - i)) + 1 * n) by lia.
  rewrite Z.rem_add by nia.
  rewrite Z.rem_small by lia.
  lia.
Qed.

Lemma proof_of_cycpattern_check_entail_wit_4 : cycpattern_check_entail_wit_4.
Proof.
  right; pre_process; entailer!.
  all: rewrite c_string_Znth_inside by
      (unfold string_length in *; lia).
  - reflexivity.
  - destruct PreH14 as [Hall Hnul]; apply Hall;
      unfold string_length in *; lia.
  - destruct PreH14 as [Hall Hnul]; apply Hall;
      unfold string_length in *; lia.
Qed.

Lemma proof_of_cycpattern_check_entail_wit_5 : cycpattern_check_entail_wit_5.
Proof.
  right; pre_process.
  assert (Hremmod : Z.rem (i + j) n = (i + j) mod n).
  { apply Z.rem_mod_nonneg; lia. }
  entailer!.
  eapply rotation_prefix_154_step; [exact PreH21 | |].
  - unfold string_length in PreH19; lia.
  - unfold string_length in PreH19.
    rewrite <- PreH19, <- Hremmod, <- PreH4; exact PreH3.
Qed.

Lemma proof_of_cycpattern_check_entail_wit_6 : cycpattern_check_entail_wit_6.
Proof.
  right; pre_process; entailer!.
  all: assert (Hjn : j = n) by lia; subst j;
       unfold rotation_prefix_154 in PreH17;
       destruct PreH17 as [Hi [Hj Hout]];
       assert (Hlen : Zlength (rotate_at_154 b_l i) = Zlength b_l)
         by (apply rotate_at_154_length; lia);
       unfold string_length in PreH15;
       rewrite sublist_self in Hout by lia;
       subst rotate_l.
  - unfold store_string, string_length, c_string in *.
    rewrite Hlen; rewrite <- PreH15; entailer!.
  - unfold rotation_prefix_154; repeat split; try lia.
    rewrite sublist_self by lia; reflexivity.
  - apply valid_string_rotate_at_154; [exact PreH13 | lia].
Qed.

Lemma proof_of_cycpattern_check_entail_wit_7 : cycpattern_check_entail_wit_7.
Proof.
  right; pre_process; entailer!.
  - unfold string_length in *.
    assert (Hi : 0 <= i <= Zlength b_l).
    { unfold rotation_prefix_154 in PreH13;
      destruct PreH13 as [Hi0 Hrest]; lia. }
    rewrite rotate_at_154_length by exact Hi.
    rewrite <- PreH11.
    apply CharArray.full_to_undef_full.
  - split.
    + unfold string_length in PreH11; rewrite <- PreH11; exact PreH13.
    + exact (strstr_result_154_success a_l (rotate_at_154 b_l i)
               retval a0 PreH1 PreH2).
Qed.

Lemma proof_of_cycpattern_check_entail_wit_8 : cycpattern_check_entail_wit_8.
Proof.
  right; pre_process; entailer!.
  - unfold string_length in *.
    assert (Hi : 0 <= i <= Zlength b_l).
    { unfold rotation_prefix_154 in PreH13;
      destruct PreH13 as [Hi0 Hrest]; lia. }
    rewrite rotate_at_154_length by exact Hi.
    rewrite <- PreH11.
    apply CharArray.full_to_undef_full.
  - eapply (rotation_scan_state_154_step a_l b_l i
              (rotate_at_154 b_l i) retval a0).
    + exact PreH12.
    + unfold string_length in PreH11; rewrite <- PreH11; exact PreH13.
    + exact PreH1.
    + exact PreH2.
Qed.

Lemma proof_of_cycpattern_check_entail_wit_9 : cycpattern_check_entail_wit_9.
Proof.
  right; pre_process; entailer!.
  all: unfold rotation_scan_state_154 in PreH10;
       destruct PreH10 as [[Hlo Hhi] Hnone].
  - exact Hlo.
  - unfold string_length in PreH9; lia.
Qed.

Lemma proof_of_cycpattern_check_return_wit_1 : cycpattern_check_return_wit_1.
Proof.
  unfold cycpattern_check_return_wit_1; intros.
  rewrite <- derivable1_orp_intros1.
  assert (i = n) by lia; subst i.
  assert (Hspec : problem_154_spec_z a_l b_l 0).
  { apply rotation_scan_state_154_problem_spec; try assumption.
    unfold string_length in PreH11; rewrite <- PreH11; exact PreH12. }
  entailer!; unfold store_string; cancel.
Qed.

Lemma proof_of_cycpattern_check_return_wit_2 : cycpattern_check_return_wit_2.
Proof.
  unfold cycpattern_check_return_wit_2; intros.
  rewrite <- derivable1_orp_intros2.
  assert (Hspec : problem_154_spec_z a_l b_l 1).
  { exact (rotation_success_154_problem_spec a_l b_l i
             (rotate_at_154 b_l i) PreH6 PreH7 PreH10). }
  entailer!; unfold store_string; cancel.
Qed.

Lemma proof_of_cycpattern_check_partial_solve_wit_5_pure :
  cycpattern_check_partial_solve_wit_5_pure.
Proof.
  right; pre_process; entailer!.
  unfold string_length in *.
  assert (Hi : 0 <= i <= Zlength b_l).
  { unfold rotation_prefix_154 in PreH15;
    destruct PreH15 as [Hi0 Hrest]; lia. }
  rewrite rotate_at_154_length by exact Hi.
  lia.
Qed.
