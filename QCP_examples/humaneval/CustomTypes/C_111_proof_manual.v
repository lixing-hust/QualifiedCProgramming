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
From SimpleC.EE Require Import C_111_goal.
From SimpleC.EE Require Import C_111_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_111.
Local Open Scope sac.

Lemma proof_of_histogram_safety_wit_15 : histogram_safety_wit_15.
Proof.
  unfold histogram_safety_wit_15.
  right; intros; entailer!.
  all: pose proof
    (histogram_counts_bounded_at_111 count_l i ch PreH17) as Hbound;
    rewrite PreH15 in Hbound; specialize (Hbound ltac:(lia)); lia.
Qed.

Lemma proof_of_histogram_entail_wit_1 : histogram_entail_wit_1.
Proof.
  unfold histogram_entail_wit_1.
  right; intros; entailer!.
Qed.

Lemma proof_of_histogram_entail_wit_2 : histogram_entail_wit_2.
Proof.
  unfold histogram_entail_wit_2.
  right; intros; entailer!.
  unfold zeros.
  replace (Z.to_nat (init + 1)) with (S (Z.to_nat init)) by lia.
  symmetry. apply repeat_snoc_111.
Qed.

Lemma proof_of_histogram_entail_wit_3 : histogram_entail_wit_3.
Proof.
  unfold histogram_entail_wit_3.
  right.
  pre_process_default.
  replace init with 256 in * by lia.
  entailer!.
  apply histogram_zero_counts_bounded_111.
Qed.

Lemma proof_of_histogram_entail_wit_4 : histogram_entail_wit_4.
Proof.
  unfold histogram_entail_wit_4.
  right; intros.
  entailer!.
  all: assert (Hi : i < n) by
    (destruct (Z.eq_dec i n) as [-> | Hneq]; [
       rewrite <- PreH7 in PreH2;
       rewrite histogram_Znth_c_string_end_111 in PreH2;
       contradiction | lia]).
  all: try exact Hi.
  all: assert (Hinside :
      Znth i (List.app input_l (0 :: nil)) 0 = Znth i input_l 0)
      by (apply histogram_Znth_c_string_inside_111; lia);
    assert (Hrange : 0 <= Znth i input_l 0 < 256)
      by (apply PreH16; rewrite PreH7; lia);
    rewrite Hinside;
    rewrite unsigned_last_nbits_eq
      by (change (2 ^ 8) with 256; lia);
    lia.
Qed.

Lemma proof_of_histogram_entail_wit_5_1 : histogram_entail_wit_5_1.
Proof.
  unfold histogram_entail_wit_5_1.
  right; intros; entailer!.
  - pose proof (histogram_counts_bounded_at_111 count_l_2 i ch PreH18).
    rewrite PreH16 in H. specialize (H ltac:(lia)). lia.
  - rewrite Zlength_replace_Znth. exact PreH16.
  - eapply histogram_scan_state_step_nonspace_gt_111.
    + lia.
    + exact PreH11.
    + exact PreH10.
    + exact PreH1.
    + exact PreH17.
  - apply histogram_counts_bounded_bump_111; [exact PreH18 |].
    rewrite PreH16. lia.
Qed.

Lemma proof_of_histogram_entail_wit_5_2 : histogram_entail_wit_5_2.
Proof.
  unfold histogram_entail_wit_5_2.
  right; intros; entailer!.
  - rewrite Zlength_replace_Znth. exact PreH16.
  - eapply histogram_scan_state_step_nonspace_le_111.
    + lia.
    + exact PreH11.
    + exact PreH10.
    + exact PreH1.
    + exact PreH17.
  - apply histogram_counts_bounded_bump_111; [exact PreH18 |].
    rewrite PreH16. lia.
Qed.

Lemma proof_of_histogram_entail_wit_5_3 : histogram_entail_wit_5_3.
Proof.
  unfold histogram_entail_wit_5_3.
  right; intros; entailer!.
  all: assert (Hi : i < n) by
    (destruct (Z.eq_dec i n) as [-> | Hneq]; [
       rewrite <- PreH7 in PreH2;
       rewrite histogram_Znth_c_string_end_111 in PreH2;
       contradiction | lia]).
  - lia.
  - eapply histogram_scan_state_step_space_111.
    + rewrite PreH7. lia.
    + rewrite histogram_Znth_c_string_inside_111 in PreH1 by lia.
      exact PreH1.
    + exact PreH13.
  - apply histogram_counts_bounded_weaken_111. exact PreH14.
Qed.

Lemma proof_of_histogram_entail_wit_6 : histogram_entail_wit_6.
Proof.
  unfold histogram_entail_wit_6.
  right; intros.
  assert (Hi : i = n).
  { destruct (Z.eq_dec i n); [assumption |].
    assert (i < n) by lia.
    rewrite histogram_Znth_c_string_inside_111 in PreH1 by lia.
    pose proof (problem_111_pre_z_nonzero_111 input_l i PreH15 PreH16)
      as Hnozero.
    specialize (Hnozero ltac:(rewrite PreH6; lia)). contradiction. }
  subst i.
  entailer!.
  apply histogram_output_state_init_111.
Qed.

Lemma proof_of_histogram_entail_wit_8_1 : histogram_entail_wit_8_1.
Proof.
  unfold histogram_entail_wit_8_1.
  right; intros; entailer!.
  - rewrite Zlength_app_cons. lia.
  - rewrite Zlength_app_cons. lia.
  - eapply histogram_output_state_step_selected_111; eauto.
Qed.

Lemma proof_of_histogram_entail_wit_8_2 : histogram_entail_wit_8_2.
Proof.
  unfold histogram_entail_wit_8_2.
  right; intros; entailer!.
  eapply histogram_output_state_step_not_count_111; eauto.
Qed.

Lemma proof_of_histogram_entail_wit_8_3 : histogram_entail_wit_8_3.
Proof.
  unfold histogram_entail_wit_8_3.
  right; intros; entailer!.
  eapply histogram_output_state_step_nonpositive_111; eauto.
Qed.

Lemma proof_of_histogram_return_wit_1 : histogram_return_wit_1.
Proof.
  unfold histogram_return_wit_1.
  right; intros.
  Exists values_l_2 keys_l_2.
  entailer!.
  - rewrite <- PreH11. entailer!.
  - apply histogram_spec_bridge_111 with
      (counts := count_l) (current_max := max).
    + apply ascii_range_z_chars_range_111. exact PreH18.
    + apply histogram_scan_state_final_summary_111.
      * apply ascii_range_z_chars_range_111. exact PreH18.
      * rewrite PreH6. exact PreH14.
    + replace scan with 256 in PreH16 by lia. exact PreH16.
Qed.
