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
From SimpleC.EE Require Import C_119_goal.
From SimpleC.EE Require Import C_119_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_119.
Require Import Lia.
Local Open Scope sac.

Lemma proof_of_match_parens_entail_wit_1 : match_parens_entail_wit_1.
Proof.
  unfold match_parens_entail_wit_1; intros.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  - apply paren_scan_initial_119.
  - pose proof (Zlength_nonneg l1).
    unfold string_lib.string_length in *; lia.
Qed.

Lemma proof_of_match_parens_entail_wit_2_1 : match_parens_entail_wit_2_1.
Proof.
  unfold match_parens_entail_wit_2_1; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *.
    pose proof (Zlength_nonneg l2); lia. }
  pose proof (paren_code_at_119 l1 i PreH16 Hi) as Hcode.
  destruct Hcode as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hnext : paren_scan_state_119 (l1 ++ l2) (i + 1) (count - 1) can).
    { eapply paren_scan_close_nonnegative_119.
      - exact PreH19.
      - exact Hwhole.
      - rewrite app_Znth1 by lia; exact H41.
      - lia. }
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_2_2 : match_parens_entail_wit_2_2.
Proof.
  unfold match_parens_entail_wit_2_2; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l2); lia. }
  pose proof (paren_code_at_119 l1 i PreH16 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hnext : paren_scan_state_119 (l1 ++ l2) (i + 1) (count - 1) can).
    { eapply paren_scan_close_nonnegative_119.
      - exact PreH19.
      - exact Hwhole.
      - rewrite app_Znth1 by lia; exact H41.
      - lia. }
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_2_3 : match_parens_entail_wit_2_3.
Proof.
  unfold match_parens_entail_wit_2_3; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l2); lia. }
  assert (H40 : Znth i l1 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hnext : paren_scan_state_119 (l1 ++ l2) (i + 1) (count + 1) can).
  { eapply paren_scan_open_119.
    - exact PreH19.
    - exact Hwhole.
    - rewrite app_Znth1 by lia; exact H40. }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_2_4 : match_parens_entail_wit_2_4.
Proof.
  unfold match_parens_entail_wit_2_4; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l2); lia. }
  assert (H40 : Znth i l1 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hnext : paren_scan_state_119 (l1 ++ l2) (i + 1) (count + 1) can).
  { eapply paren_scan_open_119.
    - exact PreH19.
    - exact Hwhole.
    - rewrite app_Znth1 by lia; exact H40. }
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_2_5 : match_parens_entail_wit_2_5.
Proof.
  unfold match_parens_entail_wit_2_5; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l2); lia. }
  pose proof (paren_code_at_119 l1 i PreH16 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hnext : paren_scan_state_119 (l1 ++ l2) (i + 1) (count - 1) 0).
    { eapply paren_scan_close_negative_119.
      - exact PreH19.
      - exact Hwhole.
      - rewrite app_Znth1 by lia; exact H41.
      - lia. }
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_2_6 : match_parens_entail_wit_2_6.
Proof.
  unfold match_parens_entail_wit_2_6; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l2); lia. }
  pose proof (paren_code_at_119 l1 i PreH16 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hnext : paren_scan_state_119 (l1 ++ l2) (i + 1) (count - 1) 0).
    { eapply paren_scan_close_negative_119.
      - exact PreH19.
      - exact Hwhole.
      - rewrite app_Znth1 by lia; exact H41.
      - lia. }
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_2_7 : match_parens_entail_wit_2_7.
Proof.
  unfold match_parens_entail_wit_2_7; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l2); lia. }
  assert (H40 : Znth i l1 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hnext : paren_scan_state_119 (l1 ++ l2) (i + 1) (count + 1) can).
  { eapply paren_scan_open_119.
    - exact PreH19.
    - exact Hwhole.
    - rewrite app_Znth1 by lia; exact H40. }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  rewrite <- PreH10; exact Hnext.
Qed.

Lemma proof_of_match_parens_entail_wit_2_8 : match_parens_entail_wit_2_8.
Proof.
  unfold match_parens_entail_wit_2_8; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l2); lia. }
  assert (H40 : Znth i l1 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hnext : paren_scan_state_119 (l1 ++ l2) (i + 1) (count + 1) can).
  { eapply paren_scan_open_119.
    - exact PreH19.
    - exact Hwhole.
    - rewrite app_Znth1 by lia; exact H40. }
  subst can.
  pose proof (paren_scan_can_one_nonnegative_119 (l1 ++ l2) (i + 1)
    (count + 1) Hnext).
  lia.
Qed.

Lemma proof_of_match_parens_entail_wit_4_1 : match_parens_entail_wit_4_1.
Proof.
  unfold match_parens_entail_wit_4_1; intros.
  rewrite <- derivable1_orp_intros1.
  entailer!.
  - replace (n1 + 0) with i by lia; exact PreH17.
  - pose proof (Zlength_nonneg l2).
    unfold string_lib.string_length in *; lia.
Qed.

Lemma proof_of_match_parens_entail_wit_4_2 : match_parens_entail_wit_4_2.
Proof.
  unfold match_parens_entail_wit_4_2; intros.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  - replace (n1 + 0) with i by lia; exact PreH17.
  - pose proof (Zlength_nonneg l2).
    unfold string_lib.string_length in *; lia.
Qed.

Lemma proof_of_match_parens_entail_wit_5_1 : match_parens_entail_wit_5_1.
Proof.
  unfold match_parens_entail_wit_5_1; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n1 + i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  pose proof (paren_code_at_119 l2 i PreH17 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hchar : Znth (n1 + i) (l1 ++ l2) 0 = 41).
    { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
      replace (n1 + i - Zlength l1) with i
        by (unfold string_lib.string_length in *; lia); exact H41. }
    assert (Hstep : paren_scan_state_119 (l1 ++ l2)
      ((n1 + i) + 1) (count - 1) can).
    { eapply paren_scan_close_nonnegative_119; eauto; lia. }
    do 3 rewrite <- derivable1_orp_intros1.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_5_2 : match_parens_entail_wit_5_2.
Proof.
  unfold match_parens_entail_wit_5_2; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n1 + i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  pose proof (paren_code_at_119 l2 i PreH17 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hchar : Znth (n1 + i) (l1 ++ l2) 0 = 41).
    { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
      replace (n1 + i - Zlength l1) with i
        by (unfold string_lib.string_length in *; lia); exact H41. }
    assert (Hstep : paren_scan_state_119 (l1 ++ l2)
      ((n1 + i) + 1) (count - 1) can).
    { eapply paren_scan_close_nonnegative_119; eauto; lia. }
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_5_3 : match_parens_entail_wit_5_3.
Proof.
  unfold match_parens_entail_wit_5_3; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n1 + i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  assert (H40 : Znth i l2 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hchar : Znth (n1 + i) (l1 ++ l2) 0 = 40).
  { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
    replace (n1 + i - Zlength l1) with i
      by (unfold string_lib.string_length in *; lia); exact H40. }
  assert (Hstep : paren_scan_state_119 (l1 ++ l2)
    ((n1 + i) + 1) (count + 1) can).
  { eapply paren_scan_open_119; eauto. }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_5_4 : match_parens_entail_wit_5_4.
Proof.
  unfold match_parens_entail_wit_5_4; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n1 + i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  assert (H40 : Znth i l2 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hchar : Znth (n1 + i) (l1 ++ l2) 0 = 40).
  { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
    replace (n1 + i - Zlength l1) with i
      by (unfold string_lib.string_length in *; lia); exact H40. }
  assert (Hstep : paren_scan_state_119 (l1 ++ l2)
    ((n1 + i) + 1) (count + 1) can).
  { eapply paren_scan_open_119; eauto. }
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_5_5 : match_parens_entail_wit_5_5.
Proof.
  unfold match_parens_entail_wit_5_5; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n1 + i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  pose proof (paren_code_at_119 l2 i PreH17 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hchar : Znth (n1 + i) (l1 ++ l2) 0 = 41).
    { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
      replace (n1 + i - Zlength l1) with i
        by (unfold string_lib.string_length in *; lia); exact H41. }
    assert (Hstep : paren_scan_state_119 (l1 ++ l2)
      ((n1 + i) + 1) (count - 1) 0).
    { eapply paren_scan_close_negative_119; eauto; lia. }
    do 3 rewrite <- derivable1_orp_intros1.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_5_6 : match_parens_entail_wit_5_6.
Proof.
  unfold match_parens_entail_wit_5_6; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n1 + i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  pose proof (paren_code_at_119 l2 i PreH17 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hchar : Znth (n1 + i) (l1 ++ l2) 0 = 41).
    { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
      replace (n1 + i - Zlength l1) with i
        by (unfold string_lib.string_length in *; lia); exact H41. }
    assert (Hstep : paren_scan_state_119 (l1 ++ l2)
      ((n1 + i) + 1) (count - 1) 0).
    { eapply paren_scan_close_negative_119; eauto; lia. }
    do 3 rewrite <- derivable1_orp_intros1.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_5_7 : match_parens_entail_wit_5_7.
Proof.
  unfold match_parens_entail_wit_5_7; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n1 + i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  assert (H40 : Znth i l2 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hchar : Znth (n1 + i) (l1 ++ l2) 0 = 40).
  { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
    replace (n1 + i - Zlength l1) with i
      by (unfold string_lib.string_length in *; lia); exact H40. }
  assert (Hstep : paren_scan_state_119 (l1 ++ l2)
    ((n1 + i) + 1) (count + 1) can).
  { eapply paren_scan_open_119; eauto. }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  replace (n1 + (i + 1)) with ((n1 + i) + 1) by lia.
  rewrite <- PreH10; exact Hstep.
Qed.

Lemma proof_of_match_parens_entail_wit_5_8 : match_parens_entail_wit_5_8.
Proof.
  unfold match_parens_entail_wit_5_8; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n1 + i < Zlength (l1 ++ l2)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  assert (H40 : Znth i l2 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hchar : Znth (n1 + i) (l1 ++ l2) 0 = 40).
  { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
    replace (n1 + i - Zlength l1) with i
      by (unfold string_lib.string_length in *; lia); exact H40. }
  assert (Hstep : paren_scan_state_119 (l1 ++ l2)
    ((n1 + i) + 1) (count + 1) can).
  { eapply paren_scan_open_119; eauto. }
  subst can.
  pose proof (paren_scan_can_one_nonnegative_119 (l1 ++ l2)
    ((n1 + i) + 1) (count + 1) Hstep).
  lia.
Qed.

Lemma proof_of_match_parens_entail_wit_6_1 : match_parens_entail_wit_6_1.
Proof.
  unfold match_parens_entail_wit_6_1; intros.
  rewrite <- derivable1_orp_intros2; entailer!.
  replace (n1 + (i + 1)) with ((n1 + i) + 1) by lia; exact PreH15.
Qed.

Lemma proof_of_match_parens_entail_wit_6_2 : match_parens_entail_wit_6_2.
Proof.
  unfold match_parens_entail_wit_6_2; intros.
  rewrite <- derivable1_orp_intros2; entailer!.
  replace (n1 + (i + 1)) with ((n1 + i) + 1) by lia; exact PreH15.
Qed.

Lemma proof_of_match_parens_entail_wit_6_3 : match_parens_entail_wit_6_3.
Proof.
  unfold match_parens_entail_wit_6_3; intros.
  rewrite <- derivable1_orp_intros1; entailer!.
  replace (n1 + (i + 1)) with ((n1 + i) + 1) by lia; exact PreH15.
Qed.

Lemma proof_of_match_parens_entail_wit_6_4 : match_parens_entail_wit_6_4.
Proof.
  unfold match_parens_entail_wit_6_4; intros.
  rewrite <- derivable1_orp_intros1; entailer!.
  replace (n1 + (i + 1)) with ((n1 + i) + 1) by lia; exact PreH15.
Qed.

Lemma proof_of_match_parens_entail_wit_7_1 : match_parens_entail_wit_7_1.
Proof.
  left.
  pre_process.
  assert (Hfull : paren_scan_state_119 (l1 ++ l2)
    (Zlength l1 + Zlength l2) count can).
  { replace (Zlength l1 + Zlength l2) with (n1 + i)
      by (unfold string_lib.string_length in *; lia).
    exact PreH18. }
  pose proof (problem_119_spec_total_nonzero l1 l2 count can
    PreH15 PreH16 Hfull PreH1) as Hspec.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_7_2 : match_parens_entail_wit_7_2.
Proof.
  unfold match_parens_entail_wit_7_2; left; intros.
  assert (Hfull : paren_scan_state_119 (l1 ++ l2)
    (Zlength l1 + Zlength l2) count can).
  { replace (Zlength l1 + Zlength l2) with (n1 + i)
      by (unfold string_lib.string_length in *; lia).
    exact PreH18. }
  pose proof (problem_119_spec_total_nonzero l1 l2 count can
    PreH15 PreH16 Hfull PreH1) as Hspec.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_8 : match_parens_entail_wit_8.
Proof.
  unfold match_parens_entail_wit_8; left; intros.
  assert (Hfull : paren_scan_state_119 (l1 ++ l2)
    (Zlength l1 + Zlength l2) 0 1).
  { replace (Zlength l1 + Zlength l2) with (n1 + i)
      by (unfold string_lib.string_length in *; lia).
    rewrite <- PreH2, <- PreH1; exact PreH19. }
  pose proof (problem_119_spec_left_yes l1 l2 PreH16 PreH17 Hfull) as Hspec.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_9 : match_parens_entail_wit_9.
Proof.
  unfold match_parens_entail_wit_9; intros.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  - apply paren_scan_initial_119.
  - subst count; subst can.
    replace (n1 + n2) with (n1 + i) by lia; exact PreH19.
Qed.

Lemma proof_of_match_parens_entail_wit_10_1 : match_parens_entail_wit_10_1.
Proof.
  unfold match_parens_entail_wit_10_1; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l1); lia. }
  pose proof (paren_code_at_119 l2 i PreH17 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hnext : paren_scan_state_119 (l2 ++ l1) (i + 1) (count - 1) can).
    { eapply paren_scan_close_nonnegative_119.
      - exact PreH20. - exact Hwhole.
      - rewrite app_Znth1 by lia; exact H41. - lia. }
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_10_2 : match_parens_entail_wit_10_2.
Proof.
  unfold match_parens_entail_wit_10_2; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l1); lia. }
  pose proof (paren_code_at_119 l2 i PreH17 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hnext : paren_scan_state_119 (l2 ++ l1) (i + 1) (count - 1) can).
    { eapply paren_scan_close_nonnegative_119.
      - exact PreH20. - exact Hwhole.
      - rewrite app_Znth1 by lia; exact H41. - lia. }
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_10_3 : match_parens_entail_wit_10_3.
Proof.
  unfold match_parens_entail_wit_10_3; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l1); lia. }
  assert (H40 : Znth i l2 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hnext : paren_scan_state_119 (l2 ++ l1) (i + 1) (count + 1) can).
  { eapply paren_scan_open_119.
    - exact PreH20. - exact Hwhole.
    - rewrite app_Znth1 by lia; exact H40. }
  do 3 rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_10_4 : match_parens_entail_wit_10_4.
Proof.
  unfold match_parens_entail_wit_10_4; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l1); lia. }
  assert (H40 : Znth i l2 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hnext : paren_scan_state_119 (l2 ++ l1) (i + 1) (count + 1) can).
  { eapply paren_scan_open_119.
    - exact PreH20. - exact Hwhole.
    - rewrite app_Znth1 by lia; exact H40. }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_10_5 : match_parens_entail_wit_10_5.
Proof.
  unfold match_parens_entail_wit_10_5; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l1); lia. }
  pose proof (paren_code_at_119 l2 i PreH17 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hnext : paren_scan_state_119 (l2 ++ l1) (i + 1) (count - 1) 0).
    { eapply paren_scan_close_negative_119.
      - exact PreH20. - exact Hwhole.
      - rewrite app_Znth1 by lia; exact H41. - lia. }
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_10_6 : match_parens_entail_wit_10_6.
Proof.
  unfold match_parens_entail_wit_10_6; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l1); lia. }
  pose proof (paren_code_at_119 l2 i PreH17 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hnext : paren_scan_state_119 (l2 ++ l1) (i + 1) (count - 1) 0).
    { eapply paren_scan_close_negative_119.
      - exact PreH20. - exact Hwhole.
      - rewrite app_Znth1 by lia; exact H41. - lia. }
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_10_7 : match_parens_entail_wit_10_7.
Proof.
  unfold match_parens_entail_wit_10_7; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l1); lia. }
  assert (H40 : Znth i l2 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hnext : paren_scan_state_119 (l2 ++ l1) (i + 1) (count + 1) can).
  { eapply paren_scan_open_119.
    - exact PreH20. - exact Hwhole.
    - rewrite app_Znth1 by lia; exact H40. }
  subst can.
  pose proof (paren_scan_can_one_nonnegative_119 (l2 ++ l1)
    (i + 1) (count + 1) Hnext).
  lia.
Qed.

Lemma proof_of_match_parens_entail_wit_10_8 : match_parens_entail_wit_10_8.
Proof.
  unfold match_parens_entail_wit_10_8; intros.
  assert (Hi : 0 <= i < Zlength l2).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; pose proof (Zlength_nonneg l1); lia. }
  assert (H40 : Znth i l2 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hnext : paren_scan_state_119 (l2 ++ l1) (i + 1) (count + 1) can).
  { eapply paren_scan_open_119.
    - exact PreH20. - exact Hwhole.
    - rewrite app_Znth1 by lia; exact H40. }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  rewrite <- PreH10; exact Hnext.
Qed.

Lemma proof_of_match_parens_entail_wit_12_1 : match_parens_entail_wit_12_1.
Proof.
  unfold match_parens_entail_wit_12_1; intros.
  rewrite <- derivable1_orp_intros1; entailer!.
  - replace (n2 + 0) with i by lia; exact PreH18.
  - pose proof (Zlength_nonneg l1).
    unfold string_lib.string_length in *; lia.
Qed.

Lemma proof_of_match_parens_entail_wit_12_2 : match_parens_entail_wit_12_2.
Proof.
  unfold match_parens_entail_wit_12_2; intros.
  rewrite <- derivable1_orp_intros2; entailer!.
  - replace (n2 + 0) with i by lia; exact PreH18.
  - pose proof (Zlength_nonneg l1).
    unfold string_lib.string_length in *; lia.
Qed.

Lemma proof_of_match_parens_entail_wit_13_1 : match_parens_entail_wit_13_1.
Proof.
  unfold match_parens_entail_wit_13_1; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n2 + i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  pose proof (paren_code_at_119 l1 i PreH16 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hchar : Znth (n2 + i) (l2 ++ l1) 0 = 41).
    { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
      replace (n2 + i - Zlength l2) with i
        by (unfold string_lib.string_length in *; lia); exact H41. }
    assert (Hstep : paren_scan_state_119 (l2 ++ l1)
      ((n2 + i) + 1) (count - 1) can).
    { eapply paren_scan_close_nonnegative_119; eauto; lia. }
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros1.
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_13_2 : match_parens_entail_wit_13_2.
Proof.
  unfold match_parens_entail_wit_13_2; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n2 + i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  pose proof (paren_code_at_119 l1 i PreH16 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hchar : Znth (n2 + i) (l2 ++ l1) 0 = 41).
    { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
      replace (n2 + i - Zlength l2) with i
        by (unfold string_lib.string_length in *; lia); exact H41. }
    assert (Hstep : paren_scan_state_119 (l2 ++ l1)
      ((n2 + i) + 1) (count - 1) can).
    { eapply paren_scan_close_nonnegative_119; eauto; lia. }
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_13_3 : match_parens_entail_wit_13_3.
Proof.
  unfold match_parens_entail_wit_13_3; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n2 + i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  assert (H40 : Znth i l1 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hchar : Znth (n2 + i) (l2 ++ l1) 0 = 40).
  { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
    replace (n2 + i - Zlength l2) with i
      by (unfold string_lib.string_length in *; lia); exact H40. }
  assert (Hstep : paren_scan_state_119 (l2 ++ l1)
    ((n2 + i) + 1) (count + 1) can).
  { eapply paren_scan_open_119; eauto. }
  do 3 rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_13_4 : match_parens_entail_wit_13_4.
Proof.
  unfold match_parens_entail_wit_13_4; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n2 + i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  assert (H40 : Znth i l1 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hchar : Znth (n2 + i) (l2 ++ l1) 0 = 40).
  { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
    replace (n2 + i - Zlength l2) with i
      by (unfold string_lib.string_length in *; lia); exact H40. }
  assert (Hstep : paren_scan_state_119 (l2 ++ l1)
    ((n2 + i) + 1) (count + 1) can).
  { eapply paren_scan_open_119; eauto. }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_13_5 : match_parens_entail_wit_13_5.
Proof.
  unfold match_parens_entail_wit_13_5; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n2 + i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  pose proof (paren_code_at_119 l1 i PreH16 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hchar : Znth (n2 + i) (l2 ++ l1) 0 = 41).
    { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
      replace (n2 + i - Zlength l2) with i
        by (unfold string_lib.string_length in *; lia); exact H41. }
    assert (Hstep : paren_scan_state_119 (l2 ++ l1)
      ((n2 + i) + 1) (count - 1) 0).
    { eapply paren_scan_close_negative_119; eauto; lia. }
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_13_6 : match_parens_entail_wit_13_6.
Proof.
  unfold match_parens_entail_wit_13_6; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n2 + i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  pose proof (paren_code_at_119 l1 i PreH16 Hi) as [H40 | H41].
  - exfalso; apply PreH2.
    rewrite string_lib.c_string_Znth_inside; auto.
  - assert (Hchar : Znth (n2 + i) (l2 ++ l1) 0 = 41).
    { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
      replace (n2 + i - Zlength l2) with i
        by (unfold string_lib.string_length in *; lia); exact H41. }
    assert (Hstep : paren_scan_state_119 (l2 ++ l1)
      ((n2 + i) + 1) (count - 1) 0).
    { eapply paren_scan_close_negative_119; eauto; lia. }
    rewrite <- derivable1_orp_intros2.
    entailer!.
    rewrite string_lib.c_string_Znth_inside; auto.
Qed.

Lemma proof_of_match_parens_entail_wit_13_7 : match_parens_entail_wit_13_7.
Proof.
  unfold match_parens_entail_wit_13_7; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n2 + i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  assert (H40 : Znth i l1 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hchar : Znth (n2 + i) (l2 ++ l1) 0 = 40).
  { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
    replace (n2 + i - Zlength l2) with i
      by (unfold string_lib.string_length in *; lia); exact H40. }
  assert (Hstep : paren_scan_state_119 (l2 ++ l1)
    ((n2 + i) + 1) (count + 1) can).
  { eapply paren_scan_open_119; eauto. }
  subst can.
  pose proof (paren_scan_can_one_nonnegative_119 (l2 ++ l1)
    ((n2 + i) + 1) (count + 1) Hstep).
  lia.
Qed.

Lemma proof_of_match_parens_entail_wit_13_8 : match_parens_entail_wit_13_8.
Proof.
  unfold match_parens_entail_wit_13_8; intros.
  assert (Hi : 0 <= i < Zlength l1).
  { unfold string_lib.string_length in *; lia. }
  assert (Hwhole : n2 + i < Zlength (l2 ++ l1)).
  { rewrite Zlength_app; unfold string_lib.string_length in *; lia. }
  assert (H40 : Znth i l1 0 = 40).
  { rewrite string_lib.c_string_Znth_inside in PreH2; auto. }
  assert (Hchar : Znth (n2 + i) (l2 ++ l1) 0 = 40).
  { rewrite app_Znth2 by (unfold string_lib.string_length in *; lia).
    replace (n2 + i - Zlength l2) with i
      by (unfold string_lib.string_length in *; lia); exact H40. }
  assert (Hstep : paren_scan_state_119 (l2 ++ l1)
    ((n2 + i) + 1) (count + 1) can).
  { eapply paren_scan_open_119; eauto. }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros2.
  entailer!.
  replace (n2 + (i + 1)) with ((n2 + i) + 1) by lia.
  rewrite <- PreH10; exact Hstep.
Qed.

Lemma proof_of_match_parens_entail_wit_14_1 : match_parens_entail_wit_14_1.
Proof.
  unfold match_parens_entail_wit_14_1; intros.
  rewrite <- derivable1_orp_intros2; entailer!.
  replace (n2 + (i + 1)) with ((n2 + i) + 1) by lia; exact PreH16.
Qed.

Lemma proof_of_match_parens_entail_wit_14_2 : match_parens_entail_wit_14_2.
Proof.
  unfold match_parens_entail_wit_14_2; intros.
  rewrite <- derivable1_orp_intros2; entailer!.
  replace (n2 + (i + 1)) with ((n2 + i) + 1) by lia; exact PreH16.
Qed.

Lemma proof_of_match_parens_entail_wit_14_3 : match_parens_entail_wit_14_3.
Proof.
  unfold match_parens_entail_wit_14_3; intros.
  rewrite <- derivable1_orp_intros1; entailer!.
  replace (n2 + (i + 1)) with ((n2 + i) + 1) by lia; exact PreH16.
Qed.

Lemma proof_of_match_parens_entail_wit_14_4 : match_parens_entail_wit_14_4.
Proof.
  unfold match_parens_entail_wit_14_4; intros.
  rewrite <- derivable1_orp_intros1; entailer!.
  replace (n2 + (i + 1)) with ((n2 + i) + 1) by lia; exact PreH16.
Qed.

Lemma proof_of_match_parens_entail_wit_15 : match_parens_entail_wit_15.
Proof.
  unfold match_parens_entail_wit_15; left; intros.
  assert (Hleft : paren_scan_state_119 (l1 ++ l2)
    (Zlength l1 + Zlength l2) 0 0).
  { replace (Zlength l1 + Zlength l2) with (n1 + n2)
      by (unfold string_lib.string_length in *; lia).
    exact PreH18. }
  assert (Hright : paren_scan_state_119 (l2 ++ l1)
    (Zlength l2 + Zlength l1) count 1).
  { replace (Zlength l2 + Zlength l1) with (n2 + i)
      by (unfold string_lib.string_length in *; lia).
    rewrite <- PreH1; exact PreH19. }
  pose proof (problem_119_spec_right_yes l1 l2 count PreH15 PreH16
    Hleft Hright) as Hspec.
  entailer!.
Qed.

Lemma proof_of_match_parens_entail_wit_16 : match_parens_entail_wit_16.
Proof.
  unfold match_parens_entail_wit_16; left; intros.
  assert (Hleft : paren_scan_state_119 (l1 ++ l2)
    (Zlength l1 + Zlength l2) 0 0).
  { replace (Zlength l1 + Zlength l2) with (n1 + n2)
      by (unfold string_lib.string_length in *; lia).
    exact PreH18. }
  assert (Hright : paren_scan_state_119 (l2 ++ l1)
    (Zlength l2 + Zlength l1) count 0).
  { replace (Zlength l2 + Zlength l1) with (n2 + i)
      by (unfold string_lib.string_length in *; lia).
    rewrite <- PreH9; exact PreH19. }
  pose proof (problem_119_spec_both_no l1 l2 count PreH15 PreH16
    Hleft Hright) as Hspec.
  entailer!.
Qed.

Lemma proof_of_match_parens_partial_solve_wit_1_pure : match_parens_partial_solve_wit_1_pure.
Proof.
  unfold match_parens_partial_solve_wit_1_pure; left; intros.
  entailer!.
  pose proof (Zlength_nonneg l2).
  unfold string_lib.string_length in *; lia.
Qed.

Lemma proof_of_match_parens_partial_solve_wit_2_pure : match_parens_partial_solve_wit_2_pure.
Proof.
  unfold match_parens_partial_solve_wit_2_pure; left; intros.
  entailer!.
  pose proof (Zlength_nonneg l1).
  unfold string_lib.string_length in *; lia.
Qed.
