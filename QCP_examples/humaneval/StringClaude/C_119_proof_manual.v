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
From SimpleC.EE Require Import C_119_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_119.
Local Open Scope sac.

Ltac mp_base :=
  pre_process; subst; entailer!;
  try rewrite paren_level_upto_0;
  try rewrite paren_good_prefix_flag_0;
  try lia.

Ltac normalize_input_char :=
  repeat match goal with
  | Hlen : Zlength ?l = ?n,
    Hi : ?i < ?n,
    Hc : Znth ?i (app ?l (cons 0 nil)) 0 = ?v |- _ =>
      rewrite Znth_app_left_119 in Hc by lia
  | Hlen : Zlength ?l = ?n,
    Hi : ?i < ?n,
    Hc : Znth ?i (app ?l (cons 0 nil)) 0 <> ?v |- _ =>
      rewrite Znth_app_left_119 in Hc by lia
  end.

Ltac rewrite_concat_left l1 l2 i :=
  rewrite (Znth_app_left_119 l1 l2 i 0) by lia.

Ltac rewrite_concat_right l1 l2 i :=
  rewrite (Znth_app_right_119 l1 l2 i 0) by lia;
  replace (i - Zlength l1) with (i - Zlength l1) by lia.

Ltac prove_flag_nonneg idx lst newlevel can :=
  let Hflag := fresh "Hflag" in
  destruct (paren_good_prefix_flag_bool idx lst) as [Hflag | Hflag];
  rewrite <- can in Hflag; subst;
  [ rewrite paren_good_prefix_flag_step_bad by lia; reflexivity
  | eapply paren_good_prefix_flag_step_nonneg; try eassumption; lia ].

Ltac step_open_common idx lst Hchar :=
  rewrite (paren_level_upto_step_open idx lst) by (try lia; exact Hchar).

Ltac step_close_common idx lst Hchar :=
  rewrite (paren_level_upto_step_close idx lst) by (try lia; exact Hchar).

Ltac step_other_common idx lst H40 H41 :=
  rewrite (paren_level_upto_step_other idx lst) by (try lia; exact H40 || exact H41).

Ltac finish_negative_flag idx lst :=
  eapply paren_good_prefix_flag_step_neg; try eassumption; lia.

Ltac solve_l1_step :=
  pre_process; subst; normalize_input_char; entailer!;
  repeat match goal with
  | H : Znth ?i ?l 0 = 40 |- context[paren_level_upto (?i + 1) ?l] =>
      step_open_common i l H
  | H : Znth ?i ?l 0 = 41 |- context[paren_level_upto (?i + 1) ?l] =>
      step_close_common i l H
  | H40 : Znth ?i ?l 0 <> 40, H41 : Znth ?i ?l 0 <> 41 |- context[paren_level_upto (?i + 1) ?l] =>
      step_other_common i l H40 H41
  end;
  try match goal with
  | |- context[paren_good_prefix_flag (?i + 1) ?l] =>
      first [ finish_negative_flag i l
            | prove_flag_nonneg i l (paren_level_upto (i + 1) l) ltac:(match goal with H: ?can = paren_good_prefix_flag i l |- _ => exact H end) ]
  end;
  try lia.

Lemma proof_of_match_parens_entail_wit_1 : match_parens_entail_wit_1.
Proof.
  unfold match_parens_entail_wit_1.
  intros.
  mp_base.
Qed. 

Lemma proof_of_match_parens_entail_wit_2_1 : match_parens_entail_wit_2_1.
Proof.
  unfold match_parens_entail_wit_2_1.
  intros.
  pre_process; subst.
  assert (Hchar_concat : Znth i (l1 ++ l2) 0 = 40).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  symmetry.
  eapply (paren_good_prefix_flag_step_neg i (l1 ++ l2)
    (paren_level_upto i (l1 ++ l2) + 1)).
  - lia.
  - rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_2_2 : match_parens_entail_wit_2_2.
Proof.
  unfold match_parens_entail_wit_2_2.
  intros.
  pre_process; subst.
  assert (Hchar_concat : Znth i (l1 ++ l2) 0 = 41).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  symmetry.
  eapply (paren_good_prefix_flag_step_neg i (l1 ++ l2)
    (paren_level_upto i (l1 ++ l2) - 1)).
  - lia.
  - rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_2_3 : match_parens_entail_wit_2_3.
Proof.
  unfold match_parens_entail_wit_2_3.
  intros.
  pre_process; subst.
  pose proof (problem_119_pre_z_l1_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_match_parens_entail_wit_2_4 : match_parens_entail_wit_2_4.
Proof.
  unfold match_parens_entail_wit_2_4.
  intros.
  pre_process; subst.
  pose proof (problem_119_pre_z_l1_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_match_parens_entail_wit_2_5 : match_parens_entail_wit_2_5.
Proof.
  unfold match_parens_entail_wit_2_5.
  intros.
  pre_process; subst.
  assert (Hchar_concat : Znth i (l1 ++ l2) 0 = 41).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  destruct (paren_good_prefix_flag_bool i (l1 ++ l2)) as [Hflag | Hflag].
  - rewrite Hflag.
    symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag.
    symmetry.
    eapply (paren_good_prefix_flag_step_nonneg i (l1 ++ l2)
      (paren_level_upto i (l1 ++ l2) - 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_2_6 : match_parens_entail_wit_2_6.
Proof.
  unfold match_parens_entail_wit_2_6.
  intros.
  pre_process; subst.
  assert (Hchar_concat : Znth i (l1 ++ l2) 0 = 40).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  destruct (paren_good_prefix_flag_bool i (l1 ++ l2)) as [Hflag | Hflag].
  - rewrite Hflag.
    symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag.
    symmetry.
    eapply (paren_good_prefix_flag_step_nonneg i (l1 ++ l2)
      (paren_level_upto i (l1 ++ l2) + 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_4_1 : match_parens_entail_wit_4_1.
Proof.
  unfold match_parens_entail_wit_4_1.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l1 + i) (l1 ++ l2) 0 = 40).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l1 + i - Zlength l1) with i by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia;
            rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia.
  symmetry.
  eapply (paren_good_prefix_flag_step_neg (Zlength l1 + i) (l1 ++ l2)
    (paren_level_upto (Zlength l1 + i) (l1 ++ l2) + 1)).
  - lia.
  - rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_4_2 : match_parens_entail_wit_4_2.
Proof.
  unfold match_parens_entail_wit_4_2.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l1 + i) (l1 ++ l2) 0 = 41).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l1 + i - Zlength l1) with i by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia;
            rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia.
  symmetry.
  eapply (paren_good_prefix_flag_step_neg (Zlength l1 + i) (l1 ++ l2)
    (paren_level_upto (Zlength l1 + i) (l1 ++ l2) - 1)).
  - lia.
  - rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_4_3 : match_parens_entail_wit_4_3.
Proof.
  unfold match_parens_entail_wit_4_3.
  intros; pre_process; subst.
  pose proof (problem_119_pre_z_l2_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_match_parens_entail_wit_4_4 : match_parens_entail_wit_4_4.
Proof.
  unfold match_parens_entail_wit_4_4.
  intros; pre_process; subst.
  pose proof (problem_119_pre_z_l2_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_match_parens_entail_wit_4_5 : match_parens_entail_wit_4_5.
Proof.
  unfold match_parens_entail_wit_4_5.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l1 + i) (l1 ++ l2) 0 = 41).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l1 + i - Zlength l1) with i by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia;
            rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia.
  destruct (paren_good_prefix_flag_bool (Zlength l1 + i) (l1 ++ l2)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg (Zlength l1 + i) (l1 ++ l2)
      (paren_level_upto (Zlength l1 + i) (l1 ++ l2) - 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_4_6 : match_parens_entail_wit_4_6.
Proof.
  unfold match_parens_entail_wit_4_6.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l1 + i) (l1 ++ l2) 0 = 40).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l1 + i - Zlength l1) with i by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia;
            rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  replace (Zlength l1 + (i + 1)) with (Zlength l1 + i + 1) by lia.
  destruct (paren_good_prefix_flag_bool (Zlength l1 + i) (l1 ++ l2)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg (Zlength l1 + i) (l1 ++ l2)
      (paren_level_upto (Zlength l1 + i) (l1 ++ l2) + 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_5 : match_parens_entail_wit_5.
Proof.
  unfold match_parens_entail_wit_5.
  intros.
  pre_process; subst.
  entailer!.
  all: try solve [lia].
  all: try solve [replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia; congruence].
  all: try solve [
    replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia;
    pose proof (paren_good_prefix_flag_bool (Zlength l1 + i) (l1 ++ l2));
    lia
  ].
Qed. 

Lemma proof_of_match_parens_entail_wit_6 : match_parens_entail_wit_6.
Proof.
  unfold match_parens_entail_wit_6.
  intros.
  pre_process; subst.
Qed.

Lemma proof_of_match_parens_entail_wit_7_1 : match_parens_entail_wit_7_1.
Proof.
  unfold match_parens_entail_wit_7_1.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth i (l2 ++ l1) 0 = 40).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  symmetry.
  eapply (paren_good_prefix_flag_step_neg i (l2 ++ l1)
    (paren_level_upto i (l2 ++ l1) + 1)).
  - lia.
  - rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_7_2 : match_parens_entail_wit_7_2.
Proof.
  unfold match_parens_entail_wit_7_2.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth i (l2 ++ l1) 0 = 41).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  symmetry.
  eapply (paren_good_prefix_flag_step_neg i (l2 ++ l1)
    (paren_level_upto i (l2 ++ l1) - 1)).
  - lia.
  - rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_7_3 : match_parens_entail_wit_7_3.
Proof.
  unfold match_parens_entail_wit_7_3.
  intros; pre_process; subst.
  pose proof (problem_119_pre_z_l2_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_match_parens_entail_wit_7_4 : match_parens_entail_wit_7_4.
Proof.
  unfold match_parens_entail_wit_7_4.
  intros; pre_process; subst.
  pose proof (problem_119_pre_z_l2_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l2 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_match_parens_entail_wit_7_5 : match_parens_entail_wit_7_5.
Proof.
  unfold match_parens_entail_wit_7_5.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth i (l2 ++ l1) 0 = 41).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  destruct (paren_good_prefix_flag_bool i (l2 ++ l1)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg i (l2 ++ l1)
      (paren_level_upto i (l2 ++ l1) - 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_7_6 : match_parens_entail_wit_7_6.
Proof.
  unfold match_parens_entail_wit_7_6.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth i (l2 ++ l1) 0 = 40).
  {
    rewrite Znth_app_left_119 by lia.
    match goal with
    | H : Znth i (app l2 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  destruct (paren_good_prefix_flag_bool i (l2 ++ l1)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg i (l2 ++ l1)
      (paren_level_upto i (l2 ++ l1) + 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_9_1 : match_parens_entail_wit_9_1.
Proof.
  unfold match_parens_entail_wit_9_1.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l2 + i) (l2 ++ l1) 0 = 40).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l2 + i - Zlength l2) with i by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia;
            rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia.
  symmetry.
  eapply (paren_good_prefix_flag_step_neg (Zlength l2 + i) (l2 ++ l1)
    (paren_level_upto (Zlength l2 + i) (l2 ++ l1) + 1)).
  - lia.
  - rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_9_2 : match_parens_entail_wit_9_2.
Proof.
  unfold match_parens_entail_wit_9_2.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l2 + i) (l2 ++ l1) 0 = 41).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l2 + i - Zlength l2) with i by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia;
            rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia.
  symmetry.
  eapply (paren_good_prefix_flag_step_neg (Zlength l2 + i) (l2 ++ l1)
    (paren_level_upto (Zlength l2 + i) (l2 ++ l1) - 1)).
  - lia.
  - rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
  - lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_9_3 : match_parens_entail_wit_9_3.
Proof.
  unfold match_parens_entail_wit_9_3.
  intros; pre_process; subst.
  pose proof (problem_119_pre_z_l1_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_match_parens_entail_wit_9_4 : match_parens_entail_wit_9_4.
Proof.
  unfold match_parens_entail_wit_9_4.
  intros; pre_process; subst.
  pose proof (problem_119_pre_z_l1_char l1 l2 i ltac:(eassumption) ltac:(eassumption) ltac:(lia)) as [Hc | Hc].
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 40) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
  - assert (Znth i (l1 ++ cons 0 nil) 0 = 41) by (rewrite Znth_app_left_119 by lia; exact Hc).
    congruence.
Qed. 

Lemma proof_of_match_parens_entail_wit_9_5 : match_parens_entail_wit_9_5.
Proof.
  unfold match_parens_entail_wit_9_5.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l2 + i) (l2 ++ l1) 0 = 41).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l2 + i - Zlength l2) with i by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 41 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia;
            rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat); lia).
  replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia.
  destruct (paren_good_prefix_flag_bool (Zlength l2 + i) (l2 ++ l1)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg (Zlength l2 + i) (l2 ++ l1)
      (paren_level_upto (Zlength l2 + i) (l2 ++ l1) - 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_close by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_match_parens_entail_wit_9_6 : match_parens_entail_wit_9_6.
Proof.
  unfold match_parens_entail_wit_9_6.
  intros; pre_process; subst.
  assert (Hchar_concat : Znth (Zlength l2 + i) (l2 ++ l1) 0 = 40).
  {
    rewrite Znth_app_right_119 by lia.
    replace (Zlength l2 + i - Zlength l2) with i by lia.
    match goal with
    | H : Znth i (app l1 (cons 0 nil)) 0 = 40 |- _ =>
        rewrite Znth_app_left_119 in H by lia; exact H
    end.
  }
  entailer!.
  all: try (replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia;
            rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat); lia).
  replace (Zlength l2 + (i + 1)) with (Zlength l2 + i + 1) by lia.
  destruct (paren_good_prefix_flag_bool (Zlength l2 + i) (l2 ++ l1)) as [Hflag | Hflag].
  - rewrite Hflag. symmetry. apply paren_good_prefix_flag_step_bad; lia.
  - rewrite Hflag. symmetry.
    eapply (paren_good_prefix_flag_step_nonneg (Zlength l2 + i) (l2 ++ l1)
      (paren_level_upto (Zlength l2 + i) (l2 ++ l1) + 1)).
    + lia.
    + exact Hflag.
    + rewrite paren_level_upto_step_open by (try lia; exact Hchar_concat). lia.
    + lia.
Qed. 

Lemma proof_of_match_parens_return_wit_1 : match_parens_return_wit_1.
Proof.
  unfold match_parens_return_wit_1.
  intros.
  pre_process; subst.
  entailer!.
  assert (Hflag21 : paren_good_prefix_flag (Zlength (l2 ++ l1)) (l2 ++ l1) = 0).
  {
    assert (Hneq : paren_good_prefix_flag (Zlength l2 + Zlength l1) (l2 ++ l1) <> 1).
    { replace (Zlength l2 + Zlength l1) with (Zlength l2 + i) by lia. congruence. }
    destruct (paren_good_prefix_flag_bool (Zlength l2 + Zlength l1) (l2 ++ l1)) as [Hflag0 | Hflag1].
    - replace (Zlength (l2 ++ l1)) with (Zlength l2 + Zlength l1) by (rewrite Zlength_app; lia).
      exact Hflag0.
    - exfalso. apply Hneq. exact Hflag1.
  }
  eapply problem_119_spec_z_false_from_flags; eauto.
  all: try (replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia); eassumption).
  all: try exact Hflag21.
Qed. 

Lemma proof_of_match_parens_return_wit_2 : match_parens_return_wit_2.
Proof.
  unfold match_parens_return_wit_2.
  intros.
  pre_process; subst.
  entailer!.
  eapply problem_119_spec_z_true_right; eauto.
  - rewrite <- (paren_total_app_comm l1 l2).
    replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia).
    eassumption.
  - replace (Zlength (l2 ++ l1)) with (Zlength l2 + Zlength l1) by (rewrite Zlength_app; lia).
    replace (Zlength l2 + Zlength l1) with (Zlength l2 + i) by lia.
    congruence.
Qed. 

Lemma proof_of_match_parens_return_wit_3 : match_parens_return_wit_3.
Proof.
  unfold match_parens_return_wit_3.
  intros.
  pre_process; subst.
  entailer!.
  eapply problem_119_spec_z_true_left; eauto.
  - replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia).
    replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia.
    congruence.
  - replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia).
    replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia.
    congruence.
Qed. 

Lemma proof_of_match_parens_return_wit_4 : match_parens_return_wit_4.
Proof.
  unfold match_parens_return_wit_4.
  intros.
  pre_process; subst.
  entailer!.
  eapply problem_119_spec_z_false_from_level; eauto.
  replace (Zlength (l1 ++ l2)) with (Zlength l1 + Zlength l2) by (rewrite Zlength_app; lia).
  replace (Zlength l1 + Zlength l2) with (Zlength l1 + i) by lia.
  congruence.
Qed. 
