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
From SimpleC.EE Require Import string_to_upper_ascii_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_to_upper_ascii.
Local Open Scope sac.

Lemma string_to_upper_ascii_spec_app :
  forall a b,
    string_to_upper_ascii_spec (a ++ b) =
    string_to_upper_ascii_spec a ++ string_to_upper_ascii_spec b.
Proof.
  induction a; intros b; simpl; auto.
  rewrite IHa; auto.
Qed.

Lemma string_to_upper_ascii_spec_zlength :
  forall a,
    Zlength (string_to_upper_ascii_spec a) = Zlength a.
Proof.
  induction a; simpl; auto.
  rewrite !Zlength_cons; lia.
Qed.

Lemma upper_ascii_char_low :
  forall x, x < 97 -> upper_ascii_char x = x.
Proof.
  intros x Hx.
  unfold upper_ascii_char.
  destruct (Z_le_dec 97 x); [lia | reflexivity].
Qed.

Lemma upper_ascii_char_high :
  forall x, x > 122 -> upper_ascii_char x = x.
Proof.
  intros x Hx.
  unfold upper_ascii_char.
  destruct (Z_le_dec 97 x).
  - destruct (Z_le_dec x 122); [lia | reflexivity].
  - reflexivity.
Qed.

Lemma upper_ascii_char_between :
  forall x, 97 <= x -> x <= 122 -> upper_ascii_char x = x - 97 + 65.
Proof.
  intros x Hlo Hhi.
  unfold upper_ascii_char.
  destruct (Z_le_dec 97 x).
  - destruct (Z_le_dec x 122); [reflexivity | lia].
  - lia.
Qed.

Lemma current_head_after_prefix :
  forall l1 x xs i,
    Zlength l1 = i ->
    Znth i ((string_to_upper_ascii_spec l1 ++ x :: xs) ++ 0 :: nil) 0 = x.
Proof.
  intros l1 x xs i Hlen.
  rewrite app_Znth1.
  - rewrite app_Znth2 by (rewrite string_to_upper_ascii_spec_zlength; lia).
    rewrite string_to_upper_ascii_spec_zlength.
    replace (i - Zlength l1) with 0 by lia.
    simpl; reflexivity.
  - repeat rewrite Zlength_app.
    rewrite string_to_upper_ascii_spec_zlength.
    rewrite Zlength_cons.
    rewrite Hlen.
    pose proof (Zlength_nonneg xs).
    pose proof (Zlength_nonneg l1).
    lia.
Qed.

Lemma replace_lowercase_head_after_prefix :
  forall l1 x xs i,
    Zlength l1 = i ->
    97 <= x ->
    x <= 122 ->
    replace_Znth i (x - 97 + 65)
      ((string_to_upper_ascii_spec l1 ++ x :: xs) ++ 0 :: nil) =
    (string_to_upper_ascii_spec (l1 ++ x :: nil) ++ xs) ++ 0 :: nil.
Proof.
  intros l1 x xs i Hlen Hlo Hhi.
  rewrite string_to_upper_ascii_spec_app.
  simpl.
  rewrite upper_ascii_char_between by lia.
  rewrite <- app_assoc.
  rewrite replace_Znth_app_r by (rewrite string_to_upper_ascii_spec_zlength; lia).
  rewrite replace_Znth_nothing by (rewrite string_to_upper_ascii_spec_zlength; lia).
  rewrite string_to_upper_ascii_spec_zlength.
  replace (i - Zlength l1) with 0 by lia.
  unfold replace_Znth.
  simpl.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma preserve_nonlower_head_after_prefix :
  forall l1 x xs,
    upper_ascii_char x = x ->
    (string_to_upper_ascii_spec (l1 ++ x :: nil) ++ xs) ++ 0 :: nil =
    (string_to_upper_ascii_spec l1 ++ x :: xs) ++ 0 :: nil.
Proof.
  intros l1 x xs Hx.
  rewrite string_to_upper_ascii_spec_app.
  simpl.
  rewrite Hx.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_1 : string_to_upper_ascii_entail_wit_1.
Proof.
  pre_process.
  prop_apply CharArray.full_length. Intros.
  Exists (@nil Z) l.
  entailer!.
  rewrite <- Zlength_correct in H2.
  rewrite Zlength_app_cons in H2.
  lia.
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_2_1 : string_to_upper_ascii_entail_wit_2_1.
Proof.
  pre_process.
  destruct l2_2 eqn:Hl2.
  - rewrite Zlength_nil in H7.
    rewrite app_nil_r in H2.
    rewrite app_Znth2 in H2 by (rewrite string_to_upper_ascii_spec_zlength; lia).
    rewrite string_to_upper_ascii_spec_zlength in H2.
    replace (i - Zlength l1_2) with 0 in H2 by lia.
    simpl in H2. contradiction H2. reflexivity.
  - rename z into x. rename l0 into xs.
    assert (Hcur :
      Znth i ((string_to_upper_ascii_spec l1_2 ++ x :: xs) ++ 0 :: nil) 0 = x)
      by (apply current_head_after_prefix; exact H6).
    rewrite Hcur in H0.
    rewrite Hcur in H1.
    rewrite Hcur in H2.
    assert (Hrep :
      replace_Znth i
        (Znth i ((string_to_upper_ascii_spec l1_2 ++ x :: xs) ++ 0 :: nil) 0 - 97 + 65)
        ((string_to_upper_ascii_spec l1_2 ++ x :: xs) ++ 0 :: nil) =
      (string_to_upper_ascii_spec (l1_2 ++ x :: nil) ++ xs) ++ 0 :: nil).
    {
      rewrite Hcur.
      apply replace_lowercase_head_after_prefix; lia.
    }
    rewrite Hrep.
    Exists (l1_2 ++ cons x nil) xs.
    entailer!;
      try (rewrite H5; rewrite <- app_assoc; reflexivity);
      try (rewrite Zlength_app_cons; lia);
      try (rewrite Zlength_cons in H7; pose proof (Zlength_nonneg xs); lia).
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_2_2 : string_to_upper_ascii_entail_wit_2_2.
Proof.
  pre_process.
  destruct l2_2 eqn:Hl2.
  - rewrite Zlength_nil in H5.
    rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by (rewrite string_to_upper_ascii_spec_zlength; lia).
    rewrite string_to_upper_ascii_spec_zlength in H0.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0. contradiction H0. reflexivity.
  - rename z into x. rename l0 into xs.
    assert (Hcur :
      Znth i ((string_to_upper_ascii_spec l1_2 ++ x :: xs) ++ 0 :: nil) 0 = x)
      by (apply current_head_after_prefix; exact H4).
    Exists (l1_2 ++ cons x nil) xs.
    replace ((string_to_upper_ascii_spec (l1_2 ++ x :: nil) ++ xs) ++ 0 :: nil)
      with ((string_to_upper_ascii_spec l1_2 ++ x :: xs) ++ 0 :: nil).
    + entailer!;
        try (rewrite H3; rewrite <- app_assoc; reflexivity);
        try (rewrite Zlength_app_cons; lia);
        try (rewrite Zlength_cons in H5; pose proof (Zlength_nonneg xs); lia).
    + symmetry.
      apply preserve_nonlower_head_after_prefix.
      apply upper_ascii_char_low.
      rewrite Hcur in H.
      lia.
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_2_3 : string_to_upper_ascii_entail_wit_2_3.
Proof.
  pre_process.
  destruct l2_2 eqn:Hl2.
  - rewrite Zlength_nil in H6.
    rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by (rewrite string_to_upper_ascii_spec_zlength; lia).
    rewrite string_to_upper_ascii_spec_zlength in H0.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    change (Znth 0 (0 :: nil) 0) with 0 in H0.
    lia.
  - rename z into x. rename l0 into xs.
    assert (Hcur :
      Znth i ((string_to_upper_ascii_spec l1_2 ++ x :: xs) ++ 0 :: nil) 0 = x)
      by (apply current_head_after_prefix; exact H5).
    Exists (l1_2 ++ cons x nil) xs.
    replace ((string_to_upper_ascii_spec (l1_2 ++ x :: nil) ++ xs) ++ 0 :: nil)
      with ((string_to_upper_ascii_spec l1_2 ++ x :: xs) ++ 0 :: nil).
    + entailer!;
        try (rewrite H4; rewrite <- app_assoc; reflexivity);
        try (rewrite Zlength_app_cons; lia);
        try (rewrite Zlength_cons in H6; pose proof (Zlength_nonneg xs); lia).
    + symmetry.
      apply preserve_nonlower_head_after_prefix.
      apply upper_ascii_char_high.
      rewrite Hcur in H.
      lia.
Qed.

Lemma proof_of_string_to_upper_ascii_return_wit_1 : string_to_upper_ascii_return_wit_1.
Proof.
  pre_process.
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - destruct l2 eqn:Hl2.
      + rewrite Zlength_nil in H4. lia.
      + rename z into x. rename l0 into xs.
        assert (Hcur :
          Znth i ((string_to_upper_ascii_spec l1 ++ x :: xs) ++ 0 :: nil) 0 = x)
          by (apply current_head_after_prefix; exact H3).
        rewrite Hcur in H.
        assert (Horig : Znth i l 0 = x).
        {
          rewrite H2.
          rewrite app_Znth2 by lia.
          replace (i - Zlength l1) with 0 by lia.
          simpl; reflexivity.
        }
        specialize (H8 i).
        rewrite Horig in H8.
        contradiction H8; lia.
    - lia.
  }
  subst i.
  destruct l2 eqn:Hl2.
  - rewrite app_nil_r in H2.
    subst l.
    rewrite app_nil_r.
    entailer!.
  - rewrite Zlength_cons in H4.
    pose proof (Zlength_nonneg l0).
    lia.
Qed.
