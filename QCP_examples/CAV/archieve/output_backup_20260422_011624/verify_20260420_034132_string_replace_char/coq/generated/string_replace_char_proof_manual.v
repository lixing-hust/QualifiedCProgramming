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
From SimpleC.EE.CAV.verify_20260420_034132_string_replace_char Require Import string_replace_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_replace_char.
Local Open Scope sac.

Lemma string_replace_char_spec_app :
  forall a b old_c new_c,
    string_replace_char_spec (a ++ b) old_c new_c =
    string_replace_char_spec a old_c new_c ++
    string_replace_char_spec b old_c new_c.
Proof.
  induction a; intros b old_c new_c; simpl; auto.
  rewrite IHa; auto.
Qed.

Lemma string_replace_char_spec_zlength :
  forall a old_c new_c,
    Zlength (string_replace_char_spec a old_c new_c) = Zlength a.
Proof.
  induction a; intros old_c new_c; simpl; auto.
  rewrite !Zlength_cons.
  rewrite IHa.
  reflexivity.
Qed.

Lemma replace_char_eq :
  forall x old_c new_c,
    x = old_c ->
    replace_char x old_c new_c = new_c.
Proof.
  intros x old_c new_c Hx.
  unfold replace_char.
  destruct (Z.eq_dec x old_c); [reflexivity | lia].
Qed.

Lemma replace_char_neq :
  forall x old_c new_c,
    x <> old_c ->
    replace_char x old_c new_c = x.
Proof.
  intros x old_c new_c Hx.
  unfold replace_char.
  destruct (Z.eq_dec x old_c); [lia | reflexivity].
Qed.

Lemma current_head_after_prefix :
  forall l1 x xs i old_c new_c,
    Zlength l1 = i ->
    Znth i
      ((string_replace_char_spec l1 old_c new_c ++ x :: xs) ++ 0 :: nil) 0 = x.
Proof.
  intros l1 x xs i old_c new_c Hlen.
  rewrite app_Znth1.
  - rewrite app_Znth2 by (rewrite string_replace_char_spec_zlength; lia).
    rewrite string_replace_char_spec_zlength.
    replace (i - Zlength l1) with 0 by lia.
    simpl; reflexivity.
  - repeat rewrite Zlength_app.
    rewrite string_replace_char_spec_zlength.
    rewrite Zlength_cons.
    rewrite Hlen.
    pose proof (Zlength_nonneg xs).
    pose proof (Zlength_nonneg l1).
    lia.
Qed.

Lemma replace_old_head_after_prefix :
  forall l1 x xs i old_c new_c,
    Zlength l1 = i ->
    x = old_c ->
    replace_Znth i new_c
      ((string_replace_char_spec l1 old_c new_c ++ x :: xs) ++ 0 :: nil) =
    (string_replace_char_spec (l1 ++ x :: nil) old_c new_c ++ xs) ++ 0 :: nil.
Proof.
  intros l1 x xs i old_c new_c Hlen Hx.
  rewrite string_replace_char_spec_app.
  simpl.
  rewrite replace_char_eq by exact Hx.
  rewrite <- app_assoc.
  rewrite replace_Znth_app_r by (rewrite string_replace_char_spec_zlength; lia).
  rewrite replace_Znth_nothing by (rewrite string_replace_char_spec_zlength; lia).
  rewrite string_replace_char_spec_zlength.
  replace (i - Zlength l1) with 0 by lia.
  unfold replace_Znth.
  simpl.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma preserve_nonold_head_after_prefix :
  forall l1 x xs old_c new_c,
    x <> old_c ->
    (string_replace_char_spec (l1 ++ x :: nil) old_c new_c ++ xs) ++ 0 :: nil =
    (string_replace_char_spec l1 old_c new_c ++ x :: xs) ++ 0 :: nil.
Proof.
  intros l1 x xs old_c new_c Hx.
  rewrite string_replace_char_spec_app.
  simpl.
  rewrite replace_char_neq by exact Hx.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma proof_of_string_replace_char_entail_wit_1 : string_replace_char_entail_wit_1.
Proof.
  pre_process.
  prop_apply CharArray.full_length. Intros.
  Exists (@nil Z) l.
  entailer!.
Qed.

Lemma proof_of_string_replace_char_entail_wit_2_1 : string_replace_char_entail_wit_2_1.
Proof.
  pre_process.
  destruct l2_2 eqn:Hl2.
  - rewrite Zlength_nil in H7.
    rewrite app_nil_r in H1.
    rewrite app_Znth2 in H1 by (rewrite string_replace_char_spec_zlength; lia).
    rewrite string_replace_char_spec_zlength in H1.
    replace (i - Zlength l1_2) with 0 in H1 by lia.
    simpl in H1. contradiction H1. reflexivity.
  - rename z into x. rename l0 into xs.
    assert (Hcur :
      Znth i ((string_replace_char_spec l1_2 old_c_pre new_c_pre ++ x :: xs) ++ 0 :: nil) 0 = x)
      by (apply current_head_after_prefix; exact H6).
    rewrite Hcur in H0.
    rewrite Hcur in H1.
    assert (Hrep :
      replace_Znth i new_c_pre
        ((string_replace_char_spec l1_2 old_c_pre new_c_pre ++ x :: xs) ++ 0 :: nil) =
      (string_replace_char_spec (l1_2 ++ x :: nil) old_c_pre new_c_pre ++ xs) ++ 0 :: nil).
    {
      apply replace_old_head_after_prefix; auto.
    }
    rewrite Hrep.
    Exists (l1_2 ++ cons x nil) xs.
    entailer!;
      try (rewrite H4; rewrite <- app_assoc; reflexivity);
      try (rewrite Zlength_app_cons; lia);
      try (rewrite Zlength_cons in H7; pose proof (Zlength_nonneg xs); lia).
Qed.

Lemma proof_of_string_replace_char_entail_wit_2_2 : string_replace_char_entail_wit_2_2.
Proof.
  pre_process.
  destruct l2_2 eqn:Hl2.
  - rewrite Zlength_nil in H6.
    rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by (rewrite string_replace_char_spec_zlength; lia).
    rewrite string_replace_char_spec_zlength in H0.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0. contradiction H0. reflexivity.
  - rename z into x. rename l0 into xs.
    assert (Hcur :
      Znth i ((string_replace_char_spec l1_2 old_c_pre new_c_pre ++ x :: xs) ++ 0 :: nil) 0 = x)
      by (apply current_head_after_prefix; exact H5).
    rewrite Hcur in H.
    rewrite Hcur in H0.
    Exists (l1_2 ++ cons x nil) xs.
    replace ((string_replace_char_spec (l1_2 ++ x :: nil) old_c_pre new_c_pre ++ xs) ++ 0 :: nil)
      with ((string_replace_char_spec l1_2 old_c_pre new_c_pre ++ x :: xs) ++ 0 :: nil).
    + entailer!;
        try (rewrite H3; rewrite <- app_assoc; reflexivity);
        try (rewrite Zlength_app_cons; lia);
        try (rewrite Zlength_cons in H6; pose proof (Zlength_nonneg xs); lia).
    + symmetry.
      apply preserve_nonold_head_after_prefix.
      exact H.
Qed.

Lemma proof_of_string_replace_char_return_wit_1 : string_replace_char_return_wit_1.
Proof.
  pre_process.
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - destruct l2 eqn:Hl2.
      + rewrite Zlength_nil in H5. lia.
      + rename z into x. rename l0 into xs.
        assert (Hcur :
          Znth i ((string_replace_char_spec l1 old_c_pre new_c_pre ++ x :: xs) ++ 0 :: nil) 0 = x)
          by (apply current_head_after_prefix; exact H4).
        rewrite Hcur in H.
        assert (Horig : Znth i l 0 = x).
        {
          rewrite H2.
          rewrite app_Znth2 by lia.
          replace (i - Zlength l1) with 0 by lia.
          simpl; reflexivity.
        }
        specialize (H10 i).
        rewrite Horig in H10.
        contradiction H10; lia.
    - lia.
  }
  subst i.
  destruct l2 eqn:Hl2.
  - rewrite app_nil_r in H2.
    subst l.
    rewrite app_nil_r.
    entailer!.
  - rewrite Zlength_cons in H5.
    pose proof (Zlength_nonneg l0).
    lia.
Qed.
