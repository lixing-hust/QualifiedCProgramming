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
From SimpleC.EE.CAV.verify_20260418_202647_string_to_upper_ascii Require Import string_to_upper_ascii_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_to_upper_ascii.
Local Open Scope sac.

Lemma string_to_upper_ascii_spec_length :
  forall (l : list Z),
    Zlength (string_to_upper_ascii_spec l) = Zlength l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite !Zlength_cons, IHl. reflexivity.
Qed.

Lemma string_to_upper_ascii_spec_app :
  forall (l1 l2 : list Z),
    string_to_upper_ascii_spec (l1 ++ l2) =
    string_to_upper_ascii_spec l1 ++ string_to_upper_ascii_spec l2.
Proof.
  induction l1.
  - reflexivity.
  - intros l2. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma replace_nth_length :
  forall {A : Type} (n : nat) (a : A) (l : list A),
    Datatypes.length (replace_nth n a l) = Datatypes.length l.
Proof.
  intros A n a l.
  revert n.
  induction l.
  - intros n. destruct n; reflexivity.
  - intros n. destruct n.
    + reflexivity.
    + simpl. rewrite IHl. reflexivity.
Qed.

Lemma replace_Znth_length :
  forall {A : Type} (n : Z) (a : A) (l : list A),
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros A n a l.
  unfold replace_Znth.
  rewrite Zlength_correct.
  rewrite Zlength_correct.
  rewrite replace_nth_length.
  reflexivity.
Qed.

Lemma upper_ascii_char_in_range :
  forall x,
    97 <= x <= 122 ->
    upper_ascii_char x = x - 97 + 65.
Proof.
  intros x Hrange.
  unfold upper_ascii_char.
  destruct (Z_le_dec 97 x) as [Hge | Hge].
  - destruct (Z_le_dec x 122) as [Hle | Hle].
    + reflexivity.
    + lia.
  - lia.
Qed.

Lemma upper_ascii_char_below :
  forall x,
    x < 97 ->
    upper_ascii_char x = x.
Proof.
  intros x Hlt.
  unfold upper_ascii_char.
  destruct (Z_le_dec 97 x) as [Hge | Hge].
  - lia.
  - reflexivity.
Qed.

Lemma upper_ascii_char_above :
  forall x,
    x > 122 ->
    upper_ascii_char x = x.
Proof.
  intros x Hgt.
  unfold upper_ascii_char.
  destruct (Z_le_dec 97 x) as [Hge | Hge].
  - destruct (Z_le_dec x 122) as [Hle | Hle].
    + lia.
    + reflexivity.
  - lia.
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_1 : string_to_upper_ascii_entail_wit_1.
Proof.
  unfold string_to_upper_ascii_entail_wit_1.
  pre_process.
  Exists (@nil Z).
  Exists l.
  entailer!.
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_2_1 : string_to_upper_ascii_entail_wit_2_1.
Proof.
  unfold string_to_upper_ascii_entail_wit_2_1.
  pre_process.
  destruct l2_2.
  - simpl in H2.
    rewrite app_Znth2 in H2 by (rewrite string_to_upper_ascii_spec_length; lia).
    replace (i - Zlength (string_to_upper_ascii_spec l1_2)) with 0 in H2 by
      (rewrite string_to_upper_ascii_spec_length; lia).
    simpl in H2.
    contradiction.
  - prop_apply CharArray.full_length. Intros.
    assert (Hlen_l : Zlength l = n).
    {
      rewrite <- Zlength_correct in H10.
      rewrite replace_Znth_length in H10.
      repeat rewrite Zlength_app in H10.
      rewrite string_to_upper_ascii_spec_length in H10.
      rewrite H5.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      rewrite H6 in H10.
      rewrite H6.
      rewrite Zlength_cons in H10.
      simpl in H10.
      lia.
    }
    assert (Hi_lt_n : i < n).
    {
      rewrite H5.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      rewrite <- Hlen_l.
      rewrite H6.
      lia.
    }
    Exists (l1_2 ++ z :: nil).
    Exists l2_2.
    entailer!.
    + rewrite app_assoc. reflexivity.
    + rewrite Zlength_app_cons. lia.
    + rewrite string_to_upper_ascii_spec_app.
      simpl.
      rewrite replace_Znth_app_r by lia.
      rewrite replace_Znth_nothing by (rewrite string_to_upper_ascii_spec_length; lia).
      replace (i - Zlength (string_to_upper_ascii_spec l1_2)) with 0 by
        (rewrite string_to_upper_ascii_spec_length; lia).
      simpl.
      rewrite upper_ascii_char_in_range by lia.
      reflexivity.
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_2_2 : string_to_upper_ascii_entail_wit_2_2.
Proof.
  unfold string_to_upper_ascii_entail_wit_2_2.
  pre_process.
  destruct l2_2.
  - simpl in H1.
    rewrite app_Znth2 in H1 by (rewrite string_to_upper_ascii_spec_length; lia).
    replace (i - Zlength (string_to_upper_ascii_spec l1_2)) with 0 in H1 by
      (rewrite string_to_upper_ascii_spec_length; lia).
    simpl in H1.
    contradiction.
  - prop_apply CharArray.full_length. Intros.
    assert (Hlen_l : Zlength l = n).
    {
      rewrite <- Zlength_correct in H10.
      repeat rewrite Zlength_app in H10.
      rewrite string_to_upper_ascii_spec_length in H10.
      rewrite H5.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      rewrite H6 in H10.
      rewrite H6.
      rewrite Zlength_cons in H10.
      simpl in H10.
      lia.
    }
    assert (Hi_lt_n : i < n).
    {
      rewrite H5.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      rewrite <- Hlen_l.
      rewrite H6.
      lia.
    }
    Exists (l1_2 ++ z :: nil).
    Exists l2_2.
    entailer!.
    + rewrite app_assoc. reflexivity.
    + rewrite Zlength_app_cons. lia.
    + rewrite string_to_upper_ascii_spec_app.
      simpl.
      rewrite upper_ascii_char_below by lia.
      reflexivity.
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_2_3 : string_to_upper_ascii_entail_wit_2_3.
Proof.
  unfold string_to_upper_ascii_entail_wit_2_3.
  pre_process.
  destruct l2_2.
  - simpl in H1.
    rewrite app_Znth2 in H1 by (rewrite string_to_upper_ascii_spec_length; lia).
    replace (i - Zlength (string_to_upper_ascii_spec l1_2)) with 0 in H1 by
      (rewrite string_to_upper_ascii_spec_length; lia).
    simpl in H1.
    contradiction.
  - prop_apply CharArray.full_length. Intros.
    assert (Hlen_l : Zlength l = n).
    {
      rewrite <- Zlength_correct in H10.
      repeat rewrite Zlength_app in H10.
      rewrite string_to_upper_ascii_spec_length in H10.
      rewrite H5.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      rewrite H6 in H10.
      rewrite H6.
      rewrite Zlength_cons in H10.
      simpl in H10.
      lia.
    }
    assert (Hi_lt_n : i < n).
    {
      rewrite H5.
      rewrite Zlength_app.
      rewrite Zlength_cons.
      rewrite <- Hlen_l.
      rewrite H6.
      lia.
    }
    Exists (l1_2 ++ z :: nil).
    Exists l2_2.
    entailer!.
    + rewrite app_assoc. reflexivity.
    + rewrite Zlength_app_cons. lia.
    + rewrite string_to_upper_ascii_spec_app.
      simpl.
      rewrite upper_ascii_char_above by lia.
      reflexivity.
Qed.

Lemma proof_of_string_to_upper_ascii_entail_wit_3 : string_to_upper_ascii_entail_wit_3.
Proof.
  unfold string_to_upper_ascii_entail_wit_3.
  pre_process.
  prop_apply CharArray.full_length. Intros.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length
        (string_to_upper_ascii_spec l1 ++ l2 ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite string_to_upper_ascii_spec_length in Hlen;
        rewrite Zlength_app_cons in Hlen;
        rewrite H4 in Hlen;
        lia
    end.
  }
  destruct l2.
  - simpl in H.
    assert (l = l1) by (rewrite app_nil_r in H3; exact H3).
    subst l.
    assert (i = n) by (rewrite <- Hlen_l; rewrite H4; lia).
    subst i.
    entailer!.
  - assert (Hi_lt_n : i < n).
    {
      rewrite Hlen_l.
      rewrite H3.
      rewrite Zlength_app_cons.
      lia.
    }
    specialize (H5 i).
    assert (Hx_nonzero : Znth i l 0 <> 0).
    {
      apply H5.
      lia.
    }
    rewrite H3 in Hx_nonzero.
    rewrite app_Znth2 in Hx_nonzero by (rewrite H4; lia).
    replace (i - Zlength l1) with 0 in Hx_nonzero by lia.
    simpl in Hx_nonzero.
    simpl in H.
    contradiction.
Qed.
