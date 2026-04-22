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
From SimpleC.EE.CAV.verify_20260418_200830_string_all_lowercase Require Import string_all_lowercase_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_all_lowercase.
Local Open Scope sac.

Lemma string_all_lowercase_spec_all :
  forall (l : list Z),
    (forall k, 0 <= k < Zlength l -> 97 <= Znth k l 0 /\ Znth k l 0 <= 122) ->
    string_all_lowercase_spec l = 1.
Proof.
  induction l.
  - intros Hall. reflexivity.
  - intros Hall. simpl.
    assert (Hhead : 97 <= a /\ a <= 122).
    {
      specialize (Hall 0).
      rewrite Znth0_cons in Hall.
      apply Hall.
      assert (0 <= 0 < Zlength (a :: l)).
      {
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l.
        lia.
      }
      assumption.
    }
    destruct Hhead as [Hge Hle].
    destruct (Z_lt_dec a 97) as [Hlt | Hnlt].
    { lia. }
    destruct (Z_gt_dec a 122) as [Hgt | Hngt].
    { lia. }
    apply IHl.
    intros k Hk.
    specialize (Hall (k + 1)).
    rewrite Znth_cons in Hall by lia.
    replace (k + 1 - 1) with k in Hall by lia.
    apply Hall.
    assert (0 <= k + 1 < Zlength (a :: l)).
    {
      rewrite Zlength_cons.
      pose proof Zlength_nonneg l.
      lia.
    }
    assumption.
Qed.

Lemma string_all_lowercase_spec_bad_at :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    (forall k, 0 <= k < i -> 97 <= Znth k l 0 /\ Znth k l 0 <= 122) ->
    (Znth i l 0 < 97 \/ Znth i l 0 > 122) ->
    string_all_lowercase_spec l = 0.
Proof.
  induction l.
  - intros i Hi Hall Hbad. rewrite Zlength_nil in Hi. lia.
  - intros i Hi Hall Hbad. rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [Heq | Hneq].
    + subst i.
      rewrite Znth0_cons in Hbad.
      simpl.
      destruct Hbad as [Hlt | Hgt].
      * destruct (Z_lt_dec a 97) as [Hcase | Hcase].
        -- reflexivity.
        -- lia.
      * destruct (Z_lt_dec a 97) as [Hcase | Hcase].
        -- lia.
        -- destruct (Z_gt_dec a 122) as [Hcase2 | Hcase2].
           ++ reflexivity.
           ++ lia.
    + assert (Hi_pos : i > 0) by lia.
      assert (Hhead : 97 <= a /\ a <= 122).
      {
        specialize (Hall 0).
        rewrite Znth0_cons in Hall.
        apply Hall.
        assert (0 <= 0 < i).
        {
          pose proof Zlength_nonneg l.
          lia.
        }
        assumption.
      }
      destruct Hhead as [Hge Hle].
      simpl.
      destruct (Z_lt_dec a 97) as [Hlt | Hnlt].
      * lia.
      * destruct (Z_gt_dec a 122) as [Hgt | Hngt].
        -- lia.
        -- apply IHl with (i := i - 1).
           ++ lia.
           ++ intros k Hk.
              specialize (Hall (k + 1)).
              rewrite Znth_cons in Hall by lia.
              replace (k + 1 - 1) with k in Hall by lia.
              apply Hall.
              assert (0 <= k + 1 < i).
              {
                pose proof Zlength_nonneg l.
                lia.
              }
              assumption.
           ++ rewrite Znth_cons in Hbad by lia.
              replace (i - 1 + 1 - 1) with (i - 1) in Hbad by lia.
              exact Hbad.
Qed.

Lemma proof_of_string_all_lowercase_entail_wit_2 : string_all_lowercase_entail_wit_2.
Proof.
  unfold string_all_lowercase_entail_wit_2.
  pre_process.
  prop_apply CharArray.full_length. Intros.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  entailer!.
  intros k Hk.
  destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
  - match goal with
    | Hall : forall k_2 : Z, 0 <= k_2 < i -> 97 <= Znth k_2 l 0 <= 122 |- _ =>
        apply Hall; lia
    end.
  - assert (k = i) by lia.
    subst k.
    assert (Hi_lt_n : i < n).
    {
      destruct (Z_lt_ge_dec i n) as [Hlt_i | Hge_i].
      - exact Hlt_i.
      - assert (i = n) by lia.
        subst i.
        match goal with
        | Hneq : Znth n (l ++ 0 :: nil) 0 <> 0 |- _ =>
            rewrite app_Znth2 in Hneq by lia;
            replace (n - Zlength l) with 0 in Hneq by lia;
            cbn in Hneq;
            contradiction
        end.
    }
    assert (Hcur_le : Znth i (l ++ 0 :: nil) 0 <= 122).
    {
      match goal with
      | Hle : Znth i (l ++ 0 :: nil) 0 <= 122 |- _ => exact Hle
      end.
    }
    assert (Hcur_ge : 97 <= Znth i (l ++ 0 :: nil) 0).
    {
      match goal with
      | Hge0 : 97 <= Znth i (l ++ 0 :: nil) 0 |- _ => exact Hge0
      end.
    }
    rewrite app_Znth1 in Hcur_le by lia.
    rewrite app_Znth1 in Hcur_ge by lia.
    split; lia.
Qed.

Lemma proof_of_string_all_lowercase_entail_wit_3 : string_all_lowercase_entail_wit_3.
Proof.
  unfold string_all_lowercase_entail_wit_3.
  pre_process.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - specialize (H5 i).
      assert (Znth i l 0 <> 0) by (apply H5; lia).
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  subst i.
  entailer!.
Qed.

Lemma proof_of_string_all_lowercase_return_wit_1 : string_all_lowercase_return_wit_1.
Proof.
  unfold string_all_lowercase_return_wit_1.
  pre_process.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      rewrite app_Znth2 in H by lia.
      replace (n - Zlength l) with 0 in H by lia.
      cbn in H.
      lia.
  }
  entailer!.
  apply string_all_lowercase_spec_bad_at with (i := i).
  - lia.
  - exact H4.
  - rewrite app_Znth1 in H by lia.
    right.
    exact H.
Qed.

Lemma proof_of_string_all_lowercase_return_wit_2 : string_all_lowercase_return_wit_2.
Proof.
  unfold string_all_lowercase_return_wit_2.
  pre_process.
  assert (Hlen_l : Zlength l = n).
  {
    match goal with
    | Hlen : Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1 |- _ =>
        rewrite <- Zlength_correct in Hlen;
        rewrite Zlength_app_cons in Hlen;
        lia
    end.
  }
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      rewrite app_Znth2 in H0 by lia.
      replace (n - Zlength l) with 0 in H0 by lia.
      cbn in H0.
      lia.
  }
  entailer!.
  apply string_all_lowercase_spec_bad_at with (i := i).
  - lia.
  - exact H3.
  - rewrite app_Znth1 in H0 by lia.
    left.
    exact H0.
Qed.

Lemma proof_of_string_all_lowercase_return_wit_3 : string_all_lowercase_return_wit_3.
Proof.
  unfold string_all_lowercase_return_wit_3.
  intros.
  entailer!.
  apply string_all_lowercase_spec_all.
  exact H.
Qed.
