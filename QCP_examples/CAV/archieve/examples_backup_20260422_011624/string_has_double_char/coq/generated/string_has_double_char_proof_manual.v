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
From SimpleC.EE.CAV.verify_20260420_161439_string_has_double_char Require Import string_has_double_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_has_double_char_entail_wit_2 : string_has_double_char_entail_wit_2.
Proof.
  unfold string_has_double_char_entail_wit_2.
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
  assert (Hi_lt_n : i < n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i = n) by lia.
      subst i.
      rewrite app_Znth2 in H by lia.
      replace (n - Zlength l) with 0 in H by lia.
      simpl in H.
      contradiction.
  }
  entailer!.
Qed.

Lemma proof_of_string_has_double_char_entail_wit_3 : string_has_double_char_entail_wit_3.
Proof.
  unfold string_has_double_char_entail_wit_3.
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
  assert (Hi1_lt_n : i + 1 < n).
  {
    destruct (Z_lt_ge_dec (i + 1) n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i + 1 = n) by lia.
      match goal with
      | Hnz : Znth (i + 1) (l ++ 0 :: nil) 0 <> 0 |- _ =>
          rewrite app_Znth2 in Hnz by lia;
          replace (i + 1 - Zlength l) with 0 in Hnz by lia;
          simpl in Hnz;
          contradiction
      end.
  }
  entailer!.
  intros j [[Hj0 Hjnext] Hjlt].
  destruct (Z_lt_ge_dec j i) as [Hj_lt_i | Hj_ge_i].
  - match goal with
    | Hprefix : forall j0 : Z, (0 <= j0 /\ j0 + 1 < n) /\ j0 < i -> _ |- _ =>
        apply Hprefix
    end;
    lia.
  - assert (j = i) by lia.
    subst j.
    rewrite app_Znth1 in H by lia.
    rewrite app_Znth1 in H by lia.
    exact H.
Qed.

Lemma proof_of_string_has_double_char_return_wit_1 : string_has_double_char_return_wit_1.
Proof.
  unfold string_has_double_char_return_wit_1.
  intros.
  Intros.
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
  assert (Hi1_lt_n : i_3 + 1 < n).
  {
    destruct (Z_lt_ge_dec (i_3 + 1) n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i_3 + 1 = n) by lia.
      rewrite app_Znth2 in H0 by lia.
      replace (i_3 + 1 - Zlength l) with 0 in H0 by lia.
      simpl in H0.
      contradiction.
  }
  rewrite app_Znth1 in H by lia.
  rewrite app_Znth1 in H by lia.
  right.
  exists i_3.
  unfold andp, coq_prop; simpl.
  repeat split; auto; try lia.
Qed.

Lemma proof_of_string_has_double_char_return_wit_2 : string_has_double_char_return_wit_2.
Proof.
  unfold string_has_double_char_return_wit_2.
  intros.
  Intros.
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
  assert (Hi1_eq_n : i_3 + 1 = n).
  {
    destruct (Z_lt_ge_dec (i_3 + 1) n) as [Hlt | Hge].
    - assert (Znth (i_3 + 1) l 0 <> 0).
      {
        match goal with
        | Hnz : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz
        end;
        lia.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  left.
  unfold andp, coq_prop; simpl.
  repeat split; auto; try lia.
  intros i [? ?].
  match goal with
  | Hprefix : forall j : Z, (0 <= j /\ j + 1 < n) /\ j < i_3 -> _ |- _ =>
      apply Hprefix
  end;
  lia.
Qed.

Lemma proof_of_string_has_double_char_return_wit_3 : string_has_double_char_return_wit_3.
Proof.
  unfold string_has_double_char_return_wit_3.
  intros.
  Intros.
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
  assert (Hi_eq_n : i_3 = n).
  {
    destruct (Z_lt_ge_dec i_3 n) as [Hlt | Hge].
    - assert (Znth i_3 l 0 <> 0).
      {
        match goal with
        | Hnz : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
            apply Hnz
        end;
        lia.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  left.
  unfold andp, coq_prop; simpl.
  repeat split; auto; try lia.
  intros i [? ?].
  match goal with
  | Hprefix : forall j : Z, (0 <= j /\ j + 1 < n) /\ j < i_3 -> _ |- _ =>
      apply Hprefix
  end;
  lia.
Qed.
