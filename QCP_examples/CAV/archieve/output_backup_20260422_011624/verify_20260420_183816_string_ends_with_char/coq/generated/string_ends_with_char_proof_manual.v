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
From SimpleC.EE.CAV.verify_20260420_183816_string_ends_with_char Require Import string_ends_with_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_ends_with_char_entail_wit_1 : string_ends_with_char_entail_wit_1.
Proof.
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
  assert (0 < n).
  {
    destruct (Z_lt_ge_dec 0 n) as [Hlt | Hge].
    - exact Hlt.
    - assert (n = 0) by lia.
      subst n.
      rewrite app_Znth2 in H by lia.
      replace (0 - Zlength l) with 0 in H by lia.
      simpl in H.
      contradiction.
  }
  entailer!.
Qed.

Lemma proof_of_string_ends_with_char_entail_wit_3 : string_ends_with_char_entail_wit_3.
Proof.
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
  assert (i_2 + 1 < n).
  {
    destruct (Z_lt_ge_dec (i_2 + 1) n) as [Hlt | Hge].
    - exact Hlt.
    - assert (i_2 + 1 = n) by lia.
      rewrite app_Znth2 in H by lia.
      replace (i_2 + 1 - Zlength l) with 0 in H by lia.
      simpl in H.
      contradiction.
  }
  entailer!.
Qed.

Lemma proof_of_string_ends_with_char_entail_wit_4 : string_ends_with_char_entail_wit_4.
Proof.
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
  assert (i = n - 1).
  {
    destruct (Z_lt_ge_dec (i + 1) n) as [Hlt | Hge].
    - rewrite app_Znth1 in H by lia.
      match goal with
      | Hforall : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
          assert (Znth (i + 1) l 0 <> 0) by (apply Hforall; lia)
      end.
      contradiction.
    - lia.
  }
  entailer!.
Qed.

Lemma proof_of_string_ends_with_char_return_wit_1 : string_ends_with_char_return_wit_1.
Proof.
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
  assert (n = 0).
  {
    destruct (Z_lt_ge_dec 0 n) as [Hlt | Hge].
    - rewrite app_Znth1 in H by lia.
      match goal with
      | Hforall : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
          assert (Znth 0 l 0 <> 0) by (apply Hforall; lia)
      end.
      contradiction.
    - lia.
  }
  subst n.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_string_ends_with_char_return_wit_3 : string_ends_with_char_return_wit_3.
Proof.
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
  assert (Znth (n - 1) l 0 <> c_pre).
  {
    subst i.
    rewrite app_Znth1 in H by lia.
    exact H.
  }
  rewrite <- derivable1_orp_intros1.
  rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.
