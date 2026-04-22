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
From SimpleC.EE.CAV.verify_20260420_183012_string_starts_with_char Require Import string_starts_with_char_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_string_starts_with_char_return_wit_1 : string_starts_with_char_return_wit_1.
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
  destruct l.
  - assert (n = 0).
    {
      rewrite Zlength_nil in Hlen_l.
      lia.
    }
    right.
    entailer!.
    simpl.
    repeat split; auto; lia.
  - exfalso.
    assert (0 < n).
    {
      rewrite Zlength_cons in Hlen_l.
      pose proof Zlength_nonneg l.
      lia.
    }
    assert (z <> 0).
    {
      match goal with
      | Hnz : forall k : Z, 0 <= k /\ k < n -> Znth k (z :: l) 0 <> 0 |- _ =>
          specialize (Hnz 0); apply Hnz; lia
      end.
    }
    simpl in H.
    contradiction.
Qed. 

Lemma proof_of_string_starts_with_char_return_wit_2 : string_starts_with_char_return_wit_2.
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
  destruct l.
  - exfalso.
    simpl in H0.
    contradiction.
  - assert (0 < n).
    {
      rewrite Zlength_cons in Hlen_l.
      pose proof Zlength_nonneg l.
      lia.
    }
    simpl in H.
    subst c_pre.
    left; right.
    entailer!.
    repeat split; auto; lia.
Qed. 

Lemma proof_of_string_starts_with_char_return_wit_3 : string_starts_with_char_return_wit_3.
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
  destruct l.
  - exfalso.
    simpl in H0.
    contradiction.
  - assert (0 < n).
    {
      rewrite Zlength_cons in Hlen_l.
      pose proof Zlength_nonneg l.
      lia.
    }
    simpl in H.
    left; left.
    entailer!.
    repeat split; auto; lia.
Qed. 
