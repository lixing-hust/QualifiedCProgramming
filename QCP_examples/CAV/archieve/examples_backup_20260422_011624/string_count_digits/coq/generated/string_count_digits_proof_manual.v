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
From SimpleC.EE.CAV.verify_20260420_185755_string_count_digits Require Import string_count_digits_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import string_count_digits.
Local Open Scope sac.

Lemma string_count_digits_spec_range :
  forall (l : list Z),
    0 <= string_count_digits_spec l <= Zlength l.
Proof.
  induction l.
  - simpl. rewrite Zlength_nil. lia.
  - simpl.
    destruct (Z_le_dec 48 a);
      destruct (Z_le_dec a 57);
      rewrite Zlength_cons; lia.
Qed.

Lemma string_count_digits_spec_app_single :
  forall (l : list Z) (x : Z),
    string_count_digits_spec (l ++ x :: nil) =
    string_count_digits_spec l +
    (if Z_le_dec 48 x then if Z_le_dec x 57 then 1 else 0 else 0).
Proof.
  induction l; intros x.
  - simpl.
    destruct (Z_le_dec 48 x); destruct (Z_le_dec x 57); lia.
  - simpl.
    destruct (Z_le_dec 48 a);
      destruct (Z_le_dec a 57);
      rewrite IHl; lia.
Qed.

Lemma proof_of_string_count_digits_safety_wit_7 : string_count_digits_safety_wit_7.
Proof.
  unfold string_count_digits_safety_wit_7.
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
  subst cnt.
  pose proof (string_count_digits_spec_range l1) as Hrange.
  match goal with
  | Hprefix_len : Zlength l1 = i |- _ =>
      rewrite Hprefix_len in Hrange
  end.
  entailer!.
Qed. 

Lemma proof_of_string_count_digits_entail_wit_1 : string_count_digits_entail_wit_1.
Proof.
  unfold string_count_digits_entail_wit_1.
  intros.
  Exists nil.
  Exists l.
  entailer!.
Qed. 

Lemma proof_of_string_count_digits_entail_wit_2_1 : string_count_digits_entail_wit_2_1.
Proof.
  unfold string_count_digits_entail_wit_2_1.
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
      rewrite app_Znth2 in H1 by lia.
      match type of H1 with
      | Znth ?d (0 :: nil) 0 <> 0 =>
          replace d with 0 in H1 by lia
      end.
      simpl in H1.
      contradiction H1.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H1.
    rewrite app_Znth2 in H1 by lia.
    replace (i - Zlength l1_2) with 0 in H1 by lia.
    simpl in H1.
    contradiction H1.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_ge : 48 <= x).
    {
      rewrite <- app_assoc in H0.
      rewrite app_Znth2 in H0 by lia.
      replace (i - Zlength l1_2) with 0 in H0 by lia.
      change (Znth 0 ((x :: xs) ++ 0 :: nil) 0) with x in H0.
      lia.
    }
    assert (Hx_le : x <= 57).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      change (Znth 0 ((x :: xs) ++ 0 :: nil) 0) with x in H.
      lia.
    }
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
    + rewrite string_count_digits_spec_app_single.
      destruct (Z_le_dec 48 x) as [_ | Hbad_low].
      * destruct (Z_le_dec x 57) as [_ | Hbad_high]; lia.
      * lia.
    + rewrite Zlength_app_cons.
      lia.
    + rewrite <- app_assoc.
      reflexivity.
Qed. 

Lemma proof_of_string_count_digits_entail_wit_2_2 : string_count_digits_entail_wit_2_2.
Proof.
  unfold string_count_digits_entail_wit_2_2.
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
      rewrite app_Znth2 in H0 by lia.
      match type of H0 with
      | Znth ?d (0 :: nil) 0 <> 0 =>
          replace d with 0 in H0 by lia
      end.
      simpl in H0.
      contradiction H0.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H0.
    rewrite app_Znth2 in H0 by lia.
    replace (i - Zlength l1_2) with 0 in H0 by lia.
    simpl in H0.
    contradiction H0.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_lt : x < 48).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      change (Znth 0 ((x :: xs) ++ 0 :: nil) 0) with x in H.
      lia.
    }
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
    + rewrite string_count_digits_spec_app_single.
      destruct (Z_le_dec 48 x); lia.
    + rewrite Zlength_app_cons.
      lia.
    + rewrite <- app_assoc.
      reflexivity.
Qed. 

Lemma proof_of_string_count_digits_entail_wit_2_3 : string_count_digits_entail_wit_2_3.
Proof.
  unfold string_count_digits_entail_wit_2_3.
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
      rewrite app_Znth2 in H1 by lia.
      match type of H1 with
      | Znth ?d (0 :: nil) 0 <> 0 =>
          replace d with 0 in H1 by lia
      end.
      simpl in H1.
      contradiction H1.
      reflexivity.
  }
  subst l.
  destruct l2_2.
  - rewrite app_nil_r in H1.
    rewrite app_Znth2 in H1 by lia.
    replace (i - Zlength l1_2) with 0 in H1 by lia.
    simpl in H1.
    contradiction H1.
    reflexivity.
  - rename z into x.
    rename l2_2 into xs.
    assert (Hx_gt : x > 57).
    {
      rewrite <- app_assoc in H.
      rewrite app_Znth2 in H by lia.
      replace (i - Zlength l1_2) with 0 in H by lia.
      change (Znth 0 ((x :: xs) ++ 0 :: nil) 0) with x in H.
      lia.
    }
    Exists (l1_2 ++ x :: nil).
    Exists xs.
    entailer!.
    + rewrite string_count_digits_spec_app_single.
      destruct (Z_le_dec 48 x).
      * destruct (Z_le_dec x 57); lia.
      * lia.
    + rewrite Zlength_app_cons.
      lia.
    + rewrite <- app_assoc.
      reflexivity.
Qed. 

Lemma proof_of_string_count_digits_entail_wit_3 : string_count_digits_entail_wit_3.
Proof.
  unfold string_count_digits_entail_wit_3.
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
  assert (Hi_eq_n : i = n).
  {
    destruct (Z_lt_ge_dec i n) as [Hlt | Hge].
    - assert (Znth i l 0 <> 0).
      {
        match goal with
        | Hnz : forall k : Z, _ -> Znth k l 0 <> 0 |- _ =>
            apply Hnz; lia
        end.
      }
      rewrite app_Znth1 in H by lia.
      contradiction.
    - lia.
  }
  rewrite Hi_eq_n in *.
  entailer!.
  subst l.
  destruct l2.
  - try rewrite app_nil_r.
    assumption.
  - rename z into x.
    rename l2 into xs.
    exfalso.
    rewrite Zlength_app, Zlength_cons in Hlen_l.
    pose proof Zlength_nonneg xs.
    lia.
Qed. 
