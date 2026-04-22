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
From SimpleC.EE.CAV.verify_20260422_012900_13_array_equal Require Import array_equal_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_equal.
Local Open Scope sac.

Lemma array_equal_spec_mismatch :
  forall (la lb : list Z) (i : Z),
    Zlength la = Zlength lb ->
    0 <= i ->
    i < Zlength la ->
    Znth i la 0 <> Znth i lb 0 ->
    (forall (j : Z), 0 <= j -> j < i -> Znth j la 0 = Znth j lb 0) ->
    array_equal_spec la lb = 0.
Proof.
  induction la; intros lb i Hlen Hi0 Hilt Hneq Hpref.
  - rewrite Zlength_nil in Hilt. lia.
  - destruct lb.
    + rewrite Zlength_nil in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof Zlength_nonneg la.
      lia.
    + rename z into b.
      destruct (Z.eq_dec a b).
      * subst b.
        simpl.
        destruct (Z.eq_dec a a).
        2: contradiction.
        assert (Hi_cases : i = 0 \/ 0 < i) by lia.
        destruct Hi_cases.
        -- subst i.
           rewrite !Znth0_cons in Hneq.
           contradiction.
        -- apply IHla with (i := i - 1).
           ++ rewrite !Zlength_cons in Hlen. lia.
           ++ lia.
           ++ rewrite Zlength_cons in Hilt.
              pose proof Zlength_nonneg la.
              lia.
           ++ rewrite !Znth_cons in Hneq by lia.
              exact Hneq.
           ++ intros j Hj0 Hjlt.
              specialize (Hpref (j + 1)).
              assert (Hj1_nonneg : 0 <= j + 1) by lia.
              assert (Hj1_lt : j + 1 < i) by lia.
              specialize (Hpref Hj1_nonneg Hj1_lt).
              rewrite !Znth_cons in Hpref by lia.
              replace (j + 1 - 1) with j in Hpref by lia.
              exact Hpref.
      * simpl.
        destruct (Z.eq_dec a b).
        -- contradiction.
        -- reflexivity.
Qed.

Lemma array_equal_spec_equal :
  forall (la lb : list Z),
    Zlength la = Zlength lb ->
    (forall (j : Z), 0 <= j -> j < Zlength la -> Znth j la 0 = Znth j lb 0) ->
    array_equal_spec la lb = 1.
Proof.
  induction la; intros lb Hlen Hall.
  - destruct lb.
    + reflexivity.
    + rewrite Zlength_nil in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof Zlength_nonneg lb.
      lia.
  - destruct lb.
    + rewrite Zlength_nil in Hlen.
      rewrite Zlength_cons in Hlen.
      pose proof Zlength_nonneg la.
      lia.
    + rename z into b.
      assert (Hab : a = b).
      {
        specialize (Hall 0).
        assert (Hlt : 0 < Zlength (a :: la)).
        {
          rewrite Zlength_cons.
          pose proof Zlength_nonneg la.
          lia.
        }
        specialize (Hall (Z.le_refl 0) Hlt).
        rewrite !Znth0_cons in Hall.
        exact Hall.
      }
      subst b.
      simpl.
      destruct (Z.eq_dec a a).
      2: contradiction.
      apply IHla.
      * rewrite !Zlength_cons in Hlen. lia.
      * intros j Hj0 Hjlt.
        specialize (Hall (j + 1)).
        assert (Hj1_nonneg : 0 <= j + 1) by lia.
        assert (Hj1_lt : j + 1 < Zlength (a :: la)).
        {
          rewrite Zlength_cons.
          pose proof Zlength_nonneg la.
          lia.
        }
        specialize (Hall Hj1_nonneg Hj1_lt).
        rewrite !Znth_cons in Hall by lia.
        replace (j + 1 - 1) with j in Hall by lia.
        exact Hall.
Qed.

Lemma proof_of_array_equal_return_wit_1 : array_equal_return_wit_1.
Proof.
  unfold array_equal_return_wit_1.
  intros.
  entailer!.
  symmetry.
  eapply array_equal_spec_mismatch.
  - rewrite H5. rewrite H6. reflexivity.
  - exact H1.
  - rewrite H5. exact H0.
  - exact H.
  - intros j Hj0 Hjlt.
    apply H3; lia.
Qed.

Lemma proof_of_array_equal_return_wit_2 : array_equal_return_wit_2.
Proof.
  unfold array_equal_return_wit_2.
  intros. Intros.
  prop_apply (IntArray.full_length a_pre n_pre la). Intros.
  prop_apply (IntArray.full_length b_pre n_pre lb). Intros.
  entailer!.
  symmetry.
  eapply array_equal_spec_equal.
  - assert (Hlen_la : Zlength la = n_pre).
    {
      rewrite Zlength_correct.
      exact H1.
    }
    assert (Hlen_lb : Zlength lb = n_pre).
    {
      rewrite Zlength_correct.
      exact H2.
    }
    rewrite Hlen_la.
    rewrite Hlen_lb.
    reflexivity.
  - intros j Hj0 Hjlt.
    apply H0.
    rewrite Zlength_correct in Hjlt.
    rewrite H1 in Hjlt.
    lia.
Qed.
