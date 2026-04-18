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
From SimpleC.EE.CAV.verify_20260418_170027_array_contains Require Import array_contains_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_contains.
Local Open Scope sac.

Lemma array_contains_spec_hit :
  forall (l : list Z) (k i : Z),
    0 <= i ->
    i < Zlength l ->
    Znth i l 0 = k ->
    (forall (j : Z), 0 <= j -> j < i -> Znth j l 0 <> k) ->
    array_contains_spec l k = 1.
Proof.
  induction l; intros k i Hi0 Hilen Hhit Hprev.
  - rewrite Zlength_nil in Hilen. lia.
  - destruct (Z.eq_dec a k) as [Heq | Hneq].
    + simpl. destruct (Z.eq_dec a k); lia.
    + simpl. destruct (Z.eq_dec a k); try contradiction.
      assert (Hi_pos : 0 < i).
      {
        assert (i <> 0).
        {
          intro Hi_eq.
          subst i.
          rewrite Znth0_cons in Hhit.
          contradiction.
        }
        lia.
      }
      apply IHl with (i := i - 1).
      * lia.
      * rewrite Zlength_cons in Hilen.
        pose proof Zlength_nonneg l.
        lia.
      * rewrite Znth_cons in Hhit by lia.
        exact Hhit.
      * intros j Hj0 Hjlt.
        specialize (Hprev (j + 1)).
        assert (Hj1_nonneg : 0 <= j + 1) by lia.
        assert (Hj1_lt : j + 1 < i) by lia.
        specialize (Hprev Hj1_nonneg Hj1_lt).
        rewrite Znth_cons in Hprev by lia.
        replace (j + 1 - 1) with j in Hprev by lia.
        exact Hprev.
Qed.

Lemma array_contains_spec_miss :
  forall (l : list Z) (k : Z),
    (forall (j : Z), 0 <= j -> j < Zlength l -> Znth j l 0 <> k) ->
    array_contains_spec l k = 0.
Proof.
  induction l; intros k Hmiss.
  - reflexivity.
  - simpl.
    destruct (Z.eq_dec a k) as [Heq | Hneq].
    + exfalso.
      specialize (Hmiss 0).
      assert (0 < Zlength (a :: l)).
      {
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l.
        lia.
      }
      specialize (Hmiss (Z.le_refl 0) H).
      rewrite Znth0_cons in Hmiss.
      contradiction.
    + apply IHl.
      intros j Hj0 Hjlt.
      specialize (Hmiss (j + 1)).
      assert (0 <= j + 1) by lia.
      assert (j + 1 < Zlength (a :: l)).
      {
        rewrite Zlength_cons.
        pose proof Zlength_nonneg l.
        lia.
      }
      specialize (Hmiss H H0).
      rewrite Znth_cons in Hmiss by lia.
      replace (j + 1 - 1) with j in Hmiss by lia.
      exact Hmiss.
Qed.

Lemma proof_of_array_contains_return_wit_1 : array_contains_return_wit_1.
Proof.
  unfold array_contains_return_wit_1.
  intros.
  entailer!.
  symmetry.
  eapply (array_contains_spec_hit l k_pre i).
  - lia.
  - lia.
  - exact H.
  - intros j Hj0 Hjlt.
    apply H3; lia.
Qed.

Lemma proof_of_array_contains_return_wit_2 : array_contains_return_wit_2.
Proof.
  unfold array_contains_return_wit_2.
  pre_process.
  prop_apply IntArray.full_length. Intros.
  assert (Hlen : Zlength l = n_pre).
  {
    rewrite Zlength_correct.
    exact H1.
  }
  entailer!.
  symmetry.
  eapply (array_contains_spec_miss l k_pre).
  intros j Hj0 Hjlt.
  apply H0.
  rewrite Hlen in Hjlt.
  lia.
Qed.
