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
From SimpleC.EE.CAV.verify_20260418_020228_array_sum Require Import array_sum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma sublist_full_Zlength : forall {A} (l : list A),
  sublist 0 (Zlength l) l = l.
Proof.
  intros.
  apply sublist_self.
  reflexivity.
Qed.

Lemma sum_abs_bound :
  forall (l : list Z) b,
    0 <= b ->
    (forall i, 0 <= i < Zlength l -> - b <= Znth i l 0 <= b) ->
    - Zlength l * b <= sum l <= Zlength l * b.
Proof.
  induction l; intros b Hb Hall.
  - rewrite Zlength_nil. simpl. lia.
  - assert (Hx : - b <= a <= b).
    {
      specialize (Hall 0).
      assert (0 <= 0 < Zlength (a :: l)).
      { rewrite Zlength_cons. pose proof Zlength_nonneg l. lia. }
      specialize (Hall H).
      simpl in Hall.
      exact Hall.
    }
    assert (Hxs : forall i, 0 <= i < Zlength l -> - b <= Znth i l 0 <= b).
    {
      intros i Hi.
      specialize (Hall (i + 1)).
      assert (Hi_succ : 0 <= i + 1 < Zlength (a :: l)).
      { rewrite Zlength_cons. pose proof Zlength_nonneg l. lia. }
      specialize (Hall Hi_succ).
      rewrite Znth_cons in Hall by lia.
      replace (i + 1 - 1) with i in Hall by lia.
      apply Hall.
    }
    specialize (IHl b Hb Hxs).
    simpl.
    rewrite Zlength_cons.
    lia.
Qed.

Lemma proof_of_array_sum_safety_wit_3 : array_sum_safety_wit_3.
Proof.
  unfold array_sum_safety_wit_3.
  intros.
  entailer!.
  - rewrite H2.
    assert (Hprefix :
      - Zlength (sublist 0 i l) * 10000 <= sum (sublist 0 i l) <= Zlength (sublist 0 i l) * 10000).
    {
      apply sum_abs_bound.
      - lia.
      - intros k Hk.
        rewrite Zlength_sublist in Hk by lia.
        replace (i - 0) with i in Hk by lia.
        rewrite Znth_sublist0 by exact Hk.
        apply H6.
        lia.
    }
    assert (Hi_bound : -10000 <= Znth i l 0 <= 10000).
    { apply H6; lia. }
    rewrite Zlength_sublist in Hprefix by lia.
    replace (i - 0) with i in Hprefix by lia.
    destruct Hprefix as [Hprefix_lo Hprefix_hi].
    destruct Hi_bound as [Hi_lo Hi_hi].
    assert (Hnext_lo :
      - (i + 1) * 10000 <= sum (sublist 0 i l) + Znth i l 0) by lia.
    eapply Z.le_trans.
    2: exact Hnext_lo.
    lia.
  - rewrite H2.
    assert (Hprefix :
      - Zlength (sublist 0 i l) * 10000 <= sum (sublist 0 i l) <= Zlength (sublist 0 i l) * 10000).
    {
      apply sum_abs_bound.
      - lia.
      - intros k Hk.
        rewrite Zlength_sublist in Hk by lia.
        replace (i - 0) with i in Hk by lia.
        rewrite Znth_sublist0 by exact Hk.
        apply H6.
        lia.
    }
    assert (Hi_bound : -10000 <= Znth i l 0 <= 10000).
    { apply H6; lia. }
    rewrite Zlength_sublist in Hprefix by lia.
    replace (i - 0) with i in Hprefix by lia.
    destruct Hprefix as [Hprefix_lo Hprefix_hi].
    destruct Hi_bound as [Hi_lo Hi_hi].
    assert (Hnext_hi :
      sum (sublist 0 i l) + Znth i l 0 <= (i + 1) * 10000) by lia.
    eapply Z.le_trans.
    1: exact Hnext_hi.
    lia.
Qed.

Lemma proof_of_array_sum_entail_wit_1 : array_sum_entail_wit_1.
Proof.
  unfold array_sum_entail_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_array_sum_entail_wit_2 : array_sum_entail_wit_2.
Proof.
  unfold array_sum_entail_wit_2.
  intros.
  entailer!.
  subst ret.
  rewrite (sublist_split 0 (i_2 + 1) i_2 l) by (pose proof Zlength_correct l; lia).
  rewrite sum_app.
  rewrite (sublist_single i_2 l 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  lia.
Qed.

Lemma proof_of_array_sum_entail_wit_3 : array_sum_entail_wit_3.
Proof.
  unfold array_sum_entail_wit_3.
  intros.
  entailer!.
  assert (i = n_pre) by lia.
  subst i.
  rewrite H2.
  rewrite <- H5.
  f_equal.
  apply sublist_self.
  reflexivity.
Qed.
