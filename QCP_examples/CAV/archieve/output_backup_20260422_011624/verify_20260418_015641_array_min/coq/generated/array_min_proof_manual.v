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
From SimpleC.EE.CAV.verify_20260418_015641_array_min Require Import array_min_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_min.
Local Open Scope sac.

Lemma sublist_full_Zlength : forall {A} (l : list A),
  sublist 0 (Zlength l) l = l.
Proof.
  intros.
  apply sublist_self.
  reflexivity.
Qed.

Lemma min_list_nonempty_lower_bound :
  forall (l : list Z) i d,
    0 <= i < Zlength l ->
    min_list_nonempty l <= Znth i l d.
Proof.
  induction l; intros i d Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct l.
    + simpl.
      assert (i = 0) by (rewrite Zlength_cons, Zlength_nil in Hi; lia).
      subst i. rewrite Znth0_cons. lia.
    + simpl.
      destruct (Z.eq_dec i 0) as [Heq | Hneq].
      * subst i. rewrite Znth0_cons. apply Z.le_min_l.
      * assert (i > 0) by lia.
        rewrite Znth_cons by lia.
        eapply Z.le_trans.
        1: apply Z.le_min_r.
        apply IHl.
        rewrite Zlength_cons in Hi. lia.
Qed.

Lemma min_list_nonempty_bounded :
  forall (l : list Z) bound,
    1 <= Zlength l ->
    (forall i, 0 <= i < Zlength l -> bound <= Znth i l 0) ->
    bound <= min_list_nonempty l.
Proof.
  induction l; intros bound Hnz Hall.
  - rewrite Zlength_nil in Hnz. lia.
  - destruct l.
    + simpl.
      specialize (Hall 0).
      assert (0 <= 0 < Zlength (a :: nil)) by (rewrite Zlength_cons, Zlength_nil; lia).
      specialize (Hall H).
      rewrite Znth0_cons in Hall.
      exact Hall.
    + simpl.
      apply Z.min_glb.
      * specialize (Hall 0).
        assert (0 <= 0 < Zlength (a :: z :: l)) by (simpl; lia).
        specialize (Hall H).
        rewrite Znth0_cons in Hall.
        exact Hall.
      * assert (1 <= Zlength (z :: l)).
        { rewrite Zlength_cons. pose proof Zlength_nonneg l. lia. }
        apply IHl.
        -- exact H.
        -- intros i Hi.
           specialize (Hall (i + 1)).
           assert (0 <= i + 1 < Zlength (a :: z :: l)).
           { rewrite !Zlength_cons in *. lia. }
           specialize (Hall H0).
           rewrite Znth_cons in Hall by lia.
           replace (i + 1 - 1) with i in Hall by lia.
           exact Hall.
Qed.

Lemma min_list_nonempty_extend_le :
  forall (l : list Z) x,
    1 <= Zlength l ->
    min_list_nonempty (l ++ x :: nil) <= min_list_nonempty l.
Proof.
  induction l; intros x Hnz.
  - rewrite Zlength_nil in Hnz. lia.
  - destruct l.
    + simpl. apply Z.le_min_l.
    + simpl.
      apply Z.min_glb.
      * apply Z.le_min_l.
      * eapply Z.le_trans.
        1: apply Z.le_min_r.
        assert (1 <= Zlength (z :: l)).
        { rewrite Zlength_cons. pose proof Zlength_nonneg l. lia. }
        apply IHl.
        exact H.
Qed.

Lemma min_list_nonempty_extend_keep :
  forall (l : list Z) x,
    1 <= Zlength l ->
    min_list_nonempty l <= x ->
    min_list_nonempty (l ++ x :: nil) = min_list_nonempty l.
Proof.
  intros l x Hnz Hx.
  apply Z.le_antisymm.
  - apply min_list_nonempty_extend_le.
    exact Hnz.
  - apply min_list_nonempty_bounded.
    + rewrite Zlength_app_cons. lia.
    + intros i Hi.
      destruct (Z_lt_ge_dec i (Zlength l)).
      * rewrite app_Znth1 by lia.
        apply min_list_nonempty_lower_bound.
        lia.
      * assert (i = Zlength l) by (rewrite Zlength_app_cons in Hi; lia).
        subst i.
        rewrite app_Znth2 by lia.
        rewrite Z.sub_diag.
        rewrite Znth0_cons.
        exact Hx.
Qed.

Lemma proof_of_array_min_entail_wit_2_2 : array_min_entail_wit_2_2.
Proof.
  unfold array_min_entail_wit_2_2.
  intros.
  entailer!.
  subst ret.
  rewrite (sublist_split 0 (i + 1) i l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  symmetry.
  apply min_list_nonempty_extend_keep.
  - rewrite Zlength_sublist by lia. lia.
  - lia.
Qed.

Lemma proof_of_array_min_return_wit_1 : array_min_return_wit_1.
Proof.
  unfold array_min_return_wit_1.
  intros.
  entailer!.
  subst ret.
  assert (i = n_pre) by lia.
  subst i.
  replace n_pre with (Zlength l) by lia.
  rewrite sublist_full_Zlength.
  reflexivity.
Qed.
