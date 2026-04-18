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
From SimpleC.EE.CAV.verify_20260418_205317_array_prefix_max Require Import array_prefix_max_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_max.
Local Open Scope sac.

Lemma sublist_full_Zlength : forall {A} (l : list A),
  sublist 0 (Zlength l) l = l.
Proof.
  intros.
  apply sublist_self.
  reflexivity.
Qed.

Lemma max_list_nonempty_upper_bound :
  forall (l : list Z) i d,
    0 <= i < Zlength l ->
    Znth i l d <= max_list_nonempty l.
Proof.
  induction l; intros i d Hi.
  - rewrite Zlength_nil in Hi. lia.
  - destruct l.
    + simpl.
      assert (i = 0) by (rewrite Zlength_cons, Zlength_nil in Hi; lia).
      subst i. rewrite Znth0_cons. lia.
    + simpl.
      destruct (Z.eq_dec i 0) as [Heq | Hneq].
      * subst i. rewrite Znth0_cons. apply Z.le_max_l.
      * assert (i > 0) by lia.
        rewrite Znth_cons by lia.
        eapply Z.le_trans.
        2: apply Z.le_max_r.
        apply IHl.
        rewrite Zlength_cons in Hi. lia.
Qed.

Lemma max_list_nonempty_bounded :
  forall (l : list Z) bound,
    1 <= Zlength l ->
    (forall i, 0 <= i < Zlength l -> Znth i l 0 <= bound) ->
    max_list_nonempty l <= bound.
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
      apply Z.max_lub.
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

Lemma max_list_nonempty_extend_ge :
  forall (l : list Z) x,
    1 <= Zlength l ->
    max_list_nonempty l <= max_list_nonempty (l ++ x :: nil).
Proof.
  induction l; intros x Hnz.
  - rewrite Zlength_nil in Hnz. lia.
  - destruct l.
    + simpl. apply Z.le_max_l.
    + simpl. apply Z.max_le_compat_l.
      assert (1 <= Zlength (z :: l)).
      { rewrite Zlength_cons. pose proof Zlength_nonneg l. lia. }
      apply IHl.
      exact H.
Qed.

Lemma max_list_nonempty_extend_keep :
  forall (l : list Z) x,
    1 <= Zlength l ->
    x <= max_list_nonempty l ->
    max_list_nonempty (l ++ x :: nil) = max_list_nonempty l.
Proof.
  intros l x Hnz Hx.
  apply Z.le_antisymm.
  - apply max_list_nonempty_bounded.
    + rewrite Zlength_app_cons. lia.
    + intros i Hi.
      destruct (Z_lt_ge_dec i (Zlength l)).
      * rewrite app_Znth1 by lia.
        eapply Z.le_trans.
        1: apply max_list_nonempty_upper_bound.
        2: lia.
        lia.
      * assert (i = Zlength l) by (rewrite Zlength_app_cons in Hi; lia).
        subst i.
        rewrite app_Znth2 by lia.
        rewrite Z.sub_diag.
        rewrite Znth0_cons.
        exact Hx.
  - apply max_list_nonempty_extend_ge.
    exact Hnz.
Qed.

Lemma proof_of_array_prefix_max_entail_wit_1 : array_prefix_max_entail_wit_1.
Proof.
  unfold array_prefix_max_entail_wit_1.
  intros.
  pre_process.
  Exists (Znth 0 la 0 :: nil).
  assert (replace_Znth 0 (Znth 0 la 0) lo =
          (Znth 0 la 0 :: nil) ++ sublist 1 n_pre lo) as Hout.
  {
    destruct lo.
    - rewrite Zlength_nil in H3. lia.
    - rewrite Zlength_cons in H3.
      assert (n_pre = 1 + Zlength lo) as Hn by lia.
      subst n_pre.
      unfold replace_Znth.
      simpl.
      unfold sublist.
      rewrite Hn.
      replace (Z.to_nat (1 + Zlength lo)) with (S (length lo)).
      2:{ rewrite Zlength_correct. lia. }
      rewrite firstn_all2 by reflexivity.
      simpl.
      reflexivity.
  }
  rewrite Hout.
  cancel.
  entailer!.
  - intros k Hk.
    assert (k = 0) by lia.
    subst k.
    rewrite Znth0_cons.
    destruct la.
    { rewrite Zlength_nil in H2. lia. }
    simpl.
    reflexivity.
  - destruct la.
    { rewrite Zlength_nil in H2. lia. }
    simpl.
    reflexivity.
Qed.

Lemma proof_of_array_prefix_max_entail_wit_2_2 : array_prefix_max_entail_wit_2_2.
Proof.
  unfold array_prefix_max_entail_wit_2_2.
  intros.
  Exists l1_2.
  entailer!.
  subst cur.
  rewrite (sublist_split 0 (i + 1) i la) by (pose proof Zlength_correct la; lia).
  rewrite (sublist_single i la 0) by (rewrite <- Zlength_correct; lia).
  symmetry.
  apply max_list_nonempty_extend_keep.
  - rewrite Zlength_sublist by lia. lia.
  - exact H.
Qed.

Lemma proof_of_array_prefix_max_entail_wit_3 : array_prefix_max_entail_wit_3.
Proof.
  unfold array_prefix_max_entail_wit_3.
  pre_process.
  Exists (l1_2 ++ cur :: nil).
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (i - Zlength l1_2) with 0 by lia.
  rewrite (sublist_split i n_pre (i + 1) lo) by (pose proof (Zlength_correct lo); lia).
  rewrite (sublist_single i lo 0) by (pose proof (Zlength_correct lo); lia).
  simpl.
  rewrite <- app_assoc.
  simpl.
  entailer!.
  - intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hlt | Hge].
    + rewrite app_Znth1 by (rewrite H4; lia).
      apply H6.
      lia.
    + assert (k = i) by lia.
      subst k.
      rewrite app_Znth2 by (rewrite H4; lia).
      rewrite H4.
      replace (i - i) with 0 by lia.
      rewrite Znth0_cons.
      exact H5.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_array_prefix_max_return_wit_1 : array_prefix_max_return_wit_1.
Proof.
  unfold array_prefix_max_return_wit_1.
  intros.
  Exists l1.
  entailer!.
  - assert (i_2 = n_pre) by lia.
    subst i_2.
    rewrite sublist_nil by lia.
    simpl.
    rewrite app_nil_r.
    cancel.
  - assert (i_2 = n_pre) by lia.
    subst i_2.
    intros i Hi.
    apply H8.
    lia.
Qed.

Lemma proof_of_array_prefix_max_return_wit_2 : array_prefix_max_return_wit_2.
Proof.
  unfold array_prefix_max_return_wit_2.
  intros.
  Exists lo.
  entailer!.
Qed.
