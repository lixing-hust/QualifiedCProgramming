Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
From AUXLib Require Import ListLib.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260421_173306_selection_sort Require Import selection_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import selection_sort.
Local Open Scope sac.

Lemma selection_sort_sublist_full_Zlength : forall {A} (l : list A),
  sublist 0 (Zlength l) l = l.
Proof.
  intros.
  unfold sublist.
  rewrite skipn_O.
  rewrite Zlength_correct.
  rewrite firstn_all2 by lia.
  reflexivity.
Qed.

Lemma selection_sort_replace_nth_length:
  forall T (l: list T) i v,
    length (replace_nth i v l) = length l.
Proof.
  intros.
  revert i v.
  induction l; intros; simpl.
  - destruct i; reflexivity.
  - destruct i; simpl; try reflexivity.
    rewrite IHl; reflexivity.
Qed.

Lemma selection_sort_nth_replace_nth_eq:
  forall T (l: list T) i v u,
    (i < length l)%nat ->
    nth i (replace_nth i v l) u = v.
Proof.
  intros.
  revert i H.
  induction l; intros; simpl in *.
  - lia.
  - destruct i; simpl.
    + reflexivity.
    + apply IHl; lia.
Qed.

Lemma selection_sort_nth_replace_nth_other:
  forall T (l: list T) a b (v u: T),
    (a <> b)%nat ->
    nth a (replace_nth b v l) u = nth a l u.
Proof.
  intros.
  revert a b H.
  induction l; intros.
  - destruct a; destruct b; try lia; reflexivity.
  - destruct a0; simpl.
    + destruct b; simpl; [lia | reflexivity].
    + destruct b; simpl; try reflexivity.
      assert (a0 <> b)%nat by lia.
      apply IHl; easy.
Qed.

Lemma selection_sort_replace_Znth_length {A: Type}:
  forall (l:list A) n a,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros l n a.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite selection_sort_replace_nth_length.
  reflexivity.
Qed.

Lemma selection_sort_Znth_replace_Znth_eq :
  forall {A} n (l : list A) v d,
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply selection_sort_nth_replace_nth_eq.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma selection_sort_Znth_replace_Znth_other :
  forall {A} n m (l : list A) v d,
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply selection_sort_nth_replace_nth_other.
  intro Heq.
  apply H1.
  apply Z2Nat.inj in Heq; lia.
Qed.

Definition selection_sort_swap (l : list Z) (i min_idx : Z) : list Z :=
  replace_Znth min_idx (Znth i l 0)
    (replace_Znth i (Znth min_idx l 0) l).

Lemma selection_sort_swap_length :
  forall l i min_idx,
    Zlength (selection_sort_swap l i min_idx) = Zlength l.
Proof.
  intros.
  unfold selection_sort_swap.
  rewrite !selection_sort_replace_Znth_length.
  reflexivity.
Qed.

Lemma selection_sort_swap_Znth_i :
  forall l i min_idx,
    0 <= i /\ i <= min_idx /\ min_idx < Zlength l ->
    Znth i (selection_sort_swap l i min_idx) 0 = Znth min_idx l 0.
Proof.
  intros l i min_idx Hrange.
  unfold selection_sort_swap.
  destruct (Z.eq_dec i min_idx) as [Heq|Hneq].
  - subst min_idx.
    rewrite selection_sort_Znth_replace_Znth_eq.
    + reflexivity.
    + rewrite selection_sort_replace_Znth_length. lia.
  - assert (Hi_inner :
      0 <= i < Zlength (replace_Znth i (Znth min_idx l 0) l)).
    { rewrite selection_sort_replace_Znth_length. lia. }
    rewrite selection_sort_Znth_replace_Znth_other
      with (n := min_idx) by (try exact Hi_inner; lia).
    apply selection_sort_Znth_replace_Znth_eq.
    lia.
Qed.

Lemma selection_sort_swap_Znth_min :
  forall l i min_idx,
    0 <= i /\ i <= min_idx /\ min_idx < Zlength l ->
    Znth min_idx (selection_sort_swap l i min_idx) 0 = Znth i l 0.
Proof.
  intros l i min_idx Hrange.
  unfold selection_sort_swap.
  apply selection_sort_Znth_replace_Znth_eq.
  rewrite selection_sort_replace_Znth_length.
  lia.
Qed.

Lemma selection_sort_swap_Znth_other :
  forall l i min_idx p,
    0 <= i /\ i <= min_idx /\ min_idx < Zlength l ->
    0 <= p < Zlength l ->
    p <> i ->
    p <> min_idx ->
    Znth p (selection_sort_swap l i min_idx) 0 = Znth p l 0.
Proof.
  intros l i min_idx p Hrange Hp Hpi Hpm.
  unfold selection_sort_swap.
  assert (Hp_inner :
    0 <= p < Zlength (replace_Znth i (Znth min_idx l 0) l)).
  { rewrite selection_sort_replace_Znth_length. exact Hp. }
  rewrite selection_sort_Znth_replace_Znth_other
    with (n := min_idx) by (try exact Hp_inner; lia).
  apply selection_sort_Znth_replace_Znth_other; lia.
Qed.

Lemma selection_sort_swap_prefix_unchanged :
  forall l i min_idx,
    0 <= i /\ i <= min_idx /\ min_idx < Zlength l ->
    sublist 0 i (selection_sort_swap l i min_idx) = sublist 0 i l.
Proof.
  intros l i min_idx Hrange.
  apply (proj2 (list_eq_ext 0 _ _)).
  split.
  - rewrite !Zlength_sublist by (rewrite ?selection_sort_swap_length; lia).
    lia.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by (rewrite ?selection_sort_swap_length; lia).
    rewrite !Znth_sublist by lia.
    apply selection_sort_swap_Znth_other; lia.
Qed.

Lemma selection_sort_swap_prefix_extend :
  forall l i min_idx,
    0 <= i /\ i <= min_idx /\ min_idx < Zlength l ->
    sublist 0 (i + 1) (selection_sort_swap l i min_idx) =
    sublist 0 i l ++ (Znth min_idx l 0 :: nil).
Proof.
  intros l i min_idx Hrange.
  rewrite (sublist_split 0 (i + 1) i).
  2:{ split; lia. }
  2:{ rewrite <- Zlength_correct.
      rewrite selection_sort_swap_length.
      lia. }
  rewrite selection_sort_swap_prefix_unchanged by exact Hrange.
  rewrite (sublist_single i (selection_sort_swap l i min_idx) 0)
    by (rewrite <- Zlength_correct; rewrite selection_sort_swap_length; lia).
  rewrite selection_sort_swap_Znth_i by exact Hrange.
  reflexivity.
Qed.

Lemma selection_sort_sorted_z_app_one :
  forall l x,
    sorted_z l ->
    (forall k, 0 <= k < Zlength l -> Znth k l 0 <= x) ->
    sorted_z (l ++ (x :: nil)).
Proof.
  induction l; intros x Hs Hle; simpl.
  - auto.
  - destruct l.
    + simpl. split; auto.
      specialize (Hle 0).
      simpl in Hle.
      apply Hle.
      rewrite Zlength_correct. simpl. lia.
    + simpl in *. destruct Hs as [Hab Hs].
      split; auto.
      apply IHl; auto.
      intros k Hk.
      specialize (Hle (k + 1)).
      simpl in Hle.
      rewrite Znth_cons in Hle by lia.
      replace (k + 1 - 1) with k in Hle by lia.
      apply Hle.
      rewrite Zlength_correct in *. simpl in *. lia.
Qed.

Lemma selection_sort_swap_sorted_prefix :
  forall l i min_idx n,
    0 <= i /\ i <= min_idx /\ min_idx < n ->
    n = Zlength l ->
    sorted_z (sublist 0 i l) ->
    (forall p, 0 <= p < i -> forall q, i <= q < n -> Znth p l 0 <= Znth q l 0) ->
    (forall k, i <= k < n -> Znth min_idx l 0 <= Znth k l 0) ->
    sorted_z (sublist 0 (i + 1) (selection_sort_swap l i min_idx)).
Proof.
  intros l i min_idx n Hrange Hlen Hsorted Hcross Hmin.
  rewrite selection_sort_swap_prefix_extend by lia.
  apply selection_sort_sorted_z_app_one.
  - exact Hsorted.
  - intros k Hk.
    rewrite Zlength_sublist in Hk by lia.
    rewrite Znth_sublist by lia.
    apply Hcross; lia.
Qed.

Lemma selection_sort_swap_cross_order :
  forall l i min_idx n p q,
    0 <= i /\ i <= min_idx /\ min_idx < n ->
    n = Zlength l ->
    0 <= p < i + 1 ->
    i + 1 <= q < n ->
    (forall p, 0 <= p < i -> forall q, i <= q < n -> Znth p l 0 <= Znth q l 0) ->
    (forall k, i <= k < n -> Znth min_idx l 0 <= Znth k l 0) ->
    Znth p (selection_sort_swap l i min_idx) 0 <=
    Znth q (selection_sort_swap l i min_idx) 0.
Proof.
  intros l i min_idx n p q Hrange Hlen Hp Hq Hcross Hmin.
  assert (Hq_range_l : 0 <= q < Zlength l) by lia.
  assert (Hq_not_i : q <> i) by lia.
  destruct (Z.eq_dec q min_idx) as [Hqmin|Hqmin].
  - subst q.
    rewrite selection_sort_swap_Znth_min by lia.
    destruct (Z.eq_dec p i) as [Hpi|Hpi].
    + subst p.
      rewrite selection_sort_swap_Znth_i by lia.
      apply Hmin; lia.
    + rewrite (selection_sort_swap_Znth_other l i min_idx p) by lia.
      apply Hcross; lia.
  - rewrite (selection_sort_swap_Znth_other l i min_idx q) by lia.
    destruct (Z.eq_dec p i) as [Hpi|Hpi].
    + subst p.
      rewrite selection_sort_swap_Znth_i by lia.
      apply Hmin; lia.
    + rewrite (selection_sort_swap_Znth_other l i min_idx p) by lia.
      apply Hcross; lia.
Qed.

Lemma selection_sort_replace_nth_at_app :
  forall (pref tail : list Z) x y,
    replace_nth (length pref) y (pref ++ x :: tail) =
    pref ++ y :: tail.
Proof.
  induction pref; intros; simpl.
  - reflexivity.
  - rewrite IHpref. reflexivity.
Qed.

Lemma selection_sort_replace_nth_swap_gap :
  forall (pref mid tail : list Z) x y,
    replace_nth (length pref + S (length mid)) x
      (replace_nth (length pref) y (pref ++ x :: mid ++ y :: tail)) =
    pref ++ y :: mid ++ x :: tail.
Proof.
  induction pref; intros; simpl.
  - rewrite selection_sort_replace_nth_at_app. reflexivity.
  - rewrite IHpref. reflexivity.
Qed.

Lemma selection_sort_swap_split_eq :
  forall (pref mid tail : list Z) x y,
    selection_sort_swap (pref ++ x :: mid ++ y :: tail)
      (Zlength pref) (Zlength pref + 1 + Zlength mid) =
    pref ++ y :: mid ++ x :: tail.
Proof.
  intros.
  unfold selection_sort_swap.
  assert (Hx : Znth (Zlength pref) (pref ++ x :: mid ++ y :: tail) 0 = x).
  { rewrite app_Znth2 by lia.
    replace (Zlength pref - Zlength pref) with 0 by lia.
    apply Znth0_cons. }
  assert (Hy : Znth (Zlength pref + 1 + Zlength mid)
    (pref ++ x :: mid ++ y :: tail) 0 = y).
  { pose proof (Zlength_nonneg mid).
    rewrite app_Znth2 by lia.
    replace (Zlength pref + 1 + Zlength mid - Zlength pref)
      with (1 + Zlength mid) by lia.
    rewrite Znth_cons by lia.
    replace (1 + Zlength mid - 1) with (Zlength mid) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength mid - Zlength mid) with 0 by lia.
    apply Znth0_cons. }
  rewrite Hx, Hy.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length pref))) with (length pref) by lia.
  replace (Z.to_nat (Z.of_nat (length pref) + 1 + Z.of_nat (length mid)))
    with (length pref + S (length mid))%nat by lia.
  apply selection_sort_replace_nth_swap_gap.
Qed.

Lemma selection_sort_swap_perm :
  forall l i min_idx,
    0 <= i /\ i <= min_idx /\ min_idx < Zlength l ->
    Permutation l (selection_sort_swap l i min_idx).
Proof.
  intros l i min_idx Hrange.
  destruct (Z.eq_dec i min_idx) as [Heq|Hneq].
  - subst min_idx.
    unfold selection_sort_swap.
    assert (Hsame :
      replace_Znth i (Znth i l 0) (replace_Znth i (Znth i l 0) l) = l).
    { apply (proj2 (list_eq_ext 0 _ _)).
      split.
      - rewrite !selection_sort_replace_Znth_length. reflexivity.
      - intros p Hp.
        destruct (Z.eq_dec p i) as [Hpi|Hpi].
        + subst p.
          rewrite selection_sort_Znth_replace_Znth_eq by
            (rewrite selection_sort_replace_Znth_length; lia).
          reflexivity.
        + assert (Hp_inner :
            0 <= p < Zlength (replace_Znth i (Znth i l 0) l)).
          { rewrite !selection_sort_replace_Znth_length in Hp.
            rewrite selection_sort_replace_Znth_length.
            lia. }
          rewrite (@selection_sort_Znth_replace_Znth_other Z i p
            (replace_Znth i (Znth i l 0) l) (Znth i l 0) 0)
            by (try exact Hp_inner; lia).
          assert (Hp_l : 0 <= p < Zlength l).
          { rewrite !selection_sort_replace_Znth_length in Hp. exact Hp. }
          rewrite (@selection_sort_Znth_replace_Znth_other Z i p l
            (Znth i l 0) 0) by (try exact Hp_l; lia).
          reflexivity. }
    rewrite Hsame.
    apply Permutation_refl.
  - assert (Hi_nat : (Z.to_nat i < length l)%nat).
    { rewrite Zlength_correct in Hrange. lia. }
    rewrite (list_split_nth _ (Z.to_nat i) l 0 Hi_nat).
    set (pref := firstn (Z.to_nat i) l).
    set (rest := skipn (S (Z.to_nat i)) l).
    assert (Hpref_len : Zlength pref = i).
    { unfold pref. rewrite Zlength_correct, firstn_length. lia. }
    assert (Hmin_rest : (Z.to_nat (min_idx - i - 1) < length rest)%nat).
    { unfold rest. rewrite skipn_length. rewrite Zlength_correct in Hrange. lia. }
    rewrite (list_split_nth _ (Z.to_nat (min_idx - i - 1)) rest 0 Hmin_rest).
    set (mid := firstn (Z.to_nat (min_idx - i - 1)) rest).
    set (tail := skipn (S (Z.to_nat (min_idx - i - 1))) rest).
    assert (Hmid_len : Zlength mid = min_idx - i - 1).
    { unfold mid. rewrite Zlength_correct, firstn_length. lia. }
    set (x0 := nth (Z.to_nat i) l 0).
    set (y0 := nth (Z.to_nat (min_idx - i - 1)) rest 0).
    change (Permutation (pref ++ x0 :: mid ++ y0 :: tail)
      (selection_sort_swap (pref ++ x0 :: mid ++ y0 :: tail) i min_idx)).
    replace i with (Zlength pref) by lia.
    replace min_idx with (Zlength pref + 1 + Zlength mid) by lia.
    rewrite selection_sort_swap_split_eq.
    apply Permutation_trans with
      (l' := pref ++ y0 :: mid ++ x0 :: tail).
    { apply Permutation_app_head.
      apply Permutation_trans with
        (l' := mid ++ x0 :: y0 :: tail).
      + apply Permutation_middle.
      + apply Permutation_trans with
          (l' := mid ++ y0 :: x0 :: tail).
        * apply Permutation_app_head. apply perm_swap.
        * symmetry. apply Permutation_middle. }
    { apply Permutation_refl. }
Qed.

Lemma proof_of_selection_sort_entail_wit_1 : selection_sort_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  entailer!.
Qed.

Lemma proof_of_selection_sort_entail_wit_2 : selection_sort_entail_wit_2.
Proof.
  pre_process.
  Exists l_outer.
  entailer!.
  intros k Hk.
  assert (k = i) by lia.
  subst k.
  apply Z.le_refl.
Qed.

Lemma proof_of_selection_sort_entail_wit_4 : selection_sort_entail_wit_4.
Proof.
  unfold selection_sort_entail_wit_4.
  intros.
  Exists (replace_Znth min_idx (Znth i l_inner 0)
    (replace_Znth i (Znth min_idx l_inner 0) l_inner)).
  Intros.
  prop_apply IntArray.full_length.
  entailer!; try lia.
  - sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    sep_apply store_int_undef_store_int.
    entailer!.
  - intros p Hp q Hq.
    change (Znth p (selection_sort_swap l_inner i min_idx) 0 <=
      Znth q (selection_sort_swap l_inner i min_idx) 0).
    eapply selection_sort_swap_cross_order with (n := n_pre).
    + lia.
    + symmetry.
      rewrite <- H18.
      rewrite <- !Zlength_correct.
      rewrite !selection_sort_replace_Znth_length.
      reflexivity.
    + exact Hp.
    + exact Hq.
    + intros p' Hp' q' Hq'. exact (H8 p' Hp' q' Hq').
    + intros k Hk. apply H9; lia.
  - change (sorted_z (sublist 0 (i + 1) (selection_sort_swap l_inner i min_idx))).
    eapply selection_sort_swap_sorted_prefix with (n := n_pre).
    + lia.
    + symmetry.
      rewrite <- H18.
      rewrite <- !Zlength_correct.
      rewrite !selection_sort_replace_Znth_length.
      reflexivity.
    + exact H7.
    + intros p Hp q Hq. exact (H8 p Hp q Hq).
    + intros k Hk. apply H9; lia.
  - eapply Permutation_trans.
    + exact H6.
    + apply selection_sort_swap_perm.
      assert (Hlen_inner : Zlength l_inner = n_pre).
      { rewrite Zlength_correct.
        rewrite <- H18.
        rewrite <- !Zlength_correct.
        rewrite !selection_sort_replace_Znth_length.
        reflexivity. }
      lia.
Qed. 

Lemma proof_of_selection_sort_return_wit_1 : selection_sort_return_wit_1.
Proof.
  pre_process.
  Exists l_outer.
  Intros.
  prop_apply IntArray.full_length.
  entailer!.
  replace i with n_pre in H3 by lia.
  replace n_pre with (Zlength l_outer) in H3.
  2:{ rewrite Zlength_correct. exact H7. }
  rewrite selection_sort_sublist_full_Zlength in H3.
  exact H3.
Qed.
