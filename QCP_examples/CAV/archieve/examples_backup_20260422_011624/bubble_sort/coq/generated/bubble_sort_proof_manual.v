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
From SimpleC.EE.CAV.verify_20260417_202657_bubble_sort Require Import bubble_sort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import bubble_sort.
Local Open Scope sac.

Lemma sublist_full_Zlength : forall {A} (l : list A),
  sublist 0 (Zlength l) l = l.
Proof.
  intros.
  unfold sublist.
  rewrite skipn_O.
  rewrite Zlength_correct.
  rewrite firstn_all2 by lia.
  reflexivity.
Qed.

Lemma sorted_z_singleton : forall x, sorted_z (x :: nil).
Proof. intros; simpl; auto. Qed.

Lemma nth_a_replace_nth_b:
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

Lemma replace_nth_length:
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

Lemma nth_replace_nth_eq:
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

Lemma replace_Znth_length {A: Type}:
  forall (l:list A) n a,
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros l n a.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite replace_nth_length.
  reflexivity.
Qed.

Lemma Znth_replace_Znth_eq :
  forall {A} n (l : list A) v d,
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_eq.
  rewrite Zlength_correct in H.
  lia.
Qed.

Lemma Znth_replace_Znth_other :
  forall {A} n m (l : list A) v d,
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
Proof.
  intros.
  unfold Znth, replace_Znth.
  apply nth_a_replace_nth_b.
  intro Heq.
  apply H1.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma sorted_z_cons_intro :
  forall x l,
    sorted_z l ->
    (forall q, 0 <= q < Zlength l -> x <= Znth q l 0) ->
    sorted_z (x :: l).
Proof.
  intros x l Hsorted Hle.
  destruct l.
  - apply sorted_z_singleton.
  - simpl.
    split.
    + specialize (Hle 0).
      simpl in Hle.
      apply Hle; rewrite Zlength_correct; simpl; lia.
    + exact Hsorted.
Qed.

Lemma swap_prefix_eq_nat : forall (pref tail : list Z) x y,
  replace_nth (length pref + 1)%nat x
    (replace_nth (length pref)%nat y (pref ++ x :: y :: tail)) =
  pref ++ y :: x :: tail.
Proof.
  induction pref; intros; simpl.
  - reflexivity.
  - rewrite IHpref; reflexivity.
Qed.

Lemma swap_prefix_eq : forall (pref tail : list Z) x y,
  replace_Znth (Zlength pref + 1) x
    (replace_Znth (Zlength pref) y (pref ++ x :: y :: tail)) =
  pref ++ y :: x :: tail.
Proof.
  intros.
  unfold replace_Znth.
  rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length pref) + 1)) with (length pref + 1)%nat by lia.
  replace (Z.to_nat (Z.of_nat (length pref))) with (length pref)%nat by lia.
  rewrite swap_prefix_eq_nat.
  reflexivity.
Qed.

Lemma Znth_pref_head : forall (pref tail : list Z) (x y d : Z),
  Znth (Zlength pref) (pref ++ x :: y :: tail) d = x.
Proof.
  intros.
  rewrite app_Znth2 by (rewrite Zlength_correct; simpl; lia).
  rewrite Zminus_diag.
  apply Znth0_cons.
Qed.

Lemma Znth_pref_next : forall (pref tail : list Z) (x y d : Z),
  Znth (Zlength pref + 1) (pref ++ x :: y :: tail) d = y.
Proof.
  intros.
  rewrite app_Znth2 by (rewrite Zlength_correct; simpl; lia).
  replace (Zlength pref + 1 - Zlength pref) with 1 by lia.
  rewrite Znth_cons by lia.
  replace (1 - 1) with 0 by lia.
  apply Znth0_cons.
Qed.

Lemma adjacent_swap_perm_pref : forall (pref tail : list Z) (x y : Z),
  Permutation (pref ++ x :: y :: tail)
    (replace_Znth (Zlength pref + 1) x
       (replace_Znth (Zlength pref) y (pref ++ x :: y :: tail))).
Proof.
  intros.
  rewrite swap_prefix_eq.
  change (Permutation (pref ++ x :: y :: tail) (pref ++ y :: x :: tail)).
  apply Permutation_app_head.
  apply perm_swap.
Qed.

Lemma adjacent_swap_perm_z :
  forall (l : list Z) j d,
    0 <= j -> j + 1 < Zlength l ->
    Permutation l
      (replace_Znth (j + 1) (Znth j l d)
         (replace_Znth j (Znth (j + 1) l d) l)).
Proof.
  intros l j d Hj Hjlen.
  pose proof Hjlen as Hjlen'.
  rewrite Zlength_correct in Hjlen'.
  set (n := Z.to_nat j).
  assert (Hn : (n < length l)%nat) by (unfold n; lia).
  rewrite (list_split_nth _ n l d Hn).
  set (pref := firstn n l).
  set (suf := skipn (S n) l).
  assert (Hsuflen : (0 < length suf)%nat).
  { unfold suf. rewrite skipn_length. lia. }
  assert (Hsuf : suf = nth 0%nat suf d :: skipn 1%nat suf).
  { destruct suf; simpl in *; [lia|reflexivity]. }
  rewrite Hsuf.
  assert (Hzpref : Zlength pref = j).
  { unfold pref, n. rewrite Zlength_correct, firstn_length. lia. }
  set (x := nth n l d).
  set (y := nth 0%nat suf d).
  set (tail := skipn 1%nat suf).
  replace j with (Zlength pref) by lia.
  change (Permutation (pref ++ x :: y :: tail)
    (replace_Znth (Zlength pref + 1)
       (Znth (Zlength pref) (pref ++ x :: y :: tail) d)
       (replace_Znth (Zlength pref)
          (Znth (Zlength pref + 1) (pref ++ x :: y :: tail) d)
          (pref ++ x :: y :: tail)))).
  rewrite (Znth_pref_head pref tail x y d).
  rewrite (Znth_pref_next pref tail x y d).
  apply adjacent_swap_perm_pref.
Qed.

Lemma adjacent_swap_suffix_unchanged :
  forall (l : list Z) j b e d,
    0 <= j -> j + 1 < b -> b <= e -> e <= Zlength l ->
    sublist b e
      (replace_Znth (j + 1) (Znth j l d)
         (replace_Znth j (Znth (j + 1) l d) l)) = sublist b e l.
Proof.
  intros l j b e d Hj Hjb Hbe Hel.
  set (lswap := replace_Znth (j + 1) (Znth j l d) (replace_Znth j (Znth (j + 1) l d) l)).
  assert (Hlen : Zlength lswap = Zlength l).
  { unfold lswap. rewrite !replace_Znth_length. reflexivity. }
  apply (proj2 (list_eq_ext 0 _ _)).
  split.
  - rewrite (Zlength_sublist b e lswap) by (rewrite Hlen; lia).
    rewrite (Zlength_sublist b e l) by lia.
    lia.
  - intros k Hk.
    assert (Hb : 0 <= b <= e) by lia.
    assert (He_swap : e <= Z.of_nat (length lswap)).
    { rewrite <- Zlength_correct. rewrite Hlen. exact Hel. }
    assert (He : e <= Z.of_nat (length l)).
    { rewrite <- Zlength_correct. exact Hel. }
    assert (Hkk : 0 <= k < e - b).
    { rewrite (Zlength_sublist b e lswap) in Hk by (rewrite Hlen; lia). lia. }
    rewrite (Znth_sublist_lt b e lswap k 0 Hb He_swap Hkk).
    rewrite (Znth_sublist_lt b e l k 0 Hb He Hkk).
    unfold lswap.
    assert (Hbk : 0 <= b + k < Zlength l) by lia.
    assert (Hbk_swap : 0 <= b + k < Zlength (replace_Znth j (Znth (j + 1) l d) l)).
    { rewrite replace_Znth_length. exact Hbk. }
    assert (Hneq_j1 : b + k <> j + 1) by lia.
    assert (Hneq_j : b + k <> j) by lia.
    assert (Houter :
      Znth (b + k)
        (replace_Znth (j + 1) (Znth j l d) (replace_Znth j (Znth (j + 1) l d) l)) 0 =
      Znth (b + k) (replace_Znth j (Znth (j + 1) l d) l) 0).
    { apply Znth_replace_Znth_other; [lia | exact Hbk_swap | exact Hneq_j1]. }
    rewrite Houter.
    assert (Hinner :
      Znth (b + k) (replace_Znth j (Znth (j + 1) l d) l) 0 =
      Znth (b + k) l 0).
    { apply Znth_replace_Znth_other; [lia | exact Hbk | exact Hneq_j]. }
    rewrite Hinner.
    reflexivity.
Qed.

Lemma adjacent_swap_Znth_j :
  forall (l : list Z) j,
    0 <= j -> j + 1 < Zlength l ->
    Znth j
      (replace_Znth (j + 1) (Znth j l 0)
         (replace_Znth j (Znth (j + 1) l 0) l)) 0 =
    Znth (j + 1) l 0.
Proof.
  intros.
  assert (Hrange : 0 <= j < Zlength (replace_Znth j (Znth (j + 1) l 0) l)).
  { rewrite replace_Znth_length. lia. }
  assert (Hneq : j <> j + 1) by lia.
  assert (Houter :
    Znth j
      (replace_Znth (j + 1) (Znth j l 0)
         (replace_Znth j (Znth (j + 1) l 0) l)) 0 =
    Znth j (replace_Znth j (Znth (j + 1) l 0) l) 0).
  { apply Znth_replace_Znth_other; [lia | exact Hrange | exact Hneq]. }
  rewrite Houter.
  apply Znth_replace_Znth_eq.
  lia.
Qed.

Lemma adjacent_swap_Znth_j1 :
  forall (l : list Z) j,
    0 <= j -> j + 1 < Zlength l ->
    Znth (j + 1)
      (replace_Znth (j + 1) (Znth j l 0)
         (replace_Znth j (Znth (j + 1) l 0) l)) 0 =
    Znth j l 0.
Proof.
  intros.
  apply Znth_replace_Znth_eq.
  rewrite replace_Znth_length.
  lia.
Qed.

Lemma adjacent_swap_Znth_other :
  forall (l : list Z) j p,
    0 <= j -> j + 1 < Zlength l ->
    0 <= p < Zlength l ->
    p <> j -> p <> j + 1 ->
    Znth p
      (replace_Znth (j + 1) (Znth j l 0)
         (replace_Znth j (Znth (j + 1) l 0) l)) 0 =
    Znth p l 0.
Proof.
  intros.
  assert (Hrange_inner : 0 <= p < Zlength (replace_Znth j (Znth (j + 1) l 0) l)).
  { rewrite replace_Znth_length. exact H1. }
  assert (Houter :
    Znth p
      (replace_Znth (j + 1) (Znth j l 0)
         (replace_Znth j (Znth (j + 1) l 0) l)) 0 =
    Znth p (replace_Znth j (Znth (j + 1) l 0) l) 0).
  { apply Znth_replace_Znth_other; [lia | exact Hrange_inner | exact H3]. }
  rewrite Houter.
  apply Znth_replace_Znth_other; [lia | exact H1 | exact H2].
Qed.

Lemma adjacent_swap_cross_order :
  forall (l : list Z) j b n p q,
    0 <= j -> j + 1 < b -> b <= n -> n <= Zlength l ->
    0 <= p < b -> b <= q < n ->
    (forall p q, 0 <= p < b -> b <= q < n -> Znth p l 0 <= Znth q l 0) ->
    Znth p
      (replace_Znth (j + 1) (Znth j l 0)
         (replace_Znth j (Znth (j + 1) l 0) l)) 0 <=
    Znth q
      (replace_Znth (j + 1) (Znth j l 0)
         (replace_Znth j (Znth (j + 1) l 0) l)) 0.
Proof.
  intros l j b n p q Hj Hjb Hbn Hnlen Hp Hq Hcross.
  assert (Hqrange : 0 <= q < Zlength l) by lia.
  assert (Hqswap :
    Znth q
      (replace_Znth (j + 1) (Znth j l 0)
         (replace_Znth j (Znth (j + 1) l 0) l)) 0 =
    Znth q l 0).
  { apply adjacent_swap_Znth_other; lia. }
  rewrite Hqswap.
  destruct (Z.eq_dec p j) as [->|Hpj].
  - rewrite adjacent_swap_Znth_j by lia.
    apply Hcross; lia.
  - destruct (Z.eq_dec p (j + 1)) as [->|Hpj1].
    + rewrite adjacent_swap_Znth_j1 by lia.
      apply Hcross; lia.
    + rewrite adjacent_swap_Znth_other by lia.
      apply Hcross; lia.
Qed.

Lemma adjacent_swap_prefix_max :
  forall (l : list Z) j,
    0 <= j -> j + 1 < Zlength l ->
    Znth j l 0 > Znth (j + 1) l 0 ->
    (forall k, 0 <= k <= j -> Znth k l 0 <= Znth j l 0) ->
    forall k,
      0 <= k <= j + 1 ->
      Znth k
        (replace_Znth (j + 1) (Znth j l 0)
           (replace_Znth j (Znth (j + 1) l 0) l)) 0 <=
      Znth (j + 1)
        (replace_Znth (j + 1) (Znth j l 0)
           (replace_Znth j (Znth (j + 1) l 0) l)) 0.
Proof.
  intros l j Hj Hjlen Hgt Hmax k Hk.
  rewrite adjacent_swap_Znth_j1 by lia.
  destruct (Z.eq_dec k (j + 1)) as [->|Hkj1].
  - rewrite adjacent_swap_Znth_j1 by lia.
    apply Z.le_refl.
  - destruct (Z.eq_dec k j) as [->|Hkj].
    + rewrite adjacent_swap_Znth_j by lia.
      lia.
    + rewrite adjacent_swap_Znth_other by lia.
      apply Hmax; lia.
Qed.

Lemma proof_of_bubble_sort_entail_wit_1 : bubble_sort_entail_wit_1.
Proof.
  unfold bubble_sort_entail_wit_1.
  intros.
  Exists l.
  entailer!.
  rewrite sublist_nil by lia.
  simpl; auto.
Qed.

Lemma proof_of_bubble_sort_entail_wit_2 : bubble_sort_entail_wit_2.
Proof.
  unfold bubble_sort_entail_wit_2.
  intros.
  Exists l_outer.
  entailer!.
  intros k [Hk0 Hk1].
  assert (k = 0) by lia.
  subst k.
  apply Z.le_refl.
Qed.

Lemma proof_of_bubble_sort_entail_wit_3_1 : bubble_sort_entail_wit_3_1.
Proof.
  unfold bubble_sort_entail_wit_3_1.
  intros.
  set (lswap := replace_Znth (j + 1) (Znth j l_inner_2 0)
    (replace_Znth j (Znth (j + 1) l_inner_2 0) l_inner_2)).
  Exists lswap.
  Intros.
  prop_apply IntArray.full_length.
  entailer!; try lia.
  - intros k Hk.
    assert (Hlen_inner_nat : Z.of_nat (Datatypes.length l_inner_2) = n_pre).
    { subst lswap. unfold replace_Znth in H17. rewrite !replace_nth_length in H17. exact H17. }
    assert (Hlen_inner : Zlength l_inner_2 = n_pre).
    { rewrite Zlength_correct. exact Hlen_inner_nat. }
    subst lswap.
    eapply adjacent_swap_prefix_max.
    + lia.
    + rewrite Hlen_inner. lia.
    + exact H.
    + exact H8.
    + exact Hk.
  - intros p_2 Hp q_2 Hq.
    assert (Hlen_inner_nat : Z.of_nat (Datatypes.length l_inner_2) = n_pre).
    { subst lswap. unfold replace_Znth in H17. rewrite !replace_nth_length in H17. exact H17. }
    assert (Hlen_inner : Zlength l_inner_2 = n_pre).
    { rewrite Zlength_correct. exact Hlen_inner_nat. }
    subst lswap.
    eapply adjacent_swap_cross_order with (b := n_pre - i_2) (n := n_pre).
    + lia.
    + exact H0.
    + lia.
    + rewrite Hlen_inner. lia.
    + exact Hp.
    + exact Hq.
    + intros p q Hp' Hq'. exact (H7 p Hp' q Hq').
  - subst lswap.
    assert (Hlen_inner_nat : Z.of_nat (Datatypes.length l_inner_2) = n_pre).
    { unfold replace_Znth in H17. rewrite !replace_nth_length in H17. exact H17. }
    assert (Hlen_inner : Zlength l_inner_2 = n_pre).
    { rewrite Zlength_correct. exact Hlen_inner_nat. }
    erewrite (adjacent_swap_suffix_unchanged l_inner_2 j (n_pre - i_2) n_pre 0).
    1:{ exact H6. }
    all: try lia.
  - subst lswap.
    assert (Hlen_inner_nat : Z.of_nat (Datatypes.length l_inner_2) = n_pre).
    { unfold replace_Znth in H17. rewrite !replace_nth_length in H17. exact H17. }
    assert (Hlen_inner : Zlength l_inner_2 = n_pre).
    { rewrite Zlength_correct. exact Hlen_inner_nat. }
    eapply Permutation_trans.
    + exact H5.
    + eapply adjacent_swap_perm_z.
      * lia.
      * rewrite Hlen_inner. lia.
Qed.

Lemma proof_of_bubble_sort_entail_wit_4 : bubble_sort_entail_wit_4.
Proof.
  unfold bubble_sort_entail_wit_4.
  intros.
  Exists l_inner.
  Intros.
  prop_apply IntArray.full_length.
  entailer!; try lia.
  - apply store_int_undef_store_int.
  - intros p Hp q Hq.
    assert (Hlen_inner : Zlength l_inner = n_pre).
    { rewrite Zlength_correct. exact H16. }
    assert (Hj : j = n_pre - i - 1) by lia.
    destruct (Z.eq_dec q j) as [->|Hqj].
    + apply H7. lia.
    + assert (n_pre - i <= q) by lia.
      apply H6; lia.
  - assert (Hlen_inner : Zlength l_inner = n_pre).
    { rewrite Zlength_correct. exact H16. }
    pose proof (Zlength_correct l_inner) as Hlen_inner_nat.
    assert (Hj : j = n_pre - i - 1) by lia.
    replace (n_pre - (i + 1)) with j by lia.
    rewrite (sublist_split j n_pre (j + 1) l_inner) by lia.
    rewrite (sublist_single j l_inner 0) by lia.
    replace (j + 1) with (n_pre - i) by lia.
    simpl.
    change (sorted_z (Znth j l_inner 0 :: sublist (n_pre - i) n_pre l_inner)).
    apply sorted_z_cons_intro.
    + exact H5.
    + intros q Hq.
      assert (Hq' : 0 <= q < n_pre - (n_pre - i)).
      { rewrite Zlength_correct in Hq.
        rewrite sublist_length in Hq by lia.
        lia. }
      rewrite (Znth_sublist (n_pre - i) q n_pre l_inner 0) by lia.
      apply H6; lia.
Qed. 

Lemma proof_of_bubble_sort_return_wit_1 : bubble_sort_return_wit_1.
Proof.
  unfold bubble_sort_return_wit_1.
  intros.
  Exists l_outer.
  Intros.
  prop_apply IntArray.full_length.
  entailer!.
  replace i with n_pre in H3 by lia.
  replace (n_pre - n_pre) with 0 in H3 by lia.
  replace n_pre with (Zlength l_outer) in H3.
  2:{ rewrite Zlength_correct. exact H7. }
  rewrite sublist_full_Zlength in H3.
  exact H3.
Qed.
