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
From SimpleC.EE.CAV.verify_20260421_232321_array_reverse_in_place Require Import array_reverse_in_place_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope sac.

Lemma array_reverse_Zlength_rev {A: Type} (xs: list A):
  Zlength (rev xs) = Zlength xs.
Proof.
  rewrite !Zlength_correct, length_rev.
  reflexivity.
Qed.

Lemma array_reverse_sublist_snoc {A: Type}:
  forall (xs: list A) lo hi (d: A),
    0 <= lo < hi ->
    hi <= Zlength xs ->
    rev (sublist lo hi xs) =
      rev (sublist (lo + 1) hi xs) ++ [Znth lo xs d].
Proof.
  intros.
  rewrite Zlength_correct in H0.
  rewrite (sublist_split lo hi (lo + 1) xs) by lia.
  rewrite (sublist_single lo xs d) by lia.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma array_reverse_sublist_extend_right {A: Type}:
  forall (xs: list A) lo hi (d: A),
    0 <= lo <= hi ->
    hi < Zlength xs ->
    rev (sublist lo (hi + 1) xs) =
      [Znth hi xs d] ++ rev (sublist lo hi xs).
Proof.
  intros.
  rewrite Zlength_correct in H0.
  rewrite (sublist_split lo (hi + 1) hi xs) by lia.
  rewrite (sublist_single hi xs d) by lia.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma array_reverse_swap_step:
  forall (xs: list Z) n left right,
    Zlength xs = n ->
    0 <= left ->
    left < right ->
    right < n ->
    left = n - 1 - right ->
    replace_Znth right
      (Znth left
        (rev (sublist (right + 1) n xs) ++
         sublist left (right + 1) xs ++ rev (sublist 0 left xs)) 0)
      (replace_Znth left
        (Znth right
          (rev (sublist (right + 1) n xs) ++
           sublist left (right + 1) xs ++ rev (sublist 0 left xs)) 0)
        (rev (sublist (right + 1) n xs) ++
         sublist left (right + 1) xs ++ rev (sublist 0 left xs))) =
    rev (sublist right n xs) ++
    sublist (left + 1) right xs ++ rev (sublist 0 (left + 1) xs).
Proof.
  intros xs n left right Hlen Hleft Hlt Hright Hsym.
  pose proof Hlen as HZlen.
  rewrite Zlength_correct in Hlen.
  set (A := rev (sublist (right + 1) n xs)).
  set (B := sublist (left + 1) right xs).
  set (C := rev (sublist 0 left xs)).
  set (x := Znth left xs 0).
  set (y := Znth right xs 0).
  assert (HlenA : Zlength A = left).
  {
    unfold A.
    rewrite array_reverse_Zlength_rev.
    rewrite Zlength_sublist by lia.
    lia.
  }
  assert (HlenB : Zlength B = right - left - 1).
  {
    unfold B.
    rewrite Zlength_sublist by lia.
    lia.
  }
  assert (Hcur :
    A ++ sublist left (right + 1) xs ++ C =
    A ++ [x] ++ B ++ [y] ++ C).
  {
    unfold B, x, y.
    rewrite (sublist_split left (right + 1) (left + 1) xs) by lia.
    rewrite (sublist_split (left + 1) (right + 1) right xs) by lia.
    rewrite (sublist_single left xs 0) by lia.
    rewrite (sublist_single right xs 0) by lia.
    repeat rewrite app_assoc.
    reflexivity.
  }
  assert (HZleft :
    Znth left (A ++ sublist left (right + 1) xs ++ C) 0 = x).
  {
    rewrite Hcur.
    rewrite app_Znth2 by lia.
    replace (left - Zlength A) with 0 by lia.
    cbn.
    reflexivity.
  }
  assert (HZright :
    Znth right (A ++ sublist left (right + 1) xs ++ C) 0 = y).
  {
    rewrite Hcur.
    rewrite app_Znth2 by lia.
    replace (right - Zlength A) with (Zlength ([x] ++ B)) by
      (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    replace (Zlength ([x] ++ B)) with (1 + Zlength B) by
      (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    rewrite app_Znth2 by (rewrite Zlength_cons, Zlength_nil; lia).
    replace (1 + Zlength B - Zlength [x]) with (Zlength B) by
      (rewrite Zlength_cons, Zlength_nil; lia).
    rewrite app_Znth2 by lia.
    replace (Zlength B - Zlength B) with 0 by lia.
    cbn.
    reflexivity.
  }
  assert (HZleft_cur : Znth left (A ++ [x] ++ B ++ [y] ++ C) 0 = x).
  {
    rewrite app_Znth2 by lia.
    replace (left - Zlength A) with 0 by lia.
    cbn.
    reflexivity.
  }
  assert (HZright_cur : Znth right (A ++ [x] ++ B ++ [y] ++ C) 0 = y).
  {
    rewrite app_Znth2 by lia.
    replace (right - Zlength A) with (1 + Zlength B) by lia.
    rewrite app_Znth2 by (rewrite Zlength_cons, Zlength_nil; lia).
    replace (1 + Zlength B - Zlength [x]) with (Zlength B) by
      (rewrite Zlength_cons, Zlength_nil; lia).
    rewrite app_Znth2 by lia.
    replace (Zlength B - Zlength B) with 0 by lia.
    cbn.
    reflexivity.
  }
  replace (A ++ (sublist left (right + 1) xs ++ C))
    with (A ++ [x] ++ B ++ [y] ++ C) by (symmetry; exact Hcur).
  rewrite HZleft_cur, HZright_cur.
  rewrite replace_Znth_app_r by lia.
  rewrite (replace_Znth_nothing left A y) by lia.
  replace (left - Zlength A) with 0 by lia.
  cbn.
  rewrite replace_Znth_app_r by lia.
  rewrite (replace_Znth_nothing right A x) by lia.
  replace (right - Zlength A) with (1 + Zlength B) by lia.
  change (replace_Znth (1 + Zlength B) x (y :: B ++ y :: C))
    with (replace_Znth (1 + Zlength B) x ([y] ++ B ++ [y] ++ C)).
  rewrite replace_Znth_app_r with (l1 := [y]) (l2 := B ++ [y] ++ C) by
    (rewrite Zlength_cons, Zlength_nil; lia).
  rewrite (replace_Znth_nothing (1 + Zlength B) [y] x) by
    (rewrite Zlength_cons, Zlength_nil; lia).
  replace (1 + Zlength B - Zlength [y]) with (Zlength B) by
    (rewrite Zlength_cons, Zlength_nil; lia).
  rewrite replace_Znth_app_r with (l1 := B) (l2 := [y] ++ C) by lia.
  rewrite (replace_Znth_nothing (Zlength B) B x) by lia.
  replace (Zlength B - Zlength B) with 0 by lia.
  cbn.
  unfold A, B, C, x, y.
  rewrite (array_reverse_sublist_snoc xs right n 0) by lia.
  change (rev (firstn (Z.to_nat (left + 1)) xs))
    with (rev (sublist 0 (left + 1) xs)).
  rewrite (array_reverse_sublist_extend_right xs 0 left 0) by lia.
  change (rev (firstn (Z.to_nat left) xs)) with (rev (sublist 0 left xs)).
  change (Znth right xs 0 :: sublist (left + 1) right xs ++
          Znth left xs 0 :: rev (sublist 0 left xs))
    with ([Znth right xs 0] ++ sublist (left + 1) right xs ++
          [Znth left xs 0] ++ rev (sublist 0 left xs)).
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma array_reverse_exit_list:
  forall (xs: list Z) n left right,
    Zlength xs = n ->
    0 <= left ->
    -1 <= right ->
    left >= right ->
    left <= right + 1 ->
    left = n - 1 - right ->
    0 <= n ->
    rev (sublist (right + 1) n xs) ++
    sublist left (right + 1) xs ++ rev (sublist 0 left xs) =
    rev xs.
Proof.
  intros xs n left right Hlen Hleft Hright Hge Hle Hsym Hn.
  pose proof Hlen as HZlen.
  rewrite Zlength_correct in Hlen.
  assert (Hcases : left = right \/ left = right + 1) by lia.
  destruct Hcases as [Heq | Heq].
  - subst right.
    assert (left < n) by lia.
    rewrite (sublist_single left xs 0) by lia.
    change (rev (firstn (Z.to_nat left) xs)) with (rev (sublist 0 left xs)).
    rewrite app_assoc.
    rewrite <- (array_reverse_sublist_snoc xs left n 0) by lia.
    rewrite <- rev_app_distr.
    rewrite <- (sublist_split 0 n left xs) by lia.
    rewrite sublist_self by lia.
    reflexivity.
  - subst left.
    replace (n - 1 - right) with (right + 1) by lia.
    rewrite (sublist_nil xs (right + 1) (right + 1)) by lia.
    simpl.
    change (rev (firstn (Z.to_nat (right + 1)) xs))
      with (rev (sublist 0 (right + 1) xs)).
    rewrite <- rev_app_distr.
    rewrite <- (sublist_split 0 n (right + 1) xs) by lia.
    rewrite sublist_self by lia.
    reflexivity.
Qed.

Lemma proof_of_array_reverse_in_place_entail_wit_1 : array_reverse_in_place_entail_wit_1.
Proof.
  pre_process.
  replace (n_pre - 1 + 1) with n_pre by lia.
  rewrite sublist_nil by lia.
  rewrite sublist_self by lia.
  rewrite sublist_nil by lia.
  simpl.
  rewrite app_nil_r.
  entailer!.
Qed.

Lemma proof_of_array_reverse_in_place_entail_wit_2 : array_reverse_in_place_entail_wit_2.
Proof.
  pre_process.
  rewrite array_reverse_swap_step by lia.
  replace (right - 1 + 1) with right by lia.
  entailer!.
Qed.

Lemma proof_of_array_reverse_in_place_return_wit_1 : array_reverse_in_place_return_wit_1.
Proof.
  pre_process.
  rewrite array_reverse_exit_list by lia.
  entailer!.
Qed.
