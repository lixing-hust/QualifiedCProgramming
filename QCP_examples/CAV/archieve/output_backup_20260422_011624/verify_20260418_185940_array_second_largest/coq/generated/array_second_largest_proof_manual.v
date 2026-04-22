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
From SimpleC.EE.CAV.verify_20260418_185940_array_second_largest Require Import array_second_largest_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_second_largest.
Local Open Scope sac.

Lemma sublist_head_cons :
  forall (l : list Z) i n,
    0 <= i < n ->
    n <= Zlength l ->
    sublist i n l = Znth i l 0 :: sublist (i + 1) n l.
Proof.
  intros l i n Hi Hn.
  rewrite (sublist_split i n (i + 1) l) by (pose proof Zlength_correct l; lia).
  rewrite (sublist_single i l 0) by (rewrite <- Zlength_correct; lia).
  simpl.
  reflexivity.
Qed.

Lemma second_largest_acc_sublist_step :
  forall (l : list Z) i n max1 max2,
    0 <= i < n ->
    n <= Zlength l ->
    second_largest_acc max1 max2 (sublist i n l) =
    if Z_gt_dec (Znth i l 0) max1 then
      second_largest_acc (Znth i l 0) max1 (sublist (i + 1) n l)
    else if Z_gt_dec (Znth i l 0) max2 then
      second_largest_acc max1 (Znth i l 0) (sublist (i + 1) n l)
    else
      second_largest_acc max1 max2 (sublist (i + 1) n l).
Proof.
  intros l i n max1 max2 Hi Hn.
  rewrite sublist_head_cons by assumption.
  simpl.
  reflexivity.
Qed.

Lemma second_largest_list_init_gt :
  forall (l : list Z),
    2 <= Zlength l ->
    Znth 1 l 0 > Znth 0 l 0 ->
    second_largest_acc (Znth 1 l 0) (Znth 0 l 0) (sublist 2 (Zlength l) l) =
    second_largest_list l.
Proof.
  intros l Hn Hgt.
  destruct l.
  - rewrite Zlength_nil in Hn. lia.
  - rename z into x1.
    rename l into l'.
    destruct l'.
    + rewrite Zlength_cons, Zlength_nil in Hn. lia.
    + match goal with
        | z : Z, l0 : list Z |- _ =>
            rename z into x2;
            rename l0 into xs
      end.
  simpl in Hgt.
  simpl.
  assert (sublist 2 (Zlength (x1 :: x2 :: xs)) (x1 :: x2 :: xs) = xs) as Hsub.
  {
    rewrite (sublist_cons2 2 (Zlength (x1 :: x2 :: xs)) x1 (x2 :: xs)).
    2: {
      split.
      - replace (Zlength (x1 :: x2 :: xs)) with (Zlength xs + 2) by (rewrite !Zlength_cons; lia).
        lia.
      - replace (Zlength (x1 :: x2 :: xs)) with (Zlength xs + 2) by (rewrite !Zlength_cons; lia).
        pose proof Zlength_nonneg xs.
        lia.
    }
    2: {
      lia.
    }
    replace (2 - 1) with 1 by lia.
    rewrite (sublist_cons2 1 (Zlength (x1 :: x2 :: xs) - 1) x2 xs).
    2: {
      split.
      - replace (Zlength (x1 :: x2 :: xs) - 1) with (Zlength xs + 1) by (rewrite !Zlength_cons; lia).
        lia.
      - replace (Zlength (x1 :: x2 :: xs) - 1) with (Zlength xs + 1) by (rewrite !Zlength_cons; lia).
        pose proof Zlength_nonneg xs.
        lia.
    }
    2: {
      rewrite !Zlength_cons. lia.
    }
    rewrite !Zlength_cons.
    simpl.
    replace (Z.succ (Z.succ (Zlength xs)) - 1 - 1) with (Zlength xs) by lia.
    apply sublist_self.
    reflexivity.
  }
  unfold second_largest_list.
  simpl.
  rewrite Hsub.
  destruct (Z_gt_dec x2 x1) as [Hcmp | Hcmp];
    [reflexivity | exfalso; apply Hcmp; exact Hgt].
Qed.

Lemma second_largest_list_init_le :
  forall (l : list Z),
    2 <= Zlength l ->
    Znth 1 l 0 <= Znth 0 l 0 ->
    second_largest_acc (Znth 0 l 0) (Znth 1 l 0) (sublist 2 (Zlength l) l) =
    second_largest_list l.
Proof.
  intros l Hn Hle.
  destruct l.
  - rewrite Zlength_nil in Hn. lia.
  - rename z into x1.
    rename l into l'.
    destruct l'.
    + rewrite Zlength_cons, Zlength_nil in Hn. lia.
    + match goal with
        | z : Z, l0 : list Z |- _ =>
            rename z into x2;
            rename l0 into xs
      end.
  simpl in Hle.
  simpl.
  assert (sublist 2 (Zlength (x1 :: x2 :: xs)) (x1 :: x2 :: xs) = xs) as Hsub.
  {
    rewrite (sublist_cons2 2 (Zlength (x1 :: x2 :: xs)) x1 (x2 :: xs)).
    2: {
      split.
      - replace (Zlength (x1 :: x2 :: xs)) with (Zlength xs + 2) by (rewrite !Zlength_cons; lia).
        lia.
      - replace (Zlength (x1 :: x2 :: xs)) with (Zlength xs + 2) by (rewrite !Zlength_cons; lia).
        pose proof Zlength_nonneg xs.
        lia.
    }
    2: {
      lia.
    }
    replace (2 - 1) with 1 by lia.
    rewrite (sublist_cons2 1 (Zlength (x1 :: x2 :: xs) - 1) x2 xs).
    2: {
      split.
      - replace (Zlength (x1 :: x2 :: xs) - 1) with (Zlength xs + 1) by (rewrite !Zlength_cons; lia).
        lia.
      - replace (Zlength (x1 :: x2 :: xs) - 1) with (Zlength xs + 1) by (rewrite !Zlength_cons; lia).
        pose proof Zlength_nonneg xs.
        lia.
    }
    2: {
      rewrite !Zlength_cons. lia.
    }
    rewrite !Zlength_cons.
    simpl.
    replace (Z.succ (Z.succ (Zlength xs)) - 1 - 1) with (Zlength xs) by lia.
    apply sublist_self.
    reflexivity.
  }
  unfold second_largest_list.
  simpl.
  rewrite Hsub.
  destruct (Z_gt_dec x2 x1) as [Hcmp | Hcmp];
    [exfalso; assert (~ x2 > x1) by lia; contradiction | reflexivity].
Qed.

Lemma proof_of_array_second_largest_entail_wit_1_1 : array_second_largest_entail_wit_1_1.
Proof.
  unfold array_second_largest_entail_wit_1_1.
  intros.
  left.
  entailer!.
  replace n_pre with (Zlength l) by lia.
  apply second_largest_list_init_gt; lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_1_2 : array_second_largest_entail_wit_1_2.
Proof.
  unfold array_second_largest_entail_wit_1_2.
  intros.
  right.
  entailer!.
  replace n_pre with (Zlength l) by lia.
  apply second_largest_list_init_le; lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_2_1 : array_second_largest_entail_wit_2_1.
Proof.
  unfold array_second_largest_entail_wit_2_1.
  intros.
  right.
  entailer!.
  rewrite <- H3.
  apply second_largest_acc_sublist_step; lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_2_2 : array_second_largest_entail_wit_2_2.
Proof.
  unfold array_second_largest_entail_wit_2_2.
  intros.
  left.
  entailer!.
  rewrite <- H3.
  apply second_largest_acc_sublist_step; lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_2_3 : array_second_largest_entail_wit_2_3.
Proof.
  unfold array_second_largest_entail_wit_2_3.
  intros.
  right.
  entailer!.
  rewrite <- H4.
  apply second_largest_acc_sublist_step; lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_2_4 : array_second_largest_entail_wit_2_4.
Proof.
  unfold array_second_largest_entail_wit_2_4.
  intros.
  left.
  entailer!.
  rewrite <- H4.
  apply second_largest_acc_sublist_step; lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_2_5 : array_second_largest_entail_wit_2_5.
Proof.
  unfold array_second_largest_entail_wit_2_5.
  intros.
  left.
  entailer!.
  rewrite <- H4.
  apply second_largest_acc_sublist_step; lia.
Qed.

Lemma proof_of_array_second_largest_entail_wit_2_6 : array_second_largest_entail_wit_2_6.
Proof.
  unfold array_second_largest_entail_wit_2_6.
  intros.
  right.
  entailer!.
  rewrite <- H4.
  apply second_largest_acc_sublist_step; lia.
Qed.

Lemma proof_of_array_second_largest_return_wit_1 : array_second_largest_return_wit_1.
Proof.
  unfold array_second_largest_return_wit_1.
  intros.
  entailer!.
  assert (i_2 = n_pre) by lia.
  subst i_2.
  replace (sublist n_pre n_pre l) with (@nil Z).
  - simpl in H2.
    exact H2.
  - rewrite sublist_same; lia.
Qed.

Lemma proof_of_array_second_largest_return_wit_2 : array_second_largest_return_wit_2.
Proof.
  unfold array_second_largest_return_wit_2.
  intros.
  entailer!.
  assert (i_2 = n_pre) by lia.
  subst i_2.
  replace (sublist n_pre n_pre l) with (@nil Z).
  - simpl in H2.
    exact H2.
  - rewrite sublist_same; lia.
Qed.
