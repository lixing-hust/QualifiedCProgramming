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
From SimpleC.EE.CAV.verify_20260420_122040_array_count_transitions Require Import array_count_transitions_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import array_count_transitions.
Local Open Scope sac.

Lemma array_count_transitions_from_bounds : forall prev xs,
  0 <= array_count_transitions_from prev xs <= Zlength xs.
Proof.
  intros prev xs.
  revert prev.
  induction xs; intros prev; simpl.
  - rewrite Zlength_nil. lia.
  - specialize (IHxs a).
    rewrite Zlength_cons.
    destruct (Z.eq_dec a prev); lia.
Qed.

Lemma array_count_transitions_spec_bounds : forall xs,
  0 <= array_count_transitions_spec xs /\
  array_count_transitions_spec xs <= Z.max 0 (Zlength xs - 1).
Proof.
  intros xs.
  destruct xs.
  - simpl. lia.
  - simpl.
    pose proof (array_count_transitions_from_bounds z xs) as H.
    rewrite Zlength_cons.
    lia.
Qed.

Lemma last_nonempty_default_irrel : forall (x: Z) (xs: list Z) (d1 d2: Z),
  last (x :: xs) d1 = last (x :: xs) d2.
Proof.
  intros x xs.
  revert x.
  induction xs; intros x d1 d2; simpl.
  - reflexivity.
  - apply IHxs.
Qed.

Lemma array_count_transitions_from_app_one : forall prev xs x,
  array_count_transitions_from prev (xs ++ cons x nil) =
  array_count_transitions_from prev xs +
  (if Z.eq_dec x (last xs prev) then 0 else 1).
Proof.
  intros prev xs.
  revert prev.
  induction xs; intros prev x; simpl.
  - destruct (Z.eq_dec x prev); lia.
  - rewrite IHxs.
    destruct xs; simpl.
    + destruct (Z.eq_dec a prev); destruct (Z.eq_dec x a); lia.
    + assert (Hlast:
        match xs with
        | nil => z
        | _ :: _ => last xs a
        end =
        match xs with
        | nil => z
        | _ :: _ => last xs prev
        end).
      {
        destruct xs; simpl.
        - reflexivity.
        - apply last_nonempty_default_irrel.
      }
      rewrite Hlast.
      repeat match goal with
      | |- context [Z.eq_dec ?u ?v] => destruct (Z.eq_dec u v)
      end; lia.
Qed.

Lemma array_count_transitions_spec_app_one : forall xs x d,
  0 < Zlength xs ->
  array_count_transitions_spec (xs ++ cons x nil) =
  array_count_transitions_spec xs +
  (if Z.eq_dec x (last xs d) then 0 else 1).
Proof.
  intros xs x d Hlen.
  destruct xs.
  - unfold Zlength in Hlen. simpl in Hlen. lia.
  - simpl.
    rewrite array_count_transitions_from_app_one.
    destruct xs; simpl.
    + destruct (Z.eq_dec x z); lia.
    + assert (Hlast:
        match xs with
        | nil => z0
        | _ :: _ => last xs z
        end =
        match xs with
        | nil => z0
        | _ :: _ => last xs d
        end).
      {
        destruct xs; simpl.
        - reflexivity.
        - apply last_nonempty_default_irrel.
      }
      rewrite Hlast.
      reflexivity.
Qed.

Lemma last_sublist_prefix : forall (l: list Z) i (d: Z),
  1 <= i <= Zlength l ->
  last (sublist 0 i l) d = Znth (i - 1) l d.
Proof.
  intros l i d Hi.
  rewrite Zlength_correct in Hi.
  rewrite (sublist_split 0 i (i - 1) l).
  2: lia.
  2: lia.
  replace (sublist (i - 1) i l) with (sublist (i - 1) ((i - 1) + 1) l) by (f_equal; lia).
  rewrite (sublist_single (i - 1) l d) by lia.
  rewrite last_last.
  reflexivity.
Qed.

Lemma array_count_transitions_spec_sublist_extend : forall l i,
  1 <= i < Zlength l ->
  array_count_transitions_spec (sublist 0 (i + 1) l) =
  array_count_transitions_spec (sublist 0 i l) +
  (if Z.eq_dec (Znth i l 0) (Znth (i - 1) l 0) then 0 else 1).
Proof.
  intros l i Hi.
  assert (Hi_len: 1 <= i < Z.of_nat (Datatypes.length l)).
  { rewrite <- Zlength_correct. lia. }
  rewrite (sublist_split 0 (i + 1) i l).
  2: lia.
  2: lia.
  rewrite (sublist_single i l 0) by lia.
  rewrite array_count_transitions_spec_app_one with (d := 0).
  - rewrite last_sublist_prefix by lia.
    reflexivity.
  - rewrite Zlength_sublist by lia.
    lia.
Qed.

Lemma sublist_0_over_length : forall {A: Type} (l: list A) i,
  Zlength l <= i ->
  sublist 0 i l = l.
Proof.
  intros A l i Hi.
  unfold sublist.
  assert (Hnat: (Datatypes.length l <= Z.to_nat i)%nat).
  { rewrite Zlength_correct in Hi. lia. }
  rewrite firstn_all2 by exact Hnat.
  simpl.
  reflexivity.
Qed.

Lemma array_count_transitions_spec_sublist_0_1_zero : forall l,
  array_count_transitions_spec (sublist 0 1 l) = 0.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - replace 1 with (0 + 1) by lia.
    rewrite (sublist_single 0 (z :: l) 0) by (simpl; lia).
    simpl. reflexivity.
Qed.

Lemma proof_of_array_count_transitions_safety_wit_5 : array_count_transitions_safety_wit_5.
Proof.
  pre_process.
  sep_apply store_int_range.
  sep_apply store_int_range.
  entailer!.
  all:
  pose proof (array_count_transitions_spec_bounds (sublist 0 i l)) as Hspec.
  all:
  rewrite Zlength_sublist in Hspec by lia.
  all:
  replace (Z.max 0 (i - 0 - 1)) with (i - 1) in Hspec by lia.
  all:
  change Int.max_signed with 2147483647 in *.
  all:
  change Int.min_signed with (-2147483648) in *.
  all:
  destruct Hspec as [Hspec_lo Hspec_hi].
  all:
  subst cnt.
  all:
  lia.
Qed.

Lemma proof_of_array_count_transitions_entail_wit_1 : array_count_transitions_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  rewrite array_count_transitions_spec_sublist_0_1_zero.
  reflexivity.
Qed.

Lemma proof_of_array_count_transitions_entail_wit_2_1 : array_count_transitions_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  rewrite array_count_transitions_spec_sublist_extend by lia.
  destruct (Z.eq_dec (Znth i l 0) (Znth (i - 1) l 0)); lia.
Qed.

Lemma proof_of_array_count_transitions_entail_wit_2_2 : array_count_transitions_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  rewrite array_count_transitions_spec_sublist_extend by lia.
  destruct (Z.eq_dec (Znth i l 0) (Znth (i - 1) l 0)); lia.
Qed.

Lemma proof_of_array_count_transitions_return_wit_1 : array_count_transitions_return_wit_1.
Proof.
  pre_process.
  entailer!.
  rewrite sublist_0_over_length in H2 by lia.
  exact H2.
Qed.
