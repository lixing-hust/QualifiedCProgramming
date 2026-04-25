Load "../spec/100".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Import ListNotations.

Definition list_Z_to_nat (l : list Z) : list nat :=
  map Z.to_nat l.

Definition problem_100_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_100_pre (Z.to_nat n).

Definition problem_100_spec_z (n : Z) (out : list Z) : Prop :=
  0 <= n /\ problem_100_spec (Z.to_nat n) (list_Z_to_nat out).

Definition pile_int_range (n : Z) : Prop :=
  forall i, 0 <= i < n -> INT_MIN <= n + 2 * i <= INT_MAX.

Definition make_pile (n : Z) : list Z :=
  map (fun i => n + 2 * i) (Zseq 0 (Z.to_nat n)).

Lemma make_pile_Zlength : forall n,
  0 <= n ->
  Zlength (make_pile n) = n.
Proof.
  intros n Hn.
  unfold make_pile.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.

Lemma make_pile_Znth : forall n i,
  0 <= i < n ->
  Znth i (make_pile n) 0 = n + 2 * i.
Proof.
  intros n i Hi.
  unfold make_pile.
  unfold Znth.
  eapply nth_error_nth.
  rewrite nth_error_map.
  rewrite nth_error_nth' with (d := 0%Z).
  - rewrite Zseq_nth by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - rewrite Zseq_length.
    lia.
Qed.

Lemma make_pile_sublist_snoc : forall n i,
  0 <= i < n ->
  sublist 0 (i + 1) (make_pile n) =
  sublist 0 i (make_pile n) ++ (n + 2 * i) :: nil.
Proof.
  intros n i Hi.
  pose proof (make_pile_Zlength n ltac:(lia)) as Hlen.
  assert (Hsplit_lo : 0 <= 0 <= i) by lia.
  assert (Hsplit_hi : i <= i + 1 <= Z.of_nat (length (make_pile n)))
    by (rewrite <- Zlength_correct; rewrite Hlen; lia).
  rewrite (sublist_split 0 (i + 1) i (make_pile n) Hsplit_lo Hsplit_hi).
  rewrite (sublist_single i (make_pile n) 0).
  - rewrite make_pile_Znth by lia.
    reflexivity.
  - rewrite <- Zlength_correct.
    rewrite Hlen.
    lia.
Qed.

Lemma problem_100_spec_z_make_pile : forall n,
  0 <= n ->
  problem_100_spec_z n (make_pile n).
Proof.
  intros n Hn.
  unfold problem_100_spec_z, problem_100_spec, list_Z_to_nat.
  split; [lia |].
  split.
  - unfold make_pile.
    rewrite length_map, length_map, Zseq_length.
    reflexivity.
  - intros i Hi.
    unfold list_Z_to_nat.
    rewrite (@nth_error_nth nat (map Z.to_nat (make_pile n)) i
             (Z.to_nat (n + 2 * Z.of_nat i)) 0%nat).
    + rewrite Z2Nat.inj_add by lia.
      rewrite Z2Nat.inj_mul by lia.
      replace (Z.to_nat (Z.of_nat i)) with i by lia.
      reflexivity.
    + unfold make_pile.
      rewrite nth_error_map.
      rewrite nth_error_map.
      rewrite nth_error_nth' with (d := 0%Z).
      * rewrite Zseq_nth by lia.
        reflexivity.
      * rewrite Zseq_length. lia.
Qed.
