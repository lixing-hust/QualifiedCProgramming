Load "../spec/42".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition map_incr (l : list Z) : list Z :=
  map (fun x => x + 1) l.

Definition list_incr_int_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> INT_MIN <= Znth i l 0 + 1 <= INT_MAX.

Lemma map_incr_Zlength : forall l,
  Zlength (map_incr l) = Zlength l.
Proof.
  intros.
  unfold map_incr.
  rewrite !Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma map_incr_sublist_snoc : forall l i,
  0 <= i < Zlength l ->
  map_incr (sublist 0 (i + 1) l) =
  map_incr (sublist 0 i l) ++ (Znth i l 0 + 1) :: nil.
Proof.
  intros.
  rewrite Zlength_correct in H.
  unfold map_incr.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single i l 0) by lia.
  rewrite map_app.
  reflexivity.
Qed.

Lemma problem_42_spec_map_incr : forall l,
  problem_42_spec l (map_incr l).
Proof.
  intros l.
  unfold problem_42_spec, map_incr.
  split.
  - rewrite length_map. reflexivity.
  - intros i Hi.
    rewrite length_map in Hi.
    destruct (nth_error l i) eqn:Hierr.
    + rewrite (@nth_error_nth Z (map (fun x : Z => x + 1) l) i (z + 1) 0%Z).
      * rewrite (@nth_error_nth Z l i z 0%Z) by exact Hierr.
        reflexivity.
      * rewrite nth_error_map. rewrite Hierr. reflexivity.
    + apply nth_error_None in Hierr. lia.
Qed.
