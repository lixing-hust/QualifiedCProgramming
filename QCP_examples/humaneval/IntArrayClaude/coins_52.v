Load "../spec/52".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.

Lemma Znth_In_range_52 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma In_Znth_exists_52 : forall (x : Z) l,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.

Lemma problem_52_spec_false_of_counter : forall l n t i,
  Zlength l = n ->
  0 <= i < n ->
  Znth i l 0 >= t ->
  problem_52_spec l t false.
Proof.
  intros l n t i Hlen Hi Hge.
  unfold problem_52_spec.
  split; intro H.
  - specialize (H (Znth i l 0)).
    assert (In (Znth i l 0) l) as Hin.
    { apply Znth_In_range_52. lia. }
    specialize (H Hin).
    lia.
  - discriminate H.
Qed.

Lemma problem_52_spec_true_of_all_below : forall l n t,
  Zlength l = n ->
  (forall k, 0 <= k < n -> Znth k l 0 < t) ->
  problem_52_spec l t true.
Proof.
  intros l n t Hlen Hall.
  unfold problem_52_spec.
  split; intro H.
  - reflexivity.
  - intros x Hin.
    destruct (In_Znth_exists_52 x l) as [i [Hi Hx]]; auto.
    rewrite <- Hx.
    apply Hall.
    lia.
Qed.
