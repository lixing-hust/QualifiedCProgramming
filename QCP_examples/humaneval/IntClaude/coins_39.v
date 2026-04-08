Load "../spec/39".
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

(* Z-typed wrappers for QCP (C int -> Z) *)
Definition problem_39_pre_z (n : Z) : Prop :=
  problem_39_pre (Z.to_nat n).

Definition prime_fib_spec (n r : Z) : Prop :=
  (n = 1 /\ r = 2) \/
  (n = 2 /\ r = 3) \/
  (n = 3 /\ r = 5) \/
  (n = 4 /\ r = 13) \/
  (n = 5 /\ r = 89).

(* States at the start of the primality test (right after the Fibonacci update)
   when n <= 5. (count, f1, f2) where f1 is the current Fibonacci candidate
   and f2 is the next Fibonacci number. *)
Definition pf_state (count f1 f2 : Z) : Prop :=
  (count = 0 /\ f1 = 2 /\ f2 = 3) \/
  (count = 1 /\ f1 = 3 /\ f2 = 5) \/
  (count = 2 /\ f1 = 5 /\ f2 = 8) \/
  (count = 3 /\ f1 = 8 /\ f2 = 13) \/
  (count = 3 /\ f1 = 13 /\ f2 = 21) \/
  (count = 4 /\ f1 = 21 /\ f2 = 34) \/
  (count = 4 /\ f1 = 34 /\ f2 = 55) \/
  (count = 4 /\ f1 = 55 /\ f2 = 89) \/
  (count = 4 /\ f1 = 89 /\ f2 = 144).

Lemma pf_state_init : pf_state 0 2 3.
Proof.
  unfold pf_state.
  left.
  repeat split; lia.
Qed.

Lemma pf_state_sum_bound :
  forall count f1 f2,
    pf_state count f1 f2 ->
    0 <= f1 /\ 0 <= f2 /\ f1 + f2 <= 233.
Proof.
  intros count f1 f2 Hst.
  unfold pf_state in Hst.
  repeat (destruct Hst as [Hst | Hst]).
  all: destruct Hst as [? [? ?]]; subst; lia.
Qed.

Lemma pf_state_bounds :
  forall count f1 f2,
    pf_state count f1 f2 ->
    0 <= count /\ 2 <= f1 /\ f1 <= 89 /\ 3 <= f2 /\ f2 <= 144.
Proof.
  intros count f1 f2 Hst.
  unfold pf_state in Hst.
  repeat (destruct Hst as [Hst | Hst]).
  all: destruct Hst as [? [? ?]]; subst; lia.
Qed.

Lemma prime_candidate_mod_nonzero :
  forall f1 w,
    2 <= w ->
    w * w <= f1 ->
    (f1 = 2 \/ f1 = 3 \/ f1 = 5 \/ f1 = 13 \/ f1 = 89) ->
    Z.rem f1 w <> 0.
Proof.
  intros f1 w Hw Hsq Hprime.
  destruct Hprime as [-> | [-> | [-> | [-> | ->]]]].
  - lia.
  - lia.
  - assert (w = 2) by nia. subst w. simpl. discriminate.
  - assert (w = 2 \/ w = 3) by nia.
    destruct H as [-> | ->]; simpl; discriminate.
  - assert (w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9) by nia.
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      simpl; discriminate.
Qed.

Lemma pf_state_nonprime_step :
  forall count f1 f2,
    pf_state count f1 f2 ->
    f1 <> 2 ->
    f1 <> 3 ->
    f1 <> 5 ->
    f1 <> 13 ->
    f1 <> 89 ->
    pf_state count f2 (f1 + f2).
Proof.
  intros count f1 f2 Hst H2 H3 H5 H13 H89.
  unfold pf_state in *.
  destruct Hst as [[? [? ?]] | Hst].
  - subst. contradiction.
  - destruct Hst as [[? [? ?]] | Hst].
    + subst. contradiction.
    + destruct Hst as [[? [? ?]] | Hst].
      * subst. contradiction.
      * destruct Hst as [[? [? ?]] | Hst].
        -- subst. right. right. right. right. left. repeat split; lia.
        -- destruct Hst as [[? [? ?]] | Hst].
           ++ subst. contradiction.
           ++ destruct Hst as [[? [? ?]] | Hst].
              ** subst. right. right. right. right. right. right. left. repeat split; lia.
              ** destruct Hst as [[? [? ?]] | Hst].
                 --- subst. right. right. right. right. right. right. right. left. repeat split; lia.
                 --- destruct Hst as [[? [? ?]] | [? [? ?]]].
                     +++ subst. right. right. right. right. right. right. right. right. repeat split; lia.
                     +++ subst. contradiction.
Qed.

Lemma pf_state_prime_step :
  forall count f1 f2 n w,
    pf_state count f1 f2 ->
    2 <= w ->
    w * w > f1 ->
    (forall k : Z, 2 <= k /\ k < w -> Z.rem f1 k <> 0) ->
    count < n ->
    n <= 5 ->
    count + 1 <> n ->
    pf_state (count + 1) f2 (f1 + f2).
Proof.
  intros count f1 f2 n w Hst Hw Hexit Hnodiv Hcount Hn Hneq.
  unfold pf_state in Hst.
  destruct Hst as [[? [? ?]] | Hst].
  - subst. right. left. repeat split; lia.
  - destruct Hst as [[? [? ?]] | Hst].
    + subst. right. right. left. repeat split; lia.
    + destruct Hst as [[? [? ?]] | Hst].
      * subst. right. right. right. left. repeat split; lia.
      * destruct Hst as [[? [? ?]] | Hst].
        -- subst.
           assert (2 < w) by nia.
           assert (2 <= 2 /\ 2 < w) by nia.
           specialize (Hnodiv 2 H0).
           simpl in Hnodiv. contradiction.
        -- destruct Hst as [[? [? ?]] | Hst].
           ++ subst. right. right. right. right. right. left. repeat split; lia.
           ++ destruct Hst as [[? [? ?]] | Hst].
              ** subst.
                 assert (3 < w) by nia.
                 assert (2 <= 3 /\ 3 < w) by nia.
                 specialize (Hnodiv 3 H0).
                 simpl in Hnodiv. contradiction.
              ** destruct Hst as [[? [? ?]] | Hst].
                 --- subst.
                     assert (2 < w) by nia.
                     assert (2 <= 2 /\ 2 < w) by nia.
                     specialize (Hnodiv 2 H0).
                     simpl in Hnodiv. contradiction.
                 --- destruct Hst as [[? [? ?]] | [? [? ?]]].
                     +++ subst.
                         assert (5 < w) by nia.
                         assert (2 <= 5 /\ 5 < w) by nia.
                         specialize (Hnodiv 5 H0).
                         simpl in Hnodiv. contradiction.
                     +++ subst.
                         assert (n = 5) by lia.
                         subst n. contradiction.
Qed.

Lemma pf_state_prime_return :
  forall count f1 f2 n w,
    pf_state count f1 f2 ->
    2 <= w ->
    w * w > f1 ->
    (forall k : Z, 2 <= k /\ k < w -> Z.rem f1 k <> 0) ->
    count < n ->
    n <= 5 ->
    count + 1 = n ->
    prime_fib_spec n f1.
Proof.
  intros count f1 f2 n w Hst Hw Hexit Hnodiv Hcount Hn Heq.
  unfold pf_state in Hst.
  unfold prime_fib_spec.
  destruct Hst as [[? [? ?]] | Hst].
  - subst. left. repeat split; lia.
  - destruct Hst as [[? [? ?]] | Hst].
    + subst. right. left. repeat split; lia.
    + destruct Hst as [[? [? ?]] | Hst].
      * subst. right. right. left. repeat split; lia.
      * destruct Hst as [[? [? ?]] | Hst].
        -- subst.
           assert (2 < w) by nia.
           assert (2 <= 2 /\ 2 < w) by nia.
           specialize (Hnodiv 2 H0).
           simpl in Hnodiv. contradiction.
        -- destruct Hst as [[? [? ?]] | Hst].
           ++ subst. right. right. right. left. repeat split; lia.
           ++ destruct Hst as [[? [? ?]] | Hst].
              ** subst.
                 assert (3 < w) by nia.
                 assert (2 <= 3 /\ 3 < w) by nia.
                 specialize (Hnodiv 3 H0).
                 simpl in Hnodiv. contradiction.
              ** destruct Hst as [[? [? ?]] | Hst].
                 --- subst.
                     assert (2 < w) by nia.
                     assert (2 <= 2 /\ 2 < w) by nia.
                     specialize (Hnodiv 2 H0).
                     simpl in Hnodiv. contradiction.
                 --- destruct Hst as [[? [? ?]] | [? [? ?]]].
                     +++ subst.
                         assert (5 < w) by nia.
                         assert (2 <= 5 /\ 5 < w) by nia.
                         specialize (Hnodiv 5 H0).
                         simpl in Hnodiv. contradiction.
                     +++ subst. right. right. right. right. repeat split; lia.
Qed.
