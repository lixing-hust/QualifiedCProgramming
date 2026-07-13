Load "../spec/130".

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_130_pre_z (n : Z) : Prop :=
  problem_130_pre (Z.to_nat n).

Definition problem_130_spec_z (n : Z) (out : list Z) : Prop :=
  problem_130_spec (Z.to_nat n) (map Z.to_nat out).

Definition tri_z_130 (n : Z) : Z :=
  Z.of_nat (tri (Z.to_nat n)).

Definition z_indices_130 (len : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat len)).

Definition tri_prefix_z_130 (len : Z) : list Z :=
  map tri_z_130 (z_indices_130 len).

Definition tri_safe_z_130 (n : Z) : Prop :=
  0 <= n <= 1000 /\
  forall i,
    0 <= i <= n ->
    0 <= tri_z_130 i <= INT_MAX /\
    (2 <= i ->
     (Z.even i = true ->
      tri_z_130 i = 1 + i / 2) /\
     (Z.even i = false ->
      tri_z_130 i =
        tri_z_130 (i - 1) + tri_z_130 (i - 2) + 1 + (i + 1) / 2) /\
     0 <= tri_z_130 (i - 1) + tri_z_130 (i - 2) + 1 + (i + 1) / 2 <= INT_MAX).

Lemma z_indices_130_snoc : forall len,
  0 <= len ->
  z_indices_130 (len + 1) = z_indices_130 len ++ [len].
Proof.
  intros len Hlen.
  unfold z_indices_130.
  rewrite Z2Nat.inj_add by lia.
  replace (Z.to_nat 1) with 1%nat by reflexivity.
  rewrite Nat.add_1_r, seq_S, map_app.
  simpl.
  replace (Z.of_nat (Z.to_nat len)) with len by lia.
  reflexivity.
Qed.

Lemma tri_prefix_z_130_snoc : forall len,
  0 <= len ->
  tri_prefix_z_130 (len + 1) =
    tri_prefix_z_130 len ++ [tri_z_130 len].
Proof.
  intros len Hlen.
  unfold tri_prefix_z_130.
  rewrite z_indices_130_snoc by exact Hlen.
  rewrite map_app.
  reflexivity.
Qed.

Lemma tri_prefix_z_130_1 :
  tri_prefix_z_130 1 = [1].
Proof. reflexivity. Qed.

Lemma tri_prefix_z_130_2 :
  tri_prefix_z_130 2 = [1; 3].
Proof. reflexivity. Qed.

Lemma tri_z_130_0 :
  tri_z_130 0 = 1.
Proof. reflexivity. Qed.

Lemma tri_z_130_1 :
  tri_z_130 1 = 3.
Proof. reflexivity. Qed.

Lemma tri_safe_z_130_step_value : forall n i,
  tri_safe_z_130 n ->
  0 <= i <= n ->
  0 <= tri_z_130 i <= INT_MAX.
Proof.
  intros n i [_ Hsafe] Hi.
  exact (proj1 (Hsafe i Hi)).
Qed.

Lemma tri_safe_z_130_even_step : forall n i,
  tri_safe_z_130 n ->
  2 <= i <= n ->
  Z.even i = true ->
  tri_z_130 i = 1 + i / 2.
Proof.
  intros n i [_ Hsafe] Hi Heven.
  destruct (Hsafe i ltac:(lia)) as [_ Hstep].
  exact (proj1 (Hstep ltac:(lia)) Heven).
Qed.

Lemma tri_safe_z_130_odd_step : forall n i,
  tri_safe_z_130 n ->
  2 <= i <= n ->
  Z.even i = false ->
  tri_z_130 i =
    tri_z_130 (i - 1) + tri_z_130 (i - 2) + 1 + (i + 1) / 2.
Proof.
  intros n i [_ Hsafe] Hi Hodd.
  destruct (Hsafe i ltac:(lia)) as [_ Hstep].
  exact (proj1 (proj2 (Hstep ltac:(lia))) Hodd).
Qed.

Lemma tri_safe_z_130_odd_sum_range : forall n i,
  tri_safe_z_130 n ->
  2 <= i <= n ->
  0 <= tri_z_130 (i - 1) + tri_z_130 (i - 2) + 1 + (i + 1) / 2 <= INT_MAX.
Proof.
  intros n i [_ Hsafe] Hi.
  destruct (Hsafe i ltac:(lia)) as [_ Hstep].
  exact (proj2 (proj2 (Hstep ltac:(lia)))).
Qed.

Lemma z_even_true_of_rem0_130 : forall i,
  0 <= i ->
  Z.rem i 2 = 0 ->
  Z.even i = true.
Proof.
  intros i Hi Hrem.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  pose proof (Zmod_odd i) as Hodd.
  rewrite Hrem in Hodd.
  destruct (Z.odd i) eqn:Hob; [discriminate|].
  rewrite Zodd_even_bool in Hob.
  destruct (Z.even i); reflexivity || discriminate.
Qed.

Lemma z_even_false_of_rem_nonzero_130 : forall i,
  0 <= i ->
  Z.rem i 2 <> 0 ->
  Z.even i = false.
Proof.
  intros i Hi Hrem.
  assert (Hmod_ne : i mod 2 <> 0).
  {
    rewrite <- Z.rem_mod_nonneg by lia.
    exact Hrem.
  }
  pose proof (Z.mod_pos_bound i 2 ltac:(lia)) as Hbound.
  assert (Hmod : i mod 2 = 1) by lia.
  pose proof (Zmod_odd i) as Hodd.
  rewrite Hmod in Hodd.
  destruct (Z.odd i) eqn:Hob; [|discriminate].
  rewrite Zodd_even_bool in Hob.
  destruct (Z.even i); discriminate || reflexivity.
Qed.

Lemma Znth_map_130 : forall {A B : Type} (f : A -> B) (l : list A) i d d',
  0 <= i < Zlength l ->
  Znth i (map f l) d' = f (Znth i l d).
Proof.
  intros A B f l i d d' Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f d)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - rewrite (@map_nth A B f l d (Z.to_nat i)).
    reflexivity.
Qed.

Lemma Znth_seq_130 : forall start len i d,
  0 <= i < Z.of_nat len ->
  Znth i (seq start len) d = (start + Z.to_nat i)%nat.
Proof.
  intros start len i d Hi.
  unfold Znth.
  rewrite nth_indep with (d' := (start + Z.to_nat i)%nat).
  - apply seq_nth. lia.
  - rewrite seq_length. lia.
Qed.

Lemma tri_prefix_z_130_nth : forall len i,
  0 <= i ->
  i < len ->
  Znth i (tri_prefix_z_130 len) 0 = tri_z_130 i.
Proof.
  intros len i Hi Hlt.
  unfold tri_prefix_z_130, z_indices_130.
  rewrite (Znth_map_130 tri_z_130 (map Z.of_nat (seq 0 (Z.to_nat len))) i 0 0)
    by (repeat rewrite Zlength_correct; repeat rewrite map_length; rewrite seq_length; lia).
  rewrite (Znth_map_130 Z.of_nat (seq 0 (Z.to_nat len)) i 0%nat 0)
    by (rewrite Zlength_correct, seq_length; lia).
  rewrite Znth_seq_130 by lia.
  replace (Z.of_nat (0 + Z.to_nat i)%nat) with i by lia.
  reflexivity.
Qed.

Lemma tri_prefix_z_130_length : forall len,
  0 <= len ->
  Zlength (tri_prefix_z_130 len) = len.
Proof.
  intros len Hlen.
  unfold tri_prefix_z_130, z_indices_130.
  repeat rewrite Zlength_correct.
  repeat rewrite map_length.
  rewrite seq_length.
  lia.
Qed.

Lemma problem_130_spec_z_of_prefix : forall n,
  0 <= n ->
  problem_130_spec_z n (tri_prefix_z_130 (n + 1)).
Proof.
  intros n Hn.
  unfold problem_130_spec_z, problem_130_spec.
  split.
  - rewrite map_length.
    unfold tri_prefix_z_130, z_indices_130.
    rewrite map_length, map_length, seq_length.
    lia.
  - intros i Hi.
    unfold tri_prefix_z_130, z_indices_130.
    change
      (nth i
         (map Z.to_nat
            (map tri_z_130 (map Z.of_nat (seq 0 (Z.to_nat (n + 1))))))
         0%nat)
      with
      (nth i
         (map Z.to_nat
            (map tri_z_130 (map Z.of_nat (seq 0 (Z.to_nat (n + 1))))))
         (Z.to_nat 0%Z)).
    rewrite (@map_nth Z nat Z.to_nat
               (map tri_z_130 (map Z.of_nat (seq 0 (Z.to_nat (n + 1)))))
               0%Z i).
    rewrite (@nth_indep Z
               (map tri_z_130 (map Z.of_nat (seq 0 (Z.to_nat (n + 1)))))
               i 0%Z (tri_z_130 0%Z)).
    2:{ rewrite map_length, map_length, seq_length. lia. }
    rewrite (@map_nth Z Z tri_z_130
               (map Z.of_nat (seq 0 (Z.to_nat (n + 1))))
               0%Z i).
    change
      (nth i (map Z.of_nat (seq 0 (Z.to_nat (n + 1)))) 0%Z)
      with
      (nth i (map Z.of_nat (seq 0 (Z.to_nat (n + 1)))) (Z.of_nat 0%nat)).
    rewrite (@map_nth nat Z Z.of_nat
               (seq 0 (Z.to_nat (n + 1)))
               0%nat i).
    rewrite seq_nth by lia.
    unfold tri_z_130.
    replace (Z.to_nat (Z.of_nat (0 + i))) with i by lia.
    lia.
Qed.
