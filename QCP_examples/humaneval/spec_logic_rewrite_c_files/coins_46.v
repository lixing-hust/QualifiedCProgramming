Load "../spec/46".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_46_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_46_pre (Z.to_nat n).

Definition problem_46_spec_z (n output : Z) : Prop :=
  0 <= n /\ 0 <= output /\ problem_46_spec (Z.to_nat n) (Z.to_nat output).

Definition fib4_z (n : Z) : Z :=
  Z.of_nat (fib4 (Z.to_nat n)).

Definition fib4_prefix_z (len : Z) : list Z :=
  map (fun i => fib4_z (Z.of_nat i)) (seq 0 (Z.to_nat len)).

Definition fib4_fill_len_z (n i : Z) : Z :=
  if Z.leb i n then i else if Z.ltb n 4 then 4 else n + 1.

Definition fib4_safe_z (n : Z) : Prop :=
  0 <= n <= 35 /\
  forall k, 0 <= k <= n -> 0 <= fib4_z k <= INT_MAX.

Lemma fib4_prefix_zlength : forall len,
  0 <= len ->
  Zlength (fib4_prefix_z len) = len.
Proof.
  intros len Hlen.
  unfold fib4_prefix_z.
  rewrite Zlength_correct, map_length, seq_length.
  lia.
Qed.

Lemma fib4_prefix_0_4 :
  fib4_prefix_z 4 = cons 0 (cons 0 (cons 2 (cons 0 nil))).
Proof.
  unfold fib4_prefix_z, fib4_z.
  cbn.
  reflexivity.
Qed.

Lemma seq_snoc_46 : forall start len,
  seq start (S len) = seq start len ++ [(start + len)%nat].
Proof.
  intros start len; revert start.
  induction len; intros start; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - change (S start :: seq (S (S start)) len) with
      (seq (S start) (S len)).
    rewrite IHlen.
    replace (start + S len)%nat with (S start + len)%nat by lia.
    reflexivity.
Qed.

Lemma fib4_prefix_z_snoc : forall len,
  0 <= len ->
  fib4_prefix_z (len + 1) = app (fib4_prefix_z len) (cons (fib4_z len) nil).
Proof.
  intros len Hlen.
  unfold fib4_prefix_z.
  replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
  rewrite seq_snoc_46.
  rewrite map_app.
  cbn [map].
  replace (0 + Z.to_nat len)%nat with (Z.to_nat len) by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Ltac split_or_cases :=
  repeat match goal with
         | H : _ \/ _ |- _ => destruct H as [H | H]
         end; subst.

Ltac small_int_cases_0_35 i :=
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/
          i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/
          i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/
          i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/
          i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/
          i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/
          i = 35) by lia;
  split_or_cases.

Ltac small_int_cases_4_35 i :=
  assert (i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/
          i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/
          i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/
          i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/
          i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/
          i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/
          i = 35) by lia;
  split_or_cases.

Definition fib4_step_state_46 (s : nat * nat * nat * nat) : nat * nat * nat * nat :=
  let '(a, b, c, d) := s in (b, c, d, (a + b + c + d)%nat).

Definition fib4_state_first_46 (n : nat) : nat :=
  let '(a, _, _, _) := Nat.iter n fib4_step_state_46 (0%nat, 0%nat, 2%nat, 0%nat) in a.

Lemma fib4_state_first_eq_46 : forall n,
  fib4 n = fib4_state_first_46 n.
Proof.
  intros n.
  reflexivity.
Qed.

Lemma fib4_state_first_step_46 : forall n,
  fib4_state_first_46 (n + 4)%nat =
    (fib4_state_first_46 n +
     fib4_state_first_46 (n + 1)%nat +
     fib4_state_first_46 (n + 2)%nat +
     fib4_state_first_46 (n + 3)%nat)%nat.
Proof.
  intro n.
  unfold fib4_state_first_46.
  replace (n + 4)%nat with (4 + n)%nat by lia.
  rewrite Nat.iter_add.
  replace (n + 1)%nat with (1 + n)%nat by lia.
  rewrite Nat.iter_add.
  replace (n + 2)%nat with (2 + n)%nat by lia.
  rewrite Nat.iter_add.
  replace (n + 3)%nat with (3 + n)%nat by lia.
  rewrite Nat.iter_add.
  destruct (Nat.iter n fib4_step_state_46 (0%nat, 0%nat, 2%nat, 0%nat)) as [[[a b] c] d].
  simpl.
  lia.
Qed.

Lemma fib4_nat_step_46 : forall n,
  fib4 (n + 4)%nat =
    (fib4 n + fib4 (n + 1)%nat + fib4 (n + 2)%nat + fib4 (n + 3)%nat)%nat.
Proof.
  intro n.
  repeat rewrite fib4_state_first_eq_46.
  apply fib4_state_first_step_46.
Qed.

Lemma fib4_z_step_46 : forall i,
  4 <= i ->
  fib4_z i = fib4_z (i - 1) + fib4_z (i - 2) + fib4_z (i - 3) + fib4_z (i - 4).
Proof.
  intros i Hi.
  unfold fib4_z.
  replace (Z.to_nat i) with (Z.to_nat (i - 4) + 4)%nat by lia.
  rewrite fib4_nat_step_46.
  replace (Z.to_nat (i - 4) + 1)%nat with (Z.to_nat (i - 3)) by lia.
  replace (Z.to_nat (i - 4) + 2)%nat with (Z.to_nat (i - 2)) by lia.
  replace (Z.to_nat (i - 4) + 3)%nat with (Z.to_nat (i - 1)) by lia.
  repeat rewrite Nat2Z.inj_add.
  lia.
Qed.

Lemma fib4_z_bound_46 : forall n k,
  fib4_safe_z n ->
  0 <= k <= n ->
  0 <= fib4_z k <= INT_MAX.
Proof.
  intros n k [_ Hsafe] Hk.
  apply Hsafe; exact Hk.
Qed.

Lemma fib4_safe_z_bound_sum_46 : forall n i,
  fib4_safe_z n ->
  4 <= i <= n ->
  0 <= fib4_z (i - 1) + fib4_z (i - 2) + fib4_z (i - 3) + fib4_z (i - 4) <= INT_MAX.
Proof.
  intros n i Hsafe Hi.
  rewrite <- fib4_z_step_46 by lia.
  destruct Hsafe as [_ Hsafe].
  apply Hsafe; lia.
Qed.

Lemma fib4_fill_len_initial_46 : forall n,
  0 <= n <= 35 ->
  fib4_fill_len_z n 4 = 4.
Proof.
  intros n Hn.
  unfold fib4_fill_len_z.
  destruct (Z.leb_spec 4 n); destruct (Z.ltb_spec n 4); lia.
Qed.

Lemma fib4_fill_len_loop_46 : forall n i,
  0 <= n <= 35 ->
  4 <= i <= n ->
  fib4_fill_len_z n i = i.
Proof.
  intros n i Hn Hi.
  unfold fib4_fill_len_z.
  destruct (Z.leb_spec i n); lia.
Qed.

Lemma fib4_fill_len_after_step_46 : forall n i,
  0 <= n <= 35 ->
  4 <= i <= n ->
  fib4_fill_len_z n (i + 1) = i + 1.
Proof.
  intros n i Hn Hi.
  unfold fib4_fill_len_z.
  destruct (Z.leb_spec (i + 1) n); destruct (Z.ltb_spec n 4); lia.
Qed.

Lemma fib4_fill_len_done_46 : forall n,
  0 <= n <= 35 ->
  fib4_fill_len_z n (n + 1) = if Z.ltb n 4 then 4 else n + 1.
Proof.
  intros n Hn.
  unfold fib4_fill_len_z.
  destruct (Z.leb_spec (n + 1) n); reflexivity || lia.
Qed.

Lemma fib4_fill_len_done_lt_46 : forall n,
  0 <= n <= 35 ->
  n < 4 ->
  fib4_fill_len_z n (n + 1) = 4.
Proof.
  intros n Hn Hlt.
  rewrite fib4_fill_len_done_46 by lia.
  destruct (Z.ltb_spec n 4); lia.
Qed.

Lemma fib4_fill_len_done_ge_46 : forall n,
  0 <= n <= 35 ->
  4 <= n ->
  fib4_fill_len_z n (n + 1) = n + 1.
Proof.
  intros n Hn Hge.
  rewrite fib4_fill_len_done_46 by lia.
  destruct (Z.ltb_spec n 4); lia.
Qed.

Lemma fib4_fill_len_done_ge_index_46 : forall n,
  0 <= n <= 35 ->
  n < fib4_fill_len_z n (n + 1).
Proof.
  intros n Hn.
  rewrite fib4_fill_len_done_46 by lia.
  destruct (Z.ltb_spec n 4); lia.
Qed.

Lemma fib4_prefix_read_46 : forall n,
  0 <= n <= 35 ->
  Znth n (fib4_prefix_z (fib4_fill_len_z n (n + 1))) 0 = fib4_z n.
Proof.
  intros n Hn.
  rewrite fib4_fill_len_done_46 by lia.
  unfold fib4_prefix_z.
  destruct (Z.ltb_spec n 4).
  - small_int_cases_0_35 n; try lia;
    vm_compute; reflexivity.
  - replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_snoc_46, map_app.
    replace (0 + Z.to_nat n)%nat with (Z.to_nat n) by lia.
    rewrite app_Znth2.
    + rewrite Zlength_correct, map_length, seq_length.
      replace (n - Z.of_nat (Z.to_nat n)) with 0 by lia.
      replace (Z.of_nat (Z.to_nat n)) with n by lia.
      cbn [map Znth].
      replace (fib4_z (Z.of_nat (Z.to_nat n))) with (fib4_z n) by (rewrite Z2Nat.id by lia; reflexivity).
      reflexivity.
    + rewrite Zlength_correct, map_length, seq_length.
      lia.
Qed.

Lemma fib4_prefix_znth_46 : forall len k,
  0 <= k < len ->
  Znth k (fib4_prefix_z len) 0 = fib4_z k.
Proof.
  intros len k Hk.
  unfold Znth, fib4_prefix_z.
  replace 0 with (fib4_z 0) by (unfold fib4_z, fib4; reflexivity).
  rewrite map_nth with (d := 0%nat).
  rewrite seq_nth by lia.
  replace (0 + Z.to_nat k)%nat with (Z.to_nat k) by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma problem_46_spec_z_from_fib4 : forall n,
  0 <= n ->
  problem_46_spec_z n (fib4_z n).
Proof.
  intros n Hn.
  unfold problem_46_spec_z, problem_46_spec, fib4_z.
  repeat split; try lia.
Qed.
