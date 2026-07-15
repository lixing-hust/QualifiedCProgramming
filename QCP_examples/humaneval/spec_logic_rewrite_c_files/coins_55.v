Load "../spec/55".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_55_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_55_pre (Z.to_nat n).

Definition problem_55_spec_z (n output : Z) : Prop :=
  0 <= n /\ 0 <= output /\ problem_55_spec (Z.to_nat n) (Z.to_nat output).

Definition fib_z (n : Z) : Z :=
  Z.of_nat (fib (Z.to_nat n)).

Definition fib_prefix_z (len : Z) : list Z :=
  map (fun i => fib_z (Z.of_nat i)) (seq 0 (Z.to_nat len)).

Definition fib_fill_len_z (n i : Z) : Z :=
  if Z.leb i n then i else if Z.ltb n 2 then 2 else n + 1.

Definition fib_safe_z (n : Z) : Prop :=
  0 <= n <= 46 /\
  forall k, 0 <= k <= n -> 0 <= fib_z k <= INT_MAX.

Lemma fib_prefix_zlength : forall len,
  0 <= len ->
  Zlength (fib_prefix_z len) = len.
Proof.
  intros len Hlen.
  unfold fib_prefix_z.
  rewrite Zlength_correct, map_length, seq_length.
  lia.
Qed.

Lemma fib_prefix_0_2 :
  fib_prefix_z 2 = cons 0 (cons 1 nil).
Proof.
  unfold fib_prefix_z, fib_z.
  cbn.
  reflexivity.
Qed.

Lemma seq_snoc_55 : forall start len,
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

Lemma fib_prefix_z_snoc : forall len,
  0 <= len ->
  fib_prefix_z (len + 1) = app (fib_prefix_z len) (cons (fib_z len) nil).
Proof.
  intros len Hlen.
  unfold fib_prefix_z.
  replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
  rewrite seq_snoc_55.
  rewrite map_app.
  cbn [map].
  replace (0 + Z.to_nat len)%nat with (Z.to_nat len) by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Definition fib_state_first_55 (n : nat) : nat :=
  let '(a, _) :=
    Nat.iter n (fun p : nat * nat => (snd p, (fst p + snd p)%nat)) (0%nat, 1%nat) in
  a.

Lemma fib_state_first_eq_55 : forall n,
  fib n = fib_state_first_55 n.
Proof.
  intros n.
  reflexivity.
Qed.

Lemma fib_state_first_step_55 : forall n,
  fib_state_first_55 (n + 2)%nat =
    (fib_state_first_55 n + fib_state_first_55 (n + 1)%nat)%nat.
Proof.
  intro n.
  unfold fib_state_first_55.
  replace (n + 2)%nat with (2 + n)%nat by lia.
  rewrite Nat.iter_add.
  replace (n + 1)%nat with (1 + n)%nat by lia.
  rewrite Nat.iter_add.
  destruct (Nat.iter n (fun p : nat * nat => (snd p, (fst p + snd p)%nat)) (0%nat, 1%nat)) as [a b].
  simpl.
  lia.
Qed.

Lemma fib_nat_step_55 : forall n,
  fib (n + 2)%nat = (fib n + fib (n + 1)%nat)%nat.
Proof.
  intro n.
  repeat rewrite fib_state_first_eq_55.
  apply fib_state_first_step_55.
Qed.

Lemma fib_z_step_55 : forall i,
  2 <= i ->
  fib_z i = fib_z (i - 1) + fib_z (i - 2).
Proof.
  intros i Hi.
  unfold fib_z.
  replace (Z.to_nat i) with (Z.to_nat (i - 2) + 2)%nat by lia.
  rewrite fib_nat_step_55.
  replace (Z.to_nat (i - 2) + 1)%nat with (Z.to_nat (i - 1)) by lia.
  repeat rewrite Nat2Z.inj_add.
  lia.
Qed.

Lemma fib_z_bound_55 : forall n k,
  fib_safe_z n ->
  0 <= k <= n ->
  0 <= fib_z k <= INT_MAX.
Proof.
  intros n k [_ Hsafe] Hk.
  apply Hsafe; exact Hk.
Qed.

Lemma fib_safe_z_bound_sum_55 : forall n i,
  fib_safe_z n ->
  2 <= i <= n ->
  0 <= fib_z (i - 1) + fib_z (i - 2) <= INT_MAX.
Proof.
  intros n i Hsafe Hi.
  rewrite <- fib_z_step_55 by lia.
  destruct Hsafe as [_ Hsafe].
  apply Hsafe; lia.
Qed.

Lemma fib_fill_len_initial_55 : forall n,
  0 <= n <= 46 ->
  fib_fill_len_z n 2 = 2.
Proof.
  intros n Hn.
  unfold fib_fill_len_z.
  destruct (Z.leb_spec 2 n); destruct (Z.ltb_spec n 2); lia.
Qed.

Lemma fib_fill_len_loop_55 : forall n i,
  0 <= n <= 46 ->
  2 <= i <= n ->
  fib_fill_len_z n i = i.
Proof.
  intros n i Hn Hi.
  unfold fib_fill_len_z.
  destruct (Z.leb_spec i n); lia.
Qed.

Lemma fib_fill_len_after_step_55 : forall n i,
  0 <= n <= 46 ->
  2 <= i <= n ->
  fib_fill_len_z n (i + 1) = i + 1.
Proof.
  intros n i Hn Hi.
  unfold fib_fill_len_z.
  destruct (Z.leb_spec (i + 1) n); destruct (Z.ltb_spec n 2); lia.
Qed.

Lemma fib_fill_len_done_55 : forall n,
  0 <= n <= 46 ->
  fib_fill_len_z n (n + 1) = if Z.ltb n 2 then 2 else n + 1.
Proof.
  intros n Hn.
  unfold fib_fill_len_z.
  destruct (Z.leb_spec (n + 1) n); reflexivity || lia.
Qed.

Lemma fib_fill_len_done_lt_55 : forall n,
  0 <= n <= 46 ->
  n < 2 ->
  fib_fill_len_z n (n + 1) = 2.
Proof.
  intros n Hn Hlt.
  rewrite fib_fill_len_done_55 by lia.
  destruct (Z.ltb_spec n 2); lia.
Qed.

Lemma fib_fill_len_done_ge_55 : forall n,
  0 <= n <= 46 ->
  2 <= n ->
  fib_fill_len_z n (n + 1) = n + 1.
Proof.
  intros n Hn Hge.
  rewrite fib_fill_len_done_55 by lia.
  destruct (Z.ltb_spec n 2); lia.
Qed.

Lemma fib_fill_len_done_ge_index_55 : forall n,
  0 <= n <= 46 ->
  n < fib_fill_len_z n (n + 1).
Proof.
  intros n Hn.
  rewrite fib_fill_len_done_55 by lia.
  destruct (Z.ltb_spec n 2); lia.
Qed.

Lemma fib_prefix_read_55 : forall n,
  0 <= n <= 46 ->
  Znth n (fib_prefix_z (fib_fill_len_z n (n + 1))) 0 = fib_z n.
Proof.
  intros n Hn.
  rewrite fib_fill_len_done_55 by lia.
  unfold fib_prefix_z.
  destruct (Z.ltb_spec n 2).
  - assert (Hsmall : n = 0 \/ n = 1) by lia.
    destruct Hsmall as [-> | ->]; vm_compute; reflexivity.
  - replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_snoc_55, map_app.
    replace (0 + Z.to_nat n)%nat with (Z.to_nat n) by lia.
    rewrite app_Znth2.
    + rewrite Zlength_correct, map_length, seq_length.
      replace (n - Z.of_nat (Z.to_nat n)) with 0 by lia.
      replace (Z.of_nat (Z.to_nat n)) with n by lia.
      cbn [map Znth].
      replace (fib_z (Z.of_nat (Z.to_nat n))) with (fib_z n) by (rewrite Z2Nat.id by lia; reflexivity).
      reflexivity.
    + rewrite Zlength_correct, map_length, seq_length.
      lia.
Qed.

Lemma fib_prefix_znth_55 : forall len k,
  0 <= k < len ->
  Znth k (fib_prefix_z len) 0 = fib_z k.
Proof.
  intros len k Hk.
  unfold Znth, fib_prefix_z.
  replace 0 with (fib_z 0) by (unfold fib_z, fib; reflexivity).
  rewrite map_nth with (d := 0%nat).
  rewrite seq_nth by lia.
  replace (0 + Z.to_nat k)%nat with (Z.to_nat k) by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma problem_55_spec_z_from_fib : forall n,
  0 <= n ->
  problem_55_spec_z n (fib_z n).
Proof.
  intros n Hn.
  unfold problem_55_spec_z, problem_55_spec, fib_z.
  repeat split; try lia.
Qed.
