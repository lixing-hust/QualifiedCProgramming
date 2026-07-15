Load "../spec/63".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_63_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_63_pre (Z.to_nat n).

Definition problem_63_spec_z (n output : Z) : Prop :=
  0 <= n /\ 0 <= output /\ problem_63_spec (Z.to_nat n) (Z.to_nat output).

Definition fibfib_z (n : Z) : Z :=
  Z.of_nat (fibfib (Z.to_nat n)).

Definition fibfib_prefix_z (len : Z) : list Z :=
  map (fun i => fibfib_z (Z.of_nat i)) (seq 0 (Z.to_nat len)).

Definition fibfib_fill_len_z (n i : Z) : Z :=
  if Z.leb i n then i else if Z.ltb n 3 then 3 else n + 1.

Definition fibfib_safe_z (n : Z) : Prop :=
  0 <= n <= 38 /\
  forall k, 0 <= k <= n -> 0 <= fibfib_z k <= INT_MAX.

Lemma fibfib_prefix_zlength : forall len,
  0 <= len ->
  Zlength (fibfib_prefix_z len) = len.
Proof.
  intros len Hlen.
  unfold fibfib_prefix_z.
  rewrite Zlength_correct, map_length, seq_length.
  lia.
Qed.

Lemma fibfib_prefix_0_3 :
  fibfib_prefix_z 3 = cons 0 (cons 0 (cons 1 nil)).
Proof.
  unfold fibfib_prefix_z, fibfib_z.
  cbn.
  reflexivity.
Qed.

Lemma seq_snoc_63 : forall start len,
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

Lemma fibfib_prefix_z_snoc : forall len,
  0 <= len ->
  fibfib_prefix_z (len + 1) = app (fibfib_prefix_z len) (cons (fibfib_z len) nil).
Proof.
  intros len Hlen.
  unfold fibfib_prefix_z.
  replace (Z.to_nat (len + 1)) with (S (Z.to_nat len)) by lia.
  rewrite seq_snoc_63.
  rewrite map_app.
  cbn [map].
  replace (0 + Z.to_nat len)%nat with (Z.to_nat len) by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Definition fibfib_step_state_63 (s : nat * nat * nat) : nat * nat * nat :=
  let '(a, b, c) := s in (b, c, (a + b + c)%nat).

Definition fibfib_state_first_63 (n : nat) : nat :=
  let '(a, _, _) := Nat.iter n fibfib_step_state_63 (0%nat, 0%nat, 1%nat) in a.

Lemma fibfib_state_first_eq_63 : forall n,
  fibfib n = fibfib_state_first_63 n.
Proof.
  intros n.
  reflexivity.
Qed.

Lemma fibfib_state_first_step_63 : forall n,
  fibfib_state_first_63 (n + 3)%nat =
    (fibfib_state_first_63 n +
     fibfib_state_first_63 (n + 1)%nat +
     fibfib_state_first_63 (n + 2)%nat)%nat.
Proof.
  intro n.
  unfold fibfib_state_first_63.
  replace (n + 3)%nat with (3 + n)%nat by lia.
  rewrite Nat.iter_add.
  replace (n + 1)%nat with (1 + n)%nat by lia.
  rewrite Nat.iter_add.
  replace (n + 2)%nat with (2 + n)%nat by lia.
  rewrite Nat.iter_add.
  destruct (Nat.iter n fibfib_step_state_63 (0%nat, 0%nat, 1%nat)) as [[a b] c].
  simpl.
  lia.
Qed.

Lemma fibfib_nat_step_63 : forall n,
  fibfib (n + 3)%nat =
    (fibfib n + fibfib (n + 1)%nat + fibfib (n + 2)%nat)%nat.
Proof.
  intro n.
  repeat rewrite fibfib_state_first_eq_63.
  apply fibfib_state_first_step_63.
Qed.

Lemma fibfib_z_step_63 : forall i,
  3 <= i ->
  fibfib_z i = fibfib_z (i - 1) + fibfib_z (i - 2) + fibfib_z (i - 3).
Proof.
  intros i Hi.
  unfold fibfib_z.
  replace (Z.to_nat i) with (Z.to_nat (i - 3) + 3)%nat by lia.
  rewrite fibfib_nat_step_63.
  replace (Z.to_nat (i - 3) + 1)%nat with (Z.to_nat (i - 2)) by lia.
  replace (Z.to_nat (i - 3) + 2)%nat with (Z.to_nat (i - 1)) by lia.
  repeat rewrite Nat2Z.inj_add.
  lia.
Qed.

Lemma fibfib_z_bound_63 : forall n k,
  fibfib_safe_z n ->
  0 <= k <= n ->
  0 <= fibfib_z k <= INT_MAX.
Proof.
  intros n k [_ Hsafe] Hk.
  apply Hsafe; exact Hk.
Qed.

Lemma fibfib_safe_z_bound_sum_63 : forall n i,
  fibfib_safe_z n ->
  3 <= i <= n ->
  0 <= fibfib_z (i - 1) + fibfib_z (i - 2) + fibfib_z (i - 3) <= INT_MAX.
Proof.
  intros n i Hsafe Hi.
  rewrite <- fibfib_z_step_63 by lia.
  destruct Hsafe as [_ Hsafe].
  apply Hsafe; lia.
Qed.

Lemma fibfib_safe_z_bound_pair_sum_63 : forall n i,
  fibfib_safe_z n ->
  3 <= i <= n ->
  0 <= fibfib_z (i - 1) + fibfib_z (i - 2) <= INT_MAX.
Proof.
  intros n i Hsafe Hi.
  assert (0 <= fibfib_z (i - 1)) by (eapply fibfib_z_bound_63; eauto; lia).
  assert (0 <= fibfib_z (i - 2)) by (eapply fibfib_z_bound_63; eauto; lia).
  assert (0 <= fibfib_z (i - 3)) by (eapply fibfib_z_bound_63; eauto; lia).
  assert (fibfib_z (i - 1) + fibfib_z (i - 2) + fibfib_z (i - 3) <= INT_MAX)
    by (pose proof (fibfib_safe_z_bound_sum_63 n i Hsafe Hi); lia).
  lia.
Qed.

Lemma fibfib_fill_len_initial_63 : forall n,
  0 <= n <= 38 ->
  fibfib_fill_len_z n 3 = 3.
Proof.
  intros n Hn.
  unfold fibfib_fill_len_z.
  destruct (Z.leb_spec 3 n); destruct (Z.ltb_spec n 3); lia.
Qed.

Lemma fibfib_fill_len_loop_63 : forall n i,
  0 <= n <= 38 ->
  3 <= i <= n ->
  fibfib_fill_len_z n i = i.
Proof.
  intros n i Hn Hi.
  unfold fibfib_fill_len_z.
  destruct (Z.leb_spec i n); lia.
Qed.

Lemma fibfib_fill_len_after_step_63 : forall n i,
  0 <= n <= 38 ->
  3 <= i <= n ->
  fibfib_fill_len_z n (i + 1) = i + 1.
Proof.
  intros n i Hn Hi.
  unfold fibfib_fill_len_z.
  destruct (Z.leb_spec (i + 1) n); destruct (Z.ltb_spec n 3); lia.
Qed.

Lemma fibfib_fill_len_done_63 : forall n,
  0 <= n <= 38 ->
  fibfib_fill_len_z n (n + 1) = if Z.ltb n 3 then 3 else n + 1.
Proof.
  intros n Hn.
  unfold fibfib_fill_len_z.
  destruct (Z.leb_spec (n + 1) n); reflexivity || lia.
Qed.

Lemma fibfib_fill_len_done_lt_63 : forall n,
  0 <= n <= 38 ->
  n < 3 ->
  fibfib_fill_len_z n (n + 1) = 3.
Proof.
  intros n Hn Hlt.
  rewrite fibfib_fill_len_done_63 by lia.
  destruct (Z.ltb_spec n 3); lia.
Qed.

Lemma fibfib_fill_len_done_ge_63 : forall n,
  0 <= n <= 38 ->
  3 <= n ->
  fibfib_fill_len_z n (n + 1) = n + 1.
Proof.
  intros n Hn Hge.
  rewrite fibfib_fill_len_done_63 by lia.
  destruct (Z.ltb_spec n 3); lia.
Qed.

Lemma fibfib_fill_len_done_ge_index_63 : forall n,
  0 <= n <= 38 ->
  n < fibfib_fill_len_z n (n + 1).
Proof.
  intros n Hn.
  rewrite fibfib_fill_len_done_63 by lia.
  destruct (Z.ltb_spec n 3); lia.
Qed.

Lemma fibfib_prefix_read_63 : forall n,
  0 <= n <= 38 ->
  Znth n (fibfib_prefix_z (fibfib_fill_len_z n (n + 1))) 0 = fibfib_z n.
Proof.
  intros n Hn.
  rewrite fibfib_fill_len_done_63 by lia.
  unfold fibfib_prefix_z.
  destruct (Z.ltb_spec n 3).
  - assert (Hsmall : n = 0 \/ n = 1 \/ n = 2) by lia.
    destruct Hsmall as [-> | [-> | ->]]; vm_compute; reflexivity.
  - replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
    rewrite seq_snoc_63, map_app.
    replace (0 + Z.to_nat n)%nat with (Z.to_nat n) by lia.
    rewrite app_Znth2.
    + rewrite Zlength_correct, map_length, seq_length.
      replace (n - Z.of_nat (Z.to_nat n)) with 0 by lia.
      replace (Z.of_nat (Z.to_nat n)) with n by lia.
      cbn [map Znth].
      replace (fibfib_z (Z.of_nat (Z.to_nat n))) with (fibfib_z n) by (rewrite Z2Nat.id by lia; reflexivity).
      reflexivity.
    + rewrite Zlength_correct, map_length, seq_length.
      lia.
Qed.

Lemma fibfib_prefix_znth_63 : forall len k,
  0 <= k < len ->
  Znth k (fibfib_prefix_z len) 0 = fibfib_z k.
Proof.
  intros len k Hk.
  unfold Znth, fibfib_prefix_z.
  replace 0 with (fibfib_z 0) by (unfold fibfib_z, fibfib; reflexivity).
  rewrite map_nth with (d := 0%nat).
  rewrite seq_nth by lia.
  replace (0 + Z.to_nat k)%nat with (Z.to_nat k) by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma problem_63_spec_z_from_fibfib : forall n,
  0 <= n ->
  problem_63_spec_z n (fibfib_z n).
Proof.
  intros n Hn.
  unfold problem_63_spec_z, problem_63_spec, fibfib_z.
  repeat split; try lia.
Qed.
