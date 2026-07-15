Load "../spec/36".

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_36_pre_z (n : Z) : Prop :=
  problem_36_pre (Z.to_nat n).

Definition problem_36_spec_z (n output : Z) : Prop :=
  0 <= output /\ problem_36_spec (Z.to_nat n) (Z.to_nat output).

Definition count_digit7_z (n : Z) : Z :=
  Z.of_nat (count_digit_7 (Z.to_nat n)).

Definition fizz_buzz_prefix_z (n : Z) : Z :=
  Z.of_nat (fizz_buzz_impl (Z.to_nat n)).

Definition fizz_buzz_prefix_safe_z (n : Z) : Prop :=
  forall k, 0 <= k <= n -> fizz_buzz_prefix_z k <= INT_MAX.

Definition divisible_11_or_13_z (i : Z) : Prop :=
  Z.rem i 11 = 0 \/ Z.rem i 13 = 0.

Definition digit7_state_z (orig q seen : Z) : Prop :=
  0 <= q /\
  0 <= seen /\
  count_digit7_z orig = seen + count_digit7_z q.

Lemma count_digit7_z_nonneg : forall n,
  0 <= count_digit7_z n.
Proof.
  intros n. unfold count_digit7_z. lia.
Qed.

Lemma fizz_buzz_prefix_z_nonneg : forall n,
  0 <= fizz_buzz_prefix_z n.
Proof.
  intros n. unfold fizz_buzz_prefix_z. lia.
Qed.

Lemma digit7_state_start : forall i,
  0 <= i ->
  digit7_state_z i i 0.
Proof.
  intros i Hi.
  unfold digit7_state_z.
  repeat split; lia.
Qed.

Lemma digit7_state_done : forall i seen,
  digit7_state_z i 0 seen ->
  seen = count_digit7_z i.
Proof.
  intros i seen H.
  unfold digit7_state_z, count_digit7_z in *.
  destruct H as (_ & _ & H).
  simpl in H.
  lia.
Qed.

Lemma problem_36_spec_z_from_prefix : forall n output,
  0 <= n ->
  output = fizz_buzz_prefix_z n ->
  problem_36_spec_z n output.
Proof.
  intros n output Hn Hout.
  subst output.
  unfold problem_36_spec_z, fizz_buzz_prefix_z.
  split.
  - lia.
  - rewrite Nat2Z.id.
    unfold problem_36_spec.
    reflexivity.
Qed.

Lemma seq_snoc : forall start len,
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

Lemma zrem_zero_nat_eqb : forall i d,
  0 <= i ->
  0 < d ->
  Z.rem i d = 0 ->
  Nat.eqb (Z.to_nat i mod Z.to_nat d) 0 = true.
Proof.
  intros i d Hi Hd Hrem.
  apply Nat.eqb_eq.
  rewrite <- (Z2Nat.inj_mod i d) by lia.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  rewrite Hrem. reflexivity.
Qed.

Lemma zrem_nonzero_nat_eqb : forall i d,
  0 <= i ->
  0 < d ->
  Z.rem i d <> 0 ->
  Nat.eqb (Z.to_nat i mod Z.to_nat d) 0 = false.
Proof.
  intros i d Hi Hd Hrem.
  apply Nat.eqb_neq.
  intro Hnat.
  apply Hrem.
  rewrite Z.rem_mod_nonneg by lia.
  apply Z2Nat.inj; try lia.
  - apply Z.mod_pos_bound; lia.
  - replace (Z.to_nat d) with (Z.to_nat d) in Hnat by reflexivity.
    rewrite <- (Z2Nat.inj_mod i d) in Hnat by lia.
    exact Hnat.
Qed.

Lemma zrem11_zero_nat_eqb : forall i,
  0 <= i ->
  Z.rem i 11 = 0 ->
  Nat.eqb (Z.to_nat i mod 11) 0 = true.
Proof.
  intros i Hi Hrem.
  replace 11%nat with (Z.to_nat 11) by reflexivity.
  apply zrem_zero_nat_eqb; lia.
Qed.

Lemma zrem13_zero_nat_eqb : forall i,
  0 <= i ->
  Z.rem i 13 = 0 ->
  Nat.eqb (Z.to_nat i mod 13) 0 = true.
Proof.
  intros i Hi Hrem.
  replace 13%nat with (Z.to_nat 13) by reflexivity.
  apply zrem_zero_nat_eqb; lia.
Qed.

Lemma zrem11_nonzero_nat_eqb : forall i,
  0 <= i ->
  Z.rem i 11 <> 0 ->
  Nat.eqb (Z.to_nat i mod 11) 0 = false.
Proof.
  intros i Hi Hrem.
  replace 11%nat with (Z.to_nat 11) by reflexivity.
  apply zrem_nonzero_nat_eqb; lia.
Qed.

Lemma zrem13_nonzero_nat_eqb : forall i,
  0 <= i ->
  Z.rem i 13 <> 0 ->
  Nat.eqb (Z.to_nat i mod 13) 0 = false.
Proof.
  intros i Hi Hrem.
  replace 13%nat with (Z.to_nat 13) by reflexivity.
  apply zrem_nonzero_nat_eqb; lia.
Qed.

Lemma fizz_buzz_prefix_step_11 : forall i,
  0 <= i ->
  Z.rem i 11 = 0 ->
  fizz_buzz_prefix_z (i + 1) =
    fizz_buzz_prefix_z i + count_digit7_z i.
Proof.
  intros i Hi Hrem.
  unfold fizz_buzz_prefix_z, count_digit7_z, fizz_buzz_impl.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_snoc.
  rewrite fold_left_app. cbn [fold_left].
  replace (0 + Z.to_nat i)%nat with (Z.to_nat i) by lia.
  rewrite (zrem11_zero_nat_eqb i Hi Hrem).
  cbn [orb].
  rewrite Nat2Z.inj_add.
  reflexivity.
Qed.

Lemma fizz_buzz_prefix_step_13 : forall i,
  0 <= i ->
  Z.rem i 13 = 0 ->
  fizz_buzz_prefix_z (i + 1) =
    fizz_buzz_prefix_z i + count_digit7_z i.
Proof.
  intros i Hi Hrem.
  unfold fizz_buzz_prefix_z, count_digit7_z, fizz_buzz_impl.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_snoc.
  rewrite fold_left_app. cbn [fold_left].
  replace (0 + Z.to_nat i)%nat with (Z.to_nat i) by lia.
  rewrite (zrem13_zero_nat_eqb i Hi Hrem).
  destruct ((Z.to_nat i mod 11)%nat =? 0)%nat; simpl;
    rewrite Nat2Z.inj_add; reflexivity.
Qed.

Lemma fizz_buzz_prefix_step_none : forall i,
  0 <= i ->
  Z.rem i 11 <> 0 ->
  Z.rem i 13 <> 0 ->
  fizz_buzz_prefix_z (i + 1) = fizz_buzz_prefix_z i.
Proof.
  intros i Hi Hrem11 Hrem13.
  unfold fizz_buzz_prefix_z, fizz_buzz_impl.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_snoc.
  rewrite fold_left_app. cbn [fold_left].
  replace (0 + Z.to_nat i)%nat with (Z.to_nat i) by lia.
  rewrite (zrem11_nonzero_nat_eqb i Hi Hrem11).
  rewrite (zrem13_nonzero_nat_eqb i Hi Hrem13).
  cbn [orb].
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma fizz_buzz_prefix_hit_bound_11 : forall n i,
  fizz_buzz_prefix_safe_z n ->
  0 <= i ->
  i < n ->
  Z.rem i 11 = 0 ->
  fizz_buzz_prefix_z i + count_digit7_z i <= INT_MAX.
Proof.
  intros n i Hsafe Hi Hin Hrem.
  rewrite <- (fizz_buzz_prefix_step_11 i Hi Hrem).
  apply Hsafe.
  lia.
Qed.

Lemma fizz_buzz_prefix_hit_bound_13 : forall n i,
  fizz_buzz_prefix_safe_z n ->
  0 <= i ->
  i < n ->
  Z.rem i 13 = 0 ->
  fizz_buzz_prefix_z i + count_digit7_z i <= INT_MAX.
Proof.
  intros n i Hsafe Hi Hin Hrem.
  rewrite <- (fizz_buzz_prefix_step_13 i Hi Hrem).
  apply Hsafe.
  lia.
Qed.

Lemma divisible_11_or_13_from_11 : forall i,
  Z.rem i 11 = 0 ->
  divisible_11_or_13_z i.
Proof.
  intros i H. left; exact H.
Qed.

Lemma divisible_11_or_13_from_13 : forall i,
  Z.rem i 13 = 0 ->
  divisible_11_or_13_z i.
Proof.
  intros i H. right; exact H.
Qed.

Lemma fizz_buzz_prefix_step_divisible : forall i,
  0 <= i ->
  divisible_11_or_13_z i ->
  fizz_buzz_prefix_z (i + 1) =
    fizz_buzz_prefix_z i + count_digit7_z i.
Proof.
  intros i Hi [H11 | H13].
  - apply fizz_buzz_prefix_step_11; assumption.
  - apply fizz_buzz_prefix_step_13; assumption.
Qed.

Definition digit7_at (k p : nat) : bool :=
  Nat.eqb (((k / Nat.pow 10 p) mod 10)) 7.

Lemma digit7_at_tail : forall k p,
  digit7_at k (S p) = digit7_at (k / 10) p.
Proof.
  intros k p.
  unfold digit7_at.
  rewrite Nat.Div0.div_div.
  rewrite <- Nat.pow_succ_r'.
  reflexivity.
Qed.

Lemma digit7_at_false_large : forall k p,
  (k <= p)%nat ->
  digit7_at k p = false.
Proof.
  intros k p Hkp.
  unfold digit7_at.
  assert (Hpow : (k < 10 ^ p)%nat).
  {
    destruct p as [|p].
    - simpl. destruct k; lia.
    - assert (S p < 10 ^ S p)%nat by (apply Nat.pow_gt_lin_r; lia).
      lia.
  }
  rewrite Nat.div_small by exact Hpow.
  reflexivity.
Qed.

Lemma filter_false_seq : forall (f : nat -> bool) start len,
  (forall p, (start <= p < start + len)%nat -> f p = false) ->
  filter f (seq start len) = [].
Proof.
  intros f start len.
  revert start.
  induction len; intros start Hfalse; simpl.
  - reflexivity.
  - rewrite Hfalse by lia.
    apply IHlen.
    intros p Hp.
    apply Hfalse.
    lia.
Qed.

Lemma count_digit_7_extend_false : forall k n,
  (k <= n)%nat ->
  length (filter (digit7_at k) (seq 0 n)) = count_digit_7 k.
Proof.
  intros k n Hkn.
  unfold count_digit_7.
  replace n with (k + (n - k))%nat by lia.
  rewrite seq_app.
  rewrite filter_app, app_length.
  replace (0 + k)%nat with k by lia.
  rewrite (filter_false_seq (digit7_at k) k (n - k)).
  - rewrite Nat.add_0_r. reflexivity.
  - intros p Hp. apply digit7_at_false_large. lia.
Qed.

Lemma filter_cons_length : forall {A : Type} (f : A -> bool) a l,
  length (filter f (a :: l)) =
    ((if f a then 1 else 0) + length (filter f l))%nat.
Proof.
  intros A f a l.
  cbn [filter length].
  destruct (f a); reflexivity.
Qed.

Lemma length_filter_digit7_tail : forall k l,
  length (filter (digit7_at k) (map S l)) =
  length (filter (digit7_at (k / 10)) l).
Proof.
  intros k l.
  induction l as [|a l IH]; cbn [map filter length].
  - reflexivity.
  - rewrite digit7_at_tail.
    destruct (digit7_at (k / 10) a); cbn [length]; lia.
Qed.

Lemma count_digit_7_step_nat : forall k,
  (0 < k)%nat ->
  count_digit_7 k =
    ((if Nat.eqb (k mod 10) 7 then 1 else 0) + count_digit_7 (k / 10))%nat.
Proof.
  intros k Hk.
  destruct k as [|k']; [lia|].
  unfold count_digit_7 at 1.
  change (fun p : nat => (((S k' / 10 ^ p) mod 10) =? 7)%nat)
    with (digit7_at (S k')).
  change (seq 0 (S k')) with (0%nat :: seq 1 k').
  rewrite filter_cons_length.
  replace (digit7_at (S k') 0) with (Nat.eqb (S k' mod 10) 7).
  2:{
    unfold digit7_at.
    change (10 ^ 0)%nat with 1%nat.
    rewrite Nat.div_1_r.
    reflexivity.
  }
  rewrite <- seq_shift.
  rewrite length_filter_digit7_tail.
  rewrite (count_digit_7_extend_false (S k' / 10) k').
  - destruct (Nat.eqb ((S k') mod 10) 7); lia.
  - assert (S k' / 10 < S k')%nat by (apply Nat.div_lt; lia).
    lia.
Qed.

Lemma Zquot_eq_Zdiv_nonneg : forall a b,
  0 <= a ->
  0 < b ->
  Z.quot a b = a / b.
Proof.
  intros a b Ha Hb.
  apply Zquot_Zdiv_pos; lia.
Qed.

Lemma count_digit7_z_step_hit : forall q,
  q > 0 ->
  Z.rem q 10 = 7 ->
  count_digit7_z q = 1 + count_digit7_z (Z.quot q 10).
Proof.
  intros q Hq Hrem.
  unfold count_digit7_z.
  rewrite Zquot_eq_Zdiv_nonneg by lia.
  rewrite Z2Nat.inj_div by lia.
  replace (Z.to_nat 10) with 10%nat by reflexivity.
  rewrite count_digit_7_step_nat by lia.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  replace (Z.to_nat q mod 10)%nat with 7%nat.
  2:{
    replace 10%nat with (Z.to_nat 10) by reflexivity.
    rewrite <- Z2Nat.inj_mod by lia.
    rewrite Hrem. reflexivity.
  }
  rewrite Nat2Z.inj_add.
  reflexivity.
Qed.

Lemma count_digit7_z_step_miss : forall q,
  q > 0 ->
  Z.rem q 10 <> 7 ->
  count_digit7_z q = count_digit7_z (Z.quot q 10).
Proof.
  intros q Hq Hrem.
  unfold count_digit7_z.
  rewrite Zquot_eq_Zdiv_nonneg by lia.
  rewrite Z2Nat.inj_div by lia.
  replace (Z.to_nat 10) with 10%nat by reflexivity.
  rewrite count_digit_7_step_nat by lia.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  destruct (Z.to_nat q mod 10 =? 7)%nat eqn:Hnat.
  - apply Nat.eqb_eq in Hnat.
    exfalso.
    apply Hrem.
    replace 10%nat with (Z.to_nat 10) in Hnat by reflexivity.
    rewrite <- Z2Nat.inj_mod in Hnat by lia.
    replace 7%nat with (Z.to_nat 7) in Hnat by reflexivity.
    assert (q mod 10 = 7) by
      (apply Z2Nat.inj; [apply Z.mod_pos_bound; lia | lia | exact Hnat]).
    exact H.
  - reflexivity.
Qed.

Lemma digit7_state_hit : forall i q seen,
  q > 0 ->
  Z.rem q 10 = 7 ->
  digit7_state_z i q seen ->
  digit7_state_z i (Z.quot q 10) (seen + 1).
Proof.
  intros i q seen Hq Hrem Hstate.
  unfold digit7_state_z in *.
  destruct Hstate as (Hq_nonneg & Hseen & Hstate).
  repeat split.
  - rewrite Zquot_eq_Zdiv_nonneg by lia.
    apply Z.div_pos; lia.
  - lia.
  - rewrite Hstate.
    rewrite (count_digit7_z_step_hit q Hq Hrem).
    lia.
Qed.

Lemma digit7_state_hit_seen_bound : forall i q seen,
  q > 0 ->
  Z.rem q 10 = 7 ->
  digit7_state_z i q seen ->
  seen + 1 <= count_digit7_z i.
Proof.
  intros i q seen Hq Hrem Hstate.
  unfold digit7_state_z in Hstate.
  destruct Hstate as (_ & _ & Hstate).
  rewrite Hstate.
  rewrite (count_digit7_z_step_hit q Hq Hrem).
  pose proof (count_digit7_z_nonneg (Z.quot q 10)).
  lia.
Qed.

Lemma hit_remaining_bound : forall base q,
  q > 0 ->
  Z.rem q 10 = 7 ->
  base + count_digit7_z q <= INT_MAX ->
  (base + 1) + count_digit7_z (Z.quot q 10) <= INT_MAX.
Proof.
  intros base q Hq Hrem Hbound.
  replace ((base + 1) + count_digit7_z (Z.quot q 10))
    with (base + (1 + count_digit7_z (Z.quot q 10))) by lia.
  rewrite <- (count_digit7_z_step_hit q Hq Hrem).
  lia.
Qed.

Lemma hit_increment_bound : forall base q,
  q > 0 ->
  Z.rem q 10 = 7 ->
  base + count_digit7_z q <= INT_MAX ->
  base + 1 <= INT_MAX.
Proof.
  intros base q Hq Hrem Hbound.
  pose proof (hit_remaining_bound base q Hq Hrem Hbound).
  pose proof (count_digit7_z_nonneg (Z.quot q 10)).
  lia.
Qed.

Lemma digit7_state_miss : forall i q seen,
  q > 0 ->
  Z.rem q 10 <> 7 ->
  digit7_state_z i q seen ->
  digit7_state_z i (Z.quot q 10) seen.
Proof.
  intros i q seen Hq Hrem Hstate.
  unfold digit7_state_z in *.
  destruct Hstate as (Hq_nonneg & Hseen & Hstate).
  repeat split.
  - rewrite Zquot_eq_Zdiv_nonneg by lia.
    apply Z.div_pos; lia.
  - lia.
  - rewrite Hstate.
    rewrite (count_digit7_z_step_miss q Hq Hrem).
    lia.
Qed.

Lemma miss_remaining_bound : forall base q,
  q > 0 ->
  Z.rem q 10 <> 7 ->
  base + count_digit7_z q <= INT_MAX ->
  base + count_digit7_z (Z.quot q 10) <= INT_MAX.
Proof.
  intros base q Hq Hrem Hbound.
  rewrite <- (count_digit7_z_step_miss q Hq Hrem).
  exact Hbound.
Qed.
