Load "../spec/94".

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_94_pre_z (lst : list Z) : Prop :=
  problem_94_pre (map Z.to_nat lst).

Definition problem_94_spec_z (lst : list Z) (output : Z) : Prop :=
  0 <= output /\ problem_94_spec (map Z.to_nat lst) (Z.to_nat output).

Definition PRIME_LOOP_BOUND_94 : Z := 2147395599.
Definition INT_MIN_94 : Z := -2147483648.

Definition digit_at_94 (n p : nat) : nat :=
  (n / Nat.pow 10 p) mod 10.

Definition sum_digits_z_94 (n : Z) : Z :=
  Z.of_nat (sum_digits (Z.to_nat n)).

Definition digit_sum_state_94 (original q sum : Z) : Prop :=
  0 <= q /\
  0 <= sum /\
  sum + sum_digits_z_94 q = sum_digits_z_94 original /\
  sum + sum_digits_z_94 q <= INT_MAX.

Definition prime_scan_state_94 (x j flag : Z) : Prop :=
  (flag = 1 /\ forall d, 2 <= d < j -> Z.rem x d <> 0) \/
  (flag = 0 /\ exists d, 2 <= d < j /\ Z.rem x d = 0).

Definition prime_flag_done_94 (x j flag : Z) : Prop :=
  prime_scan_state_94 x j flag /\
  2 <= x /\ 2 <= j /\ j <= x /\ j * j > x /\
  ((flag = 1 /\ prime x) \/ (flag = 0 /\ ~ prime x)).

Definition update_largest_nat_94 (best x : nat) : nat :=
  if prime_dec (Z.of_nat x) then Nat.max best x else best.

Definition largest_prime_nat_94 (lst : list nat) : nat :=
  fold_left update_largest_nat_94 lst 0%nat.

Definition values_prefix_94 (i : Z) (lst : list Z) : list nat :=
  map Z.to_nat (sublist 0 i lst).

Definition largest_prime_prefix_94 (i : Z) (lst : list Z) : Z :=
  Z.of_nat (largest_prime_nat_94 (values_prefix_94 i lst)).

Definition skjkasdkd_safe_94 (lst : list Z) : Prop :=
  Forall (fun x => INT_MIN_94 <= x <= PRIME_LOOP_BOUND_94) lst /\
  sum_digits_z_94 (largest_prime_prefix_94 (Zlength lst) lst) <= INT_MAX.

Lemma Zquot_eq_Zdiv_nonneg_94 : forall a b,
  0 <= a ->
  0 < b ->
  Z.quot a b = a / b.
Proof.
  intros a b Ha Hb.
  apply Zquot_Zdiv_pos; lia.
Qed.

Lemma seq_snoc_94 : forall start len,
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

Lemma digit_at_tail_94 : forall k p,
  digit_at_94 k (S p) = digit_at_94 (k / 10) p.
Proof.
  intros k p.
  unfold digit_at_94.
  rewrite Nat.Div0.div_div.
  rewrite <- Nat.pow_succ_r'.
  reflexivity.
Qed.

Lemma digit_at_zero_large_94 : forall k p,
  (k <= p)%nat ->
  digit_at_94 k p = 0%nat.
Proof.
  intros k p Hkp.
  unfold digit_at_94.
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

Lemma fold_left_add_acc_94 : forall l acc,
  fold_left Nat.add l acc = (acc + fold_left Nat.add l 0)%nat.
Proof.
  induction l as [|x xs IH]; intros acc; simpl.
  - lia.
  - rewrite IH. rewrite (IH x). lia.
Qed.

Lemma fold_left_add_zeros_94 : forall len,
  fold_left Nat.add (repeat 0%nat len) 0%nat = 0%nat.
Proof.
  induction len; simpl; auto.
Qed.

Lemma map_digit_zero_seq_94 : forall k start len,
  (k <= start)%nat ->
  map (digit_at_94 k) (seq start len) = repeat 0%nat len.
Proof.
  intros k start len Hks.
  revert start Hks.
  induction len; intros start Hks; simpl.
  - reflexivity.
  - rewrite digit_at_zero_large_94 by lia.
    rewrite IHlen by lia.
    reflexivity.
Qed.

Lemma sum_digits_extend_94 : forall k len,
  (k <= len)%nat ->
  fold_left Nat.add (map (digit_at_94 k) (seq 0 len)) 0%nat = sum_digits k.
Proof.
  intros k len Hk.
  unfold sum_digits.
  replace len with (k + (len - k))%nat by lia.
  rewrite seq_app, map_app, fold_left_app.
  replace (0 + k)%nat with k by lia.
  rewrite map_digit_zero_seq_94 by lia.
  rewrite fold_left_add_acc_94.
  rewrite fold_left_add_zeros_94.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma sum_digits_step_nat_94 : forall n,
  (0 < n)%nat ->
  sum_digits n = (n mod 10 + sum_digits (n / 10))%nat.
Proof.
  intros n Hn.
  destruct n as [|n']; [lia|].
  unfold sum_digits at 1.
  change (seq 0 (S n')) with (0%nat :: seq 1 n').
  cbn [map fold_left].
  change (10 ^ 0)%nat with 1%nat.
  rewrite Nat.div_1_r.
  rewrite <- seq_shift.
  rewrite map_map.
  rewrite fold_left_add_acc_94.
  replace (fold_left Nat.add
    (map (fun x : nat => ((S n' / (10 ^ S x)) mod 10)%nat) (seq 0 n')) 0%nat)
    with (sum_digits (S n' / 10)).
  - lia.
  - replace (map (fun x : nat => ((S n' / (10 ^ S x)) mod 10)%nat) (seq 0 n'))
      with (map (digit_at_94 (S n' / 10)) (seq 0 n')).
    + symmetry. apply sum_digits_extend_94.
      assert (S n' / 10 < S n')%nat by (apply Nat.div_lt; lia).
      lia.
    + apply map_ext.
      intro p.
      symmetry. apply digit_at_tail_94.
Qed.

Lemma zrem10_nat_94 : forall n,
  0 <= n ->
  Z.to_nat (Z.rem n 10) = (Z.to_nat n mod 10)%nat.
Proof.
  intros n Hn.
  rewrite Z.rem_mod_nonneg by lia.
  replace 10%nat with (Z.to_nat 10) by reflexivity.
  rewrite <- Z2Nat.inj_mod by lia.
  reflexivity.
Qed.

Lemma zquot10_nat_94 : forall n,
  0 <= n ->
  Z.to_nat (Z.quot n 10) = (Z.to_nat n / 10)%nat.
Proof.
  intros n Hn.
  rewrite Zquot_eq_Zdiv_nonneg_94 by lia.
  rewrite Z2Nat.inj_div by lia.
  reflexivity.
Qed.

Lemma zquot10_nonneg_94 : forall n,
  0 <= n ->
  0 <= Z.quot n 10.
Proof.
  intros n Hn.
  rewrite Zquot_eq_Zdiv_nonneg_94 by lia.
  apply Z.div_pos; lia.
Qed.

Lemma zquot10_le_self_94 : forall n,
  0 <= n ->
  Z.quot n 10 <= n.
Proof.
  intros n Hn.
  rewrite Zquot_eq_Zdiv_nonneg_94 by lia.
  apply Z.div_le_upper_bound; lia.
Qed.

Lemma sum_digits_z_step_94 : forall n,
  0 < n ->
  sum_digits_z_94 n =
    Z.rem n 10 + sum_digits_z_94 (Z.quot n 10).
Proof.
  intros n Hn.
  unfold sum_digits_z_94.
  rewrite zquot10_nat_94 by lia.
  rewrite sum_digits_step_nat_94 by lia.
  rewrite Nat2Z.inj_add.
  rewrite <- zrem10_nat_94 by lia.
  rewrite Z2Nat.id.
  - reflexivity.
  - apply Z.rem_nonneg; lia.
Qed.

Lemma sum_digits_z_nonneg_94 : forall n,
  0 <= sum_digits_z_94 n.
Proof.
  intros n. unfold sum_digits_z_94. lia.
Qed.

Lemma digit_sum_state_start_94 : forall n,
  0 <= n ->
  sum_digits_z_94 n <= INT_MAX ->
  digit_sum_state_94 n n 0.
Proof.
  intros n Hn Hbound.
  unfold digit_sum_state_94.
  repeat split; lia.
Qed.

Lemma digit_sum_state_step_94 : forall original q sum,
  0 < q ->
  digit_sum_state_94 original q sum ->
  digit_sum_state_94 original (Z.quot q 10) (sum + Z.rem q 10).
Proof.
  intros original q sum Hq Hstate.
  unfold digit_sum_state_94 in *.
  destruct Hstate as (Hqnonneg & Hsumnonneg & Heq & Hbound).
  pose proof (Z.rem_bound_pos q 10 ltac:(lia) ltac:(lia)).
  pose proof (zquot10_nonneg_94 q ltac:(lia)).
  pose proof (sum_digits_z_nonneg_94 (Z.quot q 10)).
  rewrite sum_digits_z_step_94 in Heq by lia.
  rewrite sum_digits_z_step_94 in Hbound by lia.
  repeat split; try lia.
Qed.

Lemma digit_sum_state_increment_bound_94 : forall original q sum,
  0 < q ->
  digit_sum_state_94 original q sum ->
  sum + Z.rem q 10 <= INT_MAX.
Proof.
  intros original q sum Hq Hstate.
  unfold digit_sum_state_94 in Hstate.
  destruct Hstate as (_ & _ & _ & Hbound).
  rewrite sum_digits_z_step_94 in Hbound by lia.
  pose proof (sum_digits_z_nonneg_94 (Z.quot q 10)).
  lia.
Qed.

Lemma digit_sum_state_done_94 : forall original sum,
  digit_sum_state_94 original 0 sum ->
  sum = sum_digits_z_94 original.
Proof.
  intros original sum Hstate.
  unfold digit_sum_state_94, sum_digits_z_94 in *.
  destruct Hstate as (_ & _ & Heq & _).
  simpl in Heq.
  lia.
Qed.

Lemma Forall_Znth_94 : forall {A : Type} (P : A -> Prop) (l : list A) i d,
  Forall P l ->
  0 <= i < Zlength l ->
  P (Znth i l d).
Proof.
  intros A P l i d Hall Hi.
  unfold Znth.
  apply Forall_forall with (x := nth (Z.to_nat i) l d) in Hall.
  - exact Hall.
  - apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma safe_value_94 : forall lst i,
  skjkasdkd_safe_94 lst ->
  0 <= i < Zlength lst ->
  INT_MIN_94 <= Znth i lst 0 <= PRIME_LOOP_BOUND_94.
Proof.
  intros lst i [Hall _] Hi.
  apply Forall_Znth_94; assumption.
Qed.

Lemma prime_scan_start_94 : forall x,
  prime_scan_state_94 x 2 1.
Proof.
  intros x. left. split; [reflexivity|].
  intros d Hd. lia.
Qed.

Lemma prime_scan_step_hit_94 : forall x j flag,
  2 <= j ->
  Z.rem x j = 0 ->
  prime_scan_state_94 x j flag ->
  prime_scan_state_94 x (j + 1) 0.
Proof.
  intros x j flag Hj Hrem Hstate.
  right.
  split; [reflexivity|].
  exists j. repeat split; try lia; exact Hrem.
Qed.

Lemma prime_scan_step_miss_94 : forall x j flag,
  2 <= j ->
  Z.rem x j <> 0 ->
  prime_scan_state_94 x j flag ->
  prime_scan_state_94 x (j + 1) flag.
Proof.
  intros x j flag Hj Hrem Hstate.
  destruct Hstate as [[-> Hnone] | [-> [d [Hd Hdiv]]]].
  - left. split; [reflexivity|].
    intros d Hd.
    destruct (Z.eq_dec d j) as [-> | Hneq].
    + exact Hrem.
    + apply Hnone; lia.
  - right. split; [reflexivity|].
    exists d. split; [lia| exact Hdiv].
Qed.

Lemma Zrem_zero_divide_94 : forall a b,
  b <> 0 ->
  Z.rem a b = 0 ->
  (b | a).
Proof.
  intros a b Hb Hrem.
  apply Z.rem_divide; lia.
Qed.

Lemma divide_rem_zero_94 : forall a b,
  b <> 0 ->
  (b | a) ->
  Z.rem a b = 0.
Proof.
  intros a b Hb Hdiv.
  apply Z.rem_divide; [lia|exact Hdiv].
Qed.

Lemma composite_has_small_divisor_94 : forall x j,
  2 <= x ->
  2 <= j ->
  j * j > x ->
  ~ prime x ->
  exists d, 2 <= d < j /\ Z.rem x d = 0.
Proof.
  intros x j Hx Hj Hjj Hnot.
  destruct (not_prime_divide x ltac:(lia) Hnot) as [d [[Hd1 Hdlt] Hdiv]].
  destruct (Z_lt_ge_dec d j) as [Hdsmall | Hdbig].
  - exists d. split; [lia|].
    apply divide_rem_zero_94; [lia| exact Hdiv].
  - pose (q := x / d).
    assert (Hdpos : 0 < d) by lia.
    assert (Hx_eq : x = d * q).
    {
      unfold q.
      apply Zdivide_Zdiv_eq; [lia|exact Hdiv].
    }
    assert (Hqpos : 1 < q).
    {
      assert (q <> 1).
      { intro Hq1. subst q. lia. }
      assert (0 < q).
      {
        assert (0 < d * q) by (rewrite <- Hx_eq; lia).
        nia.
      }
      lia.
    }
    assert (Hqsmall : q < j).
    {
      destruct (Z_lt_ge_dec q j) as [Hlt | Hge]; [exact Hlt|].
      assert (j * j <= d * q) by nia.
      lia.
    }
    exists q. split; [lia|].
    apply divide_rem_zero_94; [lia|].
    exists d. lia.
Qed.

Lemma prime_scan_done_94 : forall x j flag,
  2 <= x ->
  2 <= j ->
  j <= x ->
  j * j > x ->
  prime_scan_state_94 x j flag ->
  prime_flag_done_94 x j flag.
Proof.
  intros x j flag Hx Hj Hjx Hjj Hstate.
  unfold prime_flag_done_94.
  repeat split; try assumption.
  destruct Hstate as [[Hflag Hnone] | [Hflag [d [Hd Hrem]]]].
  - left. split; [exact Hflag|].
    destruct (prime_dec x) as [Hp | Hnp]; [exact Hp|].
    exfalso.
    destruct (composite_has_small_divisor_94 x j Hx Hj Hjj Hnp)
      as [d [Hd Hrem]].
    apply (Hnone d Hd Hrem).
  - right. split; [exact Hflag|].
    intro Hp.
    apply Zrem_zero_divide_94 in Hrem; [|lia].
    pose proof (prime_divisors x Hp d Hrem) as Hcases.
    lia.
Qed.

Lemma prime_flag_done_prime_94 : forall x j,
  prime_flag_done_94 x j 1 ->
  prime x.
Proof.
  intros x j H.
  unfold prime_flag_done_94 in H.
  destruct H as (_ & _ & _ & _ & _ & [[_ Hp] | [Hbad _]]); [exact Hp|lia].
Qed.

Lemma prime_flag_done_not_prime_94 : forall x j,
  prime_flag_done_94 x j 0 ->
  ~ prime x.
Proof.
  intros x j H.
  unfold prime_flag_done_94 in H.
  destruct H as (_ & _ & _ & _ & _ & [[Hbad _] | [_ Hnp]]); [lia|exact Hnp].
Qed.

Lemma fold_left_largest_snoc_94 : forall l x,
  largest_prime_nat_94 (l ++ [x]) =
  update_largest_nat_94 (largest_prime_nat_94 l) x.
Proof.
  intros l x.
  unfold largest_prime_nat_94.
  rewrite fold_left_app.
  reflexivity.
Qed.

Lemma values_prefix_snoc_94 : forall i lst,
  0 <= i < Zlength lst ->
  values_prefix_94 (i + 1) lst =
  values_prefix_94 i lst ++ [Z.to_nat (Znth i lst 0)].
Proof.
  intros i lst Hi.
  unfold values_prefix_94.
  rewrite (sublist_split 0 (i + 1) i lst) by lia.
  rewrite sublist_single with (d := 0) by lia.
  rewrite map_app.
  reflexivity.
Qed.

Lemma largest_prime_prefix_step_prime_94 : forall i lst x current,
  0 <= i < Zlength lst ->
  x = Znth i lst 0 ->
  current = largest_prime_prefix_94 i lst ->
  current < x ->
  prime x ->
  0 <= x ->
  largest_prime_prefix_94 (i + 1) lst = x.
Proof.
  intros i lst x current Hi Hx Hcur Hgt Hp Hxnonneg.
  unfold largest_prime_prefix_94 in *.
  rewrite values_prefix_snoc_94 by lia.
  rewrite fold_left_largest_snoc_94.
  unfold update_largest_nat_94.
  destruct (prime_dec (Z.of_nat (Z.to_nat (Znth i lst 0)))) as [_ | Hnp].
  - rewrite Hx.
    replace (largest_prime_nat_94 (values_prefix_94 i lst))
      with (Z.to_nat current).
    2:{ rewrite Hcur. lia. }
    rewrite Nat2Z.inj_max.
    rewrite Z2Nat.id by lia.
    lia.
  - rewrite <- Hx in Hnp.
    rewrite Z2Nat.id in Hnp by lia.
    contradiction.
Qed.

Lemma largest_prime_prefix_step_not_prime_94 : forall i lst x current,
  0 <= i < Zlength lst ->
  x = Znth i lst 0 ->
  current = largest_prime_prefix_94 i lst ->
  current < x ->
  ~ prime x ->
  0 <= x ->
  largest_prime_prefix_94 (i + 1) lst = current.
Proof.
  intros i lst x current Hi Hx Hcur Hgt Hnp Hxnonneg.
  unfold largest_prime_prefix_94 in *.
  rewrite values_prefix_snoc_94 by lia.
  rewrite fold_left_largest_snoc_94.
  unfold update_largest_nat_94.
  destruct (prime_dec (Z.of_nat (Z.to_nat (Znth i lst 0)))) as [Hp | _].
  - rewrite <- Hx in Hp.
    rewrite Z2Nat.id in Hp by lia.
    contradiction.
  - symmetry. exact Hcur.
Qed.

Lemma largest_prime_prefix_step_skip_94 : forall i lst x current,
  0 <= i < Zlength lst ->
  x = Znth i lst 0 ->
  current = largest_prime_prefix_94 i lst ->
  (x <= current \/ x <= 1) ->
  INT_MIN_94 <= x ->
  largest_prime_prefix_94 (i + 1) lst = current.
Proof.
  intros i lst x current Hi Hx Hcur Hskip Hxmin.
  unfold largest_prime_prefix_94 in *.
  rewrite values_prefix_snoc_94 by lia.
  rewrite fold_left_largest_snoc_94.
  unfold update_largest_nat_94.
  destruct (prime_dec (Z.of_nat (Z.to_nat (Znth i lst 0)))) as [Hp | _].
  - rewrite <- Hx in Hp.
    destruct Hskip as [Hle | Hle1].
    + replace (largest_prime_nat_94 (values_prefix_94 i lst))
        with (Z.to_nat current).
      2:{ rewrite Hcur. lia. }
      rewrite Nat2Z.inj_max.
      rewrite Z2Nat.id by lia.
      lia.
    + exfalso.
      destruct (Z_lt_ge_dec x 0).
      * rewrite ZifyInst.of_nat_to_nat_eq in Hp.
        replace (Z.max 0 x) with 0 in Hp by lia.
        apply not_prime_0. exact Hp.
      * assert (Z.of_nat (Z.to_nat x) <= 1) by lia.
        assert (2 <= Z.of_nat (Z.to_nat x)) by (apply prime_ge_2; exact Hp).
        lia.
  - symmetry. exact Hcur.
Qed.

Definition largest_prime_rel_94 (lst : list nat) (best : nat) : Prop :=
  (best = 0%nat /\ forall p, In p lst -> ~ prime (Z.of_nat p)) \/
  (In best lst /\ prime (Z.of_nat best) /\
   forall p, In p lst -> prime (Z.of_nat p) -> (p <= best)%nat).

Lemma largest_prime_rel_update_94 : forall lst best x,
  largest_prime_rel_94 lst best ->
  largest_prime_rel_94 (lst ++ [x]) (update_largest_nat_94 best x).
Proof.
  intros lst best x Hrel.
  unfold update_largest_nat_94.
  destruct (prime_dec (Z.of_nat x)) as [Hpx | Hnpx].
  - destruct Hrel as [[Hbest Hnone] | [Hin [Hpbest Hmax]]].
    + subst best.
      rewrite Nat.max_0_l.
      right.
      split.
      * apply in_or_app. right. simpl. auto.
      * split.
        -- exact Hpx.
        -- intros p Hp Hpprime.
        apply in_app_or in Hp. destruct Hp as [Hp | [-> | []]].
        ++ exfalso. apply (Hnone p Hp Hpprime).
        ++ lia.
    + right.
      split.
      * destruct (Nat.leb_spec best x).
        -- rewrite Nat.max_r by lia. apply in_or_app. right. simpl. auto.
        -- rewrite Nat.max_l by lia. apply in_or_app. left. exact Hin.
      * split.
        -- destruct (Nat.leb_spec best x).
           ++ rewrite Nat.max_r by lia. exact Hpx.
           ++ rewrite Nat.max_l by lia. exact Hpbest.
        -- intros p Hp Hpprime.
        apply in_app_or in Hp. destruct Hp as [Hp | [-> | []]].
        ++ pose proof (Hmax p Hp Hpprime). lia.
        ++ apply Nat.le_max_r.
  - destruct Hrel as [[Hbest Hnone] | [Hin [Hpbest Hmax]]].
    + left. split; [exact Hbest|].
      intros p Hp Hpprime.
      apply in_app_or in Hp. destruct Hp as [Hp | [-> | []]].
      * apply (Hnone p Hp Hpprime).
      * apply Hnpx. exact Hpprime.
    + right.
      split.
      * apply in_or_app. left. exact Hin.
      * split.
        -- exact Hpbest.
        -- intros p Hp Hpprime.
        apply in_app_or in Hp. destruct Hp as [Hp | [-> | []]].
        ++ apply Hmax; assumption.
        ++ exfalso. apply Hnpx. exact Hpprime.
Qed.

Lemma largest_prime_rel_empty_94 :
  largest_prime_rel_94 [] 0%nat.
Proof.
  left. split; [reflexivity|].
  intros p Hp. inversion Hp.
Qed.

Lemma largest_prime_rel_fold_94 : forall todo seen best,
  largest_prime_rel_94 seen best ->
  largest_prime_rel_94 (seen ++ todo) (fold_left update_largest_nat_94 todo best).
Proof.
  induction todo as [|x xs IH]; intros seen best Hrel.
  - simpl. rewrite app_nil_r. exact Hrel.
  - simpl.
    replace (seen ++ x :: xs)%list with ((seen ++ [x]) ++ xs)%list
      by (change (x :: xs)%list with ([x] ++ xs)%list; rewrite app_assoc; reflexivity).
    apply IH.
    apply largest_prime_rel_update_94.
    exact Hrel.
Qed.

Lemma largest_prime_nat_rel_94 : forall lst,
  largest_prime_rel_94 lst (largest_prime_nat_94 lst).
Proof.
  intros lst.
  unfold largest_prime_nat_94.
  replace lst with ([] ++ lst)%list by reflexivity.
  apply largest_prime_rel_fold_94.
  apply largest_prime_rel_empty_94.
Qed.

Lemma largest_prime_nat_spec_94 : forall lst,
  problem_94_spec lst (sum_digits (largest_prime_nat_94 lst)).
Proof.
  intros lst.
  pose proof (largest_prime_nat_rel_94 lst) as Hrel.
  unfold largest_prime_rel_94 in Hrel.
  destruct Hrel as [[Hbest Hnone] | [Hin [Hp Hmax]]].
  - right. split; [exact Hnone|].
    rewrite Hbest. reflexivity.
  - left.
    exists (largest_prime_nat_94 lst).
    split; [exact Hin|].
    split; [exact Hp|].
    split; [exact Hmax|].
    reflexivity.
Qed.

Lemma values_prefix_full_94 : forall lst,
  values_prefix_94 (Zlength lst) lst = map Z.to_nat lst.
Proof.
  intros lst.
  unfold values_prefix_94.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma problem_94_spec_z_from_result_94 : forall lst largest output,
  0 <= output ->
  largest = largest_prime_prefix_94 (Zlength lst) lst ->
  output = sum_digits_z_94 largest ->
  problem_94_spec_z lst output.
Proof.
  intros lst largest output Hout Hlargest Houtput.
  subst output.
  unfold problem_94_spec_z, largest_prime_prefix_94, sum_digits_z_94 in *.
  split; [lia|].
  rewrite Hlargest.
  rewrite values_prefix_full_94.
  rewrite Nat2Z.id.
  rewrite Nat2Z.id.
  apply largest_prime_nat_spec_94.
Qed.

Open Scope Z_scope.
